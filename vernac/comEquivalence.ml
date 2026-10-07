(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Pp
open Names
open Equivalences
open Libobject
open Libnames

(* Errors *)

type equivalence_error_kind =
  | AlreadyExists
  | NameUsed
  | Repeated of Id.t
  | UniverseLevels
  | InSection
  | NoObseq
  | NotASimpleInductive of inductive
  | NotInSet of inductive
  | PolymorphicInductive of inductive
  | KernelIllTyped of string

exception EquivalenceError of equivalence_error_kind

let explain_equivalence_error id = function
  | AlreadyExists ->
      (Id.print id ++ str " is already an equivalence")
  | NameUsed ->
      (Id.print id ++ str " is already used by another object")
  | Repeated id ->
      (Id.print id ++ str " appears several times")
  | UniverseLevels ->
      (str "The components of the equivalence must not introduce universe levels")
  | InSection ->
      (str "Equivalences cannot be declared inside sections")
  | NoObseq ->
      (str "The observational equality does not exist." ++ spc () ++
       str "Did you forget to open the observational library?")
  | NotASimpleInductive ind ->
      (Printer.pr_inductive (Global.env ()) ind ++
       str " must be an inductive type without parameters nor indices")
  | NotInSet ind ->
      (Printer.pr_inductive (Global.env ()) ind ++ str " must have type Set")
  | PolymorphicInductive ind ->
      (Printer.pr_inductive (Global.env ()) ind ++ str " must not be universe polymorphic")
  | KernelIllTyped field ->
      (str "The kernel rejected the type of " ++ str field)

(* The library object *)

let cache_equivalence (kn, e) = add_equivalence kn e

let open_equivalence i o =
  if Int.equal i 1 then
    cache_equivalence o

let subst_equivalence (subst, (kn, e)) =
  let kn' = Mod_subst.subst_kn subst kn in
  let e' = Equivalences.subst_equivalence subst e in
  if kn' == kn && e' == e then (kn, e) else (kn', e')

let eqv_cat = create_category "equivalences"

let inEquivalence : KerName.t * equivalence -> obj =
  declare_object {(default_object "EQUIVALENCE") with
    open_function = simple_open ~cat:eqv_cat open_equivalence;
    cache_function = cache_equivalence;
    subst_function = subst_equivalence;
    classify_function = (fun _ -> Substitute) }

(* Typing of the components *)

let obseq_inductive () =
  try Nametab.global_inductive (Libnames.qualid_of_ident (Id.of_string "obseq"))
  with Not_found -> raise (EquivalenceError NoObseq)

(* [forall x : ty, x ~ g (f x)] *)
let inverse_type env sigma obseq ty f g =
  let open EConstr in
  let sigma, obseq = Evd.fresh_global env sigma (GlobRef.IndRef obseq) in
  let x = mkRel 1 in
  let body = mkApp (obseq, [| ty; x; mkApp (g, [| mkApp (f, [| x |]) |]) |]) in
  let typ = mkProd (Context.make_annot (Name (Id.of_string "x")) Sorts.Relevant, ty, body) in
  (* Generates the universe constraints of [obseq] *)
  let sigma, _ = Typing.sort_of env sigma typ in
  sigma, typ

(* [ind : Set]: it has no parameters, no indices and lives in Set *)
let check_simple_inductive env ind =
  let open Declarations in
  let (mib, mip) = Inductive.lookup_mind_specif env ind in
  if mib.mind_nparams <> 0 || mip.mind_nrealargs <> 0 then
    raise (EquivalenceError (NotASimpleInductive ind));
  if Declareops.inductive_is_polymorphic mib then
    raise (EquivalenceError (PolymorphicInductive ind));
  match mip.mind_arity with
  | RegularArity { mind_sort; _ } when Sorts.is_set mind_sort -> ()
  | RegularArity _ | TemplateArity _ ->
    raise (EquivalenceError (NotInSet ind))

(* [@obseq Set A B] *)
let obseq_set_type env sigma obseq tyA tyB =
  let open EConstr in
  let sigma, obseq = Evd.fresh_global env sigma (GlobRef.IndRef obseq) in
  let typ = mkApp (obseq, [| mkSet; tyA; tyB |]) in
  let sigma, _ = Typing.sort_of env sigma typ in
  sigma, typ

let arrow_type env sigma tyA tyB =
  let typ = EConstr.mkArrowR tyA tyB in
  let sigma, _ = Typing.sort_of env sigma typ in
  sigma, typ

(* The terms were elaborated by the pretyper: check them again in the kernel *)
let kernel_check env uctx typed_terms =
  let env = Environ.push_context_set ~strict:true uctx env in
  let check (field, c, ty) =
    try
      let j = Typeops.infer env c in
      Conversion.default_conv_leq env j.Environ.uj_type ty
    with Type_errors.TypeError _ | Conversion.NotConvertible ->
      raise (EquivalenceError (KernelIllTyped field))
  in
  List.iter check typed_terms

let interp_equivalence env sigma indA indB (fwd, bwd, sect, retr) =
  let obseq = obseq_inductive () in
  check_simple_inductive env indA;
  check_simple_inductive env indB;
  let sigma, tyA = Evd.fresh_global env sigma (GlobRef.IndRef indA) in
  let sigma, tyB = Evd.fresh_global env sigma (GlobRef.IndRef indB) in
  let interp sigma c ty = Constrintern.interp_casted_constr_evars env sigma c ty in
  let sigma, fwd_ty = arrow_type env sigma tyA tyB in
  let sigma, fwd = interp sigma fwd fwd_ty in
  let sigma, bwd_ty = arrow_type env sigma tyB tyA in
  let sigma, bwd = interp sigma bwd bwd_ty in
  let sigma, sect_ty = inverse_type env sigma obseq tyA fwd bwd in
  let sigma, sect = interp sigma sect sect_ty in
  let sigma, retr_ty = inverse_type env sigma obseq tyB bwd fwd in
  let sigma, retr = interp sigma retr retr_ty in
  let sigma = Evd.minimize_universes sigma in
  (* the axiom is only declared by [register_equivalences], at Set: nothing
     else can be declared here *)
  let levels = fst (Evd.universe_context_set sigma) in
  if not (Univ.Level.Set.is_empty levels) then raise (EquivalenceError UniverseLevels);
  let to_constr = EConstr.to_constr sigma in
  let fwd = to_constr fwd and bwd = to_constr bwd in
  let sect = to_constr sect and retr = to_constr retr in
  let () = kernel_check env (Evd.universe_context_set sigma) [
      "fwd", fwd, to_constr fwd_ty;
      "bwd", bwd, to_constr bwd_ty;
      "sect", sect, to_constr sect_ty;
      "retr", retr, to_constr retr_ty;
    ] in
  sigma, (fwd, bwd, sect, retr)

(* Declaration *)

(* Cast reduction: [cast A B e t] reduces to [fwd t], where [fwd] goes from [A]
   to its representative and back to [B] (uconv_cast_equiv in uty.v).
   The rules are declared once, for all the registered equivalences. *)
let declare_cast_rules equivs =
  let repr = repr_map equivs in
  let inds = Indset_env.elements (Indmap_env.domain repr) in
  let cnt = ref 0 in
  let declare a b =
    let (ra, ea) = Indmap_env.find a repr in
    let (rb, eb) = Indmap_env.find b repr in
    if not (Ind.CanOrd.equal a b) && Ind.CanOrd.equal ra rb then begin
      incr cnt;
      let name = Id.of_string ("equivalences_cast" ^ string_of_int !cnt) in
      let fwd = (ecomp ea (einv eb)).eqv_fwd in
      Observational.declare_equivalence_cast_rule ~name a b fwd
    end
  in
  List.iter (fun a -> List.iter (declare a) inds) inds

let registered = Summary.ref ~name:"equivalences_registered" false

(* Only typechecks the components; the axiom is declared by [register_equivalences] *)
let add_new_equivalence_core id indA indB terms =
  if Lib.sections_are_opened () then raise (EquivalenceError InSection);
  let kn = Lib.make_kn id in
  if equivalence_exists kn then raise (EquivalenceError AlreadyExists);
  if Nametab.exists_cci (Lib.make_path id) then raise (EquivalenceError NameUsed);
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let _, (fwd, bwd, sect, retr) = interp_equivalence env sigma indA indB terms in
  let e = {
    eqv_indA = indA;
    eqv_indB = indB;
    eqv_fwd = fwd;
    eqv_bwd = bwd;
    eqv_sect = sect;
    eqv_retr = retr;
  } in
  Lib.add_leaf (inEquivalence (kn, e))

let try_add_new_equivalence id ~source ~target terms =
  try add_new_equivalence_core id source target terms
  with EquivalenceError e ->
    user_err (explain_equivalence_error id e ++ str ".")

(* The axiom [id : indA ~ indB] witnessing the equivalence *)
let declare_axiom id e =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let obseq = obseq_inductive () in
  let sigma, tyA = Evd.fresh_global env sigma (GlobRef.IndRef e.eqv_indA) in
  let sigma, tyB = Evd.fresh_global env sigma (GlobRef.IndRef e.eqv_indB) in
  let sigma, axiom_ty = obseq_set_type env sigma obseq tyA tyB in
  let sigma = Evd.minimize_universes sigma in
  let univs = Evd.univ_entry ~poly:false sigma in
  let entry = Declare.parameter_entry ~univs (EConstr.to_constr sigma axiom_ty) in
  let _ : Constant.t =
    Declare.declare_constant ~name:id ~kind:Decls.(IsAssumption Logical)
      (Declare.ParameterEntry entry)
  in
  ()

(* [equivs] are in declaration order, the oldest first. Declares the axioms
   and the cast rules *)
let register_equivalences equivs =
  if !registered then user_err (str "Can only register equivalences once.");
  let find qid =
    let id =
      if qualid_is_ident qid then qualid_basename qid
      else user_err (pr_qualid qid ++ str " is not an equivalence defined in the current module.") in
    try id, equivalence_info (Lib.make_kn id)
    with Not_found ->
      user_err (pr_qualid qid ++ str " is not an equivalence defined in the current module.")
  in
  let equivs = List.map find equivs in
  let _ : Id.Set.t = List.fold_left (fun seen (id, _) ->
      if Id.Set.mem id seen then
        user_err (explain_equivalence_error id (Repeated id) ++ str " in the list of equivalences.");
      Id.Set.add id seen) Id.Set.empty equivs in
  registered := true;
  List.iter (fun (id, e) -> declare_axiom id e) equivs;
  declare_cast_rules (List.rev_map snd equivs)
