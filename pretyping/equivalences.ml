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
open Names
open Constr
open Mod_subst

type equivalence = {
  eqv_indA : inductive;
  eqv_indB : inductive;
  eqv_fwd : Constr.t;
  eqv_bwd : Constr.t;
  eqv_sect : Constr.t;
  eqv_retr : Constr.t;
}

(* The equivalences by name, and their names in declaration order (newest first) *)

let equivalence_tab =
  Summary.ref ~name:"equivalence_tab" (KNmap.empty : equivalence KNmap.t)

let equivalence_order =
  Summary.ref ~name:"equivalence_order" ([] : KerName.t list)

let add_equivalence kn e =
  equivalence_tab := KNmap.add kn e !equivalence_tab;
  equivalence_order := kn :: !equivalence_order

let equivalence_exists kn = KNmap.mem kn !equivalence_tab

let equivalence_info kn = KNmap.find kn !equivalence_tab

let equivalences () =
  List.map (fun kn -> KNmap.find kn !equivalence_tab) !equivalence_order

let subst_equivalence subst e =
  let indA' = subst_ind subst e.eqv_indA in
  let indB' = subst_ind subst e.eqv_indB in
  let fwd' = subst_mps subst e.eqv_fwd in
  let bwd' = subst_mps subst e.eqv_bwd in
  let sect' = subst_mps subst e.eqv_sect in
  let retr' = subst_mps subst e.eqv_retr in
  if indA' == e.eqv_indA && indB' == e.eqv_indB
     && fwd' == e.eqv_fwd && bwd' == e.eqv_bwd
     && sect' == e.eqv_sect && retr' == e.eqv_retr
  then e
  else { eqv_indA = indA'; eqv_indB = indB';
         eqv_fwd = fwd'; eqv_bwd = bwd'; eqv_sect = sect'; eqv_retr = retr' }

(** {6 Building equivalences} *)

(* The observational primitives, all instantiated at Set: the inductives of
   equivalences live in Set and these primitives have no universe constraints *)

let set_instance = UVars.Instance.of_array ([| |], [| Univ.Universe.type0 |])
let set_instance2 = UVars.Instance.of_array ([| |], [| Univ.Universe.type0; Univ.Universe.type0 |])

let locate f s =
  try f (Libnames.qualid_of_ident (Id.of_string s))
  with Not_found ->
    user_err Pp.(str "The observational primitive " ++ str s ++ str " does not exist." ++ spc () ++
                 str "Did you forget to open the observational library?")

(* [@obseq_refl A a] *)
let mk_refl ty a =
  let obseq = locate Nametab.global_inductive "obseq" in
  mkApp (mkConstructU ((obseq, 1), set_instance), [| ty; a |])

(* [@obseq_trans A a b c e e'] *)
let mk_trans ty a b c e e' =
  let trans = locate Nametab.locate_constant "obseq_trans" in
  mkApp (mkConstU (trans, set_instance), [| ty; a; b; c; e; e' |])

(* [@ap A B f x y e] *)
let mk_ap tyA tyB f x y e =
  let ap = locate Nametab.locate_constant "ap" in
  mkApp (mkConstU (ap, set_instance2), [| tyA; tyB; f; x; y; e |])

let mk_lam ty body = mkLambda (Context.make_annot (Name (Id.of_string "x")) Sorts.Relevant, ty, body)

let app f x = mkApp (f, [| x |])

(* The inductives of equivalences are monomorphic *)
let mk_ind ind = mkIndU (ind, UVars.Instance.empty)

(* The components of equivalences are closed, so they need no lifting under [mk_lam] *)

let erefl ind =
  let ty = mk_ind ind in
  let id = mk_lam ty (mkRel 1) in
  let refl = mk_lam ty (mk_refl ty (mkRel 1)) in
  { eqv_indA = ind; eqv_indB = ind;
    eqv_fwd = id; eqv_bwd = id; eqv_sect = refl; eqv_retr = refl }

let einv e =
  { eqv_indA = e.eqv_indB; eqv_indB = e.eqv_indA;
    eqv_fwd = e.eqv_bwd; eqv_bwd = e.eqv_fwd;
    eqv_sect = e.eqv_retr; eqv_retr = e.eqv_sect }

let ecomp e1 e2 =
  if not (Ind.CanOrd.equal e1.eqv_indB e2.eqv_indA) then
    anomaly Pp.(str "ecomp: the equivalences are not composable.");
  let tyA = mk_ind e1.eqv_indA and tyB = mk_ind e1.eqv_indB and tyC = mk_ind e2.eqv_indB in
  let f1 = e1.eqv_fwd and g1 = e1.eqv_bwd and s1 = e1.eqv_sect and r1 = e1.eqv_retr in
  let f2 = e2.eqv_fwd and g2 = e2.eqv_bwd and s2 = e2.eqv_sect and r2 = e2.eqv_retr in
  let x = mkRel 1 in
  (* a ~ g1 (f1 a) ~ g1 (g2 (f2 (f1 a))) *)
  let sect =
    let f1a = app f1 x in
    let g2f2f1a = app g2 (app f2 f1a) in
    mk_lam tyA
      (mk_trans tyA x (app g1 f1a) (app g1 g2f2f1a)
         (app s1 x)
         (mk_ap tyB tyA g1 f1a g2f2f1a (app s2 f1a)))
  in
  (* c ~ f2 (g2 c) ~ f2 (f1 (g1 (g2 c))) *)
  let retr =
    let g2c = app g2 x in
    let f1g1g2c = app f1 (app g1 g2c) in
    mk_lam tyC
      (mk_trans tyC x (app f2 g2c) (app f2 f1g1g2c)
         (app r2 x)
         (mk_ap tyB tyC f2 g2c f1g1g2c (app r1 g2c)))
  in
  { eqv_indA = e1.eqv_indA; eqv_indB = e2.eqv_indB;
    eqv_fwd = mk_lam tyA (app f2 (app f1 x));
    eqv_bwd = mk_lam tyC (app g1 (app g2 x));
    eqv_sect = sect; eqv_retr = retr }

(** {6 Representatives} *)

(* The representatives of all the inductives that appear in the equivalences [l]
   (newest first). This computes [repr] of equiv.v for all of them at once, from
   the oldest equivalence to the newest: [repr (hd :: tl) ind] only depends on
   [repr tl]. *)
let repr_map l =
  let find m ind = try Indmap_env.find ind m with Not_found -> (ind, erefl ind) in
  let step m hd =
    let (i2, e2) = find m hd.eqv_indA in
    let (i3, e3) = find m hd.eqv_indB in
    let update ind m' =
      let (i1, e1) = find m ind in
      let r =
        if Ind.CanOrd.equal i1 i2 then
          (* e1 . (einv e2) . hd . e3 *)
          (i3, ecomp e1 (ecomp (einv e2) (ecomp hd e3)))
        else (i1, e1)
      in
      Indmap_env.add ind r m'
    in
    let inds = Indset_env.add hd.eqv_indA (Indset_env.add hd.eqv_indB (Indmap_env.domain m)) in
    Indset_env.fold update inds Indmap_env.empty
  in
  List.fold_left step Indmap_env.empty (List.rev l)

let repr l ind =
  try Indmap_env.find ind (repr_map l) with Not_found -> (ind, erefl ind)
