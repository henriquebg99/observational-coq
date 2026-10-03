(* Examples for the Define Equivalence and Register Equivalences commands.

   Define Equivalence name : A <-> B := { fwd := _ ; bwd := _ ; sect := _ ; retr := _ }.

   where A and B are inductive types of type Set and
     fwd  : A -> B
     bwd  : B -> A
     sect : forall a : A, a ~ bwd (fwd a)
     retr : forall b : B, b ~ fwd (bwd b)

   It declares an axiom [name : A ~ B].
   Register Equivalences name1 ... namen. then adds the cast rules (only once). *)

(** Two copies of the booleans *)

Inductive B1 := t1 | f1.
Inductive B2 := t2 | f2.

Definition f (b : B1) : B2 := match b with t1 => t2 | f1 => f2 end.
Definition g (b : B2) : B1 := match b with t2 => t1 | f2 => f1 end.

Definition f_g_sect (b : B1) : b ~ g (f b) :=
  match b return b ~ g (f b) with t1 => obseq_refl | f1 => obseq_refl end.
Definition f_g_retr (b : B2) : b ~ f (g b) :=
  match b return b ~ f (g b) with t2 => obseq_refl | f2 => obseq_refl end.

Define Equivalence bool_equiv : B1 <-> B2 := {
  fwd := f ;
  bwd := g ;
  sect := f_g_sect ;
  retr := f_g_retr }.

(** The components may also be given inline *)

Define Equivalence bool_equiv_inline : B1 <-> B2 := {
  fwd := fun b => match b with t1 => t2 | f1 => f2 end ;
  bwd := fun b => match b with t2 => t1 | f2 => f1 end ;
  sect := fun b => match b with t1 => obseq_refl | f1 => obseq_refl end ;
  retr := fun b => match b with t2 => obseq_refl | f2 => obseq_refl end }.

(** A three-element type and a rotation of it *)

Inductive Three := a | b | c.
Inductive Three' := a' | b' | c'.

Define Equivalence rotate : Three <-> Three' := {
  fwd := fun x => match x with a => b' | b => c' | c => a' end ;
  bwd := fun x => match x with a' => c | b' => a | c' => b end ;
  sect := fun x => match x with a => obseq_refl | b => obseq_refl | c => obseq_refl end ;
  retr := fun x => match x with a' => obseq_refl | b' => obseq_refl | c' => obseq_refl end }.

(** Unary and binary natural numbers *)

Inductive positive : Set := xI : positive -> positive | xO : positive -> positive | xH : positive.
Inductive N : Set := N0 : N | Npos : positive -> N.

Fixpoint double (n : nat) : nat := match n with O => O | S n => S (S (double n)) end.

Fixpoint Pos_to_nat (p : positive) : nat :=
  match p with
  | xH => S O
  | xO p => double (Pos_to_nat p)
  | xI p => S (double (Pos_to_nat p))
  end.

Fixpoint Pos_succ (p : positive) : positive :=
  match p with
  | xH => xO xH
  | xO p => xI p
  | xI p => xO (Pos_succ p)
  end.

Definition N_to_nat (m : N) : nat := match m with N0 => O | Npos p => Pos_to_nat p end.
Definition N_succ (m : N) : N := match m with N0 => Npos xH | Npos p => Npos (Pos_succ p) end.
Fixpoint N_of_nat (n : nat) : N := match n with O => N0 | S n => N_succ (N_of_nat n) end.
Definition N_double (m : N) : N := match m with N0 => N0 | Npos p => Npos (xO p) end.

Definition Pos_to_nat_succ (p : positive) : Pos_to_nat (Pos_succ p) ~ S (Pos_to_nat p).
Proof.
  induction p as [p IH | p _ |].
  - exact (ap double IH).
  - exact obseq_refl.
  - exact obseq_refl.
Defined.

Definition N_to_nat_succ (m : N) : N_to_nat (N_succ m) ~ S (N_to_nat m).
Proof.
  destruct m as [| p].
  - exact obseq_refl.
  - exact (Pos_to_nat_succ p).
Defined.

Definition nat_N_sect (n : nat) : n ~ N_to_nat (N_of_nat n).
Proof.
  induction n as [| n IH].
  - exact obseq_refl.
  - exact (obseq_trans (ap S IH) (obseq_sym (N_to_nat_succ (N_of_nat n)))).
Defined.

Definition N_succ_succ_double (m : N) : N_succ (N_succ (N_double m)) ~ N_double (N_succ m).
Proof.
  destruct m; exact obseq_refl.
Defined.

Definition N_of_nat_double (n : nat) : N_of_nat (double n) ~ N_double (N_of_nat n).
Proof.
  induction n as [| n IH].
  - exact obseq_refl.
  - exact (obseq_trans (ap (fun m => N_succ (N_succ m)) IH) (N_succ_succ_double (N_of_nat n))).
Defined.

Definition N_of_Pos_to_nat (p : positive) : N_of_nat (Pos_to_nat p) ~ Npos p.
Proof.
  induction p as [p IH | p IH |].
  - exact (obseq_trans (ap N_succ (N_of_nat_double (Pos_to_nat p))) (ap (fun m => N_succ (N_double m)) IH)).
  - exact (obseq_trans (N_of_nat_double (Pos_to_nat p)) (ap N_double IH)).
  - exact obseq_refl.
Defined.

Definition nat_N_retr (m : N) : m ~ N_of_nat (N_to_nat m).
Proof.
  destruct m as [| p].
  - exact obseq_refl.
  - exact (obseq_sym (N_of_Pos_to_nat p)).
Defined.

Define Equivalence equiv_nat_N : nat <-> N := {
  fwd := N_of_nat ;
  bwd := N_to_nat ;
  sect := nat_N_sect ;
  retr := nat_N_retr }.

(** Each equivalence declares an axiom with the same name *)

Check equiv_nat_N : nat ~ N.
Check bool_equiv : B1 ~ B2.

(** Equivalences declared in modules *)

Module M.
  Define Equivalence bool_equiv : B2 <-> B1 := {
    fwd := g ; bwd := f ; sect := f_g_retr ; retr := f_g_sect }.
End M.

(** Four more types, to compose equivalences: T1 <-> T2, T3 <-> T4 and T2 <-> T3 *)

Inductive T1 := a1 | b1 | c1.
Inductive T2 := a2 | b2 | c2.
Inductive T3 := a3 | b3 | c3.
Inductive T4 := a4 | b4 | c4.

Define Equivalence e12 : T1 <-> T2 := {
  fwd := fun x => match x with a1 => b2 | b1 => c2 | c1 => a2 end ;
  bwd := fun x => match x with a2 => c1 | b2 => a1 | c2 => b1 end ;
  sect := fun x => match x with a1 => obseq_refl | b1 => obseq_refl | c1 => obseq_refl end ;
  retr := fun x => match x with a2 => obseq_refl | b2 => obseq_refl | c2 => obseq_refl end }.

Define Equivalence e34 : T3 <-> T4 := {
  fwd := fun x => match x with a3 => a4 | b3 => b4 | c3 => c4 end ;
  bwd := fun x => match x with a4 => a3 | b4 => b3 | c4 => c3 end ;
  sect := fun x => match x with a3 => obseq_refl | b3 => obseq_refl | c3 => obseq_refl end ;
  retr := fun x => match x with a4 => obseq_refl | b4 => obseq_refl | c4 => obseq_refl end }.

Define Equivalence e23 : T2 <-> T3 := {
  fwd := fun x => match x with a2 => a3 | b2 => b3 | c2 => c3 end ;
  bwd := fun x => match x with a3 => a2 | b3 => b2 | c3 => c2 end ;
  sect := fun x => match x with a2 => obseq_refl | b2 => obseq_refl | c2 => obseq_refl end ;
  retr := fun x => match x with a3 => obseq_refl | b3 => obseq_refl | c3 => obseq_refl end }.

(** Defining equivalences adds no reduction rule: the casts are stuck *)

Eval compute in cast B1 B2 bool_equiv t1.
Eval compute in fun e : T1 ~ T4 => cast T1 T4 e a1.

(** Register Equivalences declares the cast rewrite rules, once, for the given
    equivalences (oldest first). [cast A B e t] reduces to [fwd t], where [fwd]
    goes from [A] to the representative of its class of equivalent inductives,
    then to [B]. *)

(* Only the equivalences of the current module can be registered *)
Fail Register Equivalences M.bool_equiv.
Fail Register Equivalences f.

Register Equivalences bool_equiv bool_equiv_inline rotate equiv_nat_N e12 e34 e23.

Fail Register Equivalences e12.

Eval compute in cast B1 B2 bool_equiv t1.
Eval compute in cast B2 B1 (obseq_sym bool_equiv) f2.
Eval compute in cast nat N equiv_nat_N 6.
Eval compute in cast N nat (obseq_sym equiv_nat_N) (Npos (xI (xO xH))).
(* Note: vm_compute does not fire the rewrite rules of cast (not even cast_refl) *)

(* The reduction is checked by the kernel *)
Definition cast_t1 : cast B1 B2 bool_equiv t1 ~ t2 := obseq_refl.

Eval compute in cast T1 T4 (e12 @@@ e23 @@@ e34) a1.
Eval compute in cast T4 T1 (obseq_sym (e12 @@@ e23 @@@ e34)) b4.
Eval compute in cast T1 T2 (e12) a1.
Eval cbn in fun x => cast T1 T4 (e12 @@@ e23 @@@ e34) x.
Definition cast_a1 : cast T1 T4 (e12 @@@ e23 @@@ e34) a1 ~ b4 := obseq_refl.

(** Errors *)

(* The name is already used *)
Fail Define Equivalence bool_equiv : B1 <-> B2 := {
  fwd := f ; bwd := g ; sect := f_g_sect ; retr := f_g_retr }.

(* fwd has the wrong type *)
Fail Define Equivalence wrong_fwd : B1 <-> B2 := {
  fwd := g ; bwd := g ; sect := f_g_sect ; retr := f_g_retr }.

(* sect is not a section: not every b is (g (f b)) *)
Fail Define Equivalence wrong_sect : B1 <-> B2 := {
  fwd := fun _ => t2 ; bwd := g ;
  sect := fun x => obseq_refl ; retr := f_g_retr }.

(* A and B must be inductive types *)
Fail Define Equivalence not_ind : f <-> B2 := {
  fwd := f ; bwd := g ; sect := f_g_sect ; retr := f_g_retr }.

(* Equivalences are not allowed in sections *)
Section S.
  Fail Define Equivalence in_section : B1 <-> B2 := {
    fwd := f ; bwd := g ; sect := f_g_sect ; retr := f_g_retr }.
End S.

(* A and B must not have parameters *)
Inductive option' (A : Type) := None' | Some' : A -> option' A.
Fail Define Equivalence with_param : option' <-> B2 := {
  fwd := f ; bwd := g ; sect := f_g_sect ; retr := f_g_retr }.

(* A and B must not have indices *)
Inductive is_t1 : B1 -> Type := is_t1_t1 : is_t1 t1.
Fail Define Equivalence with_index : B1 <-> is_t1 := {
  fwd := f ; bwd := g ; sect := f_g_sect ; retr := f_g_retr }.

(* A and B must have type Set *)
Inductive B3 : Type := t3 : Set -> B3 | f3.
Fail Define Equivalence in_type : B3 <-> B2 := {
  fwd := f ; bwd := g ; sect := f_g_sect ; retr := f_g_retr }.

Inductive B4 : SProp := t4 | f4.
Fail Define Equivalence in_sprop : B1 <-> B4 := {
  fwd := f ; bwd := g ; sect := f_g_sect ; retr := f_g_retr }.
