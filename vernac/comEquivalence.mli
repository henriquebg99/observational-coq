(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** Equivalences between inductive types. *)

(** [try_add_new_equivalence id ~source ~target (fwd, bwd, sect, retr)]
    declares [id] as an equivalence between the inductives [source] and
    [target], where
    - [fwd : source -> target]
    - [bwd : target -> source]
    - [sect : forall a : source, a ~ bwd (fwd a)]
    - [retr : forall b : target, b ~ fwd (bwd b)]
    It only typechecks the components, and fails if [id] is already used.
    The axiom [id : source ~ target] and the rewrite rules are only declared
    by [register_equivalences]. *)
val try_add_new_equivalence
  :  Id.t
  -> source:inductive
  -> target:inductive
  -> Constrexpr.constr_expr * Constrexpr.constr_expr
     * Constrexpr.constr_expr * Constrexpr.constr_expr
  -> unit

(** [register_equivalences equivs] declares, for the equivalences [equivs]
    (given oldest first, without repetitions) of the current module, the axioms
    witnessing them and the cast rewrite rules. It can only be called once. *)
val register_equivalences : Libnames.qualid list -> unit
