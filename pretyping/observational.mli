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


val declare_inductive_observational_data : ?loc:Loc.t -> (Names.MutInd.t * int) -> unit

val declare_observational_equality :
  (univs:UState.named_universes_entry
   -> name:Id.t
   -> Constr.t
   -> Constant.t) ref

val declare_forded_constructor :
  (univs:UState.named_universes_entry
   -> name:Id.t
   -> Constr.t
   -> Constant.t) ref

val declare_observational_rewrite :
  (univs:UState.named_universes_entry
   -> name:Id.t
   -> Constr.t
   -> Constr.t
   -> Constant.t) ref

(** [declare_equivalence_cast_rule ~name indA indB fwd] declares the rewrite
    rule [cast A B ?e ?t ==> fwd ?t] between two inductives. *)
val declare_equivalence_cast_rule : ?loc:Loc.t -> name:Names.Id.t -> Names.inductive -> Names.inductive -> Constr.t -> unit
