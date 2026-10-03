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

(** Equivalences between two inductive types [indA] and [indB] *)

type equivalence = {
  eqv_indA : inductive;
  eqv_indB : inductive;
  eqv_fwd : Constr.t;   (** [indA -> indB] *)
  eqv_bwd : Constr.t;   (** [indB -> indA] *)
  eqv_sect : Constr.t;  (** [forall a : indA, a ~ eqv_bwd (eqv_fwd a)] *)
  eqv_retr : Constr.t;  (** [forall b : indB, b ~ eqv_fwd (eqv_bwd b)] *)
}

(** {6 Access to the equivalence table} *)

val add_equivalence : KerName.t -> equivalence -> unit

val equivalence_exists : KerName.t -> bool

(** @raise Not_found if the equivalence does not exist *)
val equivalence_info : KerName.t -> equivalence

(** The declared equivalences, newest first *)
val equivalences : unit -> equivalence list

val subst_equivalence : Mod_subst.substitution -> equivalence -> equivalence

(** {6 Building equivalences, as in equiv.v} *)

(** The identity equivalence on an inductive *)
val erefl : inductive -> equivalence

(** The inverse equivalence *)
val einv : equivalence -> equivalence

(** [ecomp e1 e2] goes from [e1.eqv_indA] to [e2.eqv_indB], through
    [e1.eqv_indB = e2.eqv_indA] *)
val ecomp : equivalence -> equivalence -> equivalence

(** {6 Representatives} *)

(** [repr l ind] is the representative of [ind] with respect to the
    equivalences [l] (newest first), together with an equivalence from [ind] to
    it. Two inductives are related by [l] iff they have the same representative. *)
val repr : equivalence list -> inductive -> inductive * equivalence

(** The [repr] of every inductive appearing in [l]; the others are their own
    representative, through [erefl] *)
val repr_map : equivalence list -> (inductive * equivalence) Indmap_env.t
