(* -*- mode: coq; mode: visual-line -*-  *)

From HoTT Require Import Basics.
From WildCat Require Import Cat1 Paths Forall.

(** * The oo-category of types *)

(** The universe is a globular type with functions, homotopies, and higher homotopies.  We obtain this by putting together path-groupoids with forall-categories. *)

(** The universe is a globular type *)
Global Instance isglob_type : IsGlob 1 Type
  := Build_IsGlob
       1 Type (fun A B => A -> B)
       (fun A B => isglob_forall (const B) (fun _ => isglob_withpaths B)).

(** The universe is a 0-coherent (oo,1)-category. *)
Global Instance iscat0_type : IsCat0 1 Type.
Proof.
  unshelve econstructor.
  - intros A B C g f; exact (g o f).
  - intros A; exact idmap.
  - intros A B C g; cbn.
    apply isfunctor0_postcompose.
    intros; apply isfunctor0_withpaths.
  - intros A B C f; cbn.
    rapply isfunctor0_precompose.
  - intros [].
  - intros A B.
    rapply iscat0_forall. 
    intros; rapply iscat0_withpaths.
Defined.

Global Existing Instances iscat0_type.

Global Instance iscat1_default_type : IsCat1_Default 1 Type.
Proof.
  constructor.
  constructor.
  - intros A B C D f g h.
    (** This doesn't seem to be the correct notion of equivalence. *)  
Admitted.
