(* -*- mode: coq; mode: visual-line -*-  *)

From HoTT Require Import Basics Cubical.DPath.
From WildCat Require Import Basics Cat1.

Generalizable Variables A B.

(** * Path oo-groupoids *)

(** Every type is a globular type with its tower of identity types. *)
CoFixpoint isglob_withpaths (A : Type) : IsGlob 0 A.
Proof.
  exists (@paths A); intros.
  apply isglob_withpaths.
Defined.

(** We could make this a global but low-priority instance, but doing so seems to break stuff later. *)
(* Global Existing Instance isglob_withpaths | 1000. *)
Local Existing Instance isglob_withpaths.

(** Any function is a 0-coherent oo-functor between types equipped with their globular tower of identity types.  As for [isglob_withpaths], we don't make this an [Instance]. *)
CoFixpoint isfunctor0_withpaths {A B : Type} (F : A -> B)
  : IsFunctor0 F.
Proof.
  refine (Build_IsFunctor0 F _ _).
  exact (@ap A B F).
  (** The coinductive assumption is found by typeclass search. *)
Defined.

Local Existing Instance isfunctor0_withpaths.

(** The tower of identity types is a 0-coherent oo-category with path composition.  Again, not an [Instance]. *)
CoFixpoint iscat0_withpaths (A : Type) : IsCat0 0 A.
Proof.
  unshelve econstructor.
  - intros a b c p q; exact (q @ p).
  - intros a; exact idpath.
  - intros; cbn; apply isfunctor0_withpaths.
  - intros; cbn; apply isfunctor0_withpaths.
  - intros ? a b f; exact (f^).
  - intros; apply iscat0_withpaths.
Defined.

Local Existing Instance iscat0_withpaths.

(** Any dependent type is a displayed 0-coherent oo-category with its tower of dependent identity types. *)

CoFixpoint isdglob_withpaths (A : Type) (P : A -> Type) : IsDGlob 0 P.
Proof.
  exists (@DPath A P); intros.
  apply isdglob_withpaths.
Defined.

Local Existing Instance isdglob_withpaths.

(** Any function is a 0-coherent oo-functor between types equipped with their globular tower of identity types.  As for [isglob_withpaths], we don't make this an [Instance]. *)
CoFixpoint isdfunctor0_withpaths {A B : Type} {P : A -> Type} {Q : B -> Type}
  (F : A -> B) (F' : forall x, P x -> Q (F x))
  : IsDFunctor0 F F'.
Proof.
  construct.
  { intros a b u v f p.
    destruct f.
    cbn in *.
    exact (ap _ p). }
  exact _.
  (** The coinductive assumption is found by typeclass search. *)
Defined.

CoFixpoint isdcat0_withpaths (A : Type) (B : A -> Type) : IsDCat0 0 B.
Proof.
  construct.
  - intros a b c x y z p q u v; exact (dp_concat v u).
  - intros a u; exact dp_id.
  - intros; cbn; apply isdfunctor0_withpaths.
  - intros; cbn; apply isdfunctor0_withpaths.
  - intros ? a b u v f ? p.
Abort.

(** Every path is a quasi-isomorphism. *)
CoFixpoint isqiso_withpaths {A : Type} {a b : A} (p : a = b)
  : IsQIso p.
Proof.
  unshelve econstructor.
  - exact (p^).
  - cbn. apply concat_pV.
  - cbn. apply concat_Vp.
  - apply isqiso_withpaths.
  - apply isqiso_withpaths.
Defined.

Local Existing Instance isqiso_withpaths.

(** We can't use IsCat1_Default since we want to specify our notion of equivalence. Which in this case, happens to be a path. *)
CoFixpoint hasequivs_withpaths {A : Type} : HasEquivs 0 A.
Proof.
  snrapply Build_HasEquivs.
  1: exact (fun a b f => Unit).
  1: hnf; trivial.
  1: intros; exact _.
  cbn; intros a b.
  exact _.
Defined.

Local Existing Instance hasequivs_withpaths.

Lemma cate_promote_withpaths {A : Type} (x y : A) : x $== y -> x $<~> y.
Proof.
  intros f.
  snrapply (Build_CatEquiv f).
  constructor.
Defined.

(** Any function is a 1-coherent oo-functor between types equipped with their globular tower of identity types. *)
CoFixpoint isfunctor1_withpaths {A B : Type} (F : A -> B)
  : IsFunctor1 F.
Proof.
  srapply Build_IsFunctor1.
  1,2: hnf; intros; rapply cate_promote_withpaths.
  1: reflexivity.
  rapply ap_pp.
Defined.

Local Existing Instance isfunctor1_withpaths.

(** 1-coherent functors, 1-coherent categories *)
CoFixpoint iscat1_withpaths {A : Type} : IsCat1 0 A.
Proof.
  snrapply Build_IsCat1.
  1-5: hnf; intros; rapply cate_promote_withpaths.
  1: exact (concat_p_pp _ _ _).
  1: exact (concat_p1 _).
  1: exact (concat_1p _).
  1: exact (concat_pV _).
  1: exact (concat_Vp _).
  1,2: exact _.
  cbn; intros.
  apply iscat1_withpaths.
Defined.
