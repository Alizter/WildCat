(* -*- mode: coq; mode: visual-line -*-  *)

From HoTT Require Import Basics.
From WildCat Require Import Basics.
From WildCat Require Export Cat0.

Generalizable Variables m n p A B C.

(** * Equivalences of categories *)

Class EssSplit {m A n B} `{IsCat0 m A, HasEquivs n B}
      (F : A -> B) `{!IsFunctor0 F} :=
{
  esssplit_obj : B -> A ;
  esssplit_cate : forall a, F (esssplit_obj a) $<~> a ;
}.

CoInductive IsEquivCat {m A n B} `{IsCat0 m A, HasEquivs n B}
            (F : A -> B) `{!IsFunctor0 F} :=
{
  isequivcat_esssplit : EssSplit F ;
  isequivcat_hom : forall (a b : A),
      @IsEquivCat (pred m) (a $-> b) (pred n) (F a $-> F b)
                  _ _ _ _ _ (fmap F) _;
}.
