From HoTT Require Import Basics.
From HoTT Require Export Spaces.Nat.
From HoTT Require Export Types.Bool.
From WildCat Require Export Notations.

Local Open Scope nat_scope.

(** * Basics *)

Ltac construct := unshelve econstructor.

Notation "n .-1" := (pred n) : nat_scope.

(** ** Coinductive streams *)

CoInductive Stream (A : Type) := scons
{
  head : A ;
  tail : Stream A
}.

Arguments scons {A} _ _.
Arguments head {A} _.
Arguments tail {A} _.

CoFixpoint const_stream {A} (a : A) : Stream A
  := scons a (const_stream a).


(** *** Typeclasses for case analysis *)

(** Versions of [n = 0] and [n > 0] that are typeclasses and can be found automatically. *)
Definition IsZeroNat (n : nat) : Type :=
  match n with
  | O => Unit
  | S _ => Empty
  end.
Existing Class IsZeroNat.
Global Instance iszeronat : IsZeroNat 0 := tt.

Definition IsPosNat (n : nat) : Type :=
  match n with
  | O => Empty
  | S _ => Unit
  end.
Existing Class IsPosNat.
Global Instance isposnat (n : nat) : IsPosNat (S n) := tt.

Definition IsTrue (b : Bool) : Type :=
  match b with
  | true => Unit
  | false => Empty
  end.
Existing Class IsTrue.
Global Instance istrue : IsTrue true := tt.

Definition IsFalse (b : Bool) : Type :=
  match b with
  | true => Empty
  | false => Unit
  end.
Existing Class IsFalse.
Global Instance isfalse : IsFalse false := tt.

(** * Path Groupoids *)

Definition inv_concat2 {A} {x y z : A} {p q : x = y} {r s : y = z}
           {h : p = q} {k : r = s}
  : (h @@ k)^ = h^ @@ k^.
Proof.
  path_induction; reflexivity.
Defined.

(** [concat2] can equivalently be defined in terms of whiskering. *)
Definition concat2_is_whiskerL_whiskerR
           {A} {x y z : A} {p q : x = y} {r s : y = z}
           {h : p = q} {k : r = s}
  : (h @@ k) = (h @@ idpath) @ (idpath @@ k).
Proof.
  by destruct h, k.
Defined.

(** In two ways. *)
Definition concat2_is_whiskerR_whiskerL
           {A} {x y z : A} {p q : x = y} {r s : y = z}
           {h : p = q} {k : r = s}
  : (h @@ k) = (idpath @@ k) @ (h @@ idpath).
Proof.
  by destruct h, k.
Defined.

(** And whiskering can equivalently be defined in terms of [ap]. *)
Definition ap_concat_r {A} {x y z : A} {p q : x = y} (s : p = q) (r : y = z)
  : ap (fun t => t @ r) s = whiskerR s r.
Proof.
  by destruct s.
Defined.

Definition ap_concat_l {A} {x y z : A} (p : x = y) {q r : y = z} (s : q = r)
  : ap (fun t => p @ t) s = whiskerL p s.
Proof.
  by destruct s.
Defined.

(** * Trunc *)

(** A version of [n = -2] that's a typeclass. *)
Definition IsMinusTwo (n : trunc_index) : Type :=
  match n with
  | minus_two => Unit
  | trunc_S _ => Empty
  end.
Existing Class IsMinusTwo.
Global Instance isminustwo : IsMinusTwo (-2) := tt.

