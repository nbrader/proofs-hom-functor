Require Import Coq.Arith.Arith.
Require Import Coq.Logic.ProofIrrelevance.
Require Import HomFunctor.StructCategory.

(* Example of a finite category based on the integers 0-3 *)
Inductive FiniteInt : Type :=
  | zero  : FiniteInt
  | one   : FiniteInt
  | two   : FiniteInt
  | three : FiniteInt.

Definition leq_pred (x y : FiniteInt) : bool :=
  match x, y with
  | zero, _ => true
  | one, one | one, two | one, three => true
  | two, two | two, three => true
  | three, three => true
  | _, _ => false
  end.

Definition leq (x y : FiniteInt) := leq_pred x y = true.

Theorem leq_refl (x : FiniteInt) : leq x x.
Proof.
  unfold leq; induction x; auto.
Qed.

Definition leq_trans (x y z : FiniteInt) (f : leq y z) (g : leq x y) : leq x z.
Proof.
  case x, y, z; simpl; try (apply (leq_refl zero) || inversion f || inversion g).
Defined.

Lemma left_identity_proof : forall (x y : FiniteInt) (f : leq x y), @leq_trans x y y (leq_refl y) f = f.
Proof.
  intros.
  apply proof_irrelevance.
Qed.

Lemma right_identity_proof : forall (x y : FiniteInt) (f : leq x y), @leq_trans x x y f (leq_refl x) = f.
Proof.
  intros.
  apply proof_irrelevance.
Qed.

Lemma associativity_proof : forall (x y z w : FiniteInt) (f : leq w x) (g : leq x y) (h : leq y z),
                  leq_trans w y z h (leq_trans w x y g f) = leq_trans w x z (leq_trans x y z h g) f.
Proof.
  intros.
  apply proof_irrelevance.
Qed.

Instance PreorderExample1 : LocallySmallCategory := {
  Obj := FiniteInt;
  Mor := leq;

  id := leq_refl;
  compose := leq_trans;

  left_identity := left_identity_proof;
  right_identity := right_identity_proof;
  associativity := associativity_proof;
}.
