Require Import Coq.Arith.Arith.
Require Import Coq.Logic.ProofIrrelevance.
Require Import HomFunctor.StructCategory.

(* Example of a finite category based on the integers 0-3 *)
Inductive FiniteInt : Type :=
  | zero  : FiniteInt
  | one   : FiniteInt
  | two   : FiniteInt
  | three : FiniteInt.

Definition leq (x y : FiniteInt) : Prop :=
  match x, y with
  | zero, _ => True
  | one, one | one, two | one, three => True
  | two, two | two, three => True
  | three, three => True
  | _, _ => False
  end.

Definition leq_refl (x : FiniteInt) : leq x x :=
  match x return leq x x with
  | zero => I
  | one => I
  | two => I
  | three => I
  end.

Definition leq_trans (x y z : FiniteInt) (f : leq y z) (g : leq x y) : leq x z.
Proof.
  case x, y, z; simpl; try (apply (leq_refl zero) || inversion f || inversion g).
Defined.

Lemma left_identity_proof : forall (x y : FiniteInt) (f : leq x y), @leq_trans x y y (leq_refl y) f = f.
Proof.
  intros x y f.
  unfold leq_refl, leq_trans.
  destruct x, y; simpl in *;
  try reflexivity;
  try contradiction; apply proof_irrelevance.
Qed.

Lemma right_identity_proof : forall (x y : FiniteInt) (f : leq x y), @leq_trans x x y f (leq_refl x) = f.
Proof.
  intros x y f.
  unfold leq_refl, leq_trans.
  destruct x, y; simpl in *;
  try reflexivity;
  try contradiction; apply proof_irrelevance.
Qed.

Lemma associativity_proof : forall (x y z w : FiniteInt) (f : leq w x) (g : leq x y) (h : leq y z),
                  leq_trans w y z h (leq_trans w x y g f) = leq_trans w x z (leq_trans x y z h g) f.
Proof.
  intros.
  unfold leq_refl, leq_trans.
  destruct x, y; simpl in *;
  try reflexivity;
  try contradiction; apply proof_irrelevance.
Qed.

Instance PreorderExample1 : Category := {
  Obj := FiniteInt;
  Mor := leq;

  id := leq_refl;
  compose := leq_trans;

  left_identity := left_identity_proof;
  right_identity := right_identity_proof;
  associativity := associativity_proof;
}.
