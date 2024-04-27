Require Import Coq.Arith.Arith.
Require Import Coq.Logic.ProofIrrelevance.

(* Definition of a category using Class *)
Class Category := {
  Obj : Type;  (* Type of objects in the category *)
  Mor : Obj -> Obj -> Type;  (* Type of morphisms between objects *)
  
  id : forall {X}, Mor X X;  (* Identity morphism *)
  compose : forall {X Y Z}, Mor Y Z -> Mor X Y -> Mor X Z;  (* Composition of morphisms *)

  left_identity : forall {X Y} (f : Mor X Y), compose id f = f;
  right_identity : forall {X Y} (f : Mor X Y), compose f id = f;
  associativity : forall {X Y Z W} (f : Mor W X) (g : Mor X Y) (h : Mor Y Z),
                  compose h (compose g f) = compose (compose h g) f
}.

(* Example of a finite category based on the finite integers 0-3 *)
Inductive FiniteInt : Type :=
  | zero  : FiniteInt
  | one   : FiniteInt
  | two   : FiniteInt
  | three : FiniteInt.

(* We will redefine the leq relation slightly for clarity, assuming it was initially defined as you described. *)
Definition leq (x y : FiniteInt) : Prop :=
  match x, y with
  | zero, _ => True
  | one, one | one, two | one, three => True
  | two, two | two, three => True
  | three, three => True
  | _, _ => False
  end.

(* Let's redefine the reflexivity proofs to directly use propositional proofs instead of I, since I does not satisfy the expected type leq x x for non-zero cases. *)
Definition leq_refl (x : FiniteInt) : leq x x :=
  match x return leq x x with
  | zero => I
  | one => I
  | two => I
  | three => I
  end.

(* Define transitivity proof, respecting the actual values of x, y, z, and handling the proof objects explicitly *)
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

(* Use these lemmas in your Category instance *)
Instance PreorderCategory : Category := {
  Obj := FiniteInt;
  Mor := leq;

  id := leq_refl;
  compose := leq_trans;

  left_identity := left_identity_proof;
  right_identity := right_identity_proof;
  associativity := associativity_proof;
}.
