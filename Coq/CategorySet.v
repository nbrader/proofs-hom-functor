Require Import Coq.Arith.Arith.
Require Import Coq.Logic.ProofIrrelevance.
Require Import HomFunctor.StructCategory.
Require Import Coq.Program.Basics.
Require Import Coq.Init.Datatypes.

Definition Func (X Y : Set) : Type := X -> Y.

Definition idFunc (X : Set) : Func X X := fun x => x.

Lemma left_identity_proof : forall (X Y : Set) (f : Func X Y), compose (idFunc Y) f = f.
Proof.
  intros.
  auto.
Qed.

Lemma right_identity_proof : forall (X Y : Set) (f : Func X Y), compose f (idFunc X) = f.
Proof.
  intros.
  auto.
Qed.

Lemma associativity_proof : forall (X Y Z W : Set) (f : Func W X) (g : Func X Y) (h : Func Y Z),
  compose h (compose g f) = compose (compose h g) f.
Proof.
  intros.
  auto.
Qed.

Instance CategorySet : Category := {
  Obj := Set;
  Mor := Func;

  id := idFunc;
  compose := @compose;

  left_identity := left_identity_proof;
  right_identity := right_identity_proof;
  associativity := associativity_proof;
}.
