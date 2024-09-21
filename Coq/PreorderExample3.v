Require Import Coq.Arith.Arith.
Require Import Coq.Logic.ProofIrrelevance.
Require Import HomFunctor.StructCategory.

Theorem le_trans : forall X Y Z : nat, Y <= Z -> X <= Y -> X <= Z.
Proof.
  induction 2; auto.
  apply IHle.
  induction Z.
  - apply Nat.nle_succ_0 in H.
    contradiction.
  - apply Nat.lt_le_incl in H.
    apply H.
Qed.

Theorem left_id_proof : forall (X Y : nat) (f : X <= Y), le_trans X Y Y (Nat.le_refl Y) f = f.
Proof.
  intros; apply proof_irrelevance.
Qed.

Theorem right_id_proof : forall (X Y : nat) (f : X <= Y), le_trans X X Y f (Nat.le_refl X) = f.
Proof.
  intros; apply proof_irrelevance.
Qed.

Theorem assoc_proof : forall (X Y Z W : nat) (f : W <= X) (g : X <= Y) (h : Y <= Z),
  le_trans W Y Z h (le_trans W X Y g f) =
  le_trans W X Z (le_trans X Y Z h g) f.
Proof.
  intros; apply proof_irrelevance.
Qed.


Instance PreorderExample3 : Category := {
  Obj := nat;
  Mor := le;

  id := Nat.le_refl;
  compose := le_trans;

  left_identity := left_id_proof;
  right_identity := right_id_proof;
  associativity := assoc_proof;
}.