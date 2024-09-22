Require Import Coq.Arith.Arith.
Require Import Coq.Logic.ProofIrrelevance.
Require Import HomFunctor.StructCategory.

Theorem leb_trans : forall X Y Z : nat, Nat.leb Y Z = true -> Nat.leb X Y = true -> Nat.leb X Z = true.
Proof.
  intros X Y Z H1 H2.
  apply Nat.leb_le in H1.
  apply Nat.leb_le in H2.
  apply Nat.leb_le.
  eapply Nat.le_trans; eauto.
Qed.

Definition leb_mor := fun X Y => { p : Nat.leb X Y = true | True }.

Theorem left_id_proof : forall (X Y : nat) (f : { p : Nat.leb X Y = true | True }), 
  exist _ (leb_trans X Y Y (Nat.leb_refl Y) (proj1_sig f)) I = f.
Proof.
  intros.
  apply proof_irrelevance.
Qed.

Theorem right_id_proof : forall (X Y : nat) (f : { p : Nat.leb X Y = true | True }), 
  exist _ (leb_trans X X Y (proj1_sig f) (Nat.leb_refl X)) I = f.
Proof.
  intros.
  apply proof_irrelevance.
Qed.

Theorem assoc_proof : forall (X Y Z W : nat) (f : { p : Nat.leb W X = true | True }) 
  (g : { p : Nat.leb X Y = true | True }) (h : { p : Nat.leb Y Z = true | True }),
  exist (fun _ : Nat.leb W Z = true => True)
    (leb_trans W Y Z (proj1_sig h)
       (proj1_sig
          (exist (fun _ : Nat.leb W Y = true => True)
             (leb_trans W X Y (proj1_sig g) (proj1_sig f)) I))) I =
  exist (fun _ : Nat.leb W Z = true => True)
    (leb_trans W X Z
       (proj1_sig
          (exist (fun _ : Nat.leb X Z = true => True)
             (leb_trans X Y Z (proj1_sig h) (proj1_sig g)) I)) 
       (proj1_sig f)) I.
Proof.
  intros.
  apply proof_irrelevance.
Qed.

Instance PreorderExample2 : LocallySmallCategory := {
  Obj := nat;
  
  (* Morphisms are proofs that Nat.leb X Y = true, wrapped in sig *)
  Mor := leb_mor;
  
  id := fun X => exist _ (Nat.leb_refl X) I;
  
  compose := fun X Y Z f g => exist _ (leb_trans X Y Z (proj1_sig f) (proj1_sig g)) I;
  
  left_identity := left_id_proof;
  right_identity := right_id_proof;
  associativity := assoc_proof;
}.
