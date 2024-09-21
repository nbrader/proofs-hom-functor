Require Import Coq.Logic.ProofIrrelevance.
Require Import HomFunctor.StructCategory.
Require Import HomFunctor.StructFunctor.
Require Import HomFunctor.PreorderExample1.
Require Import HomFunctor.PreorderExample2.

Definition map_obj_1_to_2 : PreorderExample1.(Obj) -> PreorderExample2.(Obj) :=
  fun x => match x with
    | zero  => 0
    | one   => 1
    | two   => 2
    | three => 3
  end.

Definition map_mor_1_to_2 (X Y : FiniteInt) (f : leq X Y) : le (map_obj_1_to_2 X) (map_obj_1_to_2 Y).
Proof.
  induction X, Y; simpl; auto; unfold leq in f; unfold leq_pred in f; discriminate.
Qed.

Definition leb_mor := fun X Y => { p : Nat.leb X Y = true | True }.

Definition map_mor_1_to_2_mor (X Y : FiniteInt) (f : leq X Y) : leb_mor (map_obj_1_to_2 X) (map_obj_1_to_2 Y).
Proof.
  unfold leb_mor.
  unfold map_obj_1_to_2.
  induction X, Y.
  simpl.
  first [ exact (exist _ eq_refl I) | (unfold leq in f; simpl in f; discriminate) ].
  first [ exact (exist _ eq_refl I) | (unfold leq in f; simpl in f; discriminate) ].
  first [ exact (exist _ eq_refl I) | (unfold leq in f; simpl in f; discriminate) ].
  first [ exact (exist _ eq_refl I) | (unfold leq in f; simpl in f; discriminate) ].
  first [ exact (exist _ eq_refl I) | (unfold leq in f; simpl in f; discriminate) ].
  first [ exact (exist _ eq_refl I) | (unfold leq in f; simpl in f; discriminate) ].
  first [ exact (exist _ eq_refl I) | (unfold leq in f; simpl in f; discriminate) ].
  first [ exact (exist _ eq_refl I) | (unfold leq in f; simpl in f; discriminate) ].
  first [ exact (exist _ eq_refl I) | (unfold leq in f; simpl in f; discriminate) ].
  first [ exact (exist _ eq_refl I) | (unfold leq in f; simpl in f; discriminate) ].
  first [ exact (exist _ eq_refl I) | (unfold leq in f; simpl in f; discriminate) ].
  first [ exact (exist _ eq_refl I) | (unfold leq in f; simpl in f; discriminate) ].
  first [ exact (exist _ eq_refl I) | (unfold leq in f; simpl in f; discriminate) ].
  first [ exact (exist _ eq_refl I) | (unfold leq in f; simpl in f; discriminate) ].
  first [ exact (exist _ eq_refl I) | (unfold leq in f; simpl in f; discriminate) ].
  first [ exact (exist _ eq_refl I) | (unfold leq in f; simpl in f; discriminate) ].
Qed.

Definition true_eq : true = true := eq_refl.

Definition true_eq_sig : { p : true = true | True } :=
  exist _ true_eq I.

Definition true_eq_sig_to_eq (s : { p : true = true | True }) : true = true :=
  proj1_sig s.

Definition eq_to_true_eq_sig (p : true = true) : { p' : true = true | True } :=
  exist _ p I.

Theorem true_eq_isomorphism : (true = true) <-> { _ : true = true | True }.
Proof.
  split.
  - (* From true = true to the dependent pair *)
    intro H.
    apply eq_to_true_eq_sig in H.
    exact H.

  - (* From the dependent pair to true = true *)
    intro H.
    apply true_eq_sig_to_eq in H.
    exact H.
Qed.

Definition id_preservation_proof (X : FiniteInt) : leq X X = leb_mor (map_obj_1_to_2 X) (map_obj_1_to_2 X).
Proof.
  induction X; simpl; unfold leq; unfold leb_mor; simpl.
  
(*
Goal 1

(1 / 4)
(true = true) = {_ : true = true | True}
Goal 2

(2 / 4)
(true = true) = {_ : true = true | True}
Goal 3

(3 / 4)
(true = true) = {_ : true = true | True}
Goal 4

(4 / 4)
(true = true) = {_ : true = true | True}
*)
Admitted.

Definition comp_preservation_proof (X Y Z : FiniteInt) (f : leq Y Z) (g : leq X Y) : 
  map_mor_1_to_2 (compose g f) = le (map_obj_1_to_2 X) (map_obj_1_to_2 Z).
Proof.
Admitted.

Instance FunctorPreorderExample1to2 : Functor PreorderExample1 PreorderExample2 :=
  { map_obj := map_obj_1_to_2;
    map_mor := map_mor_1_to_2_mor;
    id_preservation := id_preservation_proof;
    comp_preservation := comp_preservation_proof
  }.
