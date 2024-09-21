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

Definition id_preservation_proof : forall X : FiniteInt, map_mor_1_to_2_mor X X PreorderExample1.(id) = PreorderExample2.(id).
Proof.
  induction X.
  destruct map_mor_1_to_2_mor.
  - apply proof_irrelevance.
  - apply proof_irrelevance.
  - apply proof_irrelevance.
  - apply proof_irrelevance.
Qed.

Definition comp_preservation_proof : forall (X Y Z : PreorderExample1.(Obj)) (f : Mor Y Z) (g : Mor X Y),
  map_mor_1_to_2_mor X Z (compose f g) =
  compose (map_mor_1_to_2_mor Y Z f) (map_mor_1_to_2_mor X Y g).
Proof.
  intros.
  induction X, Y, Z; 
  apply proof_irrelevance.
Qed.

Instance FunctorPreorderExample1to2 : Functor PreorderExample1 PreorderExample2 :=
  { map_obj := map_obj_1_to_2;
    map_mor := map_mor_1_to_2_mor;
    id_preservation := id_preservation_proof;
    comp_preservation := comp_preservation_proof
  }.
