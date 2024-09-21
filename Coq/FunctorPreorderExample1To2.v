Require Import Coq.Logic.ProofIrrelevance.
Require Import HomFunctor.StructCategory.
Require Import HomFunctor.StructFunctor.
Require Import HomFunctor.PreorderExample1.
Require Import HomFunctor.PreorderExample2.

(* Theorem bool_nat_eq : (true = true) = (Nat.leb 0 0 = true).
Proof.
  reflexivity.
Qed. *)

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

Definition id_preservation_proof (X : FiniteInt) : leq X X = le (map_obj_1_to_2 X) (map_obj_1_to_2 X).
Proof.
  induction X; simpl; unfold leq; simpl.
Qed.

Definition comp_preservation_proof (X Y Z : FiniteInt) (f : leq Y Z) (g : leq X Y) : 
  map_mor_1_to_2 (compose g f) = le (map_obj_1_to_2 X) (map_obj_1_to_2 Z).
Proof.
  (* You will need to show that the composition of morphisms is preserved *)
  (* Replace this with your actual proof *)
  reflexivity.
Qed.

Instance FunctorPreorderExample1to2 : Functor PreorderExample1 PreorderExample2 :=
  { map_obj := map_obj_1_to_2;
    map_mor := map_mor_1_to_2;
    id_preservation := id_preservation_proof;
    comp_preservation := comp_preservation_proof
  }.
