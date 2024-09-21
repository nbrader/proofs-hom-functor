Require Import Coq.Logic.ProofIrrelevance.
Require Import HomFunctor.StructCategory.
Require Import HomFunctor.StructFunctor.
Require Import HomFunctor.CategorySet.

Variable C : Category.

Definition map_obj_hom (A : C.(Obj)) : CategorySet.(Obj) := CategorySet.(Mor) A.

(* Definition map_mor :  *)
(* Definition id_preservation_proof :  *)
(* Definition comp_preservation_proof :  *)

Instance HomFunctor : Functor C CategorySet :=
  { map_obj := map_obj_hom;
    map_mor := map_mor_1_to_2_mor;
    id_preservation := id_preservation_proof;
    comp_preservation := comp_preservation_proof
  }.
