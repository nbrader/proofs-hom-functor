Require Import Coq.Logic.ProofIrrelevance.
Require Import HomFunctor.StructCategory.
Require Import HomFunctor.StructFunctor.
Require Import HomFunctor.StructCofunctor.
Require Import HomFunctor.CategorySet.
Require Import Coq.Logic.FunctionalExtensionality.

Variable C : LocallySmallCategory.

Definition map_obj_hom (A X : C.(Obj)) : CategorySet.(Obj) := C.(Mor) X A.

(* Postcomposition function that maps a morphism in C to a function between hom-sets *)
Definition map_mor_hom {A X1 X2 : C.(Obj)} (f : C.(Mor) X1 X2) :
  C.(Mor) X2 A -> C.(Mor) X1 A :=
  fun g => compose g f.

(* Proof that the functor preserves identities *)
Definition id_preservation_proof {A : C.(Obj)} :
  forall (X : C.(Obj)), map_mor_hom (@id _ X) = @id _ (map_obj_hom A X).
Proof.
  intros X. unfold map_obj_hom, map_mor_hom.
  extensionality g. (* Use functional extensionality *)
  rewrite right_identity.
  unfold id.
  simpl.
  unfold idFunc.
  reflexivity.
Qed.

(* Proof that the functor preserves composition *)
Definition comp_preservation_proof {A : C.(Obj)} :
  forall (X1 X2 X3 : C.(Obj)) (f : C.(Mor) X2 X3) (g : C.(Mor) X1 X2),
    @map_mor_hom A _ _ (compose f g) = compose (map_mor_hom g) (map_mor_hom f).
Proof.
  intros. unfold map_mor_hom.
  extensionality h. (* Use functional extensionality *)
  apply associativity.
Qed.

(* Final definition of the HomFunctor instance *)
Instance HomFunctor (A : C.(Obj)) : Cofunctor C CategorySet := {
  map_obj := map_obj_hom A;
  map_mor := @map_mor_hom A;
  id_preservation := id_preservation_proof;
  comp_preservation := comp_preservation_proof
}.