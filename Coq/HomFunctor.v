Require Import HomFunctor.StructCategory.
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
  forall (X : C.(Obj)), map_mor_hom (@id _ X) = @id _ (map_obj_hom A X) :=
  fun X =>
    functional_extensionality
      (fun g => map_mor_hom (@id _ X) g)
      (fun g => @id _ (map_obj_hom A X) g)
      (fun g => eq_ind _ _ eq_refl _ (right_identity g)).

(* Proof that the functor preserves composition *)
Definition comp_preservation_proof {A : C.(Obj)} :
  forall (X1 X2 X3 : C.(Obj)) (f : C.(Mor) X2 X3) (g : C.(Mor) X1 X2),
    map_mor_hom (compose f g) = compose (map_mor_hom g) (map_mor_hom f) :=
  fun X1 X2 X3 f g =>
    functional_extensionality
      (fun g0 : C.(Mor) X3 A => compose g0 (compose f g))
      (fun g0 : C.(Mor) X3 A => compose (compose g0 f) g)
      (fun h : C.(Mor) X3 A => associativity g f h).

(* Final definition of the HomFunctor instance *)
Instance HomFunctor (A : C.(Obj)) : Cofunctor C CategorySet := {
  map_obj := map_obj_hom A;
  map_mor := @map_mor_hom A;
  id_preservation := id_preservation_proof;
  comp_preservation := comp_preservation_proof
}.
