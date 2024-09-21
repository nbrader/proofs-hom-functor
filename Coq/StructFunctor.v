Require Import HomFunctor.StructCategory.

Class Functor (C D : Category) := {
  map_obj : forall (X : C.(Obj)), D.(Obj);  (* Object mapping from C to D *)
  map_mor : forall {X Y : C.(Obj)} (f : C.(Mor) X Y), D.(Mor) (map_obj X) (map_obj Y);  (* Morphism mapping *)

  (* Functoriality proofs *)
  id_preservation : forall (X : C.(Obj)), @map_mor X X (C.(@id) X) = D.(@id) (map_obj X);
  comp_preservation : forall {X Y Z : C.(Obj)} (f : C.(Mor) Y Z) (g : C.(Mor) X Y), 
    map_mor (C.(compose) f g) = D.(compose) (map_mor f) (map_mor g);
}.