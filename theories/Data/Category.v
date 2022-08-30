Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.

Module Categories.

  Set Primitive Projections.

  Polymorphic Record Funktor (D : Category) (C : Category) : Type :=
    { map_ob : D -----> C
    ; map_hom : @isCovariantFunctor D C map_ob
    }
  .

  Unset Primitive Projections.

  Global Arguments map_ob {D} {C}.
  Global Arguments map_hom {D} {C}.

  Global Infix " ---> " := Funktor (at level 100, no associativity) : type_scope.

  Polymorphic Definition NaturalTransformation {D} {C} (F : D ---> C) (F' : D ---> C) : Type :=
    @isNaturalTransformation D C F.(map_ob) F'.(map_ob)
  .

  Global Infix " ===> " := NaturalTransformation (at level 100, no associativity) : type_scope.

  Polymorphic Definition composeFunktor {C} {C'} {C''} (F2 : C' ---> C'') (F1 : C ---> C') : C ---> C'' :=
    {|
      map_ob := fun X => map_ob F2 (map_ob F1 X);
      map_hom := {| Cat.fmap A B (f : C.(hom) A B) := Cat.fmap (isCovariantFunctor := map_hom F2) (Cat.fmap (isCovariantFunctor := map_hom F1) f) |};
    |}
  .

  Polymorphic Definition idFunktor {C} : C ---> C :=
    {|
      map_ob := fun X => X;
      map_hom := {| Cat.fmap A B (f : C.(hom) A B) := f |};
    |}
  .

  Section INSTANCES_OF_CATEGORY.

  Local Polymorphic Instance OppositeCategory (cat : Category) : Category :=
    { ob := cat.(ob)
    ; hom B A := cat.(hom) A B
    ; compose {C} {B} {A} f1 f2 := cat.(compose) f2 f1
    ; id {A} := cat.(id)
    }
  .

  Local Polymorphic Instance CategoryOfCategories : Category :=
    { ob := Category
    ; hom D C := D ---> C
    ; compose {C} {C'} {C''} := composeFunktor (C := C) (C' := C') (C'' := C'')
    ; id {C} := idFunktor (C := C)
    }
  .

  Local Polymorphic Instance CategoryOfFunktors {D : Category} {C : Category} : Category :=
    { ob := Funktor D C
    ; hom F F' := F ===> F'
    ; compose {F} {F'} {F''} eta2 eta1 := fun X => compose (eta2 X) (eta1 X)
    ; id {F} := fun X => id
    }
  .

  End INSTANCES_OF_CATEGORY.

  Section CATEGORICAL_SUM.

  Polymorphic Class hasCoproduct (cat : Category) : Type :=
    { Sum (obj_l : cat.(ob)) (obj_r : cat.(ob)) : cat.(ob)
    ; Inl {obj_l : cat.(ob)} {obj_r : cat.(ob)} : cat.(hom) (obj_l) (Sum obj_l obj_r)
    ; Inr {obj_l : cat.(ob)} {obj_r : cat.(ob)} : cat.(hom) (obj_r) (Sum obj_l obj_r)
    ; Case {obj_l : cat.(ob)} {obj_r : cat.(ob)} {obj : cat.(ob)} (fl : cat.(hom) (obj_l) obj) (fr : cat.(hom) (obj_r) obj) : cat.(hom) (Sum obj_l obj_r) obj
    }
  .

  Polymorphic Definition coproduct_bimap {cat : Category} {coproduct : hasCoproduct cat} {obj1 : cat} {obj1' : cat} {obj2 : cat} {obj2' : cat} (arr1 : hom obj1 obj1') (arr2 : hom obj2 obj2') : hom (Sum obj1 obj2) (Sum obj1' obj2') :=
    Case (compose Inl arr1) (compose Inr arr2)
  .

  Local Instance Hask_hasCoproduct : hasCoproduct Hask.cat :=
    { Sum := sum
    ; Inl {A : Type} {B : Type} := @inl A B
    ; Inr {A : Type} {B : Type} := @inr A B
    ; Case {A : Type} {B : Type} {C : Type} := @sum_rect _ _ (fun _ : A + B => C)
    }
  .

  End CATEGORICAL_SUM.

  Section INITIAL_OBJECT.

  Polymorphic Class hasInitial (cat : Category) : Type :=
    { Void : cat.(ob)
    ; ExFalso {obj : cat.(ob)} : cat.(hom) Void obj
    }
  .

  Local Instance Hask_hasInitial : hasInitial Hask.cat :=
    { Void := Empty_set
    ; ExFalso {A : Type} := @Empty_set_rect (fun _ : Empty_set => A)
    }
  .

  End INITIAL_OBJECT.

End Categories.
