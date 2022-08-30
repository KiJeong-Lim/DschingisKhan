Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.

Module Categories.

  Section INSTANCES_OF_CATEGORY.

  Local Polymorphic Instance CategoryOfCategories : isCategory :=
    { Ob := isCategory
    ; hom D C := D -----> C
    ; compose {C} {C'} {C''} f2 f1 := fun X => f2 (f1 X)
    ; id {C} := fun X => X
    }
  .

  Local Polymorphic Instance CategoryOfFunctors {src : isCategory} {tgt : isCategory} : isCategory :=
    { Ob := src -----> tgt
    ; hom F F' := F =====> F'
    ; compose {F} {F'} {F''} f2 f1 := fun X => compose (f2 X) (f1 X)
    ; id {F} := fun X => id
    }
  .

  Local Instance HaskEndo : isCategory := CategoryOfFunctors (src := Hask.cat) (tgt := Hask.cat).

  End INSTANCES_OF_CATEGORY.

  Section CATEGORICAL_SUM.

  Polymorphic Class hasCoproduct (cat : isCategory) : Type :=
    { Sum (obj_l : cat.(Ob)) (obj_r : cat.(Ob)) : cat.(Ob)
    ; Inl {obj_l : cat.(Ob)} {obj_r : cat.(Ob)} : cat.(hom) (obj_l) (Sum obj_l obj_r)
    ; Inr {obj_l : cat.(Ob)} {obj_r : cat.(Ob)} : cat.(hom) (obj_r) (Sum obj_l obj_r)
    ; Case {obj_l : cat.(Ob)} {obj_r : cat.(Ob)} {obj : cat.(Ob)} (left : cat.(hom) (obj_l) obj) (right : cat.(hom) (obj_r) obj) : cat.(hom) (Sum obj_l obj_r) obj
    }
  .

  Polymorphic Definition coproduct_bimap {cat : isCategory} {coproduct : hasCoproduct cat} {obj1 : Ob} {obj1' : Ob} {obj2 : Ob} {obj2' : Ob} (arr1 : hom obj1 obj1') (arr2 : hom obj2 obj2') : hom (Sum obj1 obj2) (Sum obj1' obj2') :=
    Case (compose Inl arr1) (compose Inr arr2)
  .

  Local Instance Hask_hasCoproduct : hasCoproduct Hask.cat :=
    { Sum := sum
    ; Inl {A : Type} {B : Type} := @inl A B
    ; Inr {A : Type} {B : Type} := @inr A B
    ; Case {A : Type} {B : Type} {C : Type} := @sum_rect _ _ (fun _ : A + B => C)
    }
  .

  Local Instance HaskEndo_hasCoproduct : hasCoproduct HaskEndo :=
    { Sum := sum1
    ; Inl {FL : Type -> Type} {FR : Type -> Type} := fun X : Type => inl1 (FL := FL) (FR := FR) (X := X)
    ; Inr {FL : Type -> Type} {FR : Type -> Type} := fun X : Type => inr1 (FL := FL) (FR := FR) (X := X)
    ; Case {FL : Type -> Type} {FR : Type -> Type} {F : Type -> Type} (f1 : FL ~~> F) (f2 : FR ~~> F) := fun X : Type => @sum1_rect _ _ _ (fun _ : sum1 FL FR X => F X) (f1 X) (f2 X)
    }
  .

  End CATEGORICAL_SUM.

  Section INITIAL_OBJECT.

  Polymorphic Class hasInitial (cat : isCategory) : Type :=
    { Void : cat.(Ob)
    ; ExFalso {obj : cat.(Ob)} : cat.(hom) Void obj
    }
  .

  Local Instance Hask_hasInitial : hasInitial Hask.cat :=
    { Void := Empty_set
    ; ExFalso {A : Type} := @Empty_set_rect (fun _ : Empty_set => A)
    }
  .

  Local Instance HaskEndo_hasInitial : hasInitial HaskEndo :=
    { Void := void1
    ; ExFalso {F : Type -> Type} := fun X : Type => @void1_rect X (fun _ : void1 X => F X)
    }
  .

  End INITIAL_OBJECT.

End Categories.
