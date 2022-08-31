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

  Polymorphic Definition NaturalTransformation {D : Category} {C : Category} (F : D ---> C) (F' : D ---> C) : Type :=
    @isNaturalTransformation D C F.(map_ob) F'.(map_ob)
  .

  Global Infix " ===> " := NaturalTransformation (at level 100, no associativity) : type_scope.

  Polymorphic Definition composeFunktor {C : Category} {C' : Category} {C'' : Category} (F2 : C' ---> C'') (F1 : C ---> C') : C ---> C'' :=
    {|
      map_ob (X : C.(ob)) := F2.(map_ob) (F1.(map_ob) X);
      map_hom := {| Cat.fmap A B (f : C.(hom) A B) := F2.(map_hom).(Cat.fmap) (F1.(map_hom).(Cat.fmap) f) |};
    |}
  .

  Polymorphic Definition idFunktor {C : Category} : C ---> C :=
    {|
      map_ob (X : C.(ob)) := X;
      map_hom := {| Cat.fmap A B (f : C.(hom) A B) := f |};
    |}
  .

  Section INSTANCES_OF_CATEGORY.

  Local Polymorphic Instance OppositeCategory (cat : Category) : Category :=
    { ob := cat.(ob)
    ; hom B A := cat.(hom) A B
    ; compose {C} {B} {A} (f1 : cat.(hom) A B) (f2 : cat.(hom) B C) := cat.(compose) f2 f1
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

  Local Polymorphic Instance CategoryOfFunktors (D : Category) (C : Category) : Category :=
    { ob := D ---> C
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

Module CategoryTheory.

  Import Categories.

  Class CategoryWithEquality : Type :=
    { CategoryWithEquality_hasCategory_asSelf :> Category
    ; hom_isSetoid A B :> isSetoid (CategoryWithEquality_hasCategory_asSelf.(hom) A B)
    }
  .

  Global Coercion CategoryWithEquality_hasCategory_asSelf : CategoryWithEquality >-> Category.

(** "Categorical Concepts" *)

  Class LawsOfCategory (cat : CategoryWithEquality) : Prop :=
    { compose_assoc {A : cat} {B : cat} {C : cat} {D : cat} (f : cat.(hom) A B) (g : cat.(hom) B C) (h : cat.(hom) C D)
      : compose h (compose g f) == compose (compose h g) f
    ; compose_id_l {A : cat} {B : cat} (f : cat.(hom) A B)
      : compose id f == f
    ; compose_id_r {A : cat} {B : cat} (f : cat.(hom) A B)
      : compose f id == f
    }
  .

  Class LawsOfFunktor {D : Category} {C : CategoryWithEquality} (F : D ---> C) : Prop :=
    { fmap_preserves_compose {X : D} {Y : D} {Z : D} (f : D.(hom) X Y) (g : D.(hom) Y Z)
      : F.(map_hom).(Cat.fmap) (D.(compose) g f) == @compose C (F.(map_ob) X) (F.(map_ob) Y) (F.(map_ob) Z) (F.(map_hom).(Cat.fmap) g) (F.(map_hom).(Cat.fmap) f)
    ; fmap_preserves_id {X : D}
      : F.(map_hom).(Cat.fmap) D.(id) == @id C (F.(map_ob) X)
    }
  .

  Class LawsOfNaturalTransformation {D : Category} {C : CategoryWithEquality} {F : D ---> C} {G : D ---> C} (eta : F ===> G) : Prop :=
    { diagramOfNaturalTransformation {X : D} {Y : D} (f : D.(hom) X Y)
      : compose (eta Y) (F.(map_hom).(Cat.fmap) f) == compose (G.(map_hom).(Cat.fmap) f) (eta X)
    }
  .

  Definition isIsomorphism {cat : CategoryWithEquality} {X : cat} {Y : cat} (f : cat.(hom) X Y) : Prop :=
    exists g : cat.(hom) Y X, << LEFT_INV : compose g f == id >> /\ << RIGHT_INV : compose f g == id >>
  .

  Definition isNaturalIsomorphism {D : Category} {C : CategoryWithEquality} {F : D ---> C} {G : D ---> C} (eta : F ===> G) : Prop :=
    forall X : D, isIsomorphism (eta X)
  .

(** "Instances" *)

  Section HASK_WITH_EQUALITY.

  Local Instance HaskWithEquality : CategoryWithEquality :=
    { CategoryWithEquality_hasCategory_asSelf := Hask.cat
    ; hom_isSetoid (dom : Type) (cod : Type) := arrow_isSetoid dom cod (cod_isSetoid := theFinestSetoidOf cod)
    }
  .

  Local Instance HaskWithEquality_obeyLaws
    : LawsOfCategory HaskWithEquality.
  Proof. split; cbv; ii; congruence. Qed.

  End HASK_WITH_EQUALITY.

End CategoryTheory.
