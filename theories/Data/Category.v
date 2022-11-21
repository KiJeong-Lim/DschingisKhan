Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.

Module Categories.

  Global Declare Scope cat_scope.

  Global Bind Scope cat_scope with Category.

  Polymorphic Class Funktor (D : Category) (C : Category) : Type :=
    { map_ob : D -----> C
    ; map_hom :> @isCovariantFunctor D C map_ob
    }
  .

  Global Arguments map_ob {D} {C} {Funktor}.

  Global Arguments map_hom {D} {C} {Funktor} {dom} {cod}.

  Global Infix " ---> " := Funktor (at level 100, no associativity) : type_scope.

  Polymorphic Definition NaturalTransformation {D : Category} {C : Category} (F : D ---> C) (F' : D ---> C) : Type :=
    @isNaturalTransformation D C F.(map_ob) F'.(map_ob)
  .

  Global Infix " ===> " := NaturalTransformation (at level 100, no associativity) : type_scope.

  Local Polymorphic Instance composeFunktor {C : Category} {C' : Category} {C'' : Category} (F2 : C' ---> C'') (F1 : C ---> C') : C ---> C'' :=
    { map_ob := fun X : C.(ob) => F2.(map_ob) (F1.(map_ob) X)
    ; map_hom (dom : C.(ob)) (cod : C.(ob)) (f : C.(hom) dom cod) := F2.(map_hom) (F1.(map_hom) f)
    }
  .

  Local Polymorphic Instance idFunktor {C : Category} : C ---> C :=
    { map_ob := fun X : C.(ob) => X
    ; map_hom (dom : C.(ob)) (cod : C.(ob)) := fun f : C.(hom) dom cod => f
    }
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

  Local Polymorphic Instance ProductCategory (D : Category) (C : Category) : Category :=
    { ob := D.(ob) * C.(ob)
    ; hom f g := (D.(hom) (fst f) (fst g) * C.(hom) (snd f) (snd g))%type
    ; compose {f} {g} {h} eta2 eta1 := (compose (fst eta2) (fst eta1), compose (snd eta2) (snd eta1))
    ; id {f} := (id, id)
    }
  .

  End INSTANCES_OF_CATEGORY.

  Section CATEGORICAL_SUM.

  Polymorphic Class hasCoproduct (cat : Category) : Type :=
    { sum (A : cat.(ob)) (B : cat.(ob)) : cat.(ob)
    ; inl {A : cat.(ob)} {B : cat.(ob)} : cat.(hom) A (sum A B)
    ; inr {A : cat.(ob)} {B : cat.(ob)} : cat.(hom) B (sum A B)
    ; case {A : cat.(ob)} {B : cat.(ob)} {C : cat.(ob)} (f : cat.(hom) A C) (g : cat.(hom) B C) : cat.(hom) (sum A B) C
    }
  .

  Polymorphic Definition coproduct_bimap {cat : Category} {coproduct : hasCoproduct cat} {A : cat} {A' : cat} {B : cat} {B' : cat} (f : cat.(hom) A A') (g : cat.(hom) B B') : cat.(hom) (sum A B) (sum A' B') :=
    case (compose inl f) (compose inr g)
  .

  Local Instance Hask_hasCoproduct : hasCoproduct Hask.cat :=
    { sum := @Datatypes.sum
    ; inl {A : Type} {B : Type} := (@Datatypes.inl A B)%function
    ; inr {A : Type} {B : Type} := (@Datatypes.inr A B)%function
    ; case {A : Type} {B : Type} {C : Type} := @Datatypes.sum_rect A B (fun _ : A + B => C)
    }
  .

  End CATEGORICAL_SUM.

  Section INITIAL_OBJECT.

  Polymorphic Class hasInitial (cat : Category) : Type :=
    { Void : cat.(ob)
    ; ExFalso {A : cat.(ob)} : cat.(hom) Void A
    }
  .

  Local Instance Hask_hasInitial : hasInitial Hask.cat :=
    { Void := Empty_set
    ; ExFalso {A : Type} := @Empty_set_rect (fun _ : Empty_set => A)
    }
  .

  End INITIAL_OBJECT.

  Section CATEGORICAL_PRODUCT.

  Polymorphic Class hasProduct (cat : Category) : Type :=
    { prod (A : cat.(ob)) (B : cat.(ob)) : cat.(ob)
    ; fst {A : cat.(ob)} {B : cat.(ob)} : cat.(hom) (prod A B) A
    ; snd {A : cat.(ob)} {B : cat.(ob)} : cat.(hom) (prod A B) B
    ; pair {A : cat.(ob)} {B : cat.(ob)} {C : cat.(ob)} (f : cat.(hom) C A) (g : cat.(hom) C B) : cat.(hom) C (prod A B)
    }
  .

  End CATEGORICAL_PRODUCT.

  Section TERMINAL_OBJECT.

  Polymorphic Class hasFinal (cat : Category) : Type :=
    { unit : cat.(ob)
    ; tt {A : cat.(ob)} : cat.(hom) A unit
    }
  .

  End TERMINAL_OBJECT.

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
      : Cat.fmap (isCovariantFunctor := proj_map_hom F) (D.(compose) g f) == @compose C (F.(map_ob) X) (F.(map_ob) Y) (F.(map_ob) Z) (Cat.fmap g) (Cat.fmap f)
    ; fmap_preserves_id {X : D}
      : Cat.fmap (isCovariantFunctor := proj_map_hom F) D.(id) == @id C (F.(map_ob) X)
    }
  .

  Class LawsOfNaturalTransformation {D : Category} {C : CategoryWithEquality} {F : D ---> C} {G : D ---> C} (eta : F ===> G) : Prop :=
    { diagramOfNaturalTransformation {X : D} {Y : D} (f : D.(hom) X Y)
      : compose (eta Y) (Cat.fmap (isCovariantFunctor := proj_map_hom F) f) == compose (Cat.fmap (isCovariantFunctor := proj_map_hom G) f) (eta X)
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

  Section OPPOSITE_CATEGORY_WITH_EQUALITY.

  Local Instance OppositeCategoryWithEquality (cat : CategoryWithEquality) : CategoryWithEquality :=
    { CategoryWithEquality_hasCategory_asSelf := OppositeCategory cat
    ; hom_isSetoid (cod : cat.(ob)) (dom : cat.(ob)) := cat.(hom_isSetoid) dom cod
    }
  .

  Local Instance OppositeCategoryWithEquality_obeysLaws (cat : CategoryWithEquality)
    (cat_obeysLaws : LawsOfCategory cat)
    : LawsOfCategory (OppositeCategoryWithEquality cat).
  Proof.
    unfold OppositeCategoryWithEquality. split; cbn; ii.
    - now rewrite compose_assoc.
    - now rewrite compose_id_r.
    - now rewrite compose_id_l.
  Qed.

  End OPPOSITE_CATEGORY_WITH_EQUALITY.

End CategoryTheory.
