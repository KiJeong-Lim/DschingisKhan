Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.

Module BasicCategories.

  Polymorphic Class Category (objs : Type) : Type :=
    { hom (dom : objs) (cod : objs) : Type
    ; compose {obj_l : objs} {obj : objs} {obj_r : objs} : hom obj obj_r -> hom obj_l obj -> hom obj_l obj_r
    ; id {obj : objs} : hom obj obj
    }
  .

  Polymorphic Definition objectMap {src_objs : Type} {tgt_objs : Type} (src_cat : Category src_objs) (tgt_cat : Category tgt_objs) : Type := src_objs -> tgt_objs.

  Global Infix " -----> " := objectMap (at level 100, no associativity) : type_scope.

  Section BasicConceptsOfCategoryTheory.

  Polymorphic Context {src_objs : Type} {tgt_objs : Type} {src_cat : Category src_objs} {tgt_cat : Category tgt_objs}.

  Polymorphic Class CovariantFunctor (F : src_cat -----> tgt_cat) : Type :=
    { fmap {dom : src_objs} {cod : src_objs} : hom dom cod -> hom (F dom) (F cod)
    }
  .

  Polymorphic Class ContravariantFunctor (F : src_cat -----> tgt_cat) : Type :=
    { contramap {dom : src_objs} {cod : src_objs} : hom cod dom -> hom (F dom) (F cod)
    }
  .

  Polymorphic Definition functorMap (F_from : src_cat -----> tgt_cat) (F_to : src_cat -----> tgt_cat) : Type :=
    forall obj : src_objs, hom (F_from obj) (F_to obj)
  .

  Polymorphic Class NaturalTransformation (F_from : src_cat -----> tgt_cat) (F_to : src_cat -----> tgt_cat) : Type :=
    { component {at_obj : src_objs} : hom (F_from at_obj) (F_to at_obj)
    }
  .

  End BasicConceptsOfCategoryTheory.

  Global Infix " =====> " := functorMap (at level 100, no associativity) : type_scope.

End BasicCategories.

Module Hask.

  Universe Univ_lv.

  Definition Univ : Type@{Univ_lv + 1} := Type@{Univ_lv}.

  Polymorphic Definition t : Univ := Type.

  Global Polymorphic Instance cat : BasicCategories.Category t :=
    { hom (dom : t) (cod : t) := dom -> cod
    ; compose {A : t} {B : t} {C : t} := compose (A := A) (B := B) (C := C)
    ; id {A : t} := id (A := A)
    }
  .

End Hask.

Module MyTypeClasses.

  Import BasicCategories.

  Local Open Scope program_scope.

  Global Notation isFunctor := (CovariantFunctor (src_cat := Hask.cat) (tgt_cat := Hask.cat)).

  Polymorphic Class isMonad (M : Hask.cat -----> Hask.cat) : Type :=
    { pure {A : Hask.t} : A -> M A
    ; bind {A : Hask.t} {B : Hask.t} : M A -> (A -> M B) -> M B
    }
  .

  Global Infix " >>= " := bind (at level 90, left associativity) : program_scope.

  Polymorphic Class isSetoid (A : Hask.t) : Type :=
    { eqProp : A -> A -> Prop
    ; eqProp_Equivalence :> @Equivalence A eqProp
    }
  .

  Global Infix " == " := eqProp (at level 70, no associativity) : type_scope.

  Polymorphic Class isPoset (A : Hask.t) : Type :=
    { leProp : A -> A -> Prop
    ; Poset_requiresSetoid :> isSetoid A
    ; leProp_PreOrder :> @PreOrder A leProp
    ; leProp_PartialOrder :> @PartialOrder A eqProp (@eqProp_Equivalence A Poset_requiresSetoid) leProp leProp_PreOrder
    }
  .

  Global Infix " =< " := leProp (at level 70, no associativity) : type_scope.

End MyTypeClasses.

Module BasicInstances.

  Import BasicCategories MyTypeClasses.

  Local Open Scope program_scope.

  Global Instance option_isFunctor : isFunctor option :=
    { fmap {A : Hask.t} {B : Hask.t} := option_map (A := A) (B := B)
    }
  .

  Polymorphic Definition ensemble (X : Hask.t) : Hask.t := X -> Prop.

End BasicInstances.
