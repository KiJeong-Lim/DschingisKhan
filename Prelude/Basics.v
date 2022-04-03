Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.

Module MyInit.

  Reserved Infix " -----> " (at level 100, no associativity).

  Reserved Infix " =====> " (at level 100, no associativity).

End MyInit.

Module BasicCategories.

  Import MyInit.

  Polymorphic Class Category (objs : Type) : Type :=
    { hom (dom : objs) (cod : objs) : Type
    ; compose {obj_l : objs} {obj : objs} {obj_r : objs} : hom obj obj_r -> hom obj_l obj -> hom obj_l obj_r
    ; id {obj : objs} : hom obj obj
    }
  .

  Polymorphic Definition ObjMap {src_objs : Type} {tgt_objs : Type} (src_cat : Category src_objs) (tgt_cat : Category tgt_objs) : Type := src_objs -> tgt_objs.

  Infix " -----> " := ObjMap : type_scope.

  Section BasicConceptsOfCategory.

  Polymorphic Context {src_objs : Type} {tgt_objs : Type} {src_cat : Category src_objs} {tgt_cat : Category tgt_objs}.

  Polymorphic Class CovariantFunctor (f : src_cat -----> tgt_cat) : Type :=
    { fmap {dom : src_objs} {cod : src_objs} : hom dom cod -> hom (f dom) (f cod)
    }
  .

  Polymorphic Class ContravariantFunctor (f : src_cat -----> tgt_cat) : Type :=
    { contramap {dom : src_objs} {cod : src_objs} : hom dom cod -> hom (f cod) (f dom)
    }
  .

  Polymorphic Definition NaturalTransformation (f_from : src_cat -----> tgt_cat) (f_to : src_cat -----> tgt_cat) : Type := forall obj : src_objs, hom (f_from obj) (f_to obj).

  End BasicConceptsOfCategory.

  Infix " =====> " := NaturalTransformation : type_scope.

End BasicCategories.

Module MyUniverses.

  Universe Univ_lv.

  Definition Univ : Type@{Univ_lv+1} := Type@{Univ_lv}.

  Polymorphic Definition hask : Univ := Type.

  Global Polymorphic Instance Hask : BasicCategories.Category hask :=
    { hom (dom : hask) (cod : hask) := dom -> cod
    ; compose {A : hask} {B : hask} {C : hask} := compose (A := A) (B := B) (C := C)
    ; id {A : hask} := id (A := A)
    }
  .

End MyUniverses.

Module BasicEnsembles.

  Import MyInit BasicCategories MyUniverses.

  Polymorphic Definition ensemble (X : hask) : hask := X -> Prop.

End BasicEnsembles.
