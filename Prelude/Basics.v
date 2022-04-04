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

  Polymorphic Definition objmap {src_objs : Type} {tgt_objs : Type} (src_cat : Category src_objs) (tgt_cat : Category tgt_objs) : Type := src_objs -> tgt_objs.

  Global Infix " -----> " := objmap (at level 100, no associativity) : type_scope.

  Section BasicConceptsOfCategory.

  Polymorphic Context {src_objs : Type} {tgt_objs : Type} {src_cat : Category src_objs} {tgt_cat : Category tgt_objs}.

  Polymorphic Class CovariantFunctor (f : src_cat -----> tgt_cat) : Type :=
    { fmap {dom : src_objs} {cod : src_objs} : hom dom cod -> hom (f dom) (f cod)
    }
  .

  Polymorphic Class ContravariantFunctor (f : src_cat -----> tgt_cat) : Type :=
    { contramap {dom : src_objs} {cod : src_objs} : hom cod dom -> hom (f dom) (f cod)
    }
  .

  Polymorphic Definition NaturalTransformation (f_from : src_cat -----> tgt_cat) (f_to : src_cat -----> tgt_cat) : Type :=
    forall obj : src_objs, hom (f_from obj) (f_to obj)
  .

  End BasicConceptsOfCategory.

  Global Infix " =====> " := NaturalTransformation (at level 100, no associativity) : type_scope.

End BasicCategories.

Module Hask.

  Universe Univ_lv.

  Definition Univ : Type@{Univ_lv + 1} := Type@{Univ_lv}.

  Polymorphic Definition t : Univ := Type.

  Global Polymorphic Instance Cat : BasicCategories.Category t :=
    { hom (dom : t) (cod : t) := dom -> cod
    ; compose {A : t} {B : t} {C : t} := compose (A := A) (B := B) (C := C)
    ; id {A : t} := id (A := A)
    }
  .

End Hask.

Module MyInit.

  Polymorphic Definition ensemble (X : Hask.t) : Hask.t := X -> Prop.

End MyInit.
