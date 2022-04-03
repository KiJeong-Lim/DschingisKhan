Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.

Module BasicCategories.

  Polymorphic Class IsCategory (objs : Type) : Type :=
    { hom (dom : objs) (cod : objs) : Type
    ; compose {obj_l : objs} {obj : objs} {obj_r : objs} : hom obj obj_r -> hom obj_l obj -> hom obj_l obj_r
    ; id {obj : objs} : hom obj obj
    }
  .

  Polymorphic Definition ObjMap {src_objs : Type} {tgt_objs : Type} (src_cat : IsCategory src_objs) (tgt_cat : IsCategory tgt_objs) : Type := src_objs -> tgt_objs.

  Infix " -----> " := ObjMap (at level 100, no associativity) : type_scope.

  Section Defnitions_of_Functor_and_NaturalTransformation.

  Polymorphic Context {src_objs : Type} {tgt_objs : Type} {src_cat : IsCategory src_objs} {tgt_cat : IsCategory tgt_objs}.

  Polymorphic Class IsFunctor (f : src_cat -----> tgt_cat) : Type :=
    { fmap {dom : src_objs} {cod : src_objs} : hom dom cod -> hom (f dom) (f cod)
    }
  .

  Polymorphic Definition NatTrans (f_from : src_cat -----> tgt_cat) (f_to : src_cat -----> tgt_cat) : Type := forall obj : src_objs, hom (f_from obj) (f_to obj).

  End Defnitions_of_Functor_and_NaturalTransformation.

  Infix " =====> " := NatTrans (at level 100, no associativity) : type_scope.

End BasicCategories.

Module MyUniverses.

  Polymorphic Definition LargeUniv : Type := Type.

  Polymorphic Definition Univ : LargeUniv := Type.

  Global Instance Hask : BasicCategories.IsCategory Univ :=
    { hom (dom : Univ) (cod : Univ) := dom -> cod
    ; compose {A : Univ} {B : Univ} {C : Univ} := compose (A := A) (B := B) (C := C)
    ; id {A : Univ} := id (A := A)
    }
  .

End MyUniverses.

Module BasicEnsembles.

  Import MyUniverses.

  Definition ensemble (X : Univ) : Univ := X -> Prop.

End BasicEnsembles.
