Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.

Module BasicCategories.

  Polymorphic Class isCategory (objs : Type) : Type :=
    { arrs (dom : objs) (cod : objs) : Type
    ; compose_arr {obj1 : objs} {obj2 : objs} {obj3 : objs} : arrs obj2 obj3 -> arrs obj1 obj2 -> arrs obj1 obj3
    ; id_arr {obj1 : objs} : arrs obj1 obj1
    }
  .

  Infix " \to " := arrs (at level 100, no associativity) : type_scope.

  Polymorphic Definition Funktor {src_objs : Type} {tgt_objs : Type} (src_cat : isCategory src_objs) (tgt_cat : isCategory tgt_objs) : Type :=
    src_objs -> tgt_objs
  .

  Infix " -----> " := Funktor (at level 100, no associativity) : type_scope.

  Section Defnitions_of_Functor_and_NaturalTransformation.

  Polymorphic Context {src_objs : Type} {tgt_objs : Type} {src_cat : isCategory src_objs} {tgt_cat : isCategory tgt_objs}.

  Polymorphic Class isFunctor (F : src_cat -----> tgt_cat) : Type :=
    { fmap {dom : src_objs} {cod : src_objs} : (dom \to cod) -> (F dom \to F cod)
    }
  .

  Polymorphic Definition NatTrans (F_from : src_cat -----> tgt_cat) (F_to : src_cat -----> tgt_cat) : Type :=
    forall obj : src_objs, F_from obj \to F_to obj
  .

  End Defnitions_of_Functor_and_NaturalTransformation.

  Infix " =====> " := NatTrans (at level 100, no associativity) : type_scope.

  Global Polymorphic Instance Hask : isCategory Type :=
    { arrs (from_obj : Type) (to_obj : Type) := from_obj -> to_obj
    ; compose_arr {A : Type} {B : Type} {C : Type} := compose (A := A) (B := B) (C := C)
    ; id_arr {A : Type} := id (A := A)
    }
  .

End BasicCategories.
