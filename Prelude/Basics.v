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

  Polymorphic Class isFunctor {src_objs : Type} {tgt_objs : Type} {src_cat : isCategory src_objs} {tgt_cat : isCategory tgt_objs} (map_objs : src_objs -> tgt_objs) : Type :=
    { map_arrs {dom : src_objs} {cod : src_objs} : (dom \to cod) -> (map_objs dom \to map_objs cod)
    }
  .

  Infix " -----> " := isFunctor (at level 100, no associativity) : type_scope.

  Polymorphic Definition isNaturalTransformation {src_objs : Type} {tgt_objs : Type} {src_cat : isCategory src_objs} {tgt_cat : isCategory tgt_objs} (_from : src_objs -> tgt_objs) (_to : src_objs -> tgt_objs) : Type :=
    forall obj : src_objs, _from obj \to _to obj
  .

  Infix " =====> " := isNaturalTransformation (at level 100, no associativity) : type_scope.

  Global Polymorphic Instance Hask : isCategory Type :=
    { arrs (from_obj : Type) (to_obj : Type) := from_obj -> to_obj
    ; compose_arr {A : Type} {B : Type} {C : Type} := compose (A := A) (B := B) (C := C)
    ; id_arr {A : Type} := id (A := A)
    }
  .

End BasicCategories.
