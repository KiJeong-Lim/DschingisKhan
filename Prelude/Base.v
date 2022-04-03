Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.

Module MyCategories.

  Polymorphic Class isCategory (objs : Type) : Type :=
    { arrs (from_obj : objs) (to_obj : objs) : Type
    ; compose_arr {obj1 : objs} {obj2 : objs} {obj3 : objs} : arrs obj2 obj3 -> arrs obj1 obj2 -> arrs obj1 obj3
    ; id_arr {obj1 : objs} : arrs obj1 obj1
    }
  .

  Polymorphic Class isFunctor {src_objs : Type} {tgt_objs : Type} {src_cat : isCategory src_objs} {tgt_cat : isCategory tgt_objs} (map_objs : src_objs -> tgt_objs) : Type :=
    { map_arrs {from_obj : src_objs} {to_obj : src_objs} : arrs (objs := src_objs) from_obj to_obj -> arrs (objs := tgt_objs) (map_objs from_obj) (map_objs to_obj)
    }
  .

  Polymorphic Definition isNaturalTransformation {src_objs : Type} {tgt_objs : Type} {src_cat : isCategory src_objs} {tgt_cat : isCategory tgt_objs} (from_map_objs : src_objs -> tgt_objs) (to_map_objs : src_objs -> tgt_objs) : Type :=
    forall s_obj : src_objs, arrs (objs := tgt_objs) (from_map_objs s_obj) (to_map_objs s_obj)
  .

  Global Infix " \to " := arrs (at level 100, no associativity) : type_scope.
  Global Infix " =====> " := isNaturalTransformation (at level 100, no associativity) : type_scope.

End MyCategories.
