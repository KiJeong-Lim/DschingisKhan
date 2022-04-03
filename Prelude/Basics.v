Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.

Module BasicCategories.

  Polymorphic Class IsCategory (objs : Type) : Type :=
    { arrs (dom : objs) (cod : objs) : Type
    ; compose_arr {obj1 : objs} {obj2 : objs} {obj3 : objs} : arrs obj2 obj3 -> arrs obj1 obj2 -> arrs obj1 obj3
    ; id_arr {obj1 : objs} : arrs obj1 obj1
    }
  .

  Infix " \to " := arrs (at level 100, no associativity) : type_scope.

  Polymorphic Definition Funktor {src_objs : Type} {tgt_objs : Type} (src_cat : IsCategory src_objs) (tgt_cat : IsCategory tgt_objs) : Type :=
    src_objs -> tgt_objs
  .

  Infix " -----> " := Funktor (at level 100, no associativity) : type_scope.

  Section Defnitions_of_Functor_and_NaturalTransformation.

  Polymorphic Context {src_objs : Type} {tgt_objs : Type} {src_cat : IsCategory src_objs} {tgt_cat : IsCategory tgt_objs}.

  Polymorphic Class IsFunctor (f : src_cat -----> tgt_cat) : Type :=
    { fmap {dom : src_objs} {cod : src_objs} : (dom \to cod) -> (f dom \to f cod)
    }
  .

  Polymorphic Definition NatTrans (f_from : src_cat -----> tgt_cat) (f_to : src_cat -----> tgt_cat) : Type :=
    forall obj : src_objs, f_from obj \to f_to obj
  .

  End Defnitions_of_Functor_and_NaturalTransformation.

  Infix " =====> " := NatTrans (at level 100, no associativity) : type_scope.

  Global Polymorphic Instance Hask : IsCategory Type :=
    { arrs (dom : Type) (cod : Type) := dom -> cod
    ; compose_arr {A : Type} {B : Type} {C : Type} := compose (A := A) (B := B) (C := C)
    ; id_arr {A : Type} := id (A := A)
    }
  .

End BasicCategories.
