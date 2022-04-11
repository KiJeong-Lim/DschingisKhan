Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.

Module AczelSet.

  Universe AczelSet_outer_lv.

  Monomorphic Definition Univ := Type@{AczelSet_outer_lv}.

  Polymorphic Inductive Tree@{AczelSet_lv} : Univ :=
  | Node (children : Type@{AczelSet_lv}) (childtrees : children -> Tree) : Tree
  .

End AczelSet.
