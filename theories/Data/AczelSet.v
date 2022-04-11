Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.

Module AczelSet.

  Inductive Tree : Type :=
  | Node (children : Hask.t) (childtree : children -> Tree) : Tree
  .

End AczelSet.
