Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.

Module AczelSet.

  Universe AczelSetUniv_lv.

  Monomorphic Definition Univ : Type@{AczelSetUniv_lv + 1} := Type@{AczelSetUniv_lv}.

  Polymorphic Inductive Tree@{AczelSet_lv} : Univ :=
  | Node (children : Type@{AczelSet_lv}) (childtrees : children -> Tree) : Tree
  .

  Polymorphic Definition getChildren@{lv} (root : Tree@{lv}) : Type@{lv} :=
    match root return Type@{lv} with
    | Node children childtrees => children
    end
  .

  Polymorphic Definition getChildTrees@{lv} (root : Tree@{lv}) : getChildren@{lv} root -> Tree@{lv} :=
    match root as t return getChildren@{lv} t -> Tree@{lv} with
    | Node children childtrees => childtrees
    end
  .

End AczelSet.
