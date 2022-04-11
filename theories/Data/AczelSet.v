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

  Polymorphic Definition ordinalFromAcc@{lv} {A : Type@{lv}} {wfRel : A -> A -> Prop} : forall root : A, Acc wfRel root -> Tree@{lv} :=
    fix ordinalFromAcc_fix (tree : A) (tree_acc : Acc wfRel tree) {struct tree_acc} : Tree :=
    let children : Type@{lv} := {subtree : A | wfRel subtree tree} in
    match tree_acc with
    | Acc_intro _ hyp_acc => Node children (fun childtree : children => ordinalFromAcc_fix (proj1_sig childtree) (hyp_acc (proj1_sig childtree) (proj2_sig childtree)))
    end
  .

End AczelSet.
