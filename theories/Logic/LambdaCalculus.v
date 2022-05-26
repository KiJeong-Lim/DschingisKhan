Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeUtil.
Require Import DschingisKhan.Math.BasicPosetTheory.

Module LambdaCalculusHelper.

  Definition ivar : Set := nat.

  Global Instance ivarEqDec : EqDec ivar := natEqDec.

  Definition tvar : Set := nat.

  Global Instance tvarEqDec : EqDec tvar := natEqDec.

  Global Reserved Notation " '(∀' ty_var ')' ty_expr " (at level 100, right associativity).

  Global Declare Scope tyExpr_scope.
  Global Declare Scope tmExpr_scope.

  Global Open Scope tyExpr_scope.
  Global Open Scope tmExpr_scope.

End LambdaCalculusHelper.
