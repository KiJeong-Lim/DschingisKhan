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

Module UntypedLambdaCalculus.

  Import ListNotations LambdaCalculusHelper.

  Inductive tmExpr : Set :=
  | Var (x : ivar) : tmExpr
  | App (P1 : tmExpr) (P2 : tmExpr) : tmExpr
  | Lam (y : ivar) (Q : tmExpr) : tmExpr
  .

  Local Delimit Scope tmExpr_scope with tmExpr.

  Global Instance tmExprEqDec
    : EqDec tmExpr.
  Proof with try ((left; congruence) || (right; congruence)).
    change (forall lhs : tmExpr, forall rhs : tmExpr, {lhs = rhs} + {lhs <> rhs}).
    induction lhs as [x | P1 IH1 P2 IH2 | y Q IH], rhs as [x' | P1' P2' | y' Q']...
    { pose proof (ivarEqDec x x') as [x_eq_x' | x_ne_x']... }
    { pose proof (IH1 P1') as [P1_eq_P1' | P1_ne_P1']; pose proof (IH2 P2') as [P2_eq_P2' | P2_ne_P2']... }
    { pose proof (ivarEqDec y y') as [y_eq_y' | y_ne_y']; pose proof (IH Q') as [Q_eq_Q' | Q_ne_Q']... }
  Defined.

  Fixpoint getFVs (M : tmExpr) {struct M} : list ivar :=
    match M with
    | Var x => [x]
    | App P1 P2 => getFVs P1 ++ getFVs P2
    | Lam y Q => remove ivarEqDec y (getFVs Q)
    end
  .

  Fixpoint isFreeIn (z : ivar) (M : tmExpr) {struct M} : bool :=
    match M with
    | Var x => Nat.eqb x z
    | App P1 P2 => orb (isFreeIn z P1) (isFreeIn z P2)
    | Lam y Q => andb (negb (Nat.eqb y z)) (isFreeIn z Q)
    end
  .

  Lemma getFVs_isFreeIn (M : tmExpr)
    : forall z : ivar, In z (getFVs M) <-> isFreeIn z M = true.
  Proof. induction M as [x | P1 IH1 P2 IH2 | y Q IH]; resolver. Qed.

  Definition tmSubst : Set := ivar -> tmExpr.

  Definition nilSubst : tmSubst :=
    fun z : ivar => Var z
  .

  Definition consSubst (x : ivar) (M : tmExpr) (sigma : tmSubst) : tmSubst :=
    fun z : ivar => if ivarEqDec x z then M else sigma z
  .

  Definition chi (sigma : tmSubst) (M : tmExpr) : ivar :=
    suc (maxs (map (fun z : ivar => maxs (getFVs (sigma z))) (getFVs M)))
  .

End UntypedLambdaCalculus.
