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

Module LambdaCalculus_init.

  Definition ivar : Set := nat.

  Global Instance ivarEqDec : EqDec ivar := natEqDec.

  Definition tvar : Set := nat.

  Global Instance tvarEqDec : EqDec tvar := natEqDec.

  Global Reserved Notation " ∀ ty_var , ty_expr " (at level 100, right associativity).

  Global Declare Scope tyExpr_scope.
  Global Declare Scope tmExpr_scope.

  Global Open Scope tyExpr_scope.
  Global Open Scope tmExpr_scope.

End LambdaCalculus_init.

Module SystemF.

  Import ListNotations LambdaCalculus_init.

  Monomorphic Universe KIND_lv.
  Monomorphic Universe KIND_lv'.

  Local Notation KIND := (Type@{KIND_lv}).
  Local Notation KIND' := (Type@{KIND_lv'}).

  Inductive tyExpr : Set :=
  | TyVar (a : tvar) : tyExpr
  | TyArr (tau : tyExpr) (sigma : tyExpr) : tyExpr
  | TyAll (b : tvar) (sigma : tyExpr) : tyExpr
  .

  Local Coercion TyVar : tvar >-> tyExpr.

  Local Delimit Scope tyExpr_scope with tyExpr.
  Local Notation " tau -> sigma " := (TyArr tau sigma) : tyExpr_scope.
  Local Notation " ∀ b , sigma " := (TyAll b sigma) : tyExpr_scope.

  Local Instance typEqDec
    : EqDec tyExpr.
  Proof with first [left; congruence | right; congruence | idtac].
    change (forall lhs : tyExpr, forall rhs : tyExpr, {lhs = rhs} + {lhs <> rhs}).
    induction lhs as [a1 | tau1 IH_tau sigma1 IH_sigma | b1 sigma1 IH_sigma]; destruct rhs as [a2 | tau2 sigma2 | b2 sigma2]...
    { pose proof (eq_dec (EqDec := tvarEqDec) a1 a2) as [h_eq_a | h_ne_a]... }
    { pose proof (IH_tau tau2) as [h_eq_tau | h_ne_tau]; destruct (IH_sigma sigma2) as [h_eq_sigma | h_ne_sigma]... }
    { pose proof (eq_dec (EqDec := tvarEqDec) b1 b2) as [h_eq_b | h_ne_b]; destruct (IH_sigma sigma2) as [h_eq_sigma | h_ne_sigma]... }
  Defined.

  Definition evalTy : forall lctx : tvar -> KIND', tyExpr -> KIND :=
    fix evalTy_fix (lctx : tvar -> KIND') (tau : tyExpr) {struct tau} : KIND :=
    match tau with
    | TyVar a => (lctx a)%type
    | TyArr tau sigma => (evalTy_fix lctx tau -> evalTy_fix lctx sigma)%type
    | TyAll b sigma => (forall b_typ : KIND', evalTy_fix (fun a : tvar => if eq_dec (EqDec := tvarEqDec) a b then b_typ else lctx a) sigma)%type
    end
  .

End SystemF.
