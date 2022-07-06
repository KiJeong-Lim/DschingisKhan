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

  Section SUBSTITUTION. (* Reference: "https://github.com/ernius/formalmetatheory-stoughton/tree/7eea5b526ec58a49838daa7b21b02fafcbf9065e" *)

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

  Definition last_ivar (M : tmExpr) : ivar := maxs (getFVs M).

  Lemma last_ivar_lt (M : tmExpr) (x : ivar)
    (last_ivar_lt : last_ivar M < x)
    : isFreeIn x M = false.
  Proof.
    enough (to_show : ~ In x (getFVs M)).
    { now rewrite getFVs_isFreeIn, not_true_iff_false in to_show. }
    revert x last_ivar_lt. pose proof (maxs_in (getFVs M)) as claim1.
    intros x last_ivar_lt H_in. contradiction (le_gt_False (claim1 x H_in) last_ivar_lt).
  Qed.

  Definition tmSubst : Set := ivar -> tmExpr.

  Definition nilSubst : tmSubst :=
    fun z : ivar => Var z
  .

  Definition consSubst (x : ivar) (M : tmExpr) (sigma : tmSubst) : tmSubst :=
    fun z : ivar => if ivarEqDec x z then M else sigma z
  .

  Definition chi (sigma : tmSubst) (M : tmExpr) : ivar :=
    suc (maxs (map (fun z : ivar => last_ivar (sigma z)) (getFVs M)))
  .

  Definition isFreshIn_tmSubst (x : ivar) (sigma : tmSubst) (M : tmExpr) : bool :=
    forallb (fun z : ivar => negb (isFreeIn x (sigma z))) (getFVs M)
  .

  Lemma chi_sigma_M_sigma_x_not_free (sigma : tmSubst) (M : tmExpr) (x : ivar)
    (OCCURS_FREE : isFreeIn x M = true)
    : isFreeIn (chi sigma M) (sigma x) = false.
  Proof.
    enough (claim1 : last_ivar (sigma x) < chi sigma M) by now eapply last_ivar_lt.
    unfold chi, maxs. eapply le_intro_S_n_le_S_m. rewrite <- getFVs_isFreeIn in OCCURS_FREE.
    eapply maxs_in; resolver.
  Qed.

  Theorem chi_spec (M : tmExpr) (sigma : tmSubst)
    : isFreshIn_tmSubst (chi sigma M) sigma M = true.
  Proof with resolver. unfold isFreshIn_tmSubst... ii... eapply chi_sigma_M_sigma_x_not_free. now eapply getFVs_isFreeIn. Qed.

  Lemma chi_nil (M : tmExpr)
    : isFreeIn (chi nilSubst M) M = false.
  Proof.
    pose proof (chi_spec M nilSubst) as claim1.
    unfold isFreshIn_tmSubst in claim1. rewrite forallb_true_iff in claim1. simpl in claim1.
    eapply not_true_iff_false. intros H_false. specialize (claim1 (chi nilSubst M) (proj2 (getFVs_isFreeIn _ _) H_false)).
    rewrite negb_true_iff, Nat.eqb_neq in claim1. contradiction.
  Qed.

  Fixpoint runSubst (sigma : tmSubst) (M : tmExpr) {struct M} : tmExpr :=
    match M with
    | Var x => sigma x
    | App P1 P2 => App (runSubst sigma P1) (runSubst sigma P2)
    | Lam y Q => let z : ivar := chi sigma M in Lam z (runSubst (consSubst y (Var z) sigma) Q)
    end
  .

  End SUBSTITUTION.

End UntypedLambdaCalculus.
