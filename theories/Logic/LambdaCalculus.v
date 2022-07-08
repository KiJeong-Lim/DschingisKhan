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
    | Lam y Q => andb (isFreeIn z Q) (negb (Nat.eqb z y))
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

  Theorem isFreshIn_tmSubst_spec (M : tmExpr) (z : ivar) (sigma : tmSubst)
    : isFreshIn_tmSubst z sigma M = true <-> isFreeIn z (runSubst sigma M) = false.
  Proof with resolver.
    revert z sigma. induction M as [x | P1 IH1 P2 IH2 | y Q IH]; unfold isFreshIn_tmSubst; simpl... split.
    - intros FRESH_IN. pose proof (ivarEqDec z (chi sigma (Lam y Q))) as [z_eq | z_ne]; [red in z_eq | unfold member in z_ne]...
      left. eapply IH. unfold consSubst. eapply forallb_true_iff. intros x FREE. destruct (ivarEqDec y x) as [y_eq_x | y_ne_x]; [red in y_eq_x | unfold member in y_ne_x].
      + eapply negb_true_iff, Nat.eqb_neq...
      + eapply FRESH_IN, in_in_remove...
    - intros [FREE_IN | z_eq] x; resolver1; intros [FREE x_ne_y].
      + pose proof (proj2 (IH _ _) FREE_IN) as claim1. unfold isFreshIn_tmSubst in claim1. rewrite forallb_true_iff in claim1.
        pose proof (claim1 x FREE) as claim2. unfold consSubst in claim2. destruct (ivarEqDec y x) as [y_eq_x | y_ne_x]; [red in y_eq_x | unfold member in y_ne_x]...
      + assert (claim1 : isFreshIn_tmSubst z sigma (Lam y Q) = true).
        { rewrite z_eq. eapply chi_spec. }
        unfold isFreshIn_tmSubst in claim1. rewrite forallb_true_iff in claim1. eapply claim1...
  Qed.

  Definition equivSubstWrt (sigma1 : tmSubst) (sigma2 : tmSubst) (M : tmExpr) : Prop :=
    forall x : ivar, isFreeIn x M = true -> sigma1 x = sigma2 x
  .

  Corollary equivSubstWrt_trivialIntro (sigma1 : tmSubst) (sigma2 : tmSubst)
    (EQUIV : forall x : ivar, sigma1 x = sigma2 x)
    : forall M : tmExpr, equivSubstWrt sigma1 sigma2 M.
  Proof. unfold equivSubstWrt; now firstorder. Qed.

  Lemma chi_compatWith_equivSubstWrt (sigma1 : tmSubst) (sigma2 : tmSubst) (M : tmExpr)
    (EQUIV : equivSubstWrt sigma1 sigma2 M)
    : chi sigma1 M = chi sigma2 M.
  Proof.
    unfold chi. replace (map (fun z : ivar => last_ivar (sigma1 z)) (getFVs M)) with (map (fun z : ivar => last_ivar (sigma2 z)) (getFVs M)); try reflexivity.
    eapply map_ext_in. intros x FREE. rewrite EQUIV; try reflexivity. now eapply getFVs_isFreeIn.
  Qed.

  Theorem equivSubstWrt_spec (sigma1 : tmSubst) (sigma2 : tmSubst) (M : tmExpr)
    (EQUIV : equivSubstWrt sigma1 sigma2 M)
    : runSubst sigma1 M = runSubst sigma2 M.
  Proof with resolver.
    revert sigma1 sigma2 EQUIV; induction M as [x | P1 IH1 P2 IH2 | y Q IH]; simpl.
    - ii. eapply EQUIV...
    - ii. erewrite IH1, IH2; try reflexivity. all: ii; eapply EQUIV...
    - ii. erewrite chi_compatWith_equivSubstWrt; try eassumption.
      replace (runSubst (consSubst y (Var (chi sigma2 (Lam y Q))) sigma2) Q) with (runSubst (consSubst y (Var (chi sigma2 (Lam y Q))) sigma1) Q); try reflexivity.
      eapply IH. unfold consSubst. ii. destruct (ivarEqDec y x) as [y_eq_x | y_ne_x]; [red in y_eq_x | unfold member in y_ne_x]... eapply EQUIV...
  Qed.

  Lemma trivial_tmSubst (x : ivar) (M : tmExpr)
    : runSubst (consSubst x (Var x) nilSubst) M = runSubst nilSubst M.
  Proof. unfold consSubst, nilSubst. eapply equivSubstWrt_spec. intros y FREE. destruct (ivarEqDec x y) as [x_eq_y | x_ne_y]; [red in x_eq_y | unfold member in x_ne_y]; [congruence | reflexivity]. Qed.

  Definition composeSubst (sigma2 : tmSubst) (sigma1 : tmSubst) : tmSubst :=
    fun z : ivar => runSubst sigma2 (sigma1 z)
  .

  Lemma distr_compose_cons (Q : tmExpr) (M : tmExpr) (sigma1 : tmSubst) (sigma2 : tmSubst) (x : ivar) (y : ivar)
    (FRESH_IN : isFreshIn_tmSubst x sigma1 (Lam y Q) = true)
    : forall z : ivar, isFreeIn z Q = true -> consSubst y M (composeSubst sigma2 sigma1) z = composeSubst (consSubst x M sigma2) (consSubst y (Var x) sigma1) z.
  Proof with try now firstorder.
    unfold consSubst, composeSubst; ii. destruct (ivarEqDec y z) as [y_eq_z | y_ne_z]; [red in y_eq_z | unfold member in y_ne_z].
    - simpl. destruct (ivarEqDec x x)...
    - unfold isFreshIn_tmSubst in FRESH_IN. rewrite forallb_true_iff in FRESH_IN.
      assert (claim1 : isFreeIn x (sigma1 z) = false).
      { eapply negb_true_iff, FRESH_IN, getFVs_isFreeIn. resolver. }
      assert (claim2 : forall u : ivar, isFreeIn u (sigma1 z) = true -> consSubst x M sigma2 u = sigma2 u).
      { unfold consSubst. intros u FREE_IN. destruct (ivarEqDec x u) as [x_eq_u | x_ne_u]; [red in x_eq_u | unfold member in x_ne_u]...
        subst u. now rewrite claim1 in FREE_IN.
      }
      eapply equivSubstWrt_spec...
  Qed.

  Definition FreeInWrt (x : ivar) (sigma : tmSubst) (M : tmExpr) : Prop :=
    exists y : ivar, isFreeIn y M = true /\ isFreeIn x (sigma y) = true
  .

  Theorem FreeInWrt_iff (M : tmExpr) (z : ivar) (sigma : tmSubst)
    : FreeInWrt z sigma M <-> isFreeIn z (runSubst sigma M) = true.
  Proof with resolver.
    symmetry. revert z sigma. unfold FreeInWrt. induction M as [x | P1 IH1 P2 IH2 | y Q IH]; simpl.
    - ii. split; des... exists (x)...
    - ii... split.
      + intros [FREE_IN | FREE_IN].
        { assert (to_show : exists y : ivar, isFreeIn y P1 = true /\ isFreeIn z (sigma y) = true)... desnw. exists (y)... }
        { assert (to_show : exists y : ivar, isFreeIn y P2 = true /\ isFreeIn z (sigma y) = true)... desnw. exists (y)... }
      + des...
    - intros x sigma... split.
      + intros [FREE_IN z_ne].
        pose proof (proj1 (IH x _) FREE_IN) as [w [FREE_IN_w_Q FREE_IN']]. unfold consSubst in FREE_IN'.
        set (z := chi sigma (Lam y Q)). destruct (ivarEqDec y w) as [y_eq_w | y_ne_w]; [red in y_eq_w | unfold member in y_ne_w].
        { subst y. unfold consSubst in *. destruct (ivarEqDec w w)...
          unfold isFreeIn in FREE_IN'. rewrite Nat.eqb_eq in FREE_IN'...
        }
        { exists (w)... }
      + rename y into z. intros [y [FREE_IN1 FREE_IN2]]. set (w := chi sigma (Lam z Q))...
        destruct FREE_IN1 as [FREE_IN1 y_ne_z]. destruct (ivarEqDec w x) as [w_eq_x | w_ne_x]; [red in w_eq_x | unfold member in w_ne_x].
        { subst x. pose proof (chi_spec (Lam z Q) sigma) as claim1. fold w in claim1. unfold isFreshIn_tmSubst in claim1. rewrite forallb_true_iff in claim1.
          specialize claim1 with (x := y). rewrite getFVs_isFreeIn, negb_true_iff in claim1. rewrite claim1 in FREE_IN2...
        }
        { split... eapply IH. exists (y). split... unfold consSubst. destruct (ivarEqDec z y)... }
  Qed.

  Lemma chi_ext (sigma : tmSubst) (sigma' : tmSubst) (M : tmExpr) (M' : tmExpr)
    (EQUIV : forall z : ivar, FreeInWrt z sigma M <-> FreeInWrt z sigma' M')
    : chi sigma M = chi sigma' M'.
  Proof with try now firstorder.
    unfold chi, FreeInWrt in *. eapply eq_congruence.
    assert (lemma1 : forall z : ivar, In z (flat_map (fun y : ivar => getFVs (sigma y)) (getFVs M)) <-> In z (flat_map (fun y : ivar => getFVs (sigma' y)) (getFVs M'))).
    { intros z. do 2 rewrite in_flat_map. split; intros [x [FREE_IN1 FREE_IN2]]; rewrite getFVs_isFreeIn in FREE_IN1, FREE_IN2.
      - assert (claim1 : exists y : ivar, isFreeIn y M' = true /\ isFreeIn z (sigma' y) = true).
        { eapply EQUIV. exists (x)... }
        desnw. exists (y). do 2 rewrite getFVs_isFreeIn...
      - assert (claim1 : exists y : ivar, isFreeIn y M = true /\ isFreeIn z (sigma y) = true).
        { eapply EQUIV. exists (x)... }
        desnw. exists (y). do 2 rewrite getFVs_isFreeIn...
    }
    pose proof (claim1 := maxs_ext _ _ lemma1).
    enough (to_show : forall xs : list ivar, forall f : ivar -> list ivar, maxs (map (fun x : ivar => maxs (f x)) xs) = maxs (flat_map f xs)).
    { unfold last_ivar. do 2 rewrite to_show... }
    induction xs as [ | x xs IH]; simpl; ii... rewrite maxs_app...
  Qed.

  Theorem composeSubst_spec (M : tmExpr) (sigma1 : tmSubst) (sigma2 : tmSubst)
    : runSubst sigma2 (runSubst sigma1 M) = runSubst (composeSubst sigma2 sigma1) M.
  Proof with resolver.
    revert sigma1 sigma2. induction M as [x | P1 IH1 P2 IH2 | y Q IH]; simpl...
    - rewrite IH1, IH2...
    - enough (to_show : chi sigma2 (runSubst sigma1 (Lam y Q)) = chi (composeSubst sigma2 sigma1) (Lam y Q)).
      { set (x := chi sigma1 (Lam y Q)).
        set (x' := chi sigma2 (Lam x (runSubst (consSubst y (Var x) sigma1) Q))).
        set (z := chi (composeSubst sigma2 sigma1) (Lam y Q)).
        pose proof (claim1 := IH (consSubst y (Var x) sigma1) (consSubst x (Var x') sigma2)). rewrite claim1.
        pose proof (claim2 := distr_compose_cons Q (Var x') sigma1 sigma2 x y).
        assert (claim3 : runSubst (composeSubst (consSubst x (Var x') sigma2) (consSubst y (Var x) sigma1)) Q = runSubst (consSubst y (Var x') (composeSubst sigma2 sigma1)) Q).
        { eapply equivSubstWrt_spec. ii. erewrite claim2... eapply chi_spec. }
        rewrite claim3. replace (x') with (z)...
      }
      rename y into x. set (y := chi sigma1 (Lam x Q)).
      assert (lemma1 : forall y' : ivar, (exists x' : ivar, isFreeIn x' (Lam y (runSubst (consSubst x (Var y) sigma1) Q)) = true /\ isFreeIn y' (sigma2 x') = true) -> (exists u : ivar, isFreeIn u (Lam x Q) = true /\ isFreeIn y' (composeSubst sigma2 sigma1 u) = true)).
      { intros y' [x' [FREE_IN1 FREE_IN2]]... destruct FREE_IN1 as [FREE_IN1 x'_ne_y].
        pose proof (proj2 (FreeInWrt_iff Q x' (consSubst x (Var y) sigma1)) FREE_IN1) as [u [FREE_IN FREE_IN']].
        unfold consSubst in FREE_IN'. destruct (ivarEqDec x u) as [x_eq_u | x_ne_u]; [red in x_eq_u | unfold member in x_ne_u].
        - unfold isFreeIn in FREE_IN'. rewrite Nat.eqb_eq in FREE_IN'...
        - exists (u). split... eapply FreeInWrt_iff...
      }
      assert (lemma2 : forall y' : ivar, (exists x' : ivar, isFreeIn x' (Lam x Q) = true /\ isFreeIn y' (composeSubst sigma2 sigma1 x') = true) -> (exists u : ivar, isFreeIn u (Lam y (runSubst (consSubst x (Var y) sigma1) Q)) = true /\ isFreeIn y' (sigma2 u) = true)).
      { intros y' [x' [FREE_IN1 FREE_IN2]]. simpl in FREE_IN1. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq in FREE_IN1. destruct FREE_IN1 as [FREE_IN1 x'_ne_x].
        pose proof (proj2 (FreeInWrt_iff (sigma1 x') y' sigma2) FREE_IN2) as [u [FREE_IN FREE_IN']].
        assert (claim1 : isFreeIn u (runSubst (consSubst x (Var y) sigma1) Q) = true).
        { eapply FreeInWrt_iff. exists (x'). split... unfold consSubst. destruct (ivarEqDec x x')... }
        exists (u). split... split... subst u.
        enough (it_is_sufficient_to_show : isFreeIn y (sigma1 x') = false) by now rewrite FREE_IN in it_is_sufficient_to_show.
        pose proof (therefore := chi_spec (Lam x Q) sigma1).
        unfold isFreshIn_tmSubst in therefore. rewrite forallb_true_iff in therefore.
        eapply negb_true_iff, therefore. rewrite getFVs_isFreeIn...
      }
      eapply chi_ext...
  Qed.

  Corollary compose_one (M : tmExpr) (N : tmExpr) (sigma : tmSubst) (x : ivar)
    : runSubst (consSubst x (runSubst sigma N) sigma) M = runSubst sigma (runSubst (consSubst x N nilSubst) M).
  Proof with try now firstorder.
    replace (runSubst (consSubst x (runSubst sigma N) sigma) M) with (runSubst (consSubst x (runSubst sigma N) (composeSubst sigma nilSubst)) M).
    replace (runSubst (consSubst x (runSubst sigma N) (composeSubst sigma nilSubst)) M) with (runSubst (composeSubst sigma (consSubst x N nilSubst)) M).
    rewrite composeSubst_spec... all: eapply equivSubstWrt_spec, equivSubstWrt_trivialIntro; unfold composeSubst, consSubst, nilSubst; intros z; destruct (ivarEqDec x z)...
  Qed.

  Theorem consSubst_spec (y : ivar) (z : ivar) (Q : tmExpr) (M : tmExpr) (sigma : tmSubst)
    (NOT_FREE_IN : isFreeIn z (Lam y Q) = false)
    : runSubst (consSubst y M sigma) Q = runSubst (consSubst z M sigma) (runSubst (consSubst y (Var z) nilSubst) Q).
  Proof with resolver.
    rewrite composeSubst_spec. eapply equivSubstWrt_spec.
    intros w FREE_IN. unfold consSubst, nilSubst, composeSubst.
    destruct (ivarEqDec y w) as [y_eq_w | y_ne_w]; [red in y_eq_w | unfold member in y_ne_w]; simpl.
    - destruct (ivarEqDec z z)...
    - destruct (ivarEqDec z w) as [z_eq_w | z_ne_w]; [red in z_eq_w | unfold member in z_ne_w]...
      subst w. desnw... now rewrite NOT_FREE_IN in FREE_IN.
  Qed.

  End SUBSTITUTION.

End UntypedLambdaCalculus.
