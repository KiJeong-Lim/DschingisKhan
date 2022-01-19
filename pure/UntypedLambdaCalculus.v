Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.pure.DomainTheory.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module UntypedLamdbdaCalculus.

  Import ListNotations EqFacts MyUtilities BasicSetoidTheory MyEnsemble BasicPosetTheory.

  Class isPreLambdaStructure (DOM : Type) `{DOM_isSetoid : isSetoid DOM} : Type :=
    { runApp : DOM -> arrow DOM DOM
    ; runLam : arrow DOM DOM -> DOM
    ; runApp_preserves_eqProp :
      forall x1 : DOM,
      forall y1 : DOM,
      forall x2 : DOM,
      forall y2 : DOM,
      x1 == x2 ->
      y1 == y2 ->
      runApp x1 y1 == runApp x2 y2
    ; runLam_preserves_eqProp :
      forall f1 : arrow DOM DOM,
      forall f2 : arrow DOM DOM,
      f1 == f2 ->
      runLam f1 == runLam f2
    }
  .

  Class isUntypedLambdaStructure (DOM : Type) `{DOM_isSetoid : isSetoid DOM} : Type :=
    { UntypedLambdaStructure_requiresPreLambdaStructure :> @isPreLambdaStructure DOM DOM_isSetoid
    ; satisfiesBetaAxiom :
      forall f : arrow DOM DOM,
      runApp (runLam f) == f
    }
  .

  Section UNTYPED_LAMBDA_CALCULUS_WITH_CONSTANT.

  Definition ivar : Set :=
    nat
  .

  Definition ivar_eq_dec :
    forall x : ivar,
    forall y : ivar,
    {x = y} + {x <> y}.
  Proof.
    exact (fun x y => Nat.eq_dec x y).
  Defined.

  Variable CON : Set.

  Inductive tm : Set :=
  | Var (x : ivar) : tm
  | Con (c : CON) : tm
  | App (P1 : tm) (P2 : tm) : tm
  | Lam (y : ivar) (Q : tm) : tm
  .

  Lemma tm_eq_dec :
    (forall c1 : CON, forall c2 : CON, {c1 = c2} + {c1 <> c2}) ->
    (forall t1 : tm, forall t2 : tm, {t1 = t2} + {t1 <> t2}).
  Proof with ((left; congruence) || (right; congruence)) || eauto.
    intros CON_eq_dec.
    induction t1 as [x1 | c1 | P1_1 IH1 P2_1 IH2 | y1 Q1 IH1]; destruct t2 as [x2 | c2 | P1_2 P2_2 | y2 Q2]...
    - destruct (ivar_eq_dec x1 x2)...
    - destruct (CON_eq_dec c1 c2)...
    - destruct (IH1 P1_2); destruct (IH2 P2_2)...
    - destruct (ivar_eq_dec y1 y2); destruct (IH1 Q2)...
  Defined.

  Fixpoint getFVs (M : tm) {struct M} : list ivar :=
    match M with
    | Var x => [x]
    | Con c => []
    | App P1 P2 => getFVs P1 ++ getFVs P2
    | Lam y Q => remove ivar_eq_dec y (getFVs Q)
    end
  .

  Fixpoint isFreeIn (z : ivar) (M : tm) {struct M} : bool :=
    match M with
    | Var x => Nat.eqb x z
    | Con c => false
    | App P1 P2 => isFreeIn z P1 || isFreeIn z P2
    | Lam y Q => isFreeIn z Q && negb (Nat.eqb z y)
    end
  .

  Lemma getFVs_isFreeIn (M : tm) :
    forall z : ivar,
    In z (getFVs M) <-> isFreeIn z M = true.
  Proof with auto_rewrite.
    induction M...
  Qed.

  Section SUBSTITUTION. (* Reference: "https://github.com/ernius/formalmetatheory-stoughton/tree/7eea5b526ec58a49838daa7b21b02fafcbf9065e" *)

  Definition tmSubst : Set :=
    ivar -> tm
  .

  Definition tmSubst_nil : tmSubst :=
    Var
  .

  Definition tmSubst_cons : ivar -> tm -> tmSubst -> tmSubst :=
    fun x : ivar =>
    fun M : tm =>
    fun sigma : tmSubst =>
    fun y : ivar =>
    if ivar_eq_dec x y
    then M
    else sigma y
  .

  Fixpoint tmSubstMaker (sigma : list (ivar * tm)) {struct sigma} : tmSubst :=
    match sigma with
    | [] => tmSubst_nil
    | item :: sigma' => tmSubst_cons (fst item) (snd item) (tmSubstMaker sigma')
    end
  .

  Definition get_max_ivar : tm -> ivar :=
    fun M : tm =>
    fold_right_max_0 (getFVs M)
  .

  Lemma get_max_ivar_lt (M : tm) :
    forall x : ivar,
    get_max_ivar M < x ->
    isFreeIn x M = false.
  Proof with eauto.
    assert (claim1 := le_gt_False).
    intros x.
    enough (it_is_sufficient_to_show : get_max_ivar M < x -> ~ In x (getFVs M)) by now rewrite getFVs_isFreeIn, not_true_iff_false in it_is_sufficient_to_show.
    assert (In x (getFVs M) -> fold_right_max_0 (getFVs M) >= x) by now apply fold_right_max_0_in.
    enough (therefore : fold_right_max_0 (getFVs M) >= x -> fold_right_max_0 (getFVs M) < x -> False)...
  Qed.

  Definition isFreshIn_tmSubst : ivar -> tmSubst -> tm -> bool :=
    fun x : ivar =>
    fun sigma : tmSubst =>
    fun M : tm =>
    forallb (fun z : ivar => negb (isFreeIn x (sigma z))) (getFVs M)
  .

  Definition chi : tmSubst -> tm -> ivar :=
    fun sigma : tmSubst => 
    fun M : tm =>
    S (fold_right_max_0 (map (fun x : ivar => get_max_ivar (sigma x)) (getFVs M)))
  .

  Theorem main_property_of_chi :
    forall M : tm,
    forall sigma : tmSubst,
    isFreshIn_tmSubst (chi sigma M) sigma M = true.
  Proof with auto_rewrite.
    assert ( claim1 :
      forall sigma : tmSubst,
      forall M : tm,
      forall x : ivar,
      isFreeIn x M = true ->
      isFreeIn (chi sigma M) (sigma x) = false
    ).
    { intros sigma M x H.
      enough (claim1_aux : get_max_ivar (sigma x) < chi sigma M) by now apply get_max_ivar_lt.
      unfold chi, fold_right_max_0.
      enough (claim1_aux : fold_right max 0 (map (fun z : ivar => get_max_ivar (sigma z)) (getFVs M)) >= get_max_ivar (sigma x)) by now apply le_intro_S_n_le_S_m.
      rewrite <- getFVs_isFreeIn in H.
      apply fold_right_max_0_in...
    }
    unfold isFreshIn_tmSubst...
    apply claim1, getFVs_isFreeIn...
  Qed.

  Lemma chi_nil : 
    forall M : tm,
    isFreeIn (chi tmSubst_nil M) M = false.
  Proof with auto_rewrite.
    intros M.
    assert (claim1 : isFreshIn_tmSubst (chi tmSubst_nil M) tmSubst_nil M = true) by apply main_property_of_chi.
    unfold isFreshIn_tmSubst in claim1.
    rewrite forallb_true_iff in claim1.
    simpl in claim1.
    apply not_true_iff_false.
    intros H.
    assert (claim2 : negb (chi tmSubst_nil M =? chi tmSubst_nil M) = true) by now apply claim1, getFVs_isFreeIn...
  Qed.

  Fixpoint run_tmSubst_on_tm (sigma : tmSubst) (M : tm) {struct M} : tm :=
    match M with
    | Var x => sigma x
    | Con c => Con c
    | App P1 P2 => App (run_tmSubst_on_tm sigma P1) (run_tmSubst_on_tm sigma P2)
    | Lam y Q =>
      let z : ivar := chi sigma M in
      Lam z (run_tmSubst_on_tm (tmSubst_cons y (Var z) sigma) Q)
    end
  .

  Theorem main_property_isFreshIn_tmSubst :
    forall M : tm,
    forall z : ivar,
    forall sigma : tmSubst,
    isFreshIn_tmSubst z sigma M = true <-> isFreeIn z (run_tmSubst_on_tm sigma M) = false.
  Proof with auto_rewrite.
    induction M; unfold isFreshIn_tmSubst; simpl...
    split; intros H.
    - destruct (ivar_eq_dec z (chi sigma (Lam y M)))...
      left.
      apply IHM.
      unfold isFreshIn_tmSubst, tmSubst_cons.
      apply forallb_true_iff.
      intros x H0.
      destruct (ivar_eq_dec y x); [apply negb_true_iff, Nat.eqb_neq | apply H, in_in_remove]...
    - auto_rewrite.
      destruct H0 as [H0 H1].
      destruct H as [H | H].
      + assert (claim1 : isFreshIn_tmSubst z (tmSubst_cons y (Var (chi sigma (Lam y M))) sigma) M = true) by now apply IHM.
        unfold isFreshIn_tmSubst in claim1.
        rewrite forallb_true_iff in claim1.
        assert (claim2 := claim1 x H0).
        unfold tmSubst_cons in claim2.
        destruct (ivar_eq_dec y x)...
      + assert (claim3 : isFreshIn_tmSubst z sigma (Lam y M) = true) by now rewrite H; apply main_property_of_chi.
        unfold isFreshIn_tmSubst in claim3.
        rewrite forallb_true_iff in claim3.
        apply negb_true_iff, claim3.
        rewrite getFVs_isFreeIn.
        auto_rewrite.
        rewrite <- getFVs_isFreeIn...
  Qed.

  Definition equiv_tmSubst_wrt : tmSubst -> tmSubst -> tm -> Prop :=
    fun sigma1 : tmSubst =>
    fun sigma2 : tmSubst =>
    fun M : tm =>
    forall x : ivar,
    isFreeIn x M = true ->
    sigma1 x = sigma2 x
  .

  Lemma property1_of_equiv_tmSubst_wrt :
    forall sigma1 : tmSubst,
    forall sigma2 : tmSubst,
    (forall x : ivar, sigma1 x = sigma2 x) ->
    forall M : tm,
    equiv_tmSubst_wrt sigma1 sigma2 M.
  Proof with try now firstorder.
    unfold equiv_tmSubst_wrt...
  Qed.

  Lemma chi_equiv_tmSubst_wrt :
    forall sigma1 : tmSubst,
    forall sigma2 : tmSubst,
    forall M : tm,
    equiv_tmSubst_wrt sigma1 sigma2 M ->
    chi sigma1 M = chi sigma2 M.
  Proof with auto_rewrite.
    unfold chi.
    intros sigma1 sigma2 M H.
    enough (it_is_sufficient_to_show : (map (fun x : ivar => get_max_ivar (sigma1 x)) (getFVs M)) = (map (fun x : ivar => get_max_ivar (sigma2 x)) (getFVs M))) by congruence.
    apply map_ext_in.
    intros x H0.
    rewrite (H x (proj1 (getFVs_isFreeIn M x) H0))...
  Qed.

  Theorem main_property_of_equiv_tmSubst_wrt :
    forall M : tm,
    forall sigma1 : tmSubst,
    forall sigma2 : tmSubst,
    equiv_tmSubst_wrt sigma1 sigma2 M ->
    run_tmSubst_on_tm sigma1 M = run_tmSubst_on_tm sigma2 M.
  Proof with auto_rewrite.
    induction M; simpl.
    - intros sigma1 sigma2 H.
      apply H...
    - reflexivity.
    - intros sigma1 sigma2 H.
      enough (claim1 : equiv_tmSubst_wrt sigma1 sigma2 M1).
      enough (claim2 : equiv_tmSubst_wrt sigma1 sigma2 M2).
      rewrite (IHM1 sigma1 sigma2 claim1), (IHM2 sigma1 sigma2 claim2)...
      all: intros x H0; apply H...
    - intros sigma1 sigma2 H.
      enough (claim3 : equiv_tmSubst_wrt (tmSubst_cons y (Var (chi sigma1 (Lam y M))) sigma1) (tmSubst_cons y (Var (chi sigma2 (Lam y M))) sigma2) M).
      assert (claim4 : chi sigma1 (Lam y M) = chi sigma2 (Lam y M)) by now apply chi_equiv_tmSubst_wrt.
      rewrite (IHM (tmSubst_cons y (Var (chi sigma1 (Lam y M))) sigma1) (tmSubst_cons y (Var (chi sigma2 (Lam y M))) sigma2) claim3), claim4...
      intros x H0.
      unfold tmSubst_cons.
      destruct (ivar_eq_dec y x).
      + rewrite (chi_equiv_tmSubst_wrt sigma1 sigma2 (Lam y M) H)...
      + apply H...
  Qed.

  Lemma trivial_tmSubst :
    forall x : ivar,
    forall M : tm,
    run_tmSubst_on_tm (tmSubst_cons x (Var x) tmSubst_nil) M = run_tmSubst_on_tm tmSubst_nil M.
  Proof with try now firstorder.
    unfold tmSubst_cons.
    intros x M.
    apply main_property_of_equiv_tmSubst_wrt.
    intros y H.
    destruct (ivar_eq_dec x y)...
  Qed.

  Definition compose_tmSubst : tmSubst -> tmSubst -> tmSubst :=
    fun sigma2 : tmSubst =>
    fun sigma1 : tmSubst =>
    fun x : ivar =>
    run_tmSubst_on_tm sigma2 (sigma1 x)
  .

  Lemma distri_compose_cons :
    forall M : tm,
    forall N : tm,
    forall sigma1 : tmSubst,
    forall sigma2 : tmSubst,
    forall x : ivar,
    forall y : ivar,
    isFreshIn_tmSubst y sigma1 (Lam x M) = true ->
    forall z : ivar,
    isFreeIn z M = true ->
    tmSubst_cons x N (compose_tmSubst sigma2 sigma1) z = compose_tmSubst (tmSubst_cons y N sigma2) (tmSubst_cons x (Var y) sigma1) z.
  Proof with try now firstorder.
    intros M N sigma1 sigma2 x y H z H0.
    unfold tmSubst_cons, compose_tmSubst.
    destruct (ivar_eq_dec x z).
    - simpl.
      destruct (ivar_eq_dec y y)...
    - unfold isFreshIn_tmSubst in H.
      rewrite forallb_true_iff in H.
      assert (claim1 : isFreeIn y (sigma1 z) = false) by now apply negb_true_iff, H, getFVs_isFreeIn; auto_rewrite.
      assert ( claim2 :
        forall u : ivar,
        isFreeIn u (sigma1 z) = true ->
        tmSubst_cons y N sigma2 u = sigma2 u
      ).
      { unfold tmSubst_cons.
        intros u H1.
        destruct (ivar_eq_dec y u); subst...
        rewrite claim1 in H1...
      }
      apply main_property_of_equiv_tmSubst_wrt...
  Qed.

  Corollary distri_compose_cons_for_chi :
    forall M : tm,
    forall N : tm,
    forall sigma1 : tmSubst,
    forall sigma2 : tmSubst,
    forall x : ivar,
    let y : ivar := chi sigma1 (Lam x M) in
    forall z : ivar,
    isFreeIn z M = true ->
    tmSubst_cons x N (compose_tmSubst sigma2 sigma1) z = compose_tmSubst (tmSubst_cons y N sigma2) (tmSubst_cons x (Var y) sigma1) z.
  Proof with eauto using distri_compose_cons, main_property_of_chi.
    intros M N sigma1 sigma2 x y z H...
  Qed.

  Definition FreeIn_wrt : ivar -> tmSubst -> tm -> Prop :=
    fun x : ivar =>
    fun sigma : tmSubst =>
    fun M : tm =>
    exists y : ivar, isFreeIn y M = true /\ isFreeIn x (sigma y) = true
  .

  Theorem isFreeIn_wrt_true_iff (M : tm) :
    forall z : ivar,
    forall sigma : tmSubst,
    isFreeIn z (run_tmSubst_on_tm sigma M) = true <-> FreeIn_wrt z sigma M.
  Proof with auto_rewrite.
    unfold FreeIn_wrt.
    induction M; simpl.
    - intros z sigma.
      split; intros H.
      + exists x...
      + destruct H as [y [H H0]]...
    - firstorder.
      inversion H.
    - intros z sigma...
      split.
      + intros [H | H]; [assert (it_is_sufficient_to_show : exists y : ivar, isFreeIn y M1 = true /\ isFreeIn z (sigma y) = true) | assert (it_is_sufficient_to_show : exists y : ivar, isFreeIn y M2 = true /\ isFreeIn z (sigma y) = true)]...
        all: destruct it_is_sufficient_to_show as [y [H0 H1]]; exists y...
      + intros [y [H H0]]...
    - intros x sigma...
      split.
      + intros [H H0].
        destruct (proj1 (IHM x (tmSubst_cons y (Var (chi sigma (Lam y M))) sigma)) H) as [w [H1 H2]].
        set (z := chi sigma (Lam y M)).
        fold z in H, H0, H2.
        destruct (ivar_eq_dec y w).
        { subst.
          unfold tmSubst_cons in H2.
          destruct (ivar_eq_dec w w)...
          unfold isFreeIn in H2.
          rewrite Nat.eqb_eq in H2...
        }
        { exists w...
          unfold tmSubst_cons in H2.
          destruct (ivar_eq_dec y w)...
        }
      + rename y into z.
        intros [y [H H0]].
        set (w := chi sigma (Lam z M))...
        destruct (ivar_eq_dec w x).
        { subst.
          assert (isFreshIn_tmSubst w sigma (Lam z M) = true) by now apply main_property_of_chi.
          unfold isFreshIn_tmSubst in H1.
          rewrite forallb_true_iff in H1.
          enough (claim1 : isFreeIn w (sigma y) = false) by now rewrite H0 in claim1.
          apply negb_true_iff, H1, getFVs_isFreeIn...
        }
        { split...
          apply IHM.
          exists y.
          split...
          unfold tmSubst_cons.
          destruct (ivar_eq_dec z y)...
        }
  Qed.

  Lemma chi_ext :
    forall sigma : tmSubst,
    forall sigma' : tmSubst,
    forall M : tm,
    forall M' : tm,
    (forall z : ivar, FreeIn_wrt z sigma M <-> FreeIn_wrt z sigma' M') ->
    chi sigma M = chi sigma' M'.
  Proof with try now firstorder.
    unfold chi, FreeIn_wrt.
    intros sigma sigma' M M' H.
    enough (it_is_sufficient_to_show : fold_right_max_0 (map (fun x : ivar => get_max_ivar (sigma x)) (getFVs M)) = fold_right_max_0 (map (fun x : ivar => get_max_ivar (sigma' x)) (getFVs M'))) by congruence.
    assert ( claim1 :
      forall z : ivar,
      In z (flat_map (fun y : ivar => getFVs (sigma y)) (getFVs M)) <-> In z (flat_map (fun y : ivar => getFVs (sigma' y)) (getFVs M'))
    ).
    { intros z.
      repeat (rewrite in_flat_map).
      split; intros [x H0]; rewrite getFVs_isFreeIn in H0.
      1: assert (claim2_aux : exists y : ivar, isFreeIn y M' = true /\ isFreeIn z (sigma' y) = true) by now apply H; exists x; rewrite getFVs_isFreeIn in H0; firstorder.
      2: assert (claim2_aux : exists y : ivar, isFreeIn y M = true /\ isFreeIn z (sigma y) = true) by now apply H; exists x; rewrite getFVs_isFreeIn in H0; firstorder.
      all: destruct claim2_aux as [y [H1 H2]]; exists y; repeat (rewrite getFVs_isFreeIn)...
    }
    assert (claim2 : fold_right_max_0 (flat_map (fun y : ivar => getFVs (sigma y)) (getFVs M)) = fold_right_max_0 (flat_map (fun y : ivar => getFVs (sigma' y)) (getFVs M'))) by now apply fold_right_max_0_ext.
    unfold get_max_ivar.
    enough (claim3 : forall xs : list ivar, forall f : ivar -> list ivar, fold_right_max_0 (map (fun x : ivar => fold_right_max_0 (f x)) xs) = fold_right_max_0 (flat_map f xs)) by now repeat (rewrite claim3).
    induction xs; simpl; intros f...
    rewrite fold_right_max_0_app...
  Qed.

  Theorem main_property_of_compose_tmSubst :
    forall M : tm,
    forall sigma1 : tmSubst,
    forall sigma2 : tmSubst,
    run_tmSubst_on_tm sigma2 (run_tmSubst_on_tm sigma1 M) = run_tmSubst_on_tm (compose_tmSubst sigma2 sigma1) M.
  Proof with auto_rewrite.
    induction M; simpl...
    - rewrite IHM1, IHM2...
    - enough (it_is_sufficient_to_show : chi sigma2 (run_tmSubst_on_tm sigma1 (Lam y M)) = chi (compose_tmSubst sigma2 sigma1) (Lam y M)).
      { set (x := chi sigma1 (Lam y M)).
        set (x' := chi sigma2 (Lam x (run_tmSubst_on_tm (tmSubst_cons y (Var x) sigma1) M))).
        set (z := chi (compose_tmSubst sigma2 sigma1) (Lam y M)).
        assert (claim1 := IHM (tmSubst_cons y (Var x) sigma1) (tmSubst_cons x (Var x') sigma2)).
        rewrite claim1.
        assert (claim2 := distri_compose_cons_for_chi M (Var x') sigma1 sigma2 y).
        assert (claim3 : run_tmSubst_on_tm (compose_tmSubst (tmSubst_cons x (Var x') sigma2) (tmSubst_cons y (Var x) sigma1)) M = run_tmSubst_on_tm (tmSubst_cons y (Var x') (compose_tmSubst sigma2 sigma1)) M) by now apply main_property_of_equiv_tmSubst_wrt; firstorder.
        rewrite claim3.
        replace x' with z...
      }
      rename y into x.
      set (y := chi sigma1 (Lam x M)).
      assert ( claim1 :
        forall y' : ivar,
        (exists x' : ivar, isFreeIn x' (Lam y (run_tmSubst_on_tm (tmSubst_cons x (Var y) sigma1) M)) = true /\ isFreeIn y' (sigma2 x') = true) ->
        (exists u : ivar, isFreeIn u (Lam x M) = true /\ isFreeIn y' (compose_tmSubst sigma2 sigma1 u) = true)
      ).
      { intros y' [x' [H H0]]...
        destruct H as [H H1].
        destruct (proj1 (isFreeIn_wrt_true_iff M x' (tmSubst_cons x (Var y) sigma1)) H) as [u [H2 H3]].
        unfold tmSubst_cons in H3.
        destruct (ivar_eq_dec x u).
        - unfold isFreeIn in H3.
          rewrite Nat.eqb_eq in H3...
        - exists u.
          split...
          apply (proj2 (isFreeIn_wrt_true_iff (sigma1 u) y' sigma2))...
      }
      assert ( claim2 :
        forall y' : ivar,
        (exists x' : ivar, isFreeIn x' (Lam x M) = true /\ isFreeIn y' (compose_tmSubst sigma2 sigma1 x') = true) ->
        (exists u : ivar, isFreeIn u (Lam y (run_tmSubst_on_tm (tmSubst_cons x (Var y) sigma1) M)) = true /\ isFreeIn y' (sigma2 u) = true)
      ).
      { intros y' [x' [H H0]].
        simpl in H.
        rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq in H.
        destruct H as [H H1].
        destruct (proj1 (isFreeIn_wrt_true_iff (sigma1 x') y' sigma2) H0) as [u [H2 H3]].
        assert (claim2_aux : isFreeIn u (run_tmSubst_on_tm (tmSubst_cons x (Var y) sigma1) M) = true).
        { apply isFreeIn_wrt_true_iff.
          exists x'.
          split...
          unfold tmSubst_cons.
          destruct (ivar_eq_dec x x')...
        }
        exists u.
        split...
        split...
        subst.
        enough (it_is_sufficient_to_show : isFreeIn y (sigma1 x') = false) by now rewrite H2 in it_is_sufficient_to_show.
        assert (therefore := main_property_of_chi (Lam x M) sigma1).
        unfold isFreshIn_tmSubst in therefore.
        rewrite forallb_true_iff in therefore.
        apply negb_true_iff, therefore.
        rewrite getFVs_isFreeIn...
      }
      apply chi_ext...
  Qed.

  Corollary compose_one :
    forall M : tm,
    forall N : tm,
    forall sigma : tmSubst,
    forall x : ivar,
    run_tmSubst_on_tm (tmSubst_cons x (run_tmSubst_on_tm sigma N) sigma) M = run_tmSubst_on_tm sigma (run_tmSubst_on_tm (tmSubst_cons x N tmSubst_nil) M).
  Proof with try now firstorder.
    intros M N sigma x.
    replace (run_tmSubst_on_tm (tmSubst_cons x (run_tmSubst_on_tm sigma N) sigma) M) with (run_tmSubst_on_tm (tmSubst_cons x (run_tmSubst_on_tm sigma N) (compose_tmSubst sigma tmSubst_nil)) M).
    replace (run_tmSubst_on_tm (tmSubst_cons x (run_tmSubst_on_tm sigma N) (compose_tmSubst sigma tmSubst_nil)) M) with (run_tmSubst_on_tm (compose_tmSubst sigma (tmSubst_cons x N tmSubst_nil)) M).
    rewrite main_property_of_compose_tmSubst...
    all: apply main_property_of_equiv_tmSubst_wrt, property1_of_equiv_tmSubst_wrt; unfold compose_tmSubst, tmSubst_cons, tmSubst_nil; intros z; destruct (ivar_eq_dec x z)...
  Qed.

  Theorem main_property_of_tmSubst_cons :
    forall x : ivar,
    forall z : ivar,
    forall M : tm,
    forall N : tm,
    forall sigma : tmSubst,
    isFreeIn z (Lam x M) = false ->
    run_tmSubst_on_tm (tmSubst_cons x N sigma) M = run_tmSubst_on_tm (tmSubst_cons z N sigma) (run_tmSubst_on_tm (tmSubst_cons x (Var z) tmSubst_nil) M).
  Proof with auto_rewrite.
    intros x z M N sigma H.
    rewrite (main_property_of_compose_tmSubst M (tmSubst_cons x (Var z) tmSubst_nil) (tmSubst_cons z N sigma)).
    apply main_property_of_equiv_tmSubst_wrt.
    intros w H0.
    unfold tmSubst_cons, tmSubst_nil, compose_tmSubst.
    destruct (ivar_eq_dec x w) as [Heq | Hne]; simpl.
    - destruct (ivar_eq_dec z z)...
    - destruct (ivar_eq_dec z w) as [H_yes | H_no]...
      subst.
      destruct H as [H | H]; [rewrite H0 in H | contradiction Hne]...
  Qed.

  End SUBSTITUTION.

  Section PreliminariesOfSemantics.

  Context {D : Type}.

  Let evalEnv : Type :=
    ivar -> D
  .

  Variable runCon : CON -> D.

  Context `{D_isSetoid : isSetoid D} `{D_isPreLambdaStructure : @isPreLambdaStructure D D_isSetoid}.

  Fixpoint eval_tm (E : evalEnv) (M : tm) {struct M} : D :=
    match M with
    | Var x => E x
    | Con c => runCon c
    | App P1 P2 => runApp (eval_tm E P1) (eval_tm E P2)
    | Lam y Q => runLam (fun v : D => eval_tm (fun z : ivar => if ivar_eq_dec y z then v else E z) Q)
    end
  .

  Lemma eval_tm_ext :
    forall M : tm,
    forall E1 : evalEnv,
    forall E2 : evalEnv,
    (forall z : ivar, isFreeIn z M = true -> E1 z == E2 z) ->
    eval_tm E1 M == eval_tm E2 M.
  Proof with auto_rewrite.
    induction M; simpl.
    - intros E1 E2 H.
      apply H...
    - reflexivity.
    - intros E1 E2 H.
      apply runApp_preserves_eqProp; [apply IHM1 | apply IHM2]; intros z H0; apply H...
    - intros E1 E2 H.
      apply runLam_preserves_eqProp.
      intros v.
      apply (IHM (fun z : ivar => if ivar_eq_dec y z then v else E1 z) (fun z : ivar => if ivar_eq_dec y z then v else E2 z))...
      destruct (ivar_eq_dec y z); [subst | apply H]...
  Qed.

  Local Hint Resolve eval_tm_ext : core.

  Theorem run_tmSubst_on_tm_preserves_eval_tm :
    forall M : tm,
    forall sigma : tmSubst,
    forall E : evalEnv,
    eval_tm (fun z : ivar => eval_tm E (sigma z)) M == eval_tm E (run_tmSubst_on_tm sigma M).
  Proof with eauto with *.
    induction M.
    - intros sigma E...
    - intros sigma E...
    - intros sigma E.
      apply runApp_preserves_eqProp...
    - intros sigma E.
      enough (it_is_sufficient_to_show : forall v : D, eval_tm (fun z : ivar => if ivar_eq_dec y z then v else eval_tm E (sigma z)) M == eval_tm (fun z : ivar => if ivar_eq_dec (chi sigma (Lam y M)) z then v else E z) (run_tmSubst_on_tm (tmSubst_cons y (Var (chi sigma (Lam y M))) sigma) M)) by now apply runLam_preserves_eqProp.
      intros v.
      assert (hence := IHM (tmSubst_cons y (Var (chi sigma (Lam y M))) sigma) (fun z : ivar => if ivar_eq_dec (chi sigma (Lam y M)) z then v else E z)).
      assert ( claim1 :
        forall z : ivar,
        isFreeIn z M = true ->
        eval_tm (fun x : ivar => if ivar_eq_dec (chi sigma (Lam y M)) x then v else E x) (tmSubst_cons y (Var (chi sigma (Lam y M))) sigma z) == (if ivar_eq_dec y z then v else eval_tm E (sigma z))
      ).
      { intros z H.
        unfold tmSubst_cons.
        destruct (ivar_eq_dec y z).
        - unfold eval_tm.
          destruct (ivar_eq_dec (chi sigma (Lam y M)) (chi sigma (Lam y M)))...
          contradiction.
        - apply eval_tm_ext.
          intros z' H0.
          destruct (ivar_eq_dec (chi sigma (Lam y M)) z')...
          subst.
          assert (claim1_aux : isFreshIn_tmSubst (chi sigma (Lam y M)) sigma (Lam y M) = true) by now apply main_property_of_chi.
          unfold isFreshIn_tmSubst in claim1_aux.
          rewrite forallb_true_iff in claim1_aux.
          enough (therefore : isFreeIn (chi sigma (Lam y M)) (sigma z) = false) by now rewrite H0 in therefore.
          apply negb_true_iff, claim1_aux, getFVs_isFreeIn.
          auto_rewrite.
      }
      transitivity (eval_tm (fun z : ivar => eval_tm (fun z0 : ivar => if ivar_eq_dec (chi sigma (Lam y M)) z0 then v else E z0) (tmSubst_cons y (Var (chi sigma (Lam y M))) sigma z)) M)...
  Qed.

  End PreliminariesOfSemantics.

  Section SUBTERM.

  Definition position : Set :=
    FinSet 3
  .

  Lemma position_eq_dec :
    forall pos1 : position,
    forall pos2 : position,
    {pos1 = pos2} + {pos1 <> pos2}.
  Proof.
    exact (FinSet_eq_dec 3).
  Defined.

  Lemma list_position_eq_pirrel :
    forall poss1 : list position,
    forall poss2 : list position,
    forall H_EQ1 : poss1 = poss2,
    forall H_EQ2 : poss1 = poss2,
    H_EQ1 = H_EQ2.
  Proof.
    intros poss1; apply (eq_em_implies_eq_pirrel poss1).
    intros poss2; destruct (list_eq_dec position_eq_dec poss1 poss2); [left | right]; assumption.
  Defined.

  Definition POS0 : position :=
    (FZ 2)
  .

  Definition POS1 : position :=
    (FS 2 (FZ 1))
  .

  Definition POS2 : position :=
    (FS 2 (FS 1 (FZ 0)))
  .

  Lemma position_exhausted :
    forall pos : position,
    pos = POS0 \/ pos = POS1 \/ pos = POS2.
  Proof.
    intros pos.
    enough (it_is_sufficient_to_show : forall n : nat, n < 3 -> n = 0 \/ n = 1 \/ n = 2).
    - destruct (it_is_sufficient_to_show (evalFinSet pos) (evalFinSet_lt pos)) as [H | [H | H]]; [set (i := POS0) | set (i := POS1) | set (i := POS2)].
      all: pose (evalFinSet_inj pos i H); eauto.
    - intros n Hlt.
      do 3 (destruct n as [| n]; [tauto | apply lt_elim_S_n_lt_S_m in Hlt]).
      exact (lt_elim_n_lt_0 n Hlt).
  Qed.

  Inductive occurs (M : tm) : list position -> tm -> Set :=
  | OccursRefl : occurs M [] M
  | OccursApp1 (P1 : tm) (P2 : tm) : forall poss : list position, occurs M poss P1 -> occurs M (POS1 :: poss) (App P1 P2)
  | OccursApp2 (P1 : tm) (P2 : tm) : forall poss : list position, occurs M poss P2 -> occurs M (POS2 :: poss) (App P1 P2)
  | OccursLam0 (y : ivar) (Q : tm) : forall poss : list position, occurs M poss Q -> occurs M (POS0 :: poss) (Lam y Q)
  .

  Definition isSuper : tm -> list position -> tm -> Set :=
    fun N : tm =>
    fun poss : list position =>
    fun M : tm =>
    occurs M poss N
  .

  Definition isSuper_reflexivity (N : tm) :
    isSuper N [] N.
  Proof.
    unfold isSuper.
    constructor 1.
  Defined.

  Definition isSuper_transitivity (N : tm) :
    forall poss1 : list position,
    forall M1 : tm,
    isSuper N poss1 M1 ->
    forall poss2 : list position,
    forall M2 : tm,
    isSuper M1 poss2 M2 ->
    isSuper N (poss1 ++ poss2) M2.
  Proof.
    unfold isSuper.
    intros poss1 M1 X1.
    induction X1; intros poss2 M2 X2; simpl.
    - exact X2.
    - constructor 2; apply IHX1; exact X2.
    - constructor 3; apply IHX1; exact X2.
    - constructor 4; apply IHX1; exact X2.
  Defined.

  Local Hint Resolve isSuper_reflexivity isSuper_transitivity : core.

  Lemma occurs_pirrel (CON_eq_dec : forall c1 : CON, forall c2 : CON, {c1 = c2} + {c1 <> c2}) :
    forall N : tm,
    forall M : tm,
    forall poss : list position,
    forall X1 : occurs N poss M,
    forall X2 : occurs N poss M,
    X1 = X2.
  Proof.
    assert (claim1 : forall poss1 : list position, forall poss2 : list position, forall H_EQ1 : poss1 = poss2, forall H_EQ2 : poss1 = poss2, H_EQ1 = H_EQ2) by apply list_position_eq_pirrel.
    assert (claim2 : forall M1 : tm, forall M2 : tm, forall H_EQ1 : M1 = M2, forall H_EQ2 : M1 = M2, H_EQ1 = H_EQ2).
    { intros M1.
      apply eq_em_implies_eq_pirrel.
      intros M2.
      now destruct (tm_eq_dec CON_eq_dec M1 M2); [left | right].
    }
    refine (
      fun N : tm =>
      fix pirrel_fix (M : tm) (poss : list position) (X1 : occurs N poss M) {struct X1} : forall X2 : occurs N poss M, X1 = X2 :=
      match X1 as X' in occurs _ poss' M' return forall X2 : occurs N poss' M', X' = X2 with
      | OccursRefl _ => _
      | OccursApp1 _ P1_1 P2_1 poss_1 X1_1 => _
      | OccursApp2 _ P1_1 P2_1 poss_1 X2_1 => _
      | OccursLam0 _ y_1 Q_1 poss_1 X0_1 => _
      end
    );
    [ set (my_poss := []); set (my_M := N); set (my_X := OccursRefl N)
    | set (my_poss := POS1 :: poss_1); set (my_M := App P1_1 P2_1); set (my_X := OccursApp1 N P1_1 P2_1 poss_1 X1_1)
    | set (my_poss := POS2 :: poss_1); set (my_M := App P1_1 P2_1); set (my_X := OccursApp2 N P1_1 P2_1 poss_1 X2_1)
    | set (my_poss := POS0 :: poss_1); set (my_M := Lam y_1 Q_1); set (my_X := OccursLam0 N y_1 Q_1 poss_1 X0_1)
    ];
    refine (
      fun X2 =>
      match X2 as X' in occurs _ poss' M' return forall H_eq1 : poss' = my_poss, forall H_eq2 : M' = my_M, my_X = (eq_rec M' (occurs N my_poss) (eq_rec poss' (fun poss : list position => occurs N poss M') X' my_poss H_eq1) my_M H_eq2) with
      | OccursRefl _ => _
      | OccursApp1 _ P1_2 P2_2 poss_2 X1_2 => _
      | OccursApp2 _ P1_2 P2_2 poss_2 X2_2 => _
      | OccursLam0 _ y_2 Q_2 poss_2 X0_2 => _
      end (eq_reflexivity my_poss) (eq_reflexivity my_M)
    );
    (try discriminate);
    intros H_eq1 H_eq2;
    inversion H_eq1; subst;
    inversion H_eq2; subst;
    (replace H_eq2 with (eq_reflexivity my_M); [simpl | apply claim2]);
    (replace H_eq1 with (eq_reflexivity my_poss); [simpl | apply claim1]);
    now (reflexivity || apply eq_congruence).
  Qed.

  Definition isSubtermOf : tm -> tm -> Prop :=
    fun N : tm =>
    fun M : tm =>
    exists poss : list position, inhabited (isSuper M poss N)
  .

  Local Program Instance isSubtermOf_isPartialOrder : isPoset tm :=
    { leProp := isSubtermOf
    ; Poset_requiresSetoid :=
      {| eqProp := @eq tm; Setoid_requiresEquivalence := @eq_equivalence tm |}
    }
  .

  Next Obligation with eauto with *.
    split.
    - intros N; exists []...
    - intros N M1 M2 [poss1 [X1]] [poss2 [X2]]; exists (poss2 ++ poss1)...
  Qed.

  Next Obligation with eauto with *.
    set (getRank :=
      fix getRank_fix (M : tm) {struct M} : nat :=
      match M with
      | Var x => O
      | Con c => O
      | App P1 P2 => S (max (getRank_fix P1) (getRank_fix P2))
      | Lam y Q => S (getRank_fix Q)
      end
    ).
    assert (lemma1 := n1_le_max_n1_n2).
    assert (lemma2 := n2_le_max_n1_n2).
    assert (lemma3 := @le_asymmetry).
    assert (lemma4 := le_intro_S_n_le_S_m).
    enough (claim1 : forall N : tm, forall M : tm, isSubtermOf N M -> getRank N <= getRank M).
    enough (claim2 : forall N : tm, forall M : tm, isSubtermOf N M -> getRank N = getRank M -> N = M).
    - intros N M; split; [intros []; split; exists [] | intros [? ?]]...
    - intros N M [poss [X]]; induction X; simpl; intros H_EQ; [tauto | ..]; contradiction (not_n_lt_n (getRank N)).
      + enough (H_false : getRank N < S (max (getRank P1) (getRank P2))) by congruence; apply lemma4.
        transitivity (getRank P1); [apply claim1; exists poss | ..]...
      + enough (H_false : getRank N < S (max (getRank P1) (getRank P2))) by congruence; apply lemma4.
        transitivity (getRank P2); [apply claim1; exists poss | ..]...
      + enough (H_false : getRank N < S (getRank Q)) by congruence; apply lemma4.
        transitivity (getRank Q); [apply claim1; exists poss | ..]...
    - intros N M [poss [X]]; induction X; simpl.
      + reflexivity.
      + transitivity (getRank P1)...
      + transitivity (getRank P2)...
      + transitivity (getRank Q)...
  Qed.

  End SUBTERM.

  End UNTYPED_LAMBDA_CALCULUS_WITH_CONSTANT.

  Arguments Var {CON}.
  Arguments Con {CON}.
  Arguments App {CON}.
  Arguments Lam {CON}.

End UntypedLamdbdaCalculus.

Module SimplyTypedLambdaCalculus.

  Import ListNotations MyUtilities BasicSetoidTheory MyEnsemble BasicPosetTheory UntypedLamdbdaCalculus.

  Global Reserved Notation " Sigma ';' Gamma '⊢' M '\isof' tau " (at level 70, no associativity).

  Section STLC_WITH_CONSTANT.

  Variable BaseTy : Set.

  Inductive tyExpr : Set :=
  | TyB (base_ty : BaseTy) : tyExpr
  | ARR (arg_ty : tyExpr) (ret_ty : tyExpr) : tyExpr
  .

  Let tyCtx : Set :=
    list (ivar * tyExpr)
  .

  Variable CON : Set.

  Let tmExpr : Set :=
    tm CON
  .

  Inductive typeOf (lsig : CON -> tyExpr) : tyCtx -> tmExpr -> tyExpr -> Set :=
  | VarTypeOf (x : ivar) :
    forall good_ctx : {ctx : tyCtx | lookup x (ivar_eq_dec x) ctx <> None},
    lsig; proj1_sig good_ctx ⊢ Var x \isof fromJust (lookup x (ivar_eq_dec x) (proj1_sig good_ctx)) (proj2_sig good_ctx)
  | ConTypeOf (c : CON) :
    forall ctx : tyCtx,
    lsig; ctx ⊢ Con c \isof lsig c
  | AppTypeOf (P1 : tmExpr) (P2 : tmExpr) :
    forall ctx : tyCtx,
    forall arg_ty : tyExpr,
    forall ret_ty : tyExpr,
    lsig; ctx ⊢ P1 \isof ARR arg_ty ret_ty ->
    lsig; ctx ⊢ P2 \isof arg_ty ->
    lsig; ctx ⊢ App P1 P2 \isof ret_ty
  | LamTypeOf (y : ivar) (Q : tmExpr) :
    forall ctx : tyCtx,
    forall arg_ty : tyExpr,
    forall ret_ty : tyExpr,
    lsig; (y, arg_ty) :: ctx ⊢ Q \isof ret_ty ->
    lsig; ctx ⊢ Lam y Q \isof ARR arg_ty ret_ty
  where " Sigma ';' Gamma '⊢' M '\isof' tau " := (typeOf Sigma Gamma M tau) : type_scope.

  End STLC_WITH_CONSTANT.

  Arguments TyB {BaseTy}.
  Arguments ARR {BaseTy}.

  Arguments typeOf {BaseTy} {CON}.
  Arguments VarTypeOf {BaseTy} {CON} {lsig}.
  Arguments ConTypeOf {BaseTy} {CON} {lsig}.
  Arguments AppTypeOf {BaseTy} {CON} {lsig}.
  Arguments LamTypeOf {BaseTy} {CON} {lsig}.

  Global Notation " Sigma ';' Gamma '⊢' M '\isof' tau " := (typeOf Sigma Gamma M tau) : type_scope.

End SimplyTypedLambdaCalculus.
