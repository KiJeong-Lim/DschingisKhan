Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
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
  Proof with lia.
    intros x.
    enough (it_is_sufficient_to_show : get_max_ivar M < x -> ~ In x (getFVs M)) by now rewrite getFVs_isFreeIn, not_true_iff_false in it_is_sufficient_to_show.
    assert (In x (getFVs M) -> fold_right_max_0 (getFVs M) >= x) by now apply fold_right_max_0_in.
    enough (fold_right_max_0 (getFVs M) >= x -> fold_right_max_0 (getFVs M) < x -> False) by eauto...
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
      enough (get_max_ivar (sigma x) < chi sigma M) by now apply get_max_ivar_lt.
      unfold chi, fold_right_max_0.
      enough (fold_right max 0 (map (fun z : ivar => get_max_ivar (sigma z)) (getFVs M)) >= get_max_ivar (sigma x)) by lia.
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
    assert (H : isFreshIn_tmSubst (chi tmSubst_nil M) tmSubst_nil M = true) by apply main_property_of_chi.
    unfold isFreshIn_tmSubst in H.
    rewrite forallb_true_iff in H.
    simpl in H.
    apply not_true_iff_false.
    intros H0.
    assert (H1 : negb (chi tmSubst_nil M =? chi tmSubst_nil M) = true) by now apply H, getFVs_isFreeIn...
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
      + assert (H2 : isFreshIn_tmSubst z (tmSubst_cons y (Var (chi sigma (Lam y M))) sigma) M = true) by now apply IHM.
        unfold isFreshIn_tmSubst in H2.
        rewrite forallb_true_iff in H2.
        assert (H3 := H2 x H0).
        unfold tmSubst_cons in H3.
        destruct (ivar_eq_dec y x)...
      + assert (H2 : isFreshIn_tmSubst z sigma (Lam y M) = true) by now rewrite H; apply main_property_of_chi.
        unfold isFreshIn_tmSubst in H2.
        rewrite forallb_true_iff in H2.
        apply negb_true_iff, H2.
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
      split; intros H.
      + destruct H as [H H0].
        assert (H1 := proj1 (IHM x (tmSubst_cons y (Var (chi sigma (Lam y M))) sigma)) H).
        destruct H1 as [w [H1 H2]].
        set (z := chi sigma (Lam y M)).
        fold z in H, H0, H2.
        destruct (ivar_eq_dec y w).
        * subst.
          unfold tmSubst_cons in H2.
          destruct (ivar_eq_dec w w)...
          unfold isFreeIn in H2.
          rewrite Nat.eqb_eq in H2...
        * exists w...
          unfold tmSubst_cons in H2.
          destruct (ivar_eq_dec y w)...
      + rename y into z.
        destruct H as [y [H H0]].
        set (w := chi sigma (Lam z M))...
        destruct (ivar_eq_dec w x).
        * subst.
          assert (isFreshIn_tmSubst w sigma (Lam z M) = true) by now apply main_property_of_chi.
          unfold isFreshIn_tmSubst in H1.
          rewrite forallb_true_iff in H1.
          enough (H2 : isFreeIn w (sigma y) = false) by now rewrite H0 in H2.
          apply negb_true_iff, H1, getFVs_isFreeIn...
        * split...
          apply IHM.
          exists y.
          split...
          unfold tmSubst_cons.
          destruct (ivar_eq_dec z y)...
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
    enough (fold_right_max_0 (map (fun x : ivar => get_max_ivar (sigma x)) (getFVs M)) = fold_right_max_0 (map (fun x : ivar => get_max_ivar (sigma' x)) (getFVs M'))) by lia.
    assert ( claim1 :
      forall z : ivar,
      In z (flat_map (fun y : ivar => getFVs (sigma y)) (getFVs M)) <-> In z (flat_map (fun y : ivar => getFVs (sigma' y)) (getFVs M'))
    ).
    { intros z.
      repeat (rewrite in_flat_map).
      split; intros [x H0]; rewrite getFVs_isFreeIn in H0.
      1: assert (H1 : exists y : ivar, isFreeIn y M' = true /\ isFreeIn z (sigma' y) = true) by now apply H; exists x; rewrite getFVs_isFreeIn in H0; firstorder.
      2: assert (H1 : exists y : ivar, isFreeIn y M = true /\ isFreeIn z (sigma y) = true) by now apply H; exists x; rewrite getFVs_isFreeIn in H0; firstorder.
      all: destruct H1 as [y [H1 H2]]; exists y; repeat (rewrite getFVs_isFreeIn)...
    }
    assert (H0 : fold_right_max_0 (flat_map (fun y : ivar => getFVs (sigma y)) (getFVs M)) = fold_right_max_0 (flat_map (fun y : ivar => getFVs (sigma' y)) (getFVs M'))) by now apply fold_right_max_0_ext.
    unfold get_max_ivar.
    enough (H1 : forall xs : list ivar, forall f : ivar -> list ivar, fold_right_max_0 (map (fun x : ivar => fold_right_max_0 (f x)) xs) = fold_right_max_0 (flat_map f xs)) by now repeat (rewrite H1).
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
        assert (H := IHM (tmSubst_cons y (Var x) sigma1) (tmSubst_cons x (Var x') sigma2)).
        rewrite H.
        assert (H0 := distri_compose_cons_for_chi M (Var x') sigma1 sigma2 y).
        assert (H1 : run_tmSubst_on_tm (compose_tmSubst (tmSubst_cons x (Var x') sigma2) (tmSubst_cons y (Var x) sigma1)) M = run_tmSubst_on_tm (tmSubst_cons y (Var x') (compose_tmSubst sigma2 sigma1)) M) by now apply main_property_of_equiv_tmSubst_wrt; firstorder.
        rewrite H1.
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
        assert (claim2_aux1 : isFreeIn u (run_tmSubst_on_tm (tmSubst_cons x (Var y) sigma1) M) = true).
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
        enough (claim2_aux2 : isFreeIn y (sigma1 x') = false) by now rewrite H2 in claim2_aux2.
        assert (H4 := main_property_of_chi (Lam x M) sigma1).
        unfold isFreshIn_tmSubst in H4.
        rewrite forallb_true_iff in H4.
        apply negb_true_iff, H4.
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

  Context {D : Type} `{D_isSetoid : isSetoid D} `{D_isPreLambdaStructure : @isPreLambdaStructure D D_isSetoid}.

  Let evalEnv : Type :=
    ivar -> D
  .

  Variable runCon : CON -> D.

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
      assert (H := IHM (tmSubst_cons y (Var (chi sigma (Lam y M))) sigma) (fun z : ivar => if ivar_eq_dec (chi sigma (Lam y M)) z then v else E z)).
      assert ( claim1 :
        forall z : ivar,
        isFreeIn z M = true ->
        eval_tm (fun x : ivar => if ivar_eq_dec (chi sigma (Lam y M)) x then v else E x) (tmSubst_cons y (Var (chi sigma (Lam y M))) sigma z) == (if ivar_eq_dec y z then v else eval_tm E (sigma z))
      ).
      { intros z H0.
        unfold tmSubst_cons.
        destruct (ivar_eq_dec y z).
        - unfold eval_tm.
          destruct (ivar_eq_dec (chi sigma (Lam y M)) (chi sigma (Lam y M)))...
          contradiction.
        - apply eval_tm_ext.
          intros z' H1.
          destruct (ivar_eq_dec (chi sigma (Lam y M)) z')...
          subst.
          assert (H2 : isFreshIn_tmSubst (chi sigma (Lam y M)) sigma (Lam y M) = true) by now apply main_property_of_chi.
          unfold isFreshIn_tmSubst in H2.
          rewrite forallb_true_iff in H2.
          enough (H3 : isFreeIn (chi sigma (Lam y M)) (sigma z) = false) by now rewrite H3 in H1.
          apply negb_true_iff, H2, getFVs_isFreeIn.
          auto_rewrite.
      }
      transitivity (eval_tm (fun z : ivar => eval_tm (fun z0 : ivar => if ivar_eq_dec (chi sigma (Lam y M)) z0 then v else E z0) (tmSubst_cons y (Var (chi sigma (Lam y M))) sigma z)) M)...
  Qed.

  End PreliminariesOfSemantics.

  End UNTYPED_LAMBDA_CALCULUS_WITH_CONSTANT.

  Arguments Var {CON}.
  Arguments Con {CON}.
  Arguments App {CON}.
  Arguments Lam {CON}.

End UntypedLamdbdaCalculus.

Module SimplyTypedLambdaCalculus.

  Import ListNotations MyUtilities BasicSetoidTheory MyEnsemble BasicPosetTheory UntypedLamdbdaCalculus.

  Global Reserved Notation " lsig ';' ctx '⊢' M '\isof' ty " (at level 70, no associativity).

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
  where " lsig ';' ctx '⊢' M '\isof' ty " := (typeOf lsig ctx M ty) : type_scope.

  End STLC_WITH_CONSTANT.

  Arguments TyB {BaseTy}.
  Arguments ARR {BaseTy}.

  Arguments typeOf {BaseTy} {CON}.
  Arguments VarTypeOf {BaseTy} {CON} {lsig}.
  Arguments ConTypeOf {BaseTy} {CON} {lsig}.
  Arguments AppTypeOf {BaseTy} {CON} {lsig}.
  Arguments LamTypeOf {BaseTy} {CON} {lsig}.

  Global Notation " lsig ';' ctx '⊢' M '\isof' ty " := (typeOf lsig ctx M ty) : type_scope.

End SimplyTypedLambdaCalculus.
