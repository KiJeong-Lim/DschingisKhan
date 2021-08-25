Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Relations.Relation_Operators.
Require Import DschingisKhan.pure.DomainTheory.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module UntypedLamdbdaCalculus.

  Import ListNotations MyUtilities BasicSetoidTheory MyEnsemble BasicPosetTheory BasicTopology.

  Definition ivar : Set :=
    nat
  .

  Definition ivar_eq_dec :
    forall x : ivar,
    forall y : ivar,
    {x = y} + {x <> y}.
  Proof.
    exact Nat.eq_dec.
  Defined.

  Inductive tm : Set :=
  | tmVar : forall x : ivar, tm
  | tmApp : forall P1 : tm, forall P2 : tm, tm
  | tmLam : forall y : ivar, forall Q : tm, tm
  .

  Definition tm_eq_dec :
    forall M1 : tm,
    forall M2 : tm,
    {M1 = M2} + {M1 <> M2}.
  Proof with try ((left; congruence) || (right; congruence)).
    induction M1; destruct M2...
    - destruct (ivar_eq_dec x x0)...
    - destruct (IHM1_1 M2_1); destruct (IHM1_2 M2_2)...
    - destruct (ivar_eq_dec y y0); destruct (IHM1 M2)...
  Defined.

  Section SUBTERM.

  Fixpoint getRank (M : tm) {struct M} : nat :=
    match M with
    | tmVar x => 0
    | tmApp P1 P2 => S (max (getRank P1) (getRank P2))
    | tmLam y Q => S (getRank Q)
    end
  .

  Inductive subtm : tm -> tm -> Set :=
  | subtmRefl : forall M : tm, subtm M M
  | subtmAppL : forall M : tm, forall P1 : tm, forall P2 : tm, subtm M P1 -> subtm M (tmApp P1 P2)
  | subtmAppR : forall M : tm, forall P1 : tm, forall P2 : tm, subtm M P2 -> subtm M (tmApp P1 P2)
  | subtmLAbs : forall M : tm, forall y : ivar, forall Q : tm, subtm M Q -> subtm M (tmLam y Q)
  .

  Local Hint Constructors subtm : core.

  Lemma subtm_getRank :
    forall M : tm,
    forall N : tm,
    subtm M N ->
    getRank M <= getRank N.
  Proof with lia.
    intros M N X.
    induction X; simpl...
  Qed.

  Lemma subtm_and_same_rank_implies_same_term :
    forall M : tm,
    forall N : tm,
    subtm M N ->
    getRank M = getRank N ->
    M = N.
  Proof with lia.
    intros M N X.
    destruct X; simpl; intros H.
    - reflexivity.
    - assert (H0 := subtm_getRank M P1 X)...
    - assert (H0 := subtm_getRank M P2 X)...
    - assert (H0 := subtm_getRank M Q X)...
  Qed.

  Lemma subtm_refl :
    forall M1 : tm,
    subtm M1 M1.
  Proof.
    exact subtmRefl.
  Qed.

  Lemma subtm_asym :
    forall M1 : tm,
    forall M2 : tm,
    subtm M1 M2 ->
    subtm M2 M1 ->
    M1 = M2.
  Proof with eauto.
    intros M1 M2 H H0.
    apply subtm_and_same_rank_implies_same_term...
    enough (getRank M1 <= getRank M2 /\ getRank M2 <= getRank M1) by lia.
    split; apply subtm_getRank...
  Qed.

  Lemma subtm_trans :
    forall M1 : tm,
    forall M2 : tm,
    forall M3 : tm,
    subtm M1 M2 ->
    subtm M2 M3 ->
    subtm M1 M3.
  Proof with eauto.
    enough (claim1 : forall L : tm, forall N : tm, forall M : tm, subtm N L -> subtm M N -> subtm M L) by firstorder.
    induction L; intros N M H H0; inversion H; subst...
  Qed.

  Local Hint Resolve subtm_refl subtm_asym subtm_trans : core.

  Theorem strong_induction_on_tm (phi : tm -> Prop) :
    (forall M : tm, (forall N : tm, subtm N M -> N <> M -> phi N) -> phi M) ->
    forall M : tm,
    phi M.
  Proof with (congruence || eauto).
    intros XXX.
    enough (claim1 : forall M : tm, forall L : tm, subtm L M -> phi L)...
    induction M; intros L H; apply XXX; intros N H0 H1; inversion H0; subst...
    all: inversion H; subst...
  Qed.

  Definition induction_principle_of_subtm (L : tm) :
    forall XP : (forall M : tm, subtm L M -> Type),
    (XP L (subtmRefl L)) ->
    (forall P1 : tm, forall P2 : tm, forall X : subtm L P1, XP P1 X -> XP (tmApp P1 P2) (subtmAppL L P1 P2 X)) ->
    (forall P1 : tm, forall P2 : tm, forall X : subtm L P2, XP P2 X -> XP (tmApp P1 P2) (subtmAppR L P1 P2 X)) ->
    (forall y : ivar, forall Q : tm, forall X : subtm L Q, XP Q X -> XP (tmLam y Q) (subtmLAbs L y Q X)) ->
    (forall M : tm, forall X : subtm L M, XP M X).
  Proof.
    intros XP case_Refl case_AppL case_AppR case_LAbs.
    assert ( XXX :
      forall N : tm,
      forall M : tm,
      forall X : subtm N M,
      forall H : N = L,
      XP M (eq_rect N (fun N0 : tm => subtm N0 M) X L H)
    ).
    { assert (XP_Refl := fun M0 : tm => fun H : M0 = L => case_eqrefl M0 L H (fun M1 : tm => fun H0 : M1 = L => XP M1 (eq_rect M1 (fun N1 : tm => subtm N1 M1) (subtmRefl M1) L H0)) case_Refl).
      assert (XP_AppL := fun M0 : tm => fun P1 : tm => fun P2 : tm => fun H : M0 = L => case_eqrefl M0 L H (fun M1 : tm => fun H0 : M1 = L => forall X' : subtm M1 P1, (forall H' : M1 = L, XP P1 (eq_rect M1 (fun N1 : tm => subtm N1 P1) X' L H')) -> XP (tmApp P1 P2) (eq_rect M1 (fun N1 : tm => subtm N1 (tmApp P1 P2)) (subtmAppL M1 P1 P2 X') L H0)) (fun X' : subtm L P1 => fun IHX' : forall H' : L = L, XP P1 (eq_rect L (fun N1 : tm => subtm N1 P1) X' L H') => case_AppL P1 P2 X' (IHX' eq_refl))).
      assert (XP_AppR := fun M0 : tm => fun P1 : tm => fun P2 : tm => fun H : M0 = L => case_eqrefl M0 L H (fun M1 : tm => fun H0 : M1 = L => forall X' : subtm M1 P2, (forall H' : M1 = L, XP P2 (eq_rect M1 (fun N1 : tm => subtm N1 P2) X' L H')) -> XP (tmApp P1 P2) (eq_rect M1 (fun N1 : tm => subtm N1 (tmApp P1 P2)) (subtmAppR M1 P1 P2 X') L H0)) (fun X' : subtm L P2 => fun IHX' : forall H' : L = L, XP P2 (eq_rect L (fun N1 : tm => subtm N1 P2) X' L H') => case_AppR P1 P2 X' (IHX' eq_refl))).
      assert (XP_LAbs := fun M0 : tm => fun y : ivar => fun Q : tm => fun H : M0 = L => case_eqrefl M0 L H (fun M1 : tm => fun H0 : M1 = L => forall X' : subtm M1 Q, (forall H' : M1 = L, XP Q (eq_rect M1 (fun N1 : tm => subtm N1 Q) X' L H')) -> XP (tmLam y Q) (eq_rect M1 (fun N1 : tm => subtm N1 (tmLam y Q)) (subtmLAbs M1 y Q X') L H0)) (fun X' : subtm L Q => fun IHX' : forall H' : L = L, XP Q (eq_rect L (fun N1 : tm => subtm N1 Q) X' L H') => case_LAbs y Q X' (IHX' eq_refl))).
      exact (
        fix occurence_rect_fix (N : tm) (M : tm) (X : subtm N M) {struct X} : forall H : N = L, XP M (eq_rect N (fun N1 : tm => subtm N1 M) X L H) :=
        match X as X0 in subtm N0 M0 return forall H : N0 = L, XP M0 (eq_rect N0 (fun N1 : tm => subtm N1 M0) X0 L H) with
        | subtmRefl M0 => fun H : M0 = L => XP_Refl M0 H 
        | subtmAppL M0 P1 P2 X' => fun H : M0 = L => XP_AppL M0 P1 P2 H X' (occurence_rect_fix M0 P1 X')
        | subtmAppR M0 P1 P2 X' => fun H : M0 = L => XP_AppR M0 P1 P2 H X' (occurence_rect_fix M0 P2 X')
        | subtmLAbs M0 y Q X' => fun H : M0 = L => XP_LAbs M0 y Q H X' (occurence_rect_fix M0 Q X')
        end
      ).
    }
    exact (fun M : tm => fun X : subtm L M => XXX L M X eq_refl).
  Defined.

  End SUBTERM.

  Fixpoint getFVs (M : tm) : list ivar :=
    match M with
    | tmVar x => [x]
    | tmApp P1 P2 => getFVs P1 ++ getFVs P2
    | tmLam y Q => remove ivar_eq_dec y (getFVs Q)
    end
  .

  Fixpoint isFreeIn (z : ivar) (M : tm) {struct M} : bool :=
    match M with
    | tmVar x => Nat.eqb x z
    | tmApp P1 P2 => isFreeIn z P1 || isFreeIn z P2
    | tmLam y Q => isFreeIn z Q && negb (Nat.eqb z y)
    end
  .

  Lemma getFVs_isFreeIn (M : tm) :
    forall z : ivar,
    In z (getFVs M) <-> isFreeIn z M = true.
  Proof with auto_rewrite.
    induction M...
  Qed.

  Section SUBSTITUTION. (* Reference: "https://github.com/ernius/formalmetatheory-stoughton/tree/7eea5b526ec58a49838daa7b21b02fafcbf9065e" *)

  Definition substitution : Set :=
    ivar -> tm
  .

  Definition nil_subtitution : substitution :=
    tmVar
  .

  Definition cons_substitution : ivar -> tm -> substitution -> substitution :=
    fun x : ivar =>
    fun M : tm =>
    fun sigma : substitution =>
    fun y : ivar =>
    if ivar_eq_dec x y then M else sigma y
  .

  Fixpoint mk_substitution (sigma : list (ivar * tm)) {struct sigma} : substitution :=
    match sigma with
    | [] => nil_subtitution
    | (x, M) :: sigma' => cons_substitution x M (mk_substitution sigma')
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
    enough (get_max_ivar M < x -> ~ In x (getFVs M)) by now rewrite getFVs_isFreeIn, not_true_iff_false in H.
    assert (H1 : In x (getFVs M) -> fold_right_max_0 (getFVs M) >= x) by apply fold_right_max_0_in.
    enough (fold_right_max_0 (getFVs M) >= x -> fold_right_max_0 (getFVs M) < x -> False) by eauto...
  Qed.

  Definition isFreshIn_substitution : ivar -> substitution -> tm -> bool :=
    fun x : ivar =>
    fun sigma : substitution =>
    fun M : tm => forallb (fun z : ivar => negb (isFreeIn x (sigma z))) (getFVs M)
  .

  Definition chi : substitution -> tm -> ivar :=
    fun sigma : substitution => 
    fun M : tm =>
    S (fold_right_max_0 (map (fun x : ivar => get_max_ivar (sigma x)) (getFVs M)))
  .

  Theorem main_property_of_chi :
    forall M : tm,
    forall sigma : substitution,
    isFreshIn_substitution (chi sigma M) sigma M = true.
  Proof with auto_rewrite.
    assert ( claim1 :
      forall sigma : substitution,
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
    unfold isFreshIn_substitution...
    apply claim1, getFVs_isFreeIn...
  Qed.

  Lemma chi_nil : 
    forall M : tm,
    isFreeIn (chi nil_subtitution M) M = false.
  Proof with auto_rewrite.
    intros M.
    assert (H : isFreshIn_substitution (chi nil_subtitution M) nil_subtitution M = true) by apply main_property_of_chi.
    unfold isFreshIn_substitution in H.
    rewrite forallb_true_iff in H.
    simpl in H.
    apply not_true_iff_false.
    intros H0.
    assert (H1 : negb (chi nil_subtitution M =? chi nil_subtitution M) = true) by now apply H, getFVs_isFreeIn...
  Qed.

  Fixpoint run_substitution_on_tm (sigma : substitution) (M : tm) {struct M} : tm :=
    match M with
    | tmVar x => sigma x
    | tmApp P1 P2 => tmApp (run_substitution_on_tm sigma P1) (run_substitution_on_tm sigma P2)
    | tmLam y Q =>
      let z : ivar := chi sigma M in
      tmLam z (run_substitution_on_tm (cons_substitution y (tmVar z) sigma) Q)
    end
  .

  Theorem main_property_isFreshIn_substitution :
    forall M : tm,
    forall z : ivar,
    forall sigma : substitution,
    isFreshIn_substitution z sigma M = true <-> isFreeIn z (run_substitution_on_tm sigma M) = false.
  Proof with auto_rewrite.
    induction M; unfold isFreshIn_substitution; simpl...
    split; intros H.
    - destruct (ivar_eq_dec z (chi sigma (tmLam y M)))...
      left.
      apply IHM.
      unfold isFreshIn_substitution, cons_substitution.
      apply forallb_true_iff.
      intros x H0.
      destruct (ivar_eq_dec y x); [apply negb_true_iff, Nat.eqb_neq | apply H, in_in_remove]...
    - auto_rewrite.
      destruct H0 as [H0 H1].
      destruct H as [H | H].
      + assert (H2 : isFreshIn_substitution z (cons_substitution y (tmVar (chi sigma (tmLam y M))) sigma) M = true) by now apply IHM.
        unfold isFreshIn_substitution in H2.
        rewrite forallb_true_iff in H2.
        assert (H3 := H2 x H0).
        unfold cons_substitution in H3.
        destruct (ivar_eq_dec y x)...
      + assert (H2 : isFreshIn_substitution z sigma (tmLam y M) = true) by now rewrite H; apply main_property_of_chi.
        unfold isFreshIn_substitution in H2.
        rewrite forallb_true_iff in H2.
        apply negb_true_iff, H2.
        rewrite getFVs_isFreeIn.
        auto_rewrite.
        rewrite <- getFVs_isFreeIn...
  Qed.

  Definition equiv_substitution_wrt : substitution -> substitution -> tm -> Prop :=
    fun sigma1 : substitution =>
    fun sigma2 : substitution =>
    fun M : tm =>
    forall x : ivar,
    isFreeIn x M = true ->
    sigma1 x = sigma2 x
  .

  Lemma property1_of_equiv_substitution_wrt :
    forall sigma1 : substitution,
    forall sigma2 : substitution,
    (forall x : ivar, sigma1 x = sigma2 x) ->
    forall M : tm,
    equiv_substitution_wrt sigma1 sigma2 M.
  Proof with try now firstorder.
    unfold equiv_substitution_wrt...
  Qed.

  Lemma chi_equiv_substitution_wrt :
    forall sigma1 : substitution,
    forall sigma2 : substitution,
    forall M : tm,
    equiv_substitution_wrt sigma1 sigma2 M ->
    chi sigma1 M = chi sigma2 M.
  Proof with auto_rewrite.
    unfold chi.
    intros sigma1 sigma2 M H.
    enough (it_is_sufficient_to_show : (map (fun x : ivar => get_max_ivar (sigma1 x)) (getFVs M)) = (map (fun x : ivar => get_max_ivar (sigma2 x)) (getFVs M))) by congruence.
    apply map_ext_in.
    intros x H0.
    rewrite (H x (proj1 (getFVs_isFreeIn M x) H0))...
  Qed.

  Theorem main_property_of_equiv_substitution_wrt :
    forall M : tm,
    forall sigma1 : substitution,
    forall sigma2 : substitution,
    equiv_substitution_wrt sigma1 sigma2 M ->
    run_substitution_on_tm sigma1 M = run_substitution_on_tm sigma2 M.
  Proof with auto_rewrite.
    induction M; simpl.
    - intros sigma1 sigma2 H.
      apply H...
    - intros sigma1 sigma2 H.
      enough (claim1 : equiv_substitution_wrt sigma1 sigma2 M1).
      enough (claim2 : equiv_substitution_wrt sigma1 sigma2 M2).
      rewrite (IHM1 sigma1 sigma2 claim1), (IHM2 sigma1 sigma2 claim2)...
      all: intros x H0; apply H...
    - intros sigma1 sigma2 H.
      enough (claim3 : equiv_substitution_wrt (cons_substitution y (tmVar (chi sigma1 (tmLam y M))) sigma1) (cons_substitution y (tmVar (chi sigma2 (tmLam y M))) sigma2) M).
      assert (claim4 : chi sigma1 (tmLam y M) = chi sigma2 (tmLam y M)) by now apply chi_equiv_substitution_wrt.
      rewrite (IHM (cons_substitution y (tmVar (chi sigma1 (tmLam y M))) sigma1) (cons_substitution y (tmVar (chi sigma2 (tmLam y M))) sigma2) claim3), claim4...
      intros x H0.
      unfold cons_substitution.
      destruct (ivar_eq_dec y x).
      + rewrite (chi_equiv_substitution_wrt sigma1 sigma2 (tmLam y M) H)...
      + apply H...
  Qed.

  Lemma trivial_substitution :
    forall x : ivar,
    forall M : tm,
    run_substitution_on_tm (cons_substitution x (tmVar x) nil_subtitution) M = run_substitution_on_tm nil_subtitution M.
  Proof with try now firstorder.
    unfold cons_substitution.
    intros x M.
    apply main_property_of_equiv_substitution_wrt.
    intros y H.
    destruct (ivar_eq_dec x y)...
  Qed.

  Definition compose_substitution : substitution -> substitution -> substitution :=
    fun sigma2 : substitution =>
    fun sigma1 : substitution =>
    fun x : ivar =>
    run_substitution_on_tm sigma2 (sigma1 x)
  .

  Lemma distri_compose_cons :
    forall M : tm,
    forall N : tm,
    forall sigma1 : substitution,
    forall sigma2 : substitution,
    forall x : ivar,
    forall y : ivar,
    isFreshIn_substitution y sigma1 (tmLam x M) = true ->
    forall z : ivar,
    isFreeIn z M = true ->
    cons_substitution x N (compose_substitution sigma2 sigma1) z = compose_substitution (cons_substitution y N sigma2) (cons_substitution x (tmVar y) sigma1) z.
  Proof with try now firstorder.
    intros M N sigma1 sigma2 x y H z H0.
    unfold cons_substitution, compose_substitution.
    destruct (ivar_eq_dec x z).
    - simpl.
      destruct (ivar_eq_dec y y)...
    - unfold isFreshIn_substitution in H.
      rewrite forallb_true_iff in H.
      assert (claim1 : isFreeIn y (sigma1 z) = false) by now apply negb_true_iff, H, getFVs_isFreeIn; auto_rewrite.
      assert ( claim2 :
        forall u : ivar,
        isFreeIn u (sigma1 z) = true ->
        cons_substitution y N sigma2 u = sigma2 u
      ).
      { unfold cons_substitution.
        intros u H1.
        destruct (ivar_eq_dec y u); subst...
        rewrite claim1 in H1...
      }
      apply main_property_of_equiv_substitution_wrt...
  Qed.

  Corollary distri_compose_cons_for_chi :
    forall M : tm,
    forall N : tm,
    forall sigma1 : substitution,
    forall sigma2 : substitution,
    forall x : ivar,
    let y : ivar := chi sigma1 (tmLam x M) in
    forall z : ivar,
    isFreeIn z M = true ->
    cons_substitution x N (compose_substitution sigma2 sigma1) z = compose_substitution (cons_substitution y N sigma2) (cons_substitution x (tmVar y) sigma1) z.
  Proof with eauto using distri_compose_cons, main_property_of_chi.
    intros M N sigma1 sigma2 x y z H...
  Qed.

  Definition FreeIn_wrt : ivar -> substitution -> tm -> Prop :=
    fun x : ivar =>
    fun sigma : substitution =>
    fun M : tm =>
    exists y : ivar, isFreeIn y M = true /\ isFreeIn x (sigma y) = true
  .

  Theorem isFreeIn_wrt_true_iff (M : tm) :
    forall z : ivar,
    forall sigma : substitution,
    isFreeIn z (run_substitution_on_tm sigma M) = true <-> FreeIn_wrt z sigma M.
  Proof with auto_rewrite.
    unfold FreeIn_wrt.
    induction M; simpl.
    - intros z sigma.
      split; intros H.
      + exists x...
      + destruct H as [y [H H0]]...
    - intros z sigma...
      split.
      + intros [H | H]; [assert (it_is_sufficient_to_show : exists y : ivar, isFreeIn y M1 = true /\ isFreeIn z (sigma y) = true) | assert (it_is_sufficient_to_show : exists y : ivar, isFreeIn y M2 = true /\ isFreeIn z (sigma y) = true)]...
        all: destruct it_is_sufficient_to_show as [y [H0 H1]]; exists y...
      + intros [y [H H0]]...
    - intros x sigma...
      split; intros H.
      + destruct H as [H H0].
        assert (H1 := proj1 (IHM x (cons_substitution y (tmVar (chi sigma (tmLam y M))) sigma)) H).
        destruct H1 as [w [H1 H2]].
        set (z := chi sigma (tmLam y M)).
        fold z in H, H0, H2.
        destruct (ivar_eq_dec y w).
        * subst.
          unfold cons_substitution in H2.
          destruct (ivar_eq_dec w w)...
          unfold isFreeIn in H2.
          rewrite Nat.eqb_eq in H2...
        * exists w...
          unfold cons_substitution in H2.
          destruct (ivar_eq_dec y w)...
      + rename y into z.
        destruct H as [y [H H0]].
        set (w := chi sigma (tmLam z M))...
        destruct (ivar_eq_dec w x).
        * subst.
          assert (isFreshIn_substitution w sigma (tmLam z M) = true) by now apply main_property_of_chi.
          unfold isFreshIn_substitution in H1.
          rewrite forallb_true_iff in H1.
          enough (H2 : isFreeIn w (sigma y) = false) by now rewrite H0 in H2.
          apply negb_true_iff, H1, getFVs_isFreeIn...
        * split...
          apply IHM.
          exists y.
          split...
          unfold cons_substitution.
          destruct (ivar_eq_dec z y)...
  Qed.

  Lemma chi_ext :
    forall sigma : substitution,
    forall sigma' : substitution,
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

  Theorem main_property_of_compose_substitution :
    forall M : tm,
    forall sigma1 : substitution,
    forall sigma2 : substitution,
    run_substitution_on_tm sigma2 (run_substitution_on_tm sigma1 M) = run_substitution_on_tm (compose_substitution sigma2 sigma1) M.
  Proof with auto_rewrite.
    induction M; simpl...
    - rewrite IHM1, IHM2...
    - enough (it_is_sufficient_to_show : chi sigma2 (run_substitution_on_tm sigma1 (tmLam y M)) = chi (compose_substitution sigma2 sigma1) (tmLam y M)).
      { set (x := chi sigma1 (tmLam y M)).
        set (x' := chi sigma2 (tmLam x (run_substitution_on_tm (cons_substitution y (tmVar x) sigma1) M))).
        set (z := chi (compose_substitution sigma2 sigma1) (tmLam y M)).
        assert (H := IHM (cons_substitution y (tmVar x) sigma1) (cons_substitution x (tmVar x') sigma2)).
        rewrite H.
        assert (H0 := distri_compose_cons_for_chi M (tmVar x') sigma1 sigma2 y).
        assert (H1 : run_substitution_on_tm (compose_substitution (cons_substitution x (tmVar x') sigma2) (cons_substitution y (tmVar x) sigma1)) M = run_substitution_on_tm (cons_substitution y (tmVar x') (compose_substitution sigma2 sigma1)) M) by now apply main_property_of_equiv_substitution_wrt; firstorder.
        rewrite H1.
        replace x' with z...
      }
      rename y into x.
      set (y := chi sigma1 (tmLam x M)).
      assert ( claim1 :
        forall y' : ivar,
        (exists x' : ivar, isFreeIn x' (tmLam y (run_substitution_on_tm (cons_substitution x (tmVar y) sigma1) M)) = true /\ isFreeIn y' (sigma2 x') = true) ->
        (exists u : ivar, isFreeIn u (tmLam x M) = true /\ isFreeIn y' (compose_substitution sigma2 sigma1 u) = true)
      ).
      { intros y' [x' [H H0]]...
        destruct H as [H H1].
        destruct (proj1 (isFreeIn_wrt_true_iff M x' (cons_substitution x (tmVar y) sigma1)) H) as [u [H2 H3]].
        unfold cons_substitution in H3.
        destruct (ivar_eq_dec x u).
        - unfold isFreeIn in H3.
          rewrite Nat.eqb_eq in H3...
        - exists u.
          split...
          apply (proj2 (isFreeIn_wrt_true_iff (sigma1 u) y' sigma2))...
      }
      assert ( claim2 :
        forall y' : ivar,
        (exists x' : ivar, isFreeIn x' (tmLam x M) = true /\ isFreeIn y' (compose_substitution sigma2 sigma1 x') = true) ->
        (exists u : ivar, isFreeIn u (tmLam y (run_substitution_on_tm (cons_substitution x (tmVar y) sigma1) M)) = true /\ isFreeIn y' (sigma2 u) = true)
      ).
      { intros y' [x' [H H0]].
        simpl in H.
        rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq in H.
        destruct H as [H H1].
        destruct (proj1 (isFreeIn_wrt_true_iff (sigma1 x') y' sigma2) H0) as [u [H2 H3]].
        assert (claim2_aux1 : isFreeIn u (run_substitution_on_tm (cons_substitution x (tmVar y) sigma1) M) = true).
        { apply isFreeIn_wrt_true_iff.
          exists x'.
          split...
          unfold cons_substitution.
          destruct (ivar_eq_dec x x')...
        }
        exists u.
        split...
        split...
        subst.
        enough (claim2_aux2 : isFreeIn y (sigma1 x') = false) by now rewrite H2 in claim2_aux2.
        assert (H4 := main_property_of_chi (tmLam x M) sigma1).
        unfold isFreshIn_substitution in H4.
        rewrite forallb_true_iff in H4.
        apply negb_true_iff, H4.
        rewrite getFVs_isFreeIn...
      }
      apply chi_ext...
  Qed.

  Corollary compose_one :
    forall M : tm,
    forall N : tm,
    forall sigma : substitution,
    forall x : ivar,
    run_substitution_on_tm (cons_substitution x (run_substitution_on_tm sigma N) sigma) M = run_substitution_on_tm sigma (run_substitution_on_tm (cons_substitution x N nil_subtitution) M).
  Proof with try now firstorder.
    intros M N sigma x.
    replace (run_substitution_on_tm (cons_substitution x (run_substitution_on_tm sigma N) sigma) M) with (run_substitution_on_tm (cons_substitution x (run_substitution_on_tm sigma N) (compose_substitution sigma nil_subtitution)) M).
    replace (run_substitution_on_tm (cons_substitution x (run_substitution_on_tm sigma N) (compose_substitution sigma nil_subtitution)) M) with (run_substitution_on_tm (compose_substitution sigma (cons_substitution x N nil_subtitution)) M).
    rewrite main_property_of_compose_substitution...
    all: apply main_property_of_equiv_substitution_wrt, property1_of_equiv_substitution_wrt; unfold compose_substitution, cons_substitution, nil_subtitution; intros z; destruct (ivar_eq_dec x z)...
  Qed.

  Theorem main_property_of_cons_substitution :
    forall x : ivar,
    forall z : ivar,
    forall M : tm,
    forall N : tm,
    forall sigma : substitution,
    isFreeIn z (tmLam x M) = false ->
    run_substitution_on_tm (cons_substitution x N sigma) M = run_substitution_on_tm (cons_substitution z N sigma) (run_substitution_on_tm (cons_substitution x (tmVar z) nil_subtitution) M).
  Proof with auto_rewrite.
    intros x z M N sigma H.
    rewrite (main_property_of_compose_substitution M (cons_substitution x (tmVar z) nil_subtitution) (cons_substitution z N sigma)).
    apply main_property_of_equiv_substitution_wrt.
    intros w H0.
    unfold cons_substitution, nil_subtitution, compose_substitution.
    destruct (ivar_eq_dec x w); simpl.
    - destruct (ivar_eq_dec z z)...
    - destruct (ivar_eq_dec z w)...
      subst.
      destruct H as [H | H]; [rewrite H0 in H | contradiction n]...
  Qed.

  End SUBSTITUTION.

  Local Notation " M '{' x '+->' N '}' " := (run_substitution_on_tm (cons_substitution x N nil_subtitution) M) (at level 10, no associativity).

  Example run_substitution_on_tm_example1 :
    (tmLam 3 (tmLam 5 (tmApp (tmVar 3) (tmVar 1)))) { 1 +-> tmApp (tmVar 4) (tmVar 3) } = tmLam 5 (tmLam 6 (tmApp (tmVar 5) (tmApp (tmVar 4) (tmVar 3)))).
  Proof.
    reflexivity.
  Qed.

  Class isPreLambdaStructure (Dom : Type) `{Dom_isSetoid : isSetoid Dom} : Type :=
    { runApp : Dom -> (Dom -> Dom)
    ; runLam : (Dom -> Dom) -> Dom
    ; runApp_ext :
      forall v1 : Dom,
      forall v1' : Dom,
      forall v2 : Dom,
      forall v2' : Dom,
      v1 == v1' ->
      v2 == v2' ->
      runApp v1 v2 == runApp v1' v2'
    ; runLam_ext :
      forall vv : Dom -> Dom,
      forall vv' : Dom -> Dom,
      (forall v : Dom, vv v == vv' v) ->
      runLam vv == runLam vv'
    }
  .

  Section PreliminariesOfSemantics.

  Context {D : Type} `{D_isSetoid : isSetoid D} `{D_isPreLambdaStructure : @isPreLambdaStructure D D_isSetoid}.

  Let env : Type :=
    ivar -> D
  .

  Fixpoint eval_tm (E : env) (M : tm) {struct M} : D :=
    match M with
    | tmVar x => E x
    | tmApp P1 P2 => runApp (eval_tm E P1) (eval_tm E P2)
    | tmLam y Q => runLam (fun v : D => eval_tm (fun z : ivar => if ivar_eq_dec y z then v else E z) Q)
    end
  .

  Lemma eval_tm_ext :
    forall M : tm,
    forall E1 : env,
    forall E2 : env,
    (forall z : ivar, isFreeIn z M = true -> E1 z == E2 z) ->
    eval_tm E1 M == eval_tm E2 M.
  Proof with auto_rewrite.
    induction M; simpl.
    - intros E1 E2 H.
      apply H...
    - intros E1 E2 H.
      apply runApp_ext; [apply IHM1 | apply IHM2]; intros z H0; apply H...
    - intros E1 E2 H.
      apply runLam_ext.
      intros v.
      apply (IHM (fun z : ivar => if ivar_eq_dec y z then v else E1 z) (fun z : ivar => if ivar_eq_dec y z then v else E2 z))...
      destruct (ivar_eq_dec y z); [subst | apply H]...
  Qed.

  Local Hint Resolve eval_tm_ext : core.

  Theorem run_substitution_on_tm_preserves_eval_tm :
    forall M : tm,
    forall sigma : substitution,
    forall E : env,
    eval_tm (fun z : ivar => eval_tm E (sigma z)) M == eval_tm E (run_substitution_on_tm sigma M).
  Proof with eauto with *.
    induction M.
    - intros sigma E...
    - intros sigma E.
      apply runApp_ext...
    - intros sigma E.
      enough (it_is_sufficient_to_show : forall v : D, eval_tm (fun z : ivar => if ivar_eq_dec y z then v else eval_tm E (sigma z)) M == eval_tm (fun z : ivar => if ivar_eq_dec (chi sigma (tmLam y M)) z then v else E z) (run_substitution_on_tm (cons_substitution y (tmVar (chi sigma (tmLam y M))) sigma) M)) by now apply runLam_ext.
      intros v.
      assert (H := IHM (cons_substitution y (tmVar (chi sigma (tmLam y M))) sigma) (fun z : ivar => if ivar_eq_dec (chi sigma (tmLam y M)) z then v else E z)).
      assert ( claim1 :
        forall z : ivar,
        isFreeIn z M = true ->
        eval_tm (fun x : ivar => if ivar_eq_dec (chi sigma (tmLam y M)) x then v else E x) (cons_substitution y (tmVar (chi sigma (tmLam y M))) sigma z) == (if ivar_eq_dec y z then v else eval_tm E (sigma z))
      ).
      { intros z H0.
        unfold cons_substitution.
        destruct (ivar_eq_dec y z).
        - unfold eval_tm.
          destruct (ivar_eq_dec (chi sigma (tmLam y M)) (chi sigma (tmLam y M)))...
          contradiction.
        - apply eval_tm_ext.
          intros z' H1.
          destruct (ivar_eq_dec (chi sigma (tmLam y M)) z')...
          subst.
          assert (H2 : isFreshIn_substitution (chi sigma (tmLam y M)) sigma (tmLam y M) = true) by now apply main_property_of_chi.
          unfold isFreshIn_substitution in H2.
          rewrite forallb_true_iff in H2.
          enough (H3 : isFreeIn (chi sigma (tmLam y M)) (sigma z) = false) by now rewrite H3 in H1.
          apply negb_true_iff, H2, getFVs_isFreeIn.
          auto_rewrite.
      }
      transitivity (eval_tm (fun z : ivar => eval_tm (fun z0 : ivar => if ivar_eq_dec (chi sigma (tmLam y M)) z0 then v else E z0) (cons_substitution y (tmVar (chi sigma (tmLam y M))) sigma z)) M)...
  Qed.

  End PreliminariesOfSemantics.

  Section ASSIGN_TYPE.

  Variable tvar : Set.

  Inductive ty : Set :=
  | tyVar : forall a : tvar, ty
  | tyArr : forall tau : ty, forall sigma : ty, ty
  .

  Local Coercion tyVar : tvar >-> ty.

  Local Notation " tau '→' sigma " := (tyArr tau sigma) (at level 60, right associativity).

  Let tyctx : Set :=
    list (ivar * ty)
  .

  Fixpoint lookup_tyctx (x : ivar) (Gamma : tyctx) {struct Gamma} : option ty :=
    match Gamma with
    | [] => None
    | (z, tau) :: Gamma' =>
      if ivar_eq_dec x z
      then Some tau
      else lookup_tyctx x Gamma'
    end
  .

  Inductive typing : tyctx -> tm -> ty -> Prop :=
  | typingVar :
    forall Gamma : tyctx,
    forall x : ivar,
    forall tau : ty,
    Some tau = lookup_tyctx x Gamma ->
    typing Gamma (tmVar x) tau
  | typingApp :
    forall Gamma : tyctx,
    forall P1 : tm,
    forall P2 : tm,
    forall tau : ty,
    forall sigma : ty,
    typing Gamma P1 (tau → sigma) ->
    typing Gamma P2 tau ->
    typing Gamma (tmApp P1 P2) sigma
  | typingLam :
    forall Gamma : tyctx,
    forall y : ivar,
    forall Q : tm,
    forall tau : ty,
    forall sigma : ty,
    typing ((y, tau) :: Gamma) Q sigma ->
    typing Gamma (tmLam y Q) (tau → sigma)
  .

  Local Notation " Gamma '⊢' M  ';;' tau " := (typing Gamma M tau) (at level 70, no associativity) : type_scope.

(* [PROVE ME] 2021-08-25

  Theorem SubstitutionLemma :
    forall M : tm,
    forall sigma : ty,
    forall Gamma : tyctx,
    forall z : ivar,
    forall N : tm,
    forall tau : ty,
    Gamma ⊢ N ;; tau ->
    (z, tau) :: Gamma ⊢ M ;; sigma ->
    Gamma ⊢ M { z +-> N } ;; sigma.
  Proof.
  Admitted.

*)

  End ASSIGN_TYPE.

  Section DE_BRUIJN.

  Inductive DB (vr : Type) : Type :=
  | VarDB : vr -> DB vr
  | AppDB : DB vr -> DB vr -> DB vr
  | LamDB : DB vr -> DB vr
  .

  Definition mkVarDB {vr : Type} : vr -> DB vr :=
    VarDB vr
  .

  Definition mkAppDB {vr : Type} : DB vr -> DB vr -> DB vr :=
    AppDB vr
  .

  Definition mkLamDB {vr : Type} : DB vr -> DB vr :=
    LamDB vr
  .

  Definition fmapDB {A : Type} {B : Type} : (A -> B) -> DB A -> DB B :=
    fun f : A -> B =>
    fix fmapDB_fix (M : DB A) {struct M} : DB B :=
    match M with
    | VarDB _ vr => mkVarDB (f vr)
    | AppDB _ P1 P2 => mkAppDB (fmapDB_fix P1) (fmapDB_fix P2)
    | LamDB _ Q => mkLamDB (fmapDB_fix Q)
    end
  .

  End DE_BRUIJN.

End UntypedLamdbdaCalculus.
