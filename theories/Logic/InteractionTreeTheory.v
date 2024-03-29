Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeUtil.
Require Import DschingisKhan.Prelude.PreludeClassic.
Require Import DschingisKhan.Data.InteractionTree.
Require Import DschingisKhan.Math.BasicPosetTheory.
Require Import DschingisKhan.Logic.ConstructiveDomainTheory.

(**

Module InteractionTreeTheory.

  Import InteractionTrees BasicPosetTheory BasicCoLaTheory ParameterizedCoinduction.

  Section ITREE_BISIMULATION.

  Context {E : Type -> Type} {R : Type} {requiresSetoid : isSetoid R}.

  Variant itreeBisimF {bisim : itree E R -> itree E R -> Prop} : forall lhs : itreeF E R, forall rhs : itreeF E R, Prop :=
  | EqRetF (r1 : R) (r2 : R)
    (REL : r1 == r2)
    : itreeBisimF (RetF r1) (RetF r2)
  | EqTauF (t1 : itree E R) (t2 : itree E R)
    (REL : bisim t1 t2)
    : itreeBisimF (TauF t1) (TauF t2)
  | EqVisF (X : Type) (e : E X) (k1 : X -> itree E R) (k2 : X -> itree E R)
    (REL : forall x : X, bisim (k1 x) (k2 x))
    : itreeBisimF (VisF X e k1) (VisF X e k2)
  .

  Definition eqITreeF (BISIM : ensemble (itree E R * itree E R)) : ensemble (itree E R * itree E R) :=
    uncurry (fun lhs : itree E R => fun rhs : itree E R => itreeBisimF (bisim := curry BISIM) (observe lhs) (observe rhs))
  .

  Definition eqITreeF_monotonic (BISIM : ensemble (itree E R * itree E R)) (BISIM' : ensemble (itree E R * itree E R)) (INCL : isSubsetOf BISIM BISIM') : isSubsetOf (eqITreeF BISIM) (eqITreeF BISIM') :=
    fun '(lhs, rhs) =>
    fun lhs_REL_rhs : itreeBisimF (observe lhs) (observe rhs) =>
    match lhs_REL_rhs in itreeBisimF lhs' rhs' return itreeBisimF lhs' rhs' with
    | EqRetF r1 r2 REL => EqRetF r1 r2 REL
    | EqTauF t1 t2 REL => EqTauF t1 t2 (INCL (t1, t2) REL)
    | EqVisF X e k1 k2 REL => EqVisF X e k1 k2 (fun x : X => INCL (k1 x, k2 x) (REL x))
    end
  .

  Definition eqITreeF_isMonotonicMap : isMonotonicMap eqITreeF := eqITreeF_monotonic.

  Definition eqITreeF' : ensemble (itree E R * itree E R) -> ensemble (itree E R * itree E R) := paco eqITreeF.

  Definition eqITree (lhs : itree E R) (rhs : itree E R) : Prop := member (lhs, rhs) (eqITreeF' cola_empty).

  Local Hint Resolve eqITreeF_isMonotonicMap : core.

  Set Primitive Projections.

  CoInductive itreeBisim (lhs : itree E R) (rhs : itree E R) : Prop :=
    Fold_itreeBisim { unfold_itreeBisim : itreeBisimF (bisim := itreeBisim) (observe lhs) (observe rhs) }
  .

  Unset Primitive Projections.

  Theorem eqITree_iff_itreeBisim (lhs : itree E R) (rhs : itree E R)
    : eqITree lhs rhs <-> itreeBisim lhs rhs.
  Proof.
    revert lhs rhs. keep (uncurry itreeBisim) as itreeBisim' into (ensemble (itree E R * itree E R)).
    set (f := @exist (ensemble (itree E R * itree E R) -> ensemble (itree E R * itree E R)) isMonotonicMap eqITreeF eqITreeF_isMonotonicMap).
    enough (claim1 : isSubsetOf itreeBisim' (proj1_sig f itreeBisim')).
    enough (claim2 : isSupremumOf itreeBisim' (PostfixedPoints (proj1_sig f))).
    enough (claim3 : eqITreeF' cola_empty == itreeBisim').
    - ii. exact (claim3 (lhs, rhs)).
    - eapply @Supremum_unique with (requiresPoset := ensemble_isPoset (itree E R * itree E R)) (X1 := PostfixedPoints (proj1_sig f)) (X2 := PostfixedPoints (proj1_sig f)).
      + rewrite paco_init with (F_monotonic := eqITreeF_isMonotonicMap). eapply nu_isSupremumOf_PostfixedPoints.
      + exact (claim2).
      + reflexivity.
    - intros Y. split.
      + intros le_Y X X_in. unnw. do 2 red in X_in. rewrite <- le_Y. intros [lhs rhs] H_in. revert lhs rhs H_in.
        exact (
          cofix CIH (lhs : itree E R) (rhs : itree E R) (H_in : member (lhs, rhs) X) : itreeBisim lhs rhs :=
          Fold_itreeBisim lhs rhs (eqITreeF_isMonotonicMap X (uncurry itreeBisim) (fun '(LHS, RHS) => CIH LHS RHS) (lhs, rhs) (X_in (lhs, rhs) H_in))
        ).
      + intros ?; desnw. eapply UPPER_BOUND. exact (claim1).
    - intros [lhs rhs] H_in. eapply unfold_itreeBisim. exact (H_in). 
  Qed.

  Lemma eqITree_reflexivity
    : isSubsetOf Rel_id (eqITreeF' cola_empty).
  Proof with eauto with *.
    eapply paco_accum... set (Rel_focus := cola_union cola_empty Rel_id).
    rewrite <- paco_fold. intros [lhs rhs] lhs_eq_rhs. do 3 red. do 2 red in lhs_eq_rhs.
    destruct (observe lhs) as [r1 | t1 | X1 e1 k1] eqn: H_lhs_obs; destruct (observe rhs) as [r2 | t2 | X2 e2 k2] eqn: H_rhs_obs; try congruence.
    - econstructor 1. replace (r2) with (r1) by congruence. reflexivity.
    - econstructor 2. left. right. do 2 red. congruence.
    - assert (obs_eq : @eq (itreeF E R) (VisF X1 e1 k1) (VisF X2 e2 k2)) by congruence.
      rewrite obs_eq. econstructor 3. ii. left. right. reflexivity.
  Qed.

  Lemma eqITree_symmetry
    : isSubsetOf (Rel_flip (eqITreeF' cola_empty)) (eqITreeF' cola_empty).
  Proof with eauto with *.
    eapply paco_accum... set (Rel_focus := cola_union cola_empty (Rel_flip (eqITreeF' cola_empty))).
    rewrite <- paco_fold. intros [lhs rhs] lhs_eq_rhs. apply paco_unfold in lhs_eq_rhs... do 3 red in lhs_eq_rhs. do 3 red.
    destruct lhs_eq_rhs as [r1 r2 REL | t1 t2 REL | X e k1 k2 REL].
    - econstructor 1. symmetry...
    - econstructor 2. apply in_union_iff in REL. destruct REL as [REL | REL]; [inversion REL | left; right]...
    - econstructor 3. intros x. specialize REL with (x := x).
      apply in_union_iff in REL. destruct REL as [REL | REL]; [inversion REL | left; right]...
  Qed.

  Lemma eqITree_transitivity
    : isSubsetOf (Rel_compose (eqITreeF' cola_empty) (eqITreeF' cola_empty)) (eqITreeF' cola_empty).
  Proof with eauto with *.
    eapply paco_accum... set (Rel_focus := cola_union cola_empty (Rel_compose (eqITreeF' cola_empty) (eqITreeF' cola_empty))).
    assert (INIT : eqITreeF (cola_union cola_empty (eqITreeF' cola_empty)) =< eqITreeF (cola_union Rel_focus (eqITreeF' Rel_focus))).
    { eapply eqITreeF_isMonotonicMap. intros [lhs rhs] [lhs_eq_rhs | lhs_eq_rhs]; [inversion lhs_eq_rhs | right]. eapply paco_preserves_monotonicity with (x := cola_empty)... }
    rewrite <- paco_fold. intros [lhs rhs] [t [lhs_eq_t t_eq_rhs]]. apply paco_unfold in lhs_eq_t... apply paco_unfold in t_eq_rhs... do 3 red in lhs_eq_t, t_eq_rhs. do 3 red.
    destruct (observe t) as [r3 | t3 | X3 e3 k3] eqn: H_t_obs.
    - inversion lhs_eq_t; subst. rename REL into REL1, H0 into H_lhs_obs. 
      inversion t_eq_rhs; subst. rename REL into REL2, H into H_rhs_obs.
      econstructor 1. transitivity (r3)...
    - inversion lhs_eq_t; subst. rename REL into REL1, H0 into H_lhs_obs. 
      inversion t_eq_rhs; subst. rename REL into REL2, H into H_rhs_obs.
      apply in_union_iff in REL1, REL2. destruct REL1 as [REL1 | REL1]; [inversion REL1 | ]. destruct REL2 as [REL2 | REL2]; [inversion REL2 | ].
      econstructor 2. left. right. exists (t3)...
    - rewrite <- H_t_obs in lhs_eq_t, t_eq_rhs. revert H_t_obs. destruct t_eq_rhs as [r2' r2 REL2 | t2' t2 REL | X2 e2 k2' k2 REL2]; try congruence.
      ii. rewrite H_t_obs in lhs_eq_t. destruct lhs_eq_t as [r1 r1' REL1 | t1 t1' REL1 | X1 e1 k1 k1' REL1]; try congruence.
      assert (X2_eq_X1 : X2 = X1).
      { exact (eq_congruence (fun ot : itreeF E R => match ot with VisF X e k => X | _ => X1 end) (VisF X2 e2 k2') (VisF X1 e1 k1') H_t_obs). }
      subst X2. rename X1 into X.
      assert (e1_eq_e2 : e1 = e2).
      { inversion H_t_obs. eapply ExcludedMiddle.projT2_eq with (B := fun X' : Type => E X')... }
      assert (k1_eq_k2 : k1' = k2').
      { inversion H_t_obs. eapply ExcludedMiddle.projT2_eq with (B := fun X' : Type => X' -> itree E R)... }
      subst e2 k2'. rename e1 into e, k1' into k.
      econstructor 3. intros x. specialize REL1 with (x := x). specialize REL2 with (x := x).
      apply in_union_iff in REL1, REL2. destruct REL1 as [REL1 | REL1]; [inversion REL1 | ]. destruct REL2 as [REL2 | REL2]; [inversion REL2 | ].
      left. right. exists (k x)...
  Qed.

  Local Instance eqITree_Reflexive
    : Reflexive eqITree.
  Proof. intros t1. exact (eqITree_reflexivity (t1, t1) eq_refl). Qed.

  Local Instance eqITree_Symmetric
    : Symmetric eqITree.
  Proof. intros t1 t2 t1_eq_t2. exact (eqITree_symmetry (t2, t1) t1_eq_t2). Qed.

  Local Instance eqITree_Transitive
    : Transitive eqITree.
  Proof. intros t1 t2 t3 t1_eq_t2 t2_eq_t3. exact (eqITree_transitivity (t1, t3) (@ex_intro _ _ t2 (@conj _ _ t1_eq_t2 t2_eq_t3))). Qed.

  Global Instance eqITree_Equivalence : Equivalence eqITree :=
    { Equivalence_Reflexive := eqITree_Reflexive
    ; Equivalence_Symmetric := eqITree_Symmetric
    ; Equivalence_Transitive := eqITree_Transitive
    }
  .

  Local Instance itree_E_R_isSetoid : isSetoid (itree E R) :=
    { eqProp := eqITree
    ; eqProp_Equivalence := eqITree_Equivalence
    }
  .

  Lemma Ret_eq_Ret_iff (x1 : R) (x2 : R)
    : Ret x1 == Ret x2 <-> x1 == x2.
  Proof.
    repeat rewrite eqITree_iff_itreeBisim. split; intros H_EQ.
    - apply unfold_itreeBisim in H_EQ. now inversion H_EQ; subst.
    - econstructor. now econstructor 1. 
  Qed.

  Lemma Tau_eq_Tau_iff (t1 : itree E R) (t2 : itree E R)
    : Tau t1 == Tau t2 <-> t1 == t2.
  Proof.
    repeat rewrite eqITree_iff_itreeBisim. split; intros H_EQ.
    - apply unfold_itreeBisim in H_EQ. now inversion H_EQ.
    - econstructor. now econstructor 2. 
  Qed.

  Lemma Vis_eq_Vis_iff (X : Type) (e : E X) (k1 : X -> itree E R) (k2 : X -> itree E R)
    : Vis X e k1 == Vis X e k2 <-> k1 == k2.
  Proof.
    change (eqITree (Vis X e k1) (Vis X e k2) <-> (forall x : X, eqITree (k1 x) (k2 x))). split; intros H_EQ.
    - rewrite eqITree_iff_itreeBisim in H_EQ. apply unfold_itreeBisim in H_EQ.
      inversion H_EQ as [ | | X' e' k1' k2' REL]; subst X'.
      assert (e_eq_e' : e = e').
      { now eapply ExcludedMiddle.projT2_eq with (B := fun X' : Type => E X'). }
      assert (k1_eq_k1' : k1 = k1').
      { now eapply ExcludedMiddle.projT2_eq with (B := fun X' : Type => X' -> itree E R). }
      assert (k2_eq_k2' : k2 = k2').
      { now eapply ExcludedMiddle.projT2_eq with (B := fun X' : Type => X' -> itree E R). }
      subst e' k1' k2'. intros x; rewrite eqITree_iff_itreeBisim; exact (REL x).
    - rewrite eqITree_iff_itreeBisim. econstructor. econstructor 3.
      intros x; rewrite <- eqITree_iff_itreeBisim; exact (H_EQ x).
  Qed.

  End ITREE_BISIMULATION.

  Global Arguments itreeBisimF {E} {R} {requiresSetoid} (bisim) (lhs) (rhs).

  Local Existing Instances freeSetoidFromSetoid1.

  Local Hint Resolve eqITreeF_isMonotonicMap : core.

  Section ITREE_EQUALITY.

  Context {E : Type -> Type}.

  Local Notation eqITreeF' := (eqITreeF' (E := E) (requiresSetoid := theFinestSetoidOf _)).

  Global Instance itree_E_isSetoid1 : isSetoid1 (itree E) :=
    { liftSetoid1 {R : Type} (R_isSetoid : isSetoid R) := itree_E_R_isSetoid (R := R) (requiresSetoid := R_isSetoid) }
  .

  Theorem obs_eq_obs_implies_eqITree {R : Type} (lhs : itree E R) (rhs : itree E R)
    (obs_eq_obs : observe lhs = observe rhs)
    : lhs == rhs.
  Proof.
    eapply eqITree_iff_itreeBisim; constructor.
    replace (observe rhs) with (observe lhs) by exact (obs_eq_obs).
    eapply eqITree_iff_itreeBisim; reflexivity.
  Qed.

  Corollary itree_eta {R : Type} (t : itree E R)
    : go (observe t) == t.
  Proof. now eapply obs_eq_obs_implies_eqITree. Qed.

  Lemma itree_bind_unfold {R1 : Type} {R2 : Type} (t0 : itree E R1) (k0 : R1 -> itree E R2) :
    bind t0 k0 ==
    match observe t0 with
    | RetF r => k0 r
    | TauF t => Tau (bind t k0)
    | VisF X e k => Vis X e (fun x : X => bind (k x) k0)
    end.
  Proof. eapply obs_eq_obs_implies_eqITree. exact (itree_bind_unfold_observed t0 k0). Qed.

  Lemma itree_iter_unfold {I : Type} {R : Type} (step : I -> itree E (I + R)) (arg : I) :
    itree_iter step arg ==
    bind (step arg) (fun res : I + R =>
      match res with
      | inl arg' => Tau (itree_iter step arg')
      | inr res' => Ret res'
      end
    ).
  Proof. now eapply obs_eq_obs_implies_eqITree. Qed.

  Section ITREE_BIND_CASES.

  Context {R1 : Type} {R2 : Type} (k0 : R1 -> itree E R2).

  Corollary itree_bind_Ret (r : R1)
    : bind (Ret r) k0 == k0 r.
  Proof. now rewrite itree_bind_unfold. Qed.

  Corollary itree_bind_Tau (t : itree E R1)
    : bind (Tau t) k0 == Tau (bind t k0).
  Proof. now rewrite itree_bind_unfold. Qed.

  Corollary itree_bind_Vis (X : Type) (e : E X) (k : X -> itree E R1)
    : bind (Vis X e k) k0 == Vis X e (fun x : X => bind (k x) k0).
  Proof. now rewrite itree_bind_unfold. Qed.

  End ITREE_BIND_CASES.

  Lemma itree_bind_assoc {R1 : Type} {R2 : Type} {R3 : Type} (t_0 : itree E R1) (k_1 : R1 -> itree E R2) (k_2 : R2 -> itree E R3)
    : (t_0 >>= k_1 >>= k_2) == (t_0 >>= fun x_1 => k_1 x_1 >>= k_2).
  Proof with eauto with *.
    revert t_0. set (Rel_image := image (fun '(lhs, rhs) => (lhs >>= k_1 >>= k_2, rhs >>= fun x_1 => k_1 x_1 >>= k_2))).
    enough (to_show : isSubsetOf (Rel_image (eqITreeF' cola_empty)) (eqITreeF' cola_empty)).
    { intros t0. eapply to_show. exists (t0, t0)... change (t0 == t0)... }
    eapply paco_accum... set (Rel_focus := cola_union cola_empty (Rel_image (eqITreeF' cola_empty))).
    assert (INIT : cola_union cola_empty (eqITreeF' cola_empty) =< cola_union Rel_focus (eqITreeF' Rel_focus)).
    { intros z [z_in | z_in]; [inversion z_in | right]. revert z z_in. change (eqITreeF' cola_empty =< eqITreeF' Rel_focus). eapply paco_preserves_monotonicity... }
    rewrite <- paco_fold. intros [k0_lhs k0_rhs] k0_lhs_eq_k0_rhs. apply in_image_iff in k0_lhs_eq_k0_rhs.
    destruct k0_lhs_eq_k0_rhs as [[lhs rhs] [H_EQ H_IN]].
    pose proof (eq_congruence fst _ _ H_EQ) as k0_lhs_is.
    pose proof (eq_congruence snd _ _ H_EQ) as k0_rhs_is.
    simpl in k0_lhs_is, k0_rhs_is. subst k0_lhs k0_rhs. clear H_EQ.
    apply paco_unfold in H_IN... do 3 red in H_IN. do 3 red.
    repeat rewrite itree_bind_unfold_observed. destruct H_IN as [r1 r2 REL | t1 t2 REL | X e k1 k2 REL]; simpl in REL; simpl.
    - rewrite <- itree_bind_unfold_observed. subst r2.
      pose proof (eqITree_reflexivity (requiresSetoid := theFinestSetoidOf R3) (itree_bind (k_1 r1) k_2, (itree_bind (k_1 r1) k_2)) eq_refl) as claim1.
      apply paco_unfold in claim1... exact (eqITreeF_isMonotonicMap _ _ INIT _ claim1).
    - destruct REL as [REL | REL]; [inversion REL | ].
      econstructor 2. left. right. exists (t1, t2)...
    - econstructor 3. intros x. specialize REL with (x := x).
      apply in_union_iff in REL. destruct REL as [REL | REL]; [inversion REL | ].
      left. right. exists (k1 x, k2 x)...
  Qed.

  Lemma itree_pure_left_id_bind {R1 : Type} {R2 : Type} (k : R1 -> itree E R2) (x : R1)
    : (pure x >>= k) == k x.
  Proof. exact (itree_bind_Ret k x). Qed.

  Lemma itree_pure_right_id_bind {R1 : Type} (t : itree E R1)
    : (t >>= pure) == t.
  Proof with eauto with *.
    revert t. keep (image (fun '(lhs, rhs) => (lhs >>= pure, rhs))) as Rel_image into (ensemble (itree E R1 * itree E R1) -> ensemble (itree E R1 * itree E R1)).
    enough (to_show : isSubsetOf (Rel_image (eqITreeF' cola_empty)) (eqITreeF' cola_empty)).
    { intros t0. eapply to_show. exists (t0, t0)... change (t0 == t0)... }
    eapply paco_accum... set (Rel_focus := cola_union cola_empty (Rel_image (eqITreeF' cola_empty))).
    assert (INIT : cola_union cola_empty (eqITreeF' cola_empty) =< cola_union Rel_focus (eqITreeF' Rel_focus)).
    { intros z [z_in | z_in]; [inversion z_in | right]. revert z z_in. change (eqITreeF' cola_empty =< eqITreeF' Rel_focus). eapply paco_preserves_monotonicity... }
    rewrite <- paco_fold. intros [k0_lhs k0_rhs] k0_lhs_eq_k0_rhs. apply in_image_iff in k0_lhs_eq_k0_rhs.
    destruct k0_lhs_eq_k0_rhs as [[lhs rhs] [H_EQ H_IN]].
    pose proof (eq_congruence fst _ _ H_EQ) as k0_lhs_is.
    pose proof (eq_congruence snd _ _ H_EQ) as k0_rhs_is.
    simpl in k0_lhs_is, k0_rhs_is. subst k0_lhs k0_rhs. clear H_EQ.
    apply paco_unfold in H_IN... do 3 red in H_IN. do 3 red.
    repeat rewrite itree_bind_unfold_observed. destruct H_IN as [r1 r2 REL | t1 t2 REL | X e k1 k2 REL]; simpl in REL; simpl.
    - econstructor 1...
    - destruct REL as [REL | REL]; [inversion REL | ].
      econstructor 2. left. right. exists (t1, t2)...
    - econstructor 3. intros x. specialize REL with (x := x).
      apply in_union_iff in REL. destruct REL as [REL | REL]; [inversion REL | ].
      left. right. exists (k1 x, k2 x)...
  Qed.

  Lemma itree_bind_compatWith_eqProp_on_1st_arg {R1 : Type} {R2 : Type} (t_1 : itree E R1) (t_2 : itree E R1)
    (HYP_FST_ARG_EQ : t_1 == t_2)
    : forall k_0 : R1 -> itree E R2, (t_1 >>= k_0) == (t_2 >>= k_0).
  Proof with eauto with *.
    intros k0. revert t_1 t_2 HYP_FST_ARG_EQ. set (Rel_image := image (fun '(lhs, rhs) => (lhs >>= k0, rhs >>= k0))).
    enough (to_show : isSubsetOf (Rel_image (eqITreeF' cola_empty)) (eqITreeF' cola_empty)).
    { ii. eapply to_show. exists (t_1, t_2)... }
    eapply paco_accum... set (Rel_focus := cola_union cola_empty (Rel_image (eqITreeF' cola_empty))).
    assert (INIT : cola_union cola_empty (eqITreeF' cola_empty) =< cola_union Rel_focus (eqITreeF' Rel_focus)).
    { intros z [z_in | z_in]; [inversion z_in | right]. revert z z_in. change (eqITreeF' cola_empty =< eqITreeF' Rel_focus). eapply paco_preserves_monotonicity... }
    rewrite <- paco_fold. intros [k0_lhs k0_rhs] k0_lhs_eq_k0_rhs. apply in_image_iff in k0_lhs_eq_k0_rhs.
    destruct k0_lhs_eq_k0_rhs as [[lhs rhs] [H_EQ H_IN]].
    assert (k0_lhs_is : k0_lhs = (lhs >>= k0)) by exact (eq_congruence fst _ _ H_EQ).
    assert (k0_rhs_is : k0_rhs = (rhs >>= k0)) by exact (eq_congruence snd _ _ H_EQ).
    clear H_EQ. subst k0_lhs k0_rhs. apply paco_unfold in H_IN...
    do 3 red in H_IN. do 3 red. unfold ">>="; simpl. do 2 rewrite itree_bind_unfold_observed.
    destruct H_IN as [r1 r2 REL | t1 t2 REL | X e k1 k2 REL]; simpl in *.
    - assert (claim1 : member (k0 r1, k0 r2) Rel_id) by congruence.
      pose proof (eqITree_reflexivity (requiresSetoid := theFinestSetoidOf R2) (k0 r1, k0 r2) claim1) as claim2.
      apply paco_unfold in claim2... do 3 red in claim2.
      exact (eqITreeF_isMonotonicMap _ _ INIT (k0 r1, k0 r2) claim2).
    - destruct REL as [REL | REL]; [inversion REL | ].
      econstructor 2. left. right...
    - econstructor 3. intros x. specialize REL with (x := x).
      destruct REL as [REL | REL]; [inversion REL | ]. left. right...
  Qed.

  Lemma itree_bind_compatWith_eqProp_on_2nd_arg {R1 : Type} {R2 : Type} (k_1 : R1 -> itree E R2) (k_2 : R1 -> itree E R2)
    (HYP_SND_ARG_EQ : forall x : R1, k_1 x == k_2 x)
    : forall t_0 : itree E R1, (t_0 >>= k_1) == (t_0 >>= k_2).
  Proof with eauto with *.
    keep (image (fun '(lhs, rhs) => (lhs >>= k_1, rhs >>= k_2))) as Rel_image into (ensemble (itree E R1 * itree E R1) -> ensemble (itree E R2 * itree E R2)).
    enough (to_show : isSubsetOf (Rel_image (eqITreeF' cola_empty)) (eqITreeF' cola_empty)).
    { intros t0. eapply to_show. exists (t0, t0)... change (t0 == t0)... }
    eapply paco_accum... set (Rel_focus := cola_union cola_empty (Rel_image (eqITreeF' cola_empty))).
    assert (INIT : cola_union cola_empty (eqITreeF' cola_empty) =< cola_union Rel_focus (eqITreeF' Rel_focus)).
    { intros z [z_in | z_in]; [inversion z_in | right]. revert z z_in. change (eqITreeF' cola_empty =< eqITreeF' Rel_focus). eapply paco_preserves_monotonicity... }
    rewrite <- paco_fold. intros [k0_lhs k0_rhs] k0_lhs_eq_k0_rhs. apply in_image_iff in k0_lhs_eq_k0_rhs.
    destruct k0_lhs_eq_k0_rhs as [[lhs rhs] [H_EQ H_IN]].
    pose proof (eq_congruence fst _ _ H_EQ) as k0_lhs_is.
    pose proof (eq_congruence snd _ _ H_EQ) as k0_rhs_is.
    simpl in k0_lhs_is, k0_rhs_is. subst k0_lhs k0_rhs. clear H_EQ.
    apply paco_unfold in H_IN... do 3 red in H_IN. do 3 red.
    repeat rewrite itree_bind_unfold_observed. destruct H_IN as [r1 r2 REL | t1 t2 REL | X e k1 k2 REL]; simpl in REL; simpl.
    - subst r2. rename r1 into x. specialize HYP_SND_ARG_EQ with (x := x).
      apply paco_unfold in HYP_SND_ARG_EQ... exact (eqITreeF_isMonotonicMap _ _ INIT _ HYP_SND_ARG_EQ).
    - apply in_union_iff in REL. destruct REL as [REL | REL]; [inversion REL | ].
      econstructor 2. left. right. exists (t1, t2)...
    - econstructor 3. intros x. specialize REL with (x := x).
      destruct REL as [REL | REL]; [inversion REL | ].
      left. right. exists (k1 x, k2 x)...
  Qed.

  Global Instance itree_E_obeysMonadLaws : LawsOfMonad (itree E) (requiresSetoid1 := itree_E_isSetoid1) :=
    { bind_assoc {R1 : Type} {R2 : Type} {R3 : Type} := itree_bind_assoc (R1 := R1) (R2 := R2) (R3 := R3)
    ; pure_left_id_bind {R1 : Type} {R2 : Type} := itree_pure_left_id_bind (R1 := R1) (R2 := R2)
    ; pure_right_id_bind {R1 : Type} := itree_pure_right_id_bind (R1 := R1)
    ; bind_compatWith_eqProp_on_1st_arg {R1 : Type} {R2 : Type} := itree_bind_compatWith_eqProp_on_1st_arg (R1 := R1) (R2 := R2)
    ; bind_compatWith_eqProp_on_2nd_arg {R1 : Type} {R2 : Type} := itree_bind_compatWith_eqProp_on_2nd_arg (R1 := R1) (R2 := R2)
    }
  .

  End ITREE_EQUALITY.

  Lemma reduce_itree_tick {E : Type -> Type} {R : Type} (k : unit -> itree E R)
    : (itree_tick >>= k) == Tau (k tt).
  Proof.
    unfold itree_tick. rewrite itree_bind_Tau. eapply Tau_eq_Tau_iff.
    eapply itree_pure_left_id_bind with (x := tt).
  Qed.

  Lemma reduce_itree_trigger {E : Type -> Type} {R : Type} (X : Type) (e : E X) (k : X -> itree E R)
    : (itree_trigger X e >>= k) == Vis X e k.
  Proof.
    unfold itree_trigger. rewrite itree_bind_Vis. eapply Vis_eq_Vis_iff.
    intros x; eapply itree_pure_left_id_bind with (x := x).
  Qed.

End InteractionTreeTheory.

*)
