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

Module InteractionTreeTheory.

  Import InteractionTrees BasicPosetTheory BasicCoLaTheory ParameterizedCoinduction.

  Section ITREE_EQUIVALENCE_RELATION.

  Context {E : Type -> Type} {R : Type} {requiresSetoid : isSetoid R}.

  Lemma eqITreeF_isMonotonicMap
    : isMonotonicMap (fun BISIM : ensemble (itree E R * itree E R) => eqITreeF BISIM).
  Proof. exact (eqITreeF_monotonic). Defined.

  Definition eqITree (lhs : itree E R) (rhs : itree E R) : Prop :=
    member (lhs, rhs) (paco eqITreeF cola_empty)
  .

  Theorem eqITree_iff_itreeBisim (lhs : itree E R) (rhs : itree E R)
    : eqITree lhs rhs <-> itreeBisim lhs rhs.
  Proof.
    revert lhs rhs. keep (uncurry itreeBisim) as itreeBisim' into (ensemble (itree E R * itree E R)).
    set (f := @exist (ensemble (itree E R * itree E R) -> ensemble (itree E R * itree E R)) isMonotonicMap eqITreeF eqITreeF_isMonotonicMap).
    enough (claim1 : isSubsetOf itreeBisim' (proj1_sig f itreeBisim')).
    enough (claim2 : isSupremumOf itreeBisim' (PostfixedPoints (proj1_sig f))).
    enough (claim3 : paco eqITreeF cola_empty == itreeBisim').
    - ii. exact (claim3 (lhs, rhs)).
    - eapply @Supremum_preserves_eqProp_wrtEnsembles with (requiresPoset := ensemble_isPoset (itree E R * itree E R)%type) (X1 := PostfixedPoints (proj1_sig f)) (X2 := PostfixedPoints (proj1_sig f)).
      + rewrite paco_init with (F_monotonic := eqITreeF_isMonotonicMap). eapply nu_isSupremumOf_PostfixedPoints.
      + exact (claim2).
      + reflexivity.
    - intros Y. split.
      + intros le_Y X X_in. unnw. do 2 red in X_in. rewrite <- le_Y. intros [lhs rhs] H_in. change (itreeBisim lhs rhs). revert lhs rhs H_in.
        cofix CIH. ii. econstructor. exact (eqITreeF_isMonotonicMap X (uncurry itreeBisim) (fun '(LHS, RHS) => CIH LHS RHS) (lhs, rhs) (X_in (lhs, rhs) H_in)).
      + intros ?; desnw. eapply UPPER_BOUND. exact (claim1).
    - intros [lhs rhs] H_in. eapply unfold_itreeBisim. exact (H_in). 
  Qed.

  Definition Rel_id : ensemble (itree E R * itree E R) :=
    fun '(lhs, rhs) => lhs = rhs
  .

  Definition Rel_flip (BISIM : ensemble (itree E R * itree E R)) : ensemble (itree E R * itree E R) :=
    fun '(lhs, rhs) => member (rhs, lhs) BISIM
  .

  Definition Rel_compose (BISIM : ensemble (itree E R * itree E R)) (BISIM' : ensemble (itree E R * itree E R)) : ensemble (itree E R * itree E R) :=
    fun '(lhs, rhs) => exists t : itree E R, member (lhs, t) BISIM /\ member (t, rhs) BISIM'
  .

  Local Hint Resolve eqITreeF_isMonotonicMap : core.

  Lemma eqITree_reflexivity
    : isSubsetOf Rel_id (paco eqITreeF cola_empty).
  Proof with eauto with *.
    eapply paco_accum... set (Rel_focus := cola_union cola_empty Rel_id).
    transitivity (eqITreeF (cola_union Rel_focus (paco eqITreeF Rel_focus))).
    { intros [lhs rhs] lhs_eq_rhs. do 3 red. do 2 red in lhs_eq_rhs.
      destruct (observe lhs) as [r1 | t1 | X1 e1 k1] eqn: H_lhs_obs; destruct (observe rhs) as [r2 | t2 | X2 e2 k2] eqn: H_rhs_obs; try congruence.
      - econstructor 1. replace (r2) with (r1) by congruence. reflexivity.
      - econstructor 2. left. right. do 2 red. congruence.
      - assert (obs_eq : @eq (itreeF E R) (VisF X1 e1 k1) (VisF X2 e2 k2)) by congruence.
        rewrite obs_eq. econstructor 3. ii. left. right. reflexivity.
    }
    transitivity (paco eqITreeF (cola_union cola_empty Rel_id)).
    { eapply paco_fold. }
    eapply paco_preserves_monotonicity...
  Qed.

  Lemma eqITree_symmetry
    : isSubsetOf (Rel_flip (paco eqITreeF cola_empty)) (paco eqITreeF cola_empty).
  Proof with eauto with *.
    eapply paco_accum... set (Rel_focus := cola_union cola_empty (Rel_flip (paco eqITreeF cola_empty))).
    transitivity (eqITreeF (cola_union Rel_focus (paco eqITreeF Rel_focus))).
    { intros [lhs rhs] lhs_eq_rhs. apply paco_unfold in lhs_eq_rhs... do 3 red in lhs_eq_rhs. do 3 red.
      destruct lhs_eq_rhs as [r1 r2 REL | t1 t2 REL | X e k1 k2 REL].
      - econstructor 1. symmetry...
      - econstructor 2. apply in_union_iff in REL. destruct REL as [REL | REL]; [inversion REL | left; right]...
      - econstructor 3. intros x. specialize REL with (x := x).
        apply in_union_iff in REL. destruct REL as [REL | REL]; [inversion REL | left; right]...
    }
    eapply paco_fold.
  Qed.

  Lemma eqITree_transitivity
    : isSubsetOf (Rel_compose (paco eqITreeF cola_empty) (paco eqITreeF cola_empty)) (paco eqITreeF cola_empty).
  Proof with eauto with *.
    eapply paco_accum... set (Rel_focus := cola_union cola_empty (Rel_compose (paco eqITreeF cola_empty) (paco eqITreeF cola_empty))).
    assert (INIT : eqITreeF (cola_union cola_empty (paco eqITreeF cola_empty)) =< eqITreeF (cola_union Rel_focus (paco eqITreeF Rel_focus))).
    { eapply eqITreeF_isMonotonicMap. intros [lhs rhs] [lhs_eq_rhs | lhs_eq_rhs].
      - inversion lhs_eq_rhs.
      - right. eapply paco_preserves_monotonicity with (x := cola_empty)...
    }
    transitivity (eqITreeF (cola_union Rel_focus (paco eqITreeF Rel_focus))).
    { intros [lhs rhs] [t [lhs_eq_t t_eq_rhs]]. apply paco_unfold in lhs_eq_t... apply paco_unfold in t_eq_rhs... do 3 red in lhs_eq_t, t_eq_rhs. do 3 red.
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
        { inversion H_t_obs. eapply ExclusiveMiddle.projT2_eq with (A := Type) (B := fun X' : Type => E X')... }
        assert (k1_eq_k2 : k1' = k2').
        { inversion H_t_obs. eapply ExclusiveMiddle.projT2_eq with (A := Type) (B := fun X' : Type => X' -> itree E R)... }
        subst e2 k2'. rename e1 into e, k1' into k.
        econstructor 3. intros x. specialize REL1 with (x := x). specialize REL2 with (x := x).
        apply in_union_iff in REL1, REL2. destruct REL1 as [REL1 | REL1]; [inversion REL1 | ]. destruct REL2 as [REL2 | REL2]; [inversion REL2 | ].
        left. right. exists (k x)...
    }
    eapply paco_fold.
  Qed.

  Local Instance eqITree_Reflexive
    : Reflexive eqITree.
  Proof. intros t1. exact (eqITree_reflexivity (t1, t1) eq_refl). Qed.

  Local Instance eqITree_Symmetric
    : Symmetric eqITree.
  Proof. intros t1 t2 t1_eq_t2. exact (eqITree_symmetry (t2, t1) t1_eq_t2). Qed.

  Local Instance eqITree_Transitive
    : Transitive eqITree.
  Proof. intros t1 t2 t3 t1_eq_t2 t2_eq_t3. exact (eqITree_transitivity (t1, t3) (ex_intro _ t2 (conj t1_eq_t2 t2_eq_t3))). Qed.

  Global Add Parametric Relation : (itree E R)
    eqITree
      reflexivity proved by eqITree_Reflexive
      symmetry proved by eqITree_Symmetric
      transitivity proved by eqITree_Transitive
    as eqITree_Equivalence.

  Local Instance itree_E_R_isSetoid : isSetoid (itree E R) :=
    { eqProp := eqITree
    ; eqProp_Equivalence := eqITree_Equivalence
    }
  .

  End ITREE_EQUIVALENCE_RELATION.

  Section ITREE_MONAD_LAWS.

  Local Existing Instances freeSetoidFromSetoid1.

  Context {E : Type -> Type}.

  Global Instance itree_E_isSetoid1 : isSetoid1 (itree E) :=
    { liftSetoid1 {R : Type} (R_isSetoid : isSetoid R) := itree_E_R_isSetoid (R := R) (requiresSetoid := R_isSetoid)
    }
  .

  Theorem eqITree_intro_obs_eq_obs {R : Type}
    (lhs : itree E R)
    (rhs : itree E R)
    (H_obs_eq_obs : observe lhs = observe rhs)
    : lhs == rhs.
  Proof.
    eapply eqITree_iff_itreeBisim; constructor.
    replace (observe rhs) with (observe lhs).
    eapply eqITree_iff_itreeBisim; reflexivity.
  Qed.

  Corollary itree_eta {R : Type} (t : itree E R)
    : go (observe t) == t.
  Proof. now apply eqITree_intro_obs_eq_obs. Qed.

  Definition eqITree' {R : Type} : ensemble (itree E R * itree E R) -> ensemble (itree E R * itree E R) :=
    paco (eqITreeF (E := E) (R := R) (requiresSetoid := theFinestSetoidOf R))
  .

  End ITREE_MONAD_LAWS.

End InteractionTreeTheory.
