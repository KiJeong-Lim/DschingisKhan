Require Import Coq.Lists.List.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeUtil.
Require Import DschingisKhan.Prelude.PreludeClassic.
Require Import DschingisKhan.Math.BasicPosetTheory.
Require Import DschingisKhan.Math.BooleanAlgebra.
Require Import DschingisKhan.Logic.PropositionalLogic.

Module ClassicalMetaTheoryOnPropositonalLogic.

  Import ListNotations ExcludedMiddle BooleanAlgebra CountableBooleanAlgebra SyntaxOfPL SemanticsOfPL InferenceRulesOfPL LindenbaumBooleanAlgebraOfPL ConstructiveMetaTheoryOnPropositonalLogic.

  Lemma ByAssumption_preserves (Gamma : ensemble formula) (C : formula)
    (ELEM : C \in Gamma)
    : Gamma ⊧ C.
  Proof with eauto with *.
    eapply extend_entails with (Gamma := singleton C)...
    ii. eapply env_satisfies...
  Qed.

  Lemma ContradictionI_preserves (Gamma : ensemble formula) (A : formula)
    (ENTAILS1 : Gamma ⊧ A)
    (ENTAILS2 : Gamma ⊧ NegationF A)
    : Gamma ⊧ ContradictionF.
  Proof with (simpl in *; tauto) || eauto with *.
    ii. pose proof (ENTAILS1 env env_satisfies) as claim1. pose proof (ENTAILS2 env env_satisfies) as claim2.
    inversion claim1; subst. inversion claim2; subst. econstructor...
  Qed.

  Lemma ContradictionE_preserves (Gamma : ensemble formula) (A : formula)
    (ENTAILS1 : Gamma ⊧ ContradictionF)
    : Gamma ⊧ A.
  Proof with (simpl in *; tauto) || eauto with *.
    ii. pose proof (ENTAILS1 env env_satisfies) as claim1.
    inversion claim1; subst. econstructor...
  Qed.

  Lemma NegationI_preserves (Gamma : ensemble formula) (A : formula)
    (ENTAILS1 : insert A Gamma ⊧ ContradictionF)
    : Gamma ⊧ NegationF A.
  Proof with (simpl in *; tauto) || eauto with *.
    ii. econstructor. simpl. intros EVAL_TO_TRUE.
    assert (claim1 : forall b : formula, member b (insert A Gamma) -> env `satisfies` b).
    { intros b. rewrite in_insert_iff. intros [A_eq_b | b_in_Gamma]...
      subst b. econstructor...
    }
    pose proof (ENTAILS1 env claim1) as claim2.
    inversion claim2; subst...
  Qed.

  Lemma NegationE_preserves (Gamma : ensemble formula) (A : formula)
    (ENTAILS1 : insert (NegationF A) Gamma ⊧ ContradictionF)
    : Gamma ⊧ A.
  Proof with (simpl in *; tauto) || eauto with *.
    ii. econstructor. eapply NNPP. intros EVAL_TO_FALSE.
    assert (claim1 : forall b : formula, member b (insert (NegationF A) Gamma) -> env `satisfies` b).
    { intros b. rewrite in_insert_iff. intros [NegationF_A_eq_b | b_in_Gamma]...
      subst b. econstructor...
    }
    pose proof (ENTAILS1 env claim1) as claim2.
    inversion claim2; subst...
  Qed.

  Lemma ConjunctionI_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
    (ENTAILS1 : Gamma ⊧ A)
    (ENTAILS2 : Gamma ⊧ B)
    : Gamma ⊧ ConjunctionF A B.
  Proof with (simpl in *; tauto) || eauto with *.
    ii. pose proof (ENTAILS1 env env_satisfies) as claim1. pose proof (ENTAILS2 env env_satisfies) as claim2.
    inversion claim1; subst. inversion claim2; subst. econstructor...
  Qed.

  Lemma ConjunctionE1_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
    (ENTAILS1 : Gamma ⊧ ConjunctionF A B)
    : Gamma ⊧ A.
  Proof with (simpl in *; tauto) || eauto with *.
    ii. pose proof (ENTAILS1 env env_satisfies) as claim1.
    inversion claim1; subst. econstructor...
  Qed.

  Lemma ConjunctionE2_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
    (ENTAILS1 : Gamma ⊧ ConjunctionF A B)
    : Gamma ⊧ B.
  Proof with (simpl in *; tauto) || eauto with *.
    ii. pose proof (ENTAILS1 env env_satisfies) as claim1.
    inversion claim1; subst. econstructor...
  Qed.

  Lemma DisjunctionI1_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
    (ENTAILS1 : Gamma ⊧ A)
    : Gamma ⊧ DisjunctionF A B.
  Proof with (simpl in *; tauto) || eauto with *.
    ii. pose proof (ENTAILS1 env env_satisfies) as claim1.
    inversion claim1; subst. econstructor...
  Qed.

  Lemma DisjunctionI2_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
    (ENTAILS1 : Gamma ⊧ B)
    : Gamma ⊧ DisjunctionF A B.
  Proof with (simpl in *; tauto) || eauto with *.
    ii. pose proof (ENTAILS1 env env_satisfies) as claim1.
    inversion claim1; subst. econstructor...
  Qed.

  Lemma DisjunctionE_preserves (Gamma : ensemble formula) (A : formula) (B : formula) (C : formula)
    (ENTAILS1 : Gamma ⊧ DisjunctionF A B)
    (ENTAILS2 : insert A Gamma ⊧ C)
    (ENTAILS3 : insert B Gamma ⊧ C)
    : Gamma ⊧ C.
  Proof with (simpl in *; tauto) || eauto with *.
    ii. econstructor.
    pose proof (ENTAILS1 env env_satisfies) as claim1.
    inversion claim1; subst.
    destruct EVAL_TO_TRUE as [EVAL_TO_TRUE | EVAL_TO_TRUE].
    - assert (claim2 : forall b : formula, member b (insert A Gamma) -> env `satisfies` b).
      { intros b. rewrite in_insert_iff. intros [A_eq_b | b_in_Gamma]...
        subst b. econstructor...
      }
      pose proof (ENTAILS2 env claim2) as claim3.
      inversion claim3; subst...
    - assert (claim2 : forall b : formula, member b (insert B Gamma) -> env `satisfies` b).
      { intros b. rewrite in_insert_iff. intros [B_eq_b | b_in_Gamma]...
        subst b. econstructor...
      }
      pose proof (ENTAILS3 env claim2) as claim3.
      inversion claim3; subst...
  Qed.

  Lemma ImplicationI_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
    (ENTAILS1 : insert A Gamma ⊧ B)
    : Gamma ⊧ ImplicationF A B.
  Proof with (simpl in *; tauto) || eauto with *.
    ii. econstructor. simpl. intros EVAL_TO_TRUE.
    assert (claim1 : forall b : formula, member b (insert A Gamma) -> env `satisfies` b).
    { intros b. rewrite in_insert_iff. intros [A_eq_b | b_in_Gamma]...
      subst b. econstructor...
    }
    pose proof (ENTAILS1 env claim1) as claim2.
    inversion claim2; subst...
  Qed.

  Lemma ImplicationE_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
    (ENTAILS1 : Gamma ⊧ ImplicationF A B)
    (ENTAILS2 : Gamma ⊧ A)
    : Gamma ⊧ B.
  Proof with (simpl in *; tauto) || eauto with *.
    ii. pose proof (ENTAILS1 env env_satisfies) as claim1. inversion claim1; subst.
    econstructor. simpl in EVAL_TO_TRUE. eapply EVAL_TO_TRUE.
    pose proof (ENTAILS2 env env_satisfies) as claim2. inversion claim2; subst...
  Qed.

  Lemma BiconditionalI_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
    (ENTAILS1 : insert A Gamma ⊧ B)
    (ENTAILS2 : insert B Gamma ⊧ A)
    : Gamma ⊧ BiconditionalF A B.
  Proof with (simpl in *; tauto) || eauto with *.
    ii. econstructor. simpl. split; intros EVAL_TO_TRUE.
    - assert (claim1 : forall b : formula, member b (insert A Gamma) -> env `satisfies` b).
      { intros b. rewrite in_insert_iff. intros [A_eq_b | b_in_Gamma]...
        subst b. econstructor...
      }
      pose proof (ENTAILS1 env claim1) as claim2.
      inversion claim2; subst...
    - assert (claim1 : forall b : formula, member b (insert B Gamma) -> env `satisfies` b).
      { intros b. rewrite in_insert_iff. intros [B_eq_b | b_in_Gamma]...
        subst b. econstructor...
      }
      pose proof (ENTAILS2 env claim1) as claim2.
      inversion claim2; subst...
  Qed.

  Lemma BiconditionalE1_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
    (ENTAILS1 : Gamma ⊧ BiconditionalF A B)
    (ENTAILS2 : Gamma ⊧ A)
    : Gamma ⊧ B.
  Proof with (simpl in *; tauto) || eauto with *.
    ii. pose proof (ENTAILS1 env env_satisfies) as claim1. inversion claim1; subst.
    econstructor. simpl in EVAL_TO_TRUE. eapply EVAL_TO_TRUE.
    pose proof (ENTAILS2 env env_satisfies) as claim2. inversion claim2; subst...
  Qed.

  Lemma BiconditionalE2_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
    (ENTAILS1 : Gamma ⊧ BiconditionalF A B)
    (ENTAILS2 : Gamma ⊧ B)
    : Gamma ⊧ A.
  Proof with (simpl in *; tauto) || eauto with *.
    ii. pose proof (ENTAILS1 env env_satisfies) as claim1. inversion claim1; subst.
    econstructor. simpl in EVAL_TO_TRUE. eapply EVAL_TO_TRUE.
    pose proof (ENTAILS2 env env_satisfies) as claim2. inversion claim2; subst...
  Qed.

  Theorem the_propositional_soundness_theorem (X : ensemble formula) (b : formula)
    (INFERS : X ⊢ b)
    : X ⊧ b.
  Proof with eauto.
    induction INFERS.
    - eapply ByAssumption_preserves with (C := C)...
    - eapply ContradictionI_preserves with (A := A)...
    - eapply ContradictionE_preserves with (A := A)...
    - eapply NegationI_preserves with (A := A)...
    - eapply NegationE_preserves with (A := A)...
    - eapply ConjunctionI_preserves with (A := A) (B := B)...
    - eapply ConjunctionE1_preserves with (A := A) (B := B)...
    - eapply ConjunctionE2_preserves with (A := A) (B := B)...
    - eapply DisjunctionI1_preserves with (A := A) (B := B)...
    - eapply DisjunctionI2_preserves with (A := A) (B := B)...
    - eapply DisjunctionE_preserves with (A := A) (B := B) (C := C)...
    - eapply ImplicationI_preserves with (A := A) (B := B)...
    - eapply ImplicationE_preserves with (A := A) (B := B)...
    - eapply BiconditionalI_preserves with (A := A) (B := B)...
    - eapply BiconditionalE1_preserves with (A := A) (B := B)...
    - eapply BiconditionalE2_preserves with (A := A) (B := B)...
  Qed.

  Lemma hasModelIfConsistent (X : ensemble formula)
    (CONSISTENT : ~ X ⊢ ContradictionF)
    : isSubsetOf X (MaximalConsistentSet X) /\ isStructure (MaximalConsistentSet X).
  Proof with eauto with *. (* Infinitely grateful for Taeseung's advice! *)
    revert X CONSISTENT.
    pose proof (lemma1 := @isSubsetOf_singleton_if formula).
    assert (lemma2 : forall X : ensemble formula, forall x : formula, isSubsetOf X (insert x X)).
    { ii; ensemble_rewrite. }
    pose proof (lemma3 := @isSubsetOf_empty_if formula).
    assert (lemma4 : forall X : ensemble formula, forall x : formula, member x (insert x X)).
    { ii; ensemble_rewrite. }
    ii. set (X_dagger := MaximalConsistentSet X).
    pose proof (theorem_of_1_3_10 X) as [? ? ? ? ?].
    fold X_dagger in SUBSET, EQUICONSISTENT, CLOSED_infers, META_DN, IMPLICATION_FAITHFUL.
    pose proof (theorem_of_1_2_14 (Th X) (lemma1_of_1_3_8 X)) as [SUBSET' IS_FILTER' COMPLETE' EQUICONSISTENT'].
    fold (MaximalConsistentSet X) in SUBSET', IS_FILTER', COMPLETE', EQUICONSISTENT'.
    fold X_dagger in SUBSET', IS_FILTER', COMPLETE', EQUICONSISTENT'.
    pose proof (claim1 := Th_isSubsetOf_cl X).
    pose proof (claim2 := cl_isSubsetOf_Th X).
    assert (claim3 : equiconsistent (cl X) X_dagger).
    { split; intros INCONSISTENT.
      - eapply inconsistent_compatWith_isSubsetOf with (X := Th X)...
        rewrite <- cl_eq_Th...
      - eapply inconsistent_compatWith_isSubsetOf with (X := Th X)...
        eapply EQUICONSISTENT...
    }
    assert (claim4 : ~ inconsistent X_dagger).
    { intros INCONSISTENT. contradiction CONSISTENT.
      eapply inconsistent_cl_iff, claim3...
    }
    assert (claim5 : ~ inconsistent (cl X_dagger)).
    { intros INCONSISTENT. contradiction claim4.
      eapply inconsistent_compatWith_isSubsetOf with (X := cl X_dagger)...
      eapply fact5_of_1_2_8...
    }
    assert (
      forall i : propLetter,
      AtomF i \in X_dagger <-> evalFormula (preimage AtomF X_dagger) (AtomF i)
    ) as caseAtomF.
    { ii. change (AtomF i \in X_dagger <-> i \in preimage AtomF X_dagger).
      rewrite in_preimage_iff. split...
      intros [p [? ?]]; subst p...
    }
    assert (
      ContradictionF \in X_dagger <-> evalFormula (preimage AtomF X_dagger) ContradictionF
    ) as caseContradictionF.
    { simpl. rewrite CLOSED_infers, <- inconsistent_cl_iff. tauto. }
    assert (
      forall p1 : formula,
      forall IH1 : p1 \in X_dagger <-> evalFormula (preimage AtomF X_dagger) p1,
      NegationF p1 \in X_dagger <-> evalFormula (preimage AtomF X_dagger) (NegationF p1)
    ) as caseNegationF.
    { ii. simpl. rewrite <- IH1, CLOSED_infers. split.
      - intros INFERS H_in.
        contradiction claim5.
        eapply inconsistent_cl_iff. eapply ContradictionI with (A := p1)...
        eapply CLOSED_infers...
      - intros H_not_in.
        eapply CLOSED_infers, META_DN. unnw. intros H_in.
        eapply CLOSED_infers. eapply ContradictionI with (A := NegationF p1).
        + enough (claim6 : MaximalConsistentSet X ⊢ ImplicationF p1 ContradictionF).
          { eapply NegationI. eapply ImplicationE with (A := p1).
            - eapply extend_infers...
            - eapply ByAssumption...
          }
          eapply CLOSED_infers, IMPLICATION_FAITHFUL. tauto.
        + eapply ByAssumption...
    }
    assert (
      forall p1 : formula,
      forall p2 : formula,
      forall IH1 : p1 \in X_dagger <-> evalFormula (preimage AtomF X_dagger) p1,
      forall IH2 : p2 \in X_dagger <-> evalFormula (preimage AtomF X_dagger) p2,
      ConjunctionF p1 p2 \in X_dagger <-> evalFormula (preimage AtomF X_dagger) (ConjunctionF p1 p2)
    ) as caseConjunctionF.
    { ii. simpl. rewrite <- IH1, <- IH2. split.
      - intros H_in. split.
        + eapply CLOSED_infers, ConjunctionE1, CLOSED_infers...
        + eapply CLOSED_infers, ConjunctionE2, CLOSED_infers...
      - intros [H_in1 H_in2].
        eapply CLOSED_infers, ConjunctionI; eapply CLOSED_infers...
    }
    assert (
      forall p1 : formula,
      forall p2 : formula,
      forall IH1 : p1 \in X_dagger <-> evalFormula (preimage AtomF X_dagger) p1,
      forall IH2 : p2 \in X_dagger <-> evalFormula (preimage AtomF X_dagger) p2,
      DisjunctionF p1 p2 \in X_dagger <-> evalFormula (preimage AtomF X_dagger) (DisjunctionF p1 p2)
    ) as caseDisjunctionF.
    { ii. simpl. rewrite <- IH1, <- IH2. split.
      - intros H_in. pose proof (classic (X_dagger ⊢ p1)) as [H_yes | H_no].
        + left. eapply CLOSED_infers...
        + right. eapply CLOSED_infers.
          eapply ImplicationE with (A := NegationF p1).
          { eapply DisjunctionE with (A := p1) (B := p2) (C := ImplicationF (NegationF p1) p2).
            - eapply CLOSED_infers...
            - eapply ImplicationI, ContradictionE. eapply ContradictionI with (A := p1).
              + eapply ByAssumption. right; left...
              + eapply ByAssumption. left...
            - eapply ImplicationI, ByAssumption. right; left...
          }
          { eapply CLOSED_infers, caseNegationF...
            simpl. rewrite <- IH1. intros H_false.
            apply CLOSED_infers in H_false...
          }
      - intros [H_in | H_in].
        + eapply CLOSED_infers, DisjunctionI1, CLOSED_infers...
        + eapply CLOSED_infers, DisjunctionI2, CLOSED_infers...
    }
    assert (
      forall p1 : formula,
      forall p2 : formula,
      forall IH1 : p1 \in X_dagger <-> evalFormula (preimage AtomF X_dagger) p1,
      forall IH2 : p2 \in X_dagger <-> evalFormula (preimage AtomF X_dagger) p2,
      ImplicationF p1 p2 \in X_dagger <-> evalFormula (preimage AtomF X_dagger) (ImplicationF p1 p2)
    ) as caseImplicationF.
    { ii. rewrite IMPLICATION_FAITHFUL. simpl. unnw. tauto. }
    assert (
      forall p1 : formula,
      forall p2 : formula,
      forall IH1 : p1 \in X_dagger <-> evalFormula (preimage AtomF X_dagger) p1,
      forall IH2 : p2 \in X_dagger <-> evalFormula (preimage AtomF X_dagger) p2,
      BiconditionalF p1 p2 \in X_dagger <-> evalFormula (preimage AtomF X_dagger) (BiconditionalF p1 p2)
    ) as caseBiconditionalF.
    { ii. simpl. transitivity (ImplicationF p1 p2 \in X_dagger /\ ImplicationF p2 p1 \in X_dagger).
      { split.
        - intros H_in. split.
          { eapply CLOSED_infers, ImplicationI. eapply BiconditionalE1 with (A := p1) (B := p2).
            - eapply extend_infers with (Gamma := X_dagger)...
              eapply CLOSED_infers...
            - eapply ByAssumption. left...
          }
          { eapply CLOSED_infers, ImplicationI. eapply BiconditionalE2 with (A := p1) (B := p2).
            - eapply extend_infers with (Gamma := X_dagger)...
              eapply CLOSED_infers...
            - eapply ByAssumption. left...
          }
        - intros [H_in1 H_in2].
          eapply CLOSED_infers, BiconditionalI.
          { eapply ImplicationE with (A := p1).
            - eapply extend_infers with (Gamma := X_dagger)...
              eapply CLOSED_infers...
            - eapply ByAssumption. left...
          }
          { eapply ImplicationE with (A := p2).
            - eapply extend_infers with (Gamma := X_dagger)...
              eapply CLOSED_infers...
            - eapply ByAssumption. left...
          }
      }
      { split.
        - intros [H_in1 H_in2]. eapply caseImplicationF in H_in1, H_in2...
        - intros [H_in1 H_in2]. eapply caseImplicationF in H_in1, H_in2...
      }
    }
    split.
    { transitivity (Th X)... ii. econstructor. eapply ByAssumption... }
    { unfold isStructure. induction A... }
  Qed.

  Theorem the_propositional_completeness_theorem (Gamma : ensemble formula) (C: formula)
    (ENTAILS : Gamma ⊧ C)
    : Gamma ⊢ C.
  Proof with eauto with *.
    eapply NNPP. intros it_is_false_that_Gamma_infers_C.
    set (X := insert (NegationF C) Gamma).
    assert (CONSISTENT : X ⊬ ContradictionF).
    { intros INCONSISTENT. contradiction it_is_false_that_Gamma_infers_C. eapply NegationE... }
    pose proof (theorem_of_1_2_14 (Th X) (lemma1_of_1_3_8 X)) as [SUBSET' IS_FILTER' COMPLETE' EQUICONSISTENT'].
    fold (MaximalConsistentSet X) in SUBSET', IS_FILTER', COMPLETE', EQUICONSISTENT'.
    pose proof (hasModelIfConsistent X CONSISTENT) as [INCL IS_STRUCTURE].
    unfold isStructure in IS_STRUCTURE.
    pose proof (theorem_of_1_3_10 Gamma) as [? ? ? ? ?]; unnw.
    contradiction it_is_false_that_Gamma_infers_C.
    eapply completeness_theorem_prototype with (env := preimage AtomF (MaximalConsistentSet X)); trivial.
    - unfold equiconsistent in *.
      transitivity (inconsistent (MaximalConsistentSet X))...
      split; intros [botBA [botBA_in botBA_eq_falseBA]].
      + exists (botBA). split... eapply IS_STRUCTURE...
      + exists (botBA). split... eapply IS_STRUCTURE...
    - transitivity (MaximalConsistentSet X)...
      ii. eapply IS_STRUCTURE...
    - eapply isFilter_compatWith_eqProp...
  Qed.

  Corollary the_propositional_compactness_theorem (Gamma : ensemble formula) (C : formula)
    : Gamma ⊧ C <-> << FINITE_ENTAILS : exists xs : list formula, exists X : ensemble formula, isFiniteSubsetOf xs Gamma /\ isListRepOf xs X /\ X ⊧ C >>.
  Proof with eauto.
    unnw. split.
    - intros ENTAILS.
      apply the_propositional_completeness_theorem in ENTAILS.
      apply inference_is_finite in ENTAILS. des. exists (xs), (X').
      split... split... eapply the_propositional_soundness_theorem...
    - des. eapply extend_entails... now firstorder.
  Qed.

End ClassicalMetaTheoryOnPropositonalLogic.
