Require Import Coq.Lists.List.
Require Import DschingisKhan.classical.ExclusiveMiddle.
Require Import DschingisKhan.projects.PropositionalLogic.Base.
Require Import DschingisKhan.projects.PropositionalLogic.ConstructiveMetaTheories.
Require Import DschingisKhan.pure.CBA.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module SoundnessOfPropositionLogic. (* Thanks to Taeseung Sohn *)

  Import MyEnsemble MyEnsembleNova ExclusiveMiddle SyntaxOfPL SemanticsOfPL InferenceRulesOfPL.

  Lemma ByAssumption_preserves {hs : ensemble formula} :
    forall a : formula,
    member a hs ->
    hs |= a.
  Proof with eauto with *.
    intros c H.
    apply (@extend_entails \left\{ c \right\})...
  Qed.

  Lemma ContradictionI_preserves {hs : ensemble formula} :
    forall a : formula,
    hs |= a ->
    hs |= NegationF a ->
    hs |= ContradictionF.
  Proof with simpl in *; tauto.
    intros a H H0 v H1.
    assert (H2 := H v H1).
    assert (H3 := H0 v H1).
    inversion H2; subst.
    inversion H3; subst...
  Qed.

  Lemma ContradictionE_preserves {hs : ensemble formula} :
    forall a : formula,
    hs |= ContradictionF ->
    hs |= a.
  Proof with simpl in *; tauto.
    intros a H v H0.
    assert (H1 := H v H0).
    inversion H1; subst...
  Qed.

  Lemma NegationI_preserves {hs : ensemble formula} :
    forall a : formula,
    insert a hs |= ContradictionF ->
    hs |= NegationF a.
  Proof with simpl in *; tauto.
    intros a H v H0.
    constructor.
    simpl.
    intros H1.
    assert (claim1 : forall h : formula, member h (insert a hs) -> satisfies v h).
    { intros h.
      rewrite in_insert_iff.
      intros [H2 | H2]; constructor.
      - rewrite H2...
      - assert (H3 := H0 h H2).
        inversion H3; subst...
    }
    assert (H2 := H v claim1).
    inversion H2; subst...
  Qed.

  Lemma NegationE_preserves {hs : ensemble formula} :
    forall a : formula,
    insert (NegationF a) hs |= ContradictionF ->
    hs |= a.
  Proof with simpl in *; tauto.
    intros a H v H0.
    constructor.
    apply NNPP.
    intros H1.
    assert (claim1 : forall h : formula, member h (insert (NegationF a) hs) -> satisfies v h).
    { intros h.
      rewrite in_insert_iff.
      intros [H2 | H2]; constructor.
      - rewrite H2...
      - assert (H3 := H0 h H2).
        inversion H3; subst...
    }
    assert (H2 := H v claim1).
    inversion H2; subst...
  Qed.

  Lemma ConjunctionI_preserves {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    hs |= a ->
    hs |= b ->
    hs |= ConjunctionF a b.
  Proof with simpl in *; tauto.
    intros a b H H0 v H1.
    constructor.
    assert (H2 := H v H1).
    assert (H3 := H0 v H1).
    inversion H2; subst.
    inversion H3; subst...
  Qed.

  Lemma ConjunctionE1_preserves {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    hs |= ConjunctionF a b ->
    hs |= a.
  Proof with simpl in *; tauto.
    intros a b H v H0.
    constructor.
    assert (H1 := H v H0).
    inversion H1; subst...
  Qed.

  Lemma ConjunctionE2_preserves {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    hs |= ConjunctionF a b ->
    hs |= b.
  Proof with simpl in *; tauto.
    intros a b H v H0.
    constructor.
    assert (H1 := H v H0).
    inversion H1; subst...
  Qed.

  Lemma DisjunctionI1_preserves {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    hs |= a ->
    hs |= DisjunctionF a b.
  Proof with simpl in *; tauto.
    intros a b H v H0.
    constructor.
    assert (H1 := H v H0).
    inversion H1; subst...
  Qed.

  Lemma DisjunctionI2_preserves {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    hs |= b ->
    hs |= DisjunctionF a b.
  Proof with simpl in *; tauto.
    intros a b H v H0.
    constructor.
    assert (H1 := H v H0).
    inversion H1; subst...
  Qed.

  Lemma DisjunctionE_preserves {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    forall c : formula,
    hs |= DisjunctionF a b ->
    insert a hs |= c ->
    insert b hs |= c ->
    hs |= c.
  Proof with simpl in *; tauto.
    intros a b c H H0 H1 v H2.
    constructor.
    assert (H3 := H v H2).
    inversion H3; subst.
    destruct H4 as [H4 | H4].
    - assert (claim1 : forall h : formula, member h (insert a hs) -> satisfies v h).
      { intros h.
        rewrite in_insert_iff.
        intros [H5 | H5]; constructor.
        - rewrite H5...
        - assert (H6 := H2 h H5).
          inversion H6; subst...
      }
      assert (H5 := H0 v claim1).
      inversion H5; subst...
    - assert (claim1 : forall h : formula, member h (insert b hs) -> satisfies v h).
      { intros h.
        rewrite in_insert_iff.
        intros [H5 | H5]; constructor.
        - rewrite H5...
        - assert (H6 := H2 h H5).
          inversion H6; subst...
      }
      assert (H5 := H1 v claim1).
      inversion H5; subst...
  Qed.

  Lemma ImplicationI_preserves {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    insert a hs |= b ->
    hs |= ImplicationF a b.
  Proof with simpl in *; tauto.
    intros a b H v H0.
    constructor.
    simpl.
    intros H1.
    assert (claim1 : forall h : formula, member h (insert a hs) -> satisfies v h).
    { intros h.
      rewrite in_insert_iff.
      intros [H2 | H2]; constructor.
      - rewrite H2...
      - assert (H3 := H0 h H2).
        inversion H3; subst...
    }
    assert (H2 := H v claim1).
    inversion H2; subst...
  Qed.

  Lemma ImplicationE_preserves {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    hs |= ImplicationF a b ->
    hs |= a ->
    hs |= b.
  Proof with simpl in *; tauto.
    intros a b H H0 v H1.
    constructor.
    assert (H2 := H v H1).
    inversion H2; subst.
    simpl in H3.
    apply H3.
    assert (H4 := H0 v H1).
    inversion H4; subst...
  Qed.

  Lemma BiconditionalI_preserves {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    insert a hs |= b ->
    insert b hs |= a ->
    hs |= BiconditionalF a b.
  Proof with simpl in *; tauto.
    intros a b H H0 v H1.
    constructor.
    simpl.
    split.
    - intros H2.
      assert (claim1 : forall h : formula, member h (insert a hs) -> satisfies v h).
      { intros h.
        rewrite in_insert_iff.
        intros [H3 | H3]; constructor.
        - rewrite H3...
        - assert (H4 := H1 h H3).
          inversion H4; subst...
      }
      assert (H3 := H v claim1).
      inversion H3; subst...
    - intros H2.
      assert (claim1 : forall h : formula, member h (insert b hs) -> satisfies v h).
      { intros h.
        rewrite in_insert_iff.
        intros [H3 | H3]; constructor.
        - rewrite H3...
        - assert (H4 := H1 h H3).
          inversion H4; subst...
      }
      assert (H3 := H0 v claim1).
      inversion H3; subst...
  Qed.

  Lemma BiconditionalE1_preserves {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    hs |= BiconditionalF a b ->
    hs |= a ->
    hs |= b.
  Proof with simpl in *; tauto.
    intros a b H H0 v H1.
    constructor.
    assert (H2 := H v H1).
    inversion H2; subst.
    simpl in H3.
    apply (proj1 H3).
    assert (H4 := H0 v H1).
    inversion H4; subst...
  Qed.

  Lemma BiconditionalE2_preserves {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    hs |= BiconditionalF a b ->
    hs |= b ->
    hs |= a.
  Proof with simpl in *; tauto.
    intros a b H H0 v H1.
    constructor.
    assert (H2 := H v H1).
    inversion H2; subst.
    simpl in H3.
    apply (proj2 H3).
    assert (H4 := H0 v H1).
    inversion H4; subst...
  Qed.

  Theorem the_propositional_soundness_theorem :
    forall hs : ensemble formula,
    forall c : formula,
    hs |- c ->
    hs |= c.
  Proof with try now firstorder.
    intros hs c H_infers.
    induction H_infers.
    - apply (ByAssumption_preserves h)...
    - apply (ContradictionI_preserves a)...
    - apply (ContradictionE_preserves a)...
    - apply (NegationI_preserves a)...
    - apply (NegationE_preserves a)...
    - apply (ConjunctionI_preserves a b)...
    - apply (ConjunctionE1_preserves a b)...
    - apply (ConjunctionE2_preserves a b)...
    - apply (DisjunctionI1_preserves a b)...
    - apply (DisjunctionI2_preserves a b)...
    - apply (DisjunctionE_preserves a b c)...
    - apply (ImplicationI_preserves a b)...
    - apply (ImplicationE_preserves a b)...
    - apply (BiconditionalI_preserves a b)...
    - apply (BiconditionalE1_preserves a b)...
    - apply (BiconditionalE2_preserves a b)...
  Qed.

End SoundnessOfPropositionLogic.

Module CompletenessOfPropositionLogic. (* Thanks to Taeseung Sohn *)

  Import ListNotations BasicSetoidTheory MyEnsemble BasicPosetTheory MyEnsembleNova CountableBooleanAlgebra ExclusiveMiddle SyntaxOfPL SemanticsOfPL InferenceRulesOfPL LindenbaumBooleanAlgebraOnPropositionLogic ConstructiveMetaTheoryOnPropositonalLogic.

  Definition makeModelFromMaximalConsistentSet : ensemble formula -> env :=
    preimage AtomF
  .

  Theorem ModelExistsIfConsistent :
    forall hs : ensemble formula,
    ~ hs |- ContradictionF ->
    forall p : formula,
    member p (MaximalConsistentSet hs) <-> eval_formula (makeModelFromMaximalConsistentSet (MaximalConsistentSet hs)) p.
  Proof with eauto with *. (* Infinitely grateful for Taeseung's advice! *)
    assert (lemma1 := @isSubsetOf_intro_singleton formula).
    assert (lemma2 : forall hs : ensemble formula, forall h : formula, isSubsetOf hs (insert h hs)).
    { intros hs h b.
      rewrite in_insert_iff...
    }
    assert (lemma3 := @isSubsetOf_intro_empty formula).
    assert (lemma4 : forall hs : ensemble formula, forall h : formula, member h (insert h hs)).
    { intros hs h.
      apply in_insert_iff...
    }
    intros hs claim1.
    set (hs_hat := MaximalConsistentSet hs).
    destruct (theorem_of_1_3_10 hs) as [claim2 [claim3 [claim4 [claim5 claim6]]]].
    fold hs_hat in claim2, claim3, claim4, claim5, claim6.
    assert (claim7 := Th_isSubsetOf_Cl).
    assert (claim8 := Cl_isSubsetOf_Th).
    assert (claim9 : equiconsistent (Cl hs) hs_hat).
    { split.
      - apply inconsistent_isSubsetOf.
        transitivity (Th hs)...
      - intros H.
        apply (inconsistent_isSubsetOf (Th hs))...
        apply claim3...
    }
    assert (claim10 : ~ inconsistent hs_hat).
    { intros H.
      contradiction claim1.
      apply inconsistent_iff, claim9...
    }
    assert (claim11 : ~ inconsistent (Cl hs_hat)).
    { intros H.
      contradiction claim10.
      apply (inconsistent_isSubsetOf (Cl (MaximalConsistentSet hs)))...
      apply fact5_of_1_2_8, theorem_of_1_2_14, lemma1_of_1_3_8.
    }
    assert ( caseAtomF :
      forall i : pvar,
      (member (AtomF i) hs_hat <-> eval_formula (preimage AtomF hs_hat) (AtomF i))
    ).
    { intros i.
      rewrite <- (in_preimage_iff i)...
    }
    assert ( caseContradictonF :
      (member ContradictionF hs_hat <-> eval_formula (preimage AtomF hs_hat) ContradictionF)
    ).
    { simpl.
      rewrite claim4, <- inconsistent_iff.
      tauto.
    }
    assert ( caseNegationF :
      forall p1 : formula,
      (member p1 hs_hat <-> eval_formula (preimage AtomF hs_hat) p1) ->
      (member (NegationF p1) hs_hat <-> eval_formula (preimage AtomF hs_hat) (NegationF p1))
    ).
    { intros p1 IHp1.
      simpl.
      rewrite <- IHp1, claim4.
      split.
      - intros H H0.
        contradiction claim11.
        apply inconsistent_iff, (ContradictionI p1).
        + apply claim4...
        + apply H.
      - intros H.
        apply claim4, claim5.
        intros H0.
        apply claim4, (ContradictionI (NegationF p1)).
        + enough (caseNegationF_aux1 : MaximalConsistentSet hs |- ImplicationF p1 ContradictionF).
          { apply NegationI, (ImplicationE p1).
            - apply (extend_infers caseNegationF_aux1)...
            - apply ByAssumption...
          }
          apply claim4, claim6.
          tauto.
        + apply ByAssumption...
    }
    assert ( caseConjunctionF :
      forall p1 : formula,
      forall p2 : formula,
      (member p1 hs_hat <-> eval_formula (preimage AtomF hs_hat) p1) ->
      (member p2 hs_hat <-> eval_formula (preimage AtomF hs_hat) p2) ->
      (member (ConjunctionF p1 p2) hs_hat <-> eval_formula (preimage AtomF hs_hat) (ConjunctionF p1 p2))
    ).
    { intros p1 p2 IHp1 IHp2.
      simpl.
      rewrite <- IHp1, <- IHp2.
      split.
      - intros H.
        split.
        + apply claim4, (ConjunctionE1 p1 p2), claim4...
        + apply claim4, (ConjunctionE2 p1 p2), claim4...
      - intros [H H0].
        apply claim4, ConjunctionI; apply claim4...
    }
    assert ( caseDisjunctionF :
      forall p1 : formula,
      forall p2 : formula,
      (member p1 hs_hat <-> eval_formula (preimage AtomF hs_hat) p1) ->
      (member p2 hs_hat <-> eval_formula (preimage AtomF hs_hat) p2) ->
      (member (DisjunctionF p1 p2) hs_hat <-> eval_formula (preimage AtomF hs_hat) (DisjunctionF p1 p2))
    ).
    { intros p1 p2 IHp1 IHp2.
      simpl.
      rewrite <- IHp1, <- IHp2.
      split.
      - intros H.
        destruct (classic (hs_hat |- p1)) as [H_yes | H_no].
        + apply or_introl, claim4...
        + apply or_intror, claim4.
          apply (ImplicationE (NegationF p1)).
          { apply (DisjunctionE p1 p2 (ImplicationF (NegationF p1) p2)).
            - apply claim4...
            - apply (ImplicationI (NegationF p1) p2), (ContradictionE p2), (ContradictionI p1).
              + apply ByAssumption, in_insert_iff, or_intror...
              + apply ByAssumption...
            - apply ImplicationI, ByAssumption, in_insert_iff, or_intror...
          }
          { apply claim4, caseNegationF.
            - apply IHp1.
            - simpl.
              intros H0.
              assert (H1 := proj2 IHp1 H0).
              apply claim4 in H1.
              contradiction H_no.
          }
      - intros [H | H].
        + apply claim4, (DisjunctionI1 p1 p2), claim4...
        + apply claim4, (DisjunctionI2 p1 p2), claim4...
    }
    assert ( caseImplicationF :
      forall p1 : formula,
      forall p2 : formula,
      (member p1 hs_hat <-> eval_formula (preimage AtomF hs_hat) p1) ->
      (member p2 hs_hat <-> eval_formula (preimage AtomF hs_hat) p2) ->
      (member (ImplicationF p1 p2) hs_hat <-> eval_formula (preimage AtomF hs_hat) (ImplicationF p1 p2))
    ).
    { intros p1 p2 IHp1 IHp2.
      rewrite (claim6 p1 p2).
      simpl.
      tauto.
    }
    assert ( caseBiconditionalF :
      forall p1 : formula,
      forall p2 : formula,
      (member p1 hs_hat <-> eval_formula (preimage AtomF hs_hat) p1) ->
      (member p2 hs_hat <-> eval_formula (preimage AtomF hs_hat) p2) ->
      (member (BiconditionalF p1 p2) hs_hat <-> eval_formula (preimage AtomF hs_hat) (BiconditionalF p1 p2))
    ).
    { intros p1 p2 IHp1 IHp2.
      simpl.
      transitivity (member (ImplicationF p1 p2) hs_hat /\ member (ImplicationF p2 p1) hs_hat).
      { split.
        - intros H.
          split.
          { apply claim4, ImplicationI, (BiconditionalE1 p1 p2).
            - apply (@extend_infers hs_hat).
              + apply claim4...
              + apply lemma2.
            - apply ByAssumption... 
          }
          { apply claim4, ImplicationI, (BiconditionalE2 p1 p2).
            - apply (@extend_infers hs_hat).
              + apply claim4...
              + apply lemma2.
            - apply ByAssumption... 
          }
        - intros [H H0].
          apply claim4, (BiconditionalI p1 p2).
          { apply (ImplicationE p1 p2).
            - apply (@extend_infers hs_hat).
              + apply claim4...
              + apply lemma2.
            - apply ByAssumption...
          }
          { apply (ImplicationE p2 p1).
            - apply (@extend_infers hs_hat).
              + apply claim4...
              + apply lemma2.
            - apply ByAssumption...
          }
      }
      { split.
        - intros [H H0].
          apply caseImplicationF in H, H0...
        - intros [H H0].
          apply caseImplicationF in H, H0...
      }
    }
    unfold makeModelFromMaximalConsistentSet.
    induction p...
  Qed.

  Corollary the_propositional_completeness_theorem :
    forall hs : ensemble formula,
    forall c : formula,
    hs |= c ->
    hs |- c.
  Proof with try now firstorder.
    intros hs c H_entails.
    destruct (classic (hs |- c)) as [H_yes | H_no].
    - exact H_yes.
    - assert (claim1 : ~ insert (NegationF c) hs |- ContradictionF).
      { intros H_inconsistent.
        contradiction H_no.
        apply NegationE, H_inconsistent.
      }
      assert (claim2 : isFilter (MaximalConsistentSet (insert (NegationF c) hs))) by now apply theorem_of_1_2_14, lemma1_of_1_3_8.
      assert (claim3 := ModelExistsIfConsistent (insert (NegationF c) hs) claim1).
      destruct (theorem_of_1_3_10 (insert (NegationF c) hs)) as [claim4 [claim5 [claim6 [claim7 claim8]]]].
      apply (completeness_theorem_prototype hs c H_entails (makeModelFromMaximalConsistentSet (MaximalConsistentSet (insert (NegationF c) hs)))).
      + unfold equiconsistent in *.
        transitivity (inconsistent (MaximalConsistentSet (insert (NegationF c) hs)))...
      + transitivity (MaximalConsistentSet (insert (NegationF c) hs))...
      + apply (isFilter_ext_eq (MaximalConsistentSet (insert (NegationF c) hs)) claim2)...
  Qed.

End CompletenessOfPropositionLogic.
