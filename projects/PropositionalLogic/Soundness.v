Require Import DschingisKhan.classical.ExclusiveMiddle.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.
Require Import DschingisKhan.projects.PropositionalLogic.Basics.

Module SoundnessOfPL.

  Import MyEnsemble MyEnsembleNova ClassicalLogic SyntaxOfPL SemanticsOfPL InferenceRulesOfPL.

  Lemma ByAssumption_preserves {hs : ensemble formula} :
    forall a : formula,
    member a hs ->
    hs |= a.
  Proof with eauto with *.
    intros c H.
    apply (@extendEntails \left\{ c \right\} c)...
  Qed.

  Lemma ContradictionI_preserves {hs : ensemble formula} :
    forall a : formula,
    hs |= a ->
    hs |= (NegationF a) ->
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
    assert (claim1 : forall h : formula, h \in insert a hs -> satifisfies v h).
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
    assert (claim1 : forall h : formula, h \in insert (NegationF a) hs -> satifisfies v h).
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
    hs |= (ConjunctionF a b).
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
    - assert (claim1 : forall h : formula, h \in insert a hs -> satifisfies v h).
      { intros h.
        rewrite in_insert_iff.
        intros [H5 | H5]; constructor.
        - rewrite H5...
        - assert (H6 := H2 h H5).
          inversion H6; subst...
      }
      assert (H5 := H0 v claim1).
      inversion H5; subst...
    - assert (claim1 : forall h : formula, h \in insert b hs -> satifisfies v h).
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
    assert (claim1 : forall h : formula, h \in insert a hs -> satifisfies v h).
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
      assert (claim1 : forall h : formula, h \in insert a hs -> satifisfies v h).
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
      assert (claim1 : forall h : formula, h \in insert b hs -> satifisfies v h).
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

  Theorem Soundness (hs : ensemble formula) (c : formula) (_infer : hs |- c) :
    hs |= c.
  Proof with firstorder.
    induction _infer.
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

End SoundnessOfPL.
