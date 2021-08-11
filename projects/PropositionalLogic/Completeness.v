Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import DschingisKhan.classical.ExclusiveMiddle.
Require Import DschingisKhan.pure.CBA.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.
Require Import DschingisKhan.projects.PropositionalLogic.Basics.
Require Import DschingisKhan.projects.PropositionalLogic.Soundness.

Module CompletenessOfPL.

  Import ListNotations BasicSetoidTheory MyEnsemble BasicPosetTheory MyEnsembleNova CountableBooleanAlgebra SyntaxOfPL SemanticsOfPL InferenceRulesOfPL LindenbaumBooleanAlgebraOnPL SoundnessOfPL.

  Inductive TH : ensemble formula -> ensemble formula :=
  | in_Theory :
    forall hs : ensemble formula,
    forall c : formula,
    hs |- c ->
    member c (TH hs)
  .

  Local Hint Constructors TH : core.

  Local Instance formula_isCBA : @CountableBooleanAlgebra.isCBA formula formula_isSetoid :=
    LindenbaumBooleanAlgebra
  .

  Lemma lemma_1_of_1_3_8 :
    forall bs : ensemble formula,
    isFilter (TH bs).
  Proof with eauto with *.
    intros bs.
    split.
    { exists (ImplicationF ContradictionF ContradictionF).
      constructor.
      apply ImplicationI.
      apply ByAssumption...
    }
    split.
    { intros b1 b2 H H0.
      inversion H; subst.
      constructor.
      apply (cut_property b1).
      - apply H1.
      - apply (@extendInfers \left\{ b1 \right\} b2).
        apply (proj1 (leq_LBA b1 b2) H0).
        intros b.
        rewrite in_insert_iff, in_singleton_iff...
    }
    { intros b1 b2 b H H0 [H1 H2].
      inversion H; subst.
      inversion H0; subst.
      constructor.
      apply (cut_property (ConjunctionF b1 b2)).
      - apply ConjunctionI...
      - apply (@extendInfers \left\{ andB b1 b2 \right\} b)...
    }
  Qed.

  Lemma Cl_subset_TH :
    forall hs : ensemble formula,
    isSubsetOf (Cl hs) (TH hs).
  Proof with eauto with *.
    intros hs.
    enough ( claim1 :
      forall ps : list formula,
      (forall p : formula, In p ps -> member p hs) ->
      forall c : formula,
      andB (fold_right andB trueB ps) c == fold_right andB trueB ps ->
      (exists hs' : ensemble formula, isSubsetOf hs' hs /\ hs' |- c)
    ).
    { intros p.
      intro H.
      inversion H; subst.
      destruct (claim1 bs1 H0 p H1) as [hs' [H2 H3]].
      constructor.
      apply (extendInfers p H3)...
    }
    intros ps H c H0.
    assert (H1 : \left\{ fold_right andB trueB ps \right\} |- c) by apply leq_LBA, H0.
    destruct (proj1 (andBs_LBA ps hs H c) H1) as [hs' [H2 H3]].
    exists hs'.
    split...
    intros h H4.
    apply H.
    apply H2...
  Qed.

  Lemma infers_has_compactness :
    forall hs : ensemble formula,
    forall c : formula,
    hs |- c ->
    exists ps : list formula, (forall p : formula, In p ps -> member p hs) /\ (exists hs' : ensemble formula, (forall h : formula, In h ps <-> member h hs') /\ hs' |- c).
  Proof with eauto with *.
    intros hs c H.
    induction H.
    { exists [h].
      split.
      - intros p [H0 | []]; subst...
      - exists (\left\{ h \right\}).
        split.
        + intros p.
          split.
          * intros [H0 | []]; subst...
          * rewrite in_singleton_iff.
            simpl...
        + apply ByAssumption...
    }
    { destruct IHinfers1 as [ps1 [H1 [hs1' [H3 H5]]]].
      destruct IHinfers2 as [ps2 [H2 [hs2' [H4 H6]]]].
      exists (ps1 ++ ps2).
      split.
      - apply (in_append_implies ps1 ps2 hs H1 H2).
      - exists (union hs1' hs2').
        split.
        + apply (in_append_iff ps1 ps2 hs1' hs2' H3 H4).
        + apply (ContradictionI a).
          * apply (extendInfers a H5)...
          * apply (extendInfers (NegationF a) H6)...
    }
    { destruct IHinfers as [ps [H0 [hs' [H1 H2]]]].
      exists ps...
    }
    { destruct IHinfers as [ps [H0 [hs' [H1 H2]]]].
      exists (remove eq_formula_dec a ps).
      split.
      - apply in_remove_implies...
      - exists (delete a hs').
        split.
        + apply in_remove_iff_member_delete...
        + apply NegationI.
          apply (extendInfers ContradictionF H2).
          intros p H3.
          destruct (eq_formula_dec p a) as [H_yes | H_no].
          * subst...
          * apply in_insert_iff, or_intror, in_delete_iff...
    }
    { destruct IHinfers as [ps [H0 [hs' [H1 H2]]]].
      exists (remove eq_formula_dec (NegationF a) ps).
      split.
      - apply in_remove_implies...
      - exists (delete (NegationF a) hs').
        split.
        + intros h.
          apply (in_remove_iff_member_delete eq_formula_dec (NegationF a) ps hs' H1).
        + apply NegationE.
          apply (extendInfers ContradictionF H2).
          intros h H3.
          destruct (eq_formula_dec h (NegationF a)) as [H_yes | H_no].
          * subst...
          * apply in_insert_iff, or_intror, in_delete_iff...
    }
    { destruct IHinfers1 as [ps1 [H1 [hs1' [H3 H5]]]].
      destruct IHinfers2 as [ps2 [H2 [hs2' [H4 H6]]]].
      exists (ps1 ++ ps2).
      split.
      - apply (in_append_implies ps1 ps2 hs H1 H2).
      - exists (union hs1' hs2').
        split.
        + apply (in_append_iff ps1 ps2 hs1' hs2' H3 H4).
        + apply ConjunctionI.
          * apply (extendInfers a H5)...
          * apply (extendInfers b H6)...
    }
    { destruct IHinfers as [ps [H0 [hs' [H1 H2]]]].
      exists ps...
    }
    { destruct IHinfers as [ps [H0 [hs' [H1 H2]]]].
      exists ps...
    }
    { destruct IHinfers as [ps [H0 [hs' [H1 H2]]]].
      exists ps...
    }
    { destruct IHinfers as [ps [H0 [hs' [H1 H2]]]].
      exists ps...
    }
    { destruct IHinfers1 as [ps1 [H2 [hs1' [H5 H8]]]].
      destruct IHinfers2 as [ps2 [H3 [hs2' [H6 H9]]]].
      destruct IHinfers3 as [ps3 [H4 [hs3' [H7 H10]]]].
      exists (ps1 ++ (remove eq_formula_dec a ps2 ++ remove eq_formula_dec b ps3)).
      split.
      - apply in_append_implies...
        apply in_append_implies...
        apply in_remove_implies...
        apply in_remove_implies...
      - exists (union hs1' (union (delete a hs2') (delete b hs3'))).
        split.
        { apply in_append_iff...
          apply in_append_iff...
          apply in_remove_iff_member_delete...
          apply in_remove_iff_member_delete...
        }
        { apply (DisjunctionE a b c).
          - apply (extendInfers (DisjunctionF a b) H8)...
          - apply (extendInfers c H9).
            intros p H11.
            destruct (eq_formula_dec p a) as [H_yes | H_no].
            + subst...
            + apply in_insert_iff, or_intror, in_union_iff, or_intror, in_union_iff, or_introl, in_delete_iff...
          - apply (extendInfers c H10).
            intros p H11.
            destruct (eq_formula_dec p b) as [H_yes | H_no].
            + subst...
            + apply in_insert_iff, or_intror, in_union_iff, or_intror, in_union_iff, or_intror, in_delete_iff...
        }
    }
    { destruct IHinfers as [ps [H0 [hs' [H1 H2]]]].
      exists (remove eq_formula_dec a ps).
      split.
      - apply in_remove_implies...
      - exists (delete a hs').
        split.
        + apply in_remove_iff_member_delete...
        + apply ImplicationI.
          apply (extendInfers b H2).
          intros p H3.
          destruct (eq_formula_dec p a) as [H_yes | H_no].
          * subst...
          * apply in_insert_iff, or_intror, in_delete_iff...
    }
    { destruct IHinfers1 as [ps1 [H1 [hs1' [H3 H5]]]].
      destruct IHinfers2 as [ps2 [H2 [hs2' [H4 H6]]]].
      exists (ps1 ++ ps2).
      split.
      - apply (in_append_implies ps1 ps2 hs H1 H2).
      - exists (union hs1' hs2').
        split.
        + apply (in_append_iff ps1 ps2 hs1' hs2' H3 H4).
        + apply (ImplicationE a b).
          * apply (extendInfers (ImplicationF a b) H5)...
          * apply (extendInfers a H6)...
    }
    { destruct IHinfers1 as [ps1 [H1 [hs1' [H3 H5]]]].
      destruct IHinfers2 as [ps2 [H2 [hs2' [H4 H6]]]].
      exists (remove eq_formula_dec a ps1 ++ remove eq_formula_dec b ps2).
      split.
      - apply in_append_implies; apply in_remove_implies...
      - exists (union (delete a hs1') (delete b hs2')).
        split.
        + apply in_append_iff; apply in_remove_iff_member_delete...
        + apply BiconditionalI.
          { apply (extendInfers b H5).
            intros p H7.
            destruct (eq_formula_dec p a) as [H_yes | H_no].
            - subst...
            - apply in_insert_iff, or_intror, in_union_iff, or_introl, in_delete_iff...
          }
          { apply (extendInfers a H6).
            intros p H7.
            destruct (eq_formula_dec p b) as [H_yes | H_no].
            - subst...
            - apply in_insert_iff, or_intror, in_union_iff, or_intror, in_delete_iff...
          }
    }
    { destruct IHinfers1 as [ps1 [H1 [hs1' [H3 H5]]]].
      destruct IHinfers2 as [ps2 [H2 [hs2' [H4 H6]]]].
      exists (ps1 ++ ps2).
      split.
      - apply (in_append_implies ps1 ps2 hs H1 H2).
      - exists (union hs1' hs2').
        split.
        + apply (in_append_iff ps1 ps2 hs1' hs2' H3 H4).
        + apply (BiconditionalE1 a b).
          * apply (extendInfers (BiconditionalF a b) H5)...
          * apply (extendInfers a H6)...
    }
    { destruct IHinfers1 as [ps1 [H1 [hs1' [H3 H5]]]].
      destruct IHinfers2 as [ps2 [H2 [hs2' [H4 H6]]]].
      exists (ps1 ++ ps2).
      split.
      - apply (in_append_implies ps1 ps2 hs H1 H2).
      - exists (union hs1' hs2').
        split.
        + apply (in_append_iff ps1 ps2 hs1' hs2' H3 H4).
        + apply (BiconditionalE2 a b).
          * apply (extendInfers (BiconditionalF a b) H5)...
          * apply (extendInfers b H6)...
    }
  Qed.

(*

  Lemma TH_subset_Cl :
    forall hs : Ensemble Formula,
    isSubsetOf (TH hs) (Cl Formula hs).
  Proof.
    intros hs.
    intros c.
    intro.
    inversion H.
    subst.
    destruct (Infers_has_compactness hs c H0) as [ps].
    destruct H1.
    assert (Infers (singleton (fold_right andB trueB ps)) c).
      apply (proj2 (andBs_LBA ps hs H1 c) H2).
    apply (Closure Formula ps).
    apply H1.
    apply leq_LBA.
    apply H3.
  Qed.
  
  Lemma bound_exists :
    forall ps : list Formula,
    exists bound : nat,
    forall p : Formula,
    In p ps ->
    exists n : nat, enumerateFormula n = p /\ n < bound.
  Proof.
    intros ps.
    induction ps.
    - exists 0.
      simpl.
      tauto.
    - destruct (Formula_is_enumerable a) as [bound1].
      destruct IHps as [bound2].
      assert (bound1 >= bound2 \/ bound1 < bound2).
        lia.
      destruct H1.
      exists (S bound1).
      intros p.
      simpl.
      intro.
      destruct H2.
      exists bound1.
      constructor.
      subst.
      tauto.
      lia.
      destruct (H0 p H2) as [n].
      exists n.
      destruct H3.
      constructor.
      apply H3.
      lia.
      exists bound2.
      intros p.
      intro.
      simpl.
      inversion H2.
      exists bound1.
      subst.
      constructor.
      tauto.
      tauto.
      destruct (H0 p H3) as [n].
      destruct H4.
      exists n.
      tauto.
  Qed.
  
  Definition Filter (hs : Ensemble Formula) (n : nat) : Ensemble Formula :=
    improveFilter Formula (TH hs) n
  .
  
  Fixpoint AxmSet (hs : Ensemble Formula) (n : nat) : Ensemble Formula :=
    match n with
    | 0 => hs
    | S n' => union (AxmSet hs n') (Insert Formula (Filter hs n') n')
    end
  .
  
  Lemma inconsistent_property_1 :
    forall hs : Ensemble Formula,
    Infers hs ContradictionF <-> inconsistent Formula (Cl Formula hs).
  Proof.
    intros hs.
    constructor.
    intro.
    exists ContradictionF.
    constructor.
    assert (isSubsetOf (TH hs) (Cl Formula hs)).
      apply TH_subset_Cl.
    apply (H0 ContradictionF).
    apply InTheory.
    apply H.
    apply eqB_refl.
    intro.
    destruct H as [b'].
    destruct H.
    assert (member b' (TH hs)).
      apply (Cl_subset_TH hs b' H).
    inversion H1.
    subst.
    apply (cut_property hs b' ContradictionF).
    apply H2.
    destruct H0.
    apply (extendInfers (singleton b') ContradictionF H0).
    intros p.
    intro.
    apply UnionR.
    apply H4.
  Qed.
  
  Lemma equiconsistent_property_1 :
    forall hs1 : Ensemble Formula,
    forall hs2 : Ensemble Formula,
    isFilter Formula hs1 ->
    isFilter Formula hs2 ->
    equiconsistent Formula hs1 hs2 <-> (Infers hs1 ContradictionF <-> Infers hs2 ContradictionF).
  Proof.
    intros hs1 hs2 HHH1 HHH2.
    constructor.
    intro.
    constructor.
    intro.
    apply inconsistent_property_1.
    apply (inconsistent_subset Formula hs2).
    apply fact_3_of_1_2_8.
    apply H.
    apply (inconsistent_subset Formula (Cl Formula hs1)).
    apply fact_5_of_1_2_8.
    apply HHH1.
    apply inconsistent_property_1.
    apply H0.
    intro.
    apply inconsistent_property_1.
    apply (inconsistent_subset Formula hs1).
    apply fact_3_of_1_2_8.
    apply H.
    apply (inconsistent_subset Formula (Cl Formula hs2)).
    apply fact_5_of_1_2_8.
    apply HHH2.
    apply inconsistent_property_1.
    apply H0.
    intro.
    constructor.
    intro.
    apply (inconsistent_subset Formula (Cl Formula hs2)).
    apply fact_5_of_1_2_8.
    apply HHH2.
    apply inconsistent_property_1.
    apply H.
    apply inconsistent_property_1.
    apply (inconsistent_subset Formula hs1).
    apply fact_3_of_1_2_8.
    apply H0.
    intro.
    apply (inconsistent_subset Formula (Cl Formula hs1)).
    apply fact_5_of_1_2_8.
    apply HHH1.
    apply inconsistent_property_1.
    apply H.
    apply inconsistent_property_1.
    apply (inconsistent_subset Formula hs2).
    apply fact_3_of_1_2_8.
    apply H0.
  Qed.
  
  Lemma lemma_1_of_1_3_9 :
    forall hs : Ensemble Formula,
    forall n : nat,
    isSubsetOf (Filter hs n) (TH (AxmSet hs n)) /\ isSubsetOf (TH (AxmSet hs n)) (Filter hs n).
  Proof.
    intros hs n.
    induction n.
    - unfold Filter in *.
      simpl.
      unfold isSubsetOf.
      intuition.
    - destruct IHn.
      unfold Filter in *.
      simpl.
      constructor.
      * assert (isSubsetOf (Cl Formula (union (improveFilter Formula (TH hs) n) (Insert Formula (improveFilter Formula (TH hs) n) n))) (Cl Formula (TH (union (AxmSet hs n) (Insert Formula (Filter hs n) n))))).
          apply fact_4_of_1_2_8.
          intros b.
          intro.
          inversion H1.
          subst.
          assert (member b (TH (AxmSet hs n))).
            apply (H b H2).
          inversion H3.
          subst.
          apply InTheory.
          apply (extendInfers (AxmSet hs n) b H4).
          intros p.
          intro.
          apply UnionL.
          apply H5.
          subst.
          apply InTheory.
          apply ByAssumption.
          apply UnionR.
          apply H2.
        assert (isSubsetOf (Cl Formula (TH (union (AxmSet hs n) (Insert Formula (Filter hs n) n)))) (TH (union (AxmSet hs n) (Insert Formula (Filter hs n) n)))).
          apply fact_5_of_1_2_8.
          apply lemma_1_of_1_3_8.
        unfold isSubsetOf in *.
        intuition.
      * cut (isSubsetOf (Cl Formula (union (AxmSet hs n) (Insert Formula (Filter hs n) n))) (Cl Formula (union (improveFilter Formula (TH hs) n) (Insert Formula (improveFilter Formula (TH hs) n) n)))).
          intro.
          assert (isSubsetOf (TH (union (AxmSet hs n) (Insert Formula (Filter hs n) n))) (Cl Formula (union (AxmSet hs n) (Insert Formula (Filter hs n) n)))).
            apply TH_subset_Cl.
          unfold isSubsetOf in *.
          intuition.
        assert (isSubsetOf (Cl Formula (Cl Formula (union (improveFilter Formula (TH hs) n) (Insert Formula (improveFilter Formula (TH hs) n) n)))) (Cl Formula (union (improveFilter Formula (TH hs) n) (Insert Formula (improveFilter Formula (TH hs) n) n)))).
          apply fact_5_of_1_2_8.
          apply fact_1_of_1_2_8.
        cut (isSubsetOf (Cl Formula (union (AxmSet hs n) (Insert Formula (Filter hs n) n))) (Cl Formula (Cl Formula (union (improveFilter Formula (TH hs) n) (Insert Formula (improveFilter Formula (TH hs) n) n))))).
          unfold isSubsetOf in *.
          intuition.
        apply fact_4_of_1_2_8.
        intros b.
        intro.
        inversion H2.
        subst.
        apply (Closure Formula [b]).
        intros p.
        intro.
        inversion H4.
        subst.
        apply UnionL.
        apply (H0 p).
        apply InTheory.
        apply ByAssumption.
        apply H3.
        inversion H5.
        apply leq_LBA.
        simpl.
        apply (ConjunctionE1 _ b (ImplicationF ContradictionF ContradictionF)).
        apply ByAssumption.
        apply Singleton.
        subst.
        inversion H3.
        subst.
        apply (Closure Formula [enumB n]).
        intros p.
        intro.
        inversion H5.
        subst.
        apply UnionR.
        apply Insertion.
        apply H4.
        inversion H6.
        apply leq_LBA.
        simpl.
        apply (ConjunctionE1 _ (enumerateFormula n) (ImplicationF ContradictionF ContradictionF)).
        apply ByAssumption.
        apply Singleton.
  Qed.
  
  Lemma RequirementForCompleteness :
    forall hs : Ensemble Formula,
    forall c : Formula,
    Entails hs c ->
    forall v : Formula -> Prop,
    isStructure v ->
    equiconsistent Formula (TH (insert (NegationF c) hs)) v ->
    isSubsetOf (TH (insert (NegationF c) hs)) v ->
    isFilter Formula v ->
    Infers hs c.
  Proof.
    intros hs c.
    intro Entailment.
    intros v.
    intro IsStructure.
    intro Equiconsistent.
    intro Extensionality.
    intro IsFilter.
    apply NegationE.
    assert (inconsistent Formula (TH (insert (NegationF c) hs))).
      apply Equiconsistent.
      assert (inconsistent Formula (Cl Formula v)).
        apply inconsistent_property_1.
        apply (ContradictionI _ c).
        apply ByAssumption.
        apply Entailment.
        apply IsStructure.
        intros h.
        intro.
        apply Extensionality.
        apply InTheory.
        apply ByAssumption.
        apply UnionL.
        apply H.
        apply ByAssumption.
        apply Extensionality.
        apply InTheory.
        apply ByAssumption.
        apply UnionR.
        apply Singleton.
      apply (inconsistent_subset Formula (Cl Formula v) v).
      apply fact_5_of_1_2_8.
      apply IsFilter.
      apply H.
    assert (inconsistent Formula (Cl Formula (insert (NegationF c) hs))).
      apply (inconsistent_subset Formula (TH (insert (NegationF c) hs))).
      apply TH_subset_Cl.
      apply H.
    apply inconsistent_property_1.
    apply H0.
  Qed.
  
  Definition MaximalConsistentSet (bs : Ensemble Formula) : Ensemble Formula :=
    CompleteFilter Formula (TH bs)
  .
  
  Inductive FullAxmSet : Ensemble Formula -> Ensemble Formula :=
  | InFullAxmSet :
    forall n : nat,
    forall bs : Ensemble Formula,
    forall b : Formula,
    member b (AxmSet bs n) ->
    member b (FullAxmSet bs)
  .
  
  Lemma lemma_2_of_1_3_9 :
    forall bs : Ensemble Formula,
    isSubsetOf (MaximalConsistentSet bs) (TH (FullAxmSet bs)).
  Proof.
    intros bs.
    intros p.
    intro.
    inversion H.
    subst.
    assert (member p (TH (AxmSet bs n))).
      apply (proj1 (lemma_1_of_1_3_9 bs n) p H0).
    inversion H1.
    subst.
    apply InTheory.
    apply (extendInfers (AxmSet bs n) p H2).
    intros b.
    intro.
    apply (InFullAxmSet n).
    apply H3.
  Qed.
  
  Lemma lemma_3_of_1_3_9 :
    forall bs : Ensemble Formula,
    isSubsetOf (TH (FullAxmSet bs)) (MaximalConsistentSet bs).
  Proof.
    intros bs.
    cut (
      forall ps : list Formula,
      (forall p : Formula, In p ps -> member p (FullAxmSet bs)) ->
      exists m : nat,
      (forall p : Formula, In p ps -> member p (Filter bs m))
    ).
      intro.
      intros p.
      intro.
      inversion H0.
      subst.
      destruct (Infers_has_compactness (FullAxmSet bs) p H1) as [ps].
      destruct H2.
      destruct (H ps H2) as [m].
      apply (InCompleteFilter Formula m).
      assert (isFilter Formula (improveFilter Formula (TH bs) m)).
        apply lemma_1_of_1_2_11.
        apply lemma_1_of_1_3_8.
      inversion H5.
      destruct H7.
      apply (H7 (fold_right andB trueB ps) p).
      apply (fact_5_of_1_2_8 Formula (improveFilter Formula (TH bs) m) H5 (fold_right andB trueB ps)).
      apply (Closure Formula ps).
      apply H4.
      apply andB_idempotent.
      apply leq_LBA.
      apply andBs_Infers.
      apply H3.
    intros ps.
    induction ps.
    - intro.
      exists 0.
      simpl.
      tauto.
    - intro.
      assert (forall p : Formula, In p ps -> member p (FullAxmSet bs)).
        intros p.
        intro.
        apply H.
        simpl.
        tauto.
      assert (member a (FullAxmSet bs)).
        apply H.
        simpl.
        tauto.
      inversion H1.
      subst.
      assert (member a (Filter bs n)).
        apply (proj2 (lemma_1_of_1_3_9 bs n) a).
        apply InTheory.
        apply ByAssumption.
        apply H2.
      destruct (IHps H0) as [n'].
      assert (n >= n' \/ n < n').
        lia.
      destruct H5.
      exists n.
      intros p.
      simpl.
      intro.
      destruct H6.
      subst.
      apply H3.
      apply (lemma_1_of_1_2_12 Formula (TH bs) n' n H5 p (H4 p H6)).
      exists n'.
      simpl.
      intro.
      intro.
      destruct H6.
      assert (n <= n').
        lia.
      subst.
      apply (lemma_1_of_1_2_12 Formula (TH bs) n n' H7 p H3).
      apply (H4 p H6).
  Qed.
  
  Definition isMetaDN (bs : Ensemble Formula) : Prop :=
    forall p1 : Formula, (member (NegationF p1) bs -> member ContradictionF bs) -> member p1 bs
  .
  
  Definition isImplicationFaithful (bs : Ensemble Formula) : Prop :=
    forall p1 : Formula, forall p2 : Formula, member (ImplicationF p1 p2) bs <-> (member p1 bs -> member p2 bs)
  .
  
  Theorem theorem_1_3_10 :
    forall bs : Ensemble Formula,
    isSubsetOf (TH bs) (MaximalConsistentSet bs) /\ equiconsistent Formula (TH bs) (MaximalConsistentSet bs) /\ (forall p : Formula, member p (MaximalConsistentSet bs) <-> Infers (MaximalConsistentSet bs) p) /\ isMetaDN (MaximalConsistentSet bs) /\ isImplicationFaithful (MaximalConsistentSet bs).
  Proof.
    intros bs.
    constructor.
    apply theorem_1_2_14.
    apply lemma_1_of_1_3_8.
    constructor.
    apply lemma_3_of_1_2_13.
    apply lemma_1_of_1_3_8.
    assert (
      forall p : Formula,
      member p (MaximalConsistentSet bs) <-> Infers (MaximalConsistentSet bs) p
    ).
      intros p.
      constructor.
      intro.
      assert (member p (TH (MaximalConsistentSet bs))).
        apply Cl_subset_TH.
        apply fact_3_of_1_2_8.
        apply H.
      inversion H0.
      subst.
      apply H1.
      intro.
      apply (fact_5_of_1_2_8 Formula (MaximalConsistentSet bs)).
      apply theorem_1_2_14.
      apply lemma_1_of_1_3_8.
      apply TH_subset_Cl.
      apply InTheory.
      apply H.
    constructor.
    apply H.
    assert (isComplete Formula (MaximalConsistentSet bs)).
      apply theorem_1_2_14.
      apply lemma_1_of_1_3_8.
    assert (isMetaDN (MaximalConsistentSet bs)).
      intros p1.
      intro.
      apply (H0 p1).
      constructor.
      apply inconsistent_subset.
      assert (isSubsetOf (MaximalConsistentSet bs) (insert p1 (MaximalConsistentSet bs))).
        intros h.
        intro.
        apply UnionL.
        apply H2.
      assert (isSubsetOf (insert p1 (MaximalConsistentSet bs)) (Cl Formula (insert p1 (MaximalConsistentSet bs)))).
        apply fact_3_of_1_2_8.
      unfold isSubsetOf in *.
      intuition.
      intro.
      assert (Infers (insert p1 (MaximalConsistentSet bs)) ContradictionF).
        apply inconsistent_property_1.
        apply H2.
      exists ContradictionF.
      constructor.
      apply H1.
      apply H.
      apply NegationI.
      apply H3.
      apply eqB_refl.
    constructor.
    apply H1.
    intros p1 p2.
    constructor.
    intro.
    intro.
    apply H.
    apply (ImplicationE (MaximalConsistentSet bs) p1 p2).
    apply H.
    apply H2.
    apply H.
    apply H3.
    intro.
    apply H1.
    intro.
    apply H.
    assert (Infers (insert (ImplicationF p1 p2) (MaximalConsistentSet bs)) ContradictionF).
      apply (ContradictionI (insert (ImplicationF p1 p2) (MaximalConsistentSet bs)) (ImplicationF p1 p2)).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (extendInfers (MaximalConsistentSet bs) (NegationF (ImplicationF p1 p2))).
      apply H.
      apply H3.
      intros h.
      intro.
      apply UnionL.
      apply H4.
    assert (Infers (MaximalConsistentSet bs) (ConjunctionF p1 (NegationF p2))).
      apply (DisjunctionE _ p1 (NegationF p1)).
      apply (extendInfers empty (DisjunctionF p1 (NegationF p1)) (ExclusiveMiddle p1)).
      intros h.
      intro.
      inversion H5.
      apply (DisjunctionE _ p2 (NegationF p2)).
      apply (extendInfers empty (DisjunctionF p2 (NegationF p2)) (ExclusiveMiddle p2)).
      intros h.
      intro.
      inversion H5.
      apply ContradictionE.
      apply (cut_property _ (ImplicationF p1 p2)).
      apply ImplicationI.
      apply ByAssumption.
      apply UnionL.
      apply UnionR.
      apply Singleton.
      apply (extendInfers (insert (ImplicationF p1 p2) (MaximalConsistentSet bs)) ContradictionF H4).
      intros h.
      intro.
      inversion H5.
      subst.
      apply UnionL.
      apply UnionL.
      apply UnionL.
      apply H6.
      subst.
      apply UnionR.
      apply H6.
      apply ConjunctionI.
      apply ByAssumption.
      apply UnionL.
      apply UnionR.
      apply Singleton.
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply (DisjunctionE _ p2 (NegationF p2)).
      apply (extendInfers empty (DisjunctionF p2 (NegationF p2)) (ExclusiveMiddle p2)).
      intros h.
      intro.
      inversion H5.
      apply ContradictionE.
      apply (cut_property _ (ImplicationF p1 p2)).
      apply ImplicationI.
      apply ByAssumption.
      apply UnionL.
      apply UnionR.
      apply Singleton.
      apply (extendInfers (insert (ImplicationF p1 p2) (MaximalConsistentSet bs)) ContradictionF H4).
      intros h.
      intro.
      inversion H5.
      subst.
      apply UnionL.
      apply UnionL.
      apply UnionL.
      apply H6.
      subst.
      apply UnionR.
      apply H6.
      apply ContradictionE.
      apply (cut_property _ (ImplicationF p1 p2)).
      apply ImplicationI.
      apply ContradictionE.
      apply (ContradictionI _ p1).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply ByAssumption.
      apply UnionL.
      apply UnionL.
      apply UnionR.
      apply Singleton.
      apply (extendInfers (insert (ImplicationF p1 p2) (MaximalConsistentSet bs)) ContradictionF H4).
      intros h.
      intro.
      inversion H5.
      subst.
      apply UnionL.
      apply UnionL.
      apply UnionL.
      apply H6.
      subst.
      apply UnionR.
      apply H6.
    assert (Infers (MaximalConsistentSet bs) p1).
      apply (ConjunctionE1 _ p1 (NegationF p2)).
      apply H5.
    assert (Infers (MaximalConsistentSet bs) (NegationF p2)).
      apply (ConjunctionE2 _ p1 (NegationF p2)).
      apply H5.
    apply (ContradictionI _ p2).
    apply H.
    apply H2.
    apply H.
    apply H6.
    apply H7.
  Qed.
  
  Parameter exclusive_middle : forall P : Prop, P \/ ~ P.
  
  Lemma ModelExistsIfConsistent :
    forall bs : Ensemble Formula,
    ~ Infers bs ContradictionF ->
    isStructure (MaximalConsistentSet bs).
  Proof.
    intros bs.
    intro.
    assert (forall p : Formula, satisfies (MaximalConsistentSet bs) p <-> Infers (MaximalConsistentSet bs) p).
      apply theorem_1_3_10.
    assert (Infers (MaximalConsistentSet bs) ContradictionF <-> inconsistent Formula (MaximalConsistentSet bs)).
      assert (inconsistent Formula (MaximalConsistentSet bs) <-> inconsistent Formula (Cl Formula (MaximalConsistentSet bs))).
        apply equiconsistent_property_1.
        apply theorem_1_2_14.
        apply lemma_1_of_1_3_8.
        apply fact_1_of_1_2_8.
      constructor.
      intro.
      apply (extendInfers (MaximalConsistentSet bs) ContradictionF H1).
      apply fact_3_of_1_2_8.
      intro.
      apply (extendInfers (Cl Formula (MaximalConsistentSet bs)) ContradictionF H1).
      apply fact_5_of_1_2_8.
      apply theorem_1_2_14.
      apply lemma_1_of_1_3_8.
      assert (Infers (MaximalConsistentSet bs) ContradictionF <-> inconsistent Formula (Cl Formula (MaximalConsistentSet bs))).
        apply inconsistent_property_1.
      intuition.
    assert (~ inconsistent Formula (MaximalConsistentSet bs)).
      intro.
      apply H.
      assert (inconsistent Formula (TH bs)).
        apply lemma_3_of_1_2_13.
        apply lemma_1_of_1_3_8.
        apply H2.
      assert (Infers (TH bs) ContradictionF).
        apply inconsistent_property_1.
        apply (inconsistent_subset Formula (TH bs) (Cl Formula (TH bs))).
        apply fact_3_of_1_2_8.
        apply H3.
      assert (member ContradictionF (TH (TH bs))).
        apply InTheory.
        apply H4.
      assert (member ContradictionF (TH bs)).
        apply (fact_5_of_1_2_8 Formula (TH bs)).
        apply lemma_1_of_1_3_8.
        apply TH_subset_Cl.
        apply H5.
      inversion H6.
      subst.
      apply H7.
      assert (isMetaDN (MaximalConsistentSet bs) /\ isImplicationFaithful (MaximalConsistentSet bs)).
        apply theorem_1_3_10.
    destruct H3.
    constructor.
    constructor.
    intro.
    apply H2.
    apply H1.
    apply H0.
    apply H5.
    tauto.
    constructor.
    intros p1.
    constructor.
    intro.
    intro.
    apply H2.
    apply H1.
    apply (ContradictionI _ p1).
    apply H0.
    apply H6.
    apply H0.
    apply H5.
    intro.
    apply H3.
    intro.
    contradiction H5.
    apply H0.
    apply NegationE.
    apply (ContradictionI _ (NegationF p1)).
    apply ByAssumption.
    apply UnionR.
    apply Singleton.
    apply (extendInfers (MaximalConsistentSet bs)).
    apply H0.
    apply H6.
    intros p.
    intro.
    apply UnionL.
    apply H7.
    constructor.
    intros p1 p2.
    constructor.
    intro.
    constructor.
    apply H0.
    apply (ConjunctionE1 _ p1 p2).
    apply H0.
    apply H5.
    apply H0.
    apply (ConjunctionE2 _ p1 p2).
    apply H0.
    apply H5.
    intro.
    destruct H5.
    apply H0.
    apply ConjunctionI.
    apply H0.
    apply H5.
    apply H0.
    apply H6.
    constructor.
    intros p1 p2.
    constructor.
    intro.
    destruct (exclusive_middle (satisfies (MaximalConsistentSet bs) p1)).
    apply or_introl.
    apply H6.
    apply or_intror.
    assert (Infers (MaximalConsistentSet bs) (NegationF p1)).
      apply H0.
      apply H3.
      intro.
      contradiction H6.
      apply H0.
      apply NegationE.
      apply (ContradictionI _ (NegationF p1)).
      apply ByAssumption.
      apply UnionR.
      apply Singleton.
      apply ByAssumption.
      apply UnionL.
      apply H7.
    apply H0.
    apply (DisjunctionE _ p1 p2).
    apply H0.
    apply H5.
    apply ContradictionE.
    apply (ContradictionI _ p1).
    apply ByAssumption.
    apply UnionR.
    apply Singleton.
    apply ByAssumption.
    apply UnionL.
    apply H0.
    apply H7.
    apply ByAssumption.
    apply UnionR.
    apply Singleton.
    intro.
    destruct H5.
    apply H0.
    apply DisjunctionI1.
    apply H0.
    apply H5.
    apply H0.
    apply DisjunctionI2.
    apply H0.
    apply H5.
    constructor.
    intros p1 p2.
    constructor.
    apply H4.
    apply H4.
    constructor.
    intros p1 p2.
    constructor.
    intro.
    constructor.
    apply H4.
    apply H0.
    apply ImplicationI.
    apply (BiconditionalE1 _ p1 p2).
    apply ByAssumption.
    apply UnionL.
    apply H5.
    apply ByAssumption.
    apply UnionR.
    apply Singleton.
    apply H4.
    apply H0.
    apply ImplicationI.
    apply (BiconditionalE2 _ p1 p2).
    apply ByAssumption.
    apply UnionL.
    apply H5.
    apply ByAssumption.
    apply UnionR.
    apply Singleton.
    intro.
    assert (satisfies (MaximalConsistentSet bs) (ImplicationF p1 p2)).
      apply H4.
      apply H5.
    assert (satisfies (MaximalConsistentSet bs) (ImplicationF p2 p1)).
      apply H4.
      apply H5.
    apply H0.
    apply BiconditionalI.
    apply (ImplicationE _ p1 p2).
    apply ByAssumption.
    apply UnionL.
    apply H6.
    apply ByAssumption.
    apply UnionR.
    apply Singleton.
    apply (ImplicationE _ p2 p1).
    apply ByAssumption.
    apply UnionL.
    apply H7.
    apply ByAssumption.
    apply UnionR.
    apply Singleton.
    intros p1.
    intro.
    apply H3.
    intro.
    apply H0.
    apply (ContradictionI _ (NegationF p1)).
    apply ByAssumption.
    apply H6.
    apply ByAssumption.
    apply H5.
  Qed.
  
  Corollary Completeness :
    forall hs : Ensemble Formula,
    forall c : Formula,
    Entails hs c ->
    Infers hs c.
  Proof.
    intros hs c.
    intro.
    destruct (exclusive_middle (Infers hs c)).
    apply H0.
    apply (RequirementForCompleteness hs c H (MaximalConsistentSet (insert (NegationF c) hs))).
    apply ModelExistsIfConsistent.
    intro.
    apply H0.
    apply NegationE.
    apply H1.
    apply lemma_3_of_1_2_13.
    apply lemma_1_of_1_3_8.
    apply theorem_1_2_14.
    apply lemma_1_of_1_3_8.
    apply theorem_1_2_14.
    apply lemma_1_of_1_3_8.
  Qed.

*)

End CompletenessOfPL.
