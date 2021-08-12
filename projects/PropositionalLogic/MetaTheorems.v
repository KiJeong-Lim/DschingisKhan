Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import DschingisKhan.classical.ExclusiveMiddle.
Require Import DschingisKhan.pure.CBA.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.
Require Import DschingisKhan.projects.PropositionalLogic.Basics.

Module PropertiesOfPropostionalLogic.

  Import ListNotations BasicSetoidTheory MyEnsemble BasicPosetTheory MyEnsembleNova CountableBooleanAlgebra SyntaxOfPL SemanticsOfPL InferenceRulesOfPL LindenbaumBooleanAlgebraOnPL.

  Inductive TH : ensemble formula -> ensemble formula :=
  | in_Theory :
    forall hs : ensemble formula,
    forall c : formula,
    hs |- c ->
    member c (TH hs)
  .

  Local Hint Constructors TH : core.

  Local Instance formula_isCBA : @isCBA formula formula_isSetoid :=
    LindenbaumBooleanAlgebra
  .

  Lemma lemma1_of_1_3_8 :
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

  Local Hint Resolve lemma1_of_1_3_8 : core.

  Lemma Cl_isSubsetOf_TH :
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

  Local Hint Resolve Cl_isSubsetOf_TH : core.

  Lemma infers_has_compactness :
    forall hs : ensemble formula,
    forall c : formula,
    hs |- c ->
    exists ps : list formula, (forall p : formula, In p ps -> member p hs) /\ (exists hs' : ensemble formula, (forall h : formula, In h ps <-> member h hs') /\ hs' |- c).
  Proof with eauto with *.
    intros hs c H.
    induction H.
    { exists (cons h nil).
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

  Lemma TH_isSubsetOf_Cl :
    forall hs : ensemble formula,
    isSubsetOf (TH hs) (Cl hs).
  Proof with eauto with *.
    intros hs c H.
    inversion H; subst.
    destruct (infers_has_compactness hs c H0) as [ps [H1 H2]].
    assert (claim1 := proj2 (andBs_LBA ps hs H1 c) H2).
    exists ps.
    - exact H1.
    - apply leq_LBA...
  Qed.

  Lemma bound_exists :
    forall ps : list formula,
    exists bound : nat,
    forall p : formula,
    In p ps ->
    exists n : nat, enum_formula n = p /\ n < bound.
  Proof with lia || eauto with *.
    induction ps as [| p ps [bound2 H]]; simpl.
    - exists 0...
    - destruct (formula_is_enumerable p) as [bound1 H0].
      destruct (le_lt_dec bound1 bound2) as [Hle | Hlt].
      + exists (S bound2).
        intros h [H1 | H1].
        * subst...
        * destruct (H h H1) as [n [H2 H3]].
          exists n...
      + exists (S bound1).
        intros h [H1 | H1].
        * subst...
        * destruct (H h H1) as [n [H2 H3]].
          exists n...
  Qed.

  Definition Filter : ensemble formula -> nat -> ensemble formula :=
    fun hs : ensemble formula =>
    fun n : nat =>
    improveFilter (TH hs) n
  .

  Definition AxmSet : ensemble formula -> nat -> ensemble formula :=
    fun hs : ensemble formula =>
    fix AxmSet_fix (n : nat) {struct n} : ensemble formula :=
    match n with
    | O => hs
    | S n' => union (AxmSet_fix n') (insertion (Filter hs n') n')
    end
  .

  Lemma property1_of_inconsistent :
    forall hs : ensemble formula,
    hs |- ContradictionF <-> inconsistent (Cl hs).
  Proof with eauto with *.
    intros hs.
    split.
    - intros H.
      exists ContradictionF.
      split...
      apply TH_isSubsetOf_Cl...
    - intros [b' [H [H0 H1]]].
      assert (claim1 : member b' (TH hs)) by now apply (Cl_isSubsetOf_TH hs b' H).
      inversion claim1; subst.
      apply (cut_property b' ContradictionF).
      + exact H2.
      + apply (extendInfers ContradictionF H0)...
  Qed.

  Local Hint Resolve fact1_of_1_2_8 fact2_of_1_2_8 fact3_of_1_2_8 fact4_of_1_2_8 fact5_of_1_2_8 lemma1_of_1_2_11 inconsistent_isSubsetOf property1_of_inconsistent : core.

  Lemma property1_of_equiconsistent :
    forall hs1 : ensemble formula,
    forall hs2 : ensemble formula,
    isFilter hs1 ->
    isFilter hs2 ->
    equiconsistent hs1 hs2 <-> (hs1 |- ContradictionF <-> hs2 |- ContradictionF).
  Proof with eauto with *.
    intros hs1 hs2 HHH1 HHH2.
    split.
    - intros H.
      split.
      + intros H0.
        apply property1_of_inconsistent.
        apply (inconsistent_isSubsetOf hs2)...
        apply H...
        apply (inconsistent_isSubsetOf (Cl hs1))...
        apply property1_of_inconsistent...
      + intros H0.
        apply property1_of_inconsistent.
        apply (inconsistent_isSubsetOf hs1)...
        apply H...
        apply (inconsistent_isSubsetOf (Cl hs2))...
        apply property1_of_inconsistent...
    - intros H.
      split.
      + intros H0.
        apply (inconsistent_isSubsetOf (Cl hs2))...
        apply property1_of_inconsistent, H, property1_of_inconsistent...
      + intros H0.
        apply (inconsistent_isSubsetOf (Cl hs1))...
        apply property1_of_inconsistent, H, property1_of_inconsistent...
  Qed.

  Lemma lemma1_of_1_3_9 :
    forall n : nat,
    forall hs : ensemble formula,
    isSubsetOf (Filter hs n) (TH (AxmSet hs n)) /\ isSubsetOf (TH (AxmSet hs n)) (Filter hs n).
  Proof with eauto with *.
    unfold Filter.
    induction n as [| n IH]; simpl.
    - intros hs...
    - intros hs.
      destruct (IH hs) as [H H0].
      assert (claim1 : isSubsetOf (Cl (union (improveFilter (TH hs) n) (insertion (improveFilter (TH hs) n) n))) (Cl (TH (union (AxmSet hs n) (insertion (Filter hs n) n))))).
      { apply fact4_of_1_2_8.
        intros b.
        rewrite in_union_iff.
        intro H1.
        inversion H1; subst.
        - assert (H3 := H b H2).
          inversion H3; subst.
          constructor.
          apply (extendInfers b H4).
          intros p H5.
          apply in_union_iff, or_introl...
        - constructor.
          apply ByAssumption, in_union_iff, or_intror...
      }
      assert (claim2 : isSubsetOf (Cl (TH (union (AxmSet hs n) (insertion (Filter hs n) n)))) (TH (union (AxmSet hs n) (insertion (Filter hs n) n)))) by apply fact5_of_1_2_8, lemma1_of_1_3_8.
      assert (claim3 : isSubsetOf (TH (union (AxmSet hs n) (insertion (Filter hs n) n))) (Cl (union (AxmSet hs n) (insertion (Filter hs n) n)))) by apply TH_isSubsetOf_Cl.
      assert (claim4 : isSubsetOf (Cl (Cl (union (improveFilter (TH hs) n) (insertion (improveFilter (TH hs) n) n)))) (Cl (union (improveFilter (TH hs) n) (insertion (improveFilter (TH hs) n) n)))) by apply fact5_of_1_2_8, fact1_of_1_2_8.
      assert (claim5 : isSubsetOf (Cl (union (AxmSet hs n) (insertion (Filter hs n) n))) (Cl (Cl (union (improveFilter (TH hs) n) (insertion (improveFilter (TH hs) n) n))))).
      { transitivity (Cl (union (improveFilter (TH hs) n) (insertion (improveFilter (TH hs) n) n)))...
        apply fact4_of_1_2_8.
        intros b.
        do 2 rewrite in_union_iff.
        intros H1.
        inversion H1; subst...
      }
      split...
  Qed.

  Lemma completeness_theorem_prototype :
    forall hs : ensemble formula,
    forall c : formula,
    hs |= c ->
    forall E : env,
    equiconsistent (TH (insert (NegationF c) hs)) (eval_formula E) ->
    isSubsetOf (TH (insert (NegationF c) hs)) (eval_formula E) ->
    isFilter (eval_formula E) ->
    hs |- c.
  Proof with eauto with *.
    intros hs c H_entail E.
    set (v := eval_formula E).
    intros H_equiconsistent H_incl H_isFilter.
    assert (claim1 : inconsistent (TH (insert (NegationF c) hs))).
    { apply H_equiconsistent.
      enough (claim1_aux1 : inconsistent (Cl v))...
      apply property1_of_inconsistent.
      apply (ContradictionI c).
      - apply ByAssumption.
        enough (claim1_aux2 : satisfies E c) by now inversion claim1_aux2; subst.
        apply H_entail.
        intros h H.
        constructor.
        apply H_incl.
        constructor.
        apply ByAssumption, in_insert_iff...
      - apply ByAssumption.
        apply H_incl.
        constructor.
        apply ByAssumption, in_insert_iff...
    }
    assert (claim2 : inconsistent (Cl (insert (NegationF c) hs))).
    { apply (inconsistent_isSubsetOf (TH (insert (NegationF c) hs)))...
      apply TH_isSubsetOf_Cl.
    }
    apply NegationE, property1_of_inconsistent...
  Qed.

  Definition MaximalConsistentSet : ensemble formula -> ensemble formula :=
    fun bs : ensemble formula =>
    CompleteFilter (TH bs)
  .

  Inductive FullAxmSet : ensemble formula -> ensemble formula :=
  | InFullAxmSet :
    forall n : nat,
    forall bs : ensemble formula,
    forall b : formula,
    member b (AxmSet bs n) ->
    member b (FullAxmSet bs)
  .

  Local Hint Constructors FullAxmSet : core.

  Lemma lemma2_of_1_3_9 :
    forall bs : ensemble formula,
    isSubsetOf (MaximalConsistentSet bs) (TH (FullAxmSet bs)).
  Proof with eauto with *.
    intros bs p H.
    inversion H; subst.
    assert (H1 := proj1 (lemma1_of_1_3_9 n bs) p H0).
    inversion H1; subst.
    constructor.
    apply (extendInfers p H2)...
  Qed.

  Lemma lemma3_of_1_3_9_aux1 :
    forall ps : list formula,
    forall bs : ensemble formula,
    (forall p : formula, In p ps -> member p (FullAxmSet bs)) ->
    exists m : nat, (forall p : formula, In p ps -> member p (Filter bs m)).
  Proof with eauto with *.
    induction ps as [| p ps IH]; simpl.
    - intros bs H.
      exists 0...
    - intros bs H.
      assert (claim1 : forall h : formula, In h ps -> member h (FullAxmSet bs)) by firstorder.
      assert (claim2 : member p (FullAxmSet bs)) by firstorder.
      inversion claim2; subst.
      assert (claim3 : member p (Filter bs n)).
      { apply (proj2 (lemma1_of_1_3_9 n bs) p).
        constructor.
        apply ByAssumption...
      }
      destruct (IH bs claim1) as [n' H1].
      destruct (le_lt_dec n' n) as [Hle | Hlt].
      + exists n.
        intros h [H2 | H2].
        * subst...
        * apply (lemma1_of_1_2_12  n' n Hle (TH bs))...
      + exists n'.
        intros h [H2 | H2]; subst.
        * assert (H3 : n <= n') by lia.
          apply (lemma1_of_1_2_12 n n' H3 (TH bs))...
        * apply H1...
  Qed.

  Lemma lemma3_of_1_3_9 :
    forall bs : ensemble formula,
    isSubsetOf (TH (FullAxmSet bs)) (MaximalConsistentSet bs).
  Proof with eauto with *.
    intros bs p H.
    inversion H; subst.
    destruct (infers_has_compactness (FullAxmSet bs) p H0) as [ps [H1 [hs' [H2 H3]]]].
    destruct (lemma3_of_1_3_9_aux1 ps bs H1) as [m H4].
    assert (H5 : isFilter (improveFilter (TH bs) m)) by apply lemma1_of_1_2_11, lemma1_of_1_3_8.
    assert (H6 := proj1 H5).
    destruct (proj2 H5) as [H7 H8].
    exists m.
    apply (H7 (fold_right andB trueB ps) p).
    - apply fact5_of_1_2_8.
      + apply H5.
      + exists ps...
    - apply leq_LBA, (andBs_LBA ps hs')...
      firstorder.
  Qed.

  Definition isMetaDN : ensemble formula -> Prop :=
    fun bs : ensemble formula =>
    forall p1 : formula,
    (member (NegationF p1) bs -> member ContradictionF bs) ->
    member p1 bs
  .

  Definition isImplicationFaithful : ensemble formula -> Prop :=
    fun bs : ensemble formula =>
    forall p1 : formula,
    forall p2 : formula,
    member (ImplicationF p1 p2) bs <-> (member p1 bs -> member p2 bs)
  .

  Lemma theorem_of_1_3_10_aux1 (bs : ensemble formula) :
    isSubsetOf (TH bs) (MaximalConsistentSet bs).
  Proof with eauto with *.
    apply theorem_of_1_2_14...
  Qed.

  Lemma theorem_of_1_3_10_aux2 (bs : ensemble formula) :
    equiconsistent (TH bs) (MaximalConsistentSet bs).
  Proof with eauto with *.
    apply lemma3_of_1_2_13...
  Qed.

  Lemma theorem_of_1_3_10_aux3 (bs : ensemble formula) :
    forall p : formula,
    member p (MaximalConsistentSet bs) <-> MaximalConsistentSet bs |- p.
  Proof with eauto with *.
    intros p.
    split.
    - intros H.
      assert (claim1 : member p (TH (MaximalConsistentSet bs))) by now apply Cl_isSubsetOf_TH, fact3_of_1_2_8.
      inversion claim1; subst...
    - intros H.
      apply fact5_of_1_2_8.
      + apply theorem_of_1_2_14...
      + apply TH_isSubsetOf_Cl...
  Qed.

  Theorem theorem_of_1_3_10 :
    forall bs : ensemble formula,
    isSubsetOf (TH bs) (MaximalConsistentSet bs) /\ equiconsistent (TH bs) (MaximalConsistentSet bs) /\ (forall p : formula, member p (MaximalConsistentSet bs) <-> MaximalConsistentSet bs |- p) /\ isMetaDN (MaximalConsistentSet bs) /\ isImplicationFaithful (MaximalConsistentSet bs).
  Proof with eauto with *.
    assert (lemma1 := @isSubsetOf_singleton formula).
    assert (lemma2 : forall hs : ensemble formula, forall h : formula, isSubsetOf hs (insert h hs)).
    { intros hs h b.
      rewrite in_insert_iff...
    }
    assert (lemma3 := @isSubsetOf_empty formula).
    assert (lemma4 : forall hs : ensemble formula, forall h : formula, member h (insert h hs)).
    { intros hs h.
      apply in_insert_iff...
    }
    intros bs.
    assert (claim1 := theorem_of_1_3_10_aux1 bs).
    assert (claim2 := theorem_of_1_3_10_aux2 bs).
    assert (claim3 := theorem_of_1_3_10_aux3 bs).
    assert (claim4 : isComplete (MaximalConsistentSet bs)) by apply theorem_of_1_2_14, lemma1_of_1_3_8.
    assert (claim5 : isMetaDN (MaximalConsistentSet bs)).
    { intros p1 H.
      apply (claim4 p1).
      split.
      - apply inconsistent_isSubsetOf.
        transitivity (insert p1 (MaximalConsistentSet bs))...
      - intros H0.
        assert (claim5_aux1 : insert p1 (MaximalConsistentSet bs) |- ContradictionF) by now apply property1_of_inconsistent.
        exists ContradictionF.
        split.
        + apply H, claim3, NegationI...
        + reflexivity.
    }
    assert (claim6 : isImplicationFaithful (MaximalConsistentSet bs)).
    { intros p1 p2.
      split.
      - intros H H0.
        apply claim3.
        apply (ImplicationE p1 p2).
        + apply claim3...
        + apply claim3...
      - intros H.
        apply claim5.
        intros H0.
        apply claim3.
        assert (claim6_aux1 : insert (ImplicationF p1 p2) (MaximalConsistentSet bs) |- ContradictionF).
        { apply (ContradictionI (ImplicationF p1 p2)).
          - apply ByAssumption, in_insert_iff, or_introl...
          - apply (@extendInfers (MaximalConsistentSet bs) (NegationF (ImplicationF p1 p2))).
            + apply claim3...
            + apply lemma2.
        }
        assert (claim6_aux2 : MaximalConsistentSet bs |- ConjunctionF p1 (NegationF p2)).
        { apply (DisjunctionE p1 (NegationF p1)).
          - apply (extendInfers (DisjunctionF p1 (NegationF p1)) (Law_of_Exclusive_Middle p1))...
          - apply (DisjunctionE p2 (NegationF p2)).
            + apply (extendInfers (DisjunctionF p2 (NegationF p2)) (Law_of_Exclusive_Middle p2))...
            + apply ContradictionE.
              apply (cut_property (ImplicationF p1 p2)).
              * apply ImplicationI.
                apply ByAssumption.
                apply in_insert_iff, or_intror, in_insert_iff, or_introl...
              * apply (extendInfers ContradictionF claim6_aux1).
                apply isSubsetOf_insert.
                transitivity (insert p1 (MaximalConsistentSet bs))...
            + apply ConjunctionI.
              { apply ByAssumption.
                apply in_insert_iff, or_intror, in_insert_iff, or_introl...
              }
              { apply (DisjunctionE p2 (NegationF p2)).
                - apply (extendInfers (DisjunctionF p2 (NegationF p2)) (Law_of_Exclusive_Middle p2))...
                - apply ContradictionE.
                  apply (cut_property (ImplicationF p1 p2)).
                  + apply ImplicationI.
                    apply ByAssumption.
                    apply in_insert_iff, or_intror, in_insert_iff, or_introl...
                  + apply (extendInfers ContradictionF claim6_aux1).
                    apply isSubsetOf_insert.
                    transitivity (insert (NegationF p2) (insert p1 (MaximalConsistentSet bs))).
                    * transitivity (insert p1 (MaximalConsistentSet bs))...
                    * apply lemma2.
                - apply ByAssumption...
              }
          - apply ContradictionE.
            apply (cut_property (ImplicationF p1 p2)).
            + apply ImplicationI.
              apply ContradictionE.
              apply (ContradictionI p1).
              * apply ByAssumption...
              * apply ByAssumption.
                apply in_insert_iff, or_intror...
            + apply (extendInfers ContradictionF claim6_aux1).
              apply isSubsetOf_insert...
        }
      assert (claim6_aux3 : MaximalConsistentSet bs |- p1) by now apply (ConjunctionE1 p1 (NegationF p2)).
      assert (claim6_aux4 : MaximalConsistentSet bs |- NegationF p2) by now apply (ConjunctionE2 p1 (NegationF p2)).
      apply (ContradictionI p2).
      + apply claim3, H, claim3...
      + apply claim6_aux4.
    }
    tauto.
  Qed.

End PropertiesOfPropostionalLogic.

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

Module CompletenessOfPL.

  Import ListNotations BasicSetoidTheory MyEnsemble BasicPosetTheory MyEnsembleNova CountableBooleanAlgebra ClassicalLogic SyntaxOfPL SemanticsOfPL InferenceRulesOfPL LindenbaumBooleanAlgebraOnPL PropertiesOfPropostionalLogic SoundnessOfPL.

  Definition makeEnv : ensemble formula -> env :=
    preimage AtomF
  .

  Parameter ModelExistsIfConsistent : forall hs : ensemble formula, ~ hs |- ContradictionF -> MaximalConsistentSet hs == eval_formula (makeEnv (MaximalConsistentSet hs)).

  Corollary Completeness :
    forall hs : ensemble formula,
    forall c : formula,
    hs |= c ->
    hs |- c.
  Proof with try now firstorder.
    intros hs c H_entail.
    destruct (classic (hs |- c)) as [H_yes | H_no].
    - apply H_yes.
    - assert (claim1 : ~ insert (NegationF c) hs |- ContradictionF).
      { intros H_impossible.
        apply H_no, NegationE...
      }
      assert (claim2 : isFilter (MaximalConsistentSet (insert (NegationF c) hs))) by apply theorem_of_1_2_14, lemma1_of_1_3_8.
      assert (H_eq := ModelExistsIfConsistent (insert (NegationF c) hs) claim1).
      apply (completeness_theorem_prototype hs c H_entail (makeEnv (MaximalConsistentSet (insert (NegationF c) hs)))).
      + unfold equiconsistent.
        transitivity (inconsistent (MaximalConsistentSet (insert (NegationF c) hs))).
        * apply theorem_of_1_3_10.
        * split; apply inconsistent_isSubsetOf...
      + transitivity (MaximalConsistentSet (insert (NegationF c) hs)).
        * apply theorem_of_1_3_10.
        * firstorder.
      + apply (isFilter_ext_eq (MaximalConsistentSet (insert (NegationF c) hs)) claim2)...
  Qed.

End CompletenessOfPL.
