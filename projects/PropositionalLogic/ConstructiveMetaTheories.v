Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import DschingisKhan.pure.CBA.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.
Require Import DschingisKhan.projects.PropositionalLogic.Basics.

Module LindenbaumBooleanAlgebraOnPropositionLogic. (* Reference: "Constructive Completeness Proofs and Delimited Control" written by "Danko Ilik" *)

  Import BasicSetoidTheory MyEnsemble MyEnsembleNova CountableBooleanAlgebra SyntaxOfPL SemanticsOfPL InferenceRulesOfPL.

  Local Program Instance formula_isSetoid : isSetoid formula :=
    { eqProp :=
      fun b1 : formula =>
      fun b2 : formula =>
      \left\{ b1 \right\} |- b2 /\ \left\{ b2 \right\} |- b1
    }
  .

  Next Obligation with eauto with *.
    split.
    - intros b1.
      split; apply ByAssumption...
    - intros b1 b2 [H H0].
      split...
    - intros b1 b2 b3 [H H0] [H1 H2].
      split.
      + apply (cut_property b2 b3 H).
        apply (extend_infers H1)...
      + apply (cut_property b2 b1 H2).
        apply (extend_infers H0)...
  Qed.

  Global Program Instance LindenbaumBooleanAlgebra : @isCBA formula formula_isSetoid :=
    { trueB := ImplicationF ContradictionF ContradictionF
    ; falseB := ContradictionF
    ; negB := NegationF
    ; andB := ConjunctionF
    ; orB := DisjunctionF
    ; enumB := enum_formula
    }
  .

  Next Obligation with eauto with *.
    split.
    - apply NegationI.
      apply (ContradictionI b1).
      + apply (extend_infers H0)...
      + apply ByAssumption...
    - apply NegationI.
      apply (ContradictionI b1').
      + apply (extend_infers H)...
      + apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply ConjunctionI.
      + apply (cut_property b1 b1').
        * apply (ConjunctionE1 b1 b2).
          apply ByAssumption...
        * apply (extend_infers H)...
      + apply (cut_property b2 b2').
        * apply (ConjunctionE2 b1 b2).
          apply ByAssumption...
        * apply (extend_infers H0)...
    - apply ConjunctionI.
      + apply (cut_property b1' b1).
        * apply (ConjunctionE1 b1' b2').
          apply ByAssumption...
        * apply (extend_infers H2)...
      + apply (cut_property b2' b2).
        * apply (ConjunctionE2 b1' b2').
          apply ByAssumption...
        * apply (extend_infers H1)...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (DisjunctionE b1 b2 (DisjunctionF b1' b2')).
      + apply ByAssumption...
      + apply (DisjunctionI1 b1' b2').
        apply (extend_infers H)...
      + apply (DisjunctionI2 b1' b2').
        apply (extend_infers H0)...
    - apply (DisjunctionE b1' b2' (DisjunctionF b1 b2)).
      + apply ByAssumption...
      + apply (DisjunctionI1 b1 b2).
        apply (extend_infers H2)...
      + apply (DisjunctionI2 b1 b2).
        apply (extend_infers H1)...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply ConjunctionI.
      + apply ConjunctionI.
        * apply (ConjunctionE1 b1 (ConjunctionF b2 b3)).
          apply ByAssumption...
        * apply (ConjunctionE1 b2 b3).
          apply (ConjunctionE2 b1 (ConjunctionF b2 b3)).
          apply ByAssumption...
      + apply (ConjunctionE2 b2 b3).
        apply (ConjunctionE2 b1 (ConjunctionF b2 b3)).
        apply ByAssumption...
    - apply ConjunctionI.
      + apply (ConjunctionE1 b1 b2).
        apply (ConjunctionE1 (ConjunctionF b1 b2) b3).
        apply ByAssumption...
      + apply ConjunctionI.
        * apply (ConjunctionE2 b1 b2).
          apply (ConjunctionE1 (ConjunctionF b1 b2) b3).
          apply ByAssumption...
        * apply (ConjunctionE2 (ConjunctionF b1 b2) b3).
          apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (DisjunctionE b1 (DisjunctionF b2 b3)).
      + apply ByAssumption...
      + apply (DisjunctionI1 (DisjunctionF b1 b2) b3).
        apply (DisjunctionI1 b1 b2).
        apply ByAssumption...
      + apply (DisjunctionE b2 b3).
        * apply ByAssumption...
        * apply (DisjunctionI1 (DisjunctionF b1 b2) b3).
          apply (DisjunctionI2 b1 b2).
          apply ByAssumption...
        * apply (DisjunctionI2 (DisjunctionF b1 b2) b3).
          apply ByAssumption...
    - apply (DisjunctionE (DisjunctionF b1 b2) b3).
      + apply ByAssumption...
      + apply (DisjunctionE b1 b2).
        * apply ByAssumption...
        * apply (DisjunctionI1 b1 (DisjunctionF b2 b3)).
          apply ByAssumption...
        * apply (DisjunctionI2 b1 (DisjunctionF b2 b3)).
          apply (DisjunctionI1 b2 b3).
          apply ByAssumption...
      + apply (DisjunctionI2 b1 (DisjunctionF b2 b3)).
        apply (DisjunctionI2 b2 b3).
        apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (ConjunctionE1 b1 b1).
      apply ByAssumption...
    - apply ConjunctionI; apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (DisjunctionE b1 b1 b1); apply ByAssumption...
    - apply DisjunctionI1.
      apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply ConjunctionI.
      + apply (ConjunctionE2 b1 b2).
        apply ByAssumption...
      + apply (ConjunctionE1 b1 b2).
        apply ByAssumption...
    - apply ConjunctionI.
      + apply (ConjunctionE2 b2 b1).
        apply ByAssumption...
      + apply (ConjunctionE1 b2 b1).
        apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (DisjunctionE b1 b2).
      + apply ByAssumption...
      + apply (DisjunctionI2 b2 b1).
        apply ByAssumption...
      + apply (DisjunctionI1 b2 b1).
        apply ByAssumption...
    - apply (DisjunctionE b2 b1).
      + apply ByAssumption...
      + apply (DisjunctionI2 b1 b2).
        apply ByAssumption...
      + apply (DisjunctionI1 b1 b2).
        apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (DisjunctionE b2 b3).
      + apply (ConjunctionE2 b1 (DisjunctionF b2 b3)).
        apply ByAssumption...
      + apply DisjunctionI1.
        apply ConjunctionI.
        * apply (ConjunctionE1 b1 (DisjunctionF b2 b3)).
          apply ByAssumption...
        * apply ByAssumption...
      + apply DisjunctionI2.
        apply ConjunctionI.
        * apply (ConjunctionE1 b1 (DisjunctionF b2 b3)).
          apply ByAssumption...
        * apply ByAssumption...
    - apply (DisjunctionE (ConjunctionF b1 b2) (ConjunctionF b1 b3)).
      + apply ByAssumption...
      + apply ConjunctionI.
        * apply (ConjunctionE1 b1 b2).
          apply ByAssumption...
        * apply DisjunctionI1.
          apply (ConjunctionE2 b1 b2).
          apply ByAssumption...
      + apply ConjunctionI.
        * apply (ConjunctionE1 b1 b3).
          apply ByAssumption...
        * apply DisjunctionI2.
          apply (ConjunctionE2 b1 b3).
          apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply ConjunctionI.
      + apply (DisjunctionE b1 (ConjunctionF b2 b3)).
        * apply ByAssumption...
        * apply DisjunctionI1.
          apply ByAssumption...
        * apply DisjunctionI2.
          apply (ConjunctionE1 b2 b3).
          apply ByAssumption...
      + apply (DisjunctionE b1 (ConjunctionF b2 b3)).
        * apply ByAssumption...
        * apply DisjunctionI1.
          apply ByAssumption...
        * apply DisjunctionI2.
          apply (ConjunctionE2 b2 b3).
          apply ByAssumption...
  - apply (DisjunctionE b1 b2).
    + apply (ConjunctionE1 (DisjunctionF b1 b2) (DisjunctionF b1 b3)).
      apply ByAssumption...
    + apply DisjunctionI1.
      apply ByAssumption...
    + apply (DisjunctionE b1 b3).
      * apply (ConjunctionE2 (DisjunctionF b1 b2) (DisjunctionF b1 b3)).
        apply ByAssumption...
      * apply DisjunctionI1.
        apply ByAssumption...
      * apply DisjunctionI2.
        apply ConjunctionI; apply ByAssumption...
        apply in_insert_iff, or_intror...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (ConjunctionE1 b1 (DisjunctionF b1 b2)).
      apply ByAssumption...
    - apply ConjunctionI.
      + apply ByAssumption...
      + apply DisjunctionI1.
        apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (DisjunctionE b1 (ConjunctionF b1 b2)).
      + apply ByAssumption...
      + apply ByAssumption...
      + apply (ConjunctionE1 b1 b2).
        apply ByAssumption...
    - apply DisjunctionI1.
      apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (ConjunctionE2 b1 ContradictionF).
      apply ByAssumption...
    - apply ConjunctionI.
      + apply ContradictionE.
        apply ByAssumption...
      + apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply ImplicationI.
      apply ByAssumption...
    - apply DisjunctionI2.
      apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (DisjunctionE b1 ContradictionF).
      + apply ByAssumption...
      + apply ByAssumption...
      + apply ContradictionE.
        apply ByAssumption...
    - apply DisjunctionI1.
      apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (ConjunctionE1 b1 (ImplicationF ContradictionF ContradictionF)).
      apply ByAssumption...
    - apply ConjunctionI.
      + apply ByAssumption...
      + apply ImplicationI.
        apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (ContradictionI b1).
      + apply (ConjunctionE1 b1 (NegationF b1)).
        apply ByAssumption...
      + apply (ConjunctionE2 b1 (NegationF b1)).
        apply ByAssumption...
    - apply ContradictionE.
      apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply ImplicationI.
      apply ByAssumption...
    - apply (extend_infers (Law_of_Exclusive_Middle b1)).
      intros p H.
      apply in_empty_iff in H...
  Qed.

  Next Obligation with eauto with *.
    destruct (formula_is_enumerable b) as [n H]...
  Qed.

  Lemma leq_LBA :
    forall b1 : formula,
    forall b2 : formula,
    andB b1 b2 == b1 <-> \left\{ b1 \right\} |- b2.
  Proof with eauto with *.
    intros b1 b2.
    split.
    - intros [H H0].
      apply (ConjunctionE2 b1 b2)...
    - intros H.
      split.
      + apply (ConjunctionE1 b1 b2).
        apply ByAssumption...
      + apply ConjunctionI.
        * apply ByAssumption...
        * apply H.
  Qed.

  Lemma andBs_LBA :
    forall ps : list formula,
    forall hs : ensemble formula,
    (forall p : formula, In p ps -> member p hs) ->
    forall c : formula,
    \left\{ fold_right andB trueB ps \right\} |- c <-> (exists hs' : ensemble formula, (forall h : formula, In h ps <-> member h hs') /\ hs' |- c).
  Proof with eauto with *.
    induction ps as [| p ps IH]; simpl.
    { intros hs H c.
      split.
      - intros H0.
        exists (\emptyset).
        split.
        + intros p.
          rewrite in_empty_iff.
          reflexivity.
        + apply (ConjunctionE2 (ImplicationF ContradictionF ContradictionF) c).
          apply (cut_property (ImplicationF ContradictionF ContradictionF) (ConjunctionF (ImplicationF ContradictionF ContradictionF) c)).
          * apply ImplicationI.
            apply ByAssumption...
          * apply ConjunctionI; [apply ByAssumption | apply (extend_infers H0)]...
      - intros [hs' [H0 H1]].
        assert (claim1 : isSubsetOf hs' \emptyset).
        { intros h.
          rewrite <- (H0 h).
          intros [].
        }
        assert (claim2 : \emptyset |- c) by now apply (extend_infers H1).
        apply (extend_infers claim2)...
    }
    { intros hs H c.
      split.
      - intros H0.
        assert (claim3 : forall h : formula, In h ps -> member h hs) by firstorder.
        assert (claim4 : \left\{ fold_right andB trueB ps \right\} |- ImplicationF p c).
        { apply ImplicationI.
          apply (cut_property (fold_right andB trueB (p :: ps)) c).
          - simpl.
            apply ConjunctionI; apply ByAssumption...
          - apply (extend_infers H0)...
        }
        destruct (proj1 (IH hs claim3 (ImplicationF p c)) claim4) as [hs' [H1 H2]].
        exists (insert p hs').
        split.
        + intros h.
          rewrite in_insert_iff.
          firstorder.
        + apply (cut_property (ImplicationF p c) c).
          apply (extend_infers H2)...
          apply (ImplicationE p c).
          * apply ByAssumption...
          * apply ByAssumption, in_insert_iff, or_intror...
      - intros [hs' [H0 H1]].
        destruct (in_dec eq_formula_dec p ps) as [H_yes | H_no].
        + assert (claim5 : forall h : formula, In h ps -> member h hs) by firstorder.
          assert (claim6 : exists hs' : ensemble formula, (forall h : formula, In h ps <-> member h hs') /\ hs' |- c).
          { exists (hs').
            split.
            - intros h'.
              split.
              + firstorder.
              + intros H2.
                destruct (proj2 (H0 h') H2) as [H3 | H3].
                * subst...
                * apply H3.
            - apply H1.
          }
          assert (claim7 : \left\{ fold_right andB trueB ps \right\} |- c) by apply (proj2 (IH hs claim5 c) claim6).
          apply (cut_property (fold_right andB trueB ps) c).
          * simpl.
            apply (ConjunctionE2 p (fold_right ConjunctionF (ImplicationF ContradictionF ContradictionF) ps)).
            apply ByAssumption...
          * apply (extend_infers claim7)...
        + assert (claim8 : forall h : formula, In h ps -> member h (delete p hs)).
          { intros h H2.
            apply in_delete_iff.
            split...
            intros Heq.
            subst...
          }
          assert (claim9 : exists hs' : ensemble formula, (forall h : formula, In h ps <-> member h hs') /\ hs' |- ImplicationF p c).
          { exists (delete p hs').
            split.
            - intros h.
              rewrite in_delete_iff, <- H0.
              split.
              + intros H2.
                split...
                intros Heq.
                subst...
              + intros [[H2 | H2] H3]...
                subst; contradiction.
            - apply ImplicationI.
              apply (extend_infers H1).
              intros h' H2.
              rewrite in_insert_iff, in_delete_iff.
              destruct (eq_formula_dec h' p)...
          }
        assert (claim10 : \left\{ fold_right andB trueB ps \right\} |- ImplicationF p c) by apply (proj2 (IH (delete p hs) claim8 (ImplicationF p c)) claim9).
        apply (ImplicationE p c).
        { apply (cut_property (fold_right andB trueB ps) (ImplicationF p c)); simpl.
          - apply (ConjunctionE2 p (fold_right ConjunctionF (ImplicationF ContradictionF ContradictionF) ps)).
            apply ByAssumption...
          - apply (extend_infers claim10)...
        }
        { apply (ConjunctionE1 p (fold_right ConjunctionF (ImplicationF ContradictionF ContradictionF) ps)).
          apply ByAssumption...
        }
    }
  Qed.

End LindenbaumBooleanAlgebraOnPropositionLogic.

Module ConstructiveMetaTheoryOnPropositonalLogic. (* Reference: "Constructive Completeness Proofs and Delimited Control" written by "Danko Ilik" *)

  Import ListNotations BasicSetoidTheory MyEnsemble BasicPosetTheory MyEnsembleNova CountableBooleanAlgebra SyntaxOfPL SemanticsOfPL InferenceRulesOfPL LindenbaumBooleanAlgebraOnPropositionLogic.

  Variant Th (hs : ensemble formula) : ensemble formula :=
  | in_Th :
    forall c : formula,
    hs |- c ->
    member c (Th hs)
  .

  Local Hint Constructors Th : core.

  Local Instance formula_isCBA : @isCBA formula formula_isSetoid :=
    LindenbaumBooleanAlgebra
  .

  Lemma lemma1_of_1_3_8 :
    forall bs : ensemble formula,
    isFilter (Th bs).
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
      - apply (@extend_infers \left\{ b1 \right\}).
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
      - apply (@extend_infers \left\{ andB b1 b2 \right\})...
    }
  Qed.

  Local Hint Resolve lemma1_of_1_3_8 : core.

  Lemma Cl_isSubsetOf_Th :
    forall hs : ensemble formula,
    isSubsetOf (Cl hs) (Th hs).
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
      apply (extend_infers H3)...
    }
    intros ps H c H0.
    assert (H1 : \left\{ fold_right andB trueB ps \right\} |- c) by apply leq_LBA, H0.
    destruct (proj1 (andBs_LBA ps hs H c) H1) as [hs' [H2 H3]].
    exists (hs').
    split...
    intros h H4.
    apply H.
    apply H2...
  Qed.

  Local Hint Resolve Cl_isSubsetOf_Th : core.

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
      - apply (in_append_elim1 ps1 ps2 hs H1 H2).
      - exists (union hs1' hs2').
        split.
        + apply (in_append_iff ps1 ps2 hs1' hs2' H3 H4).
        + apply (ContradictionI a).
          * apply (extend_infers H5)...
          * apply (extend_infers H6)...
    }
    { destruct IHinfers as [ps [H0 [hs' [H1 H2]]]].
      exists (ps)...
    }
    { destruct IHinfers as [ps [H0 [hs' [H1 H2]]]].
      exists (remove eq_formula_dec a ps).
      split.
      - apply in_remove_elim1...
      - exists (delete a hs').
        split.
        + apply in_remove_iff...
        + apply NegationI.
          apply (extend_infers H2).
          intros p H3.
          destruct (eq_formula_dec p a) as [H_yes | H_no].
          * subst...
          * apply in_insert_iff, or_intror, in_delete_iff...
    }
    { destruct IHinfers as [ps [H0 [hs' [H1 H2]]]].
      exists (remove eq_formula_dec (NegationF a) ps).
      split.
      - apply in_remove_elim1...
      - exists (delete (NegationF a) hs').
        split.
        + intros h.
          apply (in_remove_iff eq_formula_dec (NegationF a) ps hs' H1).
        + apply NegationE.
          apply (extend_infers H2).
          intros h H3.
          destruct (eq_formula_dec h (NegationF a)) as [H_yes | H_no].
          * subst...
          * apply in_insert_iff, or_intror, in_delete_iff...
    }
    { destruct IHinfers1 as [ps1 [H1 [hs1' [H3 H5]]]].
      destruct IHinfers2 as [ps2 [H2 [hs2' [H4 H6]]]].
      exists (ps1 ++ ps2).
      split.
      - apply (in_append_elim1 ps1 ps2 hs H1 H2).
      - exists (union hs1' hs2').
        split.
        + apply (in_append_iff ps1 ps2 hs1' hs2' H3 H4).
        + apply ConjunctionI.
          * apply (extend_infers H5)...
          * apply (extend_infers H6)...
    }
    { destruct IHinfers as [ps [H0 [hs' [H1 H2]]]].
      exists (ps)...
    }
    { destruct IHinfers as [ps [H0 [hs' [H1 H2]]]].
      exists (ps)...
    }
    { destruct IHinfers as [ps [H0 [hs' [H1 H2]]]].
      exists (ps)...
    }
    { destruct IHinfers as [ps [H0 [hs' [H1 H2]]]].
      exists (ps)...
    }
    { destruct IHinfers1 as [ps1 [H2 [hs1' [H5 H8]]]].
      destruct IHinfers2 as [ps2 [H3 [hs2' [H6 H9]]]].
      destruct IHinfers3 as [ps3 [H4 [hs3' [H7 H10]]]].
      exists (ps1 ++ (remove eq_formula_dec a ps2 ++ remove eq_formula_dec b ps3)).
      split.
      - apply in_append_elim1...
        apply in_append_elim1...
        apply in_remove_elim1...
        apply in_remove_elim1...
      - exists (union hs1' (union (delete a hs2') (delete b hs3'))).
        split.
        { apply in_append_iff...
          apply in_append_iff...
          apply in_remove_iff...
          apply in_remove_iff...
        }
        { apply (DisjunctionE a b c).
          - apply (extend_infers H8)...
          - apply (extend_infers H9).
            intros p H11.
            destruct (eq_formula_dec p a) as [H_yes | H_no].
            + subst...
            + apply in_insert_iff, or_intror, in_union_iff, or_intror, in_union_iff, or_introl, in_delete_iff...
          - apply (extend_infers H10).
            intros p H11.
            destruct (eq_formula_dec p b) as [H_yes | H_no].
            + subst...
            + apply in_insert_iff, or_intror, in_union_iff, or_intror, in_union_iff, or_intror, in_delete_iff...
        }
    }
    { destruct IHinfers as [ps [H0 [hs' [H1 H2]]]].
      exists (remove eq_formula_dec a ps).
      split.
      - apply in_remove_elim1...
      - exists (delete a hs').
        split.
        + apply in_remove_iff...
        + apply ImplicationI.
          apply (extend_infers H2).
          intros p H3.
          destruct (eq_formula_dec p a) as [H_yes | H_no].
          * subst...
          * apply in_insert_iff, or_intror, in_delete_iff...
    }
    { destruct IHinfers1 as [ps1 [H1 [hs1' [H3 H5]]]].
      destruct IHinfers2 as [ps2 [H2 [hs2' [H4 H6]]]].
      exists (ps1 ++ ps2).
      split.
      - apply (in_append_elim1 ps1 ps2 hs H1 H2).
      - exists (union hs1' hs2').
        split.
        + apply (in_append_iff ps1 ps2 hs1' hs2' H3 H4).
        + apply (ImplicationE a b).
          * apply (extend_infers H5)...
          * apply (extend_infers H6)...
    }
    { destruct IHinfers1 as [ps1 [H1 [hs1' [H3 H5]]]].
      destruct IHinfers2 as [ps2 [H2 [hs2' [H4 H6]]]].
      exists (remove eq_formula_dec a ps1 ++ remove eq_formula_dec b ps2).
      split.
      - apply in_append_elim1; apply in_remove_elim1...
      - exists (union (delete a hs1') (delete b hs2')).
        split.
        + apply in_append_iff; apply in_remove_iff...
        + apply BiconditionalI.
          { apply (extend_infers H5).
            intros p H7.
            destruct (eq_formula_dec p a) as [H_yes | H_no].
            - subst...
            - apply in_insert_iff, or_intror, in_union_iff, or_introl, in_delete_iff...
          }
          { apply (extend_infers H6).
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
      - apply (in_append_elim1 ps1 ps2 hs H1 H2).
      - exists (union hs1' hs2').
        split.
        + apply (in_append_iff ps1 ps2 hs1' hs2' H3 H4).
        + apply (BiconditionalE1 a b).
          * apply (extend_infers H5)...
          * apply (extend_infers H6)...
    }
    { destruct IHinfers1 as [ps1 [H1 [hs1' [H3 H5]]]].
      destruct IHinfers2 as [ps2 [H2 [hs2' [H4 H6]]]].
      exists (ps1 ++ ps2).
      split.
      - apply (in_append_elim1 ps1 ps2 hs H1 H2).
      - exists (union hs1' hs2').
        split.
        + apply (in_append_iff ps1 ps2 hs1' hs2' H3 H4).
        + apply (BiconditionalE2 a b).
          * apply (extend_infers H5)...
          * apply (extend_infers H6)...
    }
  Qed.

  Lemma Th_isSubsetOf_Cl :
    forall hs : ensemble formula,
    isSubsetOf (Th hs) (Cl hs).
  Proof with eauto with *.
    intros hs c H.
    inversion H; subst.
    destruct (infers_has_compactness hs c H0) as [ps [H1 H2]].
    assert (claim1 := proj2 (andBs_LBA ps hs H1 c) H2).
    exists (ps).
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
    - exists (O)...
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
    improveFilter (Th hs) n
  .

  Definition AxmSet : ensemble formula -> nat -> ensemble formula :=
    fun hs : ensemble formula =>
    fix AxmSet_fix (n : nat) {struct n} : ensemble formula :=
    match n with
    | O => hs
    | S n' => union (AxmSet_fix n') (insertion (Filter hs n') n')
    end
  .

  Lemma inconsistent_iff :
    forall hs : ensemble formula,
    inconsistent (Cl hs) <-> hs |- ContradictionF.
  Proof with eauto with *.
    intros hs.
    split.
    - intros [b' [H [H0 H1]]].
      assert (claim1 : member b' (Th hs)) by now apply (Cl_isSubsetOf_Th hs b' H).
      inversion claim1; subst.
      apply (cut_property b' ContradictionF).
      + exact H2.
      + apply (extend_infers H0)...
    - intros H.
      exists (ContradictionF).
      split...
      apply Th_isSubsetOf_Cl...
  Qed.

  Local Hint Resolve fact1_of_1_2_8 fact2_of_1_2_8 fact3_of_1_2_8 fact4_of_1_2_8 fact5_of_1_2_8 lemma1_of_1_2_11 inconsistent_isSubsetOf inconsistent_iff : core.

  Lemma equiconsistent_iff :
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
        apply inconsistent_iff.
        apply (inconsistent_isSubsetOf hs2)...
        apply H...
        apply (inconsistent_isSubsetOf (Cl hs1))...
        apply inconsistent_iff...
      + intros H0.
        apply inconsistent_iff.
        apply (inconsistent_isSubsetOf hs1)...
        apply H...
        apply (inconsistent_isSubsetOf (Cl hs2))...
        apply inconsistent_iff...
    - intros H.
      split.
      + intros H0.
        apply (inconsistent_isSubsetOf (Cl hs2))...
        apply inconsistent_iff, H, inconsistent_iff...
      + intros H0.
        apply (inconsistent_isSubsetOf (Cl hs1))...
        apply inconsistent_iff, H, inconsistent_iff...
  Qed.

  Lemma lemma1_of_1_3_9 :
    forall n : nat,
    forall hs : ensemble formula,
    isSubsetOf (Filter hs n) (Th (AxmSet hs n)) /\ isSubsetOf (Th (AxmSet hs n)) (Filter hs n).
  Proof with eauto with *.
    unfold Filter.
    induction n as [| n IH]; simpl.
    - intros hs...
    - intros hs.
      destruct (IH hs) as [H H0].
      assert (claim1 : isSubsetOf (Cl (union (improveFilter (Th hs) n) (insertion (improveFilter (Th hs) n) n))) (Cl (Th (union (AxmSet hs n) (insertion (Filter hs n) n))))).
      { apply fact4_of_1_2_8.
        intros b.
        rewrite in_union_iff.
        intro H1.
        inversion H1; subst.
        - assert (H3 := H b H2).
          inversion H3; subst.
          constructor.
          apply (extend_infers H4).
          intros p H5.
          apply in_union_iff, or_introl...
        - constructor.
          apply ByAssumption, in_union_iff, or_intror...
      }
      assert (claim2 : isSubsetOf (Cl (Th (union (AxmSet hs n) (insertion (Filter hs n) n)))) (Th (union (AxmSet hs n) (insertion (Filter hs n) n)))) by apply fact5_of_1_2_8, lemma1_of_1_3_8.
      assert (claim3 : isSubsetOf (Th (union (AxmSet hs n) (insertion (Filter hs n) n))) (Cl (union (AxmSet hs n) (insertion (Filter hs n) n)))) by apply Th_isSubsetOf_Cl.
      assert (claim4 : isSubsetOf (Cl (Cl (union (improveFilter (Th hs) n) (insertion (improveFilter (Th hs) n) n)))) (Cl (union (improveFilter (Th hs) n) (insertion (improveFilter (Th hs) n) n)))) by apply fact5_of_1_2_8, fact1_of_1_2_8.
      assert (claim5 : isSubsetOf (Cl (union (AxmSet hs n) (insertion (Filter hs n) n))) (Cl (Cl (union (improveFilter (Th hs) n) (insertion (improveFilter (Th hs) n) n))))).
      { transitivity (Cl (union (improveFilter (Th hs) n) (insertion (improveFilter (Th hs) n) n)))...
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
    equiconsistent (Th (insert (NegationF c) hs)) (eval_formula E) ->
    isSubsetOf (Th (insert (NegationF c) hs)) (eval_formula E) ->
    isFilter (eval_formula E) ->
    hs |- c.
  Proof with eauto with *.
    intros hs c H_entail E.
    set (v := eval_formula E).
    intros H_equiconsistent H_incl H_isFilter.
    assert (claim1 : inconsistent (Th (insert (NegationF c) hs))).
    { apply H_equiconsistent.
      enough (claim1_aux1 : inconsistent (Cl v))...
      apply inconsistent_iff.
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
    { apply (inconsistent_isSubsetOf (Th (insert (NegationF c) hs)))...
      apply Th_isSubsetOf_Cl.
    }
    apply NegationE, inconsistent_iff...
  Qed.

  Definition MaximalConsistentSet : ensemble formula -> ensemble formula :=
    fun bs : ensemble formula =>
    CompleteFilter (Th bs)
  .

  Variant FullAxmSet (bs : ensemble formula) : ensemble formula :=
  | in_FullAxmSet :
    forall n : nat,
    forall b : formula,
    member b (AxmSet bs n) ->
    member b (FullAxmSet bs)
  .

  Local Hint Constructors FullAxmSet : core.

  Lemma lemma2_of_1_3_9 :
    forall bs : ensemble formula,
    isSubsetOf (MaximalConsistentSet bs) (Th (FullAxmSet bs)).
  Proof with eauto with *.
    intros bs p H.
    inversion H; subst.
    assert (H1 := proj1 (lemma1_of_1_3_9 n bs) p H0).
    inversion H1; subst.
    constructor.
    apply (extend_infers H2)...
  Qed.

  Lemma lemma3_of_1_3_9_aux1 :
    forall ps : list formula,
    forall bs : ensemble formula,
    (forall p : formula, In p ps -> member p (FullAxmSet bs)) ->
    exists m : nat, (forall p : formula, In p ps -> member p (Filter bs m)).
  Proof with eauto with *.
    induction ps as [| p ps IH]; simpl.
    - intros bs H.
      exists (O)...
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
      + exists (n).
        intros h [H2 | H2].
        * subst...
        * apply (lemma1_of_1_2_12  n' n Hle (Th bs))...
      + exists (n').
        intros h [H2 | H2]; subst.
        * assert (H3 : n <= n') by lia.
          apply (lemma1_of_1_2_12 n n' H3 (Th bs))...
        * apply H1...
  Qed.

  Lemma lemma3_of_1_3_9 :
    forall bs : ensemble formula,
    isSubsetOf (Th (FullAxmSet bs)) (MaximalConsistentSet bs).
  Proof with eauto with *.
    intros bs p H.
    inversion H; subst.
    destruct (infers_has_compactness (FullAxmSet bs) p H0) as [ps [H1 [hs' [H2 H3]]]].
    destruct (lemma3_of_1_3_9_aux1 ps bs H1) as [m H4].
    assert (H5 : isFilter (improveFilter (Th bs) m)) by apply lemma1_of_1_2_11, lemma1_of_1_3_8.
    assert (H6 := proj1 H5).
    destruct (proj2 H5) as [H7 H8].
    exists (m).
    apply (H7 (fold_right andB trueB ps) p).
    - apply fact5_of_1_2_8.
      + apply H5.
      + exists (ps)...
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
    isSubsetOf (Th bs) (MaximalConsistentSet bs).
  Proof with eauto with *.
    apply theorem_of_1_2_14...
  Qed.

  Lemma theorem_of_1_3_10_aux2 (bs : ensemble formula) :
    equiconsistent (Th bs) (MaximalConsistentSet bs).
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
      assert (claim1 : member p (Th (MaximalConsistentSet bs))) by now apply Cl_isSubsetOf_Th, fact3_of_1_2_8.
      inversion claim1; subst...
    - intros H.
      apply fact5_of_1_2_8.
      + apply theorem_of_1_2_14...
      + apply Th_isSubsetOf_Cl...
  Qed.

  Theorem theorem_of_1_3_10 :
    forall bs : ensemble formula,
    isSubsetOf (Th bs) (MaximalConsistentSet bs) /\ equiconsistent (Th bs) (MaximalConsistentSet bs) /\ (forall p : formula, member p (MaximalConsistentSet bs) <-> MaximalConsistentSet bs |- p) /\ isMetaDN (MaximalConsistentSet bs) /\ isImplicationFaithful (MaximalConsistentSet bs).
  Proof with eauto with *.
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
        assert (claim5_aux1 : insert p1 (MaximalConsistentSet bs) |- ContradictionF) by now apply inconsistent_iff.
        exists (ContradictionF).
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
          - apply (@extend_infers (MaximalConsistentSet bs)).
            + apply claim3...
            + apply lemma2.
        }
        assert (claim6_aux2 : MaximalConsistentSet bs |- ConjunctionF p1 (NegationF p2)).
        { apply (DisjunctionE p1 (NegationF p1)).
          - apply (extend_infers (Law_of_Exclusive_Middle p1))...
          - apply (DisjunctionE p2 (NegationF p2)).
            + apply (extend_infers (Law_of_Exclusive_Middle p2))...
            + apply ContradictionE.
              apply (cut_property (ImplicationF p1 p2)).
              * apply ImplicationI.
                apply ByAssumption.
                apply in_insert_iff, or_intror, in_insert_iff, or_introl...
              * apply (extend_infers claim6_aux1).
                apply insert_intro_isSubsetOf.
                transitivity (insert p1 (MaximalConsistentSet bs))...
            + apply ConjunctionI.
              { apply ByAssumption.
                apply in_insert_iff, or_intror, in_insert_iff, or_introl...
              }
              { apply (DisjunctionE p2 (NegationF p2)).
                - apply (extend_infers (Law_of_Exclusive_Middle p2))...
                - apply ContradictionE.
                  apply (cut_property (ImplicationF p1 p2)).
                  + apply ImplicationI.
                    apply ByAssumption.
                    apply in_insert_iff, or_intror, in_insert_iff, or_introl...
                  + apply (extend_infers claim6_aux1).
                    apply insert_intro_isSubsetOf.
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
            + apply (extend_infers claim6_aux1).
              apply insert_intro_isSubsetOf...
        }
      assert (claim6_aux3 : MaximalConsistentSet bs |- p1) by now apply (ConjunctionE1 p1 (NegationF p2)).
      assert (claim6_aux4 : MaximalConsistentSet bs |- NegationF p2) by now apply (ConjunctionE2 p1 (NegationF p2)).
      apply (ContradictionI p2).
      + apply claim3, H, claim3...
      + apply claim6_aux4.
    }
    tauto.
  Qed.

End ConstructiveMetaTheoryOnPropositonalLogic.
