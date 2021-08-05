Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.pure.DomainTheory.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module CountableBooleanAlgebra. (* Reference: "Constructive Completeness Proofs and Delimited Control" written by "Danko Ilik" *)

  Import ListNotations MyUtilities BasicSetoidTheory MyEnsemble BasicPosetTheory MyEnsembleNova ConstructiveCpoTheory.

  Global Create HintDb cba_hints.

  Class isCBA (B : Type) `{B_isSetoid : isSetoid B} : Type :=
    { trueB : B
    ; falseB : B
    ; negB : B -> B
    ; andB : B -> B -> B
    ; orB : B -> B -> B
    ; enumB : nat -> B
    ; trueB_preserves_eqB : trueB == trueB
    ; falseB_preserves_eqB : falseB == falseB
    ; negB_preserves_eqB : forall b1 : B, forall b1' : B, b1 == b1' -> negB b1 == negB b1'
    ; andB_preserves_eqB : forall b1 : B, forall b1' : B, forall b2 : B, forall b2' : B, b1 == b1' -> b2 == b2' -> andB b1 b2 == andB b1' b2'
    ; orB_preserves_eqB : forall b1 : B, forall b1' : B, forall b2 : B, forall b2' : B, b1 == b1' -> b2 == b2' -> orB b1 b2 == orB b1' b2'
    ; andB_associative : forall b1 : B, forall b2 : B, forall b3 : B, andB b1 (andB b2 b3) == andB (andB b1 b2) b3
    ; orB_associative : forall b1 : B, forall b2 : B, forall b3 : B, orB b1 (orB b2 b3) == orB (orB b1 b2) b3
    ; andB_idempotent : forall b1 : B, andB b1 b1 == b1
    ; orB_idempotent : forall b1 : B, orB b1 b1 == b1
    ; andB_commutative : forall b1 : B, forall b2 : B, andB b1 b2 == andB b2 b1
    ; orB_commutative : forall b1 : B, forall b2 : B, orB b1 b2 == orB b2 b1
    ; andB_distribute_orB : forall b1 : B, forall b2 : B, forall b3 : B, andB b1 (orB b2 b3) == orB (andB b1 b2) (andB b1 b3)
    ; orB_distribute_andB : forall b1 : B, forall b2 : B, forall b3 : B, orB b1 (andB b2 b3) == andB (orB b1 b2) (orB b1 b3)
    ; absorption_andB_orB : forall b1 : B, forall b2 : B, andB b1 (orB b1 b2) == b1
    ; absorption_orB_andB : forall b1 : B, forall b2 : B, orB b1 (andB b1 b2) == b1
    ; falseB_zero_andB : forall b1 : B, andB b1 falseB == falseB
    ; trueB_zero_orB : forall b1 : B, orB b1 trueB == trueB
    ; falseB_unit_orB : forall b1 : B, orB b1 falseB == b1
    ; trueB_unit_andB : forall b1 : B, andB b1 trueB == b1
    ; andB_negB : forall b1 : B, andB b1 (negB b1) == falseB
    ; orB_negB : forall b1 : B, orB b1 (negB b1) == trueB 
    ; enumB_surjective : forall b : B, exists n : nat, enumB n = b
    }
  .

  Global Hint Resolve andB_associative orB_associative andB_idempotent orB_idempotent andB_commutative orB_commutative andB_distribute_orB orB_distribute_andB absorption_andB_orB absorption_orB_andB falseB_preserves_eqB trueB_zero_orB trueB_unit_andB falseB_unit_orB andB_negB orB_negB : cba_hints.

  Add Parametric Morphism (B : Type) `{B_isSetoid : isSetoid B} `{B_isCBA : @isCBA B B_isSetoid} :
    negB with signature (eqProp ==> eqProp)
  as negB_preserves.
  Proof.
    auto using negB_preserves_eqB.
  Qed.

  Add Parametric Morphism (B : Type) `{B_isSetoid : isSetoid B} `{B_isCBA : @isCBA B B_isSetoid} :
    andB with signature (eqProp ==> eqProp ==> eqProp)
  as andB_preserves.
  Proof.
    auto using andB_preserves_eqB.
  Qed.

  Add Parametric Morphism (B : Type) `{B_isSetoid : isSetoid B} `{B_isCBA : @isCBA B B_isSetoid} :
    orB with signature (eqProp ==> eqProp ==> eqProp)
  as orB_preserves.
  Proof.
    auto using orB_preserves_eqB.
  Qed.

  Definition leCBA {B : Type} `{B_isSetoid : isSetoid B} (B_isCBA : @isCBA B B_isSetoid) :=
    fun b1 : B =>
    fun b2 : B =>
    andB b1 b2 == b1
  .

  Global Hint Unfold leCBA : cba_hints.

  Global Instance leCBA_Reflexive {B : Type} `{B_isSetoid : isSetoid B} (B_requiresCBA : @isCBA B B_isSetoid) :
    Reflexive (leCBA B_requiresCBA).
  Proof with eauto with *.
    unfold leCBA...
  Qed.

  Global Instance leCBA_Transitive {B : Type} `{B_isSetoid : isSetoid B} (B_requiresCBA : @isCBA B B_isSetoid) :
    Transitive (leCBA B_requiresCBA).
  Proof with eauto with *.
    unfold leCBA.
    intros b1 b2 b3 H H0.
    transitivity (andB b1 (andB b2 b3)).
    - rewrite andB_associative, H...
    - rewrite H0...
  Qed.

  Global Instance leCBA_PreOrder {B : Type} `{B_isSetoid : isSetoid B} (B_requiresCBA : @isCBA B B_isSetoid) : PreOrder (leCBA B_requiresCBA) :=
    { PreOrder_Reflexive := leCBA_Reflexive B_requiresCBA
    ; PreOrder_Transitive := leCBA_Transitive B_requiresCBA
    }
  .

  Global Instance leCBA_PartialOrder {B : Type} `{B_isSetoid : isSetoid B} (B_requiresCBA : @isCBA B B_isSetoid) :
    PartialOrder eqProp (leCBA B_requiresCBA).
  Proof with eauto with *.
    unfold leCBA.
    intros b1 b2.
    split; unfold flip, relation_conjunction, predicate_intersection, pointwise_extension.
    - intros H.
      split; rewrite H...
    - intros [H H0].
      transitivity (andB b1 b2)...
  Qed.

  Global Instance CBA_isPoset {B : Type} `{B_isSetoid : isSetoid B} (B_requiresCBA : @isCBA B B_isSetoid) : isPoset B :=
    { leProp := leCBA B_requiresCBA
    ; Poset_requiresSetoid := B_isSetoid
    ; Poset_requiresPreOrder := leCBA_PreOrder B_requiresCBA
    ; Poset_requiresPartialOrder := leCBA_PartialOrder B_requiresCBA
    }
  .

  Section Section2OfChapter1.

  Context {B : Type} `{B_isSetoid : isSetoid B} `{B_isCBA : @isCBA B B_isSetoid}.

  Let leCBA_is : @leProp B (@CBA_isPoset B B_isSetoid B_isCBA) = @leCBA B B_isSetoid B_isCBA :=
    eq_refl
  .

  Hint Rewrite leCBA_is : core.

  Lemma andB_leCBA_intro1 :
    forall b1 : B,
    forall b2 : B,
    andB b1 b2 =< b1.
  Proof with eauto with *.
    rewrite leCBA_is.
    unfold leCBA.
    intros b1 b2.
    rewrite andB_commutative, andB_associative, andB_idempotent...
  Qed.

  Local Hint Resolve andB_leCBA_intro1 : core.

  Lemma andB_leCBA_intro2 :
    forall b1 : B,
    forall b2 : B,
    andB b1 b2 =< b2.
  Proof with eauto with *.
    rewrite leCBA_is.
    unfold leCBA.
    intros b1 b2.
    rewrite <- andB_associative, andB_idempotent...
  Qed.

  Local Hint Resolve andB_leCBA_intro2 : core.

  Lemma andB_leCBA_andB :
    forall b1 : B,
    forall b2 : B,
    forall b1' : B,
    forall b2' : B,
    b1 =< b2 ->
    b1' =< b2' ->
    andB b1 b1' =< andB b2 b2'.
  Proof with eauto with *.
    intros b1 b2 b1' b2'.
    rewrite leCBA_is.
    intros H H0.
    assert (claim1 : andB (andB b1 b1') (andB b1 b2') == andB (andB b1 b1) (andB b1' b2')).
    { repeat erewrite andB_associative.
      rewrite (andB_commutative (andB b1 b1') b1), (andB_associative b1 b1 b1')...
    }
    assert (claim2 : andB (andB b1 b2') (andB b2 b2') == andB (andB b1 b2) (andB b2' b2')).
    { repeat rewrite andB_associative.
      rewrite (andB_commutative (andB b1 b2) b2'), (andB_commutative b2' (andB b1 b2)), <- (andB_associative b1 b2' b2), (andB_commutative b2' b2), (andB_associative b1 b2 b2')...
    }
    transitivity (andB b1 b2'); unfold leCBA in *.
    - rewrite claim1, H0, andB_idempotent...
    - rewrite claim2, H, andB_idempotent...
  Qed.

  Local Hint Resolve andB_leCBA_andB : core.

  Lemma leCBA_andB_append :
    forall bs1 : list B,
    forall bs2 : list B,
    fold_right andB trueB (bs1 ++ bs2) == andB (fold_right andB trueB bs1) (fold_right andB trueB bs2).
  Proof with eauto with *.
    induction bs1 as [| b1 bs1 IH]; simpl.
    - intros bs2...
    - intros bs2.
      rewrite IH...
  Qed.

  Local Hint Resolve leCBA_andB_append : core.

  Definition isFilter : ensemble B -> Prop :=
    fun bs : ensemble B =>
    nonempty bs /\ (forall b1 : B, forall b2 : B, member b1 bs -> b1 =< b2 -> member b2 bs) /\ (forall b1 : B, forall b2 : B, forall b : B, member b1 bs -> member b2 bs -> b == andB b1 b2 -> member b bs)
  .

  Local Hint Unfold isFilter : core.

  Lemma Filter_isDirected :
    forall bs : ensemble B,
    isFilter bs ->
    isDirected bs.
  Proof with eauto with *.
    intros bs [H [H0 H1]].
    split.
    - apply H.
    - intros b1 H2 b2 H3.
      exists (orB b1 b2).
      split.
      + apply (H0 b1 (orB b1 b2) H2).
        rewrite leCBA_is...
      + split; [rewrite leCBA_is | rewrite orB_commutative, leCBA_is]...
  Qed.

  Lemma isFilter_ext_eq :
    forall bs1 : ensemble B,
    isFilter bs1 ->
    forall bs2 : ensemble B,
    bs1 == bs2 ->
    isFilter bs2.
  Proof with ((now firstorder) || eauto with *).
    intros bs1 [[b0 H] [H0 H1]] bs2.
    replace (bs1 == bs2) with (forall b : B, member b bs1 <-> member b bs2)...
    intros H2.
    enough (claim1 : forall b1 : B, forall b2 : B, forall b : B, member b1 bs2 -> member b2 bs2 -> b == andB b1 b2 -> member b bs2) by firstorder.
    intros b1 b2 b H3 H4 H5.
    apply (proj1 (H2 b)), (H1 b1 b2)...
  Qed.

  Inductive Cl : ensemble B -> ensemble B :=
  | in_Cl :
    forall bs1 : list B,
    forall b2 : B,
    forall bs2 : ensemble B,
    (forall b1 : B, In b1 bs1 -> member b1 bs2) ->
    fold_right andB trueB bs1 =< b2 ->
    member b2 (Cl bs2)
  .

  Local Hint Constructors Cl : core.

  Definition inconsistent : ensemble B -> Prop :=
    fun bs : ensemble B =>
    exists b : B, member b bs /\ b == falseB
  .

  Local Hint Unfold inconsistent : core.

  Definition equiconsistent : ensemble B -> ensemble B -> Prop :=
    fun bs1 : ensemble B =>
    fun bs2 : ensemble B =>
    inconsistent bs1 <-> inconsistent bs2
  .

  Local Hint Unfold equiconsistent : core.

  Definition isElementComplete : ensemble B -> B -> Prop :=
    fun bs1 : ensemble B =>
    fun b2 : B =>
    equiconsistent bs1 (Cl (insert b2 bs1)) ->
    member b2 bs1
  .

  Local Hint Unfold isElementComplete : core.

  Definition isComplete : ensemble B -> Prop :=
    fun bs1 : ensemble B =>
    forall b2 : B,
    isElementComplete bs1 b2
  .

  Local Hint Unfold isComplete : core.

  Lemma inconsistent_subset :
    forall bs1 : ensemble B,
    forall bs2 : ensemble B,
    isSubsetOf bs1 bs2 ->
    inconsistent bs1 ->
    inconsistent bs2.
  Proof with firstorder.
    unfold inconsistent, isSubsetOf...
  Qed.

  Local Hint Resolve inconsistent_subset : core.

  Lemma fact1_of_1_2_8 :
    forall bs : ensemble B,
    isFilter (Cl bs).
  Proof with ((now firstorder) || eauto with *).
    intros bs.
    split.
    - exists trueB.
      apply (in_Cl []); simpl...
    - split.
      + intros b1 b2 H.
        inversion H; subst...
      + intros b1 b2 b H H0.
        inversion H; subst.
        inversion H0; subst.
        rename bs0 into bs2.
        intros H5.
        apply (in_Cl (bs1 ++ bs2)).
        * intros b0.
          rewrite in_app_iff...
        * rewrite leCBA_andB_append, H5...
  Qed.

  Local Hint Resolve fact1_of_1_2_8 : core.

  Lemma fact2_of_1_2_8 :
    forall bs : ensemble B,
    isFilter bs ->
    member trueB bs.
  Proof with eauto with *.
    intros bs [[b0 H] [H0 H1]].
    enough (H2 : b0 =< trueB) by now apply (H0 b0).
    rewrite leCBA_is...
  Qed.

  Local Hint Resolve fact2_of_1_2_8 : core.

  Lemma fact3_of_1_2_8 :
    forall bs : ensemble B,
    isSubsetOf bs (Cl bs).
  Proof with eauto with *.
    intros bs b H.
    apply (in_Cl [b])...
    intros b1 [H0 | []]; subst...
  Qed.

  Local Hint Resolve fact3_of_1_2_8 : core.

  Lemma fact4_of_1_2_8 :
    forall bs1 : ensemble B,
    forall bs2 : ensemble B,
    isSubsetOf bs1 bs2 ->
    isSubsetOf (Cl bs1) (Cl bs2).
  Proof with eauto with *.
    intros bs1 bs2 H_incl b H.
    inversion H; subst.
    apply (in_Cl bs0)...
  Qed.

  Local Hint Resolve fact4_of_1_2_8 : core.

  Lemma leCBA_andB_fold_right :
    forall bs1 : list B,
    forall bs2 : ensemble B,
    isFilter bs2 ->
    (forall b1 : B, In b1 bs1 -> member b1 bs2) ->
    member (fold_right andB trueB bs1) bs2.
  Proof with eauto with *.
    induction bs1 as [| b1 bs1 IH]; simpl.
    - intros bs2 H H0...
    - intros bs2 [[b0 H] [H0 H1]] H2.
      apply (H1 b1 (fold_right andB trueB bs1)).
      + apply H2...
      + enough (claim1 : isFilter bs2)...
        split...
      + reflexivity.
  Qed.

  Local Hint Resolve leCBA_andB_fold_right : core.

  Lemma fact5_of_1_2_8 :
    forall bs : ensemble B,
    isFilter bs ->
    isSubsetOf (Cl bs) bs.
  Proof with eauto with *.
    intros bs H b H0.
    inversion H0; subst.
    apply (proj1 (proj2 H) (fold_right andB trueB bs1) b)...
  Qed.

  Local Hint Resolve fact5_of_1_2_8 : core.

  Lemma proposition1_of_1_2_9 :
    forall bs : ensemble B,
    isFilter bs ->
    forall b1 : B,
    member b1 bs ->
    forall b2 : B,
    b1 == b2 ->
    member b2 bs.
  Proof with eauto with *.
    intros bs [[b0 H] [H0 H1]] b1 H2 b2 H3...
  Qed.

  Local Hint Resolve proposition1_of_1_2_9 : core.

  Inductive insertion : ensemble B -> nat -> ensemble B :=
  | in_insertion :
    forall bs : ensemble B,
    forall n : nat,
    equiconsistent bs (Cl (insert (enumB n) bs)) ->
    member (enumB n) (insertion bs n)
  .

  Local Hint Constructors insertion : core.

  Definition improveFilter : ensemble B -> nat -> ensemble B :=
    fun bs : ensemble B =>
    fix improveFilter_fix (n : nat) : ensemble B :=
    match n with
    | 0 => bs
    | S n' =>
      let bs' : ensemble B := improveFilter_fix n' in
      Cl (union bs' (insertion bs' n'))
    end
  .

  Lemma lemma1_of_1_2_11 :
    forall n : nat,
    forall bs : ensemble B,
    isFilter bs ->
    isFilter (improveFilter bs n).
  Proof with eauto with *.
    induction n; simpl...
  Qed.

  Local Hint Resolve lemma1_of_1_2_11 : core.

  Lemma lemma1_of_1_2_12 :
    forall n1 : nat,
    forall n2 : nat,
    n1 <= n2 ->
    forall bs : ensemble B,
    isSubsetOf (improveFilter bs n1) (improveFilter bs n2).
  Proof with eauto with *.
    intros n1 n2 H.
    induction H as [| n2 H IH].
    - simpl...
    - intros bs.
      simpl.
      transitivity ((union (improveFilter bs n2) (insertion (improveFilter bs n2) n2)))...
      intros b H0.
      apply in_union_iff.
      unfold isSubsetOf in IH...
  Qed.

  Local Hint Resolve lemma1_of_1_2_12 : core.

  Lemma lemma1_of_1_2_13_aux1 :
    forall bs1 : list B,
    forall bs2 : ensemble B,
    isFilter bs2 ->
    forall n : nat,
    (forall b2 : B, In b2 bs1 -> member b2 (union (improveFilter bs2 n) (insertion (improveFilter bs2 n) n))) ->
    member (fold_right andB trueB bs1) (improveFilter bs2 n) \/ (exists b1 : B, In b1 bs1 /\ member b1 (insertion (improveFilter bs2 n) n)).
  Proof with eauto with *.
    induction bs1 as [| b1 bs1 IH]; simpl...
    intros bs2 H n H0.
    assert (H1 := lemma1_of_1_2_11 n bs2 H).
    assert (H2 : member b1 (improveFilter bs2 n) \/ member b1 (insertion (improveFilter bs2 n) n)) by now apply in_union_iff, H0; left.
    assert (H3 := leCBA_andB_fold_right bs1 (improveFilter bs2 n) H1).
    assert (H4 : forall b2 : B, In b2 bs1 -> member b2 (union (improveFilter bs2 n) (insertion (improveFilter bs2 n) n))) by firstorder.
    destruct (IH bs2 H n H4) as [H5 | [b2 [H5 H6]]].
    - destruct H2 as [H2 | H2].
      + left.
        apply (proj2 (proj2 H1) b1 (fold_right andB trueB bs1))...
      + right.
        exists b1...
    - right.
      exists b2...
  Qed.

  Local Hint Resolve lemma1_of_1_2_13_aux1 : core.

  Lemma falseB_isBottom :
    forall b : B,
    falseB =< b.
  Proof with eauto with *.
    rewrite leCBA_is...
  Qed.

  Local Hint Resolve falseB_isBottom : core.

  Lemma lemma1_of_1_2_13_aux2 :
    forall bs : ensemble B,
    forall n : nat,
    isSubsetOf (union (improveFilter bs n) (insertion (improveFilter bs n) n)) (insert (enumB n) (improveFilter bs n)).
  Proof with eauto with *.
    intros bs n b.
    rewrite in_union_iff, in_insert_iff.
    intros [H | H].
    - right...
    - inversion H; subst...
  Qed.

  Local Hint Resolve lemma1_of_1_2_13_aux2 : core.

  Lemma lemma1_of_1_2_13 :
    forall n : nat,
    forall bs : ensemble B,
    isFilter bs ->
    equiconsistent bs (improveFilter bs n).
  Proof with eauto with *.
    unfold equiconsistent.
    induction n as [| n IH]; simpl...
    intros bs H.
    assert (claim1 : isFilter (improveFilter bs n) /\ isSubsetOf (improveFilter bs n) (Cl (improveFilter bs n \cup insertion (improveFilter bs n) n))).
    { split.
      - apply lemma1_of_1_2_11...
      - transitivity (Cl (improveFilter bs n))...
    }
    revert claim1.
    rewrite IH...
    unfold isSubsetOf, inconsistent.
    intros [H0 H1].
    split.
    - intros [b [H2 H3]]...
    - intros [b [H2 H3]].
      inversion H2; subst.
      assert (claim2 : andB b (fold_right andB trueB bs1) == falseB).
      { rewrite H3, andB_commutative.
        apply falseB_zero_andB.
      }
      assert (claim3 : fold_right andB trueB bs1 == falseB).
      { rewrite H3 in H5.
        apply (leCBA_PartialOrder B_isCBA).
        split; [apply H5 | apply falseB_isBottom].
      }
      destruct (lemma1_of_1_2_13_aux1 bs1 bs H n H4) as [H6 | [b0 [H6 H7]]].
      + assert (H7 := proj1 (proj2 H0) (fold_right andB trueB bs1)).
        exists (andB b (fold_right andB trueB bs1))...
      + inversion H7; subst.
        assert (H9 : isSubsetOf (Cl (union (improveFilter bs n) (insertion (improveFilter bs n) n))) (Cl (insert (enumB n) (improveFilter bs n)))) by now apply fact4_of_1_2_8, lemma1_of_1_2_13_aux2.
        apply H8.
        exists (fold_right andB trueB bs1)...
  Qed.

  Local Hint Resolve lemma1_of_1_2_13 : core.

  Lemma lemma2_of_1_2_13 :
    forall bs : ensemble B,
    isFilter bs ->
    forall n1 : nat,
    forall n2 : nat,
    equiconsistent (improveFilter bs n1) (improveFilter bs n2).
  Proof with tauto.
    intros bs H n1 n2.
    assert (H0 : equiconsistent bs (improveFilter bs n1)) by now apply lemma1_of_1_2_13.
    assert (H1 : equiconsistent bs (improveFilter bs n2)) by now apply lemma1_of_1_2_13.
    unfold equiconsistent in *...
  Qed.

  Local Hint Resolve lemma2_of_1_2_13 : core.

  Inductive CompleteFilter : ensemble B -> ensemble B :=
  | in_CompleteFilter :
    forall n : nat,
    forall bs : ensemble B,
    forall b : B,
    member b (improveFilter bs n) ->
    member b (CompleteFilter bs)
  .

  Local Hint Constructors CompleteFilter : core.

  Lemma lemma3_of_1_2_13 :
    forall bs : ensemble B,
    isFilter bs ->
    equiconsistent bs (CompleteFilter bs).
  Proof with eauto.
    intros bs H.
    split.
    - intros [b [H0 H1]].
      assert (H2 := in_CompleteFilter 0).
      exists b...
    - intros [b [H0 H1]].
      inversion H0; subst.
      apply (lemma1_of_1_2_13 n bs H)...
  Qed.

  Local Hint Resolve lemma3_of_1_2_13 : core.

  Lemma theorem_of_1_2_14_aux1 :
    forall bs : ensemble B,
    isFilter bs ->
    forall n : nat,
    equiconsistent (CompleteFilter bs) (Cl (insert (enumB n) (CompleteFilter bs))) ->
    equiconsistent (improveFilter bs n) (Cl (insert (enumB n) (improveFilter bs n))).
  Proof with eauto with *.
    intros bs H n H0.
    split.
    - intros [b [H1 H2]].
      exists b.
      split.
      + apply fact3_of_1_2_8, in_insert_iff...
      + apply H2.
    - intros H1.
      assert (H2 := lemma1_of_1_2_13 n bs H).
      assert (H3 := lemma3_of_1_2_13 bs H). 
      assert (claim1 : inconsistent (Cl (insert (enumB n) (CompleteFilter bs)))).
      { apply (inconsistent_subset (Cl (insert (enumB n) (improveFilter bs n))))...
        apply fact4_of_1_2_8.
        intros b.
        do 2 rewrite in_insert_iff.
        intros [Heq | H4]...
      }
      assert (H4 := proj2 H0 claim1).
      now firstorder.
  Qed.

  Theorem theorem_of_1_2_14 :
    forall bs : ensemble B,
    isFilter bs ->
    isSubsetOf bs (CompleteFilter bs) /\ isFilter (CompleteFilter bs) /\ isComplete (CompleteFilter bs) /\ equiconsistent bs (CompleteFilter bs).
  Proof with eauto with *.
    intros bs H.
    assert (claim1 : isSubsetOf bs (CompleteFilter bs)) by exact (in_CompleteFilter 0 bs).
    assert (claim2 : forall b1 : B, forall b2 : B, member b1 (CompleteFilter bs) -> b1 =< b2 -> member b2 (CompleteFilter bs)).
    { intros b1 b2 H2 H3.
      inversion H2; subst.
      assert (H5 := lemma1_of_1_2_11 n bs H).
      apply (in_CompleteFilter n), (proj1 (proj2 H5) b1 b2)...
    }
    assert (claim3 : forall b1 : B, forall b2 : B, forall b : B, member b1 (CompleteFilter bs) -> member b2 (CompleteFilter bs) -> b == andB b1 b2 -> member b (CompleteFilter bs)).
    { intros b1 b2 b H0 H1 H2.
      inversion H0; subst.
      inversion H1; subst.
      rename n into n1, n0 into n2.
      assert (H5 : n1 <= n2 \/ n2 <= n1) by lia.
      destruct H5 as [H5 | H5].
      - assert (H6 := lemma1_of_1_2_11 n2 bs H).
        assert (H7 := lemma1_of_1_2_12 n1 n2 H5 bs b1 H3).
        apply (in_CompleteFilter n2), (proj2 (proj2 H6) b1 b2)...
      - assert (H6 := lemma1_of_1_2_11 n1 bs H).
        assert (H7 := lemma1_of_1_2_12 n2 n1 H5 bs b2 H4).
        apply (in_CompleteFilter n1), (proj2 (proj2 H6) b1 b2)...
    }
    assert (claim4 : isFilter (CompleteFilter bs)).
    { split.
      - destruct (proj1 H) as [b0 H0].
        exists b0...
      - split...
    }
    assert (claim5 : isComplete (CompleteFilter bs)).
    { intros b H0.
      destruct (enumB_surjective b) as [n Heq].
      subst.
      assert (H1 := theorem_of_1_2_14_aux1 bs H n H0).
      exists (S n).
      simpl.
      exists (cons (enumB n) nil).
      - intros b1 [Heq | []]; subst.
        apply in_union_iff...
      - simpl fold_right...
    }
    assert (claim6 : equiconsistent bs (CompleteFilter bs)) by now apply lemma3_of_1_2_13...
  Qed.

  Definition isUltraFilter : ensemble B -> Prop :=
    fun bs : ensemble B =>
    isFilter bs /\ (forall bs' : ensemble B, isFilter bs' -> equiconsistent bs bs' -> isSubsetOf bs bs' -> isSubsetOf bs' bs)
  .

  Lemma corollary_of_1_2_16_aux1 :
    forall bs1 : ensemble B,
    isFilter bs1 ->
    isSubsetOf bs1 (CompleteFilter bs1) ->
    isFilter (CompleteFilter bs1) ->
    isComplete (CompleteFilter bs1) ->
    equiconsistent bs1 (CompleteFilter bs1) ->
    forall bs2 : ensemble B,
    isFilter bs2 ->
    equiconsistent (CompleteFilter bs1) bs2 ->
    isSubsetOf (CompleteFilter bs1) bs2 ->
    forall b : B,
    member b bs2 ->
    inconsistent (Cl (insert b (CompleteFilter bs1))) ->
    inconsistent (Cl (insert b bs2)).
  Proof with eauto with *.
    intros bs1 H_filter1 H H0 H1 H2 bs2 H_filter2 H3 H4 b H5.
    assert (claim1 : isSubsetOf (insert b (CompleteFilter bs1)) (insert b bs2)).
    { intros b'.
      do 2 rewrite in_insert_iff.
      intros [Heq | H7]; [subst | right]... 
    }
    intros [b' [H6 H7]].
    assert (H8 : isSubsetOf (Cl (insert b (CompleteFilter bs1))) (Cl (insert b bs2))) by apply fact4_of_1_2_8, claim1.
    exists b'...
  Qed.

  Lemma corollary_of_1_2_16_aux2 :
    forall bs1 : ensemble B,
    isFilter bs1 ->
    isSubsetOf bs1 (CompleteFilter bs1) ->
    isFilter (CompleteFilter bs1) ->
    isComplete (CompleteFilter bs1) ->
    equiconsistent bs1 (CompleteFilter bs1) ->
    forall bs2 : ensemble B,
    isFilter bs2 ->
    equiconsistent (CompleteFilter bs1) bs2 ->
    isSubsetOf (CompleteFilter bs1) bs2 ->
    forall b : B,
    member b bs2 ->
    equiconsistent (CompleteFilter bs1) (Cl (insert b (CompleteFilter bs1))).
  Proof with eauto with *.
    intros bs1 H_filter1 H H0 H1 H2 bs2 H_filter2 H3 H4 b H5.
    assert (claim1 : isSubsetOf (Cl (insert b bs2)) (Cl bs2)).
    { apply fact4_of_1_2_8.
      intros b'.
      rewrite in_insert_iff.
      intros [Heq | H6]; [subst | apply H6]...
    }
    split.
    - intros [b' [H6 H7]].
      exists b'.
      split.
      + apply fact3_of_1_2_8, in_union_iff...
      + apply H7.
    - intros H6.
      destruct (corollary_of_1_2_16_aux1 bs1 H_filter1 H H0 H1 H2 bs2 H_filter2 H3 H4 b H5 H6) as [b' [H7 H8]].
      apply (proj2 H3).
      exists b'.
      split.
      + apply fact5_of_1_2_8...
      + apply H8.
  Qed.

  Corollary corollary_of_1_2_16 :
    forall bs : ensemble B,
    isFilter bs ->
    isUltraFilter (CompleteFilter bs).
  Proof with eauto with *.
    intros bs1 H_filter1.
    destruct (theorem_of_1_2_14 bs1 H_filter1) as [H [H0 [H1 H2]]].
    split.
    - apply H0.
    - intros bs2 H_filter2 H3 H4 b H5.
      enough (claim1 : equiconsistent (CompleteFilter bs1) (Cl (insert b (CompleteFilter bs1)))) by apply H1, claim1.
      apply (corollary_of_1_2_16_aux2 bs1 H_filter1 H H0 H1 H2 bs2 H_filter2 H3 H4 b H5).
  Qed.

  End Section2OfChapter1.

End CountableBooleanAlgebra.

Module PLogic.

  Import ListNotations MyUtilities BasicSetoidTheory MyEnsemble BasicPosetTheory MyEnsembleNova CountableBooleanAlgebra.

End PLogic.
