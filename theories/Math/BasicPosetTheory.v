Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.

Module BasicPosetTheory.

  Import MathProps MathNotations MathClasses.

  Global Notation " f '\monotonic' " := (preserves_leProp1 f)
    (in custom math_form_scope at level 6, f custom math_term_scope at level 1, no associativity).
  Global Notation " '('  X  ')↑' " := (UpperBoundsOf X)
    (in custom math_form_scope at level 6, X custom math_term_scope at level 5).
  Global Notation " '\sup' X '=' sup_X " := (isSupremumOf sup_X X)
    (in custom math_form_scope at level 6, sup_X custom math_term_scope at level 1, X custom math_term_scope at level 5).
  Global Notation " '('  X  ')↓' " := (LowerBoundsOf X)
    (in custom math_form_scope at level 6, X custom math_term_scope at level 5).
  Global Notation " '\inf' X '=' inf_X " := (isInfimumOf inf_X X)
    (in custom math_form_scope at level 6, inf_X custom math_term_scope at level 1, X custom math_term_scope at level 5).
  Global Notation " '\{' '\sup' Y ':' X '∈' Xs '\}' " := (ensemble_bind Xs (fun X => fun sup => isSupremumOf sup Y))
    (in custom math_term_scope at level 0, Xs custom math_term_scope at level 5, X name, Y custom math_term_scope at level 1, no associativity).
  Global Notation " '\{' '\inf' Y ':' X '∈' Xs '\}' " := (ensemble_bind Xs (fun X => fun inf => isInfimumOf inf Y))
    (in custom math_term_scope at level 0, Xs custom math_term_scope at level 5, X name, Y custom math_term_scope at level 1, no associativity).

  Global Create HintDb poset_hints.
  Global Hint Unfold REFERENCE_HOLDER member UpperBoundsOf LowerBoundsOf isSupremumOf isInfimumOf isDirectedSubset : poset_hints.
  Global Hint Resolve member_eq_leProp_with_impl member_eq_eqProp_with_iff : poset_hints.

  Global Add Parametric Morphism (D : Type) (requiresPoset : isPoset D) :
    (UpperBoundsOf (requiresPoset := requiresPoset)) with signature (eqProp ==> eqProp)
    as UpperBoundsOf_compatWith_eqProp_wrtEnsembles.
  Proof with eauto with *.
    intros X Y X_eq_Y z. split; intros H_upper_bound.
    - intros y y_in_Y. eapply H_upper_bound. unnw. rewrite -> X_eq_Y...
    - intros x x_in_X. eapply H_upper_bound. unnw. rewrite <- X_eq_Y...
  Qed.

  Global Add Parametric Morphism (D : Type) (requiresPoset : isPoset D) :
    (UpperBoundsOf (requiresPoset := requiresPoset)) with signature (eqProp ==> eqProp)
    as LowerBoundsOf_compatWith_eqProp_wrtEnsembles.
  Proof with eauto with *.
    intros X Y X_eq_Y z. split; intros H_lower_bound.
    - intros y y_in_Y. eapply H_lower_bound. unnw. rewrite -> X_eq_Y...
    - intros x x_in_X. eapply H_lower_bound. unnw. rewrite <- X_eq_Y...
  Qed.

  Global Hint Resolve UpperBoundsOf_compatWith_eqProp_wrtEnsembles LowerBoundsOf_compatWith_eqProp_wrtEnsembles : poset_hints.

  Section BASIC_FACTS_ON_SUPREMUM.

  Context {D : Type} {requiresPoset : isPoset D}.

  Lemma Supremum_monotonic_wrtEnsembles (X1 : ensemble D) (X2 : ensemble D) (sup_X1 : D) (sup_X2 : D)
    (sup_X1_isSupremumOf_X1 : isSupremumOf sup_X1 X1)
    (sup_X2_isSupremumOf_X2 : isSupremumOf sup_X2 X2)
    (X1_isSubsetOf_X2 : isSubsetOf X1 X2)
    : sup_X1 =< sup_X2.
  Proof.
    eapply sup_X1_isSupremumOf_X1; ii.
    eapply sup_X2_isSupremumOf_X2; eauto with *.
  Qed.

  Local Hint Resolve Supremum_monotonic_wrtEnsembles : poset_hints.

  Lemma Supremum_preserves_eqProp_wrtEnsembles (X1 : ensemble D) (X2 : ensemble D) (sup_X1 : D) (sup_X2 : D)
    (sup_X1_isSupremumOf_X1 : isSupremumOf sup_X1 X1)
    (sup_X2_isSupremumOf_X2 : isSupremumOf sup_X2 X2)
    (X1_eq_X2 : X1 == X2)
    : sup_X1 == sup_X2.
  Proof.
    pose proof (eqProp_implies_leProp X1 X2 X1_eq_X2) as claim1. symmetry in X1_eq_X2.
    pose proof (eqProp_implies_leProp X2 X1 X1_eq_X2) as claim2. eapply leProp_Antisymmetric; eauto with *.
  Qed.

  Local Hint Resolve Supremum_preserves_eqProp_wrtEnsembles : poset_hints.

  Lemma Supremum_congruence (sup_X : D) (sup_Y : D) (X : ensemble D) (Y : ensemble D)
    (sup_X_eq_sup_Y : sup_X == sup_Y)
    (X_eq_Y : X == Y)
    (x_isSupremumOf_X : isSupremumOf sup_X X)
    : isSupremumOf sup_Y Y.
  Proof with eauto with *.
    intros z. unnw. rewrite <- sup_X_eq_sup_Y. split.
    - intros sup_X_le_z. rewrite <- X_eq_Y. eapply x_isSupremumOf_X...
    - intros z_isUpperBoundOf_Y. eapply x_isSupremumOf_X. unnw. rewrite -> X_eq_Y...
  Qed.

  Local Hint Resolve Supremum_congruence : poset_hints.

  Global Add Parametric Morphism :
    (@isSupremumOf D requiresPoset) with signature (eqProp ==> eqProp ==> iff)
    as Supremum_compatWith_eqProp_wrtEnsembles.
  Proof. iis; eauto with *. Qed.

  Definition SupremumMap (Xs : ensemble (ensemble D)) : ensemble D :=
    fun sup_X_i : D => exists X_i : ensemble D, member X_i Xs /\ isSupremumOf sup_X_i X_i
  .

  Lemma SupremumMap_unfold (Xs : ensemble (ensemble D))
    : SupremumMap Xs = bind Xs (fun X_i : ensemble D => fun sup_X_i : D => isSupremumOf sup_X_i X_i).
  Proof. reflexivity. Qed.

  Lemma in_SupremumMap_iff (Xs : ensemble (ensemble D)) (sup : D)
    : member sup (SupremumMap Xs) <-> (exists X_i : ensemble D, member X_i Xs /\ isSupremumOf sup X_i).
  Proof. reflexivity. Qed.

  Lemma SupremumOfSupremumMap_isGreaterThan (sup : D) (Xs : ensemble (ensemble D)) (sup_X : D) (X : ensemble D)
    (sup_isSupremumOf : isSupremumOf sup (SupremumMap Xs))
    (X_in_Xs : member X Xs)
    (sup_X_isSupremumOf_X : isSupremumOf sup_X X)
    : sup_X =< sup.
  Proof with eauto with *. eapply sup_isSupremumOf... eapply in_SupremumMap_iff... Qed.

  Local Hint Resolve SupremumOfSupremumMap_isGreaterThan : poset_hints.

  Lemma SupremumOfSupremumMap_isSupremumOfUnions (Xs : ensemble (ensemble D)) (sup : D)
    (SUP_EXISTS : forall X : ensemble D, << H_IN : member X Xs >> -> exists sup_X : D, isSupremumOf sup_X X)
    : isSupremumOf sup (SupremumMap Xs) <-> isSupremumOf sup (unions Xs).
  Proof with eauto with *.
    split; intros H_supremum z; split; ii; desnw.
    - apply in_unions_iff in H_IN. destruct H_IN as [X_i [x_in_X_i X_i_in_Xs]].
      destruct (SUP_EXISTS X_i X_i_in_Xs) as [sup_X_i sup_X_i_isSupremumOf_X_i].
      transitivity (sup_X_i).
      + eapply sup_X_i_isSupremumOf_X_i...
      + transitivity (sup)...
    - eapply H_supremum. intros sup_X_i sup_X_i_in_SupremumMap.
      apply in_SupremumMap_iff in sup_X_i_in_SupremumMap.
      destruct sup_X_i_in_SupremumMap as [X_i [X_i_in_Xs sup_X_i_isSupremumOf_X_i]].
      eapply sup_X_i_isSupremumOf_X_i. ii. desnw. eapply UPPER_BOUND. eapply in_unions_iff...
    - eapply in_SupremumMap_iff in H_IN. destruct H_IN as [X [X_in_Xs x_isSupremumOf_X]].
      rename x into sup_X. enough (to_show : sup_X =< sup) by now transitivity (sup).
      eapply x_isSupremumOf_X. ii; desnw. eapply H_supremum... eapply in_unions_iff...
    - eapply H_supremum. ii; desnw. apply in_unions_iff in H_IN.
      destruct H_IN as [X [x_in_X X_in_Xs]]. destruct (SUP_EXISTS X X_in_Xs) as [sup_X sup_X_isSupremumOf_X].
      transitivity (sup_X).
      + eapply sup_X_isSupremumOf_X...
      + eapply UPPER_BOUND, in_SupremumMap_iff...
  Qed.

  Local Hint Resolve SupremumOfSupremumMap_isGreaterThan : poset_hints.

  Proposition InfimumOfUpperBound_isSupremum (sup_X : D) (X : ensemble D)
    (sup_X_isInfimumOfUpperBound : isInfimumOf sup_X (UpperBoundsOf X))
    : isSupremumOf sup_X X.
  Proof.
    intros z. split; ii; desnw.
    - transitivity (sup_X); trivial.
      eapply sup_X_isInfimumOfUpperBound. unnw.
      intros upper_bound upper_bound_in. unnw.
      exact (upper_bound_in x H_IN).
    - unnw. eapply sup_X_isInfimumOfUpperBound; eauto with *.
  Qed.

  End BASIC_FACTS_ON_SUPREMUM.

  Global Hint Resolve Supremum_monotonic_wrtEnsembles : poset_hints.
  Global Hint Resolve Supremum_preserves_eqProp_wrtEnsembles : poset_hints.
  Global Hint Resolve Supremum_congruence : poset_hints.
  Global Hint Resolve Supremum_compatWith_eqProp_wrtEnsembles : poset_hints.

  Section LEXICOGRAPHICAL_ORDER.

  Import ListNotations.

  Context {A : Type} {requiresPoset : isPoset A}.

  Variable compare : A -> A -> comparison.

  Fixpoint lex_compare (xs : list A) (ys : list A) {struct xs} : comparison :=
    match xs, ys with
    | [], [] => Eq
    | [], y :: ys => Lt
    | x :: xs, [] => Gt
    | x :: xs, y :: ys =>
      match compare x y with
      | Lt => Lt
      | Eq => lex_compare xs ys
      | Gt => Gt
      end
    end
  .

  Definition lex_eq (lhs : list A) (rhs : list A) : Prop :=
    lex_compare lhs rhs = Eq
  .

  Definition lex_le (lhs : list A) (rhs : list A) : Prop :=
    lex_compare lhs rhs = Lt \/ lex_compare lhs rhs = Eq
  .

  Hypothesis compare_spec_LT : forall lhs : A, forall rhs : A, compare lhs rhs = Lt -> lhs =< rhs /\ ~ lhs == rhs.

  Hypothesis compare_spec_EQ : forall lhs : A, forall rhs : A, compare lhs rhs = Eq -> lhs == rhs.

  Hypothesis compare_spec_GT : forall lhs : A, forall rhs : A, compare lhs rhs = Gt -> rhs =< lhs /\ ~ lhs == rhs.

  Lemma compare_spec (lhs : A) (rhs : A) :
    match compare lhs rhs with
    | Lt => lhs =< rhs /\ ~ lhs == rhs
    | Eq => lhs == rhs
    | Gt => rhs =< lhs /\ ~ lhs == rhs
    end.
  Proof. destruct (compare lhs rhs) eqn: H_compare_result; eauto with *. Qed.

  Local Polymorphic Instance lex_eq_Equivalence
    : Equivalence lex_eq.
  Proof with discriminate || eauto with *.
    unfold lex_eq. split.
    - intros xs1; induction xs1 as [ | x1 xs1 IH]; simpl...
      pose proof (claim1 := compare_spec x1 x1).
      destruct (compare x1 x1) eqn: H_compare_result1...
      all: contradiction (proj2 claim1)...
    - intros xs1 xs2; revert xs1 xs2; induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl...
      pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x1).
      destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x1) eqn: H_compare_result2...
      all: contradiction (proj2 claim2)...
    - intros xs1 xs2 xs3; revert xs1 xs3; induction xs2 as [ | x2 xs2 IH]; destruct xs1 as [ | x1 xs1]; destruct xs3 as [ | x3 xs3]; simpl...
      pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x3); pose proof (claim3 := compare_spec x1 x3).
      destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x3) eqn: H_compare_result2; destruct (compare x1 x3) eqn: H_compare_result3...
      all: contradiction (proj2 claim3)...
  Qed.

  Local Polymorphic Instance listPointwiseEquivalence : isSetoid (list A) :=
    { eqProp := lex_eq
    ; eqProp_Equivalence := lex_eq_Equivalence
    }
  .

  Local Polymorphic Instance lex_le_PreOrder
    : PreOrder lex_le.
  Proof with discriminate || eauto with *.
    assert (lemma1 : forall x1 : A, forall x2 : A, x1 =< x2 -> x2 =< x1 -> x1 == x2). { ii... }
    assert (lemma2 : forall x1 : A, forall x2 : A, x1 == x2 -> x1 =< x2). { ii... }
    assert (lemma3 : forall x1 : A, forall x2 : A, x1 == x2 -> x2 =< x1). { ii... }
    unfold lex_le. split.
    - intros xs1; right. apply lex_eq_Equivalence.
    - intros xs1 xs2 xs3; revert xs1 xs3; induction xs2 as [ | x2 xs2 IH]; destruct xs1 as [ | x1 xs1]; destruct xs3 as [ | x3 xs3]; simpl...
      intros [H_false | H_false]...
      pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x3); pose proof (claim3 := compare_spec x1 x3); pose proof (claim4 := IH xs1 xs3).
      destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x3) eqn: H_compare_result2; destruct (compare x1 x3) eqn: H_compare_result3...
      + contradiction (proj2 claim3)...
      + contradiction (proj2 claim2)...
      + contradiction (proj2 claim3); apply lemma1; [transitivity x2 | exact (proj1 claim3)]. apply lemma2... exact (proj1 claim2).
      + contradiction (proj2 claim2)...
      + contradiction (proj2 claim1)...
      + contradiction (proj2 claim3); apply lemma1; [transitivity x2 | exact (proj1 claim3)]. exact (proj1 claim1). apply lemma2...
      + contradiction (proj2 claim1); apply lemma1; [exact (proj1 claim1) | transitivity x3]. exact (proj1 claim2). apply lemma2...
      + contradiction (proj2 claim1); apply lemma1; [exact (proj1 claim1) | transitivity x3]. exact (proj1 claim2). exact (proj1 claim3).
      + intros ? [? | ?]...
      + intros [? | ?]...
      + intros [? | ?]...
      + intros [? | ?]...
  Qed.

  Lemma lex_le_flip_spec (lhs : list A) (rhs : list A) :
    match lex_compare lhs rhs with
    | Lt => lex_compare rhs lhs = Gt
    | Eq => lex_compare rhs lhs = Eq
    | Gt => lex_compare rhs lhs = Lt
    end.
  Proof with discriminate || eauto with *.
    revert lhs rhs.
    assert (lemma1 : forall x1 : A, forall x2 : A, x1 =< x2 -> x2 =< x1 -> x1 == x2). { ii... }
    assert (lemma2 : forall x1 : A, forall x2 : A, x1 == x2 -> x1 =< x2). { ii... }
    assert (lemma3 : forall x1 : A, forall x2 : A, x1 == x2 -> x2 =< x1). { ii... }
    assert (lemma4 : forall xs1 : list A, forall xs2 : list A, lex_compare xs1 xs2 = Lt <-> lex_compare xs2 xs1 = Gt).
    { induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl... split...
      pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x1); pose proof (claim3 := IH xs2).
      destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x1) eqn: H_compare_result2...
      - contradiction (proj2 claim2)...
      - contradiction (proj2 claim2)...
      - contradiction (proj2 claim1)...
      - contradiction (proj2 claim1). apply lemma1; [exact (proj1 claim1) | exact (proj1 claim2)].
      - contradiction (proj2 claim1)...
      - contradiction (proj2 claim1). apply lemma1; [exact (proj1 claim2) | exact (proj1 claim1)].
    }
    assert (lemma5 : forall xs1 : list A, forall xs2 : list A, lex_compare xs1 xs2 = Eq <-> lex_compare xs2 xs1 = Eq).
    { induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl... split... split...
      pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x1); pose proof (claim3 := IH xs2).
      destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x1) eqn: H_compare_result2...
      - contradiction (proj2 claim2)...
      - contradiction (proj2 claim2)...
      - contradiction (proj2 claim1)...
      - split...
      - contradiction (proj2 claim1)...
      - split...
    }
    assert (lemma6 : forall xs1 : list A, forall xs2 : list A, lex_compare xs1 xs2 = Gt <-> lex_compare xs2 xs1 = Lt) by firstorder.
    intros lhs rhs; destruct (lex_compare lhs rhs) eqn: H_compare_result; now firstorder.
  Qed.

  Local Polymorphic Instance lex_le_PartialOrder
    : PartialOrder lex_eq lex_le.
  Proof with discriminate || eauto with *.
    intros xs1 xs2; cbn. unfold flip, lex_eq, lex_le.
    pose proof (claim1 := lex_le_flip_spec xs1 xs2).
    destruct (lex_compare xs1 xs2) eqn: H_compare_result.
    - split...
    - split... intros [? [H_false | H_false]].
      all: rewrite H_false in claim1...
    - split... intros [[? | ?] ?]...
  Qed.

  Local Polymorphic Instance listLexicographicalOrder : isPoset (list A) :=
    { leProp := lex_le
    ; Poset_requiresSetoid := listPointwiseEquivalence
    ; leProp_PreOrder := lex_le_PreOrder
    ; leProp_PartialOrder := lex_le_PartialOrder
    }
  .

  End LEXICOGRAPHICAL_ORDER.

  Section SCOTT_TOPOLOGY.

  End SCOTT_TOPOLOGY.

End BasicPosetTheory.
