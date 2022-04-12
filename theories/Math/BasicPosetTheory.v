Require Import Coq.Classes.RelationClasses.
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
  Global Hint Resolve eqProp_Reflexive eqProp_Symmetric eqProp_Transitive : poset_hints.
  Global Hint Resolve leProp_Reflexive leProp_Transitive eqProp_implies_leProp leProp_Antisymmetric : poset_hints.
  Global Hint Resolve member_eq_leProp_with_impl member_eq_eqProp_with_iff : poset_hints.
  Global Hint Resolve in_unions_iff : poset_hints.

  Global Add Parametric Morphism (D : Type) (requiresPoset : isPoset D) :
    (@UpperBoundsOf D requiresPoset) with signature (eqProp ==> eqProp)
    as UpperBoundsOf_compatWith_eqProp_wrtEnsembles.
  Proof with eauto with *.
    intros X Y X_eq_Y z. split; intros H_upper_bound.
    - intros y y_in_Y. eapply H_upper_bound. unnw. rewrite -> X_eq_Y...
    - intros x x_in_X. eapply H_upper_bound. unnw. rewrite <- X_eq_Y...
  Qed.

  Global Hint Resolve UpperBoundsOf_compatWith_eqProp_wrtEnsembles : poset_hints.

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

End BasicPosetTheory.
