Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.

Module BasicPosetTheory.

  Import MathProps MathNotations MathClasses.

  Global Notation " '\sup' X '=' sup_X " := (isSupremumOf sup_X X)
    (in custom math_form_scope at level 6, sup_X custom math_term_scope at level 1, X custom math_term_scope at level 5).
  Global Notation " x '∈' '('  X ')↑' " := (isUpperBoundOf x X)
    (in custom math_form_scope at level 6, x custom math_term_scope at level 1, X custom math_term_scope at level 5).
  Global Notation " f '\monotonic' " := (preserves_leProp1 f)
    (in custom math_form_scope at level 6, f custom math_term_scope at level 1, no associativity).
  Global Notation " '\{' '\sup' Y ':' X '∈' Xs '\}' " := (ensemble_bind Xs (fun X => fun sup_Y => isSupremumOf sup_Y Y))
    (in custom math_term_scope at level 0, Xs custom math_term_scope at level 5, X name, Y custom math_term_scope at level 1, no associativity).

  Global Create HintDb poset_hints.
  Global Hint Unfold REFERENCE_HOLDER isUpperBoundOf isSupremumOf isDirectedSubset : poset_hints.
  Global Hint Resolve eqProp_Reflexive eqProp_Symmetric eqProp_Transitive : poset_hints.
  Global Hint Resolve leProp_Reflexive leProp_Transitive eqProp_implies_leProp leProp_Antisymmetric : poset_hints.
  Global Hint Resolve member_eq_leProp_with_impl member_eq_eqProp_with_iff : poset_hints.

  Section BASIC_FACTS_ON_SUPREMUM.

  Context {D : Type} {requiresPoset : isPoset D}.

  Global Add Parametric Morphism :
    (@isUpperBoundOf D requiresPoset) with signature (eqProp ==> eqProp ==> iff)
    as UpperBound_compatWith_eqProp_WrtEnsembles.
  Proof with eauto with *.
    intros x y x_eq_y X Y X_eq_Y. split; intros H_upper_bound.
    - intros z z_in_Y. rewrite <- x_eq_y. eapply H_upper_bound. unnw. rewrite -> X_eq_Y...
    - intros z z_in_X. rewrite -> x_eq_y. eapply H_upper_bound. unnw. rewrite <- X_eq_Y...
  Qed.

  Local Hint Resolve UpperBound_compatWith_eqProp_WrtEnsembles : poset_hints.

  Lemma supremum_monotonic_WrtEnsembles (X1 : ensemble D) (X2 : ensemble D) (sup_X1 : D) (sup_X2 : D)
    (sup_X1_isSupremumOf_X1 : $$ \sup X1 = sup_X1 $$)
    (sup_X2_isSupremumOf_X2 : $$ \sup X2 = sup_X2 $$)
    (X1_isSubsetOf_X2 : $$ X1 ⊆ X2 $$)
    : $$ sup_X1 ≦ sup_X2 $$.
  Proof.
    eapply sup_X1_isSupremumOf_X1; ii.
    eapply sup_X2_isSupremumOf_X2; eauto with *.
  Qed.

  Local Hint Resolve supremum_monotonic_WrtEnsembles : poset_hints.

  Lemma supremum_preserves_eqProp_WrtEnsembles (X1 : ensemble D) (X2 : ensemble D) (sup_X1 : D) (sup_X2 : D)
    (sup_X1_isSupremumOf_X1 : $$ \sup X1 = sup_X1 $$)
    (sup_X2_isSupremumOf_X2 : $$ \sup X2 = sup_X2 $$)
    (X1_eq_X2 : $$ X1 ≡ X2 $$)
    : $$ sup_X1 ≡ sup_X2 $$.
  Proof.
    pose proof (eqProp_implies_leProp X1 X2 X1_eq_X2) as claim1. symmetry in X1_eq_X2.
    pose proof (eqProp_implies_leProp X2 X1 X1_eq_X2) as claim2. eapply leProp_Antisymmetric; eauto with *.
  Qed.

  Local Hint Resolve supremum_preserves_eqProp_WrtEnsembles : poset_hints.

  Lemma Supremum_congruence (sup_X : D) (sup_Y : D) (X : ensemble D) (Y : ensemble D)
    (sup_X_eq_sup_Y : $$ sup_X ≡ sup_Y $$)
    (X_eq_Y : $$ X ≡ Y $$)
    (x_isSupremumOf_X : $$ \sup X = sup_X $$)
    : $$ \sup Y = sup_Y $$.
  Proof with eauto with *.
    intros z. unnw. rewrite <- sup_X_eq_sup_Y. split.
    - intros sup_X_le_z. rewrite <- X_eq_Y. eapply x_isSupremumOf_X...
    - intros z_isUpperBoundOf_Y. eapply x_isSupremumOf_X. unnw. rewrite -> X_eq_Y...
  Qed.

  Local Hint Resolve Supremum_congruence : poset_hints.

  Global Add Parametric Morphism :
    (@isSupremumOf D requiresPoset) with signature (eqProp ==> eqProp ==> iff)
    as Supremum_compatWith_eqProp_WrtEnsembles.
  Proof. iis; eauto with *. Qed.

  Lemma Supremum_in_SupremumMap (X : ensemble D) (sup_X : D) (Xs : ensemble (ensemble D))
    (sup_X_isSupremumOf_X : $$ \sup X = sup_X $$)
    (X_in_Xs : $$ X ∈ Xs $$)
    : $$ sup_X ∈ \{ \sup X_i : X_i ∈ Xs \} $$.
  Proof. exists (X); split; [exact (X_in_Xs) | exact (sup_X_isSupremumOf_X)]. Qed.

  End BASIC_FACTS_ON_SUPREMUM.

  Global Hint Resolve UpperBound_compatWith_eqProp_WrtEnsembles : poset_hints.
  Global Hint Resolve supremum_preserves_eqProp_WrtEnsembles : poset_hints.
  Global Hint Resolve supremum_preserves_eqProp_WrtEnsembles : poset_hints.
  Global Hint Resolve Supremum_congruence : poset_hints.
  Global Hint Resolve Supremum_congruence : poset_hints.

End BasicPosetTheory.
