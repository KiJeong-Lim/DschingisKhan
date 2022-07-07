Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeUtil.

Module BasicPosetTheory.

  Import ListNotations MathProps MathNotations MathClasses.

  Lemma leProp_unfold {D : Type} {requiresPoset : isPoset D}
    : forall x : D, forall y : D, x =< y <-> (forall z : D, z =< x -> z =< y).
  Proof. exact (proj1 (PreOrder_iff leProp) (@leProp_PreOrder D requiresPoset)). Qed.

  Definition isMonotonicMap {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} (f : dom -> cod) : Prop :=
    forall x : dom, forall x' : dom, forall x_le_x' : x =< x', f x =< f x'
  .

  Lemma isMonotonicMap_iff_preserves_leProp1 {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} (f : dom -> cod)
    : isMonotonicMap f <-> preserves_leProp1 f.
  Proof. reflexivity. Qed.

  Global Notation " f '\monotonic' " := (preserves_leProp1 f)
    (in custom math_form_scope at level 6, f custom math_term_scope at level 1, no associativity).
  Global Notation " '('  X  ')↑' " := (UpperBoundsOf X)
    (in custom math_form_scope at level 0, X custom math_term_scope at level 5).
  Global Notation " sup_X '=' '\sup' X " := (isSupremumOf sup_X X)
    (in custom math_form_scope at level 6, sup_X custom math_term_scope at level 1, X custom math_term_scope at level 5).
  Global Notation " '('  X  ')↓' " := (LowerBoundsOf X)
    (in custom math_form_scope at level 0, X custom math_term_scope at level 5).
  Global Notation " inf_X '=' '\inf' X " := (isInfimumOf inf_X X)
    (in custom math_form_scope at level 6, inf_X custom math_term_scope at level 1, X custom math_term_scope at level 5).
  Global Notation " '\{' '\sup' Y ':' X '∈' Xs '\}' " := (ensemble_bind Xs (fun X => fun sup => isSupremumOf sup Y))
    (in custom math_term_scope at level 0, Xs custom math_term_scope at level 5, X pattern, Y custom math_term_scope at level 1, no associativity).
  Global Notation " '\{' '\inf' Y ':' X '∈' Xs '\}' " := (ensemble_bind Xs (fun X => fun inf => isInfimumOf inf Y))
    (in custom math_term_scope at level 0, Xs custom math_term_scope at level 5, X pattern, Y custom math_term_scope at level 1, no associativity).

  Create HintDb poset_hints.
  Global Hint Unfold REFERENCE_HOLDER member UpperBoundsOf LowerBoundsOf isSupremumOf isInfimumOf isMonotonicMap : poset_hints.
  Global Hint Resolve member_eq_leProp_with_impl member_eq_eqProp_with_iff leProp_lifted1 leProp_unfold : poset_hints.

  Global Add Parametric Morphism {D : Type} (requiresPoset : isPoset D) :
    (UpperBoundsOf (requiresPoset := requiresPoset)) with signature (eqProp ==> eqProp)
    as UpperBoundsOf_compatWith_eqProp_wrtEnsembles.
  Proof with eauto with *.
    intros X Y X_eq_Y z. split; intros H_upper_bound.
    - intros y y_in_Y. eapply H_upper_bound. unnw. rewrite -> X_eq_Y...
    - intros x x_in_X. eapply H_upper_bound. unnw. rewrite <- X_eq_Y...
  Qed.

  Global Add Parametric Morphism {D : Type} (requiresPoset : isPoset D) :
    (LowerBoundsOf (requiresPoset := requiresPoset)) with signature (eqProp ==> eqProp)
    as LowerBoundsOf_compatWith_eqProp_wrtEnsembles.
  Proof with eauto with *.
    intros X Y X_eq_Y z. split; intros H_lower_bound.
    - intros y y_in_Y. eapply H_lower_bound. unnw. rewrite -> X_eq_Y...
    - intros x x_in_X. eapply H_lower_bound. unnw. rewrite <- X_eq_Y...
  Qed.

  Global Hint Resolve UpperBoundsOf_compatWith_eqProp_wrtEnsembles LowerBoundsOf_compatWith_eqProp_wrtEnsembles monotonic_guarantees_leProp_lifted1 monotonic_guarantees_leProp_lifted2 monotonic_guarantees_eqProp_lifted1 monotonic_guarantees_eqProp_lifted2 : poset_hints.

  Section BASIC_FACTS_ON_SUPREMUM.

  Context {D : Type} {requiresPoset : isPoset D}.

  Lemma Supremum_isInfimumOf_itsUpperBounds (X : ensemble D) (q : D)
    (q_isSupremumOf_X : isSupremumOf q X)
    : isInfimumOf q (fun x : D => q =< x).
  Proof with eauto with *.
    intros d. unnw. split.
    - intros d_le_q x q_le_x. rewrite d_le_q...
    - intros d_in. eapply d_in, q_isSupremumOf_X.
      ii; desnw. eapply q_isSupremumOf_X...
  Qed.

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

  Lemma Supremum_unique (X1 : ensemble D) (X2 : ensemble D) (sup_X1 : D) (sup_X2 : D)
    (sup_X1_isSupremumOf_X1 : isSupremumOf sup_X1 X1)
    (sup_X2_isSupremumOf_X2 : isSupremumOf sup_X2 X2)
    (X1_eq_X2 : X1 == X2)
    : sup_X1 == sup_X2.
  Proof.
    pose proof (eqProp_implies_leProp X1 X2 X1_eq_X2) as claim1. symmetry in X1_eq_X2.
    pose proof (eqProp_implies_leProp X2 X1 X1_eq_X2) as claim2. eapply leProp_Antisymmetric; eauto with *.
  Qed.

  Local Hint Resolve Supremum_unique : poset_hints.

  Lemma Supremum_congruence (sup_X : D) (sup_Y : D) (X : ensemble D) (Y : ensemble D)
    (sup_X_eq_sup_Y : sup_X == sup_Y)
    (X_eq_Y : X == Y)
    (sup_X_isSupremumOf_X : isSupremumOf sup_X X)
    : isSupremumOf sup_Y Y.
  Proof with eauto with *.
    intros z. unnw. rewrite <- sup_X_eq_sup_Y. split.
    - intros sup_X_le_z. rewrite <- X_eq_Y. eapply sup_X_isSupremumOf_X...
    - intros z_isUpperBoundOf_Y. eapply sup_X_isSupremumOf_X. unnw. rewrite -> X_eq_Y...
  Qed.

  Local Hint Resolve Supremum_congruence : poset_hints.

  Global Add Parametric Morphism :
    (@isSupremumOf D requiresPoset) with signature (eqProp ==> eqProp ==> iff)
    as Supremum_compatWith_eqProp_wrtEnsembles.
  Proof. iis; eauto with *. Qed.

  Definition MapSuprema (Xs : ensemble (ensemble D)) : ensemble D :=
    bind Xs (fun X_i : ensemble D => fun sup_X_i : D => isSupremumOf sup_X_i X_i)
  .

  Lemma in_MapSuprema_iff (Xs : ensemble (ensemble D)) (sup : D)
    : member sup (MapSuprema Xs) <-> (exists X_i : ensemble D, member X_i Xs /\ isSupremumOf sup X_i).
  Proof. reflexivity. Qed.

  Lemma SupremumOfMapSuprema_ge_Suprema (sup : D) (Xs : ensemble (ensemble D)) (sup_X : D) (X : ensemble D)
    (sup_isSupremumOf : isSupremumOf sup (MapSuprema Xs))
    (X_in_Xs : member X Xs)
    (sup_X_isSupremumOf_X : isSupremumOf sup_X X)
    : sup_X =< sup.
  Proof with eauto with *. eapply sup_isSupremumOf... eapply in_MapSuprema_iff... Qed.

  Local Hint Resolve SupremumOfMapSuprema_ge_Suprema : poset_hints.

  Theorem SupremumOfMapSuprema_isSupremumOf_unions (Xs : ensemble (ensemble D)) (sup : D)
    (SUPS_EXIST : forall X : ensemble D, << H_IN : member X Xs >> -> exists sup_X : D, isSupremumOf sup_X X)
    : isSupremumOf sup (MapSuprema Xs) <-> isSupremumOf sup (unions Xs).
  Proof with eauto with *.
    split; intros H_supremum z; split; ii; desnw.
    - apply in_unions_iff in H_IN. destruct H_IN as [X_i [x_in_X_i X_i_in_Xs]].
      pose proof (SUPS_EXIST X_i X_i_in_Xs) as [sup_X_i sup_X_i_isSupremumOf_X_i].
      transitivity (sup_X_i).
      + eapply sup_X_i_isSupremumOf_X_i...
      + transitivity (sup)...
    - eapply H_supremum. intros sup_X_i sup_X_i_in_MapSuprema.
      apply in_MapSuprema_iff in sup_X_i_in_MapSuprema.
      destruct sup_X_i_in_MapSuprema as [X_i [X_i_in_Xs sup_X_i_isSupremumOf_X_i]].
      eapply sup_X_i_isSupremumOf_X_i. ii. desnw. eapply UPPER_BOUND. eapply in_unions_iff...
    - apply in_MapSuprema_iff in H_IN. destruct H_IN as [X [X_in_Xs sup_X_isSupremumOf_X]].
      rename x into sup_X. enough (to_show : sup_X =< sup) by now transitivity (sup).
      eapply sup_X_isSupremumOf_X. ii; desnw. eapply H_supremum... eapply in_unions_iff...
    - eapply H_supremum. ii; desnw. apply in_unions_iff in H_IN.
      destruct H_IN as [X [x_in_X X_in_Xs]]. pose proof (SUPS_EXIST X X_in_Xs) as [sup_X sup_X_isSupremumOf_X].
      transitivity (sup_X).
      + eapply sup_X_isSupremumOf_X...
      + eapply UPPER_BOUND, in_MapSuprema_iff...
  Qed.

  Theorem InfimumOfUpperBounds_isSupremum (sup_X : D) (X : ensemble D)
    : isSupremumOf sup_X X <-> << sup_X_isInfimumOfUpperBounds : isInfimumOf sup_X (UpperBoundsOf X) >>.
  Proof with eauto with *.
    split.
    - intros sup_X_isSupremumOf_X z. split; ii; desnw.
      + rewrite LOWER_BOUND_LE_INFIMUM.
        eapply sup_X_isSupremumOf_X...
      + eapply LOWER_BOUND, sup_X_isSupremumOf_X...
    - intros H_supremum z. split; ii; desnw.
      + rewrite <- SUPREMUM_LE_UPPER_BOUND.
        eapply sup_X_isInfimumOfUpperBounds. unnw.
        intros upper_bound upper_bound_in. unnw.
        exact (upper_bound_in x H_IN).
      + unnw. eapply sup_X_isInfimumOfUpperBounds...
  Qed.

  Theorem SupremumOfLowerBounds_isInfimum (inf_X : D) (X : ensemble D)
    : isInfimumOf inf_X X <-> << inf_X_isSupremumOfLowerBounds : isSupremumOf inf_X (LowerBoundsOf X) >>.
  Proof with eauto with *.
    split.
    - intros inf_X_isInfimumOf_X z. split; ii; desnw.
      + rewrite <- SUPREMUM_LE_UPPER_BOUND.
        eapply inf_X_isInfimumOf_X...
      + eapply UPPER_BOUND, inf_X_isInfimumOf_X...
    - intros H_infimum z. split; ii; desnw.
      + rewrite LOWER_BOUND_LE_INFIMUM.
        eapply inf_X_isSupremumOfLowerBounds. unnw.
        intros lower_bound lower_bound_in. unnw.
        exact (lower_bound_in x H_IN).
      + unnw. eapply inf_X_isSupremumOfLowerBounds...
  Qed.

  Lemma Infimum_monotonic_wrtEnsembles (X1 : ensemble D) (X2 : ensemble D) (inf_X1 : D) (inf_X2 : D)
    (inf_X1_isInfimumOf_X1 : isInfimumOf inf_X1 X1)
    (inf_X2_isInfimumOf_X2 : isInfimumOf inf_X2 X2)
    (X1_isSubsetOf_X2 : isSubsetOf X1 X2)
    : inf_X2 =< inf_X1.
  Proof.
    eapply inf_X1_isInfimumOf_X1; ii.
    eapply inf_X2_isInfimumOf_X2; eauto with *.
  Qed.

  Local Hint Resolve Infimum_monotonic_wrtEnsembles : poset_hints.

  Lemma Infimum_unique (X1 : ensemble D) (X2 : ensemble D) (inf_X1 : D) (inf_X2 : D)
    (inf_X1_isInfimumOf_X1 : isInfimumOf inf_X1 X1)
    (inf_X2_isInfimumOf_X2 : isInfimumOf inf_X2 X2)
    (X1_eq_X2 : X1 == X2)
    : inf_X1 == inf_X2.
  Proof.
    pose proof (eqProp_implies_leProp X1 X2 X1_eq_X2) as claim1. symmetry in X1_eq_X2.
    pose proof (eqProp_implies_leProp X2 X1 X1_eq_X2) as claim2. eapply leProp_Antisymmetric; eauto with *.
  Qed.

  Lemma Infimum_congruence (inf_X : D) (inf_Y : D) (X : ensemble D) (Y : ensemble D)
    (inf_X_eq_inf_Y : inf_X == inf_Y)
    (X_eq_Y : X == Y)
    (inf_X_isInfimumOf_X : isInfimumOf inf_X X)
    : isInfimumOf inf_Y Y.
  Proof with eauto with *.
    intros z. unnw. rewrite <- inf_X_eq_inf_Y. split.
    - intros z_le_inf_X. rewrite <- X_eq_Y. eapply inf_X_isInfimumOf_X...
    - intros z_isLowerBoundOf_Y. eapply inf_X_isInfimumOf_X. unnw. rewrite -> X_eq_Y...
  Qed.

  Local Hint Resolve Infimum_unique Infimum_congruence : core.

  Global Add Parametric Morphism :
    (@isInfimumOf D requiresPoset) with signature (eqProp ==> eqProp ==> iff)
    as Infimum_compatWith_eqProp_wrtEnsembles.
  Proof. iis; eauto with *. Qed.

  Definition isLeastFixedPointOf (lfp : D) (f : D -> D) : Prop :=
    << IS_FIXED_POINT : member lfp (FixedPoints f) >> /\ << LOWER_BOUND_OF_FIXED_POINTS : member lfp (LowerBoundsOf (FixedPoints f)) >>
  .

  Definition isGreatestFixedPointOf (gfp : D) (f : D -> D) : Prop :=
    << IS_FIXED_POINT : member gfp (FixedPoints f) >> /\ << UPPER_BOUND_OF_FIXED_POINTS : member gfp (UpperBoundsOf (FixedPoints f)) >>
  .

  Local Hint Unfold isLeastFixedPointOf isGreatestFixedPointOf : poset_hints.

  Theorem theLeastFixedPointOfMonotonicMap (f : D -> D) (lfp : D)
    (f_isMonotonicMap : isMonotonicMap f)
    (lfp_isInfimumOfPrefixedPoints : isInfimumOf lfp (PrefixedPoints f))
    : isLeastFixedPointOf lfp f.
  Proof with eauto with *.
    assert (claim1 : forall x : D, member x (FixedPoints f) -> lfp =< x).
    { intros x H_IN. transitivity (f x).
      - eapply lfp_isInfimumOfPrefixedPoints... eapply f_isMonotonicMap...
      - eapply eqProp_implies_leProp...
    }
    assert (claim2 : f lfp =< lfp).
    { eapply lfp_isInfimumOfPrefixedPoints. ii; desnw. transitivity (f x); trivial.
      eapply f_isMonotonicMap, lfp_isInfimumOfPrefixedPoints...
    }
    assert (claim3 : lfp =< f lfp).
    { eapply lfp_isInfimumOfPrefixedPoints... eapply f_isMonotonicMap... }
    split... eapply leProp_Antisymmetric...
  Qed.

  Lemma theGreatestFixedPointOfMonotonicMap (f : D -> D) (gfp : D)
    (f_isMonotonicMap : isMonotonicMap f)
    (gfp_isSupremumOfPostfixedPoints : isSupremumOf gfp (PostfixedPoints f))
    : isGreatestFixedPointOf gfp f.
  Proof with eauto with *.
    assert (claim1 : gfp =< f gfp).
    { eapply gfp_isSupremumOfPostfixedPoints... ii; desnw. transitivity (f x); trivial.
      eapply f_isMonotonicMap, gfp_isSupremumOfPostfixedPoints...
    }
    assert (claim2 : f gfp =< gfp).
    { eapply gfp_isSupremumOfPostfixedPoints... eapply f_isMonotonicMap... }
    split.
    - eapply leProp_Antisymmetric...
    - intros fix_f H_in. desnw.
      eapply gfp_isSupremumOfPostfixedPoints...
      eapply eqProp_implies_leProp...
  Qed.

  Definition isSupremumIn (sup : D) (X : ensemble D) (phi : D -> Prop) : Prop :=
    ⟪ IN_SUBSET : phi sup ⟫ /\ ⟪ SUPREMUM_OF_SUBSET : forall upper_bound : @sig D phi, << SUPREMUM_LE_UPPER_BOUND : sup =< (proj1_sig upper_bound) >> <-> << UPPER_BOUND : member (proj1_sig upper_bound) (UpperBoundsOf X) >> ⟫
  .

  Theorem isSupremumIn_iff (phi : D -> Prop) (sup_X : @sig D phi) (X : ensemble (@sig D phi))
    : isSupremumIn (proj1_sig sup_X) (image (@proj1_sig D phi) X) phi <-> isSupremumOf sup_X X.
  Proof with eauto with *.
    split.
    { intros [? ?] z; desnw; split.
      - ii; desnw. eapply SUPREMUM_OF_SUBSET... eapply in_image_iff...
      - ii; desnw. eapply SUPREMUM_OF_SUBSET.
        intros x H_in_image. unnw. eapply in_image_iff in H_in_image.
        destruct H_in_image as [[x' phi_x] [x_eq x_in]]. simpl in x_eq; subst x'.
        change (@exist D phi x phi_x =< z)...
    }
    { intros sup_X_isSupremumOf_X. split.
      - exact (proj2_sig sup_X).
      - split; ii; desnw.
        + eapply in_image_iff in H_IN. destruct H_IN as [[x' phi_x] [x_eq x_in]].
          simpl in x_eq; subst x'. rewrite <- SUPREMUM_LE_UPPER_BOUND.
          change (@exist D phi x phi_x =< sup_X). eapply sup_X_isSupremumOf_X...
        + change (sup_X =< upper_bound). eapply sup_X_isSupremumOf_X.
          intros x x_in. change (proj1_sig x =< proj1_sig upper_bound).
          eapply UPPER_BOUND, in_image_iff...
    }
  Qed.

  End BASIC_FACTS_ON_SUPREMUM.

  Global Hint Resolve Supremum_monotonic_wrtEnsembles Supremum_unique Supremum_congruence Supremum_compatWith_eqProp_wrtEnsembles : poset_hints.

  Class isDecidableTotalOrder (A : Type) {requiresPoset : isPoset A} : Type :=
    { compare (lhs : A) (rhs : A) : comparison
    ; compare_LT_implies (lhs : A) (rhs : A) (H_lt : compare lhs rhs = Lt) : lhs =< rhs /\ ~ lhs == rhs
    ; compare_EQ_implies (lhs : A) (rhs : A) (H_eq : compare lhs rhs = Eq) : lhs == rhs
    ; compare_GT_implies (lhs : A) (rhs : A) (H_gt : compare lhs rhs = Gt) : rhs =< lhs /\ ~ lhs == rhs
    }
  .

  Local Hint Resolve compare_LT_implies compare_EQ_implies compare_GT_implies : poset_hints.

  Section LEXICOGRAPHICAL_ORDER.

  Context {A : Type} {requiresPoset : isPoset A} {requiresDecidableTotalOrder : isDecidableTotalOrder A (requiresPoset := requiresPoset)}.

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

  Definition lex_eq (lhs : list A) (rhs : list A) : Prop := lex_compare lhs rhs = Eq.

  Definition lex_le (lhs : list A) (rhs : list A) : Prop := lex_compare lhs rhs = Lt \/ lex_compare lhs rhs = Eq.

  Lemma compare_spec (lhs : A) (rhs : A) :
    match compare lhs rhs with
    | Lt => lhs =< rhs /\ ~ lhs == rhs
    | Eq => lhs == rhs
    | Gt => rhs =< lhs /\ ~ lhs == rhs
    end.
  Proof. destruct (compare lhs rhs) eqn: H_compare_result; eauto with *. Qed.

  Local Instance lex_eq_Equivalence
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

  Local Instance listPointwiseEquivalence : isSetoid (list A) :=
    { eqProp := lex_eq
    ; eqProp_Equivalence := lex_eq_Equivalence
    }
  .

  Local Instance lex_le_PreOrder
    : PreOrder lex_le.
  Proof with discriminate || eauto with *.
    assert (lemma1 : forall x1 : A, forall x2 : A, x1 =< x2 -> x2 =< x1 -> x1 == x2). { ii... }
    assert (lemma2 : forall x1 : A, forall x2 : A, x1 == x2 -> x1 =< x2). { ii... }
    assert (lemma3 : forall x1 : A, forall x2 : A, x1 == x2 -> x2 =< x1). { ii... }
    unfold lex_le. split.
    - intros xs1; right. eapply lex_eq_Equivalence.
    - intros xs1 xs2 xs3; revert xs1 xs3; induction xs2 as [ | x2 xs2 IH]; destruct xs1 as [ | x1 xs1]; destruct xs3 as [ | x3 xs3]; simpl...
      intros [H_false | H_false]...
      pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x3); pose proof (claim3 := compare_spec x1 x3); pose proof (claim4 := IH xs1 xs3).
      destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x3) eqn: H_compare_result2; destruct (compare x1 x3) eqn: H_compare_result3...
      + contradiction (proj2 claim3)...
      + contradiction (proj2 claim2)...
      + contradiction (proj2 claim3); eapply lemma1; [transitivity x2 | exact (proj1 claim3)]. eapply lemma2... exact (proj1 claim2).
      + contradiction (proj2 claim2)...
      + contradiction (proj2 claim1)...
      + contradiction (proj2 claim3); eapply lemma1; [transitivity x2 | exact (proj1 claim3)]. exact (proj1 claim1). eapply lemma2...
      + contradiction (proj2 claim1); eapply lemma1; [exact (proj1 claim1) | transitivity x3]. exact (proj1 claim2). eapply lemma2...
      + contradiction (proj2 claim1); eapply lemma1; [exact (proj1 claim1) | transitivity x3]. exact (proj1 claim2). exact (proj1 claim3).
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
      - contradiction (proj2 claim1). eapply lemma1; [exact (proj1 claim1) | exact (proj1 claim2)].
      - contradiction (proj2 claim1)...
      - contradiction (proj2 claim1). eapply lemma1; [exact (proj1 claim2) | exact (proj1 claim1)].
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

  Corollary lex_le_flip_iff (lhs : list A) (rhs : list A) (compare_result : comparison) :
    lex_compare lhs rhs = compare_result <->
    match compare_result with
    | Lt => lex_compare rhs lhs = Gt
    | Eq => lex_compare rhs lhs = Eq
    | Gt => lex_compare rhs lhs = Lt
    end.
  Proof.
    split.
    - ii; subst compare_result. exact (lex_le_flip_spec lhs rhs).
    - pose proof (lex_le_flip_spec rhs lhs) as claim1. intros H_eq.
      destruct compare_result eqn: H_compare_result; now rewrite H_eq in claim1.
  Qed.

  Local Instance lex_le_PartialOrder
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

  Local Instance listLexicographicalOrder : isPoset (list A) :=
    { leProp := lex_le
    ; Poset_requiresSetoid := listPointwiseEquivalence
    ; leProp_PreOrder := lex_le_PreOrder
    ; leProp_PartialOrder := lex_le_PartialOrder
    }
  .

  Local Obligation Tactic := cbn; unfold lex_le, lex_eq; ii.
  Global Program Instance listLexicographicalOrder_liftsDecidableTotalOrder : isDecidableTotalOrder (list A) := { compare := lex_compare }.
  Next Obligation. rewrite H_lt. split; [now left | congruence]. Qed.
  Next Obligation. exact (H_eq). Qed.
  Next Obligation. exploit (lex_le_flip_spec lhs rhs). rewrite H_gt. intros H_lt. rewrite H_lt. split; [now left | congruence]. Qed.

  End LEXICOGRAPHICAL_ORDER.

  Section NAT_TOSET.

  Local Instance nat_isPoset : isPoset nat :=
    { leProp := le
    ; Poset_requiresSetoid := theFinestSetoidOf nat
    ; leProp_PreOrder := Nat.le_preorder
    ; leProp_PartialOrder := Nat.le_partialorder
    }
  .

  Fixpoint nat_compare (x : nat) (y : nat) {struct x} : comparison :=
    match x, y with
    | O, O => Eq
    | O, S y' => Lt
    | S x', O => Gt
    | S x', S y' => nat_compare x' y'
    end
  .

  Lemma nat_compare_lt (x : nat) (y : nat)
    (hyp_lt : nat_compare x y = Lt)
    : x <= y /\ x <> y.
  Proof with eauto with *.
    revert x y hyp_lt. induction x as [ | x IH], y as [ | y]; simpl; ii.
    - inversion hyp_lt.
    - split.
      { eapply le_intro_0_le_n. }
      { ii; eapply not_S_n_eq_0... }
    - inversion hyp_lt.
    - pose proof (IH y hyp_lt) as [x_le_y x_ne_y]. split.
      { eapply le_intro_S_n_le_S_m... }
      { ii. eapply x_ne_y, suc_n_eq_suc_m_elim... }
  Qed.

  Lemma nat_compare_eq (x : nat) (y : nat)
    (hyp_lt : nat_compare x y = Eq)
    : x = y.
  Proof with eauto with *.
    revert x y hyp_lt. induction x as [ | x IH], y as [ | y]; simpl; ii.
    - reflexivity.
    - inversion hyp_lt.
    - inversion hyp_lt.
    - pose proof (IH y hyp_lt) as x_eq_y.
      exact (eq_congruence suc x y x_eq_y).
  Qed.

  Lemma nat_compare_gt (x : nat) (y : nat)
    (hyp_lt : nat_compare x y = Gt)
    : y <= x /\ x <> y.
  Proof with eauto with *.
    cbn. revert x y hyp_lt. induction x as [ | x IH], y as [ | y]; simpl; ii.
    - inversion hyp_lt.
    - inversion hyp_lt.
    - split.
      { eapply le_intro_0_le_n. }
      { ii; eapply not_S_n_eq_0... }
    - pose proof (IH y hyp_lt) as [y_le_x x_ne_y]. split.
      { eapply le_intro_S_n_le_S_m... }
      { ii. eapply x_ne_y, suc_n_eq_suc_m_elim... }
  Qed.

  Local Instance nat_hasDecidableTotalOrder : isDecidableTotalOrder nat (requiresPoset := nat_isPoset) :=
    { compare := nat_compare
    ; compare_LT_implies := nat_compare_lt
    ; compare_EQ_implies := nat_compare_eq
    ; compare_GT_implies := nat_compare_gt
    }
  .

  End NAT_TOSET.

End BasicPosetTheory.

Module DomainTheoryHelper.

  Import ListNotations BasicPosetTheory.

  Global Reserved Notation " '⟬' X '⟶' Y '⟭' " (X at level 60, Y at level 60, at level 0, no associativity).

  Class isCoLa (D : Type) {requiresPoset : isPoset D} : Type := getSupremumOf_inCoLa (X : ensemble D) : {sup_X : D | isSupremumOf sup_X X}.

  Global Hint Constructors image finite : poset_hints.

  Definition isDirectedOrEmpty {D : Type} {requiresPoset : isPoset D} (X : ensemble D) : Prop :=
    forall x1 : D, << H_IN1 : member x1 X >> ->
    forall x2 : D, << H_IN2 : member x2 X >> ->
    exists x3 : D, << H_IN3 : member x3 X >> /\
    << UPPER_BOUND : x1 =< x3 /\ x2 =< x3 >>
  .

  Definition isDirected {D : Type} {requiresPoset : isPoset D} (X : ensemble D) : Prop :=
    << NONEMPTY : exists x0 : D, member x0 X >> /\ << DIRECTED_OR_EMPTY : isDirectedOrEmpty X >>
  .

  Lemma isDirected_iff {D : Type} {requiresPoset : isPoset D} (X : ensemble D)
    : isDirected X <-> << DIRECTED : forall xs : list D, forall xs_isFiniteSubsetOf : isFiniteSubsetOf xs X, exists y : D, << H_IN : y \in X >> /\ << UPPER_BOUND : forall x : D, In x xs -> x =< y >> >>.
  Proof with eauto with *.
    split; intros DIRECTED.
    - ii. destruct DIRECTED; desnw. induction xs as [ | x xs IH].
      + exists (x0). split... intros z [].
      + assert (xs_isFiniteSubsetOf' : isFiniteSubsetOf xs X).
        { ii. eapply xs_isFiniteSubsetOf. right... }
        pose proof (IH xs_isFiniteSubsetOf') as [y' ?]; desnw.
        assert (x_in_X : x \in X).
        { eapply xs_isFiniteSubsetOf. left... }
        pose proof (DIRECTED_OR_EMPTY x x_in_X y' H_IN) as [y [? [? ?]]].
        exists (y). split... intros x1 [x1_eq_x | x1_in_xs].
        { subst x1... }
        { transitivity (y')... }
    - unnw. split.
      + assert (xs_isFiniteSubsetOf : isFiniteSubsetOf [] X).
        { intros z []. }
        pose proof (DIRECTED [] xs_isFiniteSubsetOf) as [x0 ?]; desnw.
        exists (x0)...
      + ii. set (xs := [x1; x2]).
        assert (xs_isFiniteSubsetOf : isFiniteSubsetOf xs X).
        { intros z [z_eq_x1 | [z_eq_x2 | []]]; subst z... }
        pose proof (DIRECTED xs xs_isFiniteSubsetOf) as [y [H_IN UPPER_BOUND]].
        exists (y). split... split; eapply UPPER_BOUND; [left | right; left]...
  Qed.

  Class isCPO (D : Type) {requiresPoset : isPoset D} : Type :=
    { getBottom_inCPO : D
    ; getSupremumOf_inCPO (X : ensemble D) (X_isDirected : isDirected X) : D
    ; getBottom_inCPO_isBottom : forall x : D, getBottom_inCPO =< x
    ; getSupremumOf_inCPO_isSupremum (X : ensemble D) (X_isDirected : isDirected X) : isSupremumOf (getSupremumOf_inCPO X X_isDirected) X
    }
  .

  Lemma preservesDirected_if_isMonotonicMap {dom : Type} {cod : Type} {dom_requiresPoset : isPoset dom} {cod_requiresPoset : isPoset cod} (f : dom -> cod)
    (f_isMonotonicMap : isMonotonicMap f)
    : forall X : ensemble dom, << DIRECTED : isDirected X >> -> isDirected (image f X).
  Proof.
    ii; desnw. destruct DIRECTED; desnw. split; unnw.
    - exists (f x0). econstructor; eauto.
    - intros y1 ? y2 ?; desnw. apply in_image_iff in H_IN1, H_IN2.
      destruct H_IN1 as [x1 [y1_eq x1_in]]; destruct H_IN2 as [x2 [y2_eq x2_in]]; subst y1 y2.
      pose proof (DIRECTED_OR_EMPTY x1 x1_in x2 x2_in) as [x3 [x3_in [x1_le_x3 x2_le_x3]]]; unnw.
      exists (f x3). rewrite in_image_iff. split; eauto with *.
  Qed.

End DomainTheoryHelper.
