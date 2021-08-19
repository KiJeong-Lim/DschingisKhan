Require Import DschingisKhan.projects.SmullyanGIT.PA.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module SmullyanGIT. (* Reference: "Goedel's Incompleteness Theorems" of "Raymond M. Smullyan" *)

  Import MyUtilities BasicSetoidTheory MyEnsemble BasicPosetTheory MyEnsembleNova.

  Class isGoedelianLanguage (mathcalE : Type) : Type :=
    { enum_mathcalE : nat -> mathcalE
    ; mathcalE_is_denumerable : forall E : mathcalE, {n : nat | enum_mathcalE n = E}
    ; isSentence : ensemble mathcalE
    ; isProvable : ensemble mathcalE
    ; isRefutable : ensemble mathcalE
    ; isPredicate : ensemble mathcalE
    ; appnat : mathcalE -> nat -> mathcalE
    ; isTrue : ensemble mathcalE
    ; onlyProvableIsSentence : isSubsetOf isProvable isSentence
    ; onlyRefutableIsSentence : isSubsetOf isRefutable isSentence
    ; appnatForPredicate : forall h : mathcalE, isPredicate h -> forall n : nat, isSentence (appnat h n)
    ; onlyTrueIsSentence : isSubsetOf isTrue isSentence
    }
  .

  Section AbstractFormOfTheTheorems.

  Context (mathcalE : Type) `{mathcalE_isGoedelianLanguage : isGoedelianLanguage mathcalE}.

  Definition diagonalizer : nat -> nat :=
    fun n : nat =>
    proj1_sig (mathcalE_is_denumerable (appnat (enum_mathcalE n) n))
  .

  Local Hint Unfold diagonalizer : core.

  Lemma diagonalizer_diagonalizes :
    forall n : nat,
    forall E : mathcalE,
    enum_mathcalE n = E ->
    enum_mathcalE (diagonalizer n) = appnat E n.
  Proof with eauto with *.
    unfold diagonalizer.
    intros n E H_eqE.
    subst.
    destruct (mathcalE_is_denumerable (appnat (enum_mathcalE n) n)) as [d_n H]...
  Qed.

  Definition expressPredicate : mathcalE -> ensemble nat -> Prop :=
    fun H : mathcalE =>
    fun A : ensemble nat =>
    forall n : nat,
    isTrue (appnat H n) <-> member n A
  .

  Local Hint Unfold expressPredicate : core.

  Definition is_expressible : ensemble nat -> Prop :=
    fun A : ensemble nat =>
    exists H : mathcalE, expressPredicate H A
  .

  Local Hint Unfold is_expressible : core.

  Definition StarOf : ensemble nat -> ensemble nat :=
    fun ns : ensemble nat =>
    fun n : nat =>
    member (diagonalizer n) ns
  .

  Local Hint Unfold StarOf : core.

  Definition isCorrect : Prop :=
    isProvable \subseteq isTrue /\ isRefutable \cap isTrue \subseteq \emptyset
  .

  Local Hint Unfold isCorrect : core.

  Definition P : ensemble nat :=
    fun n : nat =>
    isProvable (enum_mathcalE n)
  .

  Local Hint Unfold P : core.

  Theorem After_Goedel_with_shades_of_Tarski :
    isCorrect ->
    is_expressible (StarOf (completement P)) ->
    exists E : mathcalE, isTrue E /\ ~ isProvable E.
  Proof with try now firstorder.
    intros mathcalE_is_correct [H H_express_StarOf_complement_P].
    destruct (mathcalE_is_denumerable H) as [n n_is_the_goedel_number_of_H].
    assert (diagonalization_of_n_is_true_iff_n_is_in_StarOf_complement_of_P : isTrue (enum_mathcalE (diagonalizer n)) <-> member n (StarOf (completement P))).
    { unfold expressPredicate in H_express_StarOf_complement_P.
      rewrite (diagonalizer_diagonalizes n H n_is_the_goedel_number_of_H)...
    }
    enough (n_is_in_StarOf_complement_of_P_iff_diagonalization_of_n_is_not_Provable : member n (StarOf (completement P)) <-> ~ isProvable (enum_mathcalE (diagonalizer n)))...
  Qed.

  Let the_first_goal : Prop :=
    forall A : ensemble nat,
    is_expressible A ->
    is_expressible (StarOf A)
  .

  Let the_second_goal : Prop :=
    forall A : ensemble nat,
    is_expressible A ->
    is_expressible (completement A)
  .

  Let the_third_goal : Prop :=
    is_expressible P
  .

  Definition isGoedelSentence : mathcalE -> ensemble nat -> Prop :=
    fun E : mathcalE =>
    fun A : ensemble nat =>
    exists n : nat, enum_mathcalE n = E /\ (isTrue E <-> member n A)
  .

  Lemma A_Diagonal_Lemma_a :
    forall A : ensemble nat,
    is_expressible (StarOf A) ->
    exists E : mathcalE, isGoedelSentence E A.
  Proof with try now firstorder.
    intros A [H H_express_StarOf_A].
    destruct (mathcalE_is_denumerable H) as [n g_H_is_n].
    assert (H_n_is_true_iff_d_n_is_in_A : isTrue (appnat H n) <-> member (diagonalizer n) A) by firstorder.
    assert (d_n_is_g_H_n : enum_mathcalE (diagonalizer n) = appnat H n).
    { unfold diagonalizer.
      rewrite (proj2_sig (mathcalE_is_denumerable (appnat (enum_mathcalE n) n))), g_H_is_n...
    }
    exists (appnat H n)...
  Qed.

  Lemma A_Diagonal_Lemma_b :
    the_first_goal ->
    forall A : ensemble nat,
    is_expressible A ->
    exists E : mathcalE, isGoedelSentence E A.
  Proof with eauto with *.
    intros the_first_goal_holds A A_is_expressible.
    apply A_Diagonal_Lemma_a...
  Qed.

  Definition T : ensemble nat :=
    fun n : nat =>
    isTrue (enum_mathcalE n)
  .

  Local Hint Unfold T : core.

  Lemma there_is_no_GoedelSentence_of_complement_of_T :
    ~ (exists E : mathcalE, isGoedelSentence E (completement T)).
  Proof with try now firstorder.
    intros [E [n [n_is_g_E E_is_true_iff_n_is_in_complement_T]]].
    subst...
  Qed.

  Theorem After_Tarski_1 :
    ~ is_expressible (StarOf (completement T)).
  Proof with eauto with *.
    intros StarOf_T_is_expressible.
    destruct (A_Diagonal_Lemma_a (completement T) StarOf_T_is_expressible) as [H H_is_GoedelSentence_for_complement_of_T].
    contradiction there_is_no_GoedelSentence_of_complement_of_T...
  Qed.

  Theorem After_Tarski_2 :
    the_first_goal ->
    ~ is_expressible (completement T).
  Proof with eauto.
    intros the_first_goal_holds completement_of_T_is_expressible.
    apply After_Tarski_1...
  Qed.

  Theorem After_Tarski_3 :
    the_first_goal ->
    the_second_goal ->
    ~ is_expressible T.
  Proof with eauto.
    intros the_first_goal_holds the_second_goal_holds T_is_expressible.
    apply After_Tarski_2...
  Qed.

  End AbstractFormOfTheTheorems.

End SmullyanGIT.
