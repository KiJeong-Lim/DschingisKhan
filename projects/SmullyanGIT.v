Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module SmullyanGIT. (* Raymond M. Smullyan's "Goedel's Incompleteness Theorems" *)

  Import ListNotations MyUtilities BasicSetoidTheory MyEnsemble BasicPosetTheory MyEnsembleNova.

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

(* [Fix Me: "Refactoring"]

  Definition vr : Set :=
    nat
  .

  Inductive tm : Set :=
  | ivar_tm : vr -> tm
  | zero_tm : tm
  | succ_tm : tm -> tm
  | plus_tm : tm -> tm -> tm
  | mult_tm : tm -> tm -> tm
  | expo_tm : tm -> tm -> tm
  .

  Inductive form : Set :=
  | eqn_form : tm -> tm -> form
  | leq_form : tm -> tm -> form
  | neg_form : form -> form
  | imp_form : form -> form -> form
  | all_form : vr -> form -> form
  .

  Lemma vr_eq_dec :
    forall x1 : vr,
    forall x2 : vr,
    {x1 = x2} + {x1 <> x2}.
  Proof.
    apply Nat.eq_dec.
  Qed.

  Ltac case_vr_eq_dec x1 x2 :=
    let H := fresh "H" in
    destruct (vr_eq_dec x1 x2) as [H | H];
    simpl;
    [destruct H | try now contradiction H];
    try now firstorder
  .

  Ltac simpl_vr_eq_dec :=
    simpl;
    repeat (repeat split; intro);
    match goal with
    | H : (if vr_eq_dec ?x1 ?x2 then ?casel else ?caser) = ?rhs |- _ => case_vr_eq_dec x1 x2
    | H : ?lhs = (if vr_eq_dec ?x1 ?x2 then ?casel else ?caser) |- _ => case_vr_eq_dec x1 x2
    | |- (if vr_eq_dec ?x1 ?x2 then ?casel else ?caser) = ?rhs => case_vr_eq_dec x1 x2
    | |- ?lhs = (if vr_eq_dec ?x1 ?x2 then ?casel else ?caser) => case_vr_eq_dec x1 x2
    end
  .

  Ltac auto_rewrite :=
    repeat intro;
    repeat (
      rewrite in_app_iff ||
      rewrite orb_true_iff ||
      rewrite orb_false_iff ||
      rewrite andb_true_iff ||
      rewrite negb_true_iff ||
      rewrite andb_false_iff ||
      rewrite negb_false_iff ||
      rewrite forallb_true_iff
    );
    try now firstorder
  .

  Fixpoint occursFreeIn_tm (z : vr) (t : tm) : bool :=
    match t with
    | ivar_tm x => if vr_eq_dec z x then true else false
    | zero_tm => false
    | succ_tm t1 => occursFreeIn_tm z t1
    | plus_tm t1 t2 => occursFreeIn_tm z t1 || occursFreeIn_tm z t2
    | mult_tm t1 t2 => occursFreeIn_tm z t1 || occursFreeIn_tm z t2
    | expo_tm t1 t2 => occursFreeIn_tm z t1 || occursFreeIn_tm z t2
    end
  .

  Fixpoint occursFreeIn_form (z : vr) (f : form) : bool :=
    match f with
    | eqn_form t1 t2 => occursFreeIn_tm z t1 || occursFreeIn_tm z t2
    | leq_form t1 t2 => occursFreeIn_tm z t1 || occursFreeIn_tm z t2
    | neg_form f1 => occursFreeIn_form z f1
    | imp_form f1 f2 => occursFreeIn_form z f1 || occursFreeIn_form z f2
    | all_form x f1 => if vr_eq_dec z x then false else occursFreeIn_form z f1
    end
  .

  Fixpoint getFreeVars_tm (t : tm) : list vr :=
    match t with
    | ivar_tm x => [x]
    | zero_tm => []
    | succ_tm t1 => getFreeVars_tm t1
    | plus_tm t1 t2 => getFreeVars_tm t1 ++ getFreeVars_tm t2
    | mult_tm t1 t2 => getFreeVars_tm t1 ++ getFreeVars_tm t2
    | expo_tm t1 t2 => getFreeVars_tm t1 ++ getFreeVars_tm t2
    end
  .

  Theorem the_rule_of_getFreeVars_tm :
    forall t : tm,
    forall x : vr,
    In x (getFreeVars_tm t) <-> occursFreeIn_tm x t = true.
  Proof with try now eauto.
    induction t; simpl.
    1: simpl_vr_eq_dec.
    1: split...
    1: intros x...
    all: auto_rewrite.
  Qed.

  Fixpoint getFreeVars_form (f : form) : list vr :=
    match f with
    | eqn_form t1 t2 => getFreeVars_tm t1 ++ getFreeVars_tm t2
    | leq_form t1 t2 => getFreeVars_tm t1 ++ getFreeVars_tm t2
    | neg_form f1 => getFreeVars_form f1
    | imp_form f1 f2 => getFreeVars_form f1 ++ getFreeVars_form f2
    | all_form x f1 => remove vr_eq_dec x (getFreeVars_form f1)
    end
  .

  Theorem the_rule_of_getFreeVars_form :
    forall f : form,
    forall x : vr,
    In x (getFreeVars_form f) <-> occursFreeIn_form x f = true.
  Proof with try now firstorder.
    induction f; simpl.
    - auto_rewrite.
      do 2 rewrite the_rule_of_getFreeVars_tm...
    - auto_rewrite.
      do 2 rewrite the_rule_of_getFreeVars_tm...
    - auto_rewrite.
    - auto_rewrite.
    - intros x.
      split; intros H.
      + assert (H0 : In x (getFreeVars_form f) /\ x <> v) by now apply (in_remove vr_eq_dec (getFreeVars_form f) x v).
        simpl_vr_eq_dec.
      + simpl_vr_eq_dec.
        apply in_in_remove...
  Qed.

  Definition value_assignment : Set :=
    vr -> nat
  .

  Fixpoint eval_tm (va : value_assignment) (t : tm) : nat :=
    match t with
    | ivar_tm x => va x
    | zero_tm => O
    | succ_tm t1 => S (eval_tm va t1)
    | plus_tm t1 t2 => eval_tm va t1 + eval_tm va t2
    | mult_tm t1 t2 => eval_tm va t1 * eval_tm va t2
    | expo_tm t1 t2 => (eval_tm va t1)^(eval_tm va t2)
    end
  .

  Lemma eval_tm_extensionality :
    forall t : tm,
    forall va1 : value_assignment,
    forall va2 : value_assignment,
    (forall x : vr, occursFreeIn_tm x t = true -> va1 x = va2 x) ->
    eval_tm va1 t = eval_tm va2 t.
  Proof with eauto.
    assert ( claim1 :
      forall v : vr,
      forall va1 va2 : value_assignment,
      (forall x : vr, (if vr_eq_dec x v then true else false) = true -> va1 x = va2 x) ->
      va1 v = va2 v
    ).
    { intros v va1 va2 H.
      apply H.
      simpl_vr_eq_dec.
    }
    induction t; simpl...
    all: intros va1 va2 H; rewrite (IHt1 va1 va2), (IHt2 va1 va2)...
    all: intros x H0; apply H, orb_true_iff...
  Qed.

  Fixpoint eval_form (va : value_assignment) (f : form) : Prop :=
    match f with
    | eqn_form t1 t2 => eval_tm va t1 = eval_tm va t2
    | leq_form t1 t2 => eval_tm va t1 <= eval_tm va t2
    | neg_form f1 => ~ eval_form va f1
    | imp_form f1 f2 => eval_form va f1 -> eval_form va f2
    | all_form x f1 => forall val : nat, eval_form (fun z : vr => if vr_eq_dec x z then val else va z) f1
    end
  .

  Lemma eval_form_extensionality :
    forall f : form,
    forall va1 : value_assignment,
    forall va2 : value_assignment,
    (forall x : vr, occursFreeIn_form x f = true -> va1 x = va2 x) ->
    eval_form va1 f <-> eval_form va2 f.
  Proof with (reflexivity || eauto).
    induction f; simpl; intros va1 va2 H.
    1, 2: rewrite (eval_tm_extensionality t va1 va2), (eval_tm_extensionality t0 va1 va2)...
    5: rewrite (IHf va1 va2)...
    5: rewrite (IHf1 va1 va2), (IHf2 va1 va2)...
    1, 2, 3, 4, 5, 6: intros x H0; apply H, orb_true_iff...
    enough (claim1 : forall n : nat, eval_form (fun z : vr => if vr_eq_dec v z then n else va1 z) f <->  eval_form (fun z : vr => if vr_eq_dec v z then n else va2 z) f) by firstorder.
    intros n.
    rewrite (IHf (fun z : vr => if vr_eq_dec v z then n else va1 z) (fun z : vr => if vr_eq_dec v z then n else va2 z))...
    simpl_vr_eq_dec.
    apply H.
    simpl_vr_eq_dec.
  Qed.

  Fixpoint make_numeral (n : nat) : tm :=
    match n with
    | 0 => zero_tm
    | S n => succ_tm (make_numeral n)
    end
  .

  Lemma eval_tm_make_numeral :
    forall n : nat,
    forall va : value_assignment,
    eval_tm va (make_numeral n) = n.
  Proof with eauto.
    induction n; simpl...
  Qed.

  Definition substitution : Set :=
    list (vr * tm)
  .

  Fixpoint substitute_vr (sigma : substitution) (x : vr) : tm :=
    match sigma with
    | [] => ivar_tm x
    | (x1, tm1) :: sigma' => if vr_eq_dec x x1 then tm1 else substitute_vr sigma' x
    end
  .

  Fixpoint substitute_tm (sigma : substitution) (t : tm) : tm :=
    match t with
    | ivar_tm x => substitute_vr sigma x
    | zero_tm => zero_tm
    | succ_tm t1 => succ_tm (substitute_tm sigma t1)
    | plus_tm t1 t2 => plus_tm (substitute_tm sigma t1) (substitute_tm sigma t2)
    | mult_tm t1 t2 => mult_tm (substitute_tm sigma t1) (substitute_tm sigma t2)
    | expo_tm t1 t2 => expo_tm (substitute_tm sigma t1) (substitute_tm sigma t2)
    end
  .

  Theorem substitute_tm_preserves_eval_tm :
    forall t : tm,
    forall sigma : substitution,
    forall va : value_assignment,
    eval_tm (fun z : vr => eval_tm va (substitute_vr sigma z)) t = eval_tm va (substitute_tm sigma t).
  Proof with eauto.
    induction t; simpl...
  Qed.

  Definition getMaxNumOfFreeVars_tm (t : tm) : vr :=
    fold_right_max_0 (getFreeVars_tm t)
  .

  Lemma getMaxNumOfFreeVars_tm_lt :
    forall t : tm,
    forall x : vr,
    getMaxNumOfFreeVars_tm t < x ->
    occursFreeIn_tm x t = false.
  Proof with (lia || eauto).
    assert (claim1 : forall v : vr, forall x : vr, max v 0 < x -> (if vr_eq_dec x v then true else false) = false) by now simpl_vr_eq_dec; lia.
    unfold getMaxNumOfFreeVars_tm.
    induction t; simpl...
    all: auto_rewrite; rewrite fold_right_max_0_app in H; split; [apply IHt1 | apply IHt2]...
  Qed.

  Definition isFreshVarIn_substitute_tm (sigma : substitution) (z : vr) (t : tm) : Prop :=
    forallb (fun x : vr => negb (occursFreeIn_tm z (substitute_vr sigma x))) (getFreeVars_tm t) = true
  .

  Definition isFreshVarIn_substitute_form (sigma : substitution) (z : vr) (f : form) : Prop :=
    forallb (fun x : vr => negb (occursFreeIn_tm z (substitute_vr sigma x))) (getFreeVars_form f) = true
  .

  Definition chi (sigma : substitution) (f : form) : vr :=
    S (fold_right_max_0 (map (fun x : vr => getMaxNumOfFreeVars_tm (substitute_vr sigma x)) (getFreeVars_form f)))
  .

  Theorem the_rule_of_chi :
    forall f : form,
    forall sigma : substitution,
    isFreshVarIn_substitute_form sigma (chi sigma f) f.
  Proof with eauto.
    assert ( claim1 :
      forall sigma : substitution,
      forall f : form,
      forall x : vr,
      occursFreeIn_form x f = true ->
      occursFreeIn_tm (chi sigma f) (substitute_vr sigma x) = false
    ).
    { intros sigma f x H.
      enough (claim1_aux1 : getMaxNumOfFreeVars_tm (substitute_vr sigma x) < chi sigma f) by now apply getMaxNumOfFreeVars_tm_lt.
      unfold chi, fold_right_max_0.
      enough (claim1_aux2 : fold_right max 0 (map (fun z : vr => getMaxNumOfFreeVars_tm (substitute_vr sigma z)) (getFreeVars_form f)) >= getMaxNumOfFreeVars_tm (substitute_vr sigma x)) by lia.
      rewrite <- the_rule_of_getFreeVars_form in H.
      apply fold_right_max_0_in, in_map_iff...
    }
    unfold isFreshVarIn_substitute_form.
    do 2 auto_rewrite.
    apply claim1, the_rule_of_getFreeVars_form...
  Qed.

  Fixpoint substitute_form (sigma : substitution) (f : form) : form :=
    match f with
    | eqn_form t1 t2 => eqn_form (substitute_tm sigma t1) (substitute_tm sigma t2)
    | leq_form t1 t2 => leq_form (substitute_tm sigma t1) (substitute_tm sigma t2)
    | neg_form f1 => neg_form (substitute_form sigma f1)
    | imp_form f1 f2 => imp_form (substitute_form sigma f1) (substitute_form sigma f2)
    | all_form x f1 =>
      let z : vr := chi sigma f in
      all_form z (substitute_form ((x, ivar_tm z) :: sigma) f1)
    end
  .

  Theorem substitute_form_preserves_eval_form :
    forall f : form,
    forall sigma : substitution,
    forall va : value_assignment,
    eval_form (fun z : vr => eval_tm va (substitute_vr sigma z)) f <-> eval_form va (substitute_form sigma f).
  Proof with (reflexivity || eauto).
    induction f; simpl; intros sigma va.
    - do 2 rewrite substitute_tm_preserves_eval_tm...
    - do 2 rewrite substitute_tm_preserves_eval_tm...
    - rewrite IHf...
    - rewrite IHf1, IHf2...
    - enough (claim1 : forall n : nat, eval_form (fun z : vr => if vr_eq_dec v z then n else eval_tm va (substitute_vr sigma z)) f <-> eval_form (fun z : vr => if vr_eq_dec (chi sigma (all_form v f)) z then n else va z) (substitute_form ((v, ivar_tm (chi sigma (all_form v f))) :: sigma) f)) by firstorder.
      intros n.
      rewrite <- (IHf ((v, ivar_tm (chi sigma (all_form v f))) :: sigma) (fun z : vr => if vr_eq_dec (chi sigma (all_form v f)) z then n else va z)).
      apply eval_form_extensionality.
      intros x H.
      simpl.
      case_vr_eq_dec v x.
      + case_vr_eq_dec v v.
        now case_vr_eq_dec (chi sigma (all_form v f)) (chi sigma (all_form v f)).
      + case_vr_eq_dec x v.
        apply eval_tm_extensionality.
        intros x' H2.
        simpl_vr_eq_dec.
        assert (claim1_aux1 : isFreshVarIn_substitute_form sigma (chi sigma (all_form v f)) (all_form v f)) by apply the_rule_of_chi.
        unfold isFreshVarIn_substitute_form in claim1_aux1.
        rewrite forallb_true_iff in claim1_aux1.
        enough (claim1_aux2 : negb (occursFreeIn_tm (chi sigma (all_form v f)) (substitute_vr sigma x)) = true) by now rewrite H2 in claim1_aux2.
        apply claim1_aux1, the_rule_of_getFreeVars_form.
        simpl_vr_eq_dec.
  Qed.

  Lemma substitute_tm_make_numeral :
    forall n : nat,
    forall sigma : substitution,
    substitute_tm sigma (make_numeral n) = make_numeral n.
  Proof with eauto.
    induction n; simpl; intros sigma...
    rewrite (IHn sigma)...
  Qed.

  Lemma occursFreeIn_tm_make_numeral :
    forall val : nat,
    forall x : vr,
    occursFreeIn_tm x (make_numeral val) = false.
  Proof with eauto.
    induction val; simpl...
  Qed.

  Lemma vr_eq_dec_is_Nat_eq_dec {A : Type} :
    forall x1 : A,
    forall x2 : A,
    forall z1 : vr,
    forall z2 : vr,
    (if vr_eq_dec z1 z2 then x1 else x2) = (if Nat.eq_dec z1 z2 then x1 else x2).
  Proof with firstorder.
    intros x1 x2 z1 z2.
    destruct (vr_eq_dec z1 z2); destruct (Nat.eq_dec z1 z2)...
  Qed.

  Ltac eval_vr_eq_dec :=
    repeat (rewrite vr_eq_dec_is_Nat_eq_dec; simpl)
  .

  Ltac simpl_eval_tm_make_numeral :=
    repeat (rewrite substitute_tm_make_numeral);
    repeat (rewrite eval_tm_make_numeral)
  .

  Ltac simpl_in_eval_tm_make_numeral H := 
    repeat (rewrite substitute_tm_make_numeral in H);
    repeat (rewrite eval_tm_make_numeral in H)
  .

  Ltac simplify_make_numeral :=
    repeat (rewrite substitute_tm_make_numeral);
    repeat (apply occursFreeIn_tm_make_numeral)
  .

  Ltac eval_in_vr_eq_dec H :=
    repeat (rewrite vr_eq_dec_is_Nat_eq_dec in H; simpl in H)
  .

  Ltac auto_show_it_is_sentence_aux1 :=
    tryif (apply orb_false_iff; split)
    then auto_show_it_is_sentence_aux1
    else (eval_vr_eq_dec; simplify_make_numeral)
  .

  Ltac auto_show_it_is_sentence :=
    repeat intro;
    auto_show_it_is_sentence_aux1
  .

  Fixpoint relation_of_arity (n : nat) : Type :=
    match n with
    | 0 => Prop
    | S n' => nat -> relation_of_arity n'
    end
  .

  Fixpoint lift_relation (n : nat) : relation_of_arity (S n) -> nat -> relation_of_arity n :=
    match n as n0 return relation_of_arity (S n0) -> nat -> relation_of_arity n0 with
    | 0 =>
      fun pred : nat -> Prop =>
      fun val : nat =>
      pred val
    | S n' =>
      fun pred : nat -> nat -> relation_of_arity n' =>
      fun val : nat =>
      fun val' : nat =>
      lift_relation n' (pred val') val 
    end
  .

  Fixpoint express_relation (n : nat) : form -> relation_of_arity n -> Prop :=
    match n as n0 return form -> relation_of_arity n0 -> Prop with
    | 0 =>
      fun f : form =>
      fun pred : Prop =>
      (forall x : vr, occursFreeIn_form x f = false) /\ (~ ~ pred <-> forall va : value_assignment, eval_form va f)
    | S n' =>
      fun f : form =>
      fun pred : nat -> relation_of_arity n' =>
      forall val : nat, express_relation n' (substitute_form [(n', make_numeral val)] f) (lift_relation n' pred val)
    end
  .

  Fixpoint function_of_arity (n : nat) : Type :=
    match n with
    | 0 => nat
    | S n' => nat -> function_of_arity n'
    end
  .

  Fixpoint lift_function (n : nat) : function_of_arity (S n) -> nat -> function_of_arity n :=
    match n as n0 return function_of_arity (S n0) -> nat -> function_of_arity n0 with
    | 0 =>
      fun func : nat -> nat =>
      fun val : nat =>
      func val
    | S n' =>
      fun func : nat -> nat -> function_of_arity n' =>
      fun val : nat =>
      fun val' : nat =>
      lift_function n' (func val') val 
    end
  .

  Fixpoint express_function (n : nat) : form -> function_of_arity n -> Prop :=
    match n as n0 return form -> function_of_arity n0 -> Prop with
    | 0 =>
      fun f : form =>
      fun func : nat =>
      forall val : nat,
      let f' : form := substitute_form [(0, make_numeral val)] f in
      (forall x : vr, occursFreeIn_form x f' = false) /\ (val = func <-> forall va : value_assignment, eval_form va f')
    | S n' =>
      fun f : form =>
      fun func : nat -> function_of_arity n' =>
      forall val : nat, express_function n' (substitute_form [(n, make_numeral val)] f) (lift_function n' func val)
    end
  .

  Example express_relation_example1 :
    express_relation 2 (leq_form (ivar_tm 0) (ivar_tm 1)) (fun x0 : nat => fun x1 : nat => x0 <= x1).
  Proof with (lia || eauto).
    simpl.
    intros val1 val2.
    split.
    - auto_show_it_is_sentence.
    - split.
      + intros H va.
        eval_vr_eq_dec.
        simpl_eval_tm_make_numeral...
      + intros H.
        assert (H0 := H (fun _ : vr => 0)).
        eval_in_vr_eq_dec H0.
        simpl_in_eval_tm_make_numeral H0...
  Qed.

  Example express_function_example1 :
    express_function 3 (eqn_form (ivar_tm 0) (plus_tm (ivar_tm 1) (plus_tm (ivar_tm 2) (ivar_tm 3)))) (fun x1 : nat => fun x2 : nat => fun x3 : nat => x1 + (x2 + x3)).
  Proof with eauto.
    simpl.
    intros val3 val2 val1 val0.
    split.
    - auto_show_it_is_sentence.
    - split.
      + intros H va.
        eval_vr_eq_dec.
        simpl_eval_tm_make_numeral...
      + intros H.
        assert (H0 := H (fun _ : vr => 0)).
        eval_in_vr_eq_dec H0.
        simpl_in_eval_tm_make_numeral H0...
  Qed.

*)

End SmullyanGIT.
