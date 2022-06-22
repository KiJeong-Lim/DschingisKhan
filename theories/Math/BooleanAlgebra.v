Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeUtil.
Require Import DschingisKhan.Math.BasicPosetTheory.

Module BooleanAlgebra.

  Import ListNotations MathProps MathClasses BasicPosetTheory.

  Create HintDb boolalg_hints.

  Class BooleanAlgebra_sig (BA : Type) : Type :=
    { andBA : BA -> BA -> BA
    ; orBA : BA -> BA -> BA
    ; notBA : BA -> BA
    ; trueBA : BA
    ; falseBA : BA
    }
  .

  Definition andsBA {BA : Type} {requiresBooleanAlgebraMethods : BooleanAlgebra_sig BA} : list BA -> BA := fold_right andBA trueBA.

  Class BooleanAlgebra_axiom (BA : Type) {requiresSetoid : isSetoid BA} {requiresBooleanAlgebraMethods : BooleanAlgebra_sig BA} : Prop :=
    { andBA_congru :> preserves_eqProp2 andBA
    ; orBA_congru :> preserves_eqProp2 orBA
    ; notBA_congru :> preserves_eqProp1 notBA
    ; andBA_assoc :> Assoc andBA
    ; orBA_assoc :> Assoc orBA
    ; andBA_comm :> Comm andBA
    ; orBA_comm :> Comm orBA
    ; andBA_distr_orBA :> andBA `distributesOver` orBA
    ; orBA_distr_andBA :> orBA `distributesOver` andBA
    ; trueBA_id_andBA :> trueBA `isIdentityOf` andBA
    ; falseBA_id_orBA :> falseBA `isIdentityOf` orBA
    ; falseBA_ann_andBA :> falseBA `isAnnihilatorFor` andBA
    ; trueBA_ann_orBA :> trueBA `isAnnihilatorFor` orBA
    ; andBA_idem :> Idem andBA
    ; orBA_idem :> Idem orBA
    ; Absorption_andBA_orBA :> Absorption andBA orBA
    ; andBA_notBA_falseBA
      : forall x : BA, andBA x (notBA x) == falseBA
    ; orBA_notBA_trueBA
      : forall x : BA, orBA x (notBA x) == trueBA
    }
  .

  Class isBooleanAlgebra (BA : Type) {requiresSetoid : isSetoid BA} : Type :=
    { hasBooleanAlgebraMethods :> BooleanAlgebra_sig BA
    ; BooleanAlgebra_obeysBooleanAlgebra_axiom :> BooleanAlgebra_axiom BA (requiresSetoid := requiresSetoid) (requiresBooleanAlgebraMethods := hasBooleanAlgebraMethods)
    }
  .

  Section BasicInstancesOfBooleanAlgebra.

  Local Instance bool_hasBooleanAlgebraMethods : BooleanAlgebra_sig bool :=
    { andBA := andb
    ; orBA := orb
    ; notBA := negb
    ; trueBA := true
    ; falseBA := false
    }
  .

  Local Instance bool_obeysBooleanAlgebra_axiom
    : BooleanAlgebra_axiom bool (requiresSetoid := theFinestSetoidOf bool) (requiresBooleanAlgebraMethods := bool_hasBooleanAlgebraMethods).
  Proof. (repeat (try split; repeat intros [ | ])); now cbn in *. Qed.

  Local Instance bool_isBooleanAlgebra : isBooleanAlgebra bool (requiresSetoid := theFinestSetoidOf bool) :=
    { hasBooleanAlgebraMethods := bool_hasBooleanAlgebraMethods
    ; BooleanAlgebra_obeysBooleanAlgebra_axiom := bool_obeysBooleanAlgebra_axiom
    }
  .

  End BasicInstancesOfBooleanAlgebra.

  Section BooleanAlgebraAsPoset.

  Context {BA : Type} {requiresSetoid : isSetoid BA} {requiresBooleanAlgebra : isBooleanAlgebra BA (requiresSetoid := requiresSetoid)}.

  Let leBA (lhs : BA) (rhs : BA) : Prop := andBA lhs rhs == lhs.

  Global Instance leBA_Reflexive
    : Reflexive leBA.
  Proof. intros x. eapply andBA_idem with (x := x). Qed.

  Global Instance leBA_Transitive
    : Transitive leBA.
  Proof. intros x y z x_le_y y_le_z. unfold leBA in *. rewrite <- x_le_y at 2. rewrite <- y_le_z. now rewrite andBA_assoc, x_le_y. Qed.

  Global Instance leBA_PreOrder : PreOrder leBA :=
    { PreOrder_Reflexive := leBA_Reflexive
    ; PreOrder_Transitive := leBA_Transitive
    }
  .

  Global Instance leBA_PartialOrder
    : PartialOrder eqProp leBA.
  Proof.
    intros lhs rhs. unfold leBA. split; unfold relation_conjunction, flip; cbn.
    - intros hyp_eq. rewrite hyp_eq. split; eapply leBA_Reflexive.
    - intros [hyp_le hyp_ge]. rewrite <- hyp_le. rewrite <- hyp_ge at 2. eapply andBA_comm.
  Qed.

  Global Instance BooleanAlgebra_isPoset : isPoset BA :=
    { leProp := leBA
    ; Poset_requiresSetoid := requiresSetoid
    ; leProp_PreOrder := leBA_PreOrder
    ; leProp_PartialOrder := leBA_PartialOrder
    }
  .

  End BooleanAlgebraAsPoset.

  Section section_2_of_chapter_1_PART1. (* Reference: << Constructive Completeness Proofs and Delimited Control >> written by "Danko Ilik" *)

  Context {BA : Type} {requiresSetoid : isSetoid BA} {requiresBooleanAlgebra : isBooleanAlgebra BA (requiresSetoid := requiresSetoid)}.

  Local Notation andBA := (andBA (BA := BA)).
  Local Notation andsBA := (andsBA (BA := BA)).

  Lemma andBA_le_intro_l (x1 : BA) (x2 : BA)
    : andBA x1 x2 =< x1.
  Proof. rewrite andBA_comm. cbn. now rewrite <- andBA_assoc, andBA_idem. Qed.

  Lemma andBA_le_intro_r (x1 : BA) (x2 : BA)
    : andBA x1 x2 =< x2.
  Proof. rewrite andBA_comm. eapply andBA_le_intro_l. Qed.

  Global Instance andBA_preserves_leProp2
    : preserves_leProp2 andBA.
  Proof.
    ii. cbn in *. transitivity (andBA (andBA lhs1 rhs1) (andBA lhs2 rhs2)).
    - repeat rewrite andBA_assoc.
      rewrite @commutativity with (Comm := andBA_comm) (x := andBA lhs1 lhs2) (y := rhs1).
      rewrite @associativity with (Assoc := andBA_assoc) (x := rhs1) (y := lhs1) (z := lhs2).
      rewrite @commutativity with (Comm := andBA_comm) (x := rhs1) (y := lhs1).
      reflexivity.
    - now rewrite H_LE1, H_LE2.
  Qed.

  Lemma andsBA_app (xs1 : list BA) (xs2 : list BA)
    : andsBA (xs1 ++ xs2) == andBA (andsBA xs1) (andsBA xs2).
  Proof.
    ii. cbn. revert xs2. induction xs1 as [ | x1 xs1 IH]; simpl; ii.
    - now rewrite @left_id with (IdElemOf := trueBA_id_andBA).
    - rewrite <- andBA_assoc. now rewrite IH.
  Qed.

  Lemma andsBA_zero
    : andsBA [] == trueBA.
  Proof. reflexivity. Qed.

  Lemma andsBA_one (x1 : BA)
    : andsBA [x1] == x1.
  Proof. cbn. eapply trueBA_id_andBA. Qed.

  Lemma andsBA_two (x1 : BA) (x2 : BA)
    : andsBA [x1; x2] == andBA x1 x2.
  Proof. replace ([x1; x2]) with ([x1] ++ [x2]); trivial. rewrite andsBA_app. now do 2 rewrite andsBA_one. Qed.

  Lemma falseBA_isBottom
    : forall x : BA, falseBA =< x.
  Proof. ii. red; simpl. eapply falseBA_ann_andBA. Qed.

  Lemma andsBA_le_In (xs : list BA) (x : BA)
    (x_in_xs : In x xs)
    : andsBA xs =< x.
  Proof.
    revert x x_in_xs.
    induction xs as [ | x1 xs1 IH]; simpl in *.
    - tauto.
    - intros x [x_eq_x1 | x_in_xs1].
      + subst x.
        rewrite <- @associativity with (Assoc := andBA_assoc) (x := x1) (y := andsBA xs1) (z := x1).
        rewrite @commutativity with (Comm := andBA_comm) (x := andsBA xs1) (y := x1).
        rewrite -> @associativity with (Assoc := andBA_assoc) (x := x1) (z := andsBA xs1) (y := x1).
        rewrite @idemponence with (Idem := andBA_idem) (x := x1).
        reflexivity.
      + rewrite <- @associativity with (Assoc := andBA_assoc) (x := x1) (y := andsBA xs1) (z := x).
        rewrite IH with (x := x) (x_in_xs := x_in_xs1).
        reflexivity.
  Qed.

  Variant isFilter (F : ensemble BA) : Prop :=
  | isFilterIf
    (CLOSED_andsBA : forall xs : list BA, ⟪ xs_isFiniteSubsetOfFilter : isFiniteSubsetOf xs F ⟫ -> member (andsBA xs) F)
    (CLOSED_UPWARD : forall x : BA, ⟪ x_inFilter : member x F ⟫ -> forall x' : BA, ⟪ x_le_x' : x =< x' ⟫ -> member x' F)
    : isFilter F
  .

  Lemma isFilter_intro (F : ensemble BA)
    (NONEMPTY : exists x0 : BA, member x0 F)
    (CLOSED_MEET : forall x1 : BA, forall x2 : BA, ⟪ x1_inFilter : member x1 F ⟫ -> ⟪ x2_inFilter : member x2 F ⟫ -> member (andBA x1 x2) F)
    (CLOSED_UPWARD : forall x : BA, ⟪ x_inFilter : member x F ⟫ -> forall x' : BA, ⟪ x_le_x' : x =< x' ⟫ -> member x' F)
    : isFilter F.
  Proof.
    split; trivial. induction xs as [ | x xs IH]; simpl; ii.
    - desnw. eapply CLOSED_UPWARD with (x := x0); trivial. cbn. eapply trueBA_id_andBA.
    - eapply CLOSED_MEET; [eapply CLOSED_UPWARD | eapply IH]; eauto with *.
  Qed.

  Lemma isFilter_compatWith_eqProp (F : ensemble BA) (F' : ensemble BA)
    (F_isFilter : isFilter F)
    (F_eq_F' : F == F')
    : isFilter F'.
  Proof.
    inversion F_isFilter. eapply isFilter_intro.
    - exists (trueBA). eapply F_eq_F'. now eapply CLOSED_andsBA with (xs := []).
    - ii; desnw. eapply F_eq_F'. eapply CLOSED_UPWARD with (x := andsBA [x1; x2]).
      + eapply CLOSED_andsBA. intros z [z_eq_x1 | [z_eq_x2 | []]]; subst z. all: now eapply F_eq_F'.
      + unnw. now rewrite andsBA_two.
    - ii; desnw. eapply F_eq_F'. eapply CLOSED_UPWARD with (x := x); unnw; trivial. now eapply F_eq_F'.
  Qed.

  Definition inconsistent (X : ensemble BA) : Prop :=
    exists botBA : BA, member botBA X /\ botBA == falseBA
  .

  Lemma inconsistent_compatWith_isSubsetOf (X : ensemble BA) (X' : ensemble BA)
    (INCONSISTENT : inconsistent X)
    (SUBSET : isSubsetOf X X')
    : inconsistent X'.
  Proof.
    destruct INCONSISTENT as [botBA [botBA_in_X botBA_eq_falseBA]].
    exists (botBA). split; [exact (SUBSET botBA botBA_in_X) | exact (botBA_eq_falseBA)].
  Qed.

  Global Add Parametric Morphism :
    inconsistent with signature (eqProp ==> iff)
    as inconsistent_compatWith_eqProp.
  Proof. intros X X' X_eq_X'. split; ii; eapply inconsistent_compatWith_isSubsetOf; eauto. all: intros z z_in; eapply X_eq_X'; eauto. Qed.

  Definition isProperFilter (F : ensemble BA) : Prop :=
    << IS_FILTER : isFilter F >> /\ << CONSISTENT : ~ inconsistent F >>
  .

  Lemma isProperFilter_compatWith_eqProp (F : ensemble BA) (F' : ensemble BA)
    (F_eq_F' : F == F')
    (F_isProperFilter : isProperFilter F)
    : isProperFilter F'.
  Proof.
    destruct F_isProperFilter; desnw. split; unnw.
    - eapply isFilter_compatWith_eqProp; eauto.
    - intros INCONSISTENT. contradiction (CONSISTENT). now rewrite F_eq_F'.
  Qed.

  Definition equiconsistent (X : ensemble BA) (X' : ensemble BA) : Prop :=
    inconsistent X <-> inconsistent X'
  .

  Global Instance equiconsistent_Equivalence : Equivalence equiconsistent :=
    relation_on_image_liftsEquivalence inconsistent iff_equivalence
  .

  Definition cl (X : ensemble BA) : ensemble BA :=
    fun x : BA => exists xs : list BA, ⟪ xs_isFiniteSubsetOf : isFiniteSubsetOf xs X ⟫ /\ ⟪ andsBA_xs_le : andsBA xs =< x ⟫
  .

  Lemma fact1_of_1_2_8 (X : ensemble BA)
    : isFilter (cl X).
  Proof with eauto with *.
    eapply isFilter_intro.
    - exists (trueBA). exists ([]). unnw. split.
      + intros z z_in. inversion z_in.
      + rewrite andsBA_zero...
    - ii; desnw.
      destruct x1_inFilter as [xs1 [xs1_isFiniteSubsetOf andsBA_xs1_le]]; unnw.
      destruct x2_inFilter as [xs2 [xs2_isFiniteSubsetOf andsBA_xs2_le]]; unnw.
      exists (xs1 ++ xs2). unnw. split.
      + eapply isFiniteSubsetOf_append...
      + rewrite andsBA_app. eapply andBA_preserves_leProp2...
    - ii; desnw. destruct x_inFilter as [xs [? ?]]; desnw.
      exists (xs). unnw. split; [ | etransitivity]...
  Qed.

  Lemma fact2_of_1_2_8 (X : ensemble BA)
    (X_isFilter : isFilter X)
    : member trueBA X.
  Proof.
    inversion X_isFilter. eapply CLOSED_UPWARD with (x := andsBA []).
    - eapply CLOSED_andsBA. intros z z_in. inversion z_in.
    - red. reflexivity.
  Qed.

  Lemma fact3_of_1_2_8 (X : ensemble BA)
    : isSubsetOf X (cl X).
  Proof with eauto with *.
    intros b b_in. exists ([b]). unnw. split.
    - intros z [z_eq_b | []]; subst z...
    - rewrite andsBA_one...
  Qed.

  Lemma fact4_of_1_2_8 (X : ensemble BA) (X' : ensemble BA)
    (X_isSubsetOf_X' : isSubsetOf X X')
    : isSubsetOf (cl X) (cl X').
  Proof.
    intros b b_in. destruct b_in as [xs [? ?]]; desnw.
    exists (xs); unnw. split; eauto with *.
  Qed.

  Lemma fact5_of_1_2_8 (X : ensemble BA)
    (X_isFilter : isFilter X)
    : isSubsetOf (cl X) X.
  Proof.
    intros b b_in. destruct b_in as [xs [? ?]]; desnw.
    inversion X_isFilter. eauto with *.
  Qed.

  Global Instance cl_preserves_leProp : preserves_leProp1 cl := fact4_of_1_2_8.

  Lemma proposition1_of_1_2_9 (X : ensemble BA)
    (X_isFilter : isFilter X)
    : forall b : BA, member b X -> forall b' : BA, b == b' -> member b' X.
  Proof. ii. inversion X_isFilter. eauto with *. Qed.

  Definition isElementCompleteFor (X : ensemble BA) (b : BA) : Prop :=
    forall EQUICONSISTENT : equiconsistent X (cl (insert b X)), member b X
  .

  Definition isComplete (X : ensemble BA) : Prop :=
    forall b : BA, isElementCompleteFor X b
  .

  Variant isUltraFilter (F : ensemble BA) : Prop :=
  | isUltraFilterIf
    (IS_FILTER : isFilter F)
    (ULTRAFILTER : forall F' : ensemble BA, << IS_FILTER' : isFilter F' >> -> forall EQUICONSISTENT : equiconsistent F F', << SUBSET : isSubsetOf F F' >> -> F == F')
    : isUltraFilter F
  .

  End section_2_of_chapter_1_PART1.

End BooleanAlgebra.

Module CountableBooleanAlgebra.

  Import ListNotations MathProps MathClasses BasicPosetTheory BooleanAlgebra.

  Class isCBA (BA : Type) {requiresSetoid : isSetoid BA} : Type :=
    { CBA_requiresBooleanAlgebra :> isBooleanAlgebra BA
    ; CBA_requiresCountable :> isCountable BA
    }
  .

  Section section_2_of_chapter_1_PART2. (* Reference: << Constructive Completeness Proofs and Delimited Control >> written by "Danko Ilik" *)

  Context {BA : Type} {requiresSetoid : isSetoid BA} {requiresCBA : isCBA BA (requiresSetoid := requiresSetoid)}.

  Variant insertion (X : ensemble BA) (n : nat) : ensemble BA :=
  | In_insertion
    (EQUICONSISTENT : equiconsistent X (cl (insert (enum n) X)))
    : member (enum n) (insertion X n)
  .

  Definition Insertion (X : ensemble BA) (n : nat) : ensemble BA := union X (insertion X n).

  Definition iterInsertion (X : ensemble BA) : nat -> ensemble BA :=
    fix iterInsertion_fix (n : nat) {struct n} : ensemble BA :=
    match n with
    | O => X
    | S n' => cl (Insertion (iterInsertion_fix n') n')
    end
  .

  Definition completeFilterOf (X : ensemble BA) : ensemble BA :=
    fun b : BA => exists n : nat, member b (iterInsertion X n)
  .

  Lemma lemma1_of_1_2_11 (n : nat)
    : forall X : ensemble BA, << IS_FILTER : isFilter X >> -> isFilter (iterInsertion X n).
  Proof.
    induction n as [ | n IH]; simpl; eauto.
    ii; desnw. eapply fact1_of_1_2_8.
  Qed.

  Lemma lemma1_of_1_2_12 (n1 : nat) (n2 : nat) (n1_le_n2 : n1 <= n2)
    : forall X : ensemble BA, isSubsetOf (iterInsertion X n1) (iterInsertion X n2).
  Proof with eauto with *.
    induction n1_le_n2 as [ | n2 n1_le_n2 IH]; intros X...
    rewrite IH with (X := X). transitivity (Insertion (iterInsertion X n2) n2).
    - intros z z_in; left...
    - simpl; eapply fact3_of_1_2_8...
  Qed.

  Lemma lemma1_of_1_2_13_aux1 (bs : list BA) (F : ensemble BA) (n : nat)
    (F_isFilter : isFilter F)
    (FINITE_SUBSET : isFiniteSubsetOf bs (union (iterInsertion F n) (insertion (iterInsertion F n) n)))
    : member (andsBA bs) (iterInsertion F n) \/ (exists b : BA, In b bs /\ member b (insertion (iterInsertion F n) n)).
  Proof.
    revert F n F_isFilter FINITE_SUBSET. induction bs as [ | b1 bs1 IH]; simpl; ii.
    - left. now eapply fact2_of_1_2_8, lemma1_of_1_2_11.
    - pose proof (lemma1_of_1_2_11 n F F_isFilter) as claim1. inversion claim1. unnw.
      assert (H_IN : member b1 (iterInsertion F n) \/ member b1 (insertion (iterInsertion F n) n)).
      { rewrite <- in_union_iff. eapply FINITE_SUBSET. now left. }
      assert (claim2 : isFiniteSubsetOf bs1 (union (iterInsertion F n) (insertion (iterInsertion F n) n))).
      { unfold isFiniteSubsetOf in *. ii. eapply FINITE_SUBSET. now right. }
      specialize (IH F n F_isFilter claim2). destruct IH as [IH | [b [b_in b_in_insertion]]].
      { destruct H_IN as [H_IN | H_IN].
        - left. eapply CLOSED_andsBA with (xs := b1 :: bs1).
          intros z [z_eq_b | z_in_bs1].
          + now subst z.
          + eapply CLOSED_UPWARD with (x := andsBA bs1); trivial.
            now eapply andsBA_le_In.
        - right. exists (b1). split; trivial. now left.
      }
      { right. exists (b). split; trivial. now right. }
  Qed.

  Lemma lemma1_of_1_2_13_aux2 (X : ensemble BA) (n : nat)
    : isSubsetOf (Insertion (iterInsertion X n) n) (insert (enum n) (iterInsertion X n)).
  Proof.
    intros z [z_in | z_in]; [right | left]; trivial.
    inversion z_in; subst. reflexivity.
  Qed.

  Lemma lemma1_of_1_2_13 (F : ensemble BA) (n : nat)
    (F_isFilter : isFilter F)
    : equiconsistent F (iterInsertion F n).
  Proof.
    revert F F_isFilter. induction n as [ | n IH]; simpl; ii.
    - reflexivity.
    - rewrite IH with (F_isFilter := F_isFilter) at 1.
      split; intros INCONSISTENT.
      { eapply inconsistent_compatWith_isSubsetOf.
        - exact INCONSISTENT.
        - rewrite <- fact3_of_1_2_8.
          ii; now left.
      }
      { destruct INCONSISTENT as [botBA [botBA_in botBA_eq_falseBA]].
        destruct botBA_in as [xs [? ?]]; desnw.
        pose proof (lemma1_of_1_2_11 n F F_isFilter) as claim1. inversion claim1; unnw.
        assert (claim2 : isSubsetOf (cl (Insertion (iterInsertion F n) n)) (cl (insert (enum n) (iterInsertion F n)))).
        { eapply fact4_of_1_2_8, lemma1_of_1_2_13_aux2. }
        pose proof (lemma1_of_1_2_13_aux1 xs F n F_isFilter xs_isFiniteSubsetOf) as [H_in | [b [b_in b_in_insertion]]].
        - exists (andBA botBA (andsBA xs)). split.
          + eapply CLOSED_UPWARD with (x := andsBA xs); trivial.
            rewrite <- andsBA_xs_le, andBA_idem. reflexivity.
          + rewrite botBA_eq_falseBA. change (falseBA =< andsBA xs).
            eapply falseBA_isBottom.
        - inversion b_in_insertion; subst. eapply EQUICONSISTENT. exists (andsBA xs). split.
          + eapply claim2. exists (xs). split; unnw; trivial. reflexivity.
          + eapply @leProp_Antisymmetric with (requiresPoset := BooleanAlgebra_isPoset).
            { now rewrite <- botBA_eq_falseBA. }
            { eapply falseBA_isBottom. }
      }
  Qed.

  Lemma lemma2_of_1_2_13 (F : ensemble BA) (n1 : nat) (n2 : nat)
    (F_isFilter : isFilter F)
    : equiconsistent (iterInsertion F n1) (iterInsertion F n2).
  Proof.
    transitivity (F).
    - symmetry. now eapply lemma1_of_1_2_13.
    - now eapply lemma1_of_1_2_13.
  Qed.

  Lemma lemma3_of_1_2_13 (F : ensemble BA)
    (F_isFilter : isFilter F)
    : equiconsistent F (completeFilterOf F).
  Proof.
    split; intros [botBA [botBA_in botBA_eq_falseBA]].
    - exists (botBA). split.
      + exists (0). trivial.
      + trivial.
    - destruct botBA_in as [n H_IN].
      eapply lemma1_of_1_2_13; trivial.
      exists (botBA); eauto.
  Qed.

  Theorem theorem_of_1_2_14_aux1 (F : ensemble BA) (n : nat)
    (F_isFilter : isFilter F)
    (EQUICONSISTENT : equiconsistent (completeFilterOf F) (cl (insert (enum n) (completeFilterOf F))))
    : equiconsistent (iterInsertion F n) (cl (insert (enum n) (iterInsertion F n))).
  Proof.
    split.
    - intros [botBA [botBA_in botBA_eq_falseBA]].
      exists (botBA). split; trivial.
      eapply fact3_of_1_2_8. now right.
    - intros INCONSISTENT.
      pose proof (claim1 := lemma1_of_1_2_13 F n F_isFilter).
      pose proof (claim2 := lemma3_of_1_2_13 F F_isFilter).
      assert (claim3 : inconsistent (cl (insert (enum n) (completeFilterOf F)))).
      { eapply inconsistent_compatWith_isSubsetOf.
        - exact (INCONSISTENT).
        - eapply fact4_of_1_2_8.
          intros z z_in. apply in_insert_iff in z_in. destruct z_in as [eq_z | z_in].
          + subst z. now left.
          + right. now exists (n).
      }
      unfold equiconsistent in *. tauto. 
  Qed.

  Variant propertiesOfFilter (F : ensemble BA) : Prop :=
  | propertiesOfFilter_areTheFollowings
    (SUBSET : isSubsetOf F (completeFilterOf F))
    (IS_FILTER : isFilter (completeFilterOf F))
    (COMPLETE : isComplete (completeFilterOf F))
    (EQUICONSISTENT : equiconsistent F (completeFilterOf F))
    : propertiesOfFilter F
  .

  Theorem theorem_of_1_2_14 (F : ensemble BA)
    (F_isFilter : isFilter F)
    : propertiesOfFilter F.
  Proof.
    inversion F_isFilter. split.
    - intros z z_in. exists (0). trivial.
    - eapply isFilter_intro.
      + exists (trueBA). exists (0). eapply fact2_of_1_2_8. trivial.
      + ii; desnw. destruct x1_inFilter as [n1 H_IN1]. destruct x2_inFilter as [n2 H_IN2].
        pose proof (n_le_m_or_m_lt_n_holds_for_any_n_and_any_m n1 n2) as [n1_le_n2 | n2_lt_n1].
        { pose proof (lemma1_of_1_2_12 n1 n2 n1_le_n2 F x1 H_IN1) as claim1.
          pose proof (lemma1_of_1_2_11 n2 F F_isFilter) as [claim2 claim3].
          exists (n2). eapply claim3 with (x := andsBA [x1; x2]); unnw.
          - eapply claim2. now intros z [z_eq | [z_eq | []]]; subst z.
          - now rewrite andsBA_two.
        }
        { pose proof (lemma1_of_1_2_12 n2 n1 (le_transitivity (le_S _ _ le_reflexitivity) n2_lt_n1) F x2 H_IN2) as claim1.
          pose proof (lemma1_of_1_2_11 n1 F F_isFilter) as [claim2 claim3].
          exists (n1). eapply claim3 with (x := andsBA [x1; x2]); unnw.
          - eapply claim2. now intros z [z_eq | [z_eq | []]]; subst z.
          - now rewrite andsBA_two.
        }
      + ii; desnw. destruct x_inFilter as [n H_IN].
        pose proof (lemma1_of_1_2_11 n F F_isFilter) as [claim1 claim2].
        exists (n). eapply claim2; eauto.
    - ii. pose proof (enum_isSurjective b) as [n b_eq_enum_n]; unnw. subst b.
      pose proof (claim1 := theorem_of_1_2_14_aux1 F n F_isFilter EQUICONSISTENT).
      exists (1 + n). simpl. exists ([enum n]). split.
      + intros z [z_eq | []]; subst z. right. now econstructor.
      + unnw. now rewrite andsBA_one.
    - now eapply lemma3_of_1_2_13.
  Qed.

  Corollary corollary_of_1_2_16_aux1 (X : ensemble BA) (F : ensemble BA) (b : BA)
    (EQUICONSISTENT : equiconsistent (completeFilterOf X) F)
    (SUBSET : isSubsetOf (completeFilterOf X) F)
    (H_IN : member b F)
    (INCONSISTENT : inconsistent (cl (insert b (completeFilterOf X))))
    : inconsistent (cl (insert b F)).
  Proof.
    assert (claim1 : isSubsetOf (insert b (completeFilterOf X)) (insert b F)).
    { intros z [z_in | z_in]; [now left | right; now eapply SUBSET]. }
    destruct INCONSISTENT as [botBA [botBA_in botBA_eq_falseBA]].
    assert (claim2 : isSubsetOf (cl (insert b (completeFilterOf X))) (cl (insert b F))).
    { now eapply fact4_of_1_2_8. }
    exists (botBA). split; trivial. now eapply claim2.
  Qed.

  Corollary corollary_of_1_2_16_aux2 (X : ensemble BA) (F : ensemble BA)
    (F_isFilter : isFilter F)
    (EQUICONSISTENT : equiconsistent (completeFilterOf X) F)
    (SUBSET : isSubsetOf (completeFilterOf X) F)
    : forall b : BA, member b F -> equiconsistent (completeFilterOf X) (cl (insert b (completeFilterOf X))).
  Proof.
    intros b H_IN.
    assert (claim1 : isSubsetOf (cl (insert b F)) (cl F)).
    { eapply fact4_of_1_2_8. intros z [z_in | z_in]; trivial. repeat red in z_in. congruence. }
    split; intros INCONSISTENT.
    - destruct INCONSISTENT as [botBA [botBA_in botBA_eq_falseBA]].
      exists (botBA). split; trivial.
      eapply fact3_of_1_2_8. now right.
    - eapply EQUICONSISTENT.
      pose proof (corollary_of_1_2_16_aux1 X F b EQUICONSISTENT SUBSET H_IN INCONSISTENT) as [botBA [botBA_in botBA_eq_falseBA]].
      exists (botBA). split; trivial.
      eapply fact5_of_1_2_8; trivial.
      now eapply claim1.
  Qed.

  Corollary corollary_of_1_2_16 (F : ensemble BA)
    (F_isFilter : isFilter F)
    : isUltraFilter (completeFilterOf F).
  Proof.
    pose proof (theorem_of_1_2_14 F F_isFilter) as [? ? ? ?]. split; trivial.
    intros F' IS_FILTER' EQUICONSISTENT' SUBSET' b; unnw. split.
    - exact (SUBSET' b).
    - intros H_IN.
      enough (claim1 : equiconsistent (completeFilterOf F) (cl (insert b (completeFilterOf F)))) by now eapply COMPLETE.
      eapply corollary_of_1_2_16_aux2; eauto.
  Qed.

  End section_2_of_chapter_1_PART2.

End CountableBooleanAlgebra.
