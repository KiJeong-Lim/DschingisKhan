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
Require Import DschingisKhan.Math.BasicGeneralTopology.

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
    ; trueBA_ann_orBA :> falseBA `isAnnihilatorFor` andBA
    ; andBA_idem :> Idem andBA
    ; orBA_idem :> Idem orBA
    ; Absorption_andBA_orBA :> Absorption andBA orBA
    ; andBA_notBA_falseBA (x : BA)
      : andBA x (notBA x) == falseBA
    ; orBA_notBA_trueBA (x : BA)
      : orBA x (notBA x) == trueBA
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

  Section section_2_of_chapter_1. (* Reference: << Constructive Completeness Proofs and Delimited Control >> written by "Danko Ilik" *)

  Context {BA : Type} {requiresSetoid : isSetoid BA} {requiresBooleanAlgebra : isBooleanAlgebra BA (requiresSetoid := requiresSetoid)}.

  Local Notation andBA := (andBA (BA := BA)).
  Local Notation andsBA := (andsBA (BA := BA)).

  Lemma andBA_intro_l (x1 : BA) (x2 : BA)
    : andBA x1 x2 =< x1.
  Proof.
    rewrite andBA_comm. cbn. now rewrite <- andBA_assoc, andBA_idem.
  Qed.

  Lemma andBA_intro_r (x1 : BA) (x2 : BA)
    : andBA x1 x2 =< x2.
  Proof.
    rewrite andBA_comm. eapply andBA_intro_l.
  Qed.

  Global Instance andBA_preserves_leProp2
    : preserves_leProp2 andBA.
  Proof.
    ii. cbn in *. transitivity (andBA (andBA lhs1 rhs1) (andBA lhs2 rhs2)).
    - repeat erewrite andBA_assoc.
      rewrite (andBA_comm (andBA lhs1 lhs2) rhs1).
      rewrite (andBA_assoc rhs1 lhs1 lhs2).
      rewrite (andBA_comm rhs1 lhs1).
      reflexivity.
    - now rewrite H_LE1, H_LE2.
  Qed.

  Lemma andsBA_app (xs1 : list BA) (xs2 : list BA)
    : andsBA (xs1 ++ xs2) == andBA (andsBA xs1) (andsBA xs2).
  Proof.
    ii. cbn. revert xs2. induction xs1 as [ | x1 xs1 IH]; simpl; ii.
    - symmetry. eapply trueBA_id_andBA.
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
    split; trivial. induction xs as [ | x xs IH]; simpl; ii; desnw.
    - des. eapply CLOSED_UPWARD with (x := x0); trivial. cbn. eapply trueBA_id_andBA.
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

  Lemma inconsistent_compatWith_eqProp (X : ensemble BA) (X' : ensemble BA)
    (IS_INCONSISTENT : inconsistent X)
    (X_eq_X' : X == X')
    : inconsistent X'.
  Proof.
    destruct IS_INCONSISTENT as [botBA [botBA_in_X botBA_eq_falseBA]].
    exists (botBA). split; [now eapply X_eq_X' | exact (botBA_eq_falseBA)].
  Qed.

  Definition isProperFilter (F : ensemble BA) : Prop :=
    << IS_FILTER : isFilter F >> /\ << IS_CONSISTENT : ~ inconsistent F >>
  .

  Lemma isProperFilter_compatWith_eqProp (F : ensemble BA) (F' : ensemble BA)
    (F_isProperFilter : isProperFilter F)
    (F_eq_F' : F == F')
    : isProperFilter F'.
  Proof.
    destruct F_isProperFilter; desnw. split; unnw.
    - eapply isFilter_compatWith_eqProp; eauto.
    - intros H_inconsistent. contradiction (IS_CONSISTENT).
      now eapply inconsistent_compatWith_eqProp with (X := F').
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

  Definition isElementCompleteFor (X : ensemble BA) (b : BA) : Prop :=
    forall EQUICONSISTENT : equiconsistent X (cl (insert b X)), member b X
  .

  Definition isComplete (X : ensemble BA) : Prop :=
    forall b : BA, isElementCompleteFor X b
  .

  End section_2_of_chapter_1.

End BooleanAlgebra.

Module CountableBooleanAlgebra.

  Import ListNotations MathProps MathClasses BasicPosetTheory BooleanAlgebra.

  Class isCBA (BA : Type) {requiresSetoid : isSetoid BA} : Type :=
    { CBA_requiresBooleanAlgebra :> isBooleanAlgebra BA
    ; CBA_requiresCountable :> isCountable BA
    }
  .

End CountableBooleanAlgebra.
