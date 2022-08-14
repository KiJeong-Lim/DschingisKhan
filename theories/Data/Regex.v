Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.

Module RegularExpressions.

  Import ListNotations MathClasses.

  Section REGULAR_EXPRESSION.

  Context {A : Type}.

  Inductive regex : Type :=
  | ReZero : regex
  | ReUnit : regex
  | ReChar (ch : A) : regex
  | RePlus (re1 : regex) (re2 : regex) : regex
  | ReMult (re1 : regex) (re2 : regex) : regex
  | ReStar (re1 : regex) : regex
  .

  Let lang : Type := ensemble (list A).

  Inductive langStar (L : lang) : lang :=
  | nil_in_langStar
    : [] \in langStar L
  | app_in_langStar (str1 : list A) (str2 : list A)
    (H_IN1 : str1 \in L)
    (H_IN2 : str2 \in langStar L)
    : str1 ++ str2 \in langStar L
  .

  Global Add Parametric Morphism :
    langStar with signature (eqProp ==> eqProp)
    as langStar_compatWith_eqProp.
  Proof with eauto with *.
    enough (to_show : forall L : lang, forall L' : lang, L == L' -> forall str : list A, str \in langStar L -> str \in langStar L').
    { iis... }
    intros L L' H_EQ str H_IN. revert L' H_EQ.
    induction H_IN as [ | str1 str2 H_IN1 H_IN2 IH]; ii.
    - econstructor 1.
    - econstructor 2... rewrite <- H_EQ...
  Qed.

  Fixpoint evalRegex (re : regex) {struct re} : lang :=
    match re with
    | ReZero => empty
    | ReUnit => singleton []
    | ReChar ch => singleton [ch]
    | RePlus re1 re2 => union (evalRegex re1) (evalRegex re2)
    | ReMult re1 re2 => liftM2 (@app A) (evalRegex re1) (evalRegex re2)
    | ReStar re1 => langStar (evalRegex re1)
    end
  .

  Lemma evalRegex_ReMult_iff (re1 : regex) (re2 : regex)
    : forall str : list A, str \in evalRegex (ReMult re1 re2) <-> (exists str1 : list A, exists str2 : list A, str1 \in evalRegex re1 /\ str2 \in evalRegex re2 /\ str = str1 ++ str2).
  Proof.
    iis.
    - intros [str1 [H_IN1 [str2 [H_IN2 H_EQ]]]].
      exists (str1), (str2). now firstorder.
    - intros [str1 [str2 [H_IN1 [H_IN2 H_EQ]]]].
      exists (str1). split; trivial.
      exists (str2). split; trivial.
      now rewrite H_EQ.
  Qed.

  Global Instance regex_isSetoid : isSetoid regex :=
    { eqProp (lhs : regex) (rhs : regex) := forall str : list A, str \in evalRegex lhs <-> str \in evalRegex rhs
    ; eqProp_Equivalence := relation_on_image_liftsEquivalence evalRegex (@eqProp_Equivalence (ensemble (list A)) (ensemble_isSetoid (list A)))
    }
  .

  Global Add Parametric Morphism :
    ReChar with signature (eq ==> eqProp)
    as ReChar_congruence.
  Proof. now firstorder. Qed.

  Global Instance RePlus_preserves_eqProp
    : preserves_eqProp2 RePlus.
  Proof. now firstorder. Qed.

  Global Instance ReMult_preserves_eqProp
    : preserves_eqProp2 ReMult.
  Proof. now firstorder. Qed.

  Global Instance ReStar_preserves_eqProp
    : preserves_eqProp1 ReStar.
  Proof. now firstorder using langStar_compatWith_eqProp. Qed.

  Global Instance RePlus_assoc
    : Assoc RePlus.
  Proof. iis; now firstorder. Qed.

  Global Instance RePlus_comm
    : Comm RePlus.
  Proof. iis; now firstorder. Qed.

  Global Instance ReZero_id_RePlus
    : ReZero `isIdentityOf` RePlus.
  Proof. iis; now firstorder. Qed.

  Global Instance ReMult_assoc
    : Assoc ReMult.
  Proof with eauto with *.
    iis.
    - intros H_IN. rewrite evalRegex_ReMult_iff in H_IN.
      destruct H_IN as [str1 [str' [H_IN1 [H_IN' ?]]]]; subst str.
      rewrite evalRegex_ReMult_iff in H_IN'.
      destruct H_IN' as [str2 [str3 [H_IN2 [H_IN3 ?]]]]; subst str'.
      rewrite evalRegex_ReMult_iff. exists (str1 ++ str2), (str3).
      split... rewrite evalRegex_ReMult_iff...
    - intros H_IN. rewrite evalRegex_ReMult_iff in H_IN.
      destruct H_IN as [str' [str3 [H_IN' [H_IN3 ?]]]]; subst str.
      rewrite evalRegex_ReMult_iff in H_IN'.
      destruct H_IN' as [str1 [str2 [H_IN1 [H_IN2 ?]]]]; subst str'.
      rewrite evalRegex_ReMult_iff. exists (str1), (str2 ++ str3).
      split... split... rewrite evalRegex_ReMult_iff...
  Qed.

  Global Instance ReMult_distr_RePlus
    : ReMult `distributesOver` RePlus.
  Proof. iis; now firstorder. Qed.

  Global Instance ReUnit_id_ReMult
    : ReUnit `isIdentityOf` ReMult.
  Proof with now firstorder.
    split; iis.
    - rewrite evalRegex_ReMult_iff; unnw.
      intros [str1 [str2 [H_IN1 [H_IN2 ?]]]]; subst str.
      do 3 red in H_IN1; subst str1.
      rewrite app_nil_l; exact (H_IN2).
    - intros H_IN; rewrite evalRegex_ReMult_iff.
      exists ([]), (str); rewrite app_nil_l...
    - rewrite evalRegex_ReMult_iff; unnw.
      intros [str1 [str2 [H_IN1 [H_IN2 ?]]]]; subst str.
      do 3 red in H_IN2; subst str2.
      rewrite app_nil_r; exact (H_IN1).
    - intros H_IN; rewrite evalRegex_ReMult_iff.
      exists (str), ([]); rewrite app_nil_r...
  Qed.

  Global Instance regex_has_add : Has_add regex := RePlus.

  Global Instance regex_has_zero : Has_zero regex := ReZero.

  Global Instance regex_has_mul : Has_mul regex := ReMult.

  Global Instance regex_has_unity : Has_unity regex := ReUnit.

  Global Instance regex_isSemigroup : isSemigroup regex :=
    { Semigroup_has_add := regex_has_add
    ; Semigroup_add_congru := RePlus_preserves_eqProp
    ; Semigroup_add_assoc := RePlus_assoc
    }
  .

  Global Instance regex_isMonoid : isMonoid regex :=
    { Monoid_hasSemigroup := regex_isSemigroup
    ; Monoid_has_zero := regex_has_zero
    ; Monoid_zero_id_add := ReZero_id_RePlus
    }
  .

  Global Instance regex_isRig : isRig regex :=
    { Rig_hasMonoid := regex_isMonoid
    ; Rig_has_mul := regex_has_mul
    ; Rig_has_unity := regex_has_unity
    ; Rig_add_comm := RePlus_comm
    ; Rig_unity_id_mul := {| Monoid_requiresSemigroup := {| Semigroup_requiresMagma := ReMult_preserves_eqProp; Semigroup_requiresAssoc := ReMult_assoc |}; Monoid_requiresIdElem := ReUnit_id_ReMult |}
    ; Rig_mul_distr_add := ReMult_distr_RePlus
    }
  .

  End REGULAR_EXPRESSION.

  Global Arguments regex : clear implicits.

End RegularExpressions.
