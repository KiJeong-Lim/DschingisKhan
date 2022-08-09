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
  | langStar_zero
    : [] \in langStar L
  | langStar_succ (str1 : list A) (str2 : list A)
    (str1_in : str1 \in L)
    (str2_in : str2 \in langStar L)
    : str1 ++ str2 \in langStar L
  .

  Global Add Parametric Morphism :
    langStar with signature (eqProp ==> eqProp)
    as langStar_compatWith_eqProp.
  Proof with eauto with *.
    enough (to_show : forall L : lang, forall L' : lang, L == L' -> forall str : list A, str \in langStar L -> str \in langStar L').
    { iis... }
    intros L L' H_EQ str H_IN. induction H_IN as [ | str1 str2 H_IN_L H_IN IH].
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

  Global Instance regex_isSetoid : isSetoid regex :=
    { eqProp (lhs : regex) (rhs : regex) := evalRegex lhs == evalRegex rhs
    ; eqProp_Equivalence := relation_on_image_liftsEquivalence evalRegex (@eqProp_Equivalence (ensemble (list A)) (ensemble_isSetoid (list A)))
    }
  .

  Global Instance RePlus_preserves_eqProp
    : preserves_eqProp2 RePlus.
  Proof. now firstorder. Qed.

  Global Instance ReMult_preserves_eqProp
    : preserves_eqProp2 ReMult.
  Proof. now firstorder. Qed.

  Global Instance ReStar_preserves_eqProp
    : preserves_eqProp1 ReStar.
  Proof with eauto.
    intros re1 re1' H_EQ1. do 2 red in H_EQ1.
    do 2 red. simpl evalRegex. intros str. split.
    - intros H_IN; inversion H_IN; subst; econstructor; rewrite <- H_EQ1...
    - intros H_IN; inversion H_IN; subst; econstructor; rewrite -> H_EQ1...
  Qed.

  Global Instance regex_has_add : Has_add regex := RePlus.

  Global Instance regex_has_zero : Has_zero regex := ReZero.

  Global Instance regex_has_mul : Has_mul regex := ReMult.

  Global Instance regex_has_unity : Has_unity regex := ReUnit.

  End REGULAR_EXPRESSION.

  Global Arguments regex : clear implicits.

End RegularExpressions.
