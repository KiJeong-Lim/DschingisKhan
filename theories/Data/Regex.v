Require Import Coq.Lists.List.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.

Module RegularExpressions.

  Import ListNotations.

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

  Inductive langStar (L : ensemble (list A)) : ensemble (list A) :=
  | langStar_zero
    : [] \in langStar L
  | langStar_succ (str1 : list A) (str2 : list A)
    (str1_in : str1 \in L)
    (str2_in : str2 \in langStar L)
    : str1 ++ str2 \in langStar L
  .

  Fixpoint evalRegex (re : regex) {struct re} : ensemble (list A) :=
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

  End REGULAR_EXPRESSION.

  Global Arguments regex : clear implicits.

End RegularExpressions.
