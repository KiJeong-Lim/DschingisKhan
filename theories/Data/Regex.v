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
  .

  Fixpoint evalRegex (re : regex) {struct re} : ensemble (list A) :=
    match re with
    | ReZero => empty
    | ReUnit => singleton []
    | ReChar ch => singleton [ch]
    | RePlus re1 re2 => union (evalRegex re1) (evalRegex re2)
    | ReMult re1 re2 => liftM2 (@app A) (evalRegex re1) (evalRegex re2)
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
