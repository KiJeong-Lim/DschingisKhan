Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeLtac.
Require Import DschingisKhan.Prelude.PreludeMath.

Module CountableBooleanAlgebra.

  Import BasicMath UndergraduateAlgebra.

  Class isBooleanAlgebra (BA : Hask.t) {requiresSetoid : isSetoid BA} : Type :=
    { BooleanAlgebra_requiresRing :> isRing BA
    ; and_idempotent (x : BA) :
      mul x x == x
    }
  .

  Section TheoryOfBooleanAlgebra.

  Context {BA : Hask.t} {requiresSetoid : isSetoid BA} {requiresBooleanAlgebra : isBooleanAlgebra BA (requiresSetoid := requiresSetoid)}.

  Definition or_BA : BA -> BA -> BA := plu.

  Definition true_BA : BA := zer.

  Definition and_BA : BA -> BA -> BA := mul.

  Definition false_BA : BA := unity.

(**
  Lemma or_idempotent (x : BA)
    : and_BA x x == x.
  *)

  End TheoryOfBooleanAlgebra.

  Class isCBA (BA : Hask.t) {requiresSetoid : isSetoid BA} : Type :=
    { CBA_requiresBooleanAlgebra :> isBooleanAlgebra BA
    ; CBA_requiresCountable :> isCountable BA
    }
  .

End CountableBooleanAlgebra.
