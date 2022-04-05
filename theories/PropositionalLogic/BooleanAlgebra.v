Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeLtac.
Require Import DschingisKhan.Prelude.PreludeMath.

Module CountableBooleanAlgebra.

  Import UndergraduateAlgebra.

  Class isBooleanAlgebra (B : Hask.t) {requiresSetoid : isSetoid B} : Type :=
    { BooleanAlgebra_requiresRing :> isRing B
    ; mul_idempotent (x : B) :
      mul x x == x
    }
  .

  Section TheoryOfBooleanAlgebra.

  Variable B : Hask.t.

  Context {requiresSetoid : isSetoid B} {requiresBooleanAlgebra : isBooleanAlgebra B (requiresSetoid := requiresSetoid)}.

(**
  Local Instance and_isCommutative
    : isCommutativeBinaryOperation mul.
  *)

  End TheoryOfBooleanAlgebra.

End CountableBooleanAlgebra.
