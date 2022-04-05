Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeLtac.
Require Import DschingisKhan.Prelude.PreludeMath.

Module CountableBooleanAlgebra.

  Import BasicMath UndergraduateAlgebra.

  Class isBooleanAlgebra (BA : Hask.t) {requiresSetoid : isSetoid BA} : Type :=
    { BooleanAlgebra_requiresRing :> isRing BA
    ; mul_idempotent (x : BA) :
      mul x x == x
    }
  .

  Section TheoryOfBooleanAlgebra.

  Variable BA : Hask.t.

  Context {requiresSetoid : isSetoid BA} {requiresBooleanAlgebra : isBooleanAlgebra BA (requiresSetoid := requiresSetoid)}.

(**
  Local Instance and_isCommutative
    : isCommutativeBinaryOperation mul.
  *)

  End TheoryOfBooleanAlgebra.

  Class isCBA (BA : Hask.t) {requiresSetoid : isSetoid BA} : Type :=
    { CBA_requiresBooleanAlgebra :> isBooleanAlgebra BA
    ; CBA_isCountable :> isCountable BA
    }
  .

End CountableBooleanAlgebra.
