Require Import DschingisKhan.Prelude.

Module CountableBooleanAlgebra.

  Import UndergraduateAlgebra.

  Class isBooleanAlgebra (BA : Hask.t) {requiresSetoid : isSetoid BA} : Type :=
    { BooleanAlgebra_requiresRing :> isRing BA
    ; and_idempotent (x : BA) :
      mul x x == x
    }
  .

  Section TheoryOfBooleanAlgebra.

  Context {BA : Hask.t} {requiresSetoid : isSetoid BA} {requiresBooleanAlgebra : isBooleanAlgebra BA (requiresSetoid := requiresSetoid)}.

  Local Notation or := plu.

  Local Notation false := zer.

  Local Notation and := mul.

  Local Notation true := unity.

(**
  Lemma orBA_idempotent (x : BA)
    : or x x == x.
  *)

  End TheoryOfBooleanAlgebra.

  Class isCBA (BA : Hask.t) {requiresSetoid : isSetoid BA} : Type :=
    { CBA_requiresBooleanAlgebra :> isBooleanAlgebra BA (requiresSetoid := requiresSetoid)
    ; CBA_requiresCountable :> isCountable BA
    }
  .

End CountableBooleanAlgebra.
