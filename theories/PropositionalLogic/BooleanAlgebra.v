Require Import DschingisKhan.Prelude.

Module CountableBooleanAlgebra.

  Class BooleanAlgebra_sig (BA : Hask.t) : Type :=
    { andBA : BA -> BA -> BA
    ; orBA : BA -> BA -> BA
    ; notBA : BA -> BA
    ; trueBA : BA
    ; falseBA : BA
    }
  .

  Class isBooleanAlgebra (BA : Hask.t) {requiresSetoid : isSetoid BA} : Type :=
    { BooleanAlgebra_methods :> BooleanAlgebra_sig BA
    ; andBA_lifts_eqProp :> isBinaryOperationCompatibleWithSetoid andBA
    ; orBA_lifts_eqProp :> isBinaryOperationCompatibleWithSetoid orBA
    ; notBA_lifts_eqProp :> isUnaryOperationCompatibleWithSetoid notBA
    ; andBA_assoc :> isAssociativeBinaryOperation andBA
    ; orBA_assoc :> isAssociativeBinaryOperation orBA
    ; andBA_idem :> isIdempotentBinaryOperation andBA
    ; orBA_idem :> isIdempotentBinaryOperation andBA
    ; andBA_comm :> isCommutativeBinaryOperation andBA
    ; orBA_comm :> isCommutativeBinaryOperation orBA
    ; andBA_distr_orBA :> andBA `distributesOver` orBA
    ; orBA_distr_andBA :> orBA `distributesOver` andBA
    ; andBA_orBA_absorption :> linkedByAbsorptionLaw andBA orBA
    ; trueBA_id_andBA :> trueBA `isIdentityOf` andBA
    ; falseBA_id_orBA :> falseBA `isIdentityOf` orBA
    ; trueBA_fix_orBA (x : BA) : orBA x trueBA == trueBA
    ; falseBA_fix_andBA (x : BA) : andBA x falseBA == falseBA
    ; andBA_notBA_falseBA (x : BA) : andBA x (notBA x) == falseBA
    ; orBA_notBA_trueBA (x : BA) : orBA x (notBA x) == trueBA
    }
  .

  Section TheoryOfBooleanAlgebra.

  Context {BA : Hask.t} {requiresSetoid : isSetoid BA} {requiresBooleanAlgebra : isBooleanAlgebra BA}.

  End TheoryOfBooleanAlgebra.

  Class isCBA (BA : Hask.t) {requiresSetoid : isSetoid BA} : Type :=
    { CBA_requiresBooleanAlgebra :> isBooleanAlgebra BA
    ; CBA_isCountable :> isCountable BA
    }
  .

  Section TheoryOfCountableBooleanAlgebra.

  Context {BA : Hask.t} {requiresSetoid : isSetoid BA} {requiresCBA : isCBA BA}.

  End TheoryOfCountableBooleanAlgebra.

End CountableBooleanAlgebra.
