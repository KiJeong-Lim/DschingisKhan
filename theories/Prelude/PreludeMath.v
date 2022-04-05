Require Import DschingisKhan.Prelude.PreludeInit.

Module MathPrelude.

  Polymorphic Class isCountable (X : Hask.t) : Type :=
    { enum (n : nat) : X
    ; enumeratable (x : X) : exists n : nat, enum n = x
    }
  .

End MathPrelude.

Export MathPrelude.

Module UndergraduateAlgebra.

  Section BasicTheoryOfRng.

  Variable R : Hask.t.

  Context {requiresSetoid : isSetoid R} {requiresRng : isRng R (requiresSetoid := requiresSetoid)}.

(**
  Lemma neg_a_mul_neg_b_is_a_mul_b (a : R) (b : R)
    : mul (neg a) (neg b) == mul a b.
  *)

(**
  Lemma mul_comm_if_idem
    (mul_idempotent : forall x : R, mul x x == x)
    : isCommutativeBinaryOperation mul.
  *)

  End BasicTheoryOfRng.

End UndergraduateAlgebra.
