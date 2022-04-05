Require Import DschingisKhan.Prelude.PreludeInit.

Module UndergraduateAlgebra.

  Section TheoryOfRing.

  Variable R : Hask.t.

  Context {requiresSetoid : isSetoid R} {requiresRing : isRing R (requiresSetoid := requiresSetoid)}.

(**
  Lemma neg_a_mul_neg_b_is_a_mul_b (a : R) (b : R)
    : mul (neg a) (neg b) == mul a b.
  *)

  End TheoryOfRing.

End UndergraduateAlgebra.
