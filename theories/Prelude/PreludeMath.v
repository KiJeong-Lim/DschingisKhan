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

End UndergraduateAlgebra.
