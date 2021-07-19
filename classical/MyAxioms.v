Require Export Coq.Logic.Classical.

Module AxiomOfChoice.

  Axiom AC : forall A : Type, forall B : Type, forall phi : A -> B -> Prop, (forall x : A, forall y : B, phi x y) -> (exists f : A -> B, forall x : A, phi x (f x)).

End AxiomOfChoice.
