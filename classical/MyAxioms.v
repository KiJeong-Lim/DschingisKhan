Require Import DschingisKhan.pure.MyUtilities.

Module ExclusiveMiddleFacts.

  Axiom classic : forall A : Prop, A \/ ~ A.

  Module ExclusiveMiddleFacts_axiom : ExclusiveMiddleFacts_requirements.

    Definition LEM : forall A : Prop, A \/ ~ A :=
      classic
    .

  End ExclusiveMiddleFacts_axiom.

  Module ExclusiveMiddleFacts_internal := ExclusiveMiddleFacts_prototype(ExclusiveMiddleFacts_axiom).

  Module ClassicalEqFacts_axiom : ClassicalEqFacts_requirements.

    Definition eq_rect_eq : forall U : Type, forall p : U, forall Q : U -> Type, forall x : Q p, forall h : p = p, x = eq_rect p Q x p h :=
      ExclusiveMiddleFacts_internal.eq_rect_eq
    .

  End ClassicalEqFacts_axiom.

  Module ClassicalEqFacts_internal := ClassicalEqFacts_prototype(ClassicalEqFacts_axiom).

  Export ExclusiveMiddleFacts_internal ClassicalEqFacts_internal.

End ExclusiveMiddleFacts.
