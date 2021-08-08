Require Import DschingisKhan.pure.MyUtilities.

Module ClassicalLogic.

  Axiom classic : forall A : Prop, A \/ ~ A.

  Section InternalFactBindings.

  Let __internal_axiom1__ : forall A : Prop, A \/ ~ A :=
    classic
  .

  Definition proof_irrelevance : forall P : Prop, forall p1 : P, forall p2 : P, p1 = p2 :=
    FUN_FACT.proof_irrelevance __internal_axiom1__
  .

  Definition eq_rect_eq : forall A : Type, forall x : A, forall B : A -> Type, forall y : B x, forall H : x = x, y = eq_rect x B y x H :=
    FUN_FACT.eq_rect_eq __internal_axiom1__
  .

  Let __internal_axiom2__ : forall A : Type, forall x : A, forall B : A -> Type, forall y : B x, forall H : x = x, y = eq_rect x B y x H :=
    eq_rect_eq
  .

  Definition Streicher_K : forall A : Type, forall x : A, forall phi : x = x -> Type, phi (@eq_refl A x) -> forall eq_val0 : x = x, phi eq_val0 :=
    FUN_FACT.Streicher_K __internal_axiom2__
  .

  Definition existT_inj2_eq : forall A : Type, forall B : A -> Type, forall x : A, forall y1 : B x, forall y2 : B x, existT B x y1 = existT B x y2 -> y1 = y2 :=
    FUN_FACT.existT_inj2_eq __internal_axiom2__
  .

  Definition NNPP : forall P : Prop, ~ ~ P -> P :=
    FUN_FACT.NNPP __internal_axiom1__
  .

  Definition Peirce : forall P : Prop, forall Q : Prop, ((P -> Q) -> P) -> P :=
    FUN_FACT.Peirce __internal_axiom1__
  .

  Definition not_imply_elim : forall P : Prop, forall Q : Prop, ~ (P -> Q) -> P :=
    FUN_FACT.not_imply_elim __internal_axiom1__
  .

  Definition not_imply_elim2 : forall P : Prop, forall Q : Prop, ~ (P -> Q) -> ~ Q :=
    FUN_FACT.not_imply_elim2 __internal_axiom1__
  .

  Definition imply_to_or : forall P : Prop, forall Q : Prop, (P -> Q) -> ~ P \/ Q :=
    FUN_FACT.imply_to_or __internal_axiom1__
  .

  Definition imply_to_and : forall P : Prop, forall Q : Prop, ~ (P -> Q) -> P /\ ~ Q :=
    FUN_FACT.imply_to_and __internal_axiom1__
  .

  Definition or_to_imply : forall P : Prop, forall Q : Prop, ~ P \/ Q -> P -> Q :=
    FUN_FACT.or_to_imply __internal_axiom1__
  .

  Definition not_and_or : forall P : Prop, forall Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q :=
    FUN_FACT.not_and_or __internal_axiom1__
  .

  Definition or_not_and : forall P : Prop, forall Q : Prop, ~ P \/ ~ Q -> ~ (P /\ Q) :=
    FUN_FACT.or_not_and __internal_axiom1__
  .

  Definition not_or_and : forall P : Prop, forall Q : Prop, ~ (P \/ Q) -> ~ P /\ ~ Q :=
    FUN_FACT.not_or_and __internal_axiom1__
  .

  Definition and_not_or : forall P : Prop, forall Q : Prop, ~ P /\ ~ Q -> ~ (P \/ Q) :=
    FUN_FACT.and_not_or __internal_axiom1__
  .

  Definition imply_and_or : forall P : Prop, forall Q : Prop, (P -> Q) -> P \/ Q -> Q :=
    FUN_FACT.imply_and_or __internal_axiom1__
  .

  Definition imply_and_or2 : forall P : Prop, forall Q : Prop, forall R : Prop, (P -> Q) -> P \/ R -> Q \/ R :=
    FUN_FACT.imply_and_or2 __internal_axiom1__
  .

  Definition not_all_not_ex : forall U : Type, forall P : U -> Prop, ~ (forall n : U, ~ P n) -> exists n : U, P n :=
    FUN_FACT.not_all_not_ex __internal_axiom1__
  .

  Definition not_all_ex_not : forall U : Type, forall P : U -> Prop, ~ (forall n : U, P n) -> exists n : U, ~ P n :=
    FUN_FACT.not_all_ex_not __internal_axiom1__
  .

  Definition not_ex_all_not : forall U : Type, forall P : U -> Prop, ~ (exists n : U, P n) -> forall n : U, ~ P n :=
    FUN_FACT.not_ex_all_not __internal_axiom1__
  .

  Definition not_ex_not_all : forall U : Type, forall P : U -> Prop, ~ (exists n : U, ~ P n) -> forall n : U, P n :=
    FUN_FACT.not_ex_not_all __internal_axiom1__
  .

  Definition ex_not_not_all : forall U : Type, forall P : U -> Prop, (exists n : U, ~ P n) -> ~ (forall n : U, P n) :=
    FUN_FACT.ex_not_not_all __internal_axiom1__
  .

  Definition all_not_not_ex : forall U : Type, forall P : U -> Prop, (forall n : U, ~ P n) -> ~ (exists n : U, P n) :=
    FUN_FACT.all_not_not_ex __internal_axiom1__
  .

  End InternalFactBindings.

End ClassicalLogic.
