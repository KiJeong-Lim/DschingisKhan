Require Import DschingisKhan.pure.MyUtilities.

Module ClassicalLogic.

  Axiom classic : forall A : Prop, A \/ ~ A.

  Section InternalFactBindings.

  Let __internal_axiom1 : forall A : Prop, A \/ ~ A :=
    classic
  .

  Definition ProofIrrelevance {P : Prop} : forall p1 : P, forall p2 : P, p1 = p2 :=
    FUN_FACT.ProofIrrelevance __internal_axiom1 P
  .

  Definition eq_rect_eq {A : Type} : forall x : A, forall B : A -> Type, forall y : B x, forall H : x = x, y = eq_rect x B y x H :=
    FUN_FACT.eq_rect_eq __internal_axiom1 A
  .

  Definition RuleK {A : Type} : forall x : A, forall phi : x = x -> Type, phi eq_refl -> forall eq_val0 : x = x, phi eq_val0 :=
    FUN_FACT.RuleK (@eq_rect_eq) A
  .

  Definition existT_snd_eq {A : Type} {B : A -> Type} : forall x : A, forall y1 : B x, forall y2 : B x, existT B x y1 = existT B x y2 -> y1 = y2 :=
    FUN_FACT.existT_snd_eq (@eq_rect_eq) A B
  .

  Definition NNPP {P : Prop} : ~ ~ P -> P :=
    FUN_FACT.NNPP __internal_axiom1 P
  .

  Definition Peirce {P : Prop} {Q : Prop} : ((P -> Q) -> P) -> P :=
    FUN_FACT.Peirce __internal_axiom1 P Q
  .

  Definition not_imply_elim {P : Prop} {Q : Prop} : ~ (P -> Q) -> P :=
    FUN_FACT.not_imply_elim __internal_axiom1 P Q
  .

  Definition not_imply_elim2 {P : Prop} {Q : Prop} : ~ (P -> Q) -> ~ Q :=
    FUN_FACT.not_imply_elim2 __internal_axiom1 P Q
  .

  Definition imply_to_or {P : Prop} {Q : Prop} : (P -> Q) -> ~ P \/ Q :=
    FUN_FACT.imply_to_or __internal_axiom1 P Q
  .

  Definition imply_to_and {P : Prop} {Q : Prop} : ~ (P -> Q) -> P /\ ~ Q :=
    FUN_FACT.imply_to_and __internal_axiom1 P Q
  .

  Definition or_to_imply {P : Prop} {Q : Prop} : ~ P \/ Q -> P -> Q :=
    FUN_FACT.or_to_imply __internal_axiom1 P Q
  .

  Definition not_and_or {P : Prop} {Q : Prop} : ~ (P /\ Q) -> ~ P \/ ~ Q :=
    FUN_FACT.not_and_or __internal_axiom1 P Q
  .

  Definition or_not_and {P : Prop} {Q : Prop} : ~ P \/ ~ Q -> ~ (P /\ Q) :=
    FUN_FACT.or_not_and __internal_axiom1 P Q
  .

  Definition not_or_and {P : Prop} {Q : Prop} : ~ (P \/ Q) -> ~ P /\ ~ Q :=
    FUN_FACT.not_or_and __internal_axiom1 P Q
  .

  Definition and_not_or {P : Prop} {Q : Prop} : ~ P /\ ~ Q -> ~ (P \/ Q) :=
    FUN_FACT.and_not_or __internal_axiom1 P Q
  .

  Definition imply_and_or {P : Prop} {Q : Prop} : (P -> Q) -> P \/ Q -> Q :=
    FUN_FACT.imply_and_or __internal_axiom1 P Q
  .

  Definition imply_and_or2 {P : Prop} {Q : Prop} {R : Prop} : (P -> Q) -> P \/ R -> Q \/ R :=
    FUN_FACT.imply_and_or2 __internal_axiom1 P Q R
  .

  Definition not_all_not_ex {U : Type} {P : U -> Prop} : ~ (forall n : U, ~ P n) -> exists n : U, P n :=
    FUN_FACT.not_all_not_ex __internal_axiom1 U P
  .

  Definition not_all_ex_not {U : Type} {P : U -> Prop} : ~ (forall n : U, P n) -> exists n : U, ~ P n :=
    FUN_FACT.not_all_ex_not __internal_axiom1 U P
  .

  Definition not_ex_all_not {U : Type} {P : U -> Prop} : ~ (exists n : U, P n) -> forall n : U, ~ P n :=
    FUN_FACT.not_ex_all_not __internal_axiom1 U P
  .

  Definition not_ex_not_all {U : Type} {P : U -> Prop} : ~ (exists n : U, ~ P n) -> forall n : U, P n :=
    FUN_FACT.not_ex_not_all __internal_axiom1 U P
  .

  Definition ex_not_not_all {U : Type} {P : U -> Prop} : (exists n : U, ~ P n) -> ~ (forall n : U, P n) :=
    FUN_FACT.ex_not_not_all __internal_axiom1 U P
  .

  Definition all_not_not_ex {U : Type} {P : U -> Prop} : (forall n : U, ~ P n) -> ~ (exists n : U, P n) :=
    FUN_FACT.all_not_not_ex __internal_axiom1 U P
  .

  End InternalFactBindings.

End ClassicalLogic.
