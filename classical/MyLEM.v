Require Import DschingisKhan.pure.MyUtilities.

Module Type ClassicalLogicAxioms.

  Parameter LEM : forall A : Prop, A \/ ~ A.

End ClassicalLogicAxioms.

Module ClassicalLogicFactsTemplate (ClassicalLogic_axioms : ClassicalLogicAxioms).

  Definition ProofIrrelevance {P : Prop} : forall p1 : P, forall p2 : P, p1 = p2 :=
    MyUtilities.__ProofIrrelevance ClassicalLogic_axioms.LEM P
  .

  Definition eq_rect_eq {A : Type} : forall x : A, forall B : A -> Type, forall y : B x, forall H : x = x, y = eq_rect x B y x H :=
    MyUtilities.__eq_rect_eq ClassicalLogic_axioms.LEM A
  .

  Definition RuleK {A : Type} : forall x : A, forall phi : x = x -> Type, phi eq_refl -> forall eq_val0 : x = x, phi eq_val0 :=
    MyUtilities.__RuleK (@eq_rect_eq) A
  .

  Definition existT_snd_eq {A : Type} {B : A -> Type} : forall x : A, forall y1 : B x, forall y2 : B x, existT B x y1 = existT B x y2 -> y1 = y2 :=
    MyUtilities.__existT_snd_eq (@eq_rect_eq) A B
  .

  Definition NNPP {P : Prop} : ~ ~ P -> P :=
    MyUtilities.__NNPP ClassicalLogic_axioms.LEM P
  .

  Definition Peirce {P : Prop} {Q : Prop} : ((P -> Q) -> P) -> P :=
    MyUtilities.__Peirce ClassicalLogic_axioms.LEM P Q
  .

  Definition not_imply_elim {P : Prop} {Q : Prop} : ~ (P -> Q) -> P :=
    MyUtilities.__not_imply_elim ClassicalLogic_axioms.LEM P Q
  .

  Definition not_imply_elim2 {P : Prop} {Q : Prop} : ~ (P -> Q) -> ~ Q :=
    MyUtilities.__not_imply_elim2 ClassicalLogic_axioms.LEM P Q
  .

  Definition imply_to_or {P : Prop} {Q : Prop} : (P -> Q) -> ~ P \/ Q :=
    MyUtilities.__imply_to_or ClassicalLogic_axioms.LEM P Q
  .

  Definition imply_to_and {P : Prop} {Q : Prop} : ~ (P -> Q) -> P /\ ~ Q :=
    MyUtilities.__imply_to_and ClassicalLogic_axioms.LEM P Q
  .

  Definition or_to_imply {P : Prop} {Q : Prop} : ~ P \/ Q -> P -> Q :=
    MyUtilities.__or_to_imply ClassicalLogic_axioms.LEM P Q
  .

  Definition not_and_or {P : Prop} {Q : Prop} : ~ (P /\ Q) -> ~ P \/ ~ Q :=
    MyUtilities.__not_and_or ClassicalLogic_axioms.LEM P Q
  .

  Definition or_not_and {P : Prop} {Q : Prop} : ~ P \/ ~ Q -> ~ (P /\ Q) :=
    MyUtilities.__or_not_and ClassicalLogic_axioms.LEM P Q
  .

  Definition not_or_and {P : Prop} {Q : Prop} : ~ (P \/ Q) -> ~ P /\ ~ Q :=
    MyUtilities.__not_or_and ClassicalLogic_axioms.LEM P Q
  .

  Definition and_not_or {P : Prop} {Q : Prop} : ~ P /\ ~ Q -> ~ (P \/ Q) :=
    MyUtilities.__and_not_or ClassicalLogic_axioms.LEM P Q
  .

  Definition imply_and_or {P : Prop} {Q : Prop} : (P -> Q) -> P \/ Q -> Q :=
    MyUtilities.__imply_and_or ClassicalLogic_axioms.LEM P Q
  .

  Definition imply_and_or2 {P : Prop} {Q : Prop} {R : Prop} : (P -> Q) -> P \/ R -> Q \/ R :=
    MyUtilities.__imply_and_or2 ClassicalLogic_axioms.LEM P Q R
  .

  Definition not_all_not_ex {U : Type} {P : U -> Prop} : ~ (forall n : U, ~ P n) -> exists n : U, P n :=
    MyUtilities.__not_all_not_ex ClassicalLogic_axioms.LEM U P
  .

  Definition not_all_ex_not {U : Type} {P : U -> Prop} : ~ (forall n : U, P n) -> exists n : U, ~ P n :=
    MyUtilities.__not_all_ex_not ClassicalLogic_axioms.LEM U P
  .

  Definition not_ex_all_not {U : Type} {P : U -> Prop} : ~ (exists n : U, P n) -> forall n : U, ~ P n :=
    MyUtilities.__not_ex_all_not ClassicalLogic_axioms.LEM U P
  .

  Definition not_ex_not_all {U : Type} {P : U -> Prop} : ~ (exists n : U, ~ P n) -> forall n : U, P n :=
    MyUtilities.__not_ex_not_all ClassicalLogic_axioms.LEM U P
  .

  Definition ex_not_not_all {U : Type} {P : U -> Prop} : (exists n : U, ~ P n) -> ~ (forall n : U, P n) :=
    MyUtilities.__ex_not_not_all ClassicalLogic_axioms.LEM U P
  .

  Definition all_not_not_ex {U : Type} {P : U -> Prop} : (forall n : U, ~ P n) -> ~ (exists n : U, P n) :=
    MyUtilities.__all_not_not_ex ClassicalLogic_axioms.LEM U P
  .

End ClassicalLogicFactsTemplate.

Module ClassicalLogic.

  Axiom classic : forall A : Prop, A \/ ~ A.

  Module ClassicalLogic_axioms : ClassicalLogicAxioms.

    Definition LEM : forall A : Prop, A \/ ~ A :=
      classic
    .

  End ClassicalLogic_axioms.

  Module ClassicalLogicFacts := ClassicalLogicFactsTemplate(ClassicalLogic_axioms).

  Export ClassicalLogicFacts.

End ClassicalLogic.
