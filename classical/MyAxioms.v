Require Export Coq.Logic.Classical.
Require Import DschingisKhan.pure.MyUtilities.

Module AxiomK.

  Export Eq_rect_eq EqFacts.

  Proposition RuleK {A : Type} :
    forall x : A,
    forall phi : x = x -> Type,
    phi eq_refl ->
    forall eq_val0 : x = x,
    phi eq_val0.
  Proof with try tauto.
    intros x.
    set (eq_val := @eq_refl A x). 
    intros phi phi_val0 eq_val0.
    replace eq_val0 with eq_val...
    rewrite (eq_rect_eq A x (eq x) eq_val eq_val0).
    destruct eq_val0...
  Qed.

  Definition existT_snd_eq {A : Type} {B : A -> Type} : forall x : A, forall y1 : B x, forall y2 : B x, existT B x y1 = existT B x y2 -> y1 = y2 :=
    let phi' : forall p1 : sigT B, forall p2 : sigT B, p1 = p2 -> Type := fun p1 : sigT B => fun p2 : sigT B => fun H : p1 = p2 => forall H0 : projT1 p1 = projT1 p2, eq_rect (projT1 p1) B (projT2 p1) (projT1 p2) H0 = projT2 p2 in
    let phi : forall p1 : sigT B, forall p2 : sigT B, forall H : p1 = p2, phi' p2 p2 eq_refl -> phi' p1 p2 H := RuleJ phi' in
    fun x : A =>
    fun y1 : B x =>
    fun y2 : B x =>
    fun H : existT B x y1 = existT B x y2 =>
    phi (existT B x y1) (existT B x y2) H (fun H0 : x = x => eq_symmetry y2 (eq_rect x B y2 x H0) (eq_rect_eq A x B y2 H0)) eq_refl
  .

End AxiomK.

Module AxiomOfChoice.

  Section StatementOfAC.

  Context {A : Type} {B : Type} (psi : A -> B -> Prop).

  Axiom AC : (forall x : A, forall y : B, psi x y) -> (exists f : A -> B, forall x : A, psi x (f x)).

  End StatementOfAC.

End AxiomOfChoice.
