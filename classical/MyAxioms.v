Require Export Coq.Logic.Classical.
Require Import DschingisKhan.pure.MyUtilities.

Module AxiomOfChoice.

  Section AC_Statement.

  Context {A : Type} {B : Type} (phi : A -> B -> Prop).

  Axiom AC : (forall x : A, forall y : B, phi x y) -> (exists f : A -> B, forall x : A, phi x (f x)).

  End AC_Statement.

End AxiomOfChoice.

Module AxiomK.

  Export Eq_rect_eq EqElim.

  Proposition RuleK {A : Type} :
    forall x : A,
    forall phi : x = x -> Type,
    phi eq_refl ->
    forall eq_id : x = x,
    phi eq_id.
  Proof with eauto with *.
    intros x phi phi_refl eq_id.
    replace eq_id with (@eq_refl A x)...
    rewrite (eq_rect_eq A x (eq x) (@eq_refl A x) eq_id).
    destruct eq_id...
  Qed.

  Definition run_identity {A : Type} {B : A -> Type} : forall x : A, forall y : B x, forall H : x = x, eq_rect x B y x H = y :=
    fun x : A =>
    fun y : B x =>
    fun H : x = x =>
    let H0 : y = eq_rect x B y x H := eq_rect_eq A x B y H in
    eq_ind y (fun y0 : B x => y0 = y) eq_refl (eq_rect x B y x H) H0
  .

  Definition existT_inj2_eq {A : Type} {B : A -> Type} : forall x : A, forall y1 : B x, forall y2 : B x, existT B x y1 = existT B x y2 -> y1 = y2 :=
    let phi' : forall p1 : sigT B, forall p2 : sigT B, p1 = p2 -> Type := fun p1 : sigT B => fun p2 : sigT B => fun H : p1 = p2 => forall H0 : projT1 p1 = projT1 p2, eq_rect (projT1 p1) B (projT2 p1) (projT1 p2) H0 = projT2 p2 in
    let phi : forall p1 : sigT B, forall p2 : sigT B, forall H : p1 = p2, phi' p2 p2 eq_refl -> phi' p1 p2 H := RuleJ phi' in
    fun x : A =>
    fun y1 : B x =>
    fun y2 : B x =>
    fun H : existT B x y1 = existT B x y2 =>
    phi (existT B x y1) (existT B x y2) H (run_identity x y2) eq_refl
  .

End AxiomK.
