Require Import DschingisKhan.pure.FunFacts.

Module ExclusiveMiddle.

  Import FunFacts.

  Axiom classic : forall A : Prop, A \/ ~ A.

  Definition proof_irrelevance : forall P : Prop, forall p1 : P, forall p2 : P, p1 = p2 :=
    exclusive_middle_implies_proof_irrelevance classic
  .

  Polymorphic Definition eq_rect_eq : forall A : Type, forall x : A, forall B : A -> Type, forall y : B x, forall H : x = x, y = eq_rect x B y x H :=
    proof_irrelevance_implies_eq_rect_eq proof_irrelevance
  .

  Polymorphic Definition Streicher_K : forall A : Type, forall x : A, forall phi : x = x -> Type, phi (@eq_refl A x) -> forall eq_val0 : x = x, phi eq_val0 :=
    fun A : Type =>
    fun x : A =>
    eq_rect_eq_implies_Streicher_K A x (eq_rect_eq A x)
  .

  Polymorphic Definition existT_inj2_eq : forall A : Type, forall B : A -> Type, forall x : A, forall y1 : B x, forall y2 : B x, existT B x y1 = existT B x y2 -> y1 = y2 :=
    fun A : Type =>
    fun B : A -> Type =>
    fun x : A =>
    eq_rect_eq_implies_existT_inj2_eq A x B (eq_rect_eq A x B)
  .

  Global Ltac ctauto :=
    match goal with
    | |- ?P => destruct (classic P); tauto
    end
  .

  Section Classical_Prop.

  Variable P : Prop.

  Lemma NNPP :
    (~ (~ P)) ->
    P.
  Proof.
    ctauto.
  Qed.

  Variable Q : Prop.

  Lemma Peirce :
    ((P -> Q) -> P) ->
    P.
  Proof.
    ctauto.
  Qed.

  Lemma not_imply_elim :
    (~ (P -> Q)) ->
    P.
  Proof.
    ctauto.
  Qed.

  Lemma imply_to_or :
    (P -> Q) ->
    ((~ P) \/ Q).
  Proof.
    ctauto.
  Qed.

  Lemma imply_to_and :
    (~ (P -> Q)) ->
    (P /\ (~ Q)).
  Proof.
    ctauto.
  Qed.

  Lemma not_and_or :
    (~ (P /\ Q)) ->
    ((~ P) \/ (~ Q)).
  Proof.
    ctauto.
  Qed.

  Lemma law1_of_DeMorgan :
    ~ (~ P /\ ~ Q) ->
    P \/ Q.
  Proof.
    ctauto.
  Qed.

  End Classical_Prop.

  Global Ltac cfirstorder :=
    now apply NNPP; firstorder
  .

  Section Classical_Pred_Type.

  Context (U : Type) (P : U -> Prop).

  Let not_forall_isInconsistentWith_not_exists_not : (~ (forall n : U, P n)) -> (~ (exists n : U, (~ P n))) -> False :=
    fun H : ~ (forall n : U, P n) =>
    fun H0 : ~ (exists n : U, ~ (P n)) =>
    H (fun n : U => NNPP (P n) (fun H1 : ~ P n => H0 (ex_intro (fun n0 : U => ~ P n0) n H1)))
  . 

  Lemma not_all_not_ex :
    (~ (forall n : U, ~ P n)) ->
    (exists n : U, P n).
  Proof.
    now destruct (classic (exists n : U, P n)); firstorder.
  Qed.

  Lemma not_all_ex_not :
    (~ (forall n : U, P n)) ->
    (exists n : U, (~ P n)).
  Proof.
    now destruct (classic (exists n : U, ~ P n)); firstorder.
  Qed.

  Lemma not_ex_not_all :
    (~ (exists n : U, (~ P n))) ->
    (forall n : U, P n).
  Proof.
    now destruct (classic (forall n : U, P n)); firstorder.
  Qed.

  End Classical_Pred_Type.

End ExclusiveMiddle.
