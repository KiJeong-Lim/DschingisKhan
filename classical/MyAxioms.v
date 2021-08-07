Require Import DschingisKhan.pure.MyUtilities.

Module Type ClassicalEqFacts_requirements.

  Parameter eq_rect_eq : forall U : Type, forall p : U, forall Q : U -> Type, forall x : Q p, forall h : p = p, x = eq_rect p Q x p h.

End ClassicalEqFacts_requirements.

Module Type ExclusiveMiddleFacts_requirements.

  Parameter LEM : forall A : Prop, A \/ ~ A.

End ExclusiveMiddleFacts_requirements.

Module ClassicalEqFacts_prototype (my_requirements : ClassicalEqFacts_requirements).

  Import EqFacts.

  Section ClassicalEqTheory.

  Let _eq_rect_eq {A : Type} : forall x : A, forall B : A -> Type, forall y : B x, forall H : x = x, y = eq_rect x B y x H :=
    my_requirements.eq_rect_eq A
  .

  Section DeriveAxiomK.

  Context {A : Type}.

  Definition RuleK :
    forall x : A,
    forall phi : x = x -> Type,
    phi eq_refl ->
    forall eq_val0 : x = x,
    phi eq_val0.
  Proof.
    intros x.
    set (eq_val := @eq_refl A x). 
    intros phi phi_val0 eq_val0.
    replace eq_val0 with eq_val.
    - apply phi_val0.
    - rewrite (_eq_rect_eq x (eq x) eq_val eq_val0).
      destruct eq_val0.
      reflexivity.
  Defined.

  End DeriveAxiomK.

  Section ExistTSndEq.

  Context {A : Type} {B : A -> Type}.

  Let phi' : forall p1 : sigT B, forall p2 : sigT B, p1 = p2 -> Type :=
    fun p1 : sigT B =>
    fun p2 : sigT B =>
    fun H : p1 = p2 =>
    forall H0 : projT1 p1 = projT1 p2,
    eq_rect (projT1 p1) B (projT2 p1) (projT1 p2) H0 = projT2 p2
  .

  Let phi : forall p1 : sigT B, forall p2 : sigT B, forall H : p1 = p2, phi' p2 p2 eq_refl -> phi' p1 p2 H :=
    RuleJ phi'
  .

  Definition existT_snd_eq : forall x : A, forall y1 : B x, forall y2 : B x, existT B x y1 = existT B x y2 -> y1 = y2 :=
    fun x : A =>
    fun y1 : B x =>
    fun y2 : B x =>
    fun H : existT B x y1 = existT B x y2 =>
    phi (existT B x y1) (existT B x y2) H (fun H0 : x = x => eq_symmetry y2 (eq_rect x B y2 x H0) (_eq_rect_eq x B y2 H0)) eq_refl
  .

  End ExistTSndEq.

  End ClassicalEqTheory.

End ClassicalEqFacts_prototype.

Module ExclusiveMiddleFacts_prototype (my_requirements : ExclusiveMiddleFacts_requirements).

  Section Berardi's_Paradox. (* Reference: "https://coq.inria.fr/library/Coq.Logic.Berardi.html" *)

  Let EM : forall P : Prop, P \/ ~ P :=
    my_requirements.LEM
  .

  Section Retracts.

  Section IF_PROP.

  Context {P : Prop} (B : Prop).

  Definition IfProp : P -> P -> P :=
    fun p1 : P =>
    fun p2 : P =>
    match EM B with
    | or_introl H => p1
    | or_intror H => p2
    end
  .

  Lemma AC_IF :
    forall p1 : P,
    forall p2 : P,
    forall Q : P -> Prop,
    (B -> Q p1) ->
    (~ B -> Q p2) ->
    Q (IfProp p1 p2).
  Proof with eauto.
    unfold IfProp.
    destruct (EM B)...
  Qed.

  End IF_PROP.

  Record retract (A : Prop) (B : Prop) : Prop :=
    { _i : A -> B
    ; _j : B -> A
    ; _inv : forall a : A, _j (_i a) = a
    }
  .

  Local Hint Constructors retract : core.

  Record retract_cond (A : Prop) (B : Prop) : Prop :=
    { _i2 : A -> B
    ; _j2 : B -> A
    ; _inv2 : retract A B -> forall a : A, _j2 (_i2 a) = a
    }
  .

  Local Hint Constructors retract_cond : core.

  Lemma AC {A : Prop} {B : Prop} :
    forall r : retract_cond A B,
    retract A B ->
    forall a : A,
    _j2 A B r (_i2 A B r a) = a.
  Proof with eauto.
    intros [i2 j2 inv2] [i j inv] a...
  Qed.

  Context {Bool : Prop} (T : Bool) (F : Bool).

  Let pow : Prop -> Prop :=
    fun P : Prop =>
    P -> Bool
  .

  Lemma L1 :
    forall A : Prop,
    forall B : Prop,
    retract_cond (pow A) (pow B).
  Proof with (tauto || eauto).
    intros A B.
    destruct (my_requirements.LEM (retract (pow A) (pow B))) as [[i j inv] | H].
    - exists i j...
    - exists (fun pa : pow A => fun b : B => F) (fun pb : pow B => fun a : A => F)...
  Qed.

  Let U : Prop :=
    forall P : Prop,
    pow P
  .

  Let f : U -> pow U :=
    fun u : U =>
    u U
  .

  Let g : pow U -> U :=
    fun h : pow U =>
    fun X : Prop =>
    let lX := _j2 (pow X) (pow U) (L1 X U) in
    let rU := _i2 (pow U) (pow U) (L1 U U) in
    lX (rU h)
  .

  Lemma retract_pow_U_U :
    retract (pow U) U.
  Proof with eauto.
    exists g f.
    intros a.
    apply AC.
    exists (fun x : pow U => x) (fun x : pow U => x)...
  Qed.

  Let Not_b : Bool -> Bool :=
    fun b : Bool =>
    IfProp (b = T) F T
  .

  Let R : U :=
    g (fun u : U => Not_b (u U u))
  .

  Let RR : Bool :=
    R U R
  .

  Lemma Not_b_has_fixpoint :
    RR = Not_b RR.
  Proof.
    assert (X : retract (pow U) (pow U)) by now exists (fun x : pow U => x) (fun x : pow U => x).
    apply (eq_ind (fun u : U => Not_b (u U u)) (fun Phi : pow U => Phi R = Not_b (R U R)) eq_refl).
    symmetry.
    exact (AC (L1 U U) X (fun u : U => Not_b (u U u))).
  Qed.

  Theorem classical_proof_irrelevance :
    T = F.
  Proof with (tauto || eauto).
    assert (claim1 := fun is_true : R U R = T => fun is_false : R U R = F => eq_ind (R U R) (fun T0 : Bool => T0 = F) (eq_ind (R U R) (fun F0 : Bool => R U R = F0) eq_refl F is_false) T is_true).
    assert (claim2 := fun not_true : R U R <> T => fun is_true : R U R = T => False_ind (T = F) (not_true is_true)).
    assert (claim3 : R U R = Not_b (R U R)) by apply Not_b_has_fixpoint.
    destruct (EM (R U R = T)) as [claim4 | claim4]; simpl in *.
    - rewrite claim4 in claim3.
      unfold Not_b, IfProp in claim3.
      destruct (EM (T = T))...
    - apply claim2...
      rewrite claim3.
      unfold Not_b, IfProp.
      destruct (EM (R U R = T))...
  Qed.

  End Retracts.

  Corollary ProofIrrelevance {P : Prop} :
    forall p1 : P,
    forall p2 : P,
    p1 = p2.
  Proof.
    exact (@classical_proof_irrelevance P).
  Qed.

  End Berardi's_Paradox.

  Lemma eq_rect_eq (A : Type) :
    forall x : A,
    forall B : A -> Type,
    forall y : B x,
    forall H : x = x,
    y = eq_rect x B y x H.
  Proof.
    intros x B y H.
    rewrite <- (@ProofIrrelevance (@eq A x x) (@eq_refl A x) H).
    reflexivity.
  Qed.

  Section Classical_Prop.

  Let classic : forall P : Prop, P \/ ~ P :=
    my_requirements.LEM
  .

  Context {P : Prop}.

  Lemma NNPP :
    ~ ~ P ->
    P.
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Context {Q : Prop}.

  Lemma Peirce :
    ((P -> Q) -> P) ->
    P.
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Lemma not_imply_elim :
    ~ (P -> Q) ->
    P.
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Lemma not_imply_elim2 :
    ~ (P -> Q) ->
    ~ Q.
  Proof with tauto.
    destruct (classic Q)...
  Qed.

  Lemma imply_to_or :
    (P -> Q) ->
    ~ P \/ Q.
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Lemma imply_to_and :
    ~ (P -> Q) ->
    P /\ ~ Q.
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Lemma or_to_imply :
    ~ P \/ Q ->
    P ->
    Q.
  Proof with tauto.
    destruct (classic Q)...
  Qed.

  Lemma not_and_or :
    ~ (P /\ Q) ->
    ~ P \/ ~ Q.
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Lemma or_not_and :
    ~ P \/ ~ Q ->
    ~ (P /\ Q).
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Lemma not_or_and :
    ~ (P \/ Q) ->
    ~ P /\ ~ Q.
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Lemma and_not_or :
    ~ P /\ ~ Q ->
    ~ (P \/ Q).
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Lemma imply_and_or :
    (P -> Q) ->
    P \/ Q ->
    Q.
  Proof with tauto.
    destruct (classic Q)...
  Qed.

  Context {R : Prop}.

  Lemma imply_and_or2 :
    (P -> Q) ->
    P \/ R ->
    Q \/ R.
  Proof with tauto.
    destruct (classic P)...
  Qed.

  End Classical_Prop.

  Section Classical_Pred_Type.

  Let classic : forall P : Prop, P \/ ~ P :=
    my_requirements.LEM
  .

  Context {U : Type} {P : U -> Prop}.

  Let forall_exists_False : ~ (forall n : U, P n) -> ~ (exists n : U, ~ P n) -> False :=
    fun H : ~ (forall n : U, P n) =>
    fun H0 : ~ (exists n : U, ~ P n) =>
    H (fun n : U => @NNPP (P n) (fun H1 : ~ P n => H0 (@ex_intro U (fun n' : U => ~ P n') n H1)))
  .

  Lemma not_all_not_ex :
    ~ (forall n : U, ~ P n) ->
    exists n : U, P n.
  Proof with firstorder.
    destruct (classic (exists n : U, P n))...
  Qed.

  Lemma not_all_ex_not :
    ~ (forall n : U, P n) ->
    exists n : U, ~ P n.
  Proof with firstorder.
    destruct (classic (exists n : U, ~ P n))...
  Qed.

  Lemma not_ex_all_not :
    ~ (exists n : U, P n) ->
    forall n : U,
    ~ P n.
  Proof with firstorder.
    destruct (classic (forall n : U, ~ P n))...
  Qed.

  Lemma not_ex_not_all :
    ~ (exists n : U, ~ P n) ->
    forall n : U,
    P n.
  Proof with firstorder.
    destruct (classic (forall n : U, P n))...
  Qed.

  Lemma ex_not_not_all :
    (exists n : U, ~ P n) ->
    ~ (forall n : U, P n).
  Proof with firstorder.
    destruct (classic (exists n : U, ~ P n))...
  Qed.

  Lemma all_not_not_ex :
    (forall n : U, ~ P n) ->
    ~ (exists n : U, P n).
  Proof with firstorder.
    destruct (classic (forall n : U, ~ P n))...
  Qed.

  End Classical_Pred_Type.

End ExclusiveMiddleFacts_prototype.

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
