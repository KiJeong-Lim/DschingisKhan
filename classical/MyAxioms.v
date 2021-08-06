Require Import DschingisKhan.pure.MyUtilities.

Module Type ClassicalEqFacts_requirements.

  Parameter eq_rect_eq : forall (U : Type) (p : U) (Q : U -> Type) (x: Q p) (h : p = p), x = eq_rect p Q x p h.

End ClassicalEqFacts_requirements.

Module Type ExclusiveMiddleFacts_requirements.

  Parameter LEM : forall A : Prop, A \/ ~ A.

End ExclusiveMiddleFacts_requirements.

Module ClassicalEqFacts_prototype (my_requirements : ClassicalEqFacts_requirements).

  Import EqFacts.

  Definition RuleK {A : Type} :
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
    - rewrite (my_requirements.eq_rect_eq A x (eq x) eq_val eq_val0).
      destruct eq_val0.
      reflexivity.
  Defined.

  Definition existT_snd_eq {A : Type} {B : A -> Type} : forall x : A, forall y1 : B x, forall y2 : B x, existT B x y1 = existT B x y2 -> y1 = y2 :=
    let phi' : forall p1 : sigT B, forall p2 : sigT B, p1 = p2 -> Type := fun p1 : sigT B => fun p2 : sigT B => fun H : p1 = p2 => forall H0 : projT1 p1 = projT1 p2, eq_rect (projT1 p1) B (projT2 p1) (projT1 p2) H0 = projT2 p2 in
    let phi : forall p1 : sigT B, forall p2 : sigT B, forall H : p1 = p2, phi' p2 p2 eq_refl -> phi' p1 p2 H := RuleJ phi' in
    fun x : A =>
    fun y1 : B x =>
    fun y2 : B x =>
    fun H : existT B x y1 = existT B x y2 =>
    phi (existT B x y1) (existT B x y2) H (fun H0 : x = x => eq_symmetry y2 (eq_rect x B y2 x H0) (my_requirements.eq_rect_eq A x B y2 H0)) eq_refl
  .

End ClassicalEqFacts_prototype.

Module ExclusiveMiddleFacts_prototype (my_requirements : ExclusiveMiddleFacts_requirements). (* Reference: "https://coq.inria.fr/library/Coq.Logic.Berardi.html" *)

  Import EqFacts.

  Section Berardis_paradox.

  Let EM : forall P : Prop, P \/ ~ P :=
    my_requirements.LEM
  .

  Section IFPROP.

  Context {P : Prop} (B : Prop).

  Definition IFProp : P -> P -> P :=
    fun p1 : P =>
    fun p2 : P =>
    match EM B with
    | or_introl _ => p1
    | or_intror _ => p2
    end
  .

  Lemma AC_IF :
    forall p1 : P,
    forall p2 : P,
    forall Q : P -> Prop,
    (B -> Q p1) ->
    (~ B -> Q p2) ->
    Q (IFProp p1 p2).
  Proof with eauto.
    unfold IFProp.
    destruct (EM B)...
  Qed.

  End IFPROP.

  Section Retracts.

  Record retract (A : Prop) (B : Prop) : Prop :=
    { i : A -> B
    ; j : B -> A
    ; inv : forall a : A, j (i a) = a
    }
  .

  Local Hint Constructors retract : core.

  Record retract_cond (A : Prop) (B : Prop) : Prop :=
    { i2 : A -> B
    ; j2 : B -> A
    ; inv2 : retract A B -> forall a : A, j2 (i2 a) = a
    }
  .

  Local Hint Constructors retract_cond : core.

  Lemma AC {A : Prop} {B : Prop} :
    forall r : retract_cond A B,
    retract A B ->
    forall a : A,
    j2 A B r (i2 A B r a) = a.
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
  Proof with eauto.
    intros A B.
    destruct (my_requirements.LEM (retract (pow A) (pow B))) as [[i j inv] | H].
    - exists i j...
    - exists (fun pa : pow A => fun b : B => F) (fun pb : pow B => fun a : A => F).
      contradiction.
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
    let lX := j2 (pow X) (pow U) (L1 X U) in
    let rU := i2 (pow U) (pow U) (L1 U U) in
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
    IFProp (b = T) F T
  .

  Let R : U :=
    g (fun u : U => Not_b (u U u))
  .

  Let RR : Bool :=
    R U R
  .

  Lemma not_has_fixpoint :
    RR = Not_b RR.
  Proof with eauto.
    assert (X : retract (pow U) (pow U)) by now exists (fun x : pow U => x) (fun x : pow U => x).
    apply (eq_ind (fun u : U => Not_b (u U u)) (fun Phi : pow U => Phi R = Not_b (R U R)) eq_refl).
    symmetry.
    apply (AC (L1 U U) X (fun u : U => Not_b (u U u))).
  Qed.

  Corollary classical_proof_irrelevance :
    T = F.
  Proof with (tauto || eauto).
    assert (claim1 := fun is_true : R U R = T => fun is_false : R U R = F => eq_ind (R U R) (fun T0 : Bool => T0 = F) (eq_ind (R U R) (fun F0 : Bool => R U R = F0) eq_refl F is_false) T is_true).
    assert (claim2 := fun not_true : R U R <> T => fun is_true : R U R = T => False_ind (T = F) (not_true is_true)).
    assert (claim3 : R U R = Not_b (R U R)) by apply not_has_fixpoint.
    destruct (EM (R U R = T)) as [claim4 | claim4]; simpl in *.
    - rewrite claim4 in claim3.
      unfold Not_b, IFProp in claim3.
      destruct (EM (T = T))...
    - apply claim2...
      rewrite claim3.
      unfold Not_b, IFProp.
      destruct (EM (R U R = T))...
  Qed.

  End Retracts.

  Theorem ProofIrrelevance {P : Prop} :
    forall p1 : P,
    forall p2 : P,
    p1 = p2.
  Proof.
    exact (@classical_proof_irrelevance P).
  Qed.

  End Berardis_paradox.

End ExclusiveMiddleFacts_prototype.
