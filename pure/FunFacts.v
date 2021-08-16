Require Import DschingisKhan.pure.MyUtilities.

Module FunFacts.

  Import EqFacts MyUtilities.

  Record RETRACT (A : Prop) (B : Prop) : Prop :=
    { _i : A -> B
    ; _j : B -> A
    ; _inv : forall a : A, _j (_i a) = a
    }
  .

  Record RETRACT_COND (A : Prop) (B : Prop) : Prop :=
    { _i2 : A -> B
    ; _j2 : B -> A
    ; _inv2 : RETRACT A B -> forall a : A, _j2 (_i2 a) = a
    }
  .

  Inductive BB : Prop :=
  | TRUE_BB : BB
  | FALSE_BB : BB
  .

  Local Hint Constructors RETRACT RETRACT_COND : core.

  Section PROOF_IRRELEVANCE_implies_EQ_RECT_EQ.

  Hypothesis proof_irrelevance : forall P : Prop, forall p1 : P, forall p2 : P, p1 = p2.

  Theorem proof_irrelevance_implies_eq_rect_eq (A : Type) (x : A) (B : A -> Type) (y : B x) (H : x = x) :
    y = eq_rect x B y x H.
  Proof with reflexivity.
    rewrite <- (proof_irrelevance (@eq A x x) (@eq_refl A x) H)...
  Qed.

  End PROOF_IRRELEVANCE_implies_EQ_RECT_EQ.

  Section EQ_RECT_EQ_implies_STREICHER_K.

  Hypothesis EQ_RECT_EQ : forall A : Type, forall x : A, forall B : A -> Type, forall y : B x, forall H : x = x, y = eq_rect x B y x H.

  Lemma eq_rect_eq_implies_Streicher_K (A : Type) :
    forall x : A,
    forall phi : x = x -> Type,
    phi (eq_reflexivity x) ->
    forall eq_val0 : x = x,
    phi eq_val0.
  Proof.
    intros x.
    set (eq_val := eq_reflexivity x). 
    intros phi phi_eq_val eq_val0.
    replace eq_val0 with eq_val.
    - apply phi_eq_val.
    - rewrite (EQ_RECT_EQ A x (eq x) eq_val eq_val0).
      destruct eq_val0.
      reflexivity.
  Qed.

  End EQ_RECT_EQ_implies_STREICHER_K.

  Section EQ_RECT_EQ_implies_EXISTT_INJ2_EQ.

  Hypothesis EQ_RECT_EQ : forall A : Type, forall x : A, forall B : A -> Type, forall y : B x, forall H : x = x, y = eq_rect x B y x H.

  Context (A : Type) (B : A -> Type).

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

  Definition eq_rect_eq_implies_existT_inj2_eq : forall x : A, forall y1 : B x, forall y2 : B x, existT B x y1 = existT B x y2 -> y1 = y2 :=
    fun x : A =>
    fun y1 : B x =>
    fun y2 : B x =>
    fun H : existT B x y1 = existT B x y2 =>
    phi (existT B x y1) (existT B x y2) H (fun H0 : x = x => eq_symmetry y2 (eq_rect x B y2 x H0) (EQ_RECT_EQ A x B y2 H0)) eq_refl
  .

  End EQ_RECT_EQ_implies_EXISTT_INJ2_EQ.

  Section EXCLUSIVE_MIDDLE_implies_PROOF_IRRELEVANCE. (* Reference: "https://coq.inria.fr/library/Coq.Logic.Berardi.html" *)

  Hypothesis EXCLUSIVE_MIDDLE : forall P : Prop, P \/ ~ P.

  Let CHOICE {A : Prop} {B : Prop} :
    forall r : RETRACT_COND A B,
    RETRACT A B ->
    forall a : A,
    _j2 A B r (_i2 A B r a) = a.
  Proof with eauto.
    intros [i2 j2 inv2] [i j inv]...
  Qed.

  Context (BOOL : Prop) (TRUE : BOOL) (FALSE : BOOL).

  Let POW : Prop -> Prop :=
    fun P : Prop =>
    P ->
    BOOL
  .

  Let COND :
    forall A : Prop,
    forall B : Prop,
    RETRACT_COND (POW A) (POW B).
  Proof with tauto.
    intros A B.
    destruct (EXCLUSIVE_MIDDLE (RETRACT (POW A) (POW B))) as [[i j inv] | H].
    - exists i j...
    - exists (fun pa : POW A => fun b : B => FALSE) (fun pb : POW B => fun a : A => FALSE)...
  Qed.

  Let U : Prop :=
    forall P : Prop,
    POW P
  .

  Let r : POW U -> U :=
    fun p : POW U =>
    fun P : Prop =>
    let LEFT : POW U -> POW P := _j2 (POW P) (POW U) (COND P U) in
    let RIGHT : POW U -> POW U := _i2 (POW U) (POW U) (COND U U) in
    LEFT (RIGHT p)
  .

  Let RETRACT_POW_U_POW_U : RETRACT (POW U) (POW U) :=
    {| _i := fun p : POW U => p; _j := fun p : POW U => p; _inv := @eq_refl (POW U) |}
  .

  Let NOT : BOOL -> BOOL :=
    fun b : BOOL =>
    match (EXCLUSIVE_MIDDLE (b = TRUE)) with
    | or_introl H_yes => FALSE
    | or_intror H_no => TRUE
    end
  .

  Let R : U :=
    r (fun u : U => NOT (u U u))
  .

  Let RUSSEL : BOOL :=
    R U R
  .

  Let PARADOX_OF_BERARDI :
    RUSSEL = NOT RUSSEL.
  Proof with eauto.
    set (app := fun p : POW U => fun u : U => p u).
    enough (claim1 : RUSSEL = app (fun u : U => NOT (u U u)) R) by exact claim1.
    replace (fun u : U => NOT (u U u)) with (R U)...
  Qed.

  Theorem exclusive_middle_implies_proof_irrelevance :
    TRUE = FALSE.
  Proof with tauto.
    destruct (EXCLUSIVE_MIDDLE (RUSSEL = TRUE)) as [H | H].
    - assert (claim1 : TRUE = NOT TRUE) by now rewrite <- H; exact PARADOX_OF_BERARDI.
      unfold NOT in claim1.
      destruct (EXCLUSIVE_MIDDLE (TRUE = TRUE)) as [H_yes | H_no]...
    - assert (claim1 : NOT RUSSEL <> TRUE) by now rewrite <- PARADOX_OF_BERARDI; exact H.
      unfold NOT in claim1. 
      destruct (EXCLUSIVE_MIDDLE (RUSSEL = TRUE)) as [H_yes | H_no]...
  Qed.

  End EXCLUSIVE_MIDDLE_implies_PROOF_IRRELEVANCE.

  Section EXCLUSIVE_MIDDLE_implies_UNRESTRICTED_MINIMIZATION.

  Hypothesis EXCLUSIVE_MIDDLE : forall P : Prop, P \/ ~ P.

  Context (phi : nat -> Prop).

  Let isMinimal : nat -> Prop :=
    fun n : nat =>
    phi n /\ (forall m : nat, phi m -> n <= m)
  .

  Theorem exclusive_middle_implies_unrestricted_minimization :
    forall n : nat,
    phi n ->
    exists n_min : nat, isMinimal n_min.
  Proof with eauto.
    intros n phi_n.
    destruct (EXCLUSIVE_MIDDLE (forall x : nat, ~ isMinimal x)) as [H_yes | H_no].
    - assert (claim1 : forall x : nat, x < n -> ~ phi n).
      { intros x x_lt_n.
        pattern n.
        apply strong_induction.
        intros i acc phi_i.
        contradiction (H_yes i).
        split.
        - apply phi_i.
        - intros m phi_m.
          destruct (Compare_dec.le_lt_dec i m) as [i_le_m | m_lt_i]; firstorder.
      }
      exists n.
      split.
      + apply phi_n.
      + intros m phi_m.
        destruct (Compare_dec.le_lt_dec n m) as [n_le_m | m_lt_n]; firstorder.
    - destruct (EXCLUSIVE_MIDDLE (exists m : nat, isMinimal m)); firstorder.
  Qed.

  End EXCLUSIVE_MIDDLE_implies_UNRESTRICTED_MINIMIZATION.

  Section PROPOSITIONAL_EXTENSIONALITY_implies_PROOF_IRRELEVANCE. (* Reference: "https://coq.inria.fr/library/Coq.Logic.ClassicalFacts.html" *)

  Hypothesis propositional_extensionality : forall P1 : Prop, forall P2 : Prop, (P1 <-> P2) <-> (P1 = P2).

  Let A_COERCE_A_ARROW_A (A : Prop) `{A_inhabited : inhabited A} :
    A = (A -> A).
  Proof with tauto.
    destruct A_inhabited as [a].
    apply (propositional_extensionality A (A -> A))...
  Qed.

  Let UNTYPED_LAMBDA_CALCULUS (A : Prop) `{A_inhabited : inhabited A} :
    RETRACT (A -> A) A.
  Proof with eauto.
    replace (A -> A) with A...
    exists (fun a : A => a) (fun a : A => a)...
  Qed.

  Let Y_COMBINATOR (A : Prop) `{A_inhabited : inhabited A} :
    exists fix_A : (A -> A) -> A, forall f : A -> A, fix_A f = f (fix_A f).
  Proof.
    destruct (@UNTYPED_LAMBDA_CALCULUS A A_inhabited) as [lam_A app_A beta_A].
    set (Y_com := fun f : A -> A => app_A (lam_A (fun x : A => f (app_A x x))) (lam_A (fun x : A => f (app_A x x)))).
    exists Y_com.
    intros f.
    enough (claim1 : app_A (lam_A (fun x : A => f (app_A x x))) (lam_A (fun x : A => f (app_A x x))) = f (Y_com f)) by exact claim1.
    rewrite (beta_A (fun x : A => f (app_A x x))).
    exact (eq_reflexivity (f (Y_com f))).
  Qed.

  Let NOT_BB : BB -> BB :=
    fun b : BB =>
    if b then FALSE_BB else TRUE_BB
  .

  Let PARADOX_OF_RUSSEL :
    TRUE_BB = FALSE_BB.
  Proof with eauto.
    assert (BB_inhabited : inhabited BB) by now constructor; left.
    destruct (@Y_COMBINATOR BB BB_inhabited) as [fix_BB fix_BB_spec].
    assert (claim1 : fix_BB NOT_BB = NOT_BB (fix_BB NOT_BB)) by now apply fix_BB_spec.
    set (RUSSEL := fix_BB NOT_BB).
    fold RUSSEL in claim1.
    unfold NOT_BB in claim1.
    destruct RUSSEL as [|]...
  Qed.

  Theorem propositional_extensionality_implies_proof_irrelevance :
    forall BOOL : Prop,
    forall TRUE : BOOL,
    forall FALSE : BOOL,
    TRUE = FALSE.
  Proof with eauto.
    intros BOOL TRUE FALSE.
    set (go := fun b : BB => if b then TRUE else FALSE).
    assert (claim1 : go TRUE_BB = go FALSE_BB) by now apply (eq_congruence go TRUE_BB FALSE_BB PARADOX_OF_RUSSEL).
    simpl in claim1...
  Qed.

  End PROPOSITIONAL_EXTENSIONALITY_implies_PROOF_IRRELEVANCE.

  Section AXIOM_OF_CHOICE_implies_EXCLUSIVE_MIDDLE.

End FunFacts.
