Require Import DschingisKhan.pure.MyUtilities.

Module FunFacts.

  Import EqFacts MyUtilities.

  Record RETRACT (A : Prop) (B : Prop) : Prop :=
    { _i : A -> B
    ; _j : B -> A
    ; _inv : forall a : A, _j (_i a) = a
    }
  .

  Record RETRACT_CONDITIONAL (A : Prop) (B : Prop) : Prop :=
    { _i2 : A -> B
    ; _j2 : B -> A
    ; _inv2 : RETRACT A B -> forall a : A, _j2 (_i2 a) = a
    }
  .

  Inductive BB : Prop :=
  | TRUE_BB : BB
  | FALSE_BB : BB
  .

  Local Hint Constructors RETRACT RETRACT_CONDITIONAL : core.

  Section PROOF_IRRELEVANCE_implies_EQ_RECT_EQ.

  Hypothesis proof_irrelevance : forall P : Prop, forall p1 : P, forall p2 : P, p1 = p2.

  Theorem proof_irrelevance_implies_eq_rect_eq (A : Type) (x : A) (B : A -> Type) (y : B x) (H : x = x) :
    y = eq_rect x B y x H.
  Proof with reflexivity.
    rewrite <- (proof_irrelevance (@eq A x x) (@eq_refl A x) H)...
  Qed.

  End PROOF_IRRELEVANCE_implies_EQ_RECT_EQ.

  Section EQ_RECT_EQ_implies_STREICHER_K.

  Hypothesis eq_rect_eq : forall A : Type, forall x : A, forall B : A -> Type, forall y : B x, forall H : x = x, y = eq_rect x B y x H.

  Theorem eq_rect_eq_implies_Streicher_K (A : Type) :
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
    - rewrite (eq_rect_eq A x (eq x) eq_val eq_val0).
      destruct eq_val0.
      reflexivity.
  Qed.

  End EQ_RECT_EQ_implies_STREICHER_K.

  Section EQ_RECT_EQ_implies_EXISTT_INJ2_EQ.

  Hypothesis eq_rect_eq : forall A : Type, forall x : A, forall B : A -> Type, forall y : B x, forall H : x = x, y = eq_rect x B y x H.

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

  Theorem eq_rect_eq_implies_existT_inj2_eq :
    forall x : A,
    forall y1 : B x,
    forall y2 : B x,
    existT B x y1 = existT B x y2 ->
    y1 = y2.
  Proof.
    intros x y1 y2 Heq.
    exact (phi (existT B x y1) (existT B x y2) Heq (fun H : x = x => eq_symmetry y2 (eq_rect x B y2 x H) (eq_rect_eq A x B y2 H)) (eq_reflexivity (projT1 (existT B x y1)))).
  Qed.

  End EQ_RECT_EQ_implies_EXISTT_INJ2_EQ.

  Section EXCLUSIVE_MIDDLE_implies_PROOF_IRRELEVANCE. (* Reference: "https://coq.inria.fr/library/Coq.Logic.Berardi.html" *)

  Hypothesis exclusive_middle : forall P : Prop, P \/ ~ P.

  Let CHOICE {A : Prop} {B : Prop} :
    forall r : RETRACT_CONDITIONAL A B,
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

  Let GET_RETRACT_CONDITIONAL_POW_A_POW_B :
    forall A : Prop,
    forall B : Prop,
    RETRACT_CONDITIONAL (POW A) (POW B).
  Proof with tauto.
    intros A B.
    destruct (exclusive_middle (RETRACT (POW A) (POW B))) as [H_yes | H_no].
    - destruct H_yes as [i j inv].
      exists i j...
    - exists (fun pa : POW A => fun b : B => FALSE) (fun pb : POW B => fun a : A => FALSE)...
  Qed.

  Let U : Prop :=
    forall P : Prop,
    POW P
  .

  Let r : POW U -> U :=
    fun p : POW U =>
    fun P : Prop =>
    let LEFT : POW U -> POW P := _j2 (POW P) (POW U) (GET_RETRACT_CONDITIONAL_POW_A_POW_B P U) in
    let RIGHT : POW U -> POW U := _i2 (POW U) (POW U) (GET_RETRACT_CONDITIONAL_POW_A_POW_B U U) in
    LEFT (RIGHT p)
  .

  Let RETRACT_POW_U_POW_U : RETRACT (POW U) (POW U) :=
    {| _i := fun p : POW U => p; _j := fun p : POW U => p; _inv := @eq_refl (POW U) |}
  .

  Let NOT : BOOL -> BOOL :=
    fun b : BOOL =>
    match (exclusive_middle (b = TRUE)) with
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
    destruct (exclusive_middle (RUSSEL = TRUE)) as [H | H].
    - assert (claim1 : TRUE = NOT TRUE) by now rewrite <- H; exact PARADOX_OF_BERARDI.
      unfold NOT in claim1.
      destruct (exclusive_middle (TRUE = TRUE)) as [H_yes | H_no]...
    - assert (claim1 : NOT RUSSEL <> TRUE) by now rewrite <- PARADOX_OF_BERARDI; exact H.
      unfold NOT in claim1. 
      destruct (exclusive_middle (RUSSEL = TRUE)) as [H_yes | H_no]...
  Qed.

  End EXCLUSIVE_MIDDLE_implies_PROOF_IRRELEVANCE.

  Section EXCLUSIVE_MIDDLE_implies_UNRESTRICTED_MINIMIZATION.

  Hypothesis exclusive_middle : forall P : Prop, P \/ ~ P.

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
    destruct (exclusive_middle (forall x : nat, ~ isMinimal x)) as [H_yes | H_no].
    - assert (claim1 : forall x : nat, x < n -> ~ phi n).
      { intros x x_lt_n.
        pattern n.
        apply strong_induction.
        intros i acc phi_i.
        contradiction (H_yes i).
        split.
        - apply phi_i.
        - intros m phi_m.
          destruct (n_le_m_or_m_lt_n_for_n_and_m i m) as [i_le_m | m_lt_i]; firstorder.
      }
      exists n.
      split.
      + exact phi_n.
      + intros m phi_m.
        destruct (n_le_m_or_m_lt_n_for_n_and_m n m) as [n_le_m | m_lt_n]; firstorder.
    - destruct (exclusive_middle (exists m : nat, isMinimal m)); firstorder.
  Qed.

  End EXCLUSIVE_MIDDLE_implies_UNRESTRICTED_MINIMIZATION.

  Section UNTYPED_LAMBDA_CALCULUS_FOR_BB_implies_PARADOX_OF_RUSSEL.

  Hypothesis untyped_lambda_calculus_for_BB : RETRACT (BB -> BB) BB.

  Let Y_COMBINATOR_FOR_BB :
    exists Y : (BB -> BB) -> BB, forall f : BB -> BB, Y f = f (Y f).
  Proof with try easy.
    destruct untyped_lambda_calculus_for_BB as [lam_BB app_BB beta_BB].
    set (Y_com := fun f : BB -> BB => app_BB (lam_BB (fun x : BB => f (app_BB x x))) (lam_BB (fun x : BB => f (app_BB x x)))).
    exists Y_com.
    intros f.
    enough (claim1 : app_BB (lam_BB (fun x : BB => f (app_BB x x))) (lam_BB (fun x : BB => f (app_BB x x))) = f (Y_com f))...
    replace (app_BB (lam_BB (fun x : BB => f (app_BB x x)))) with (fun x : BB => f (app_BB x x))...
  Qed.

  Let NOT_BB : BB -> BB :=
    fun b : BB =>
    match b return BB with
    | TRUE_BB => FALSE_BB
    | FALSE_BB => TRUE_BB
    end
  .

  Theorem untyped_lambda_calculus_for_BB_implies_paradox_of_russel :
    TRUE_BB = FALSE_BB.
  Proof with eauto.
    assert (BB_inhabited : inhabited BB) by repeat constructor.
    destruct Y_COMBINATOR_FOR_BB as [Y Y_spec].
    set (RUSSEL := Y NOT_BB).
    assert (RUSSEL_PARADOX : RUSSEL = NOT_BB RUSSEL) by now apply Y_spec.
    unfold NOT_BB in RUSSEL_PARADOX.
    destruct RUSSEL...
  Qed.

  End UNTYPED_LAMBDA_CALCULUS_FOR_BB_implies_PARADOX_OF_RUSSEL.

  Section PROPOSITIONAL_EXTENSIONALITY_implies_PROOF_IRRELEVANCE. (* Reference: "https://coq.inria.fr/library/Coq.Logic.ClassicalFacts.html" *)

  Hypothesis propositional_extensionality : forall P1 : Prop, forall P2 : Prop, (P1 <-> P2) <-> (P1 = P2).

  Let D_coerce_D_ARROW_D_for_any_inhabited_Prop_D (D : Prop) (D_inhabited : inhabited D) :
    D = (D -> D).
  Proof with tauto.
    destruct D_inhabited as [d0].
    apply (proj1 (propositional_extensionality D (D -> D)))...
  Qed.

  Let UNTYPED_LAMBDA_CALCULUS_for_any_inhabited_Prop (D : Prop) (D_inhabited : inhabited D) :
    RETRACT (D -> D) D.
  Proof with eauto.
    replace (D -> D) with D...
    exists (fun d : D => d) (fun d : D => d)...
  Qed.

  Theorem propositional_extensionality_implies_proof_irrelevance :
    forall BOOL : Prop,
    forall TRUE : BOOL,
    forall FALSE : BOOL,
    TRUE = FALSE.
  Proof with eauto.
    assert (BB_inhabited : inhabited BB) by now constructor; left.
    assert (claim1 := untyped_lambda_calculus_for_BB_implies_paradox_of_russel (UNTYPED_LAMBDA_CALCULUS_for_any_inhabited_Prop BB BB_inhabited)).
    intros BOOL TRUE FALSE.
    set (go := fun b : BB => if b then TRUE else FALSE).
    assert (claim2 : go TRUE_BB = go FALSE_BB) by now apply (eq_congruence go)...
  Qed.

  End PROPOSITIONAL_EXTENSIONALITY_implies_PROOF_IRRELEVANCE.

End FunFacts.
