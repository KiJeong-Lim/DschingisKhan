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

  Local Hint Constructors RETRACT RETRACT_CONDITIONAL : core.

  Lemma RETRACT_ID (A : Prop) :
    RETRACT A A.
  Proof.
    exists (fun x : A => x) (fun x : A => x).
    exact (@eq_refl A).
  Qed.

  Local Hint Resolve RETRACT_ID : core.

  Lemma FIND_FIXED_POINT_COMBINATOR (D : Prop) (untyped_lambda_calculus_for_D : RETRACT (D -> D) D) :
    {Y : (D -> D) -> D | forall f : D -> D, Y f = f (Y f)}.
  Proof.
    destruct untyped_lambda_calculus_for_D as [lam_D app_D beta_D].
    set (Y_combinator_of_Curry := fun f : D -> D => app_D (lam_D (fun x : D => f (app_D x x))) (lam_D (fun x : D => f (app_D x x)))).
    exists Y_combinator_of_Curry.
    intros f.
    enough (it_is_sufficient_to_show : app_D (lam_D (fun x : D => f (app_D x x))) (lam_D (fun x : D => f (app_D x x))) = f (Y_combinator_of_Curry f)) by exact it_is_sufficient_to_show.
    now replace (app_D (lam_D (fun x : D => f (app_D x x)))) with (fun x : D => f (app_D x x)).
  Qed.

  Inductive BB : Prop :=
  | TRUE_BB : BB
  | FALSE_BB : BB
  .

  Section PROOF_IRRELEVANCE_implies_EQ_RECT_EQ.

  Hypothesis proof_irrelevance : forall P : Prop, forall p1 : P, forall p2 : P, p1 = p2.

  Theorem proof_irrelevance_implies_eq_rect_eq (A : Type) (x : A) (B : A -> Type) (y : B x) (H : x = x) :
    y = eq_rect x B y x H.
  Proof.
    now rewrite <- (proof_irrelevance (x = x) (eq_reflexivity x) H).
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
    - exact phi_eq_val.
    - rewrite (eq_rect_eq A x (eq x) eq_val eq_val0).
      now destruct eq_val0.
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

  Let inv2 {A : Prop} {B : Prop} : forall r : RETRACT_CONDITIONAL A B, RETRACT A B -> forall a : A, _j2 A B r (_i2 A B r a) = a :=
    _inv2 A B
  .

  Let POW : Prop -> Prop :=
    fun P : Prop =>
    P ->
    BB
  .

  Let RETRACT_CONDITIONAL_POW_A_POW_B :
    forall A : Prop,
    forall B : Prop,
    RETRACT_CONDITIONAL (POW A) (POW B).
  Proof with tauto.
    intros A B.
    destruct (exclusive_middle (RETRACT (POW A) (POW B))) as [H_yes | H_no].
    - destruct H_yes as [i j inv].
      exists i j...
    - exists (fun pa : POW A => fun b : B => FALSE_BB) (fun pb : POW B => fun a : A => FALSE_BB)...
  Qed.

  Let UNIV : Prop :=
    forall P : Prop,
    POW P
  .

  Let SATISFIES : UNIV -> (UNIV -> BB) -> BB :=
    fun x : UNIV =>
    fun phi : UNIV -> BB =>
    phi x
  .

  Local Notation " x `satisfies` phi " := (SATISFIES x phi) (at level 60, no associativity) : type_scope.

  Let SET_BUILDER_NOTATION : (UNIV -> BB) -> UNIV :=
    fun phi : UNIV -> BB =>
    fun P : Prop =>
    let LEFT : POW UNIV -> POW P := _j2 (POW P) (POW UNIV) (RETRACT_CONDITIONAL_POW_A_POW_B P UNIV) in
    let RIGHT : POW UNIV -> POW UNIV := _i2 (POW UNIV) (POW UNIV) (RETRACT_CONDITIONAL_POW_A_POW_B UNIV UNIV) in
    LEFT (RIGHT phi)
  .

  Local Notation " ⦃ x | P ⦄ " := (SET_BUILDER_NOTATION (fun x : UNIV => P)) (at level 0, no associativity) : type_scope.

  Let HAS_AS_AN_ELEMENT : UNIV -> UNIV -> BB :=
    fun x : UNIV =>
    fun z : UNIV =>
    x UNIV z
  .

  Local Notation " z ∈ x " := (HAS_AS_AN_ELEMENT x z) (at level 70, no associativity) : type_scope.

  Let SET_BUILDER_NOTATION_SPEC :
    forall phi : UNIV -> BB,
    (fun z : UNIV => z ∈ ⦃ x | x `satisfies` phi ⦄) = phi.
  Proof with eauto.
    unfold SET_BUILDER_NOTATION, HAS_AS_AN_ELEMENT, SATISFIES.
    destruct (RETRACT_CONDITIONAL_POW_A_POW_B UNIV UNIV); simpl in *...
  Qed.

  Let RETRACT_POW_UNIV_UNIV : RETRACT (POW UNIV) UNIV :=
    {| _i := SET_BUILDER_NOTATION; _j := HAS_AS_AN_ELEMENT; _inv := SET_BUILDER_NOTATION_SPEC |}
  .

  Let NOT_BB : BB -> BB :=
    fun b : BB =>
    match exclusive_middle (b = TRUE_BB) return BB with
    | or_introl if_b_eq_TRUE_BB => FALSE_BB
    | or_intror if_b_ne_TRUE_BB => TRUE_BB
    end
  .

  Local Notation " ¬ b " := (NOT_BB b) (at level 55, right associativity) : type_scope.

  Let NOT_BB_SPEC1 :
    forall b : BB,
    (b = TRUE_BB) ->
    (¬ b) = FALSE_BB.
  Proof with tauto.
    unfold NOT_BB.
    intros b.
    destruct (exclusive_middle (b = TRUE_BB)); simpl...
  Qed.

  Let NOT_BB_SPEC2 :
    forall b : BB,
    ~ (b = TRUE_BB) ->
    (¬ b) = TRUE_BB.
  Proof with tauto.
    unfold NOT_BB.
    intros b.
    destruct (exclusive_middle (b = TRUE_BB)); simpl...
  Qed.

  Let R : UNIV :=
    ⦃ x | ¬ (x ∈ x) ⦄
  .

  Let RUSSELL : BB :=
    R ∈ R
  .

  Let PARADOX_OF_BERARDI :
    RUSSELL = ¬ RUSSELL.
  Proof with eauto.
    enough (it_is_sufficient_to_show : RUSSELL = (R `satisfies` (fun x : UNIV => ¬ (x ∈ x)))) by exact it_is_sufficient_to_show.
    replace (fun x : UNIV => ¬ (x ∈ x)) with (R UNIV)...
  Qed.

  Theorem exclusive_middle_implies_proof_irrelevance :
    forall BOOL : Prop,
    forall TRUE : BOOL,
    forall FALSE : BOOL,
    TRUE = FALSE.
  Proof.
    enough (it_is_sufficient_to_show : TRUE_BB = FALSE_BB) by exact (fun BOOL : Prop => fun TRUE : BOOL => fun FALSE : BOOL => eq_congruence (fun b : BB => if b then TRUE else FALSE) TRUE_BB FALSE_BB it_is_sufficient_to_show).
    destruct (exclusive_middle (RUSSELL = TRUE_BB)) as [H_RUSSELL_eq_TRUE_BB | H_RUSSELL_ne_TRUE_BB].
    - rewrite <- H_RUSSELL_eq_TRUE_BB.
      rewrite PARADOX_OF_BERARDI.
      now apply NOT_BB_SPEC1.
    - contradiction H_RUSSELL_ne_TRUE_BB.
      rewrite PARADOX_OF_BERARDI.
      now apply NOT_BB_SPEC2.
  Qed.

  End EXCLUSIVE_MIDDLE_implies_PROOF_IRRELEVANCE.

  Section EXCLUSIVE_MIDDLE_implies_UNRESTRICTED_MINIMIZATION.

  Hypothesis exclusive_middle : forall P : Prop, P \/ ~ P.

  Let isMinimal : nat -> (nat -> Prop) -> Prop :=
    fun n : nat =>
    fun phi : nat -> Prop =>
    phi n /\ (forall m : nat, phi m -> n <= m)
  .

  Context (phi : nat -> Prop).

  Theorem exclusive_middle_implies_unrestricted_minimization :
    forall n : nat,
    phi n ->
    exists n_min : nat, isMinimal n_min phi.
  Proof.
    intros n phi_n.
    destruct (exclusive_middle (forall x : nat, ~ isMinimal x phi)) as [H_yes | H_no].
    - enough (claim1 : ~ phi n) by contradiction claim1.
      pattern n.
      apply strong_induction.
      intros i acc phi_i.
      contradiction (H_yes i).
      split.
      + exact phi_i.
      + intros m phi_m.
        destruct (n_le_m_or_m_lt_n_for_n_and_m i m); now firstorder.
    - destruct (exclusive_middle (exists m : nat, isMinimal m phi)); now firstorder.
  Qed.

  End EXCLUSIVE_MIDDLE_implies_UNRESTRICTED_MINIMIZATION.

  Section UNTYPED_LAMBDA_CALCULUS_FOR_BB_implies_PARADOX_OF_RUSSELL.

  Hypothesis untyped_lambda_calculus_for_BB : RETRACT (BB -> BB) BB.

  Let NOT_BB : BB -> BB :=
    fun b : BB =>
    match b return BB with
    | TRUE_BB => FALSE_BB
    | FALSE_BB => TRUE_BB
    end
  .

  Theorem untyped_lambda_calculus_for_BB_implies_paradox_of_russell :
    TRUE_BB = FALSE_BB.
  Proof.
    destruct (FIND_FIXED_POINT_COMBINATOR BB untyped_lambda_calculus_for_BB) as [Y Y_spec].
    set (RUSSELL := Y NOT_BB).
    assert (PARADOX_OF_RUSSELL : RUSSELL = NOT_BB RUSSELL) by now apply Y_spec.
    unfold NOT_BB in PARADOX_OF_RUSSELL.
    now destruct RUSSELL.
  Qed.

  End UNTYPED_LAMBDA_CALCULUS_FOR_BB_implies_PARADOX_OF_RUSSELL.

  Section PROPOSITIONAL_EXTENSIONALITY_implies_PROOF_IRRELEVANCE. (* Reference: "https://coq.inria.fr/library/Coq.Logic.ClassicalFacts.html" *)

  Hypothesis propositional_extensionality : forall P1 : Prop, forall P2 : Prop, (P1 <-> P2) -> (P1 = P2).

  Let D_coerce_D_ARROW_D_for_any_inhabited_Prop_D (D : Prop) (D_inhabited : inhabited D) :
    D = (D -> D).
  Proof with tauto.
    destruct D_inhabited as [d0].
    apply (propositional_extensionality D (D -> D))...
  Qed.

  Let UNTYPED_LAMBDA_CALCULUS_for_any_inhabited_Prop (D : Prop) (D_inhabited : inhabited D) :
    RETRACT (D -> D) D.
  Proof with eauto.
    replace (D -> D) with D...
  Qed.

  Theorem propositional_extensionality_implies_proof_irrelevance :
    forall BOOL : Prop,
    forall TRUE : BOOL,
    forall FALSE : BOOL,
    TRUE = FALSE.
  Proof.
    enough (it_is_sufficient_to_show : TRUE_BB = FALSE_BB) by exact (fun BOOL : Prop => fun TRUE : BOOL => fun FALSE : BOOL => eq_congruence (fun b : BB => if b then TRUE else FALSE) TRUE_BB FALSE_BB it_is_sufficient_to_show).
    assert (BB_inhabited : inhabited BB) by repeat constructor.
    exact (untyped_lambda_calculus_for_BB_implies_paradox_of_russell (UNTYPED_LAMBDA_CALCULUS_for_any_inhabited_Prop BB BB_inhabited)).
  Qed.

  End PROPOSITIONAL_EXTENSIONALITY_implies_PROOF_IRRELEVANCE.

End FunFacts.
