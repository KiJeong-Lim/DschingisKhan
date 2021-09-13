Require Import DschingisKhan.pure.MyUtilities.

Module FunFacts.

  Import EqFacts MyUtilities.

  Record RETRACT (A : Prop) (B : Prop) : Prop :=
    { _i : A -> B
    ; _j : B -> A
    ; _inv : forall x : A, _j (_i x) = x
    }
  .

  Record RETRACT2 (A : Prop) (B : Prop) : Prop :=
    { _i2 : A -> B
    ; _j2 : B -> A
    ; _inv2 : RETRACT A B -> forall x : A, _j2 (_i2 x) = x
    }
  .

  Definition get_i {A : Prop} {B : Prop} : RETRACT A B -> A -> B :=
    _i A B
  .

  Definition get_j {A : Prop} {B : Prop} : RETRACT A B -> B -> A :=
    _j A B
  .

  Definition get_inv {A : Prop} {B : Prop} : forall r : RETRACT A B, forall x : A, get_j r (get_i r x) = x :=
    _inv A B
  .

  Definition get_i2 {A : Prop} {B : Prop} : RETRACT2 A B -> A -> B :=
    _i2 A B
  .

  Definition get_j2 {A : Prop} {B : Prop} : RETRACT2 A B -> B -> A :=
    _j2 A B
  .

  Definition get_inv2 {A : Prop} {B : Prop} : forall r : RETRACT2 A B, RETRACT A B -> forall x : A, get_j2 r (get_i2 r x) = x :=
    _inv2 A B
  .

  Definition RETRACT_A_A : forall A : Prop, RETRACT A A :=
    fun A : Prop =>
    {| _i := fun x : A => x; _j := fun x : A => x; _inv := @eq_refl A |}
  .

  Local Hint Resolve get_inv get_inv2 RETRACT_A_A : core.

  Lemma derive_fixedpoint_combinator (D : Prop) :
    RETRACT (D -> D) D ->
    {Y : (D -> D) -> D | forall f : D -> D, Y f = f (Y f)}.
  Proof.
    intros [lam_D app_D beta_D].
    pose (Y_combinator_of_Curry := fun f : D -> D => app_D (lam_D (fun x : D => f (app_D x x))) (lam_D (fun x : D => f (app_D x x)))).
    exists Y_combinator_of_Curry.
    intros f.
    enough (it_is_sufficient_to_show : app_D (lam_D (fun x : D => f (app_D x x))) (lam_D (fun x : D => f (app_D x x))) = f (Y_combinator_of_Curry f)) by exact it_is_sufficient_to_show.
    now replace (app_D (lam_D (fun x : D => f (app_D x x)))) with (fun x : D => f (app_D x x)).
  Qed.

  Inductive BB : Prop :=
  | TRUE_BB : BB
  | FALSE_BB : BB
  .

  Lemma TRUE_BB_eq_FALSE_BB_implies_proof_irrelevance :
    TRUE_BB = FALSE_BB ->
    forall BOOL : Prop,
    forall TRUE : BOOL,
    forall FALSE : BOOL,
    TRUE = FALSE.
  Proof.
    intros TRUE_BB_eq_FALSE_BB BOOL TRUE FALSE.
    exact (eq_congruence (fun b : BB => if b then TRUE else FALSE) TRUE_BB FALSE_BB TRUE_BB_eq_FALSE_BB).
  Qed.

  Section PROOF_IRRELEVANCE_implies_EQ_RECT_EQ.

  Hypothesis proof_irrelevance : forall P : Prop, forall p1 : P, forall p2 : P, p1 = p2.

  Theorem proof_irrelevance_implies_eq_rect_eq (A : Type) (x : A) (B : A -> Type) (y : B x) (H : x = x) :
    y = eq_rect x B y x H.
  Proof.
    now rewrite <- (proof_irrelevance (x = x) (eq_reflexivity x) H).
  Qed.

  End PROOF_IRRELEVANCE_implies_EQ_RECT_EQ.

  Section EQ_RECT_EQ_implies_STREICHER_K.

  Context (A : Type) (x : A).

  Hypothesis eq_rect_eq : forall B : A -> Type, forall y : B x, forall H : x = x, y = eq_rect x B y x H.

  Theorem eq_rect_eq_implies_Streicher_K :
    forall phi : x = x -> Type,
    phi (eq_reflexivity x) ->
    forall eq_val0 : x = x,
    phi eq_val0.
  Proof.
    set (eq_val := eq_reflexivity x). 
    intros phi phi_eq_val eq_val0.
    replace (eq_val0) with (eq_val).
    - exact phi_eq_val.
    - rewrite (eq_rect_eq (eq x) eq_val eq_val0).
      now destruct eq_val0.
  Qed.

  End EQ_RECT_EQ_implies_STREICHER_K.

  Section EQ_RECT_EQ_implies_EXISTT_INJ2_EQ.

  Context (A : Type) (x : A) (B : A -> Type).

  Hypothesis eq_rect_eq : forall y : B x, forall H : x = x, y = eq_rect x B y x H.

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
    forall y1 : B x,
    forall y2 : B x,
    existT B x y1 = existT B x y2 ->
    y1 = y2.
  Proof.
    intros y1 y2 Heq.
    exact (phi (existT B x y1) (existT B x y2) Heq (fun H : x = x => eq_symmetry y2 (eq_rect x B y2 x H) (eq_rect_eq y2 H)) (eq_reflexivity (projT1 (existT B x y1)))).
  Qed.

  End EQ_RECT_EQ_implies_EXISTT_INJ2_EQ.

  Section EXCLUSIVE_MIDDLE_implies_PROOF_IRRELEVANCE. (* Reference: "https://coq.inria.fr/library/Coq.Logic.Berardi.html" *)

  Hypothesis exclusive_middle : forall P : Prop, P \/ ~ P.

  Let POW : Prop -> Prop :=
    fun P : Prop =>
    P ->
    BB
  .

  Let RETRACT2_POW_A_POW_B (A : Prop) (B : Prop) :
    RETRACT2 (POW A) (POW B).
  Proof.
    destruct (exclusive_middle (RETRACT (POW A) (POW B))) as [H_yes | H_no].
    - exact ({| _i2 := get_i H_yes; _j2 := get_j H_yes; _inv2 := fun _ : RETRACT (POW A) (POW B) => get_inv H_yes |}).
    - exact ({| _i2 := fun _ : POW A => fun _ : B => FALSE_BB; _j2 := fun _ : POW B => fun _ : A => FALSE_BB; _inv2 := fun r : RETRACT (POW A) (POW B) => False_ind (forall pa : POW A, (fun _ : A => FALSE_BB) = pa) (H_no r) |}).
  Qed.

  Let UNIV : Prop :=
    forall P : Prop,
    POW P
  .

  Let SET_BUILDER_NOTATION : (UNIV -> BB) -> UNIV :=
    fun phi : UNIV -> BB =>
    fun P : Prop =>
    let LEFT : POW UNIV -> POW P := get_j2 (RETRACT2_POW_A_POW_B P UNIV) in
    let RIGHT : POW UNIV -> POW UNIV := get_i2 (RETRACT2_POW_A_POW_B UNIV UNIV) in
    LEFT (RIGHT phi)
  .

  Local Notation " ⦃ x | P ⦄ " := (SET_BUILDER_NOTATION (fun x : UNIV => P)) (at level 0, no associativity) : type_scope.

  Let HAS_AS_AN_ELEMENT : UNIV -> UNIV -> BB :=
    fun x : UNIV =>
    x UNIV
  .

  Local Notation " z ∈ x " := (HAS_AS_AN_ELEMENT x z) (at level 70, no associativity) : type_scope.

  Let SET_BUILDER_NOTATION_SPEC :
    forall phi : UNIV -> BB,
    (fun z : UNIV => z ∈ ⦃ x | phi x ⦄) = phi.
  Proof with eauto.
    unfold SET_BUILDER_NOTATION, HAS_AS_AN_ELEMENT.
    destruct (RETRACT2_POW_A_POW_B UNIV UNIV); simpl in *...
  Qed.

  Let RETRACT_POW_UNIV_UNIV : RETRACT (UNIV -> BB) UNIV :=
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

  Let NOT_BB_SPEC1 (b : BB) (if_b_eq_TRUE_BB : b = TRUE_BB) :
    (¬ b) = FALSE_BB.
  Proof with tauto.
    unfold NOT_BB.
    destruct (exclusive_middle (b = TRUE_BB))...
  Qed.

  Let NOT_BB_SPEC2 (b : BB) (if_b_ne_TRUE_BB : b <> TRUE_BB) :
    (¬ b) = TRUE_BB.
  Proof with tauto.
    unfold NOT_BB.
    destruct (exclusive_middle (b = TRUE_BB))...
  Qed.

  Let russell : UNIV -> BB :=
    fun r : UNIV =>
    ¬ (r ∈ r)
  .

  Let R : UNIV :=
    ⦃ r | russell r ⦄
  .

  Let RUSSELL : BB :=
    R ∈ R
  .

  Let PARADOX_OF_BERARDI :
    RUSSELL = ¬ RUSSELL.
  Proof with eauto.
    enough (it_is_sufficient_to_show : RUSSELL = russell R) by exact it_is_sufficient_to_show.
    replace (russell) with (fun r : UNIV => r ∈ R)...
  Qed.

  Theorem exclusive_middle_implies_proof_irrelevance :
    forall P : Prop,
    forall p1 : P,
    forall p2 : P,
    p1 = p2.
  Proof.
    apply TRUE_BB_eq_FALSE_BB_implies_proof_irrelevance.
    destruct (exclusive_middle (RUSSELL = TRUE_BB)) as [RUSSELL_eq_TRUE_BB | RUSSELL_ne_TRUE_BB].
    - rewrite <- RUSSELL_eq_TRUE_BB.
      rewrite PARADOX_OF_BERARDI.
      now apply NOT_BB_SPEC1.
    - contradiction RUSSELL_ne_TRUE_BB.
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

  Theorem exclusive_middle_implies_unrestricted_minimization (phi : nat -> Prop) :
    (~ forall n : nat, ~ phi n) ->
    exists n_min : nat, isMinimal n_min phi.
  Proof.
    intros not_forall_n_not_phi_n.
    assert (claim1 : exists n : nat, phi n) by now destruct (exclusive_middle (exists n : nat, phi n)); firstorder.
    destruct claim1 as [n phi_n].
    destruct (exclusive_middle (forall x : nat, ~ isMinimal x phi)) as [H_yes | H_no].
    - enough (it_is_sufficient_to_show : ~ phi n) by contradiction it_is_sufficient_to_show.
      apply (@strong_induction (fun x : nat => ~ phi x)).
      intros i acc_hyp phi_i.
      contradiction (H_yes i).
      split.
      + exact phi_i.
      + intros m phi_m.
        now destruct (n_le_m_or_m_lt_n_holds_for_any_n_and_any_m i m); firstorder.
    - now destruct (exclusive_middle (exists m : nat, isMinimal m phi)); firstorder.
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
    destruct (derive_fixedpoint_combinator BB untyped_lambda_calculus_for_BB) as [Y Y_spec].
    set (RUSSELL := Y NOT_BB).
    assert (PARADOX_OF_RUSSELL : RUSSELL = NOT_BB RUSSELL) by exact (Y_spec NOT_BB).
    unfold NOT_BB in PARADOX_OF_RUSSELL.
    now destruct RUSSELL.
  Qed.

  End UNTYPED_LAMBDA_CALCULUS_FOR_BB_implies_PARADOX_OF_RUSSELL.

  Section PROPOSITIONAL_EXTENSIONALITY_implies_PROOF_IRRELEVANCE. (* Reference: "https://coq.inria.fr/library/Coq.Logic.ClassicalFacts.html" *)

  Hypothesis propositional_extensionality : forall P1 : Prop, forall P2 : Prop, (P1 <-> P2) -> (P1 = P2).

  Let D_coerce_D_ARROW_D_for_any_inhabited_Prop_D (D : Prop) (D_inhabited : inhabited D) :
    D = (D -> D).
  Proof with tauto.
    destruct D_inhabited as [D_holds].
    apply propositional_extensionality...
  Qed.

  Let UNTYPED_LAMBDA_CALCULUS_for_any_inhabited_Prop (D : Prop) (D_inhabited : inhabited D) :
    RETRACT (D -> D) D.
  Proof with eauto.
    replace (D -> D) with (D)...
  Qed.

  Theorem propositional_extensionality_implies_proof_irrelevance :
    forall P : Prop,
    forall p1 : P,
    forall p2 : P,
    p1 = p2.
  Proof.
    assert (BB_inhabited : inhabited BB) by now constructor; exact FALSE_BB.
    exact (TRUE_BB_eq_FALSE_BB_implies_proof_irrelevance (untyped_lambda_calculus_for_BB_implies_paradox_of_russell (UNTYPED_LAMBDA_CALCULUS_for_any_inhabited_Prop BB BB_inhabited))).
  Qed.

  End PROPOSITIONAL_EXTENSIONALITY_implies_PROOF_IRRELEVANCE.

End FunFacts.
