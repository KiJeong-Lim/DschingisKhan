Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.

Module EQ_FACTS.

  Section EQ_CONSTRUCTORS.

  Context {A : Type}.

  Definition eq_reflexivity (x1 : A) : x1 = x1 := @eq_refl A x1.

  Definition eq_symmetry (x1 : A) (x2 : A) (hyp_1EQ2 : x1 = x2) : x2 = x1 := @eq_ind A x1 (fun x : A => x = x1) (@eq_refl A x1) x2 hyp_1EQ2.

  Definition eq_transitivity (x1 : A) (x2 : A) (x3 : A) (hyp_1EQ2 : x1 = x2) (hyp_2EQ3 : x2 = x3) : x1 = x3 := @eq_ind A x2 (fun x : A => x1 = x) hyp_1EQ2 x3 hyp_2EQ3.

  Context {B : Type}.

  Definition eq_congruence (f : A -> B) (x1 : A) (x2 : A) (hyp_1EQ2 : x1 = x2) : f x1 = f x2 := @eq_ind A x1 (fun x : A => f x1 = f x) (@eq_refl B (f x1)) x2 hyp_1EQ2.

  Context {C : Type}.

  Definition eq_congruence2 (f : A -> B -> C) (x1 : A) (x2 : A) (hyp_x_EQ : x1 = x2) (y1 : B) (y2 : B) (hyp_y_EQ : y1 = y2) : f x1 y1 = f x2 y2 := @eq_ind B y1 (fun y : B => f x1 y1 = f x2 y) (@eq_ind A x1 (fun x : A => f x1 y1 = f x y1) (@eq_refl C (f x1 y1)) x2 hyp_x_EQ) y2 hyp_y_EQ.

  End EQ_CONSTRUCTORS.

  Section EQ_DESTRUCTORS.

  Context {A : Type}.

  Definition rect_eq_l (lhs : A) (phi : forall rhs : A, lhs = rhs -> Type) (phi_pf : phi lhs (eq_reflexivity lhs)) (rhs : A) (hyp_eq : lhs = rhs) : phi rhs hyp_eq :=
    match hyp_eq as hyp_eq' in eq _ lhs' return phi lhs' hyp_eq' with
    | eq_refl => phi_pf
    end
  .

  Definition rect_eq_r_aux (rhs : A) (lhs : A) (hyp_eq : lhs = rhs) : forall phi : forall lhs : A, lhs = rhs -> Type, phi rhs (eq_reflexivity rhs) -> phi lhs hyp_eq :=
    match hyp_eq as hyp_eq' in eq _ rhs' return forall phi' : forall lhs' : A, lhs' = rhs' -> Type, phi' rhs' (eq_reflexivity rhs') -> phi' lhs hyp_eq' with
    | eq_refl => fun phi' : forall lhs' : A, lhs' = lhs -> Type => fun phi_pf' : phi' lhs (eq_reflexivity lhs) => phi_pf'
    end
  .

  Definition rect_eq_r (rhs : A) (phi : forall lhs : A, lhs = rhs -> Type) (phi_pf : phi rhs (eq_reflexivity rhs)) (lhs : A) (hyp_eq : lhs = rhs) : phi lhs hyp_eq := rect_eq_r_aux rhs lhs hyp_eq phi phi_pf.

  Context {B : A -> Type}.

  Definition elim_eq_l (x1 : A) (x2 : A) (hyp_eq : x1 = x2) (pf : B x1) : B x2 := eq_rect x1 B pf x2 hyp_eq.

  Definition elim_eq_r (x1 : A) (x2 : A) (hyp_eq : x1 = x2) (pf : B x2) : B x1 := eq_rect x2 B pf x1 (eq_symmetry x1 x2 hyp_eq).

  Local Notation pi_A_B := (forall x : A, B x).

  Lemma elim_eq_l_spec (x1 : A) (x2 : A) (f : pi_A_B) (hyp_eq : x1 = x2)
    : elim_eq_l x1 x2 hyp_eq (f x1) = elim_eq_l x2 x2 (eq_reflexivity x2) (f x2).
  Proof. destruct hyp_eq; reflexivity. Defined.

  Lemma elim_eq_r_spec (x1 : A) (x2 : A) (f : pi_A_B) (hyp_eq : x1 = x2)
    : elim_eq_r x1 x2 hyp_eq (f x2) = elim_eq_r x1 x1 (eq_reflexivity x1) (f x1).
  Proof. destruct hyp_eq; reflexivity. Defined.

  Definition transport {x1 : A} {x2 : A} (hyp_eq : x1 = x2) : B x1 -> B x2 := elim_eq_l x1 x2 hyp_eq.

  End EQ_DESTRUCTORS.

  Section EQ_EM_implies_EQ_PIRREL. (* Reference: "https://coq.inria.fr/library/Coq.Logic.Eqdep_dec.html" *)

  Context {A : Type}.

  Definition eq_round_trip (x : A) : forall y : A, forall hyp_eq : x = y, eq_transitivity y x y (eq_symmetry x y hyp_eq) hyp_eq = eq_reflexivity y :=
    rect_eq_l x (fun y : A => fun hyp_eq : x = y => eq_transitivity y x y (eq_symmetry x y hyp_eq) hyp_eq = eq_reflexivity y) (eq_reflexivity (eq_reflexivity x))
  .

  Variable x : A.

  Section ABSTRACT_FORM.

  Variable eq_encoder : forall y : A, x = y -> x = y.

  Let eq_decoder (y : A) : x = y -> x = y := eq_transitivity x x y (eq_symmetry x x (eq_encoder x (eq_reflexivity x))).

  Let eq_decoder_decodes_properly : forall y : A, forall hyp_eq : x = y, eq_decoder y (eq_encoder y hyp_eq) = hyp_eq :=
    rect_eq_l x (fun y : A => fun hyp_eq : x = y => eq_decoder y (eq_encoder y hyp_eq) = hyp_eq) (eq_round_trip x x (eq_encoder x (eq_reflexivity x)))
  .

  Hypothesis all_eq_codes_are_indistinguishable_from_each_other : forall y : A, forall hyp_eq1 : x = y, forall hyp_eq2 : x = y, eq_encoder y hyp_eq1 = eq_encoder y hyp_eq2.

  Definition eq_pirrel_holds_if_we_have_an_eq_encoder_which_returns_the_same_code (y : A) (hyp_eq1 : x = y) (hyp_eq2 : x = y) : hyp_eq1 = hyp_eq2 :=
    let claim1 : eq_decoder y (eq_encoder y hyp_eq1) = eq_decoder y (eq_encoder y hyp_eq2) := eq_congruence (eq_decoder y) (eq_encoder y hyp_eq1) (eq_encoder y hyp_eq2) (all_eq_codes_are_indistinguishable_from_each_other y hyp_eq1 hyp_eq2) in
    eq_ind (eq_decoder y (eq_encoder y hyp_eq2)) (fun hyp_eq : x = y => hyp_eq1 = hyp_eq) (eq_ind (eq_decoder y (eq_encoder y hyp_eq1)) (fun hyp_eq : x = y => hyp_eq = eq_decoder y (eq_encoder y hyp_eq2)) claim1 hyp_eq1 (eq_decoder_decodes_properly y hyp_eq1)) hyp_eq2 (eq_decoder_decodes_properly y hyp_eq2)
  .

  End ABSTRACT_FORM.

  Hypothesis eq_em : forall y : A, x = y \/ x <> y.

  Let my_eq_encoder (y : A) (hyp_eq : x = y) : x = y :=
    match eq_em y return x = y with
    | or_introl h_eq => h_eq
    | or_intror h_ne => False_ind (x = y) (h_ne hyp_eq)
    end
  .

  Lemma my_eq_encoder_x_eq_reflexivity_x_is
    (hyp_eq : x = x)
    : my_eq_encoder x (eq_reflexivity x) = my_eq_encoder x hyp_eq.
  Proof.
    keep (fun eq_em_x : x = x \/ x <> x => fun h_eq : x = x =>
      match eq_em_x return x = x with
      | or_introl Heq => Heq
      | or_intror Hne => False_ind (x = x) (Hne h_eq)
      end
    ) as ret.
    exact (
      match eq_em x as eq_em_x return ret eq_em_x (eq_reflexivity x) = ret eq_em_x hyp_eq with
      | or_introl h_eq => eq_reflexivity h_eq
      | or_intror h_ne => False_ind (False_ind (x = x) (h_ne (eq_reflexivity x)) = False_ind (x = x) (h_ne hyp_eq)) (h_ne hyp_eq)
      end
    ).
  Defined.

  Definition eq_em_implies_eq_pirrel : forall y : A, forall hyp_eq1 : x = y, forall hyp_eq2 : x = y, hyp_eq1 = hyp_eq2 :=
    eq_pirrel_holds_if_we_have_an_eq_encoder_which_returns_the_same_code my_eq_encoder (rect_eq_l x (fun y : A => fun hyp_eq1 : x = y => forall hyp_eq2 : x = y, my_eq_encoder y hyp_eq1 = my_eq_encoder y hyp_eq2) my_eq_encoder_x_eq_reflexivity_x_is)
  .

  End EQ_EM_implies_EQ_PIRREL.

  Lemma eq_pirrel_fromEqDec {A : Type} {requiresEqDec : EqDec A}
    : forall x : A, forall y : A, forall hyp_eq1 : x = y, forall hyp_eq2 : x = y, hyp_eq1 = hyp_eq2.
  Proof.
    intros x.
    keep (fun y : A =>
      match eq_dec x y with
      | left hyp_yes => or_introl hyp_yes
      | right hyp_no => or_intror hyp_no
      end
    ) as eq_em into (forall y : A, x = y \/ x <> y).
    exact (fun y : A => fun hyp_eq1 : x = y =>
      match hyp_eq1 as hyp_eq1' in eq _ y' return forall hyp_eq : x = y', hyp_eq1' = hyp_eq with
      | eq_refl => eq_em_implies_eq_pirrel x eq_em x (eq_reflexivity x)
      end
    ).
  Defined.

End EQ_FACTS.

Export EQ_FACTS.

Module NAT_FACTS.

  Global Notation zero := O.
  Global Notation suc := S.

  Definition is_suc (n : nat) : Prop :=
    match n with
    | zero => False
    | suc n' => True
    end
  .

  Definition not_S_n_eq_0 {n : nat} (hyp_eq : S n = 0) : False :=
    match hyp_eq in eq _ x return is_suc x with
    | eq_refl => I
    end
  .

  Definition suc_n_eq_zero_elim {A : Type} {n : nat} (hyp_eq : S n = 0) : A :=
    False_rect A (not_S_n_eq_0 hyp_eq)
  .

  Definition suc_n_eq_suc_m_elim {n : nat} {m : nat} (hyp_eq : S n = S m) : n = m :=
    eq_congruence Nat.pred (S n) (S m) hyp_eq
  .

  Definition not_S_n_le_0 {n : nat} (hyp_le : S n <= 0) : False :=
    match hyp_le in le _ x return is_suc x with
    | le_n _ => I
    | le_S _ m' hyp_lt' => I
    end
  .

  Definition lt_elim_n_lt_0 {A : Type} {n : nat} (hyp_lt : n < 0) : A :=
    False_rect A (not_S_n_le_0 hyp_lt)
  .

  Definition suc_pred_n_eq_n_if_m_lt_n {n : nat} {m : nat} (hyp_lt : m < n) : S (pred n) = n :=
    match hyp_lt in le _ x return S (pred x) = x with
    | le_n _ => eq_reflexivity (S m)
    | le_S _ n' hyp_lt' => eq_reflexivity (S n')
    end
  .

  Fixpoint n_le_pred_m_if_n_lt_m {n : nat} {m : nat} (hyp_le : S n <= m) {struct hyp_le} : n <= pred m :=
    match hyp_le in le _ x return n <= pred x with
    | le_n _ => le_n n
    | le_S _ m' hyp_le' => eq_ind (S (pred m')) (le n) (le_S n (pred m') (n_le_pred_m_if_n_lt_m hyp_le')) m' (suc_pred_n_eq_n_if_m_lt_n hyp_le')
    end
  .

  Definition lt_elim_n_lt_S_m {n : nat} {m : nat} (hyp_lt : n < S m) : n <= m :=
    n_le_pred_m_if_n_lt_m hyp_lt
  .

  Definition le_reflexivity {n1 : nat} : n1 <= n1 := le_n n1.

  Fixpoint le_transitivity {n1 : nat} {n2 : nat} {n3 : nat} (hyp1 : n1 <= n2) {struct hyp1} : n2 <= n3 -> n1 <= n3 :=
    match hyp1 in le _ x return x <= n3 -> n1 <= n3 with
    | le_n _ => fun hyp2 : n1 <= n3 => hyp2
    | le_S _ n2' hyp1' => fun hyp2 : n2' < n3 => le_transitivity hyp1' (eq_ind (S (pred n3)) (fun x : nat => n2' <= x) (le_S n2' (pred n3) (n_le_pred_m_if_n_lt_m hyp2)) n3 (suc_pred_n_eq_n_if_m_lt_n hyp2))
    end
  .

  Fixpoint le_antisymmetry {n1 : nat} {n2 : nat} {struct n1} : n1 <= n2 -> n1 >= n2 -> n1 = n2 :=
    match n1 as x, n2 as y return x <= y -> y <= x -> x = y with
    | O, O => fun hyp1 : O <= O => fun hyp2 : O <= O => eq_reflexivity 0
    | O, S n2' => fun hyp1 : O <= S n2' => fun hyp2 : S n2' <= O => lt_elim_n_lt_0 hyp2
    | S n1', O => fun hyp1 : S n1' <= O => fun hyp2 : O <= S n1' => lt_elim_n_lt_0 hyp1
    | S n1', S n2' => fun hyp1 : n1' < S n2' => fun hyp2 : n2' < S n1' => eq_congruence S n1' n2' (le_antisymmetry (lt_elim_n_lt_S_m hyp1) (lt_elim_n_lt_S_m hyp2))
    end
  .

  Fixpoint le_intro_S_n_le_S_m {n : nat} {m : nat} (hyp_LE : n <= m) {struct hyp_LE} : S n <= S m :=
    match hyp_LE in le _ x return le (S n) (S x) with
    | le_n _ => le_n (S n)
    | le_S _ m' hyp_LE' => le_S (S n) (S m') (le_intro_S_n_le_S_m hyp_LE')
    end
  .

  Fixpoint le_intro_0_le_n {n : nat} {struct n} : 0 <= n :=
    match n with
    | O => le_n O
    | S n' => le_S O n' le_intro_0_le_n
    end
  .

  Fixpoint not_n_lt_n (n : nat) {struct n} : ~ n < n :=
    match n with
    | O => lt_elim_n_lt_0
    | S n' => fun hyp_lt : S n' < S n' => not_n_lt_n n' (lt_elim_n_lt_S_m hyp_lt)
    end
  .

  Fixpoint n1_le_max_n1_n2 (n1 : nat) (n2 : nat) {struct n1} : n1 <= max n1 n2 :=
    match n1 as n return n <= max n n2 with
    | O => le_intro_0_le_n
    | S n1' =>
      match n2 as m return S n1' <= max (S n1') m with
      | O => le_n (S n1')
      | S n2' => le_intro_S_n_le_S_m (n1_le_max_n1_n2 n1' n2')
      end
    end
  .

  Fixpoint n2_le_max_n1_n2 (n1 : nat) (n2 : nat) {struct n1} : n2 <= max n1 n2 :=
    match n1 as n return n2 <= max n n2 with
    | O => le_n n2
    | S n1' =>
      match n2 as m return m <= max (S n1') m with
      | O => le_intro_0_le_n
      | S n2' => le_intro_S_n_le_S_m (n2_le_max_n1_n2 n1' n2')
      end
    end
  .

  Fixpoint le_intro_plus_l (n1 : nat) (n2 : nat) {struct n1} : n1 <= n1 + n2 :=
    match n1 with
    | O => le_intro_0_le_n
    | S n1' => le_intro_S_n_le_S_m (le_intro_plus_l n1' n2)
    end
  .

  Fixpoint le_intro_plus_r (n1 : nat) (n2 : nat) {struct n1} : n2 <= n1 + n2 :=
    match n1 with
    | O => le_reflexivity
    | S n1' => le_transitivity (le_intro_plus_r n1' n2) (le_S (n1' + n2) (n1' + n2) le_reflexivity)
    end
  .

  Definition le_elim_max_n1_n2_le_m (n1 : nat) (n2 : nat) (m : nat) (hyp_le : max n1 n2 <= m) : n1 <= m /\ n2 <= m :=
    @conj _ _ (le_transitivity (n1_le_max_n1_n2 n1 n2) hyp_le) (le_transitivity (n2_le_max_n1_n2 n1 n2) hyp_le)
  .

  Lemma le_unfold {n : nat} {m : nat} :
    n <= m <->
    match m with
    | O => n = 0
    | S m' => n = S m' \/ n <= m'
    end.
  Proof.
    split; destruct m as [ | m'].
    - intros hyp_le.
      exact (le_antisymmetry hyp_le le_intro_0_le_n).
    - intros hyp_le.
      exact (
        match hyp_le in le _ x return n = x \/ n <= Nat.pred x with
        | le_n _ => or_introl (eq_reflexivity n)
        | le_S _ m' hyp_le' => or_intror hyp_le'
        end
      ).
    - exact (eq_ind n (le n) (le_n n) 0).
    - intros [hyp_eq | hyp_le].
      + exact (eq_ind n (le n) (le_n n) (suc m') hyp_eq).
      + exact (le_S n m' hyp_le).
  Qed.

  Global Instance natEqDec : EqDec nat :=
    { eq_dec :=
      fix eq_dec_fix (n1 : nat) (n2 : nat) {struct n1} : {n1 = n2} + {n1 <> n2} :=
      match n1 as x, n2 as y return {x = y} + {x <> y} with
      | O, O => left (eq_reflexivity O)
      | O, S n2' => right (fun h_eq : O = S n2' => suc_n_eq_zero_elim (eq_symmetry O (S n2') h_eq))
      | S n1', O => right (fun h_eq : S n1' = O => suc_n_eq_zero_elim h_eq)
      | S n1', S n2' =>
        match eq_dec_fix n1' n2' with
        | left h_eq => left (eq_congruence S n1' n2' h_eq)
        | right h_ne => right (fun h_eq : S n1' = S n2' => h_ne (suc_n_eq_suc_m_elim h_eq))
        end
      end
    }
  .

  Theorem le_pirrel {n1 : nat} {n2 : nat}
    (hyp1 : n1 <= n2)
    (hyp2 : n1 <= n2)
    : hyp1 = hyp2.
  Proof.
    revert n2 hyp1 hyp2.
    refine (
      fix le_pirrel_fix (n2 : nat) (hyp1 : n1 <= n2) {struct hyp1} : forall hyp2 : n1 <= n2, hyp1 = hyp2 :=
      match hyp1 as hyp1' in le _ n2' return forall hyp2 : n1 <= n2', hyp1' = hyp2 with
      | le_n _ => fun hyp2 : n1 <= n1 => _
      | le_S _ n1' hyp1' => fun hyp2 : n1 <= S n1' => _
      end
    ).
    { memo (
        match hyp2 as hyp2' in le _ n2' return forall h_eq : n1 = n2', eq_ind n1 (le n1) (le_n n1) n2' h_eq = hyp2' with
        | le_n _ => _
        | le_S _ n2' hyp2' => _
        end
      ) as claim1.
      - exact (claim1 (eq_reflexivity n1)).
      - intros h_eq.
        rewrite eq_pirrel_fromEqDec with (hyp_eq1 := h_eq) (hyp_eq2 := eq_reflexivity n1).
        exact (eq_reflexivity (le_n n1)).
      - intros h_eq. contradiction (not_n_lt_n n2').
        unfold "<". now rewrite <- h_eq.
    }
    { memo (
        match hyp2 as hyp2' in le _ n2' return forall h_eq : n2' = S n1', le_S n1 n1' hyp1' = eq_ind n2' (le n1) hyp2' (S n1') h_eq with
        | le_n _ => _
        | le_S _ n2' hyp2' => _
        end
      ) as claim2.
      - exact (claim2 (eq_reflexivity (S n1'))).
      - intros h_eq. contradiction (not_n_lt_n n1').
        unfold "<". now rewrite <- h_eq.
      - intros h_eq.
        pose proof (suc_n_eq_suc_m_elim h_eq) as hyp_eq; subst n2'.
        rewrite eq_pirrel_fromEqDec with (hyp_eq1 := h_eq) (hyp_eq2 := eq_reflexivity (S n1')).
        exact (eq_congruence (le_S n1 n1') hyp1' hyp2' (le_pirrel_fix n1' hyp1' hyp2')).
    }
  Qed.

  Fixpoint le_gt_False {n : nat} {m : nat} (hyp_le : n <= m) {struct hyp_le} : ~ n > m :=
    match hyp_le in le _ m' return n > m' -> False with
    | le_n _ => not_n_lt_n n
    | le_S _ m' hyp_le' => fun hyp_gt : n > S m' => le_gt_False hyp_le' (le_transitivity (le_S (S m') (S m') (le_n (S m'))) hyp_gt)
    end
  .

  Theorem lt_strong_ind {phi : nat -> Prop}
    (IND : forall n : nat, << IH : forall m : nat, m < n -> phi m >> -> phi n)
    : forall n : nat, phi n.
  Proof.
    unnw. intros n. eapply IND with (n := n). induction n as [ | n IH].
    - intros m. exact (@lt_elim_n_lt_0 (phi m) m).
    - intros m hyp_m_lt_S_n. eapply IND with (n := m).
      intros i hyp_i_lt_m. eapply IH with (m := i). exact (le_transitivity hyp_i_lt_m (lt_elim_n_lt_S_m hyp_m_lt_S_n)).
  Defined.

  Fixpoint n_le_m_or_m_lt_n_holds_for_any_n_and_any_m (n : nat) (m : nat) {struct n} : {n <= m} + {m < n} :=
    match n as x return {x <= m} + {m < x} with
    | zero => left le_intro_0_le_n
    | suc n' =>
      match m as y return {suc n' <= y} + {y < suc n'} with
      | zero => right (le_intro_S_n_le_S_m le_intro_0_le_n)
      | suc m' =>
        match n_le_m_or_m_lt_n_holds_for_any_n_and_any_m n' m' with
        | left hyp_le => left (le_intro_S_n_le_S_m hyp_le)
        | right hyp_lt => right (le_intro_S_n_le_S_m hyp_lt)
        end
      end
    end
  .

(** "Set-level le" *)

  Inductive Le (n : nat) : nat -> Set :=
  | Le_n : Le n n
  | Le_S (m : nat) (hyp_Le : Le n m) : Le n (S m)
  .

  Fixpoint Le_intro_0_le_n {n : nat} {struct n} : Le 0 n :=
    match n with
    | O => Le_n O
    | S n' => Le_S O n' Le_intro_0_le_n
    end
  .

  Fixpoint Le_intro_S_n_le_S_m {n : nat} {m : nat} (hyp_LE : Le n m) {struct hyp_LE} : Le (S n) (S m) :=
    match hyp_LE in Le _ x return Le (S n) (S x) with
    | Le_n _ => Le_n (S n)
    | Le_S _ m' hyp_LE' => Le_S (S n) (S m') (Le_intro_S_n_le_S_m hyp_LE')
    end
  .

  Fixpoint le_implies_Le {n : nat} {m : nat} {struct n} : le n m -> Le n m :=
    match n as x return le x m -> Le x m with
    | O => fun hyp_le : O <= m => Le_intro_0_le_n
    | S n' =>
      match m as y return le (S n') y -> Le (S n') y with
      | O => fun hyp_le : n' < O => lt_elim_n_lt_0 hyp_le
      | S m' => fun hyp_le : n' < S m' => Le_intro_S_n_le_S_m (le_implies_Le (lt_elim_n_lt_S_m hyp_le))
      end
    end
  .

  Fixpoint Le_implies_le {n : nat} {m : nat} (hyp_le : Le n m) {struct hyp_le} : le n m :=
    match hyp_le with
    | Le_n _ => le_n n
    | Le_S _ m' hyp_le' => le_S n m' (Le_implies_le hyp_le')
    end
  .

End NAT_FACTS.

Export NAT_FACTS.

Module MyData.

  Global Declare Scope vector_scope.

  Inductive Fin : nat -> Set :=
  | FZ {n : nat} : Fin (S n)
  | FS {n : nat} (i : Fin n) : Fin (S n)
  .

  Lemma Fin_case0 {phi : Fin (O) -> Type} 
    : forall i : Fin (O), phi i.
  Proof.
    keep (fun m : nat =>
      match m as x return Fin x -> Type with
      | O => fun i : Fin (O) => forall phi' : Fin (O) -> Type, phi' i
      | S m' => fun i : Fin (S m') => unit
      end
    ) as ret into (forall x : nat, Fin x -> Type).
    intros i.
    memo (
      match i as this in Fin x return ret x this with
      | @FZ n' => _
      | @FS n' i' => _
      end
    ) as claim1.
    - exact (claim1 phi).
    - exact (tt).
    - exact (tt).
  Defined.

  Lemma Fin_caseS {n : nat} {phi : Fin (S n) -> Type}
    (hypZ : phi FZ)
    (hypS : forall i' : Fin n, phi (FS i'))
    : forall i : Fin (S n), phi i.
  Proof.
    keep (fun m : nat =>
      match m as x return Fin x -> Type with
      | O => fun i : Fin (O) => unit
      | S m' => fun i : Fin (S m') => forall phi' : Fin (S m') -> Type, phi' (@FZ m') -> (forall i' : Fin m', phi' (@FS m' i')) -> phi' i
      end
    ) as ret into (forall x : nat, Fin x -> Type).
    intros i.
    memo (
      match i as this in Fin x return ret x this with
      | @FZ n' => _
      | @FS n' i' => _
      end
    ) as claim1.
    - exact (claim1 phi hypZ hypS).
    - intros phi' hypZ' hypS'; exact (hypZ').
    - intros phi' hypZ' hypS'; exact (hypS' i').
  Defined.

  Global Tactic Notation "introFin0" := intro_pattern_revert; eapply Fin_case0.
  Global Tactic Notation "introFinS" ident( i' ) := intro_pattern_revert; eapply Fin_caseS; [ | intros i'].

  Lemma Fin_eq_dec (n : nat)
    : forall i1 : Fin n, forall i2 : Fin n, {i1 = i2} + {i1 <> i2}.
  Proof.
    induction n as [ | n IH]; [introFin0 | introFinS i1'; introFinS i2'].
    - left; reflexivity.
    - right; congruence.
    - right; congruence.
    - destruct (IH i1' i2') as [hyp_yes | hyp_no]; [left | right].
      + exact (eq_congruence (@FS n) i1' i2' hyp_yes).
      + intros hyp_eq.
        keep (fun i : Fin (S n) =>
          match i in Fin m return Fin (pred m) -> Fin (pred m) with
          | @FZ n' => fun d : Fin n' => d
          | @FS n' i' => fun d : Fin n' => i'
          end
        ) as cool_idea into (Fin (S n) -> Fin n -> Fin n).
        exact (hyp_no (eq_congruence2 cool_idea (FS i1') (FS i2') hyp_eq i1' i1' (eq_reflexivity i1'))).
  Defined.

  Global Instance FinEqDec (n : nat) : EqDec (Fin n) := { eq_dec := Fin_eq_dec n }.

  Definition fin (n : nat) : Set := @sig nat (gt n).

  Fixpoint runFin {n : nat} (i : Fin n) {struct i} : fin n :=
    match i in Fin x return @sig nat (gt x) with
    | @FZ n' => @exist nat (gt (S n')) O (le_intro_S_n_le_S_m le_intro_0_le_n)
    | @FS n' i' => @exist nat (gt (S n')) (S (proj1_sig (runFin i'))) (le_intro_S_n_le_S_m (proj2_sig (runFin i')))
    end
  .

  Fixpoint getFin {n : nat} (m : nat) {struct n} : m < n -> Fin n :=
    match n as x return S m <= x -> Fin x with
    | O => lt_elim_n_lt_0
    | S n' =>
      match m as y return S y <= S n' -> Fin (S n') with
      | O => fun hyp_lt : O < S n' => FZ
      | S m' => fun hyp_lt : S m' < S n' => FS (getFin m' (lt_elim_n_lt_S_m hyp_lt))
      end
    end
  .

  Lemma runFin_getFin_id {m : nat} {n : nat} (hyp_lt : m < n)
    : runFin (getFin m hyp_lt) = exist (gt n) m hyp_lt.
  Proof.
    revert n hyp_lt. induction m as [ | m IH]; intros [ | n'] hyp_lt; cbn in *.
    - exact (lt_elim_n_lt_0 hyp_lt).
    - eapply eq_congruence, le_pirrel.
    - exact (lt_elim_n_lt_0 hyp_lt).
    - rewrite IH; cbn. eapply eq_congruence, le_pirrel.
  Qed.

  Lemma getFin_runFin_id {n : nat} (i : Fin n)
    : getFin (proj1_sig (runFin i)) (proj2_sig (runFin i)) = i.
  Proof.
    induction i as [n' | n' i' IH].
    - reflexivity.
    - cbn. eapply eq_congruence. etransitivity; [eapply eq_congruence, le_pirrel | exact (IH)].
  Qed.

  Global Instance Fin_equipotent_fin (n : nat)
    : Equipotent (Fin n) (fin n).
  Proof.
    exists (@runFin n).
    - intros i1 i2 hyp_eq. desnw; unnw.
      rewrite <- getFin_runFin_id with (i := i1).
      rewrite <- getFin_runFin_id with (i := i2).
      rewrite f_x1_eq_f_x2.
      reflexivity.
    - intros [m hyp_lt]. unnw.
      exists (@getFin n m hyp_lt).
      rewrite runFin_getFin_id with (hyp_lt := hyp_lt).
      reflexivity.
  Defined.

  Section LIST.

  Definition safe_nth {A : Type} : forall xs : list A, Fin (length xs) -> A :=
    fix safe_nth_fix (xs : list A) {struct xs} : Fin (length xs) -> A :=
    match xs as this return Fin (length this) -> A with
    | nil => Fin_case0
    | cons x xs => Fin_caseS x (safe_nth_fix xs)
    end
  .

  Lemma list_liftsEqDec {A : Type}
    (requiresEqDec : EqDec A)
    : EqDec (list A).
  Proof with try ((left; congruence) || (right; congruence)).
    change (forall lhs : list A, forall rhs : list A, {lhs = rhs} + {lhs <> rhs}).
    induction lhs as [ | x1 xs1 IH], rhs as [ | x2 xs2]...
    pose proof (requiresEqDec x1 x2) as [ | ]; pose proof (IH xs2) as [ | ]...
  Defined.

  End LIST.

  Section VECTOR.

  Variable A : Type.

  Inductive vector : nat -> Type :=
  | VNil : vector (O)
  | VCons (n : nat) (x : A) (xs : vector n) : vector (S n)
  .

  Definition vector_casting {n : nat} {m : nat} (hyp_eq : n = m) : vector n -> vector m :=
    match hyp_eq in eq _ m' return vector n -> vector m' with
    | eq_refl => fun xs : vector n => xs
    end
  .

  Lemma vector_case0 (phi : vector (O) -> Type)
    (hypNil : phi VNil)
    : forall xs : vector (O), phi xs.
  Proof.
    memo (fun xs : vector (O) =>
      match xs as this in vector m return forall hyp_eq : m = O, phi (vector_casting hyp_eq this) with
      | VNil => fun hyp_eq : O = O => _
      | VCons n' x' xs' => fun hyp_eq : S n' = O => _
      end
    ) as claim1.
    - intros xs. exact (claim1 xs (eq_reflexivity (O))).
    - rewrite eq_pirrel_fromEqDec with (hyp_eq1 := hyp_eq) (hyp_eq2 := eq_reflexivity (O)).
      exact (hypNil).
    - exact (suc_n_eq_zero_elim hyp_eq).
  Defined.

  Lemma vector_caseS (n : nat) (phi : vector (S n) -> Type)
    (hypCons : forall x : A, forall xs : vector n, phi (VCons n x xs))
    : forall xs : vector (S n), phi xs.
  Proof.
    memo (fun xs : vector (S n) =>
      match xs as this in vector m return forall hyp_eq : m = S n, phi (vector_casting hyp_eq this) with
      | VNil => fun hyp_eq : O = S n => _
      | VCons n' x' xs' => fun hyp_eq : S n' = S n => _
      end
    ) as claim1.
    - intros xs. exact (claim1 xs (eq_reflexivity (S n))).
    - exact (suc_n_eq_zero_elim (eq_symmetry O (S n) hyp_eq)).
    - pose proof (suc_n_eq_suc_m_elim hyp_eq) as n_eq_n'; subst n'.
      rewrite eq_pirrel_fromEqDec with (hyp_eq1 := hyp_eq) (hyp_eq2 := eq_reflexivity (S n)).
      exact (hypCons x' xs').
  Defined.

  Definition vector_uncons {n : nat} (xs : vector (S n)) : S n = S n -> A * vector n :=
    match xs in vector m return S n = m -> A * vector (pred m) with
    | VNil => suc_n_eq_zero_elim
    | VCons n' x' xs' => fun _ : S n = S n' => (x', xs')
    end
  .

  End VECTOR.

  Global Arguments VNil {A}.
  Global Arguments VCons {A}.
  Global Arguments vector_casting {A} {n} {m} (hyp_eq).
  Global Arguments vector_case0 {A} {phi} (hypNil).
  Global Arguments vector_caseS {A} {n} {phi} (hypCons).
  Global Arguments vector_uncons {A} {n}.

  Global Tactic Notation "introVNil" := intro_pattern_revert; eapply vector_case0.
  Global Tactic Notation "introVCons" ident( HEAD ) ident( TAIL ) := intro_pattern_revert; eapply vector_caseS; intros HEAD TAIL.

  Definition vector_head {A : Type} {n : nat} (xs : vector A (S n)) : A := fst (vector_uncons xs (eq_reflexivity (S n))).

  Definition vector_tail {A : Type} {n : nat} (xs : vector A (S n)) : vector A n := snd (vector_uncons xs (eq_reflexivity (S n))).

  Global Bind Scope vector_scope with vector.

  Global Notation " '[' ']' " := (@VNil _) : vector_scope.
  Global Notation " x '::' xs " := (@VCons _ _ x xs) : vector_scope.

End MyData.

Export MyData.

Module MyUtil.

  Section NAT_ARITH.

  Lemma greater_than_iff (x : nat) (y : nat)
    : x > y <-> (exists z : nat, x = S (y + z)).
  Proof with try (lia || eauto).
    split.
    - intros Hgt. induction Hgt as [ | m Hgt [z x_eq]]; [exists (0) | rewrite x_eq]...
    - intros [z Heq]...
  Qed.

  Lemma div_mod_uniqueness a b q r
    (H_DIVISION : a = b * q + r)
    (r_lt_b : r < b)
    : (a / b = q /\ a mod b = r)%nat.
  Proof with try (lia || now (firstorder; eauto)).
    assert (claim1 : a = b * (a / b) + (a mod b)) by now eapply (Nat.div_mod a b); lia.
    assert (claim2 : 0 <= a mod b /\ a mod b < b) by now eapply (Nat.mod_bound_pos a b); lia.
    assert (claim3 : ~ q > a / b).
    { intros H_false. destruct (proj1 (greater_than_iff q (a / b)) H_false) as [z q_eq].
      enough (so_we_obatain : b * q + r >= b * S (a / b) + r)...
    }
    assert (claim4 : ~ q < a / b).
    { intros H_false. destruct (proj1 (greater_than_iff (a / b) q) H_false) as [z a_div_b_eq].
      enough (so_we_obtain : b * q + a mod b >= b * S (a / b) + a mod b)...
    }
    enough (therefore : q = a / b)...
  Qed.

  Theorem div_mod_inv a b q r (H_b_ne_0 : b <> 0)
    : (a = b * q + r /\ r < b)%nat <-> (q = (a - r) / b /\ r = a mod b /\ a >= r)%nat.
  Proof with lia || eauto.
    pose proof (lemma1 := Nat.div_mod). pose proof (lemma2 := greater_than_iff). split.
    - intros [H_a H_r_bound].
      assert (claim1 : a = b * (a / b) + (a mod b))...
      assert (claim2 : 0 <= a mod b /\ a mod b < b). 
      { eapply (Nat.mod_bound_pos a b)... }
      assert (claim3 : a >= r)...
      enough (claim4 : ~ q > a / b). enough (claim5 : ~ q < a / b). enough (claim6 : q = a / b)...
      + split... replace (a - r) with (q * b)... symmetry; eapply Nat.div_mul...
      + intros H_false. destruct (proj1 (lemma2 (a / b) q) H_false) as [x Hx]...
      + intros H_false. destruct (proj1 (lemma2 q (a / b)) H_false) as [x Hx]...
    - intros [H_q [H_r H_a_ge_r]].
      pose proof (claim1 := Nat.mod_bound_pos a b). split...
      assert (claim2 : r < b)... assert (claim3 := Nat.div_mod a b H_b_ne_0).
      rewrite <- H_r in claim3. enough (claim4 : q = a / b)...
      rewrite H_q; symmetry. eapply Nat.div_unique with (r := 0)...
  Qed.

  Lemma positive_odd n_odd n
    : (n_odd = 2 * n + 1)%nat <-> (n = (n_odd - 1) / 2 /\ n_odd mod 2 = 1 /\ n_odd > 0)%nat.
  Proof with lia || eauto.
    pose proof (claim1 := div_mod_inv n_odd 2 n 1)...
  Qed.

  Lemma positive_even n_even n
    : (n_even = 2 * n + 2)%nat <-> (n = (n_even - 2) / 2 /\ n_even mod 2 = 0 /\ n_even > 0)%nat.
  Proof with lia || eauto.
    pose proof (claim1 := div_mod_inv (n_even - 2) 2 n 0). split.
    - intros ?; subst.
      assert (claim2 : n = (2 * n + 2 - 2 - 0) / 2 /\ 0 = (2 * n + 2 - 2) mod 2 /\ 2 * n + 2 - 2 >= 0)...
      split. rewrite (proj1 claim2) at 1. replace (2 * n + 2 - 2 - 0) with (2 * n + 2 - 2)...
      split... replace (2 * n + 2) with (2 + n * 2)... rewrite Nat.mod_add...
    - intros [H_n [H_r H_gt_0]].
      assert (claim2 : n_even >= 2).
      { destruct n_even as [ | [ | n_even]]... inversion H_r. }
      assert (claim3 : n_even = 2 * (n_even / 2) + n_even mod 2).
      { eapply Nat.div_mod... }
      enough (claim4 : (n_even - 2) mod 2 = 0).
      + assert (claim5 : n_even - 2 = 2 * n + 0 /\ 0 < 2)...
        rewrite H_r, Nat.add_0_r in claim3. eapply claim1...
        replace (n_even - 2 - 0) with (n_even - 2)...
      + transitivity (n_even mod 2)...
        symmetry; replace (n_even) with ((n_even - 2) + 1 * 2) at 1...
        eapply Nat.mod_add...
  Qed.

  Lemma plus_a_b_divmod_b a b (H_b_ne_0 : b <> 0)
    : ((a + b) / b = (a / b) + 1)%nat /\ ((a + b) mod b = a mod b)%nat.
  Proof with try lia.
    eapply (div_mod_uniqueness (a + b) b ((a / b) + 1) (a mod b)).
    - replace (b * (a / b + 1) + a mod b) with ((b * (a / b) + a mod b) + b)...
      enough (claim1 : a = b * (a / b) + a mod b) by congruence.
      exact (Nat.div_mod a b H_b_ne_0).
    - assert (claim2 : b > 0)...
      exact (proj2 (Nat.mod_bound_pos a b le_intro_0_le_n claim2)).
  Qed.

  Lemma n_div_b_lt_n_if_b_gt_1_and_n_ge_1 (n : nat) (b : nat)
    (H_b_gt_1 : b > 1)
    (H_n_ge_1 : n >= 1)
    : n / b < n.
  Proof with try lia.
    assert (claim1 : b <> 0)...
    pose proof (claim2 := Nat.mod_bound_pos n b le_intro_0_le_n (le_transitivity (le_S 1 1 (le_n 1)) H_b_gt_1)).
    pose proof (claim3 := Nat.div_mod n b claim1).
    enough (it_is_sufficient_to_show : n / b < b * (n / b) + n mod b)...
    assert (claim4 : n mod b > 0 \/ n mod b = 0)...
    pose proof (claim5 := suc_pred_n_eq_n_if_m_lt_n H_b_gt_1).
    assert (claim6 : n / b > 0 \/ n / b = 0)...
  Qed.

  Lemma n_div_b_ge_1_if_n_ge_b_and_b_ge_1 (n : nat) (b : nat)
    (H_n_ge_b : n >= b)
    (H_b_ge_1 : b >= 1)
    : n / b >= 1.
  Proof with try lia.
    assert (claim1 : b <> 0)...
    pose proof (claim2 := Nat.div_mod n b claim1).
    assert (claim3 : b * (n / b) + n mod b >= b)...
    pose proof (claim4 := Nat.mod_bound_pos n b (@le_intro_0_le_n n) H_b_ge_1).
    assert (therefore : b * (n / b) + b > b)...
  Qed.

  End NAT_ARITH.

  Definition first_nat (p : nat -> bool) : nat -> nat :=
    fix first_nat_fix (n : nat) {struct n} : nat :=
    match n with
    | O => 0
    | S n' => if p (first_nat_fix n') then first_nat_fix n' else 1 + n'
    end
  .

  Theorem well_ordering_principle (p : nat -> bool) (n : nat)
    (WITNESS : p n = true)
    : p (first_nat p n) = true /\ (forall i : nat, p i = true -> i >= first_nat p n).
  Proof with eauto. (* This proof has been improved by Junyoung Clare Jang. *)
    set (m := first_nat p n).
    assert (claim1 : forall x : nat, p x = true -> p (first_nat p x) = true).
    { induction x as [ | x IH]... simpl. destruct (p (first_nat p x)) as [ | ] eqn: ?... }
    split... intros i p_i_eq_true.
    enough (claim2 : forall x : nat, first_nat p x <= x).
    enough (claim3 : forall x : nat, p (first_nat p x) = true -> (forall y : nat, x < y -> first_nat p x = first_nat p y)).
    enough (claim4 : forall x : nat, forall y : nat, p y = true -> first_nat p x <= y)...
    - intros x y p_y_eq_true. destruct (le_gt_dec x y) as [x_le_y | x_gt_y].
      + eapply Nat.le_trans...
      + replace (first_nat p x) with (first_nat p y)...
    - intros x p_first_nat_p_x_eq_true y x_gt_y. induction x_gt_y as [ | y x_gt_y IH]; simpl.
      + rewrite p_first_nat_p_x_eq_true...
      + rewrite <- IH, p_first_nat_p_x_eq_true...
    - induction x as [ | x IH]... simpl.
      destruct (p (first_nat p x)) as [ | ]...
  Qed.

  Fixpoint sum_from_0_to (n : nat) {struct n} : nat :=
    match n with
    | O => 0
    | S n' => n + sum_from_0_to n'
    end
  .

  Lemma sum_from_0_to_is n
    : 2 * sum_from_0_to n = n * (S n).
  Proof. induction n; simpl in *; lia. Qed.

  Fixpoint cantor_pairing (n : nat) {struct n} : nat * nat :=
    match n with
    | O => (0, 0)
    | S n' =>
      match cantor_pairing n' with
      | (O, y) => (S y, 0)
      | (S x, y) => (x, S y)
      end
    end
  .

  Lemma cantor_pairing_is_surjective x y
    : (x, y) = cantor_pairing (sum_from_0_to (x + y) + y).
  Proof with (lia || eauto).
    remember (x + y) as z eqn: z_is; revert y x z_is.
    induction z as [ | z IH].
    - ii. replace (x) with (0)... replace (y) with (0)...
    - induction y as [ | y IHy]; ii.
      + assert (x_is_S_z : x = S z) by lia. subst x; simpl.
        destruct (cantor_pairing (z + sum_from_0_to z + 0)) as [x y] eqn: H_eqn.
        assert (claim3 : (0, z) = cantor_pairing (sum_from_0_to z + z))...
        rewrite Nat.add_0_r, Nat.add_comm in H_eqn.
        rewrite H_eqn in claim3. inversion claim3; subst...
      + assert (claim4 : (S x, y) = cantor_pairing (sum_from_0_to (S z) + y)) by now eapply (IHy (S x)); lia.
        assert (claim5 : z + sum_from_0_to z + S y = sum_from_0_to (S z) + y) by now simpl.
        simpl. rewrite claim5, <- claim4...
  Qed.

  Lemma cantor_pairing_is_injective n x y
    (H_eq : cantor_pairing n = (x, y))
    : n = sum_from_0_to (x + y) + y.
  Proof with (lia || eauto).
    revert x y H_eq. induction n as [ | n IH]; simpl; ii.
    - inversion H_eq; subst...
    - destruct (cantor_pairing n) as [[ | x'] y'] eqn: H_eqn; inversion H_eq; subst.
      + do 2 rewrite Nat.add_0_r. simpl.
        rewrite IH with (x := 0) (y := y')...
        rewrite Nat.add_0_l...
      + assert (claim1 : forall x' : nat, S x' + y' = x' + S y')...
        rewrite IH with (x := S x) (y := y')... rewrite claim1 with (x' := x)...
  Qed.

  Definition cantor_pairing_inv (x : nat) (y : nat) : nat := sum_from_0_to (x + y) + y.

  Theorem cantor_pairing_spec n x y
    : cantor_pairing n = (x, y) <-> n = cantor_pairing_inv x y.
  Proof.
    split.
    - exact (cantor_pairing_is_injective n x y).
    - intros Heq. subst n. symmetry.
      exact (cantor_pairing_is_surjective x y).
  Qed.

  Definition pair_enum {fsts : Type} {snds : Type} {fsts_requiresCountable : isCountable fsts} {snds_requiresCountable : isCountable snds} (n : nat) : fsts * snds :=
    let '(a, b) := cantor_pairing n in (enum a, enum b)
  .

  Lemma pair_enum_isSurjective {fsts : Type} {snds : Type} {fsts_requiresCountable : isCountable fsts} {snds_requiresCountable : isCountable snds}
    : isSurjective (cod := (fsts * snds)%type) pair_enum.
  Proof.
    intros [x y]. exploit (enum_isSurjective x) as [a x_is_enum_a]. exploit (enum_isSurjective y) as [b y_is_enum_b].
    exists (cantor_pairing_inv a b). unnw. subst x y. remember (cantor_pairing_inv a b) as c eqn: c_is. rewrite <- cantor_pairing_spec in c_is.
    unfold pair_enum. rewrite c_is. reflexivity. 
  Qed.

  Global Instance pair_isCountable {fsts : Type} {snds : Type} (fsts_requiresCountable : isCountable fsts) (snds_requiresCountable : isCountable snds) : isCountable (fsts * snds)%type :=
    { enum := pair_enum
    ; enum_isSurjective := pair_enum_isSurjective
    }
  .

  Section LIST_ACCESSORIES.

  Import ListNotations.

  Lemma forallb_true_iff {A : Type} (p : A -> bool)
    : forall xs : list A, forallb p xs = true <-> (forall x : A, In x xs -> p x = true).
  Proof with try now firstorder.
    induction xs as [ | x xs IH]; simpl... rewrite andb_true_iff. split...
    intros [p_x_true forallb_p_xs_true] y [x_eq_y | y_in_xs]; [rewrite x_eq_y in p_x_true | eapply IH]...
  Qed.

  Definition maxs : list nat -> nat := fold_right max 0.

  Lemma maxs_in (ns : list nat) (n : nat) (H_IN : In n ns)
    : maxs ns >= n.
  Proof with (lia || eauto).
    unfold maxs. revert n H_IN. induction ns as [ | n' ns IH]; simpl...
    intros n [H_eq | H_in]... enough (H_suff : fold_right max 0 ns >= n)...
  Qed.

  Lemma maxs_app (ns1 : list nat) (ns2 : list nat)
    : maxs (ns1 ++ ns2) = max (maxs ns1) (maxs ns2).
  Proof with (lia || eauto).
    unfold maxs. revert ns2.
    induction ns1 as [ | n1 ns1 IH]; simpl... 
    intros n; rewrite IH...
  Qed.

  Lemma property1_of_maxs (phi : nat -> Prop) (ns : list nat)
    (phi_dec : forall i : nat, {phi i} + {~ phi i})
    (phi_implies_in : forall i : nat, phi i -> In i ns)
    : forall n : nat, phi n -> fold_right max 0 ns >= n.
  Proof with try now (lia || firstorder; eauto).
    induction ns as [ | n1 ns1 IH]; simpl... intros n phi_n.
    destruct (le_gt_dec n n1) as [H_le | H_gt]... enough (claim1 : fold_right max 0 ns1 >= n)...
    destruct (phi_dec n) as [H_yes | H_no]... destruct (phi_implies_in n H_yes)...
    enough (claim2 : forall ks : list nat, forall k : nat, In k ks -> fold_right max 0 ks >= k)...
    induction ks; simpl... intros k [H_eq | H_in]... enough (claim3 : fold_right Init.Nat.max 0 ks >= k)...
  Qed.

  Lemma property2_of_maxs (ns : list nat) (n : nat)
    : fold_right max 0 ns > n <-> (exists i : nat, In i ns /\ i > n).
  Proof with try now (lia || firstorder; eauto).
    revert n; induction ns as [ | n1 ns1 IH]; simpl... intros n.
    destruct (le_gt_dec n1 (fold_right Init.Nat.max 0 ns1)); split.
    - intros H_gt. assert (claim1 : fold_right Init.Nat.max 0 ns1 > n)...
    - intros [i [[H_eq | H_in] H_gt]]... enough (claim2 : fold_right max 0 ns1 > n)...
    - intros H_gt. exists (n1)...
    - intros [i [[H_eq | H_in] H_gt]]... enough (claim3 : fold_right Init.Nat.max 0 ns1 > n)...
  Qed.

  Lemma property3_of_maxs (ns1 : list nat) (ns2 : list nat)
    : fold_right max 0 (ns1 ++ ns2) = max (fold_right max 0 ns1) (fold_right max 0 ns2).
  Proof. exact (maxs_app ns1 ns2). Qed.

  Lemma property4_of_maxs (ns : list nat) (n : nat) (H_IN : In n ns)
    : fold_right max 0 ns >= n.
  Proof with try now (lia || firstorder; eauto).
    revert n H_IN; induction ns as [ | n ns IH]; simpl...
    intros m [H_eq | H_in]... enough (H_suff : fold_right max 0 ns >= m)...
  Qed.

  Lemma property5_of_maxs (ns1 : list nat) (ns2 : list nat)
    (H_SUBSET : forall n : nat, In n ns1 -> In n ns2)
    : fold_right max 0 ns1 <= fold_right max 0 ns2.
  Proof with try now (lia || firstorder; eauto).
    revert ns2 H_SUBSET; induction ns1 as [ | n1 ns1 IH]; simpl...
    intros ns2 H. destruct (le_gt_dec n1 (fold_right max 0 ns1)).
    - enough (H_suff : fold_right max 0 ns1 <= fold_right max 0 ns2)...
    - enough (H_suff : n1 <= fold_right max 0 ns2)... eapply property4_of_maxs...
  Qed.

  Lemma maxs_ext (ns1 : list nat) (ns2 : list nat)
    (H_EXT_EQ : forall n : nat, In n ns1 <-> In n ns2)
    : fold_right max 0 ns1 = fold_right max 0 ns2.
  Proof with try now firstorder.
    enough (claim1 : fold_right max 0 ns1 <= fold_right max 0 ns2 /\ fold_right max 0 ns2 <= fold_right max 0 ns1) by lia.
    split; eapply property5_of_maxs...
  Qed.

  Lemma in_remove_iff {A : Type} (x0 : A) (xs : list A)
    (requiresEqDec : forall x1 : A, forall x2 : A, {x1 = x2} + {x1 <> x2})
    : forall x : A, In x (remove requiresEqDec x0 xs) <-> (In x xs /\ x <> x0).
  Proof.
    pose proof (claim1 := in_remove requiresEqDec).
    pose proof (claim2 := in_in_remove requiresEqDec).
    now firstorder.
  Qed.

  Lemma fold_left_unfold {A : Type} {B : Type} (f : B -> A -> B) (z0 : B) (xs : list A) :
    fold_left f xs z0 =
    match xs with
    | [] => z0
    | hd_xs :: tl_xs => fold_left f tl_xs (f z0 hd_xs)
    end.
  Proof. destruct xs; reflexivity. Qed.

  Lemma fold_right_unfold {A : Type} {B : Type} (f : A -> B -> B) (z0 : B) (xs : list A) :
    fold_right f z0 xs =
    match xs with
    | [] => z0
    | hd_xs :: tl_xs => f hd_xs (fold_right f z0 tl_xs)
    end.
  Proof. destruct xs; reflexivity. Qed.

  Definition elemIndex_In {A : Type} (x : A) (x_eq_dec : forall y : A, {x = y} + {x <> y}) : forall xs : list A, In x xs -> nat :=
    fix elemIndex_In_fix (xs : list A) {struct xs} : In x xs -> nat :=
    match xs as xs0 return In x xs0 -> nat with
    | [] => False_rec nat
    | x' :: xs' =>
      fun H_In : x' = x \/ In x xs' =>
      match x_eq_dec x' with
      | left H_yes => 0
      | right H_no =>
        let H_In' : In x xs' := or_ind (fun H : x' = x => False_ind (In x xs') (H_no (eq_symmetry x' x H))) (fun H : In x xs' => H) H_In in
        1 + elemIndex_In_fix xs' H_In'
      end
    end
  .

  Lemma elemIndex_In_nth_error {A : Type} (x : A) (x_eq_dec : forall y : A, {x = y} + {x <> y}) :
    forall xs : list A,
    forall H_In : In x xs,
    nth_error xs (elemIndex_In x x_eq_dec xs H_In) = Some x.
  Proof.
    induction xs as [ | x' xs' IH]; simpl.
    - contradiction.
    - intros [H_eq | H_In']; destruct (x_eq_dec x') as [H_yes | H_no].
      + now subst x'.
      + now contradiction H_no.
      + now subst x'.
      + exact (IH H_In').
  Qed.

  Definition elemIndex {A : Type} (x : A) (x_eq_dec : forall x' : A, {x = x'} + {x <> x'}) : forall xs : list A, option (Fin (length xs)) :=
    fix elemIndex_fix (xs : list A) {struct xs} : option (Fin (length xs)) :=
    match xs as xs0 return option (Fin (length xs0)) with
    | [] => None
    | x' :: xs' => if x_eq_dec x' then Some (@FZ (length xs')) else option_map (@FS (length xs')) (elemIndex_fix xs')
    end
  .

  Definition lookup {dom : Type} {cod : Type} {dom_requiresEqDec : EqDec dom} (x : dom) : list (dom * cod) -> option cod :=
    fix lookup_fix (zs : list (dom * cod)) {struct zs} : option cod :=
    match zs with
    | [] => None
    | z :: zs' => if eq_dec (EqDec := dom_requiresEqDec) x (fst z) then lookup_fix zs' else Some (snd z)
    end
  .

  End LIST_ACCESSORIES.

  Section OPTION_ACCESSORIES.

  Definition Some_inj {A : Type} (x : A) (y : A) : Some x = Some y -> x = y :=
    eq_congruence (maybe y id) (Some x) (Some y)
  .

  Definition Some_ne_None {A : Type} (x : A) : Some x <> None :=
    fun hyp_eq : Some x = None => @transport (option A) (maybe False (fun _ : A => True)) (Some x) None hyp_eq I
  .

  Definition fromJust {A : Type} (Some_x : option A) : Some_x <> None -> A :=
    match Some_x as Some_x0 return Some_x0 <> None -> A with
    | None => fun hyp_no : None <> None => False_rect A (hyp_no (eq_reflexivity None))
    | Some x => fun _ : Some x <> None => x
    end
  .

  Lemma fromJust_spec {A : Type} (Some_x : option A) (x : A)
    : Some_x = Some x <-> (exists hyp_no : Some_x <> None, x = fromJust Some_x hyp_no).
  Proof with contradiction || eauto.
    split.
    - intros H_yes. subst Some_x. exists (Some_ne_None x)...
    - intros [H_no H_eq]. subst x. destruct Some_x as [x | ]...
  Qed.

  End OPTION_ACCESSORIES.

(** "resolver" *)

  Ltac resolver1 :=
    simpl in *;
    first
    [ rewrite in_app_iff in *
    | rewrite in_remove_iff in *
    | rewrite orb_false_iff in *
    | rewrite forallb_app in *
    | rewrite andb_true_iff in *
    | rewrite orb_true_iff in *
    | rewrite negb_true_iff in *
    | rewrite andb_false_iff in *
    | rewrite negb_false_iff in *
    | rewrite Nat.eqb_eq in *
    | rewrite Nat.eqb_neq in *
    | rewrite forallb_true_iff in *
    | rewrite in_map_iff in *
    | rewrite not_true_iff_false in *
    | rewrite not_false_iff_true in *
    ]
  .

  Ltac resolver :=
    repeat resolver1; repeat (try intro; try resolver1; try now (subst; firstorder))
  .

End MyUtil.

Export MyUtil.

Module FUN_FACTS.

(** "Statements" *)

  Polymorphic Definition projT2_eq_STMT (A : Type) (B : A -> Type) (x : A) : Prop :=
    forall y1 : B x, forall y2 : B x, << PAIR_EQ : @existT A B x y1 = @existT A B x y2 >> -> y1 = y2
  .

  Polymorphic Definition axiomK_STMT (A : Type) (x : A) : Prop :=
    forall phi : x = x -> Prop, << phi_refl : phi (eq_reflexivity x) >> -> forall hyp_eq : x = x, phi hyp_eq
  .

  Polymorphic Definition eq_rect_eq_STMT (A : Type) (phi : A -> Type) (x : A) : Prop :=
    forall phi_x : phi x, forall hyp_eq : x = x, @eq_rect A x phi phi_x x hyp_eq = phi_x
  .

  Definition pirrel_STMT (phi : Prop) : Prop :=
    forall pf1 : phi, forall pf2 : phi, pf1 = pf2
  .

  Polymorphic Class isWellFounded (A : Type) : Type :=
    { wfRel (subtree : A) (tree : A) : Prop
    ; wfRel_well_founded (root : A) : Acc wfRel root
    }
  .

(** "Auxiliaries" *)

  Inductive BB : Prop := TrueBB | FalseBB.

  Record RETRACT (A : Prop) (B : Prop) : Prop :=
    { _i : A -> B
    ; _j : B -> A
    ; _inv : forall x : A, _j (_i x) = x
    }
  .

  Global Arguments _i {A} {B}.
  Global Arguments _j {A} {B}.
  Global Arguments _inv {A} {B}.

  Record RETRACT2 (A : Prop) (B : Prop) : Prop :=
    { _i2 : A -> B
    ; _j2 : B -> A
    ; _inv2 : RETRACT A B -> forall x : A, _j2 (_i2 x) = x
    }
  .

  Global Arguments _i2 {A} {B}.
  Global Arguments _j2 {A} {B}.
  Global Arguments _inv2 {A} {B}.

  Definition RETRACT_REFL (A : Prop) : RETRACT A A :=
    {| _i := fun x : A => x; _j := fun x : A => x; _inv := @eq_refl A |}
  .

  Local Hint Resolve _inv _inv2 RETRACT_REFL : core.

  Definition isMinimalNum (phi : nat -> Prop) (n : nat) : Prop :=
    phi n /\ (forall m : nat, phi m -> n <= m)
  .

  Polymorphic Definition isChoicable (A : Type) : Type :=
    forall phi : A -> Prop, << UNIQUE : exists x : A, forall y : A, phi y <-> x = y >> -> {x : A | phi x}
  .

(** "Contents" *)

  Lemma derive_fixedpoint_combinator (D : Prop)
    (RETRACT_DtoD_D : RETRACT (D -> D) D)
    : {Y : (D -> D) -> D | forall f : D -> D, Y f = f (Y f)}.
  Proof.
    destruct RETRACT_DtoD_D as [lam_D app_D beta_D].
    pose (Y_combinator_of_Curry := fun f : D -> D => app_D (lam_D (fun x : D => f (app_D x x))) (lam_D (fun x : D => f (app_D x x)))).
    exists (Y_combinator_of_Curry). intros f.
    change (app_D (lam_D (fun x : D => f (app_D x x))) (lam_D (fun x : D => f (app_D x x))) = f (Y_combinator_of_Curry f)).
    now replace (app_D (lam_D (fun x : D => f (app_D x x)))) with (fun x : D => f (app_D x x)).
  Qed.

  Lemma TrueBB_eq_FalseBB_iff_pirrel
    : TrueBB = FalseBB <-> ⟪ PROOF_IRRELEVANCE : forall phi : Prop, pirrel_STMT phi ⟫.
  Proof.
    unnw. split.
    - intros hyp_eq phi pf1 pf2. exact (eq_congruence (fun b : BB => if b then pf1 else pf2) TrueBB FalseBB hyp_eq).
    - intros h_pirrel. exact (h_pirrel BB TrueBB FalseBB).
  Qed.

  Polymorphic Lemma pirrel_iff_eq_rect_eq (A : Type) (x : A)
    : ⟪ PROOF_IRRELEVANCE : pirrel_STMT (x = x) ⟫ <-> ⟪ EQ_RECT_EQ : forall B : A -> Type, eq_rect_eq_STMT A B x ⟫.
  Proof.
    iis; ii; desnw.
    - now rewrite PROOF_IRRELEVANCE with (pf1 := hyp_eq) (pf2 := eq_reflexivity x).
    - now do 2 (match goal with [ pf : x = x |- _ ] => rewrite <- EQ_RECT_EQ with (B := eq x) (phi_x := pf) (hyp_eq := eq_symmetry x x pf); destruct pf end).
  Qed.

  Polymorphic Lemma pirrel_iff_axiomK (A : Type) (x : A)
    : ⟪ PROOF_IRRELEVANCE : pirrel_STMT (x = x) ⟫ <-> ⟪ AXIOM_K : axiomK_STMT A x ⟫.
  Proof.
    iis; ii; desnw.
    - now rewrite PROOF_IRRELEVANCE with (pf1 := hyp_eq) (pf2 := eq_reflexivity x).
    - now do 2 (match goal with [ pf : x = x |- _ ] => pattern pf; revert pf; eapply AXIOM_K end).
  Qed.

  Polymorphic Lemma eq_rect_eq_iff_projT2_eq (A : Type) (B : A -> Type) (x : A)
    : ⟪ EQ_RECT_EQ : eq_rect_eq_STMT A B x ⟫ <-> ⟪ projT2_eq : projT2_eq_STMT A B x ⟫.
  Proof.
    iis; ii; desnw.
    - set (phi := fun pr1 : @sigT A B => fun pr2 : @sigT A B => fun projT1_eq : projT1 pr1 = projT1 pr2 => @eq_rect A (projT1 pr1) B (projT2 pr1) (projT1 pr2) projT1_eq = projT2 pr2).
      assert (claim1 : phi (@existT A B x y1) (@existT A B x y2) (eq_congruence (@projT1 A B) (@existT A B x y1) (@existT A B x y2) PAIR_EQ)) by now rewrite <- PAIR_EQ.
      unfold phi in claim1. rewrite EQ_RECT_EQ in claim1. exact (claim1).
    - eapply projT2_eq. now destruct hyp_eq.
  Qed.

  Section EXCLUSIVE_MIDDLE_implies_PROOF_IRRELEVANCE. (* Reference: "https://coq.inria.fr/library/Coq.Logic.Berardi.html" *)

  Hypothesis exclusive_middle : forall P : Prop, P \/ ~ P.

  Let POW (P : Prop) : Prop := P -> BB.

  Let RETRACT2_POW_A_POW_B (A : Prop) (B : Prop)
    : RETRACT2 (POW A) (POW B).
  Proof.
    destruct (exclusive_middle (RETRACT (POW A) (POW B))) as [hyp_yes | hyp_no].
    - exact ({| _i2 := _i hyp_yes; _j2 := _j hyp_yes; _inv2 := fun _ : RETRACT (POW A) (POW B) => _inv hyp_yes |}).
    - exact ({| _i2 := fun _ : POW A => fun _ : B => FalseBB; _j2 := fun _ : POW B => fun _ : A => FalseBB; _inv2 := fun r : RETRACT (POW A) (POW B) => False_ind (forall pa : POW A, (fun _ : A => FalseBB) = pa) (hyp_no r) |}).
  Qed.

  Let UNIV : Prop := forall P : Prop, POW P.

  Let SET_BUILDER_NOTATION (phi : UNIV -> BB) : UNIV :=
    fun P : Prop =>
    let LEFT : POW UNIV -> POW P := _j2 (RETRACT2_POW_A_POW_B P UNIV) in
    let RIGHT : POW UNIV -> POW UNIV := _i2 (RETRACT2_POW_A_POW_B UNIV UNIV) in
    LEFT (RIGHT phi)
  .

  Local Notation " ⦃ x | P ⦄ " := (SET_BUILDER_NOTATION (fun x : UNIV => P)) (x binder, at level 0, no associativity) : type_scope.

  Let HAS_AS_AN_ELEMENT (x : UNIV) : UNIV -> BB := x UNIV.

  Local Notation " z ∈ x " := (HAS_AS_AN_ELEMENT x z) (at level 70, no associativity) : type_scope.

  Let SET_BUILDER_NOTATION_SPEC (phi : UNIV -> BB)
    : (fun z : UNIV => z ∈ ⦃ x | phi x ⦄) = phi.
  Proof.
    unfold SET_BUILDER_NOTATION, HAS_AS_AN_ELEMENT.
    destruct (RETRACT2_POW_A_POW_B UNIV UNIV); cbn in *; eauto.
  Qed.

  Let NAIVE_SET_THEORY : RETRACT (POW UNIV) UNIV := {| _i := SET_BUILDER_NOTATION; _j := HAS_AS_AN_ELEMENT; _inv := SET_BUILDER_NOTATION_SPEC |}.

  Let NotBB (b : BB) : BB :=
    match exclusive_middle (b = TrueBB) return BB with
    | or_introl if_b_eq_TRUE_BB => FalseBB
    | or_intror if_b_ne_TRUE_BB => TrueBB
    end
  .

  Local Notation " ¬ b " := (NotBB b) (at level 55, right associativity) : type_scope.

  Let NOT_BB_SPEC1 (b : BB)
    (if_b_eq_TrueBB : b = TrueBB)
    : (¬ b) = FalseBB.
  Proof. cbv; destruct (exclusive_middle (b = TrueBB)); tauto. Qed.

  Let NOT_BB_SPEC2 (b : BB)
    (if_b_ne_TrueBB : b <> TrueBB)
    : (¬ b) = TrueBB.
  Proof. cbv; destruct (exclusive_middle (b = TrueBB)); tauto. Qed.

  Let russell (r : UNIV) : BB := ¬ (r ∈ r).

  Let R : UNIV := ⦃ r | russell r ⦄.

  Let RUSSELL : BB := R ∈ R.

  Let PARADOX_OF_BERARDI
    : RUSSELL = ¬ RUSSELL.
  Proof with eauto.
    enough (it_is_sufficient_to_show : RUSSELL = russell R)...
    replace (russell) with (fun r : UNIV => r ∈ R)...
  Qed.

  Theorem exclusive_middle_implies_proof_irrelevance (P : Prop)
    : pirrel_STMT P.
  Proof.
    eapply TrueBB_eq_FalseBB_iff_pirrel.
    destruct (exclusive_middle (RUSSELL = TrueBB)) as [RUSSELL_eq_TrueBB | RUSSELL_ne_TrueBB].
    - rewrite <- RUSSELL_eq_TrueBB. rewrite PARADOX_OF_BERARDI. now eapply NOT_BB_SPEC1.
    - contradiction (RUSSELL_ne_TrueBB). rewrite PARADOX_OF_BERARDI. now eapply NOT_BB_SPEC2.
  Qed.

  End EXCLUSIVE_MIDDLE_implies_PROOF_IRRELEVANCE.

  Section UNTYPED_LAMBDA_CALCULUS_FOR_BB_implies_PARADOX_OF_RUSSELL.

  Hypothesis untyped_lambda_calculus_for_BB : RETRACT (BB -> BB) BB.

  Let NotBB (b : BB) : BB :=
    match b return BB with
    | TrueBB => FalseBB
    | FalseBB => TrueBB
    end
  .

  Theorem untyped_lambda_calculus_for_BB_implies_paradox_of_russell
    : TrueBB = FalseBB.
  Proof.
    exploit (derive_fixedpoint_combinator BB untyped_lambda_calculus_for_BB) as [Y Y_spec]. set (RUSSELL := Y NotBB).
    assert (PARADOX_OF_RUSSELL : RUSSELL = NotBB RUSSELL) by exact (Y_spec NotBB). now destruct RUSSELL.
  Qed.

  End UNTYPED_LAMBDA_CALCULUS_FOR_BB_implies_PARADOX_OF_RUSSELL.

  Section PROPOSITIONAL_EXTENSIONALITY_implies_PROOF_IRRELEVANCE. (* Reference: "https://coq.inria.fr/library/Coq.Logic.ClassicalFacts.html" *)

  Hypothesis propositional_extensionality : forall P1 : Prop, forall P2 : Prop, (P1 <-> P2) -> (P1 = P2).

  Let D_coerce_D_ARROW_D_for_any_inhabited_Prop_D (D : Prop)
    (D_inhabited : inhabited D)
    : D = (D -> D).
  Proof.
    destruct D_inhabited as [D_holds].
    eapply propositional_extensionality; tauto.
  Qed.

  Let UNTYPED_LAMBDA_CALCULUS_for_any_inhabited_Prop (D : Prop)
    (D_inhabited : inhabited D)
    : RETRACT (D -> D) D.
  Proof. replace (D -> D) with (D); eauto. Qed.

  Theorem propositional_extensionality_implies_proof_irrelevance (P : Prop)
    : pirrel_STMT P.
  Proof.
    assert (BB_inhabited : inhabited BB) by now constructor; exact (FalseBB).
    eapply TrueBB_eq_FalseBB_iff_pirrel, untyped_lambda_calculus_for_BB_implies_paradox_of_russell; eauto.
  Qed.

  End PROPOSITIONAL_EXTENSIONALITY_implies_PROOF_IRRELEVANCE.

  Lemma propositional_extensionality_implies_proof_irrelevance_beautiful_ver
    (PROPOSITIONAL_EXTENSIONALITY : forall P1 : Prop, forall P2 : Prop, (P1 <-> P2) -> (P1 = P2))
    : forall P : Prop, pirrel_STMT P.
  Proof. (* Thanks to Minki Cho *)
    intros P p. assert (P_is_True : P = True) by now eapply PROPOSITIONAL_EXTENSIONALITY; tauto.
    revert p. subst P. now intros [] [].
  Qed.

  Section EXCLUSIVE_MIDDLE_implies_UNRESTRICTED_MINIMIZATION.

  Hypothesis exclusive_middle : forall P : Prop, P \/ ~ P.

  Theorem exclusive_middle_implies_Prop_level_unrestricted_minimization (phi : nat -> Prop)
    (not_forall_n_not_phi_n : ~ forall n : nat, ~ phi n)
    : exists n_min : nat, isMinimalNum phi n_min.
  Proof.
    assert (claim1 : exists n : nat, phi n) by now destruct (exclusive_middle (exists n : nat, phi n)); firstorder.
    destruct claim1 as [n phi_n]. destruct (exclusive_middle (forall x : nat, ~ isMinimalNum phi x)) as [H_yes | H_no].
    - enough (it_is_sufficient_to_show : ~ phi n) by contradiction (it_is_sufficient_to_show phi_n).
      induction n as [n IH] using @lt_strong_ind. contradiction (H_yes n). split.
      + exact (phi_n).
      + intros m phi_m. destruct (n_le_m_or_m_lt_n_holds_for_any_n_and_any_m n m) as [n_le_m | m_lt_n].
        { exact (n_le_m). }
        { contradiction (IH m). }
    - now destruct (exclusive_middle (exists m : nat, isMinimalNum phi m)); firstorder.
  Qed.

  End EXCLUSIVE_MIDDLE_implies_UNRESTRICTED_MINIMIZATION.

  Section CLASSICAL_IF_THEN_ELSE.

  Hypothesis bool_isChoicable : isChoicable bool.

  Theorem classical_if_then_else (P : Prop)
    (P_EXCLUSIVE_MIDDLE : P \/ ~ P)
    : {P} + {~ P}.
  Proof.
    enough (claim1 : {b : bool | if b then P else ~ P}) by exact ((if proj1_sig claim1 as b return (if b then P else ~ P) -> ({P} + {~ P}) then left else right) (proj2_sig claim1)).
    eapply bool_isChoicable; destruct P_EXCLUSIVE_MIDDLE as [hyp_yes | hyp_no]; [exists (true) | exists (false)]; now intros [ | ].
  Qed.

  End CLASSICAL_IF_THEN_ELSE.

  Polymorphic Theorem NotherianRecursion {A : Type} {requiresWellFounded : isWellFounded A} (phi : A -> Type)
    (IND : forall tree : A, << IH : forall subtree : A, wfRel subtree tree -> phi subtree >> -> phi tree)
    : forall root : A, phi root.
  Proof.
    unnw. intros root. induction (wfRel_well_founded root) as [tree hyp_acc_tree IH].
    eapply IND. intros subtree hyp_acc_subtree. exact (IH subtree hyp_acc_subtree).
  Defined.

  Global Instance nat_isWellFounded : isWellFounded nat :=
    { wfRel := lt
    ; wfRel_well_founded := @lt_strong_ind (@Acc nat lt) (@Acc_intro nat lt)
    }
  .

  Global Instance wfRel_Irreflexive {A : Type}
    {requiresWellFounded : isWellFounded A}
    : Irreflexive wfRel.
  Proof. intros x hyp_lt. induction x as [x IH] using NotherianRecursion. eapply IH; exact (hyp_lt). Defined.

  Polymorphic Lemma well_founded_relation_on_image {A : Type} {B : Type} (f : A -> B) (R : B -> B -> Prop)
    (R_wf : forall y : B, Acc R y)
    : forall x : A, Acc (binary_relation_on_image R f) x.
  Proof.
    intros x. remember (f x) as y eqn: y_eq_f_x.
    revert x y_eq_f_x. induction (R_wf y) as [y' hyp_wf IH].
    intros x' hyp_eq. econstructor. intros x f_x_R_f_x'.
    subst y'. eapply IH; [exact (f_x_R_f_x') | reflexivity].
  Defined.

  Lemma PreOrder_iff {A : Type} (R : A -> A -> Prop)
    : PreOrder R <-> << PREORDER_PROPERTY : forall x : A, forall y : A, R x y <-> ⟪ UNFOLDED : forall z : A, R z x -> R z y ⟫ >>.
  Proof. (split; ii; desnw); (split; ii; unnw); (now firstorder). Qed.

End FUN_FACTS.

Export FUN_FACTS.

Module SCRATCH.

  Import ListNotations.

  Section ACKERMANN.

  Record AckermannFuncSpec (ack : nat * nat -> nat) : Prop :=
    { AckermannFunc_spec1 : forall n, ack (0, n) = n + 1
    ; AckermannFunc_spec2 : forall m, ack (m + 1, 0) = ack (m, 1)
    ; AckermannFunc_spec3 : forall m n, ack (m + 1, n + 1) = ack (m, ack (m + 1, n))
    }
  .

  Definition AckermannImpl1Aux1 (kont : nat -> nat) : nat -> nat :=
    fix AckermannImpl1Aux1_fix (n : nat) {struct n} : nat :=
    match n with
    | zero => kont (suc zero)
    | suc n' => kont (AckermannImpl1Aux1_fix n')
    end
  .

  Definition AckermannImpl1Aux2 : nat -> nat -> nat :=
    fix AckermannImpl1Aux2_fix (m : nat) {struct m} : nat -> nat :=
    match m with
    | zero => suc
    | suc m' => AckermannImpl1Aux1 (AckermannImpl1Aux2_fix m')
    end
  .

  Definition AckermannImpl1 (it : nat * nat) : nat := AckermannImpl1Aux2 (fst it) (snd it).

  Theorem AckermannImpl1_satisfies_AckermannFuncSpec
    : AckermannFuncSpec AckermannImpl1.
  Proof with (lia || eauto).
    split.
    - intros n; replace (n + 1) with (S n)...
    - intros m; replace (m + 1) with (S m)...
    - intros [ | m']; induction n as [ | n IH]; cbn in *...
      all: replace (m' + 1) with (S m') in *...
  Qed.

  End ACKERMANN.

  Section SYNCHRONOUS_CIRCUIT.

  Set Primitive Projections.

  CoInductive circuit (Input : Type) (Output : Type) : Type :=
    { Circuit_observe : Input -> (circuit Input Output) * Output }
  .

  Unset Primitive Projections.

  End SYNCHRONOUS_CIRCUIT.

  Global Arguments Circuit_observe {Input} {Output}.
  Global Notation Circuit_go oc := ({| Circuit_observe := oc |}).

  Definition delayWithInit {I : Type} : I -> circuit I I :=
    cofix delayWithInit_cofix (x : I) : circuit I I :=
    Circuit_go (fun x' : I => (delayWithInit_cofix x', x))
  .

  Definition embedFunIntoCircuit {I : Type} {O : Type} (arr : I -> O) : circuit I O :=
    cofix embedFunIntoCircuit_cofix : circuit I O :=
    Circuit_go (fun x : I => (embedFunIntoCircuit_cofix, arr x))
  .

  Definition combineCircuit {I1 : Type} {I2 : Type} {O1 : Type} {O2 : Type} : circuit I1 O1 -> circuit I2 O2 -> circuit (I1 * I2) (O1 * O2) :=
    cofix combineCircuit_cofix (circuit1 : circuit I1 O1) (circuit2 : circuit I2 O2) : circuit (I1 * I2) (O1 * O2) :=
    Circuit_go (fun '(x1, x2) =>
      let '(circuit1', y1) := Circuit_observe circuit1 x1 in
      let '(circuit2', y2) := Circuit_observe circuit2 x2 in
      (combineCircuit_cofix circuit1' circuit2', (y1, y2))
    )
  .

End SCRATCH.
