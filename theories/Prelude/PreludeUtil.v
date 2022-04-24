Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
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

  Definition rect_eq_r' (rhs : A) (lhs : A) (hyp_eq : lhs = rhs) : forall phi : forall lhs : A, lhs = rhs -> Type, phi rhs (eq_reflexivity rhs) -> phi lhs hyp_eq :=
    match hyp_eq as hyp_eq' in eq _ rhs' return forall phi' : forall lhs' : A, lhs' = rhs' -> Type, phi' rhs' (eq_reflexivity rhs') -> phi' lhs hyp_eq' with
    | eq_refl => fun phi' : forall lhs' : A, lhs' = lhs -> Type => fun phi_pf' : phi' lhs (eq_reflexivity lhs) => phi_pf'
    end
  .

  Definition rect_eq_r (rhs : A) (phi : forall lhs : A, lhs = rhs -> Type) (phi_pf : phi rhs (eq_reflexivity rhs)) (lhs : A) (hyp_eq : lhs = rhs) : phi lhs hyp_eq := rect_eq_r' rhs lhs hyp_eq phi phi_pf.

  Context {B : A -> Type}.

  Definition elim_eq_l (x1 : A) (x2 : A) (hyp_eq : x1 = x2) (pf : B x1) : B x2 := eq_rect x1 B pf x2 hyp_eq.

  Definition elim_eq_r (x1 : A) (x2 : A) (hyp_eq : x1 = x2) (pf : B x2) : B x1 := eq_rect x2 B pf x1 (eq_symmetry x1 x2 hyp_eq).

  Local Notation " 'pi_A_B' " := (forall x : A, B x) : type_scope.

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

  Let eq_curve (eq_em_x : x = x \/ x <> x) (h_eq : x = x) : x = x :=
    match eq_em_x with
    | or_introl Heq => Heq
    | or_intror Hne => False_ind (x = x) (Hne h_eq)
    end
  .

  Let my_eq_encoder_x_eq_reflexivity_x_is (hyp_eq : x = x) : my_eq_encoder x (eq_reflexivity x) = my_eq_encoder x hyp_eq :=
    match eq_em x as eq_em_x return eq_curve eq_em_x (eq_reflexivity x) = eq_curve eq_em_x hyp_eq with
    | or_introl h_eq => eq_reflexivity h_eq
    | or_intror h_ne => False_ind (False_ind (x = x) (h_ne (eq_reflexivity x)) = False_ind (x = x) (h_ne hyp_eq)) (h_ne hyp_eq)
    end
  .

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
    match n return Prop with
    | O => False
    | S n' => True
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

  Definition le_reflexitivity {n1 : nat} : n1 <= n1 := le_n n1.

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

  Theorem lt_strong_ind {phi : nat -> Prop}
    (IND : forall n : nat, << IH : forall m : nat, m < n -> phi m >> -> phi n)
    : forall n : nat, phi n.
  Proof.
    unnw. intros n. eapply IND with (n := n). induction n as [ | n IH].
    - intros m. exact (@lt_elim_n_lt_0 (phi m) m).
    - intros m hyp_m_lt_S_n. eapply IND with (n := m).
      intros i hyp_i_lt_m. eapply IH with (m := i). exact (le_transitivity hyp_i_lt_m (lt_elim_n_lt_S_m hyp_m_lt_S_n)).
  Defined.

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

  Import ListNotations.

  Definition safe_nth {A : Type} : forall xs : list A, Fin (length xs) -> A :=
    fix safe_nth_fix (xs : list A) {struct xs} : Fin (length xs) -> A :=
    match xs as this return Fin (length this) -> A with
    | [] => Fin_case0
    | x :: xs => Fin_caseS x (safe_nth_fix xs)
    end
  .

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
    assert (claim1 : a = b * (a / b) + (a mod b)) by now apply (Nat.div_mod a b); lia.
    assert (claim2 : 0 <= a mod b /\ a mod b < b) by now apply (Nat.mod_bound_pos a b); lia.
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
      { apply (Nat.mod_bound_pos a b)... }
      assert (claim3 : a >= r)...
      enough (claim4 : ~ q > a / b). enough (claim5 : ~ q < a / b). enough (claim6 : q = a / b)...
      + split... replace (a - r) with (q * b)... symmetry; apply Nat.div_mul...
      + intros H_false. destruct (proj1 (lemma2 (a / b) q) H_false) as [x Hx]...
      + intros H_false. destruct (proj1 (lemma2 q (a / b)) H_false) as [x Hx]...
    - intros [H_q [H_r H_a_ge_r]].
      pose proof (claim1 := Nat.mod_bound_pos a b). split...
      assert (claim2 : r < b)... assert (claim3 := Nat.div_mod a b H_b_ne_0).
      rewrite <- H_r in claim3. enough (claim4 : q = a / b)...
      rewrite H_q; symmetry. apply Nat.div_unique with (r := 0)...
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
      { apply Nat.div_mod... }
      enough (claim4 : (n_even - 2) mod 2 = 0).
      + assert (claim5 : n_even - 2 = 2 * n + 0 /\ 0 < 2)...
        rewrite H_r, Nat.add_0_r in claim3. apply claim1...
        replace (n_even - 2 - 0) with (n_even - 2)...
      + transitivity (n_even mod 2)...
        symmetry; replace (n_even) with ((n_even - 2) + 1 * 2) at 1...
        apply Nat.mod_add...
  Qed.

  Lemma plus_a_b_divmod_b a b (H_b_ne_0 : b <> 0)
    : ((a + b) / b = (a / b) + 1)%nat /\ ((a + b) mod b = a mod b)%nat.
  Proof with try lia.
    apply (div_mod_uniqueness (a + b) b ((a / b) + 1) (a mod b)).
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

  Lemma n_div_b_ge_1_if_n_ge_b_and_b_ge_1 (n : nat) (b : nat) :
    n >= b ->
    b >= 1 ->
    n / b >= 1.
  Proof with try lia.
    intros H_n_ge_b H_b_ge_1.
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

  Theorem well_ordering_principle : 
    forall p : nat -> bool,
    forall n : nat,
    p n = true ->
    let m : nat := first_nat p n in
    p m = true /\ (forall i : nat, p i = true -> i >= m).
  Proof with eauto. (* This proof has been improved by Junyoung Clare Jang. *)
    intros p n H3 m.
    assert (forall x : nat, p x = true -> p (first_nat p x) = true).
    { induction x...
      simpl.
      destruct (p (first_nat p x)) eqn: H0...
    }
    split...
    intros i H4.
    enough (forall x : nat, first_nat p x <= x).
    enough (forall x : nat, p (first_nat p x) = true -> (forall y : nat, x < y -> first_nat p x = first_nat p y)).
    enough (forall x : nat, forall y : nat, p y = true -> first_nat p x <= y)...
    - intros x y H2.
      destruct (le_gt_dec x y).
      + eapply Nat.le_trans...
      + replace (first_nat p x) with (first_nat p y)...
    - intros x H1 y H2.
      induction H2; simpl.
      + rewrite H1...
      + rewrite <- IHle, H1...
    - induction x...
      simpl.
      destruct (p (first_nat p x)) eqn: H0...
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
      + assert (claim4 : (S x, y) = cantor_pairing (sum_from_0_to (S z) + y)) by now apply (IHy (S x)); lia.
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

  Theorem cantor_pairing_spec n x y
    : cantor_pairing n = (x, y) <-> n = sum_from_0_to (x + y) + y.
  Proof.
    split.
    - exact (cantor_pairing_is_injective n x y).
    - intros Heq. subst n. symmetry.
      exact (cantor_pairing_is_surjective x y).
  Qed.

  Section LIST_ACCESSORIES.

  Import ListNotations.

  Lemma forallb_true_iff {A : Type} (p : A -> bool)
    : forall xs : list A, forallb p xs = true <-> (forall x : A, In x xs -> p x = true).
  Proof with try now firstorder.
    induction xs as [ | x xs IH]; simpl... rewrite andb_true_iff. split...
    intros [p_x_true forallb_p_xs_true] y [x_eq_y | y_in_xs]; [rewrite x_eq_y in p_x_true | apply IH]...
  Qed.

  Definition fold_right_max_0 : list nat -> nat := fold_right max 0.

  Lemma fold_right_max_0_in (ns : list nat) (n : nat) (H_IN : In n ns)
    : fold_right_max_0 ns >= n.
  Proof with (lia || eauto).
    unfold fold_right_max_0. revert n H_IN. induction ns as [ | n' ns IH]; simpl...
    intros n [H_eq | H_in]... enough (H_suff : fold_right max 0 ns >= n)...
  Qed.

  Lemma fold_right_max_0_app (ns1 : list nat) (ns2 : list nat)
    : fold_right_max_0 (ns1 ++ ns2) = max (fold_right_max_0 ns1) (fold_right_max_0 ns2).
  Proof with (lia || eauto).
    unfold fold_right_max_0. revert ns2.
    induction ns1 as [ | n1 ns1 IH]; simpl... 
    intros n; rewrite IH...
  Qed.

  Lemma property1_of_fold_right_max_0 (phi : nat -> Prop) (ns : list nat)
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

  Lemma property2_of_fold_right_max_0 (ns : list nat) (n : nat)
    : fold_right max 0 ns > n <-> (exists i : nat, In i ns /\ i > n).
  Proof with try now (lia || firstorder; eauto).
    revert n; induction ns as [ | n1 ns1 IH]; simpl... intros n.
    destruct (le_gt_dec n1 (fold_right Init.Nat.max 0 ns1)); split.
    - intros H_gt. assert (claim1 : fold_right Init.Nat.max 0 ns1 > n)...
    - intros [i [[H_eq | H_in] H_gt]]... enough (claim2 : fold_right max 0 ns1 > n)...
    - intros H_gt. exists (n1)...
    - intros [i [[H_eq | H_in] H_gt]]... enough (claim3 : fold_right Init.Nat.max 0 ns1 > n)...
  Qed.

  Lemma property3_of_fold_right_max_0 (ns1 : list nat) (ns2 : list nat)
    : fold_right max 0 (ns1 ++ ns2) = max (fold_right max 0 ns1) (fold_right max 0 ns2).
  Proof. exact (fold_right_max_0_app ns1 ns2). Qed.

  Lemma property4_of_fold_right_max_0 (ns : list nat) (n : nat) (H_IN : In n ns)
    : fold_right max 0 ns >= n.
  Proof with try now (lia || firstorder; eauto).
    revert n H_IN; induction ns as [ | n ns IH]; simpl...
    intros m [H_eq | H_in]... enough (H_suff : fold_right max 0 ns >= m)...
  Qed.

  Lemma property5_of_fold_right_max_0 (ns1 : list nat) (ns2 : list nat)
    (H_SUBSET : forall n : nat, In n ns1 -> In n ns2)
    : fold_right max 0 ns1 <= fold_right max 0 ns2.
  Proof with try now (lia || firstorder; eauto).
    revert ns2 H_SUBSET; induction ns1 as [ | n1 ns1 IH]; simpl...
    intros ns2 H. destruct (le_gt_dec n1 (fold_right max 0 ns1)).
    - enough (H_suff : fold_right max 0 ns1 <= fold_right max 0 ns2)...
    - enough (H_suff : n1 <= fold_right max 0 ns2)... apply property4_of_fold_right_max_0...
  Qed.

  Lemma fold_right_max_0_ext (ns1 : list nat) (ns2 : list nat)
    (H_EXT_EQ : forall n : nat, In n ns1 <-> In n ns2)
    : fold_right max 0 ns1 = fold_right max 0 ns2.
  Proof with try now firstorder.
    enough (claim1 : fold_right max 0 ns1 <= fold_right max 0 ns2 /\ fold_right max 0 ns2 <= fold_right max 0 ns1) by lia.
    split; apply property5_of_fold_right_max_0...
  Qed.

  Lemma in_remove_iff {A : Type} (x0 : A) (xs : list A)
    (A_eq_dec : forall x1 : A, forall x2 : A, {x1 = x2} + {x1 <> x2})
    : forall x : A, In x (remove A_eq_dec x0 xs) <-> (In x xs /\ x <> x0).
  Proof.
    pose proof (claim1 := in_remove A_eq_dec).
    pose proof (claim2 := in_in_remove A_eq_dec).
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
    induction xs as [| x' xs' IH]; simpl.
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

  End LIST_ACCESSORIES.

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

(* "REFACTOR ME!"
  Ltac repeat_rewrite :=
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
  Ltac auto_rewrite := repeat repeat_rewrite; repeat (try intro; try repeat_rewrite; try now (subst; firstorder)).
*)

End MyUtil.

Export MyUtil.

Module FUN_FACTS.

(** "Statements" *)

  Polymorphic Definition projT2_eq_STMT (A : Type) (B : A -> Type) (x : A) : Prop :=
    forall y1 : B x, forall y2 : B x, @existT A B x y1 = @existT A B x y2 -> y1 = y2
  .

  Polymorphic Definition axiomK_STMT (A : Type) (x : A) : Prop :=
    forall phi : x = x -> Prop, phi (eq_reflexivity x) -> forall hyp_eq : x = x, phi hyp_eq
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
    : TrueBB = FalseBB <-> << PROOF_IRRELEVANCE : forall phi : Prop, pirrel_STMT phi >>.
  Proof.
    unnw. split.
    - intros hyp_eq phi pf1 pf2.
      exact (eq_congruence (fun b : BB => if b then pf1 else pf2) TrueBB FalseBB hyp_eq).
    - intros h_pirrel.
      exact (h_pirrel BB TrueBB FalseBB).
  Qed.

  Polymorphic Theorem NotherianRecursion {A : Type} {requiresWellFounded : isWellFounded A} {phi : A -> Type}
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

End FUN_FACTS.

Export FUN_FACTS.

Module SCRATCH.

  Import ListNotations.

  Section ACKERMANN.

  Record AckermannFuncSpec (ack : (nat * nat) -> nat) : Prop :=
    { AckermannFunc_spec1 : forall n, ack (0, n) = n + 1
    ; AckermannFunc_spec2 : forall m, ack (m + 1, 0) = ack (m, 1)
    ; AckermannFunc_spec3 : forall m n, ack (m + 1, n + 1) = ack (m, ack (m + 1, n))
    }
  .

  Let AckermannFunc1_aux1 (kont : nat -> nat) : nat -> nat :=
    fix AckermannFunc1_aux1_fix (n : nat) {struct n} : nat :=
    match n with
    | zero => kont (suc zero)
    | suc n' => kont (AckermannFunc1_aux1_fix n')
    end
  .

  Let AckermannFunc1_aux2 : nat -> nat -> nat :=
    fix AckermannFunc1_aux2_fix (m : nat) {struct m} : nat -> nat :=
    match m with
    | zero => suc
    | suc m' => AckermannFunc1_aux1 (AckermannFunc1_aux2_fix m')
    end
  .

  Definition AckermannFunc1 (pr : nat * nat) : nat := AckermannFunc1_aux2 (fst pr) (snd pr).

  Theorem AckermannFunc1_satisfies_AckermannFuncSpec :
    AckermannFuncSpec AckermannFunc1.
  Proof with (lia || eauto).
    split.
    - intros n; replace (n + 1) with (S n)...
    - intros m; replace (m + 1) with (S m)...
    - intros [ | m']; induction n as [ | n IH]; cbn in *...
      all: replace (m' + 1) with (S m') in *...
  Qed.

  End ACKERMANN.

(* (* Reference: "https://github.com/agda/agda-stdlib/blob/456930d31e99ba1669a51a70e0d41e0434a9bb14/src/Induction/WellFounded.agda#L183" *)
  Section LexicographicalOrder.

  Context {A : Type} {B : A -> Type}.

  Let C : Type := @sigT A B.

  Inductive sigT_wfRel (wfRel_A : A -> A -> Prop) (wfRel_B : forall x : A, B x -> B x -> Prop) : C -> C -> Prop :=
  | sigT_wfRel_fst (x1 : A) (x2 : A) (y1 : B x1) (y2 : B x2)
    (hyp_wfRel_x1_x2 : wfRel_A x1 x2)
    : sigT_wfRel wfRel_A wfRel_B (@existT A B x1 y1) (@existT A B x2 y2)
  | sigT_wfRel_snd (x : A) (y1 : B x) (y2 : B x)
    (hyp_wfRel_y1_y2 : wfRel_B x y1 y2)
    : sigT_wfRel wfRel_A wfRel_B (@existT A B x y1) (@existT A B x y2)
  .

  Lemma sigT_wfRel_well_founded_aux {wfRel_A : A -> A -> Prop} {wfRel_B : forall x : A, B x -> B x -> Prop}
    (wf_A : forall x' : A, Acc wfRel_A x')
    (wf_B : forall x' : A, forall y' : B x', Acc (wfRel_B x') y')
    : forall root : C, Acc (sigT_wfRel wfRel_A wfRel_B) root.
  Proof.
    unnw. intros root.
    pose proof (wf_A (projT1 root)) as acc_x.
    pose proof (wf_B (projT1 root) (projT2 root)) as acc_y.
    revert root acc_x acc_y.
    refine (
      fix to_show_fix (tree : C) (acc_tree1 : Acc wfRel_A (projT1 tree)) (acc_tree2 : Acc (wfRel_B (projT1 tree)) (projT2 tree)) : Acc (sigT_wfRel wfRel_A wfRel_B) tree :=
      match acc_tree1, acc_tree2 with
      | Acc_intro _ hyp_acc_root1, Acc_intro _ hyp_acc_root2 => _
      end
    ).
    econstructor. intros subtree wfRel_subtree_tree. destruct wfRel_subtree_tree as [x1 x2 y1 y2 hyp_wfRel_x1_x2 | x y1 y2 hyp_wfRel_y1_y2].
    - eapply to_show_fix with (tree := existT B x1 y1).
      + eapply hyp_acc_root1. exact (hyp_wfRel_x1_x2).
      + exact (wf_B x1 y1).
    - eapply to_show_fix with (tree := existT B x y1).
      + exact (wf_A x).
      + eapply hyp_acc_root2. exact (hyp_wfRel_y1_y2).
  Defined.

  Hypothesis A_isWellFounded : isWellFounded A.

  Hypothesis B_x_isWellFounded : forall x : A, isWellFounded (B x).

  Definition indexed_lexicographical_order : C -> C -> Prop := sigT_wfRel (@wfRel A A_isWellFounded) (fun x : A => @wfRel (B x) (B_x_isWellFounded x)).

  Global Instance pair_isWellFounded
    : isWellFounded (@sigT A B).
  Proof.
    exists (indexed_lexicographical_order).
  Defined.

  End LexicographicalOrder.
*)

  Definition dep_S {A : Type} {B : forall x : A, Type} {C : forall x : A, forall y : B x, Type} (f : forall x : A, forall y : B x, C x y) (g : forall x : A, B x) (x : A) : C x (g x) := f x (g x).

  Definition dep_K {A : Type} {B : forall x : A, Type} (x : A) (y : B x) : A := x.

  Definition curry' {I : Type} {A : I -> Type} {B : I -> Type} {C : Type} : ({i : I & prod (A i) (B i)} -> C) -> (forall i : I, A i -> B i -> C) :=
    fun f : {i : I & prod (A i) (B i)} -> C =>
    fun i : I =>
    fun x : A i =>
    fun y : B i =>
    f (existT _ i (x, y))
  .

  Definition uncurry' {I : Type} {A : I -> Type} {B : I -> Type} {C : Type} : (forall i : I, A i -> B i -> C) -> ({i : I & prod (A i) (B i)} -> C) :=
    fun f : forall i : I, A i -> B i -> C =>
    fun p : {i : I & prod (A i) (B i)} =>
    match p with
    | existT _ i (x, y) => f i x y
    end
  .

  Definition kconcat {M : Hask.cat -----> Hask.cat} {requiresMonad : isMonad M} {X : Type} : list (kleisli M X X) -> kleisli M X X :=
    fix kconcat_fix (ks : list (kleisli M X X)) {struct ks} : kleisli M X X :=
    match ks with
    | [] => kempty
    | k :: ks => k <=< kconcat_fix ks
    end
  .

  Section SYNCHRONOUS_CIRCUIT.

  Set Primitive Projections.

  CoInductive circuit (Input : Type) (Output : Type) : Type :=
    Circuit_go { Circuit_observe : Input -> (circuit Input Output) * Output }
  .

  Global Arguments Circuit_go {Input} {Output}.
  Global Arguments Circuit_observe {Input} {Output}.

  Definition delayWithInit {I : Type} : I -> circuit I I :=
    cofix delayWithInit_cofix (x : I) : circuit I I :=
    Circuit_go (fun x' : I => (delayWithInit_cofix x', x))
  .

  Definition embedFunIntoCircuit {I : Type} {O : Type} (arr : I -> O) : circuit I O :=
    cofix embedFunIntoCircuit_cofix : circuit I O :=
    Circuit_go (fun x : I => (embedFunIntoCircuit_cofix, arr x))
  .

  Definition combineCircuit {I1 : Type} {I2 : Type} {O1 : Type} {O2 : Type}
    : circuit I1 O1 -> circuit I2 O2 -> circuit (I1 * I2) (O1 * O2).
  Proof.
    cofix combineCircuit_cofix.
    intros circuit1 circuit2. econstructor. intros [x1 x2].
    destruct (Circuit_observe circuit1 x1) as [circuit1' y1].
    destruct (Circuit_observe circuit2 x2) as [circuit2' y2].
    exact (combineCircuit_cofix circuit1' circuit2', (y1, y2)).
  Defined.

  End SYNCHRONOUS_CIRCUIT.

End SCRATCH.
