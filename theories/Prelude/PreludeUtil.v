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

  Let eq_decoder (y : A) : x = y -> x = y := eq_transitivity x x y (eq_symmetry x x (eq_encoder x (eq_reflexivity x))) .

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

  Let eq_encode (eq_em_x : x = x \/ x <> x) (h_eq : x = x) : x = x :=
    match eq_em_x with
    | or_introl Heq => Heq
    | or_intror Hne => False_ind (x = x) (Hne h_eq)
    end
  .

  Let my_eq_encoder_x_eq_reflexivity_x_is (hyp_eq : x = x) : my_eq_encoder x (eq_reflexivity x) = my_eq_encoder x hyp_eq :=
    match eq_em x as eq_em_x return eq_encode eq_em_x (eq_reflexivity x) = eq_encode eq_em_x hyp_eq with
    | or_introl h_eq => eq_reflexivity h_eq
    | or_intror h_ne => False_ind (False_ind (x = x) (h_ne (eq_reflexivity x)) = False_ind (x = x) (h_ne hyp_eq)) (h_ne hyp_eq)
    end
  .

  Definition eq_em_implies_eq_pirrel : forall y : A, forall hyp_eq1 : x = y, forall hyp_eq2 : x = y, hyp_eq1 = hyp_eq2 :=
    eq_pirrel_holds_if_we_have_an_eq_encoder_which_returns_the_same_code my_eq_encoder (rect_eq_l x (fun y : A => fun hyp_eq1 : x = y => forall hyp_eq2 : x = y, my_eq_encoder y hyp_eq1 = my_eq_encoder y hyp_eq2) my_eq_encoder_x_eq_reflexivity_x_is)
  .

  End EQ_EM_implies_EQ_PIRREL.

  Definition eq_pirrel_fromEqDec {A : Type} {requiresEqDec : EqDec A}
    : forall x : A, forall y : A, forall hyp_eq1 : x = y, forall hyp_eq2 : x = y, hyp_eq1 = hyp_eq2.
  Proof.
    intros x.
    keep (fun y : A =>
      match eq_dec x y with
      | left hyp_yes => or_introl hyp_yes
      | right hyp_no => or_intror hyp_no
      end
    ) as eq_em into (forall y : A, x = y \/ x <> y).
    exact (
      fun x' : A => fun hyp_eq1 : x = x' =>
      match hyp_eq1 as hyp_eq1' in eq _ y' return forall hyp_eq : x = y', hyp_eq1' = hyp_eq with
      | eq_refl => eq_em_implies_eq_pirrel x eq_em x (eq_reflexivity x)
      end
    ).
  Defined.

End EQ_FACTS.

Export EQ_FACTS.

Module NAT_FACTS.

  Local Notation suc := S.
  Local Notation zero := O.

  Definition is_suc (n : nat) : Prop :=
    match n as x return Prop with
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

  Lemma le_iff {n : nat} {m : nat} :
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

  Lemma le_unfold {n : nat} {m : nat} (hyp_le : n <= m) :
    match m with
    | O => {_ : unit | n = 0}
    | S m' => {n = S m'} + {n <= m'}
    end.
  Proof.
    destruct m as [ | m'].
    - exists (tt). exact (le_antisymmetry hyp_le le_intro_0_le_n).
    - exact (
        match le_implies_Le hyp_le in Le _ x return {n = x} + {n <= Nat.pred x} with
        | Le_n _ => left (eq_reflexivity n)
        | Le_S _ m' hyp_le' => right (Le_implies_le hyp_le')
        end
      ).
  Defined.

  Theorem lt_strong_ind {phi : nat -> Prop}
    (ind_claim : forall n : nat, << IH : forall m : nat, m < n -> phi m >> -> phi n)
    : forall n : nat, phi n.
  Proof.
    unnw. intros n. eapply ind_claim. induction n as [ | n IH].
    - intros m. exact (@lt_elim_n_lt_0 (phi m) m).
    - intros m hyp_m_lt_S_n. eapply ind_claim. intros i hyp_i_lt_m. eapply IH. exact (le_transitivity hyp_i_lt_m (lt_elim_n_lt_S_m hyp_m_lt_S_n)).
  Defined.

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

  Lemma Fin_eq_dec (n : nat)
    : forall i1 : Fin n, forall i2 : Fin n, {i1 = i2} + {i1 <> i2}.
  Proof.
    induction n as [ | n IH].
    - intro_pattern_revert; eapply Fin_case0.
    - intro_pattern_revert; eapply Fin_caseS.
      + intro_pattern_revert; eapply Fin_caseS.
        { left. reflexivity. }
        { intros i2'. right. congruence. }
      + intros i1'. intro_pattern_revert; eapply Fin_caseS.
        { right. congruence. }
        { intros i2'. destruct (IH i1' i2') as [hyp_yes | hyp_no]; [left | right].
          - exact (eq_congruence (@FS n) i1' i2' hyp_yes).
          - intros hyp_eq.
            keep (fun i : Fin (S n) =>
              match i in Fin m return Fin (pred m) -> Fin (pred m) with
              | @FZ n' => fun x : Fin n' => x
              | @FS n' i' => fun _ : Fin n' => i'
              end
            ) as f_cong into (Fin (S n) -> Fin n -> Fin n).
            exact (hyp_no (eq_congruence2 f_cong (FS i1') (FS i2') hyp_eq i1' i1' (eq_reflexivity i1'))).
        }
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
    - cbn. eapply eq_congruence. etransitivity; [eapply eq_congruence, le_pirrel | exact IH].
  Qed.

  Global Instance Fin_equiv_fin (n : nat)
    : HasSameCardinality (Fin n) (fin n).
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

  Definition evalFin {n : nat} (i : Fin n) : nat := proj1_sig (runFin i).

  Lemma evalFin_unfold {n : nat} (i : Fin n) :
    evalFin i =
    match i with
    | FZ => O
    | FS i' => S (evalFin i')
    end.
  Proof. destruct i; reflexivity. Qed.

  Lemma evalFin_inj {n : nat} (i1 : Fin n) (i2 : Fin n)
    (hyp_eq : evalFin i1 = evalFin i2)
    : i1 = i2.
  Proof.
    unfold evalFin in hyp_eq.
    rewrite <- getFin_runFin_id with (i := i1).
    rewrite <- getFin_runFin_id with (i := i2).
    destruct (runFin i1) as [m1 hyp_lt1].
    destruct (runFin i2) as [m2 hyp_lt2].
    cbn in *. subst m1. eapply eq_congruence, le_pirrel.
  Qed.

  Definition incrFin {m : nat} : forall n : nat, Fin m -> Fin (n + m) :=
    fix incrFin_fix (n : nat) (i : Fin m) {struct n} : Fin (n + m) :=
    match n as x return Fin (x + m) with
    | O => i
    | S n' => FS (incrFin_fix n' i)
    end
  .

  Lemma incrFin_spec {m : nat} (n : nat) (i : Fin m)
    : evalFin (incrFin n i) = n + evalFin i.
  Proof with eauto.
    induction n as [ | n IH]; simpl...
    rewrite evalFin_unfold. eapply eq_congruence...
  Qed.

  Section VECTOR_ACCESSORIES.

  Variable A : Type.

  Inductive vector : nat -> Hask.t :=
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

  End VECTOR_ACCESSORIES.

  Global Arguments VNil {A}.
  Global Arguments VCons {A}.
  Global Arguments vector_casting {A} {n} {m} (hyp_eq).
  Global Arguments vector_case0 {A} {phi} (hypNil).
  Global Arguments vector_caseS {A} {n} {phi} (hypCons).
  Global Arguments vector_uncons {A} {n}.

  Global Tactic Notation "introVNil" := intro_pattern_revert; eapply vector_case0.
  Global Tactic Notation "introVCons" ident( _hd ) ident( _tl ) := intro_pattern_revert; eapply vector_caseS; intros _hd _tl.

  Definition vector_head {A : Type} {n : nat} (xs : vector A (S n)) : A := fst (vector_uncons xs (eq_reflexivity (S n))).

  Definition vector_tail {A : Type} {n : nat} (xs : vector A (S n)) : vector A n := snd (vector_uncons xs (eq_reflexivity (S n))).

  Global Bind Scope vector_scope with vector.

  Global Notation " '[' ']' " := (@VNil _) : vector_scope.
  Global Notation " x '::' xs " := (@VCons _ _ x xs) : vector_scope.

End MyData.

Export MyData.

Module FUN_FACTS.

  Class isWellFounded (A : Type) : Type :=
    { wfRel (subtree : A) (tree : A) : Prop
    ; wfRel_well_founded (root : A) : Acc wfRel root
    }
  .

  Theorem NotherianRecursion {A : Type} {requiresWellFounded : isWellFounded A} {phi : A -> Type}
    (acc_claim : forall tree : A, << IH : forall subtree : A, wfRel subtree tree -> phi subtree >> -> phi tree)
    : forall root : A, phi root.
  Proof.
    unnw. intros root. induction (wfRel_well_founded root) as [tree hyp_acc_tree IH].
    eapply acc_claim. intros subtree hyp_acc_subtree. exact (IH subtree hyp_acc_subtree).
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

  Definition dep_S {A : Type} {B : forall x : A, Type} {C : forall x : A, forall y : B x, Type} (f : forall x : A, forall y : B x, C x y) (g : forall x : A, B x) (x : A) : C x (g x) := f x (g x).

  Definition dep_K {A : Type} {B : forall x : A, Type} (x : A) (y : B x) : A := x.

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
