Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Module EqFacts.

  Section EQ_CONSTRUCTORS.

  Context {A : Type}.

  Definition eq_reflexivity : forall x1 : A, x1 = x1 :=
    fun x1 : A =>
    @eq_refl A x1
  .

  Definition eq_symmetry : forall x1 : A, forall x2 : A, x1 = x2 -> x2 = x1 :=
    fun x1 : A =>
    fun x2 : A =>
    @eq_ind A x1 (fun x : A => x = x1) (@eq_refl A x1) x2
  .

  Definition eq_transitivity : forall x1 : A, forall x2 : A, forall x3 : A, x1 = x2 -> x2 = x3 -> x1 = x3 :=
    fun x1 : A =>
    fun x2 : A =>
    fun x3 : A =>
    fun H : x1 = x2 =>
    @eq_ind A x2 (fun x : A => x1 = x) H x3
  .

  Context {B : Type}.

  Definition eq_congruence : forall f : A -> B, forall x1 : A, forall x2 : A, x1 = x2 -> f x1 = f x2 :=
    fun f : A -> B =>
    fun x1 : A =>
    fun x2 : A =>
    @eq_ind A x1 (fun x : A => f x1 = f x) (@eq_refl B (f x1)) x2
  .

  Context {C : Type}.

  Definition eq_congruence2 : forall f : A -> B -> C, forall x1 : A, forall x2 : A, x1 = x2 -> forall y1 : B, forall y2 : B, y1 = y2 -> f x1 y1 = f x2 y2 :=
    fun f : A -> B -> C =>
    fun x1 : A =>
    fun x2 : A =>
    fun Heq1 : x1 = x2 =>
    fun y1 : B =>
    fun y2 : B =>
    fun Heq2 : y1 = y2 =>
    @eq_ind B y1 (fun y : B => f x1 y1 = f x2 y) (@eq_ind A x1 (fun x : A => f x1 y1 = f x y1) (@eq_refl C (f x1 y1)) x2 Heq1) y2 Heq2
  .

  End EQ_CONSTRUCTORS.

  Section EQ_DESTRUCTORS.

  Context {A : Type}.

  Definition ind_eq_l (lhs : A) (phi : forall rhs : A, lhs = rhs -> Prop) : phi lhs (eq_reflexivity lhs) -> forall rhs : A, forall H : lhs = rhs, phi rhs H :=
    fun phi_pf : phi lhs (eq_reflexivity lhs) =>
    fun rhs : A =>
    fun H : lhs = rhs =>
    match H as H0 in eq _ lhs0 return phi lhs0 H0 with
    | eq_refl => phi_pf
    end
  .

  Definition ind_eq_r (rhs : A) (phi : forall lhs : A, lhs = rhs -> Prop) : phi rhs (eq_reflexivity rhs) -> forall lhs : A, forall H : lhs = rhs, phi lhs H :=
    fun phi_pf : phi rhs (eq_reflexivity rhs) =>
    fun lhs : A =>
    fun H : lhs = rhs =>
    match H as H0 in eq _ rhs0 return forall phi0 : forall lhs0 : A, lhs0 = rhs0 -> Prop, phi0 rhs0 (eq_reflexivity rhs0) -> phi0 lhs H0 with
    | eq_refl =>
      fun phi0 : forall lhs0 : A, lhs0 = lhs -> Prop =>
      fun phi0_pf : phi0 lhs (eq_reflexivity lhs) =>
      phi0_pf
    end phi phi_pf
  .

  Definition rec_eq_l (lhs : A) (phi : forall rhs : A, lhs = rhs -> Set) : phi lhs (eq_reflexivity lhs) -> forall rhs : A, forall H : lhs = rhs, phi rhs H :=
    fun phi_pf : phi lhs (eq_reflexivity lhs) =>
    fun rhs : A =>
    fun H : lhs = rhs =>
    match H as H0 in eq _ lhs0 return phi lhs0 H0 with
    | eq_refl => phi_pf
    end
  .

  Definition rec_eq_r (rhs : A) (phi : forall lhs : A, lhs = rhs -> Set) : phi rhs (eq_reflexivity rhs) -> forall lhs : A, forall H : lhs = rhs, phi lhs H :=
    fun phi_pf : phi rhs (eq_reflexivity rhs) =>
    fun lhs : A =>
    fun H : lhs = rhs =>
    match H as H0 in eq _ rhs0 return forall phi0 : forall lhs0 : A, lhs0 = rhs0 -> Set, phi0 rhs0 (eq_reflexivity rhs0) -> phi0 lhs H0 with
    | eq_refl =>
      fun phi0 : forall lhs0 : A, lhs0 = lhs -> Set =>
      fun phi0_pf : phi0 lhs (eq_reflexivity lhs) =>
      phi0_pf
    end phi phi_pf
  .

  Definition rect_eq_l (lhs : A) (phi : forall rhs : A, lhs = rhs -> Type) : phi lhs (eq_reflexivity lhs) -> forall rhs : A, forall H : lhs = rhs, phi rhs H :=
    fun phi_pf : phi lhs (eq_reflexivity lhs) =>
    fun rhs : A =>
    fun H : lhs = rhs =>
    match H as H0 in eq _ lhs0 return phi lhs0 H0 with
    | eq_refl => phi_pf
    end
  .

  Definition rect_eq_r (rhs : A) (phi : forall lhs : A, lhs = rhs -> Type) : phi rhs (eq_reflexivity rhs) -> forall lhs : A, forall H : lhs = rhs, phi lhs H :=
    fun phi_pf : phi rhs (eq_reflexivity rhs) =>
    fun lhs : A =>
    fun H : lhs = rhs =>
    match H as H0 in eq _ rhs0 return forall phi0 : forall lhs0 : A, lhs0 = rhs0 -> Type, phi0 rhs0 (eq_reflexivity rhs0) -> phi0 lhs H0 with
    | eq_refl =>
      fun phi0 : forall lhs0 : A, lhs0 = lhs -> Type =>
      fun phi0_pf : phi0 lhs (eq_reflexivity lhs) =>
      phi0_pf
    end phi phi_pf
  .

  Context {B : A -> Type}.

  Definition elim_eq_l : forall x1 : A, forall x2 : A, x1 = x2 -> B x1 -> B x2 :=
    fun x1 : A =>
    fun x2 : A =>
    fun H_eq : x1 = x2 =>
    fun pf : B x1 =>
    eq_rect x1 B pf x2 H_eq
  .

  Definition elim_eq_r : forall x1 : A, forall x2 : A, x1 = x2 -> B x2 -> B x1 :=
    fun x1 : A =>
    fun x2 : A =>
    fun H_eq : x1 = x2 =>
    fun pf : B x2 =>
    eq_rect x2 B pf x1 (eq_symmetry x1 x2 H_eq)
  .

  Local Notation " 'pi_A_B' " := (forall x : A, B x) : type_scope.

  Lemma elim_eq_l_spec :
    forall x1 : A,
    forall x2 : A,
    forall f : pi_A_B,
    forall H_eq : x1 = x2,
    elim_eq_l x1 x2 H_eq (f x1) = f x2.
  Proof.
    intros x1 x2 f []; constructor.
  Qed.

  Lemma elim_eq_r_spec :
    forall x1 : A,
    forall x2 : A,
    forall f : pi_A_B,
    forall H_eq : x1 = x2,
    elim_eq_r x1 x2 H_eq (f x2) = f x1.
  Proof.
    intros x1 x2 f []; constructor.
  Qed.

  Definition transport {x1 : A} {x2 : A} : x1 = x2 -> B x1 -> B x2 :=
    elim_eq_l x1 x2
  .

  End EQ_DESTRUCTORS.

  Section EQ_EM_implies_EQ_PIRREL. (* Reference: "https://coq.inria.fr/library/Coq.Logic.Eqdep_dec.html" *)

  Context {A : Type}.

  Definition eq_round_trip : forall x1 : A, forall x2 : A, forall H : x1 = x2, eq_transitivity x2 x1 x2 (eq_symmetry x1 x2 H) H = eq_reflexivity x2 :=
    fun x : A =>
    ind_eq_l x (fun y : A => fun H : x = y => eq_transitivity y x y (eq_symmetry x y H) H = eq_reflexivity y) (eq_reflexivity (eq_reflexivity x))
  .

  Variable x : A.

  Section ABSTRACT_FORM.

  Variable eq_encoder : forall y : A, x = y -> x = y.

  Let eq_decoder : forall y : A, x = y -> x = y :=
    fun y : A =>
    eq_transitivity x x y (eq_symmetry x x (eq_encoder x (eq_reflexivity x)))
  .

  Let eq_decoder_decodes_properly : forall y : A, forall H : x = y, eq_decoder y (eq_encoder y H) = H :=
    ind_eq_l x (fun y : A => fun H : x = y => eq_decoder y (eq_encoder y H) = H) (eq_round_trip x x (eq_encoder x (eq_reflexivity x)))
  .

  Hypothesis all_eq_codes_are_indistinguishable_from_each_other : forall y : A, forall H1 : x = y, forall H2 : x = y, eq_encoder y H1 = eq_encoder y H2.

  Definition eq_pirrel_holds_if_we_have_an_eq_encoder_which_returns_the_same_code : forall y : A, forall H1 : x = y, forall H2 : x = y, H1 = H2 :=
    fun y : A =>
    fun H1 : x = y =>
    fun H2 : x = y =>
    let claim1 : eq_decoder y (eq_encoder y H1) = eq_decoder y (eq_encoder y H2) := eq_congruence (eq_decoder y) (eq_encoder y H1) (eq_encoder y H2) (all_eq_codes_are_indistinguishable_from_each_other y H1 H2) in
    eq_ind (eq_decoder y (eq_encoder y H2)) (fun H : x = y => H1 = H) (eq_ind (eq_decoder y (eq_encoder y H1)) (fun H : x = y => H = eq_decoder y (eq_encoder y H2)) claim1 H1 (eq_decoder_decodes_properly y H1)) H2 (eq_decoder_decodes_properly y H2)
  .

  End ABSTRACT_FORM.

  Hypothesis eq_em : forall y : A, x = y \/ x <> y.

  Let my_eq_encoder : forall y : A, x = y -> x = y :=
    fun y : A =>
    fun H_EQ : x = y =>
    match eq_em y return x = y with
    | or_introl Heq => Heq
    | or_intror Hne => False_ind (x = y) (Hne H_EQ)
    end
  .

  Let my_eq_encoder_x_eq_reflexivity_x_is : forall H_EQ : x = x, my_eq_encoder x (eq_reflexivity x) = my_eq_encoder x H_EQ :=
    fun H_EQ : x = x =>
    match eq_em x as eq_em_x return (match eq_em_x return x = x with | or_introl Heq => Heq | or_intror Hne => False_ind (x = x) (Hne (eq_reflexivity x)) end) = (match eq_em_x return x = x with | or_introl Heq => Heq | or_intror Hne => False_ind (x = x) (Hne H_EQ) end) with
    | or_introl Heq => eq_reflexivity Heq
    | or_intror Hne => False_ind (False_ind (x = x) (Hne (eq_reflexivity x)) = False_ind (x = x) (Hne H_EQ)) (Hne H_EQ)
    end
  .

  Definition eq_em_implies_eq_pirrel : forall y : A, forall H_EQ1 : x = y, forall H_EQ2 : x = y, H_EQ1 = H_EQ2 :=
    eq_pirrel_holds_if_we_have_an_eq_encoder_which_returns_the_same_code my_eq_encoder (ind_eq_l x (fun y : A => fun H1 : x = y => forall H2 : x = y, my_eq_encoder y H1 = my_eq_encoder y H2) my_eq_encoder_x_eq_reflexivity_x_is)
  .

  End EQ_EM_implies_EQ_PIRREL.

End EqFacts.

Module MyUtilities.

  Import ListNotations EqFacts.

  Global Create HintDb my_hints.

  Section ARITH_WITHOUT_SOLVER.

  Definition S_eq_0_elim {A : Type} : forall n : nat, S n = O -> A :=
    fun n : nat =>
    fun H : S n = O =>
    False_rect A (eq_ind O (fun x : nat => if Nat.eqb O x then True else False) I (S n) (eq_symmetry (S n) O H))
  .

  Definition S_eq_S_elim : forall n1 : nat, forall n2 : nat, S n1 = S n2 -> n1 = n2 :=
    fun n1 : nat =>
    fun n2 : nat =>
    eq_congruence Nat.pred (S n1) (S n2)
  .

  Definition lt_elim_n_lt_0 {A : Type} : forall n : nat, n < O -> A :=
    fun n : nat =>
    fun H : S n <= O =>
    False_rect A (le_ind (S n) (fun x : nat => if Nat.eqb O x then False else True) I (fun m : nat => fun H0 : S n <= m => fun H1 : if Nat.eqb O m then False else True => I) O H)
  .

  Definition guarantee1_S_pred_n_eq_n {m : nat} {n : nat} : S m <= n -> S (pred n) = n :=
    fun H : S m <= n =>
    match H in le _ n0 return S (pred n0) = n0 with
    | le_n _ => eq_reflexivity (S m)
    | le_S _ n' H' => eq_reflexivity (S n')
    end
  .

  Definition le_elim_S_n_le_m : forall n : nat, forall m : nat, S n <= m -> n <= pred m :=
    fun n : nat =>
    fix le_elim_S_n_le_m_fix (m : nat) (H : S n <= m) {struct H} : n <= pred m :=
    match H in le _ m0 return n <= pred m0 with
    | le_n _ => le_n n
    | le_S _ m' H' => eq_ind (S (pred m')) (le n) (le_S n (pred m') (le_elim_S_n_le_m_fix m' H')) m' (guarantee1_S_pred_n_eq_n H')
    end
  .

  Definition le_reflexivity {n1 : nat} : n1 <= n1 :=
    le_n n1
  .

  Let le_transitivity_aux1 : forall n1 : nat, forall n2 : nat, n1 <= n2 -> forall n3 : nat, n2 <= n3 -> n1 <= n3 :=
    fun n1 : nat =>
    fix le_transitivity_aux1_fix (n2 : nat) (Hle1 : le n1 n2) {struct Hle1} : forall n3 : nat, n2 <= n3 -> n1 <= n3 :=
    match Hle1 in le _ m return forall n3 : nat, m <= n3 -> n1 <= n3 with
    | le_n _ =>
      fun n3 : nat =>
      fun Hle2 : n1 <= n3 =>
      Hle2
    | le_S _ n2' Hle1' =>
      fun n3 : nat =>
      fun Hle2 : S n2' <= n3 =>
      let claim1 : n2' <= pred n3 := le_elim_S_n_le_m n2' n3 Hle2 in
      let claim2 : S (pred n3) = n3 := guarantee1_S_pred_n_eq_n Hle2 in
      let claim3 : n2' <= S (pred n3) := le_S n2' (pred n3) claim1 in
      let claim4 : n2' <= n3 := eq_ind (S (pred n3)) (fun m : nat => n2' <= m) claim3 n3 claim2 in
      le_transitivity_aux1_fix n2' Hle1' n3 claim4
    end
  .

  Definition le_transitivity {n1 : nat} {n2 : nat} {n3 : nat} : n1 <= n2 -> n2 <= n3 -> n1 <= n3 :=
    fun Hle1 : n1 <= n2 =>
    fun Hle2 : n2 <= n3 =>
    le_transitivity_aux1 n1 n2 Hle1 n3 Hle2
  .

  Definition le_inversion (P : nat -> nat -> Prop) : forall n1 : nat, forall n2 : nat, forall Hle : n1 <= n2, (n1 = n2 -> P n2 n2) -> (forall m' : nat, n1 <= m' -> S m' = n2 -> P n1 (S m')) -> P n1 n2 :=
    fun n1 : nat =>
    fun n2 : nat =>
    fun Hle : n1 <= n2 =>
    match Hle in le _ m return m = n2 -> (n1 = n2 -> P m m) -> (forall m' : nat, n1 <= m' -> S m' = n2 -> P n1 (S m')) -> P n1 m with
    | le_n _ =>
      fun Heq : n1 = n2 =>
      fun H1 : n1 = n2 -> P n1 n1 =>
      fun H2 : forall m' : nat, n1 <= m' -> S m' = n2 -> P n1 (S m') =>
      H1 Heq
    | le_S _ m' Hle' =>
      fun Heq : S m' = n2 =>
      fun H1 : n1 = n2 -> P (S m') (S m') =>
      fun H2 : forall m' : nat, n1 <= m' -> S m' = n2 -> P n1 (S m') =>
      H2 m' Hle' Heq
    end (eq_reflexivity n2)
  .

  Definition le_intro_0_le_n : forall n : nat, 0 <= n :=
    fix le_intro_0_le_n_fix (n : nat) {struct n} : 0 <= n :=
    match n as n0 return 0 <= n0 with
    | O => le_n O
    | S n' => le_S O n' (le_intro_0_le_n_fix n')
    end
  .

  Definition le_intro_S_n_le_S_m : forall n : nat, forall m : nat, n <= m -> S n <= S m :=
    fun n : nat =>
    fix le_intro_S_n_le_S_m_fix (m : nat) (Hle : n <= m) {struct Hle} : S n <= S m :=
    match Hle in le _ m0 return le (S n) (S m0) with
    | le_n _ => le_n (S n)
    | le_S _ m' H' => le_S (S n) (S m') (le_intro_S_n_le_S_m_fix m' H')
    end
  .

  Definition n1_le_max_n1_n2 : forall n1 : nat, forall n2 : nat, n1 <= max n1 n2 :=
    fix n1_le_max_n1_n2_fix (n : nat) {struct n} : forall m : nat, n <= max n m :=
    match n as n0 return forall m : nat, n0 <= max n0 m with
    | O => le_intro_0_le_n
    | S n' =>
      fun m : nat =>
      match m as m0 return S n' <= max (S n') m0 with
      | O => le_n (S n')
      | S m' => le_intro_S_n_le_S_m n' (max n' m') (n1_le_max_n1_n2_fix n' m')
      end
    end
  .

  Definition n2_le_max_n1_n2 : forall n1 : nat, forall n2 : nat, n2 <= max n1 n2 :=
    fix n2_le_max_n1_n2_fix (n : nat) {struct n} : forall m : nat, m <= max n m :=
    match n as n0 return forall m : nat, m <= max n0 m with
    | O => le_n
    | S n' =>
      fun m : nat =>
      match m as m0 return m0 <= max (S n') m0 with
      | O => le_intro_0_le_n (S n')
      | S m' => le_intro_S_n_le_S_m m' (max n' m') (n2_le_max_n1_n2_fix n' m')
      end
    end
  .

  Definition le_elim_max_n1_n2_le_m : forall n1 : nat, forall n2 : nat, forall m : nat, max n1 n2 <= m -> n1 <= m /\ n2 <= m :=
    fun n1 : nat =>
    fun n2 : nat =>
    fun m : nat =>
    fun Hle : max n1 n2 <= m =>
    conj (le_transitivity (n1_le_max_n1_n2 n1 n2) Hle) (le_transitivity (n2_le_max_n1_n2 n1 n2) Hle)
  .

  Definition lt_elim_S_n_lt_S_m : forall n : nat, forall m : nat, S n < S m -> n < m :=
    fun n1 : nat =>
    fun n2 : nat =>
    le_elim_S_n_le_m (S n1) (S n2)
  .

  Definition lt_intro_0_lt_S_n : forall n : nat, 0 < S n :=
    fix lt0_intro_fix (n : nat) {struct n} : S O <= S n :=
    match n as n0 return S O <= S n0 with
    | O => le_n (S O)
    | S n' => le_S (S O) (S n') (lt0_intro_fix n')
    end
  .

  Definition lt_intro_S_m_lt_S_n : forall m : nat, forall n : nat, m < n -> S m < S n :=
    fun n1 : nat =>
    fun n2 : nat =>
    le_intro_S_n_le_S_m (S n1) n2
  .

  Definition not_n_lt_n : forall n : nat, ~ n < n :=
    fix not_n_lt_n_fix (n : nat) {struct n} : S n <= n -> False :=
    match n as n0 return S n0 <= n0 -> False with
    | O => lt_elim_n_lt_0 O
    | S n' =>
      fun Hle : S (S n') <= S n' =>
      not_n_lt_n_fix n' (le_elim_S_n_le_m (S n') (S n') Hle)
    end
  .

  Definition le_gt_False : forall n : nat, forall m : nat, n <= m -> n > m -> False :=
    fun n : nat =>
    fix le_gt_False_fix (m : nat) (Hle : n <= m) {struct Hle} : m < n -> False :=
    match Hle in le _ m0 return m0 < n -> False with
    | le_n _ => not_n_lt_n n
    | le_S _ m' Hle' =>
      fun Hlt : S m' < n =>
      le_gt_False_fix m' Hle' (le_transitivity (le_S (S m') (S m') (le_n (S m'))) Hlt)
    end
  .

  Definition le_asymmetry {n1 : nat} {n2 : nat} : n1 <= n2 -> n2 <= n1 -> n1 = n2 :=
    fun Hle1 : n1 <= n2 =>
    match Hle1 in le _ m return m <= n1 -> n1 = m with
    | le_n _ =>
      fun Hle2 : n1 <= n1 =>
      eq_reflexivity n1
    | le_S _ m' Hle1' =>
      fun Hle2 : m' < n1 =>
      False_ind (n1 = S m') (le_gt_False n1 m' Hle1' Hle2)
    end
  .

  Definition le_intro_plus1 : forall n : nat, forall m : nat, n <= n + m :=
    fix le_intro_plus1_fix (n : nat) {struct n} : forall m : nat, n <= n + m :=
    match n as n0 return forall m : nat, n0 <= n0 + m with
    | O => le_intro_0_le_n
    | S n' =>
      fun m : nat =>
      le_intro_S_n_le_S_m n' (n' + m) (le_intro_plus1_fix n' m)
    end
  .

  Definition le_intro_plus2 : forall n : nat, forall m : nat, m <= n + m :=
    fix le_intro_plus2_fix (n : nat) {struct n} : forall m : nat, m <= n + m :=
    match n as n0 return forall m : nat, m <= n0 + m with
    | O => le_n
    | S n' =>
      fun m : nat =>
      le_S m (n' + m) (le_intro_plus2_fix n' m)
    end
  .

  Definition eq_dec_nat : forall n1 : nat, forall n2 : nat, {n1 = n2} + {n1 <> n2} :=
    fix eq_dec_nat_fix (n1 : nat) {struct n1} : forall n2 : nat, {n1 = n2} + {n1 <> n2} :=
    match n1 as n return forall n2 : nat, {n = n2} + {n <> n2} with
    | O =>
      fun n2 : nat =>
      match n2 as n return {O = n} + {O <> n} with
      | O => left (eq_reflexivity O)
      | S n2' => right (fun H : O = S n2' => S_eq_0_elim n2' (eq_symmetry O (S n2') H))
      end
    | S n1' =>
      fun n2 : nat =>
      match n2 as n return {S n1' = n} + {S n1' <> n} with
      | O => right (fun H : S n1' = O => S_eq_0_elim n1' H)
      | S n2' =>
        match eq_dec_nat_fix n1' n2' return {S n1' = S n2'} + {S n1' <> S n2'} with
        | left Heq => left (eq_congruence S n1' n2' Heq)
        | right Hne => right (fun Heq : S n1' = S n2' => Hne (S_eq_S_elim n1' n2' Heq))
        end
      end
    end
  .

  Definition n_le_m_and_n_ne_m_implies_n_lt_m : forall n : nat, forall m : nat, n <= m -> n <> m -> n < m :=
    fun n : nat =>
    fun m : nat =>
    fun Hle : n <= m =>
    match Hle in le _ m0 return n <> m0 -> n < m0 with
    | le_n _ =>
      fun Hne : n <> n =>
      False_ind (n < n) (Hne (eq_reflexivity n))
    | le_S _ m' Hle' =>
      fun Hne : n <> S m' =>
      le_intro_S_n_le_S_m n m' Hle'
    end
  .

  Definition n_le_m_or_m_lt_n_holds_for_any_n_and_any_m : forall n : nat, forall m : nat, {n <= m} + {m < n} :=
    fix n_le_m_or_m_lt_n_holds_for_any_n_and_any_m_fix (n : nat) {struct n} : forall m : nat, {n <= m} + {m < n} :=
    match n as n0 return forall m : nat, {n0 <= m} + {m < n0} with
    | O =>
      fun m : nat =>
      left (le_intro_0_le_n m)
    | S n' =>
      fun m : nat =>
      match n_le_m_or_m_lt_n_holds_for_any_n_and_any_m_fix n' m return {S n' <= m} + {m < S n'} with
      | left Hle =>
        match eq_dec_nat n' m return {S n' <= m} + {m < S n'} with
        | left Heq => right (eq_ind m (fun x : nat => le (S m) (S x)) (le_n (S m)) n' (eq_symmetry n' m Heq))
        | right Hne => left (n_le_m_and_n_ne_m_implies_n_lt_m n' m Hle Hne)
        end
      | right Hlt => right (le_S (S m) n' Hlt)
      end
    end
  .

  End ARITH_WITHOUT_SOLVER.

  Section STRONG_INDUCTION_ON_nat.

  Variable P : nat -> Prop.

  Let case0 : forall n : nat, forall H : n < O, P n :=
    fun n : nat =>
    @lt_elim_n_lt_0 (P n) n
  .

  Hypothesis ACC_HYP : forall m : nat, (forall n : nat, n < m -> P n) -> P m.

  Let caseS : forall m : nat, (forall n : nat, n < m -> P n) -> forall n : nat, n < S m -> P n :=
    fun m : nat =>
    fun IH : forall n : nat, n < m -> P n =>
    fun n : nat =>
    fun Hle : S n <= S m =>
    ACC_HYP n (fun i : nat => fun Hlt : i < n => IH i (le_transitivity Hlt (le_elim_S_n_le_m n (S m) Hle)))
  .

  Definition strong_induction : forall i : nat, P i :=
    fun i : nat =>
    ACC_HYP i (nat_ind (fun m : nat => forall n : nat, n < m -> P n) case0 caseS i)
  .

  End STRONG_INDUCTION_ON_nat.

  Section ARITHMETIC_PIRREL.

  Let eqnat_em : forall n1 : nat, forall n2 : nat, n1 = n2 \/ n1 <> n2 :=
    fun n1 : nat =>
    fun n2 : nat =>
    match eq_dec_nat n1 n2 return n1 = n2 \/ n1 <> n2 with
    | left H_yes => or_introl H_yes
    | right H_no => or_intror H_no
    end
  .

  Definition eqnat_proof_irrelevance : forall n1 : nat, forall n2 : nat, forall H_EQ1 : n1 = n2, forall H_EQ2 : n1 = n2, H_EQ1 = H_EQ2 :=
    fun n : nat =>
    eq_em_implies_eq_pirrel n (eqnat_em n)
  .

  Theorem lenat_proof_irrelevance :
    forall n1 : nat,
    forall n2 : nat,
    forall H_LE1 : n1 <= n2,
    forall H_LE2 : n1 <= n2,
    H_LE1 = H_LE2.
  Proof.
    refine (
      fun n1 : nat =>
      fix lenat_proof_irrelevance_fix (n2 : nat) (H_LE1 : n1 <= n2) {struct H_LE1} : forall H_LE2 : n1 <= n2, H_LE1 = H_LE2 :=
      match H_LE1 as Hle in le _ m1 return forall H_LE2 : n1 <= m1, Hle = H_LE2 with
      | le_n _ =>
        fun Hle2 : n1 <= n1 =>
        match Hle2 as Hle in le _ m2 return forall H_EQ : n1 = m2, eq_ind n1 (le n1) (le_n n1) m2 H_EQ = Hle with
        | le_n _ => _
        | le_S _ m2' H_LE2' => _
        end (eq_reflexivity n1)
      | le_S _ m1' H_LE1' =>
        fun H_LE2 : n1 <= S m1' =>
        match H_LE2 as Hle in le _ m2 return forall H_EQ : m2 = S m1', le_S n1 m1' H_LE1' = eq_ind m2 (le n1) Hle (S m1') H_EQ with
        | le_n _ => _
        | le_S _ m2' H_LE2' => _
        end (eq_reflexivity (S m1'))
      end
    ).
    - intros H_EQ.
      rewrite (eqnat_proof_irrelevance n1 n1 H_EQ (eq_reflexivity n1)).
      exact (eq_reflexivity (le_n n1)).
    - intros H_EQ.
      assert (Hlt : m2' < n1) by now rewrite H_EQ; constructor.
      contradiction (le_gt_False n1 m2' H_LE2' Hlt).
    - intros H_EQ.
      assert (Hlt : m1' < n1) by now rewrite H_EQ; constructor.
      contradiction (le_gt_False n1 m1' H_LE1' Hlt).
    - intros H_EQ.
      assert (Heq : m2' = m1') by exact (S_eq_S_elim m2' m1' H_EQ).
      subst m1'.
      rewrite (eqnat_proof_irrelevance (S m2') (S m2') H_EQ (eq_reflexivity (S m2'))).
      apply (eq_congruence (le_S n1 m2')).
      exact (lenat_proof_irrelevance_fix m2' H_LE1' H_LE2').
  Qed.

  End ARITHMETIC_PIRREL.

  Section MyFinSet.

  Inductive FinSet : nat -> Set :=
  | FZ : forall n : nat, FinSet (S n) 
  | FS : forall n : nat, FinSet n -> FinSet (S n)
  .

  Definition FinSet_case0 {P : FinSet O -> Type} : forall i : FinSet O, P i :=
    fun i : FinSet O =>
    match i as i0 in FinSet Sn return Sn = O -> P i with
    | FZ n => S_eq_0_elim n
    | FS n i' => S_eq_0_elim n
    end (eq_reflexivity O)
  .

  Definition FinSet_caseS {n : nat} {P : FinSet (S n) -> Type} : P (FZ n) -> (forall i' : FinSet n, P (FS n i')) -> (forall i : FinSet (S n), P i) :=
    fun PZ : P (FZ n) =>
    fun PS : forall i' : FinSet n, P (FS n i') =>
    fun i : FinSet (S n) =>
    match i as i0 in FinSet Sn0 return (match Sn0 as Sn1 return FinSet Sn1 -> Type with O => fun i1 : FinSet O => 2 + 2 = 5 | S n0 => fun i1 : FinSet (S n0) => forall P0 : FinSet (S n0) -> Type, P0 (FZ n0) -> (forall i' : FinSet n0, P0 (FS n0 i')) -> P0 i1 end) i0 with
    | FZ n0 =>
      fun P0 : FinSet (S n0) -> Type =>
      fun PZ0 : P0 (FZ n0) =>
      fun PS0 : forall i' : FinSet n0, P0 (FS n0 i') =>
      PZ0
    | FS n0 i' =>
      fun P0 : FinSet (S n0) -> Type =>
      fun PZ0 : P0 (FZ n0) =>
      fun PS0 : forall i' : FinSet n0, P0 (FS n0 i') =>
      PS0 i'
    end P PZ PS
  .

  Definition FinSet_rectS {P : forall n : nat, FinSet n -> Type} : (forall n : nat, P (S n) (FZ n)) -> (forall n : nat, forall i' : FinSet n, P n i' -> P (S n) (FS n i')) -> (forall n : nat, forall i : FinSet (S n), P (S n) i) :=
    fun PZ : forall n : nat, P (S n) (FZ n) =>
    fun PS : forall n : nat, forall i' : FinSet n, P n i' -> P (S n) (FS n i') =>
    fix FinSet_rectS_fix (n : nat) (i : FinSet (S n)) {struct i} : P (S n) i :=
    match i as i0 in FinSet Sn0 return P Sn0 i0 with
    | FZ n0 => PZ n0
    | FS n0 i' =>
      match n0 as n1 return forall i0' : FinSet n1, P (S n1) (FS n1 i0') with
      | O => FinSet_case0
      | S n0' =>
        fun i0' : FinSet (S n0') =>
        PS (S n0') i0' (FinSet_rectS_fix n0' i0')
      end i'
    end
  .

  Definition mkFinSet : forall n : nat, forall i : nat, i < n -> FinSet n :=
    fix mkFinSet_fix (n : nat) {struct n} : forall i : nat, i < n -> FinSet n :=
    match n as n0 return forall i : nat, i < n0 -> FinSet n0 with
    | O => lt_elim_n_lt_0
    | S n' =>
      fun i : nat =>
      match i as i0 return i0 < S n' -> FinSet (S n') with
      | O =>
        fun H : O < S n' =>
        FZ n'
      | S i' =>
        fun H : S i' < S n' =>
        FS n' (mkFinSet_fix n' i' (lt_elim_S_n_lt_S_m i' n' H))
      end
    end
  .

  Definition runFinSet : forall n : nat, FinSet n -> {m : nat | m < n} :=
    fix runFinSet_fix (n : nat) (i : FinSet n) {struct i} : sig (fun m_ : nat => S m_ <= n) :=
    match i in FinSet Sn' return sig (fun m_ : nat => S m_ <= Sn') with
    | FZ n' => exist (fun m_ : nat => S m_ <= S n') O (lt_intro_0_lt_S_n n')
    | FS n' i' =>
      match runFinSet_fix n' i' return sig (fun m_ : nat => S m_ <= S n') with
      | exist _ m H => exist (fun m_ : nat => S m_ <= S n') (S m) (lt_intro_S_m_lt_S_n m n' H)
      end
    end
  .

  Definition FZ_eq_FS_elim : forall n : nat, forall i : FinSet n, FZ n = FS n i -> False :=
    fun n : nat =>
    fun i : FinSet n =>
    eq_ind (FZ n) (fun FS_n_i_ : FinSet (S n) => match FS_n_i_ return Prop with | FZ n_ => True | FS n_ i_ => False end) I (FS n i)
  .

  Definition FS_eq_FZ_elim : forall n : nat, forall i : FinSet n, FS n i = FZ n -> False :=
    fun n : nat =>
    fun i : FinSet n =>
    eq_ind (FS n i) (fun FS_n_i_ : FinSet (S n) => match FS_n_i_ return Prop with | FZ n_ => False | FS n_ i_ => True end) I (FZ n)
  .

  Definition FS_eq_FS_elim : forall n : nat, forall i1 : FinSet n, forall i2 : FinSet n, FS n i1 = FS n i2 -> i1 = i2 :=
    fun n : nat =>
    fun i : FinSet n =>
    fun j : FinSet n =>
    eq_ind (FS n i) (fun FS_n_j_ : FinSet (S n) => (match FS_n_j_ in FinSet S_n_ return FinSet (pred S_n_) -> Prop with | FZ n_ => fun i_ : FinSet n_ => 2 + 2 = 5 | FS n_ j_ => fun i_ : FinSet n_ => i_ = j_ end) i) (eq_reflexivity i) (FS n j)
  .

  Let FinSet_eq_dec_aux1 : forall n : nat, forall j : FinSet (S n), {FZ n = j} + {FZ n <> j} :=
    fun n : nat =>
    FinSet_caseS (left (eq_reflexivity (FZ n))) (fun j' : FinSet n => right (FZ_eq_FS_elim n j'))
  .

  Let FinSet_eq_dec_aux2 : forall n : nat, (forall i' : FinSet n, forall j' : FinSet n, {i' = j'} + {i' <> j'}) -> forall i' : FinSet n, forall j : FinSet (S n), {FS n i' = j} + {FS n i' <> j} :=
    fun n : nat =>
    fun IH_i' : forall i' : FinSet n, forall j' : FinSet n, sumbool (i' = j') (i' = j' -> False) =>
    fun i' : FinSet n =>
    FinSet_caseS (right (FS_eq_FZ_elim n i')) (fun j' : FinSet n => match IH_i' i' j' return sumbool (FS n i' = FS n j') (FS n i' = FS n j' -> False) with | left Heq => left (eq_congruence (FS n) i' j' Heq) | right Hne => right (fun Heq : FS n i' = FS n j' => Hne (FS_eq_FS_elim n i' j' Heq)) end)
  .

  Definition FinSet_eq_dec : forall n : nat, forall i1 : FinSet n, forall i2 : FinSet n, {i1 = i2} + {i1 <> i2} :=
    fix FinSet_eq_dec_fix (n : nat) {struct n} : forall i : FinSet n, forall j : FinSet n, sumbool (i = j) (i = j -> False) :=
    match n as n0 return forall i : FinSet n0, forall j : FinSet n0, sumbool (i = j) (i = j -> False) with
    | O => FinSet_case0
    | S n' => FinSet_caseS (FinSet_eq_dec_aux1 n') (FinSet_eq_dec_aux2 n' (FinSet_eq_dec_fix n'))
    end
  .

  Definition mkFinSet_ext : forall n : nat, forall i : nat, forall Hlt1 : i < n, forall Hlt2 : i < n, mkFinSet n i Hlt1 = mkFinSet n i Hlt2 :=
    fix mkFinSet_ext_fix (n : nat) {struct n} : forall i : nat, forall Hlt1 : i < n, forall Hlt2 : i < n, mkFinSet n i Hlt1 = mkFinSet n i Hlt2 :=
    match n as n0 return forall i : nat, forall Hlt1 : i < n0, forall Hlt2 : i < n0, mkFinSet n0 i Hlt1 = mkFinSet n0 i Hlt2 with
    | O =>
      fun i : nat =>
      fun Hlt1 : i < O =>
      lt_elim_n_lt_0 i Hlt1
    | S n' =>
      fun i : nat =>
      match i as i0 return forall Hlt1 : i0 < S n', forall Hlt2 : i0 < S n', mkFinSet (S n') i0 Hlt1 = mkFinSet (S n') i0 Hlt2 with
      | O =>
        fun Hlt1 : O < S n' =>
        fun Hlt2 : O < S n' =>
        eq_reflexivity (FZ n')
      | S i' =>
        fun Hlt1 : S i' < S n' =>
        fun Hlt2 : S i' < S n' =>
        eq_congruence (FS n') (mkFinSet n' i' (lt_elim_S_n_lt_S_m i' n' Hlt1)) (mkFinSet n' i' (lt_elim_S_n_lt_S_m i' n' Hlt2)) (mkFinSet_ext_fix n' i' (lt_elim_S_n_lt_S_m i' n' Hlt1) (lt_elim_S_n_lt_S_m i' n' Hlt2))
      end
    end
  .

  Lemma mkFinSet_runFinSet_identity (n : nat) :
    forall i : FinSet n,
    mkFinSet n (proj1_sig (runFinSet n i)) (proj2_sig (runFinSet n i)) = i.
  Proof.
    induction i as [n' | n' i' IH].
    - reflexivity.
    - transitivity (FS n' (mkFinSet n' (proj1_sig (runFinSet n' i')) (proj2_sig (runFinSet n' i')))).
      + simpl.
        destruct (runFinSet n' i') as [m Hlt].
        simpl in *.
        apply (eq_congruence (FS n')).
        exact (mkFinSet_ext n' m (lt_elim_S_n_lt_S_m m n' (lt_intro_S_m_lt_S_n m n' Hlt)) Hlt).
      + apply (eq_congruence (FS n')).
        exact IH.
  Qed.

  Lemma runFinSet_mkFinSet_identity :
    forall m : nat,
    forall n : nat,
    forall Hlt : m < n,
    runFinSet n (mkFinSet n m Hlt) = exist (fun x : nat => x < n) m Hlt.
  Proof.
    induction m as [| m IH]; intros [| n'] Hlt; simpl in *.
    - exact (lt_elim_n_lt_0 0 Hlt).
    - rewrite (lenat_proof_irrelevance 1 (S n') (lt_intro_0_lt_S_n n') Hlt).
      reflexivity.
    - exact (lt_elim_n_lt_0 (S m) Hlt).
    - rewrite (IH n' (lt_elim_S_n_lt_S_m m n' Hlt)).
      rewrite (lenat_proof_irrelevance (S (S m)) (S n') (lt_intro_S_m_lt_S_n m n' (lt_elim_S_n_lt_S_m m n' Hlt)) Hlt).
      reflexivity.
  Qed.

  Definition evalFinSet {n : nat} : FinSet n -> nat :=
    fun i : FinSet n =>
    proj1_sig (runFinSet n i)
  .

  Definition evalFinSet_caseFZ {n : nat} :
    @evalFinSet (S n) (FZ n) = 0.
  Proof.
    exact (eq_reflexivity 0).
  Defined.

  Definition evalFinSet_caseFS {n : nat} :
    forall i : FinSet n,
    @evalFinSet (S n) (FS n i) = 1 + @evalFinSet n i.
  Proof.
    unfold evalFinSet.
    induction i as [n | n i IH]; simpl.
    - exact (eq_reflexivity 1).
    - destruct (runFinSet n i) as [m Hlt].
      exact (eq_reflexivity (2 + m)).
  Defined.

  Definition evalFinSet_lt {n : nat} :
    forall i : FinSet n,
    @evalFinSet n i < n.
  Proof.
    exact (fun i : FinSet n => proj2_sig (runFinSet n i)).
  Defined.

  Theorem evalFinSet_spec :
    forall n : nat,
    forall i : FinSet n,
    forall m : nat,
    forall Hlt : m < n,
    (@evalFinSet n i = m) <-> (mkFinSet n m Hlt = i).
  Proof.
    unfold evalFinSet.
    intros n i m Hlt.
    split.
    - intros Heq.
      subst m.
      rewrite (lenat_proof_irrelevance (S (proj1_sig (runFinSet n i))) n Hlt (proj2_sig (runFinSet n i))).
      exact (mkFinSet_runFinSet_identity n i).
    - intros Heq.
      subst i.
      rewrite (runFinSet_mkFinSet_identity m n Hlt).
      reflexivity.
  Qed.

  Lemma evalFinSet_inj {n : nat} :
    forall i1 : FinSet n,
    forall i2 : FinSet n,
    @evalFinSet n i1 = @evalFinSet n i2 ->
    i1 = i2.
  Proof.
    assert (claim1 := fun i1 : FinSet n => fun i2 : FinSet n => proj1 (evalFinSet_spec n i1 (@evalFinSet n i2) (@evalFinSet_lt n i2))).
    intros i1 i2 Heq.
    rewrite <- (claim1 i1 i2 Heq).
    exact (claim1 i2 i2 (eq_reflexivity (evalFinSet i2))).
  Qed.

  Definition safe_nth {A : Type} : forall xs : list A, FinSet (length xs) -> A :=
    fix safe_nth_fix (xs : list A) {struct xs} : FinSet (length xs) -> A :=
    match xs as xs0 return FinSet (length xs0) -> A with
    | [] => FinSet_case0
    | x' :: xs' => FinSet_caseS x' (safe_nth_fix xs')
    end
  .

  Lemma safe_nth_spec {A : Type} :
    forall xs : list A,
    forall i : FinSet (length xs),
    Some (safe_nth xs i) = nth_error xs (evalFinSet i).
  Proof.
    induction xs as [| x xs IH].
    - exact FinSet_case0.
    - simpl.
      apply FinSet_caseS; simpl.
      + exact (eq_reflexivity (Some x)).
      + intros i.
        rewrite (@evalFinSet_caseFS (length xs) i).
        exact (IH i).
  Qed.

  Definition castFinSet {m : nat} {n : nat} : FinSet m -> m = n -> FinSet n :=
    fun i : FinSet m =>
    eq_rec m FinSet i n
  .

  Lemma castFinSet_spec {n : nat} :
    forall m : nat,
    forall Heq : n = m,
    forall i : FinSet n,
    evalFinSet (castFinSet i Heq) = evalFinSet i.
  Proof.
    apply (ind_eq_l n (fun m : nat => fun Heq : n = m => forall i : FinSet n, evalFinSet (castFinSet i Heq) = evalFinSet i)).
    exact (fun i : FinSet n => eq_reflexivity (@evalFinSet n i)).
  Qed.

  Lemma castFinSet_FZ :
    forall m : nat,
    forall n : nat,
    forall H_EQ : m = n,
    castFinSet (FZ m) (eq_congruence S m n H_EQ) = FZ n.
  Proof.
    intros m.
    apply ind_eq_l.
    exact (eq_reflexivity (FZ m)).
  Qed.

  Lemma castFinSet_FS :
    forall m : nat,
    forall n : nat,
    forall H_EQ : m = n,
    forall i : FinSet m,
    castFinSet (FS m i) (eq_congruence S m n H_EQ) = FS n (castFinSet i H_EQ).
  Proof.
    intros m n H_EQ.
    pattern n, H_EQ.
    revert n H_EQ.
    apply ind_eq_l.
    exact (fun i : FinSet m => eq_reflexivity (FS m i)).
  Qed.

  Lemma safe_nth_map {A : Type} {B : Type} :
    forall f : A -> B,
    forall xs : list A,
    forall i : FinSet (length (map f xs)),
    f (safe_nth xs (castFinSet i (map_length f xs))) = safe_nth (map f xs) i.
  Proof.
    intros f.
    set (my_map_length := list_ind (fun xs : list A => length (map f xs) = length xs) (eq_reflexivity O) (fun _ : A => fun xs : list A => eq_congruence S (length (map f xs)) (length xs))).
    intros xs.
    replace (map_length f xs) with (my_map_length xs).
    - induction xs as [| x xs IH]; simpl.
      + apply FinSet_case0.
      + apply FinSet_caseS.
        { rewrite (castFinSet_FZ (length (map f xs)) (length xs) (my_map_length xs)).
          exact (eq_reflexivity (f x)).
        }
        { intros i.
          rewrite (castFinSet_FS (length (map f xs)) (length xs) (my_map_length xs) i).
          exact (IH i).
        }
    - apply eqnat_proof_irrelevance.
  Qed.

  Definition liftFinSet : forall m : nat, forall n : nat, FinSet n -> FinSet (n + m) :=
    fun m : nat =>
    fix liftFinSet_fix (n : nat) (i : FinSet n) {struct i} : FinSet (n + m) :=
    match i in FinSet Sn0 return FinSet (Sn0 + m) with
    | FZ n0 => FZ (n0 + m)
    | FS n0 i' => FS (n0 + m) (liftFinSet_fix n0 i')
    end
  .

  Lemma liftFinSet_spec :
    forall m : nat,
    forall n : nat,
    forall i : FinSet n,
    evalFinSet (liftFinSet m n i) = evalFinSet i.
  Proof.
    intros m n i.
    apply (proj2 (evalFinSet_spec (n + m) (liftFinSet m n i) (evalFinSet i) (le_transitivity (@evalFinSet_lt n i) (le_intro_plus1 n m)))).
    induction i as [n' | n' i' IH].
    - exact (eq_reflexivity (liftFinSet m (S n') (FZ n'))).
    - apply (proj1 (evalFinSet_spec (S n' + m) (liftFinSet m (S n') (FS n' i')) (evalFinSet (FS n' i')) (le_transitivity (evalFinSet_lt (FS n' i')) (le_intro_plus1 (S n') m)))).
      simpl.
      rewrite (evalFinSet_caseFS (liftFinSet m n' i')).
      rewrite (evalFinSet_caseFS i').
      simpl.
      apply (eq_congruence S).
      exact (proj2 (evalFinSet_spec (n' + m) (liftFinSet m n' i') (evalFinSet i') (le_transitivity (evalFinSet_lt i') (le_intro_plus1 n' m))) IH).
  Qed.

  Definition incrFinSet {m : nat} : forall n : nat, FinSet m -> FinSet (n + m) :=
    fix incrFinSet_fix (n : nat) {struct n} : FinSet m -> FinSet (n + m) :=
    fun i : FinSet m =>
    match n as n0 return FinSet (n0 + m) with
    | O => i
    | S n' => FS (n' + m) (incrFinSet_fix n' i)
    end
  .

  Lemma incrFinSet_spec :
    forall n : nat,
    forall m : nat,
    forall i : FinSet m,
    evalFinSet (incrFinSet n i) = n + evalFinSet i.
  Proof.
    induction n as [| n IH]; intros m i; simpl.
    - exact (eq_reflexivity (evalFinSet i)).
    - rewrite <- (IH m i).
      exact (evalFinSet_caseFS (incrFinSet n i)).
  Qed.

  Let eqFinSet_em : forall n : nat, forall i1 : FinSet n, forall i2 : FinSet n, i1 = i2 \/ i1 <> i2 :=
    fun n : nat =>
    fun i1 : FinSet n =>
    fun i2 : FinSet n =>
    match FinSet_eq_dec n i1 i2 return i1 = i2 \/ i1 <> i2 with
    | left H_yes => or_introl H_yes
    | right H_no => or_intror H_no
    end
  .

  Definition eqFinSet_proof_irrelevance {n : nat} : forall i1 : FinSet n, forall i2 : FinSet n, forall H_EQ1 : i1 = i2, forall H_EQ2 : i1 = i2, H_EQ1 = H_EQ2 :=
    fun i : FinSet n =>
    eq_em_implies_eq_pirrel i (eqFinSet_em n i)
  .

  End MyFinSet.

  Lemma greater_than_iff :
    forall x : nat,
    forall y : nat,
    x > y <-> (exists z : nat, x = S (y + z)).
  Proof with try (lia || eauto).
    intros x y.
    split.
    - intros Hgt.
      induction Hgt as [| m Hgt [z Heq]]; [exists 0 | rewrite Heq]...
    - intros [z Heq]...
  Qed.

  Lemma div_mod_uniqueness :
    forall a : nat,
    forall b : nat,
    forall q : nat,
    forall r : nat,
    a = b * q + r ->
    r < b ->
    a / b = q /\ a mod b = r.
  Proof with try (lia || now (firstorder; eauto)).
    intros a b q r H H0.
    assert (claim1 : a = b * (a / b) + (a mod b)) by now apply (Nat.div_mod a b); lia.
    assert (claim2 : 0 <= a mod b /\ a mod b < b) by now apply (Nat.mod_bound_pos a b); lia.
    assert (claim3 : ~ q > a / b).
    { intros H1.
      destruct (proj1 (greater_than_iff q (a / b)) H1) as [z H2].
      enough (so_we_obatain : b * q + r >= b * S (a / b) + r)...
    }
    assert (claim4 : ~ q < a / b).
    { intros H1.
      destruct (proj1 (greater_than_iff (a / b) q) H1) as [z H2].
      enough (so_we_obtain : b * q + a mod b >= b * S (a / b) + a mod b)...
    }
    enough (therefore : q = a / b)...
  Qed.

  Definition first_nat : (nat -> bool) -> nat -> nat :=
    fun p : nat -> bool =>
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
      destruct (n_le_m_or_m_lt_n_holds_for_any_n_and_any_m x y).
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

  Lemma sum_from_0_to_is :
    forall n : nat,
    2 * sum_from_0_to n = n * (S n).
  Proof with lia.
    induction n; simpl in *...
  Qed.

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

  Lemma cantor_pairing_is_surjective :
    forall x : nat,
    forall y : nat,
    (x, y) = cantor_pairing (sum_from_0_to (x + y) + y).
  Proof with (lia || eauto).
    enough (forall z : nat, forall y : nat, forall x : nat, z = x + y -> (x, y) = cantor_pairing (sum_from_0_to z + y)) by firstorder.
    induction z.
    - intros y x H.
      assert (H0 : x = 0) by lia.
      assert (H1 : y = 0) by lia.
      subst...
    - induction y; intros x H.
      + assert (Heq : x = S z) by lia.
        subst.
        simpl.
        destruct (cantor_pairing (z + sum_from_0_to z + 0)) as [x y] eqn: H0.
        assert (H1 : (0, z) = cantor_pairing (sum_from_0_to z + z))...
        rewrite Nat.add_0_r, Nat.add_comm in H0.
        rewrite H0 in H1.
        inversion H1; subst...
      + assert (H0 : (S x, y) = cantor_pairing (sum_from_0_to (S z) + y)) by now apply (IHy (S x)); lia.
        assert (H1 : z + sum_from_0_to z + S y = sum_from_0_to (S z) + y) by now simpl.
        simpl.
        rewrite H1, <- H0...
  Qed.

  Lemma cantor_pairing_is_injective :
    forall n : nat,
    forall x : nat,
    forall y : nat,
    cantor_pairing n = (x, y) ->
    n = sum_from_0_to (x + y) + y.
  Proof with (lia || eauto).
    induction n; simpl.
    - intros x y H.
      inversion H; subst...
    - intros x y H.
      destruct (cantor_pairing n) as [[| x'] y'] eqn: H0; inversion H; subst.
      + do 2 rewrite Nat.add_0_r.
        simpl.
        rewrite (IHn 0 y' eq_refl), Nat.add_0_l...
      + assert (H1 : forall x' : nat, S x' + y' = x' + S y') by lia.
        rewrite (IHn (S x) y' eq_refl), (H1 x)...
  Qed.

  Theorem cantor_pairing_spec :
    forall n : nat,
    forall x : nat,
    forall y : nat,
    cantor_pairing n = (x, y) <-> n = sum_from_0_to (x + y) + y.
  Proof.
    intros n x y.
    split.
    - exact (cantor_pairing_is_injective n x y).
    - intros Heq.
      subst n.
      symmetry.
      exact (cantor_pairing_is_surjective x y).
  Qed.

  Lemma forallb_true_iff {A : Type} (p : A -> bool) :
    forall xs : list A,
    forallb p xs = true <-> (forall x : A, In x xs -> p x = true).
  Proof with try now firstorder.
    induction xs as [| x xs IH]; simpl...
    rewrite andb_true_iff.
    split...
    intros [H H0] x0 [H1 | H1]; [rewrite H1 in H | apply IH]...
  Qed.

  Definition fold_right_max_0 : list nat -> nat :=
    fold_right max 0
  .

  Lemma fold_right_max_0_in :
    forall ns : list nat,
    forall n : nat,
    In n ns ->
    fold_right_max_0 ns >= n.
  Proof with (lia || eauto).
    unfold fold_right_max_0.
    induction ns as [| n' ns]; simpl...
    intros n [H | H]...
    enough (fold_right max 0 ns >= n)...
  Qed.

  Lemma fold_right_max_0_app :
    forall ns1 : list nat,
    forall ns2 : list nat,
    fold_right_max_0 (ns1 ++ ns2) = max (fold_right_max_0 ns1) (fold_right_max_0 ns2).
  Proof with (lia || eauto).
    unfold fold_right_max_0.
    induction ns1 as [| n1 ns1 IH]; simpl... 
    intros n.
    rewrite IH...
  Qed.

  Lemma property1_of_fold_right_max_0 (Phi : nat -> Prop) (Phi_dec : forall i : nat, {Phi i} + {~ Phi i}) :
    forall ns : list nat,
    (forall i : nat, Phi i -> In i ns) ->
    forall n : nat,
    Phi n ->
    fold_right max 0 ns >= n.
  Proof with try now (lia || firstorder; eauto).
    induction ns; simpl...
    intros H n H0.
    destruct (n_le_m_or_m_lt_n_holds_for_any_n_and_any_m n a)...
    enough (fold_right max 0 ns >= n)...
    destruct (Phi_dec n)...
    destruct (H n p)...
    enough (forall ks : list nat, forall k : nat, In k ks -> fold_right max 0 ks >= k)...
    induction ks; simpl...
    intros k [H2 | H2]...
    enough (fold_right Init.Nat.max 0 ks >= k)...
  Qed.

  Lemma property2_of_fold_right_max_0 :
    forall ns : list nat,
    forall n : nat,
    fold_right max 0 ns > n <-> (exists i : nat, In i ns /\ i > n).
  Proof with try now (lia || firstorder; eauto).
    induction ns; simpl...
    intros n.
    destruct (n_le_m_or_m_lt_n_holds_for_any_n_and_any_m a (fold_right Init.Nat.max 0 ns)); split.
    - intros H.
      assert (H0 : fold_right Init.Nat.max 0 ns > n)...
    - intros [i [[H | H] H0]]...
      enough (fold_right max 0 ns > n)...
    - intros H.
      exists a...
    - intros [i [[H | H] H0]]...
      enough (fold_right Init.Nat.max 0 ns > n)...
  Qed.

  Definition property3_of_fold_right_max_0 :
    forall ns1 : list nat,
    forall ns2 : list nat,
    fold_right max 0 (ns1 ++ ns2) = max (fold_right max 0 ns1) (fold_right max 0 ns2).
  Proof.
    exact fold_right_max_0_app.
  Defined.

  Lemma property4_of_fold_right_max_0 :
    forall ns : list nat,
    forall n : nat,
    In n ns ->
    fold_right max 0 ns >= n.
  Proof with try now (lia || firstorder; eauto).
    induction ns; simpl...
    intros n [H | H]...
    enough (fold_right max 0 ns >= n)...
  Qed.

  Lemma property5_of_fold_right_max_0 :
    forall ns1 : list nat,
    forall ns2 : list nat,
    (forall n : nat, In n ns1 -> In n ns2) ->
    fold_right max 0 ns1 <= fold_right max 0 ns2.
  Proof with try now (lia || firstorder; eauto).
    induction ns1; simpl...
    intros ns2 H.
    destruct (n_le_m_or_m_lt_n_holds_for_any_n_and_any_m a (fold_right max 0 ns1)).
    - enough (fold_right max 0 ns1 <= fold_right max 0 ns2)...
    - enough (a <= fold_right max 0 ns2)...
      apply property4_of_fold_right_max_0...
  Qed.

  Lemma fold_right_max_0_ext :
    forall ns1 : list nat,
    forall ns2 : list nat,
    (forall n : nat, In n ns1 <-> In n ns2) ->
    fold_right max 0 ns1 = fold_right max 0 ns2.
  Proof with try now firstorder.
    intros ns1 ns2 H.
    enough (fold_right max 0 ns1 <= fold_right max 0 ns2 /\ fold_right max 0 ns2 <= fold_right max 0 ns1) by lia.
    split; apply property5_of_fold_right_max_0...
  Qed.

  Lemma in_remove_iff {A : Type} (A_eq_dec : forall x1 : A, forall x2 : A, {x1 = x2} + {x1 <> x2}) :
    forall x : A,
    forall x0 : A,
    forall xs : list A,
    In x (remove A_eq_dec x0 xs) <-> (In x xs /\ x <> x0).
  Proof with firstorder.
    assert (claim1 := in_remove A_eq_dec).
    assert (claim2 := in_in_remove A_eq_dec)...
  Qed.

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

  Definition fmapMaybe {A : Type} {B : Type} : (A -> B) -> (option A -> option B) :=
    fun f : A -> B =>
    fun x : option A =>
    match x return option B with
    | None => None
    | Some x' => Some (f x')
    end
  .

  Definition maybe {A : Type} {B : Type} : B -> (A -> B) -> option A -> B :=
    fun NONE_A : B =>
    fun SOME_A : A -> B =>
    fun OPTION_A : option A =>
    match OPTION_A with
    | None => NONE_A
    | Some a => SOME_A a
    end
  .

  Definition injSome {A : Type} : forall x : A, forall y : A, Some x = Some y -> x = y :=
    fun x : A =>
    fun y : A =>
    eq_congruence (maybe y id) (Some x) (Some y)
  .

  Definition Some_ne_None {A : Type} : forall x : A, Some x <> None :=
    fun x : A =>
    fun H_eq : Some x = None =>
    @transport (option A) (maybe False (fun _ : A => True)) (Some x) None H_eq I
  .

  Definition elemIndex {A : Type} : forall x : A, (forall x' : A, {x = x'} + {x <> x'}) -> forall xs : list A, option (FinSet (length xs)) :=
    fun x : A =>
    fun eq_dec : forall x' : A, {x = x'} + {x <> x'} =>
    fix elemIndex_fix (xs : list A) {struct xs} : option (FinSet (length xs)) :=
    match xs as xs0 return option (FinSet (length xs0)) with
    | [] => None
    | x' :: xs' => if eq_dec x' then Some (FZ (length xs')) else fmapMaybe (FS (length xs')) (elemIndex_fix xs')
    end
  .

  Definition fromJust {A : Type} : forall Some_x : option A, Some_x <> None -> A :=
    fun Some_x : option A =>
    match Some_x as Some_x0 return Some_x0 <> None -> A with
    | None => fun H_no : None <> None => False_rect A (H_no (eq_reflexivity None))
    | Some x => fun _ : Some x <> None => x
    end
  .

  Lemma fromJust_spec {A : Type} :
    forall Some_x : option A,
    forall x : A,
    Some_x = Some x <-> (exists H_no : Some_x <> None, x = fromJust Some_x H_no).
  Proof with eauto.
    intros Some_x x.
    split.
    - intros H_yes.
      subst Some_x.
      exists (Some_ne_None x).
      reflexivity.
    - intros [H_no H_eq].
      subst x.
      destruct Some_x as [x |].
      + reflexivity.
      + contradiction.
  Qed.

  Global Ltac repeat_rewrite :=
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

  Global Ltac auto_rewrite :=
    repeat repeat_rewrite; repeat (try intro; try repeat_rewrite; try now (subst; firstorder))
  .

  Section SET_LEVEL_LE.

  Inductive leq (n : nat) : nat -> Set :=
  | leq_init : leq n n
  | leq_step : forall m : nat, leq n m -> leq n (S m)
  .

  Local Hint Constructors leq : core.

  Lemma leq_reflexivity :
    forall n : nat,
    leq n n.
  Proof.
    constructor 1.
  Defined.

  Lemma leq_intro_leq_0_n :
    forall n : nat,
    leq 0 n.
  Proof with eauto.
    induction n as [| n IH]...
  Defined.

  Lemma leq_intro_leq_S_n_S_m :
    forall n : nat,
    forall m : nat,
    leq n m ->
    leq (S n) (S m).
  Proof with eauto.
    intros n m Hleq.
    induction Hleq as [| m Hleq IH]...
  Defined.

  Lemma leq_transitivity :
    forall n1 : nat,
    forall n2 : nat,
    forall n3 : nat,
    leq n1 n2 ->
    leq n2 n3 ->
    leq n1 n3.
  Proof with eauto.
    intros n1 n2 n3 Hle1 Hle2.
    revert n3 n2 n1 Hle2 Hle1.
    induction n3; intros n2 n1 Hle2 Hle1; inversion Hle2; subst...
  Defined.

  Local Hint Resolve leq_transitivity : core.

  Theorem accumulation_leq (phi : nat -> Type) :
    (forall n : nat, (forall i : nat, leq i n -> i <> n -> phi i) -> phi n) ->
    forall n : nat,
    phi n.
  Proof with (congruence || eauto).
    intros acc_hyp.
    enough (it_is_sufficient_to_show : forall n : nat, forall i : nat, leq i n -> phi i)...
    induction n; intros m leq_m_n; apply acc_hyp; intros i leq_i_m H_ne; inversion leq_i_m; subst...
    all: inversion leq_m_n; subst...
  Defined.

  Lemma leq_implies_le :
    forall n : nat,
    forall m : nat,
    leq n m ->
    n <= m.
  Proof with eauto.
    intros n m Hleq.
    induction Hleq as [| m Hleq IH]...
  Defined.

  Lemma leq_asymmetry :
    forall n1 : nat,
    forall n2 : nat,
    leq n1 n2 ->
    leq n2 n1 ->
    n1 = n2.
  Proof.
    intros n1 n2 Hleq1 Hleq2.
    apply le_asymmetry.
    - exact (leq_implies_le n1 n2 Hleq1).
    - exact (leq_implies_le n2 n1 Hleq2).
  Defined.

  Lemma le_implies_leq :
    forall n : nat,
    forall m : nat,
    n <= m ->
    leq n m.
  Proof.
    induction n as [| n IH].
    - intros m Hle.
      exact (leq_intro_leq_0_n m).
    - intros [| m'] Hle.
      + exact (lt_elim_n_lt_0 n Hle).
      + exact (leq_intro_leq_S_n_S_m n m' (IH m' (le_elim_S_n_le_m n (S m') Hle))).
  Defined.

  Lemma leq_unique :
    forall n1 : nat,
    forall n2 : nat,
    forall Hleq1 : leq n1 n2,
    forall Hleq2 : leq n1 n2,
    Hleq1 = Hleq2.
  Proof.
    refine (
      fun n1 : nat =>
      fix leq_unique_fix (n2 : nat) (Hleq1 : leq n1 n2) {struct Hleq1} : forall Hleq2 : leq n1 n2, Hleq1 = Hleq2 :=
      match Hleq1 as Hleq in leq _ m1 return forall Hleq2 : leq n1 m1, Hleq = Hleq2 with
      | leq_init _ =>
        fun Hleq2 : leq n1 n1 =>
        match Hleq2 as Hleq in leq _ m2 return forall Heq : n1 = m2, eq_rec n1 (leq n1) (leq_init n1) m2 Heq = Hleq with
        | leq_init _ => _
        | leq_step _ m2' H_LE2' => _
        end (eq_reflexivity n1)
      | leq_step _ m1' Hleq1' =>
        fun Hleq2 : leq n1 (S m1') =>
        match Hleq2 as Hleq in leq _ m2 return forall Heq : m2 = S m1', leq_step n1 m1' Hleq1' = eq_rec m2 (leq n1) Hleq (S m1') Heq with
        | leq_init _ => _
        | leq_step _ m2' Hleq2' => _
        end (eq_reflexivity (S m1'))
      end
    ).
    - intros Heq.
      rewrite (eqnat_proof_irrelevance n1 n1 Heq (eq_reflexivity n1)).
      reflexivity.
    - intros Heq.
      assert (Hlt : m2' < n1) by now rewrite Heq; constructor.
      assert (Hle : n1 <= m2') by now apply leq_implies_le.
      contradiction (le_gt_False n1 m2' Hle Hlt).
    - intros Heq.
      assert (Hlt : m1' < n1) by now rewrite Heq; constructor.
      assert (Hle : n1 <= m1') by now apply leq_implies_le.
      contradiction (le_gt_False n1 m1' Hle Hlt).
    - intros Heq.
      assert (Heq' : m2' = m1') by exact (S_eq_S_elim m2' m1' Heq).
      destruct Heq' as [].
      rewrite (eqnat_proof_irrelevance (S m2') (S m2') Heq (eq_reflexivity (S m2'))).
      apply (eq_congruence (leq_step n1 m2')).
      exact (leq_unique_fix m2' Hleq1' Hleq2').
  Qed.

  Corollary well_founded_recursion_of_nat [phi : nat -> Type] :
    (forall n : nat, (forall i : nat, i < n -> phi i) -> phi n) ->
    (forall n : nat, phi n).
  Proof.
    intros acc_hyp.
    apply accumulation_leq with (phi := phi).
    intros n IH.
    apply acc_hyp.
    intros i H_lt.
    apply IH.
    - apply le_implies_leq.
      exact (le_transitivity (le_S i i (le_n i)) H_lt).
    - intros H_eq; subst n.
      contradiction (not_n_lt_n i).
  Defined.

  End SET_LEVEL_LE.

  Section ACKERMANN.

  Record AckermannFuncSpec (ack : (nat * nat) -> nat) : Prop :=
    { AckermannFunc_spec1 : forall n, ack (0, n) = n + 1
    ; AckermannFunc_spec2 : forall m, ack (m + 1, 0) = ack (m, 1)
    ; AckermannFunc_spec3 : forall m n, ack (m + 1, n + 1) = ack (m, ack (m + 1, n))
    }
  .

  Let AckermannFunc1_aux1 : (nat -> nat) -> nat -> nat :=
    fun kont : nat -> nat =>
    fix AckermannFunc1_aux1_fix (n : nat) {struct n} : nat :=
    match n return nat with
    | O => kont 1
    | S n' => kont (AckermannFunc1_aux1_fix n')
    end
  .

  Let AckermannFunc1_aux2 : nat -> nat -> nat :=
    fix AckermannFunc1_aux2_fix (m : nat) {struct m} : nat -> nat :=
    match m return nat -> nat with
    | O => S
    | S m' => AckermannFunc1_aux1 (AckermannFunc1_aux2_fix m')
    end
  .

  Definition AckermannFunc1 : (nat * nat) -> nat :=
    fun p : nat * nat =>
    AckermannFunc1_aux2 (fst p) (snd p)
  .

  Theorem AckermannFunc1_satisfies_AckermannFuncSpec :
    AckermannFuncSpec AckermannFunc1.
  Proof with (lia || eauto).
    split.
    - intros n; replace (n + 1) with (S n)...
    - intros m; replace (m + 1) with (S m)...
    - intros [| m']; induction n as [| n IHn]; cbn in *...
      all: replace (m' + 1) with (S m') in *...
  Qed.

  End ACKERMANN.

  Section FIBONACCI.

  Lemma n_ne_S_plus_m_n :
    forall m : nat,
    forall n : nat,
    n <> S (m + n).
  Proof.
    intros m n H_eq.
    contradiction (not_n_lt_n n).
    enough (it_is_sufficient_to_show : n < S (m + n)) by congruence.
    apply le_intro_S_n_le_S_m, le_intro_plus2.
  Defined.

  Inductive fibonacci_spec : forall n : nat, forall f_n : nat, Prop :=
  | FibonacciSpec_when_eq_0 :
    fibonacci_spec 0 (0)
  | FibonacciSpec_when_eq_1 :
    fibonacci_spec 1 (1)
  | FibonacciSpec_when_ge_2 :
    forall n : nat,
    forall f_n : nat,
    forall f_n' : nat,
    fibonacci_spec n f_n ->
    fibonacci_spec (S n) f_n' ->
    fibonacci_spec (S (S n)) (f_n + f_n')
  .

  Definition fibonacci :
    forall n : nat,
    {f_n : nat | fibonacci_spec n f_n}.
  Proof.
    apply accumulation_leq with (phi := fun n : nat => {f_n : nat | fibonacci_spec n f_n}).
    intros [| [| n]] acc.
    - exists (0).
      now constructor 1.
    - exists (1).
      now constructor 2.
    - set (acc_n := acc n (leq_step n (S n) (leq_step n n (leq_init n))) (n_ne_S_plus_m_n 1 n)).
      set (acc_n' := acc (S n) (leq_step (S n) (S n) (leq_init (S n))) (n_ne_S_plus_m_n 0 (S n))).
      set (f_n := proj1_sig acc_n).
      set (f_n' := proj1_sig acc_n').
      exists (f_n + f_n').
      now constructor 3; [exact (proj2_sig acc_n) | exact (proj2_sig acc_n')].
  Defined.

  (* Eval compute in proj1_sig (fibonacci 10). = 55 : nat *)

  End FIBONACCI.

  Definition lookup {A : Type} {B : Type} (x : A) (eq_dec : forall y : A, {x = y} + {x <> y}) : list (A * B) -> option B :=
    fix lookup_fix (zs : list (A * B)) {struct zs} : option B :=
    match zs with
    | [] => None
    | z :: zs => if eq_dec (fst z) then Some (snd z) else lookup_fix zs
    end
  .

  Lemma lookup_ne_None_iff {A : Type} {B : Type} (x : A) (eq_dec : forall y : A, {x = y} + {x <> y}) :
    forall zs : list (A * B),
    lookup x eq_dec zs <> None <-> In x (map fst zs).
  Proof.
    induction zs as [| z zs IH]; simpl.
    - tauto.
    - destruct (eq_dec (fst z)) as [H_yes | H_no]; split; intros H.
      + now left.
      + apply Some_ne_None.
      + tauto.
      + now firstorder.
  Qed.

  Definition elemIndex_In {A : Type} (x : A) (eq_dec : forall y : A, {x = y} + {x <> y}) : forall xs : list A, In x xs -> nat :=
    fix elemIndex_In_fix (xs : list A) {struct xs} : In x xs -> nat :=
    match xs as xs0 return In x xs0 -> nat with
    | [] => False_rec nat
    | x' :: xs' =>
      fun H_In : x' = x \/ In x xs' =>
      match eq_dec x' with
      | left H_yes => 0
      | right H_no =>
        let H_In' : In x xs' := or_ind (fun H : x' = x => False_ind (In x xs') (H_no (eq_symmetry x' x H))) (fun H : In x xs' => H) H_In in
        1 + elemIndex_In_fix xs' H_In'
      end
    end
  .

  Lemma elemIndex_In_nth_error {A : Type} (x : A) (eq_dec : forall y : A, {x = y} + {x <> y}) :
    forall xs : list A,
    forall H_In : In x xs,
    nth_error xs (elemIndex_In x eq_dec xs H_In) = Some x.
  Proof.
    induction xs as [| x' xs' IH]; simpl.
    - contradiction.
    - intros [H_eq | H_In']; destruct (eq_dec x') as [H_yes | H_no].
      + now subst x'.
      + now contradiction H_no.
      + now subst x'.
      + exact (IH H_In').
  Qed.

  Lemma list_eq_dec {A : Type} (eq_dec : forall x1 : A, forall x2 : A, {x1 = x2} + {x1 <> x2}) :
    forall xs1 : list A,
    forall xs2 : list A,
    {xs1 = xs2} + {xs1 <> xs2}.
  Proof with ((left; congruence) || (right; congruence)) || eauto.
    induction xs1 as [| x1 xs1 IH]; destruct xs2 as [| x2 xs2]...
    - destruct (eq_dec x1 x2); destruct (IH xs2)...
  Defined.

End MyUtilities.

Module MyUniverses.

  Definition SuperiorUniverse : Type :=
    Type
  .

  Definition InferiorUniverse : SuperiorUniverse :=
    Type
  .

End MyUniverses.

Module MyScratch.

  Import EqFacts MyUtilities.

  Section MyStream.

  Variable A : Type.

  CoInductive Stream : Type :=
    Cons
    { hd : A
    ; tl : Stream
    }
  .

  Definition Stream_corec (X : Type) : (X -> A * X) -> (X -> Stream) :=
    fun acc : X -> A * X =>
    cofix CIH : X -> Stream :=
    fun x : X =>
    {| hd := fst (acc x); tl := CIH (snd (acc x)) |}
  .

  End MyStream.

  Section SYNCHRONOUS_CIRCUIT.

  CoInductive circuit (Input : Type) (Output : Type) : Type :=
    circuit_intro
    { circuit_elim : Input -> (circuit Input Output) * Output
    }
  .

  Definition delayWithInit {I : Type} : I -> circuit I I :=
    cofix delayWithInit_cofix : I -> circuit I I :=
    fun x0 : I =>
    circuit_intro I I (fun x : I => (delayWithInit_cofix x, x0))
  .

  Definition embedFunIntoCircuit {I : Type} {O : Type} : (I -> O) -> circuit I O :=
    fun f : I -> O =>
    cofix embedFunIntoCircuit_cofix : circuit I O :=
    circuit_intro I O (fun x : I => (embedFunIntoCircuit_cofix, f x))
  .

  Definition combineCircuit {I1 : Type} {I2 : Type} {O1 : Type} {O2 : Type} :
    circuit I1 O1 ->
    circuit I2 O2 ->
    circuit (I1 * I2) (O1 * O2).
  Proof.
    cofix combineCircuit_cofix.
    intros circuit1 circuit2.
    apply (circuit_intro (I1 * I2) (O1 * O2)).
    intros p.
    set (p1 := circuit_elim I1 O1 circuit1 (fst p)).
    set (p2 := circuit_elim I2 O2 circuit2 (snd p)).
    exact (combineCircuit_cofix (fst p1) (fst p2), (snd p1, snd p2)).
  Defined.

  End SYNCHRONOUS_CIRCUIT.

  Section CONAT.

  CoInductive conat : Set :=
  | coO : conat
  | coS : conat -> conat
  .

  Fixpoint burn_conat (n : nat) {struct n} : conat -> conat :=
    fun cn : conat =>
    match n with
    | O => cn
    | S n' =>
      match cn with
      | coO => coO
      | coS cn' => coS (burn_conat n' cn')
      end
    end
  .

  Lemma usage_of_burn_conat :
    forall n : nat,
    forall cn : conat,
    burn_conat n cn = cn.
  Proof.
    induction n as [| n IH]; simpl.
    - reflexivity.
    - intros cn.
      destruct cn as [| cn'].
      + exact (eq_reflexivity coO).
      + exact (eq_congruence coS (burn_conat n cn') cn' (IH cn')).
  Qed.

  Local Hint Resolve usage_of_burn_conat : core.

  CoInductive conat_bisim : conat -> conat -> Prop :=
  | bisim_coO :
    conat_bisim coO coO
  | bisim_coS :
    forall cn1 : conat,
    forall cn2 : conat,
    conat_bisim cn1 cn2 ->
    conat_bisim (coS cn1) (coS cn2)
  .

  Local Notation " cn1 =-= cn2 " := (conat_bisim cn1 cn2) (at level 70, no associativity) : type_scope.

  Local Hint Constructors conat_bisim : core.

  Fixpoint to_conat (n : nat) {struct n} : conat :=
    match n with
    | O => coO
    | S n' => coS (to_conat n')
    end
  .

  CoFixpoint infty : conat :=
    coS infty
  .

  End CONAT.

End MyScratch.
