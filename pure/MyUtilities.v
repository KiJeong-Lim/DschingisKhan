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
    eq_ind x1 (fun x : A => x = x1) eq_refl x2
  .

  Definition eq_transitivity : forall x1 : A, forall x2 : A, forall x3 : A, x1 = x2 -> x2 = x3 -> x1 = x3 :=
    fun x1 : A =>
    fun x2 : A =>
    fun x3 : A =>
    fun H : x1 = x2 =>
    eq_ind x2 (fun x : A => x1 = x) H x3
  .

  Context {B : Type}.

  Definition eq_congruence : forall f : A -> B, forall x1 : A, forall x2 : A, x1 = x2 -> f x1 = f x2 :=
    fun f : A -> B =>
    fun x1 : A =>
    fun x2 : A =>
    eq_ind x1 (fun x : A => f x1 = f x) eq_refl x2
  .

  End EQ_CONSTRUCTORS.

  Section EQ_ELIMINATORS.

  Context {A : Type}.

  Definition RuleJ (phi' : forall x0 : A, forall y0 : A, x0 = y0 -> Type) : forall x : A, forall y : A, forall H : x = y, phi' y y eq_refl -> phi' x y H :=
    fun x : A =>
    fun y : A =>
    fun H : eq x y =>
    match H as H0 in eq _ y0 return forall phi : forall x0 : A, forall y0 : A, x0 = y0 -> Type, phi y0 y0 eq_refl -> phi x y0 H0 with
    | eq_refl =>
      fun phi : forall x0 : A, forall y0 : A, x0 = y0 -> Type =>
      fun phi_y : phi x x eq_refl =>
      phi_y
    end phi'
  .

  Definition ind_eq_l (lhs : A) (phi : forall rhs : A, lhs = rhs -> Prop) : phi lhs (eq_reflexivity lhs) -> forall rhs : A, forall H_EQ : lhs = rhs, phi rhs H_EQ :=
    fun phi_lhs : phi lhs (eq_reflexivity lhs) =>
    fun rhs : A =>
    fun H_EQ : lhs = rhs =>
    match H_EQ as H_EQ0 in eq _ lhs0 return phi lhs0 H_EQ0 with
    | eq_refl => phi_lhs
    end
  .

  Definition ind_eq_r (rhs : A) (phi : forall lhs : A, lhs = rhs -> Prop) : phi rhs (eq_reflexivity rhs) -> forall lhs : A, forall H_EQ : lhs = rhs, phi lhs H_EQ :=
    fun phi_rhs : phi rhs (eq_reflexivity rhs) =>
    fun lhs : A =>
    fun H_EQ : lhs = rhs =>
    match H_EQ as H_EQ0 in eq _ rhs0 return forall phi0 : forall lhs0 : A, lhs0 = rhs0 -> Prop, phi0 rhs0 (eq_reflexivity rhs0) -> phi0 lhs H_EQ0 with
    | eq_refl =>
      fun phi0 : forall lhs0 : A, lhs0 = lhs -> Prop =>
      fun phi0_lhs : phi0 lhs (eq_reflexivity lhs) =>
      phi0_lhs
    end phi phi_rhs
  .

  Definition rec_eq_l (lhs : A) (phi : forall rhs : A, lhs = rhs -> Set) : phi lhs (eq_reflexivity lhs) -> forall rhs : A, forall H_EQ : lhs = rhs, phi rhs H_EQ :=
    fun phi_lhs : phi lhs (eq_reflexivity lhs) =>
    fun rhs : A =>
    fun H_EQ : lhs = rhs =>
    match H_EQ as H_EQ0 in eq _ lhs0 return phi lhs0 H_EQ0 with
    | eq_refl => phi_lhs
    end
  .

  Definition rec_eq_r (rhs : A) (phi : forall lhs : A, lhs = rhs -> Set) : phi rhs (eq_reflexivity rhs) -> forall lhs : A, forall H_EQ : lhs = rhs, phi lhs H_EQ :=
    fun phi_rhs : phi rhs (eq_reflexivity rhs) =>
    fun lhs : A =>
    fun H_EQ : lhs = rhs =>
    match H_EQ as H_EQ0 in eq _ rhs0 return forall phi0 : forall lhs0 : A, lhs0 = rhs0 -> Set, phi0 rhs0 (eq_reflexivity rhs0) -> phi0 lhs H_EQ0 with
    | eq_refl =>
      fun phi0 : forall lhs0 : A, lhs0 = lhs -> Set =>
      fun phi0_lhs : phi0 lhs (eq_reflexivity lhs) =>
      phi0_lhs
    end phi phi_rhs
  .

  Definition rect_eq_l (lhs : A) (phi : forall rhs : A, lhs = rhs -> Type) : phi lhs (eq_reflexivity lhs) -> forall rhs : A, forall H_EQ : lhs = rhs, phi rhs H_EQ :=
    fun phi_lhs : phi lhs (eq_reflexivity lhs) =>
    fun rhs : A =>
    fun H_EQ : lhs = rhs =>
    match H_EQ as H_EQ0 in eq _ lhs0 return phi lhs0 H_EQ0 with
    | eq_refl => phi_lhs
    end
  .

  Definition rect_eq_r (rhs : A) (phi : forall lhs : A, lhs = rhs -> Type) : phi rhs (eq_reflexivity rhs) -> forall lhs : A, forall H_EQ : lhs = rhs, phi lhs H_EQ :=
    fun phi_rhs : phi rhs (eq_reflexivity rhs) =>
    fun lhs : A =>
    fun H_EQ : lhs = rhs =>
    match H_EQ as H_EQ0 in eq _ rhs0 return forall phi0 : forall lhs0 : A, lhs0 = rhs0 -> Type, phi0 rhs0 (eq_reflexivity rhs0) -> phi0 lhs H_EQ0 with
    | eq_refl =>
      fun phi0 : forall lhs0 : A, lhs0 = lhs -> Type =>
      fun phi0_lhs : phi0 lhs (eq_reflexivity lhs) =>
      phi0_lhs
    end phi phi_rhs
  .

  End EQ_ELIMINATORS.

  Section EQ_EM_implies_EQ_PIRREL. (* Reference: "https://coq.inria.fr/library/Coq.Logic.Eqdep_dec.html" *)

  Definition eq_round_trip {A : Type} : forall x1 : A, forall x2 : A, forall H : x1 = x2, eq_transitivity x2 x1 x2 (eq_symmetry x1 x2 H) H = eq_reflexivity x2 :=
    fun x1 : A =>
    fun x2 : A =>
    fun H : x1 = x2 =>
    match H as H0 in eq _ x0 return eq_transitivity x0 x1 x0 (eq_symmetry x1 x0 H0) H0 = eq_reflexivity x0 with
    | eq_refl => eq_reflexivity (eq_reflexivity x1)
    end
  .

  Context {A : Type} (x : A).

  Local Ltac elim_eq :=
    let y := fresh "y" in
    let H_EQ := fresh "H_EQ" in
    intros y H_EQ;
    pattern y, H_EQ;
    revert y H_EQ;
    apply (@ind_eq_l A x)
  .

  Section PARAMETERIZED_DECODER.

  Variable eq_encoder : forall y : A, x = y -> x = y.

  Definition eq_decoder : forall y : A, x = y -> x = y :=
    fun y : A =>
    eq_transitivity x x y (eq_symmetry x x (eq_encoder x (eq_reflexivity x)))
  .

  Definition eq_decoder_decodes_for_any_given_eq_encoder :
    forall y : A,
    forall H : x = y,
    eq_decoder y (eq_encoder y H) = H.
  Proof.
    elim_eq.
    exact (eq_round_trip x x (eq_encoder x (eq_reflexivity x))).
  Defined.

  End PARAMETERIZED_DECODER.

  Hypothesis eq_em : forall y : A, x = y \/ x <> y.

  Definition eq_encoder (y : A) : x = y -> x = y :=
    fun H_EQ : x = y =>
    match eq_em y return x = y with
    | or_introl Heq => Heq
    | or_intror Hne => False_ind (x = y) (Hne H_EQ)
    end
  .

  Definition eq_encoder_returns_the_same_result :
    forall y : A,
    forall H_EQ1 : x = y,
    forall H_EQ2 : x = y,
    eq_encoder y H_EQ1 = eq_encoder y H_EQ2.
  Proof.
    elim_eq.
    unfold eq_encoder.
    intros H_EQ.
    destruct (eq_em x) as [Heq | Hne].
    - exact (eq_reflexivity Heq).
    - contradiction (Hne H_EQ).
  Defined.

  Definition eq_em_implies_eq_pirrel :
    forall y : A,
    forall H_EQ1 : x = y,
    forall H_EQ2 : x = y,
    H_EQ1 = H_EQ2.
  Proof.
    intros y H_EQ1 H_EQ2.
    rewrite <- (eq_decoder_decodes_for_any_given_eq_encoder eq_encoder y H_EQ1).
    rewrite <- (eq_decoder_decodes_for_any_given_eq_encoder eq_encoder y H_EQ2).
    apply (eq_congruence (eq_decoder eq_encoder y)).
    exact (eq_encoder_returns_the_same_result y H_EQ1 H_EQ2).
  Defined.

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

  Definition le_reflexivity : forall n1 : nat, n1 <= n1 :=
    le_n
  .

  Let le_transitivity_aux1 : forall n1 : nat, forall n2 : nat, n1 <= n2 -> forall n3 : nat, n2 <= n3 -> n1 <= n3 :=
    fix le_transitivity_aux1_fix (n1 : nat) (n2 : nat) (Hle1 : le n1 n2) {struct Hle1} : forall n3 : nat, n2 <= n3 -> n1 <= n3 :=
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
      le_transitivity_aux1_fix n1 n2' Hle1' n3 claim4
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
    | O =>
      fun Hle : S O <= O =>
      match Hle in le _ m return m = O -> False with
      | le_n _ => S_eq_0_elim O
      | le_S _ m' Hle' => S_eq_0_elim m'
      end (eq_reflexivity O)
    | S n' =>
      fun Hle : S (S n') <= S n' =>
      not_n_lt_n_fix n' (le_elim_S_n_le_m (S n') (S n') Hle)
    end
  .

  Definition le_lt_False : forall m : nat, forall n : nat, m <= n -> n < m -> False :=
    fun m : nat =>
    fix le_lt_False_fix (n : nat) (Hle : m <= n) {struct Hle} : n < m -> False :=
    match Hle in le _ n0 return n0 < m -> False with
    | le_n _ => not_n_lt_n m
    | le_S _ n' Hle' =>
      fun Hlt : S n' < m =>
      le_lt_False_fix n' Hle' (le_transitivity (le_S (S n') (S n') (le_n (S n'))) Hlt)
    end
  .

  Definition le_asymmetry : forall n1 : nat, forall n2 : nat, n1 <= n2 -> n2 <= n1 -> n1 = n2 :=
    fun n1 : nat =>
    fun n2 : nat =>
    fun Hle1 : n1 <= n2 =>
    match Hle1 in le _ m return m <= n1 -> n1 = m with
    | le_n _ =>
      fun Hle2 : n1 <= n1 =>
      eq_reflexivity n1
    | le_S _ m' Hle1' =>
      fun Hle2 : m' < n1 =>
      False_ind (n1 = S m') (le_lt_False n1 m' Hle1' Hle2)
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
        | left Heq =>
          right (eq_ind m (fun x : nat => le (S m) (S x)) (le_n (S m)) n' (eq_symmetry n' m Heq))
        | right Hne =>
          left (n_le_m_and_n_ne_m_implies_n_lt_m n' m Hle Hne)
        end
      | right Hlt =>
        right (le_S (S m) n' Hlt)
      end
    end
  .

  End ARITH_WITHOUT_SOLVER.

  Section STRONG_INDUCTION_ON_nat.

  Context {P : nat -> Prop} (ACC : forall n : nat, (forall m : nat, m < n -> P m) -> P n).

  Let case0 : forall m : nat, forall H : m < O, P m :=
    fun m : nat =>
    fun Hlt : m < O => lt_elim_n_lt_0 m Hlt
  .

  Let caseS : forall n : nat, (forall m : nat, m < n -> P m) -> forall m : nat, m < S n -> P m :=
    fun n : nat =>
    fun IH : forall m : nat, m < n -> P m =>
    fun m : nat =>
    fun Hlt : m < S n =>
    le_inversion (fun n1 : nat => fun n2 : nat => P (pred n1)) (S m) (S n) Hlt (fun Heq : S m = S n => ACC n IH) (fun m' : nat => fun H' : S m <= m' => fun Heq : S m' = S n => IH m (eq_ind m' (le (S m)) H' n (S_eq_S_elim m' n Heq)))
  .

  Definition strong_induction : forall l : nat, P l :=
    fun l : nat =>
    ACC l (nat_ind (fun n : nat => forall m : nat, m < n -> P m) case0 caseS l)
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

  Theorem eqnat_proof_irrelevance :
    forall n1 : nat,
    forall n2 : nat,
    forall H_EQ1 : n1 = n2,
    forall H_EQ2 : n1 = n2,
    H_EQ1 = H_EQ2.
  Proof.
    exact (fun n : nat => eq_em_implies_eq_pirrel n (eqnat_em n)).
  Qed.

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
      reflexivity.
    - intros H_EQ.
      assert (Hlt : m2' < n1) by now rewrite H_EQ; constructor.
      contradiction (le_lt_False n1 m2' H_LE2' Hlt).
    - intros H_EQ.
      assert (Hlt : m1' < n1) by now rewrite H_EQ; constructor.
      contradiction (le_lt_False n1 m1' H_LE1' Hlt).
    - intros H_EQ.
      assert (Heq : m2' = m1') by exact (S_eq_S_elim m2' m1' H_EQ).
      destruct Heq as [].
      rewrite (eqnat_proof_irrelevance (S m2') (S m2') H_EQ (eq_reflexivity (S m2'))).
      apply (eq_congruence (le_S n1 m2')).
      exact (lenat_proof_irrelevance_fix m2' H_LE1' H_LE2').
  Qed.

  End ARITHMETIC_PIRREL.

  Section MyFin.

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

  Definition safe_nth {A : Type} : forall xs : list A, FinSet (length xs) -> A :=
    fix safe_nth_fix (xs : list A) {struct xs} : FinSet (length xs) -> A :=
    match xs as xs0 return FinSet (length xs0) -> A with
    | [] => FinSet_case0
    | x :: xs' => FinSet_caseS x (safe_nth_fix xs')
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

  Lemma evalFinSet_inj :
    forall n : nat,
    forall i1 : FinSet n,
    forall i2 : FinSet n,
    @evalFinSet n i1 = @evalFinSet n i2 ->
    i1 = i2.
  Proof.
    intros n i1 i2 Heq.
    apply (proj1 (evalFinSet_spec n i1 (@evalFinSet n i2) (@evalFinSet_lt n i2))) in Heq.
    subst i1.
    apply (proj1 (evalFinSet_spec n i2 (@evalFinSet n i2) (@evalFinSet_lt n i2))).
    reflexivity.
  Qed.

  Definition castFinSet {m : nat} {n : nat} : FinSet m -> m = n -> FinSet n :=
    fun i : FinSet m =>
    eq_rect m FinSet i n
  .

  Lemma castFinSet_evalFinSet {n : nat} :
    forall m : nat,
    forall i : FinSet n,
    forall Heq : n = m,
    evalFinSet (castFinSet i Heq) = evalFinSet i.
  Proof.
    intros m i Heq.
    now destruct Heq.
  Qed.

  Definition liftFinSet : forall m : nat, forall n : nat, FinSet n -> FinSet (n + m) :=
    fun m : nat =>
    fix liftFinSet_fix (n : nat) (i : FinSet n) {struct i} : FinSet (n + m) :=
    match i in FinSet Sn0 return FinSet (Sn0 + m) with
    | FZ n0 => FZ (n0 + m)
    | FS n0 i' => FS (n0 + m) (liftFinSet_fix n0 i')
    end
  .

  Lemma liftFinSet_evalFinSet :
    forall m : nat,
    forall n : nat,
    forall i : FinSet n,
    evalFinSet (liftFinSet m n i) = evalFinSet i.
  Proof.
    intros m n i.
    apply (proj2 (evalFinSet_spec (n + m) (liftFinSet m n i) (evalFinSet i) (le_transitivity (@evalFinSet_lt n i) (le_intro_plus1 n m)))).
    induction i as [n' | n' i' IH].
    - reflexivity.
    - apply (proj1 (evalFinSet_spec (S n' + m) (liftFinSet m (S n') (FS n' i')) (evalFinSet (FS n' i')) (le_transitivity (evalFinSet_lt (FS n' i')) (le_intro_plus1 (S n') m)))).
      apply (proj2 (evalFinSet_spec (n' + m) (liftFinSet m n' i') (evalFinSet i') (le_transitivity (evalFinSet_lt i') (le_intro_plus1 n' m)))) in IH.
      unfold evalFinSet in *.
      simpl.
      destruct (runFinSet (n' + m) (liftFinSet m n' i')) as [m2 Hlt2].
      simpl in *.
      subst m2.
      destruct (runFinSet n' i') as [m1 Hlt1].
      reflexivity.
  Qed.

  Definition incrFinSet {m : nat} : forall n : nat, FinSet m -> FinSet (n + m) :=
    fix incrFinSet_fix (n : nat) {struct n} : FinSet m -> FinSet (n + m) :=
    fun i : FinSet m =>
    match n as n0 return FinSet (n0 + m) with
    | O => i
    | S n' => FS (n' + m) (incrFinSet_fix n' i)
    end
  .

  Lemma incrFinSet_evalFinSet :
    forall n : nat,
    forall m : nat,
    forall i : FinSet m,
    evalFinSet (incrFinSet n i) = n + evalFinSet i.
  Proof.
    induction n as [| n IH]; intros m i; simpl.
    - reflexivity.
    - rewrite <- (IH m i).
      unfold evalFinSet.
      simpl.
      destruct (runFinSet (n + m) (incrFinSet n i)) as [m2 Hlt2].
      reflexivity.
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

  Theorem eqFinSet_proof_irrelevance {n : nat} :
    forall i1 : FinSet n,
    forall i2 : FinSet n,
    forall H_EQ1 : i1 = i2,
    forall H_EQ2 : i1 = i2,
    H_EQ1 = H_EQ2.
  Proof.
    exact (fun i : FinSet n => eq_em_implies_eq_pirrel i (eqFinSet_em n i)).
  Qed.

  End MyFin.

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
    assert (H1 : a = b * (a / b) + (a mod b)) by now apply (Nat.div_mod a b); lia.
    assert (H2 : 0 <= a mod b < b) by now apply (Nat.mod_bound_pos a b); lia.
    assert (claim1 : ~ q > a / b).
    { intros H3.
      destruct (proj1 (greater_than_iff q (a / b)) H3) as [z H4].
      enough (so_we_obatain : b * q + r >= b * S (a / b) + r)...
    }
    assert (claim2 : ~ q < a / b).
    { intros H3.
      destruct (proj1 (greater_than_iff (a / b) q) H3) as [z H4].
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

  Definition case_eqrefl {A : Type} : forall x : A, forall y : A, forall H : x = y, forall phi : forall x0 : A, x0 = y -> Type, phi y eq_refl -> phi x H :=
    fun x : A =>
    fun y : A =>
    fun H : eq x y =>
    match H as H0 in eq _ y0 return forall phi : forall x0 : A, x0 = y0 -> Type, phi y0 eq_refl -> phi x H0 with
    | eq_refl =>
      fun phi : forall x0 : A, x0 = x -> Type =>
      fun phi_y : phi x eq_refl =>
      phi_y
    end
  .

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

  Definition elemIndex {A : Type} : forall x : A, (forall x' : A, {x = x'} + {x <> x'}) -> forall xs : list A, option (FinSet (length xs)) :=
    fun x : A =>
    fun eq_dec : forall x' : A, {x = x'} + {x <> x'} =>
    fix elemIndex_fix (xs : list A) {struct xs} : option (FinSet (length xs)) :=
    match xs as xs0 return option (FinSet (length xs0)) with
    | [] => None
    | x' :: xs' => if eq_dec x' then Some (FZ (length xs')) else fmapMaybe (FS (length xs')) (elemIndex_fix xs')
    end
  .

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
    exact leq_init.
  Qed.

  Lemma leq_intro_leq_0_n :
    forall n : nat,
    leq 0 n.
  Proof with eauto.
    induction n as [| n IH]...
  Qed.

  Lemma leq_intro_leq_S_n_S_m :
    forall n : nat,
    forall m : nat,
    leq n m ->
    leq (S n) (S m).
  Proof with eauto.
    intros n m Hleq.
    induction Hleq as [| m Hleq IH]...
  Qed.

  Lemma leq_transitivity :
    forall n1 : nat,
    forall n2 : nat,
    forall n3 : nat,
    leq n1 n2 ->
    leq n2 n3 ->
    leq n1 n3.
  Proof with eauto.
    enough (it_is_sufficient_to_show : forall l : nat, forall n : nat, forall m : nat, leq n l -> leq m n -> leq m l) by firstorder.
    induction l; intros n m H H0; inversion H; subst...
  Qed.

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
  Qed.

  Lemma leq_implies_le :
    forall n : nat,
    forall m : nat,
    leq n m ->
    n <= m.
  Proof with eauto.
    intros n m Hleq.
    induction Hleq as [| m Hleq IH]...
  Qed.

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
  Qed.

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
      + apply leq_intro_leq_S_n_S_m, IH.
        exact (le_elim_S_n_le_m n (S m') Hle).
  Qed.

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
      contradiction (le_lt_False n1 m2' Hle Hlt).
    - intros Heq.
      assert (Hlt : m1' < n1) by now rewrite Heq; constructor.
      assert (Hle : n1 <= m1') by now apply leq_implies_le.
      contradiction (le_lt_False n1 m1' Hle Hlt).
    - intros Heq.
      assert (Heq' : m2' = m1') by exact (S_eq_S_elim m2' m1' Heq).
      destruct Heq' as [].
      rewrite (eqnat_proof_irrelevance (S m2') (S m2') Heq (eq_reflexivity (S m2'))).
      apply (eq_congruence (leq_step n1 m2')).
      exact (leq_unique_fix m2' Hleq1' Hleq2').
  Qed.

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

End MyScratch.
