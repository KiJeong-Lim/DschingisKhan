Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Module EqFacts.

  Definition RuleJ {A : Type} (phi' : forall x0 : A, forall y0 : A, x0 = y0 -> Type) : forall x : A, forall y : A, forall H : x = y, phi' y y eq_refl -> phi' x y H :=
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

  Definition eq_reflexivity {A : Type} : forall x1 : A, x1 = x1 :=
    @eq_refl A
  .

  Definition eq_symmetry {A : Type} : forall x1 : A, forall x2 : A, x1 = x2 -> x2 = x1 :=
    fun x1 : A =>
    eq_ind x1 (fun x : A => x = x1) eq_refl
  .

  Definition eq_transitivity {A : Type} : forall x1 : A, forall x2 : A, forall x3 : A, x1 = x2 -> x2 = x3 -> x1 = x3 :=
    fun x1 : A =>
    fun x2 : A =>
    fun x3 : A =>
    fun H : x1 = x2 =>
    eq_ind x2 (fun x : A => x1 = x) H x3
  .

  Definition eq_congruence {A : Type} {B : Type} : forall f : A -> B, forall x1 : A, forall x2 : A, x1 = x2 -> f x1 = f x2 :=
    fun f : A -> B =>
    fun x1 : A =>
    fun x2 : A =>
    eq_ind x1 (fun x : A => f x1 = f x) eq_refl x2
  .

End EqFacts.

Module MyUtilities.

  Import ListNotations EqFacts.

  Global Create HintDb my_hints.

  Section ARITH_WITHOUT_LIA.

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

  Definition strong_induction {P : nat -> Prop} : (forall n : nat, (forall m : nat, m < n -> P m) -> P n) -> (forall l : nat, P l) :=
    fun ACC : (forall n : nat, (forall m : nat, m < n -> P m) -> P n) =>
    fun n : nat =>
    let case0 : forall m : nat, forall H : m < O, P m := fun m : nat => fun H : m < O => lt_elim_n_lt_0 m H in
    let caseS : forall n : nat, (forall m : nat, m < n -> P m) -> (forall m : nat, m < S n -> P m) := fun n : nat => fun IH : forall m : nat, m < n -> P m => fun m : nat => fun Hlt : m < S n => le_inversion (fun n1 : nat => fun n2 : nat => P (pred n1)) (S m) (S n) Hlt (fun Heq : S m = S n => ACC n IH) (fun m' : nat => fun H' : S m <= m' => fun Heq : S m' = S n => IH m (eq_ind m' (le (S m)) H' n (S_eq_S_elim m' n Heq))) in
    ACC n (nat_ind (fun n0 : nat => forall m : nat, m < n0 -> P m) case0 caseS n)
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

  Definition n_le_m_or_m_lt_n_for_n_and_m : forall n : nat, forall m : nat, {n <= m} + {m < n} :=
    fix n_le_m_or_m_lt_n_for_n_and_m_fix (n : nat) {struct n} : forall m : nat, {n <= m} + {m < n} :=
    match n as n0 return forall m : nat, {n0 <= m} + {m < n0} with
    | O =>
      fun m : nat =>
      left (le_intro_0_le_n m)
    | S n' =>
      fun m : nat =>
      match n_le_m_or_m_lt_n_for_n_and_m_fix n' m return {S n' <= m} + {m < S n'} with
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

  End ARITH_WITHOUT_LIA.

  Section DecidableProofIrrelevance.

  Context {A : Type} (x : A) (eq_lem : forall y : A, x = y \/ x <> y).

  Definition choice_eq : forall y : A, x = y -> x = y :=
    fun y : A =>
    fun H_EQ : x = y =>
    match eq_lem y return x = y with
    | or_introl Heq => Heq
    | or_intror Hne => False_ind (x = y) (Hne H_EQ)
    end
  .

  Hypothesis choice_eq_is : forall y : A, forall H_EQ : x = y, choice_eq y H_EQ = H_EQ.

  Lemma choice_eq_const :
    forall y : A,
    forall H_EQ1 : x = y,
    forall H_EQ2 : x = y,
    choice_eq y H_EQ1 = choice_eq y H_EQ2.
  Proof.
    unfold choice_eq.
    intros y H_EQ1 H_EQ2.
    destruct (eq_lem y) as [Heq | Hne].
    - exact (eq_reflexivity Heq).
    - contradiction (Hne H_EQ1).
  Qed.

  Theorem choice_eq_proof_irrelevance_prototype :
    forall y : A,
    forall H_EQ1 : x = y,
    forall H_EQ2 : x = y,
    H_EQ1 = H_EQ2.
  Proof.
    assert ( claim1 :
      forall y : A,
      forall H_EQ : x = y,
      eq_ind x (fun z : A => z = y) (choice_eq y H_EQ) x (choice_eq x (eq_reflexivity x)) = H_EQ
    ).
    { rewrite (choice_eq_is x (eq_reflexivity x)).
      exact choice_eq_is.
    }
    intros y H_EQ1 H_EQ2.
    rewrite <- (claim1 y H_EQ1).
    rewrite <- (claim1 y H_EQ2).
    rewrite <- (choice_eq_const y H_EQ1 H_EQ2).
    reflexivity.
  Qed.

  End DecidableProofIrrelevance.

  Section ArithProofIrrelevance.

  Let eqnat : nat -> nat -> Prop :=
    @eq nat
  .

  Definition eq_lem_nat : forall n1 : nat, forall n2 : nat, eqnat n1 n2 \/ ~ eqnat n1 n2 :=
    fun n1 : nat =>
    fun n2 : nat =>
    match eq_dec_nat n1 n2 return n1 = n2 \/ n1 <> n2 with
    | left H_yes => or_introl H_yes
    | right H_no => or_intror H_no
    end
  .

  Definition choice_eqnat : forall n1 : nat, forall n2 : nat, eqnat n1 n2 -> eqnat n1 n2 :=
    fun n1 : nat =>
    fun n2 : nat =>
    choice_eq n1 (eq_lem_nat n1) n2
  .

  Lemma choice_eqnat_is :
    forall n1 : nat,
    forall n2 : nat,
    forall H_EQ : eqnat n1 n2,
    choice_eqnat n1 n2 H_EQ = H_EQ.
  Proof.
    induction n1 as [| n IH]; intros n2 [].
    - exact (eq_reflexivity (eq_reflexivity O)).
    - unfold choice_eqnat, choice_eq, eq_lem_nat in *.
      simpl.
      assert (claim1 := IH n (eq_reflexivity n)).
      destruct (eq_dec_nat n n) as [Heq | Hne].
      + rewrite claim1.
        exact (eq_reflexivity (eq_reflexivity (S n))).
      + contradiction (Hne (eq_reflexivity n)).
  Qed.

  Theorem eqnat_proof_irrelevance :
    forall n1 : nat,
    forall n2 : nat,
    forall H_EQ1 : eqnat n1 n2,
    forall H_EQ2 : eqnat n1 n2,
    H_EQ1 = H_EQ2.
  Proof.
    intros n.
    exact (choice_eq_proof_irrelevance_prototype n (eq_lem_nat n) (choice_eqnat_is n)).
  Qed.

  Corollary eqnat_K :
    forall n : nat,
    forall H_EQ : eqnat n n,
    H_EQ = eq_reflexivity n.
  Proof.
    intros n H_EQ.
    exact (eqnat_proof_irrelevance n n H_EQ (eq_reflexivity n)).
  Qed.

  Let lenat : nat -> nat -> Prop :=
    le
  .

  Theorem lenat_proof_irrelevance :
    forall n1 : nat,
    forall n2 : nat,
    forall H_LE1 : lenat n1 n2,
    forall H_LE2 : lenat n1 n2,
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
      rewrite (eqnat_K n1 H_EQ).
      reflexivity.
    - intros H_EQ.
      assert (Hlt : m2' < n1) by now rewrite H_EQ; constructor.
      contradiction (le_lt_False n1 m2' H_LE2' Hlt).
    - intros H_EQ.
      assert (Hlt : m1' < n1) by now rewrite H_EQ; constructor.
      contradiction (le_lt_False n1 m1' H_LE1' Hlt).
    - intros H_EQ.
      refine (
        match S_eq_S_elim m2' m1' H_EQ in eq _ m return forall Heq : S m2' = S m, forall Hle1 : n1 <= m, le_S n1 m Hle1 = eq_ind (S m2') (le n1) (le_S n1 m2' H_LE2') (S m) Heq with
        | eq_refl => _
        end H_EQ H_LE1'
      ).
      intros h_EQ h_LE1'.
      rewrite (eqnat_K (S m2') h_EQ).
      apply (eq_congruence (le_S n1 m2') h_LE1' H_LE2').
      exact (lenat_proof_irrelevance_fix m2' h_LE1' H_LE2').
  Qed.

  End ArithProofIrrelevance.

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

  Definition liftFinSet {m : nat} : forall n : nat, FinSet n -> FinSet (n + m) :=
    fix liftFinSet_fix (n : nat) (i : FinSet n) {struct i} : FinSet (n + m) :=
    match i in FinSet Sn0 return FinSet (Sn0 + m) with
    | FZ n0 => FZ (n0 + m)
    | FS n0 i' => FS (n0 + m) (liftFinSet_fix n0 i')
    end
  .

  Definition incrFinSet {m : nat} : forall n : nat, FinSet m -> FinSet (n + m) :=
    fix incrFinSet_fix (n : nat) {struct n} : FinSet m -> FinSet (n + m) :=
    fun i : FinSet m =>
    match n as n0 return FinSet (n0 + m) with
    | O => i
    | S n' => FS (n' + m) (incrFinSet_fix n' i)
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

  Definition mkFinSet_runFinSet_identity (n : nat) :
    forall i : FinSet n,
    mkFinSet n (proj1_sig (runFinSet n i)) (proj2_sig (runFinSet n i)) = i.
  Proof.
    induction i as [n' | n' i' IH].
    - exact (eq_reflexivity (FZ n')). 
    - apply (eq_transitivity (mkFinSet (S n') (proj1_sig (runFinSet (S n') (FS n' i'))) (proj2_sig (runFinSet (S n') (FS n' i')))) (FS n' (mkFinSet n' (proj1_sig (runFinSet n' i')) (proj2_sig (runFinSet n' i')))) (FS n' i')).
      + simpl.
        destruct (runFinSet n' i') as [m Hlt].
        simpl in *.
        assert (claim1 := mkFinSet_ext n' m (lt_elim_S_n_lt_S_m m n' (lt_intro_S_m_lt_S_n m n' Hlt)) Hlt).
        exact (eq_congruence (FS n') (mkFinSet n' m (lt_elim_S_n_lt_S_m m n' (lt_intro_S_m_lt_S_n m n' Hlt))) (mkFinSet n' m Hlt) claim1).
      + exact (eq_congruence (FS n') (mkFinSet n' (proj1_sig (runFinSet n' i')) (proj2_sig (runFinSet n' i'))) i' IH).
  Defined.

  Lemma runFinSet_mkFinSet_identity :
    forall m : nat,
    forall n : nat,
    forall Hlt : m < n,
    runFinSet n (mkFinSet n m Hlt) = exist (fun m_ : nat => m_ < n) m Hlt.
  Proof.
    induction m; simpl.
    - induction n; simpl.
      + intros Hlt.
        apply (lt_elim_n_lt_0 0 Hlt).
      + intros Hlt.
        rewrite (lenat_proof_irrelevance 1 (S n) (lt_intro_0_lt_S_n n) Hlt).
        reflexivity.
    - induction n; simpl in *.
      + intros Hlt.
        apply (lt_elim_n_lt_0 (S m) Hlt).
      + intros Hlt.
        rewrite (IHm n (lt_elim_S_n_lt_S_m m n Hlt)).
        rewrite (lenat_proof_irrelevance (S (S m)) (S n) (lt_intro_S_m_lt_S_n m n (lt_elim_S_n_lt_S_m m n Hlt)) Hlt).
        reflexivity.
  Qed.

  End MyFin.

  Section SIMPLE_LOGIC.

  Lemma not_imply_elim2 :
    forall P : Prop,
    forall Q : Prop,
    (~ (P -> Q)) ->
    (~ Q).
  Proof with tauto.
    intros P Q...
  Qed.

  Lemma or_to_imply :
    forall P : Prop,
    forall Q : Prop,
    (~ P \/ Q) ->
    (P) ->
    (Q).
  Proof with tauto.
    intros P Q...
  Qed.

  Lemma or_not_and :
    forall P : Prop,
    forall Q : Prop,
    (~ P \/ ~ Q) ->
    (~ (P /\ Q)).
  Proof with tauto.
    intros P Q...
  Qed.

  Lemma not_or_and :
    forall P : Prop,
    forall Q : Prop,
    (~ (P \/ Q)) ->
    (~ P /\ ~ Q).
  Proof with tauto.
    intros P Q...
  Qed.

  Lemma and_not_or :
    forall P : Prop,
    forall Q : Prop,
    (~ P /\ ~ Q) ->
    (~ (P \/ Q)).
  Proof with tauto.
    intros P Q...
  Qed.

  Lemma imply_and_or :
    forall P : Prop,
    forall Q : Prop,
    (P -> Q) ->
    (P \/ Q) ->
    (Q).
  Proof with tauto.
    intros P Q...
  Qed.

  Lemma imply_and_or2 :
    forall P : Prop,
    forall Q : Prop,
    forall R : Prop,
    (P -> Q) ->
    (P \/ R) ->
    (Q \/ R).
  Proof with tauto.
    intros P Q R...
  Qed.

  Lemma not_ex_all_not :
    forall U : Type,
    forall P : U -> Prop,
    (~ exists n : U, P n) ->
    (forall n : U, ~ P n).
  Proof with firstorder.
    intros U P...
  Qed.

  Lemma ex_not_not_all :
    forall U : Type,
    forall P : U -> Prop,
    (exists n : U, ~ P n) ->
    (~ forall n : U, P n).
  Proof with firstorder.
    intros U P...
  Qed.

  Lemma all_not_not_ex :
    forall U : Type,
    forall P : U -> Prop,
    (forall n : U, ~ P n) ->
    (~ exists n : U, P n).
  Proof with firstorder.
    intros U P...
  Qed.

  End SIMPLE_LOGIC.

  Section BORING.

  Variant AckermannFuncSpec (ack : nat -> nat -> nat) : Prop :=
  | AckermannCharacterization :
    (forall n : nat, ack 0 n = n + 1) ->
    (forall m : nat, ack (m + 1) 0 = ack m 1) ->
    (forall m : nat, forall n : nat, ack (m + 1) (n + 1) = ack m (ack (m + 1) n)) ->
    AckermannFuncSpec ack
  .

  Definition AckermannFunc : nat -> nat -> nat :=
    let AckermannFunc_aux1 : nat -> (nat -> nat) -> nat := nat_rect (fun _ : nat => (nat -> nat) -> nat) (fun kont : nat -> nat => kont 1) (fun n' : nat => fun call_n' : (nat -> nat) -> nat => fun kont : nat -> nat => kont (call_n' kont)) in
    fix AckermannFunc_fix (m : nat) {struct m} : nat -> nat :=
    match m return nat -> nat with
    | O => S
    | S m' =>
      fun n : nat =>
      AckermannFunc_aux1 n (AckermannFunc_fix m')
    end
  .

  Lemma AckermannFuncSatisfiesItsSpecification :
    AckermannFuncSpec AckermannFunc.
  Proof with (lia || eauto).
    constructor.
    - induction n as [| n' IHn]; simpl...
    - intros m.
      replace (m + 1) with (S m)...
    - induction m as [| m' IHm]; induction n as [| n' IHn]; simpl in *...
      + replace (m' + 1) with (S m')...
      + replace (m' + 1) with (S m') in *...
        rewrite IHn...
  Qed.

  Lemma greater_than_iff :
    forall x : nat,
    forall y : nat,
    x > y <-> (exists z : nat, x = S (y + z)).
  Proof with try (lia || now (firstorder; eauto)).
    intros x y.
    split.
    - intros H.
      induction H as [| m H [z H0]]...
      exists (S z)...
    - intros [z H]...
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
    | S n' => if p (first_nat_fix n') then first_nat_fix n' else n
    end
  .

  Theorem well_ordering_principle : 
    forall p : nat -> bool,
    forall n : nat,
    p n = true ->
    let m : nat := first_nat p n in
    p m = true /\ (forall i : nat, p i = true -> i >= m).
  Proof with eauto. (* This proof has been improved by JunYoung Clare Jang. *)
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
      destruct (n_le_m_or_m_lt_n_for_n_and_m x y).
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

  Corollary cantor_pairing_is :
    forall n : nat,
    forall x : nat,
    forall y : nat,
    cantor_pairing n = (x, y) <-> n = sum_from_0_to (x + y) + y.
  Proof with eauto using cantor_pairing_is_injective, cantor_pairing_is_surjective.
    split...
    intros Heq.
    subst...
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
    destruct (n_le_m_or_m_lt_n_for_n_and_m n a)...
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
    destruct (n_le_m_or_m_lt_n_for_n_and_m a (fold_right Init.Nat.max 0 ns)); split.
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
    destruct (n_le_m_or_m_lt_n_for_n_and_m a (fold_right max 0 ns1)).
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

  End BORING.

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

  Definition elemIndex {A : Type} : forall x : A, (forall x' : A, {x = x'} + {x <> x'}) -> forall xs : list A, option (FinSet (length xs)) :=
    fun x : A =>
    fun eq_dec : forall x' : A, {x = x'} + {x <> x'} =>
    fix elemIndex_fix (xs : list A) : option (FinSet (length xs)) :=
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
