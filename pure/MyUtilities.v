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

  Lemma strong_induction (P : nat -> Prop) :
    (forall n : nat, (forall m : nat, m < n -> P m) -> P n) ->
    forall l : nat,
    P l.
  Proof with eauto.
    intros ind_claim l.
    apply ind_claim.
    induction l; intros m H; inversion H; subst...
  Qed.

  Lemma div_mod_uniqueness_aux1 :
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
      destruct (proj1 (div_mod_uniqueness_aux1 q (a / b)) H3) as [z H4].
      enough (so_we_obatain : b * q + r >= b * S (a / b) + r)...
    }
    assert (claim2 : ~ q < a / b).
    { intros H3.
      destruct (proj1 (div_mod_uniqueness_aux1 (a / b) q) H3) as [z H4].
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
      destruct (Compare_dec.le_lt_dec x y).
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

  Definition Seq0_elim {A : Type} : forall n : nat, S n = 0 -> A :=
    fun n : nat =>
    fun H : S n = O =>
    False_rect A (eq_ind O (fun x : nat => if Nat.eqb O x then True else False) I (S n) (eq_symmetry (S n) O H))
  .

  Definition SeqS_elim : forall n1 : nat, forall n2 : nat, S n1 = S n2 -> n1 = n2 :=
    fun n1 : nat =>
    fun n2 : nat =>
    eq_congruence Nat.pred (S n1) (S n2)
  .

  Definition lt0_elim {A : Type} : forall n : nat, n < 0 -> A :=
    fun n : nat =>
    fun H : S n <= O =>
    False_rect A (le_ind (S n) (fun x : nat => if Nat.eqb O x then False else True) I (fun m : nat => fun H0 : S n <= m => fun H1 : if Nat.eqb O m then False else True => I) O H)
  .

  Definition ltS_elim_aux1 : forall n1 : nat, forall n2 : nat, S n1 <= n2 -> S (pred n2) = n2 :=
    fun n1 : nat =>
    fun n2 : nat =>
    fun H : S n1 <= n2 =>
    match H as H0 in le _ m return S (pred m) = m with
    | le_n _ => eq_refl
    | le_S _ _ m' => eq_refl
    end
  .

  Definition ltS_elim_aux2 : forall n1 : nat, forall n2 : nat, S n1 <= n2 -> n1 <= pred n2 :=
    fix ltS_elim_aux2_fix (n1 : nat) (n2 : nat) (H : S n1 <= n2) {struct H} : n1 <= pred n2 :=
    match H as H0 in le _ n2' return n1 <= pred n2' with
    | le_n _ => le_n n1
    | le_S _ n2' H' => eq_ind (S (pred n2')) (fun x : nat => n1 <= x) (le_S n1 (pred n2') (ltS_elim_aux2_fix n1 n2' H')) n2' (ltS_elim_aux1 n1 n2' H')
    end
  .

  Definition ltS : forall n1 : nat, forall n2 : nat, S n1 < S n2 -> n1 < n2 :=
    fun n1 : nat =>
    fun n2 : nat =>
    ltS_elim_aux2 (S n1) (S n2)
  .

  Inductive FinSet : nat -> Set :=
  | FZ : forall n : nat, FinSet (S n) 
  | FS : forall n : nat, FinSet n -> FinSet (S n)
  .

  Definition FinSet_case0 {P : FinSet O -> Type} : forall i : FinSet O, P i :=
    fun i : FinSet O =>
    match i as i0 in FinSet Sn return Sn = O -> P i with
    | FZ n => Seq0_elim n
    | FS n i' => Seq0_elim n
    end eq_refl
  .

  Definition FinSet_caseS {n : nat} {P : FinSet (S n) -> Type} : P (FZ n) -> (forall i' : FinSet n, P (FS n i')) -> (forall i : FinSet (S n), P i) :=
    fun PZ : P (FZ n) =>
    fun PS : forall i' : FinSet n, P (FS n i') =>
    fun i : FinSet (S n) =>
    match i as i0 in FinSet Sn0 return (match Sn0 as Sn1 return FinSet Sn1 -> Type with O => fun i1 : FinSet O => Set | S n0 => fun i1 : FinSet (S n0) => forall P0 : FinSet (S n0) -> Type, P0 (FZ n0) -> (forall i' : FinSet n0, P0 (FS n0 i')) -> P0 i1 end) i0 with
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
    match n with
    | O => lt0_elim
    | S n' =>
      fun i : nat =>
      match i with
      | O =>
        fun H : 0 < S n' =>
        FZ n'
      | S i' =>
        fun H : S i' < S n' =>
        FS n' (mkFinSet_fix n' i' (ltS i' n' H))
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

  Definition lt0_intro : forall n : nat, 0 < S n :=
    fix lt0_intro_fix (n : nat) {struct n} : S O <= S n :=
    match n as n0 return S O <= S n0 with
    | O => le_n (S O)
    | S n' => le_S (S O) (S n') (lt0_intro_fix n')
    end
  .

  Definition ltS_intro_aux1 : forall n1 : nat, forall n2 : nat, n1 <= n2 -> S n1 <= S n2 :=
    fix ltS_intro_aux1_fix (n : nat) (m : nat) (Hle : n <= m) {struct Hle} : S n <= S m :=
    match Hle as Hle0 in le _ m0 return le (S n) (S m0) with
    | le_n _ => le_n (S n)
    | le_S _ m' H' => le_S (S n) (S m') (ltS_intro_aux1_fix n m' H')
    end
  .

  Definition ltS_intro : forall n1 : nat, forall n2 : nat, n1 < n2 -> S n1 < S n2 :=
    fun n1 : nat =>
    fun n2 : nat =>
    fun H : S n1 <= n2 =>
    ltS_intro_aux1 (S n1) n2 H
  .

  Definition runFinSet : forall n : nat, FinSet n -> {i : nat | i < n} :=
    fix runFinSet_fix (n : nat) (i : FinSet n) {struct i} : sig (fun x : nat => S x <= n) :=
    match i as i0 in FinSet Sn0 return sig (fun x : nat => S x <= Sn0) with
    | FZ n0 => exist (fun x : nat => S x <= S n0) O (lt0_intro n0)
    | FS n0 i' =>
      match runFinSet_fix n0 i' as sig0 in sig _ return sig (fun x : nat => S x <= S n0) with
      | exist _ x H => exist (fun x : nat => S x <= S n0) (S x) (ltS_intro x n0 H)
      end
    end
  .

  Definition FZeqFZ : forall n : nat, FZ n = FZ n :=
    fun n : nat =>
    @eq_refl (FinSet (S n)) (FZ n)
  .

  Definition FZeqFS : forall n : nat, forall i : FinSet n, FZ n = FS n i -> False :=
    fun n : nat =>
    fun i : FinSet n =>
    @eq_ind (FinSet (S n)) (FZ n) (fun j : FinSet (S n) => match j as j0 in FinSet Sn0 return Prop with | FZ n0 => True | FS n0 j' => False end) I (FS n i)
  .

  Definition FSeqFZ : forall n : nat, forall i : FinSet n, FS n i = FZ n -> False :=
    fun n : nat =>
    fun i : FinSet n =>
    @eq_ind (FinSet (S n)) (FS n i) (fun j : FinSet (S n) => match j as j0 in FinSet Sn0 return Prop with | FZ n0 => False | FS n0 j' => True end) I (FZ n)
  .

  Definition FSeqFS : forall n : nat, forall i1 : FinSet n, forall i2 : FinSet n, FS n i1 = FS n i2 -> i1 = i2 :=
    fun n : nat =>
    fun i1 : FinSet n =>
    fun i2 : FinSet n =>
    fun Heq : FS n i1 = FS n i2 =>
    match Heq as Heq0 in eq _ rhs return (match rhs as rhs0 in FinSet Sn0 return FinSet (pred Sn0) -> Prop with | FZ n0 => fun lhs : FinSet n0 => 2 + 2 = 5 | FS n0 i2' => fun lhs : FinSet n0 => lhs = i2' end) i1 with
    | eq_refl => @eq_refl (FinSet n) i1
    end
  .

  Definition FinSet_eq_dec_aux1 : forall n : nat, forall j : FinSet (S n), {FZ n = j} + {FZ n <> j} :=
    fun n : nat =>
    FinSet_caseS (left (FZeqFZ n)) (fun j' : FinSet n => right (FZeqFS n j'))
  .

  Definition FinSet_eq_dec_aux2 : forall n : nat, (forall i : FinSet n, forall j : FinSet n, {i = j} + {i <> j}) -> forall i' : FinSet n, forall j : FinSet (S n), {FS n i' = j} + {FS n i' <> j} :=
    fun n : nat =>
    fun IH : forall i : FinSet n, forall j : FinSet n, sumbool (i = j) (i = j -> False) =>
    fun i' : FinSet n =>
    FinSet_caseS (right (FSeqFZ n i')) (fun j' : FinSet n => match IH i' j' as b0 in sumbool _ _ return {FS n i' = FS n j'} + {FS n i' <> FS n j'} with | left Heq => left (eq_congruence (FS n) i' j' Heq) | right Hne => right (fun Heq : FS n i' = FS n j' => Hne (FSeqFS n i' j' Heq)) end)
  .

  Definition FinSet_eq_dec : forall n : nat, forall i1 : FinSet n, forall i2 : FinSet n, {i1 = i2} + {i1 <> i2} :=
    fix FinSet_eq_dec_fix (n : nat) {struct n} : forall i : FinSet n, forall j : FinSet n, {i = j} + {i <> j} :=
    match n as n0 return forall i : FinSet n0, forall j : FinSet n0, {i = j} + {i <> j} with
    | O => FinSet_case0
    | S n' => FinSet_caseS (FinSet_eq_dec_aux1 n') (FinSet_eq_dec_aux2 n' (FinSet_eq_dec_fix n'))
    end
  .

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
    destruct (Compare_dec.le_lt_dec n a)...
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
    destruct (Compare_dec.le_lt_dec a (fold_right Init.Nat.max 0 ns)); split.
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
    destruct (Compare_dec.le_lt_dec a (fold_right max 0 ns1)).
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

  Definition case_eq {A : Type} : forall x : A, forall y : A, forall H : x = y, forall phi : forall x0 : A, x0 = y -> Type, phi y eq_refl -> phi x H :=
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

End MyUtilities.

Module MyUniverses.

  Definition SuperiorUniverse : Type :=
    Type
  .

  Definition InferiorUniverse : SuperiorUniverse :=
    Type
  .

End MyUniverses.

Module PRIVATE.

  Import EqFacts MyUtilities.

  Record retract (A : Prop) (B : Prop) : Prop :=
    { _i : A -> B
    ; _j : B -> A
    ; _inv : forall a : A, _j (_i a) = a
    }
  .

  Local Hint Constructors retract : core.

  Record retract_cond (A : Prop) (B : Prop) : Prop :=
    { _i2 : A -> B
    ; _j2 : B -> A
    ; _inv2 : retract A B -> forall a : A, _j2 (_i2 a) = a
    }
  .

  Local Hint Constructors retract_cond : core.

  Section ClassicalEqTheory.

  Hypothesis eq_rect_eq : forall A : Type, forall x : A, forall B : A -> Type, forall y : B x, forall H : x = x, y = eq_rect x B y x H.

  Section AxiomK.

  Context (A : Type).

  Lemma RuleK :
    forall x : A,
    forall phi : x = x -> Type,
    phi eq_refl ->
    forall eq_val0 : x = x,
    phi eq_val0.
  Proof with eauto.
    intros x.
    set (eq_val := @eq_refl A x). 
    intros phi phi_val0 eq_val0.
    replace eq_val0 with eq_val...
    rewrite (eq_rect_eq A x (eq x) eq_val eq_val0).
    destruct eq_val0...
  Qed.

  End AxiomK.

  Section ExistTSndEq.

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

  Definition existT_snd_eq : forall x : A, forall y1 : B x, forall y2 : B x, existT B x y1 = existT B x y2 -> y1 = y2 :=
    fun x : A =>
    fun y1 : B x =>
    fun y2 : B x =>
    fun H : existT B x y1 = existT B x y2 =>
    phi (existT B x y1) (existT B x y2) H (fun H0 : x = x => eq_symmetry y2 (eq_rect x B y2 x H0) (eq_rect_eq A x B y2 H0)) eq_refl
  .

  End ExistTSndEq.

  End ClassicalEqTheory.

  Section ClassicalLogic.

  Hypothesis LEM : forall P : Prop, P \/ ~ P.

  Section ProofIrrelevance. (* Reference: "https://coq.inria.fr/library/Coq.Logic.Berardi.html" *)

  Lemma AC {A : Prop} {B : Prop} :
    forall r : retract_cond A B,
    retract A B ->
    forall a : A,
    _j2 A B r (_i2 A B r a) = a.
  Proof with eauto.
    intros [i2 j2 inv2] [i j inv] a...
  Qed.

  Let IF_PROP {P : Prop} (B : Prop) : P -> P -> P :=
    fun p1 : P =>
    fun p2 : P =>
    match LEM B with
    | or_introl H => p1
    | or_intror H => p2
    end
  .

  Section ParadoxOfBerardi.

  Context {Bool : Prop} (T : Bool) (F : Bool).

  Let pow : Prop -> Prop :=
    fun P : Prop =>
    P -> Bool
  .

  Lemma L1 :
    forall A : Prop,
    forall B : Prop,
    retract_cond (pow A) (pow B).
  Proof with tauto.
    intros A B.
    destruct (LEM (retract (pow A) (pow B))) as [[i j inv] | H].
    - exists i j...
    - exists (fun pa : pow A => fun b : B => F) (fun pb : pow B => fun a : A => F)...
  Qed.

  Let U : Prop :=
    forall P : Prop,
    pow P
  .

  Let f : U -> pow U :=
    fun u : U =>
    u U
  .

  Let g : pow U -> U :=
    fun h : pow U =>
    fun X : Prop =>
    let lX := _j2 (pow X) (pow U) (L1 X U) in
    let rU := _i2 (pow U) (pow U) (L1 U U) in
    lX (rU h)
  .

  Let retract_pow_U_pow_U : retract (pow U) (pow U) :=
    {| _i := fun x : pow U => x; _j := fun x : pow U => x; _inv := @eq_refl (pow U) |}
  .

  Let NotB : Bool -> Bool :=
    fun b : Bool =>
    IF_PROP (b = T) F T
  .

  Let R : U :=
    g (fun u : U => NotB (u U u))
  .

  Let Russel : Bool :=
    R U R
  .

  Lemma NotB_has_fixpoint :
    Russel = NotB Russel.
  Proof with eauto.
    set (Apply := fun f : U -> Bool => fun x : U => f x).
    enough (claim1 : Russel = Apply (fun u : U => NotB (u U u)) R)...
    replace (fun u : U => NotB (u U u)) with (R U)...
    apply AC...
  Qed.

  Local Hint Resolve NotB_has_fixpoint : core.

  Theorem ParadoxOfBerardi :
    T = F.
  Proof with tauto.
    destruct (LEM (Russel = T)) as [H | H].
    - assert (claim1 : T = NotB T) by now rewrite <- H.
      unfold NotB, IF_PROP in claim1.
      destruct (LEM (T = T))...
    - assert (claim1 : NotB Russel <> T) by now rewrite <- NotB_has_fixpoint.
      unfold NotB, IF_PROP in claim1. 
      destruct (LEM (Russel = T))...
  Qed.

  End ParadoxOfBerardi.

  Corollary ProofIrrelevance :
    forall P : Prop,
    forall p1 : P,
    forall p2 : P,
    p1 = p2.
  Proof.
    exact (@ParadoxOfBerardi).
  Qed.

  End ProofIrrelevance.

  Corollary eq_rect_eq (A : Type) :
    forall x : A,
    forall B : A -> Type,
    forall y : B x,
    forall H : x = x,
    y = eq_rect x B y x H.
  Proof with reflexivity.
    intros x B y H.
    rewrite <- (ProofIrrelevance (@eq A x x) (@eq_refl A x) H)...
  Qed.

  Section Classical_Prop.

  Let classic : forall P : Prop, P \/ ~ P :=
    LEM
  .

  Variable P : Prop.

  Lemma NNPP :
    ~ ~ P ->
    P.
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Variable Q : Prop.

  Lemma Peirce :
    ((P -> Q) -> P) ->
    P.
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Lemma not_imply_elim :
    ~ (P -> Q) ->
    P.
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Lemma not_imply_elim2 :
    ~ (P -> Q) ->
    ~ Q.
  Proof with tauto.
    destruct (classic Q)...
  Qed.

  Lemma imply_to_or :
    (P -> Q) ->
    ~ P \/ Q.
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Lemma imply_to_and :
    ~ (P -> Q) ->
    P /\ ~ Q.
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Lemma or_to_imply :
    ~ P \/ Q ->
    P ->
    Q.
  Proof with tauto.
    destruct (classic Q)...
  Qed.

  Lemma not_and_or :
    ~ (P /\ Q) ->
    ~ P \/ ~ Q.
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Lemma or_not_and :
    ~ P \/ ~ Q ->
    ~ (P /\ Q).
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Lemma not_or_and :
    ~ (P \/ Q) ->
    ~ P /\ ~ Q.
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Lemma and_not_or :
    ~ P /\ ~ Q ->
    ~ (P \/ Q).
  Proof with tauto.
    destruct (classic P)...
  Qed.

  Lemma imply_and_or :
    (P -> Q) ->
    P \/ Q ->
    Q.
  Proof with tauto.
    destruct (classic Q)...
  Qed.

  Variable R : Prop.

  Lemma imply_and_or2 :
    (P -> Q) ->
    P \/ R ->
    Q \/ R.
  Proof with tauto.
    destruct (classic P)...
  Qed.

  End Classical_Prop.

  Section Classical_Pred_Type.

  Let classic : forall P : Prop, P \/ ~ P :=
    LEM
  .

  Context (U : Type) (P : U -> Prop).

  Let forall_exists_False : ~ (forall n : U, P n) -> ~ (exists n : U, ~ P n) -> False :=
    fun H : ~ (forall n : U, P n) =>
    fun H0 : ~ (exists n : U, ~ P n) =>
    H (fun n : U => NNPP (P n) (fun H1 : ~ P n => H0 (@ex_intro U (fun n' : U => ~ P n') n H1)))
  .

  Lemma not_all_not_ex :
    ~ (forall n : U, ~ P n) ->
    exists n : U, P n.
  Proof with firstorder.
    destruct (classic (exists n : U, P n))...
  Qed.

  Lemma not_all_ex_not :
    ~ (forall n : U, P n) ->
    exists n : U, ~ P n.
  Proof with firstorder.
    destruct (classic (exists n : U, ~ P n))...
  Qed.

  Lemma not_ex_all_not :
    ~ (exists n : U, P n) ->
    forall n : U,
    ~ P n.
  Proof with firstorder.
    destruct (classic (forall n : U, ~ P n))...
  Qed.

  Lemma not_ex_not_all :
    ~ (exists n : U, ~ P n) ->
    forall n : U,
    P n.
  Proof with firstorder.
    destruct (classic (forall n : U, P n))...
  Qed.

  Lemma ex_not_not_all :
    (exists n : U, ~ P n) ->
    ~ (forall n : U, P n).
  Proof with firstorder.
    destruct (classic (exists n : U, ~ P n))...
  Qed.

  Lemma all_not_not_ex :
    (forall n : U, ~ P n) ->
    ~ (exists n : U, P n).
  Proof with firstorder.
    destruct (classic (forall n : U, ~ P n))...
  Qed.

  End Classical_Pred_Type.

  End ClassicalLogic.

End PRIVATE.
