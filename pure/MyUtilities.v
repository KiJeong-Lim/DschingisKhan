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

  Lemma div_mod_uniqueness :
    forall a : nat,
    forall b : nat,
    forall q : nat,
    forall r : nat,
    a = b * q + r ->
    r < b ->
    a / b = q /\ a mod b = r.
  Proof with try (lia || now (firstorder; eauto)).
    assert (claim1 : forall x : nat, forall y : nat, x > y <-> (exists z : nat, x = S (y + z))).
    { intros x y.
      split.
      - intros H.
        induction H...
        destruct IHle as [z H0].
        exists (S z)...
      - intros [z H]...
    }
    intros a b q r H H0.
    assert (H1 : a = b * (a / b) + (a mod b)) by now apply (Nat.div_mod a b); lia.
    assert (H2 : 0 <= a mod b < b) by now apply (Nat.mod_bound_pos a b); lia.
    assert (claim2 : ~ q > a / b).
    { intros H3.
      assert (H4 : exists z : nat, q = S (a / b + z)) by firstorder.
      destruct H4 as [z H4].
      enough (so_we_obatain : b * q + r >= b * S (a / b) + r)...
    }
    assert (claim3 : ~ q < a / b).
    { intros H3.
      assert (H4 : exists z : nat, a / b = S (q + z)) by firstorder.
      destruct H4 as [z H4].
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

  Definition S_0 {A : Type} : forall n : nat, S n = O -> A :=
    fun n : nat =>
    fun H : S n = O =>
    False_rect A (eq_ind O (fun x : nat => if Nat.eqb x O then True else False) I (S n) (eq_symmetry (S n) O H))
  .

  Definition S_S : forall n1 : nat, forall n2 : nat, S n1 = S n2 -> n1 = n2 :=
    fun n1 : nat =>
    fun n2 : nat =>
    eq_congruence Nat.pred (S n1) (S n2)
  .

  Inductive FinSet : nat -> Set :=
  | FZ : forall n : nat, FinSet (S n) 
  | FS : forall n : nat, FinSet n -> FinSet (S n)
  .

  Definition FinSet_case0 {P : FinSet O -> Type} : forall i : FinSet O, P i :=
    fun i : FinSet O =>
    match i as i0 in FinSet Sn return Sn = O -> P i with
    | FZ n => S_0 n
    | FS n i' => S_0 n
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

  Definition lt_0 {A : Type} : forall n : nat, n < O -> A :=
    fun n : nat =>
    fun H : S n <= O =>
    False_rect A (le_ind (S n) (fun x : nat => if Nat.eqb O x then False else True) I (fun m : nat => fun H0 : S n <= m => fun H1 : if Nat.eqb O m then False else True => I) O H)
  .

  Definition lt_S_aux1 : forall n1 : nat, forall n2 : nat, S n1 <= n2 -> n1 <= pred n2 :=
    fix lt_S_aux1_fix (n1 : nat) (n2 : nat) (H : S n1 <= n2) {struct H} : n1 <= pred n2 :=
    match H as H0 in le _ n2' return n1 <= pred n2' with
    | le_n _ => le_n n1
    | le_S _ m H' => eq_ind (S (pred m)) (fun x : nat => n1 <= x) (le_S n1 (pred m) (lt_S_aux1_fix n1 m H')) m (match H' as H0' in le _ m' return S (pred m') = m' with | le_n _ => eq_refl | le_S _ _ l => eq_refl end)
    end
  .

  Definition lt_S : forall n1 : nat, forall n2 : nat, S n1 < S n2 -> n1 < n2 :=
    fun n1 : nat =>
    fun n2 : nat =>
    lt_S_aux1 (S n1) (S n2)
  .

  Definition mkFinSet : forall n : nat, forall i : nat, i < n -> FinSet n :=
    fix mkFinSet_fix (n : nat) {struct n} : forall i : nat, i < n -> FinSet n :=
    match n with
    | O => lt_0
    | S n' =>
      fun i : nat =>
      match i with
      | O =>
        fun H : 0 < S n' =>
        FZ n'
      | S i' =>
        fun H : S i' < S n' =>
        FS n' (mkFinSet_fix n' i' (lt_S i' n' H))
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
