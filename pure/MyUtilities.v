Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Module MyUtilities.

  Import ListNotations.

  Lemma strong_induction (P : nat -> Prop) :
    (forall n : nat, (forall m : nat, m < n -> P m) -> P n) ->
    forall l : nat,
    P l.
  Proof with try lia.
    intros ind_claim l.
    apply ind_claim.
    induction l...
    intros m H.
    apply ind_claim.
    intros n H0.
    apply IHl...
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
    assert (H : forall x : nat, forall y : nat, x > y <-> (exists z : nat, x = S (y + z))).
    { intros x y.
      split.
      - intros H.
        induction H...
        destruct IHle as [z H0].
        exists (S z)...
      - intros H.
        destruct H as [z H]...
    }
    intros a b q r H0 H1.
    assert (H2 : a = b * (a / b) + (a mod b)) by now apply (Nat.div_mod a b); lia.
    assert (H3 : 0 <= a mod b < b) by now apply (Nat.mod_bound_pos a b); lia.
    assert (claim1 : ~ q > a / b).
    { intros H4.
      enough (H5 : exists z : nat, q = S (a / b + z))...
      destruct H5 as [z H5].
      enough (so_we_have : b * q + r >= b * S (a / b) + r)...
    }
    assert (claim2 : ~ q < a / b).
    { intros H5.
      enough (H6 : exists z : nat, a / b = S (q + z))...
      destruct H6 as [z H6].
      enough (so_we_have : b * q + a mod b >= b * S (a / b) + a mod b)...
    }
    enough (therefore : q = a / b)...
  Qed.

  Definition first_nat : (nat -> bool) -> nat -> nat :=
    fun p : nat -> bool =>
    fix first_nat_fix (n : nat) {struct n} : nat :=
    match n with
    | 0 => 0
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
      destruct (p (first_nat p x)) eqn:H0...
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
    | 0 => 0
    | S n' => n + sum_from_0_to n'
    end
  .

  Proposition sum_from_0_to_is :
    forall n : nat,
    2 * sum_from_0_to n = n * (S n).
  Proof with lia.
    induction n; simpl in *...
  Qed.

  Fixpoint cantor_pairing (n : nat) {struct n} : nat * nat :=
    match n with
    | 0 => (0, 0)
    | S n' =>
      match cantor_pairing n' with
      | (0, y) => (S y, 0)
      | (S x, y) => (x, S y)
      end
    end
  .

  Lemma cantor_pairing_is_surjective :
    forall x : nat,
    forall y : nat,
    (x, y) = cantor_pairing (sum_from_0_to (x + y) + y).
  Proof with (lia || eauto).
    enough (forall z : nat, forall y : nat, forall x : nat, z = x + y -> (x, y) = cantor_pairing (sum_from_0_to z + y))...
    induction z.
    - intros y x H.
      assert (H0 : x = 0)...
      assert (H1 : y = 0)...
      subst...
    - induction y.
      + intros x H.
        assert (H0 : x = S z)...
        subst.
        simpl.
        destruct (cantor_pairing (z + sum_from_0_to z + 0)) as [x y] eqn: H0.
        assert (H1 : (0, z) = cantor_pairing (sum_from_0_to z + z))...
        rewrite Nat.add_0_r, Nat.add_comm in H0.
        rewrite H0 in H1.
        inversion H1; subst...
      + intros x H.
        enough (H0 : (S x, y) = cantor_pairing (sum_from_0_to (S z) + y)).
        { assert (H1 : z + sum_from_0_to z + S y = sum_from_0_to (S z) + y) by now simpl.
          simpl.
          rewrite H1, <- H0...
        }
        apply (IHy (S x))...
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
      destruct (cantor_pairing n) as [x' y'] eqn: H0.
      destruct x'; (inversion H; subst).
      + repeat (rewrite Nat.add_0_r).
        simpl.
        rewrite (IHn 0 y' eq_refl), Nat.add_0_l...
      + rewrite (IHn (S x) y' eq_refl).
        assert (H1 : forall x' : nat, S x' + y' = x' + S y')...
        repeat (rewrite H1)...
  Qed.

  Corollary cantor_pairing_is :
    forall n : nat,
    forall x : nat,
    forall y : nat,
    cantor_pairing n = (x, y) <-> n = sum_from_0_to (x + y) + y.
  Proof with eauto using cantor_pairing_is_injective, cantor_pairing_is_surjective.
    split...
    intros H.
    subst...
  Qed.

  Definition S_0 {A : Type} : forall n : nat, S n = O -> A :=
    fun n : nat =>
    fun H0 : S n = O =>
    let H1 : O = S n := @eq_ind nat (S n) (fun x : nat => x = S n) eq_refl O H0 in
    let H2 : False := @eq_ind nat O (fun x : nat => if Nat.eqb x O then True else False) I (S n) H1 in
    False_rect A H2
  .

  Definition S_S : forall n1 : nat, forall n2 : nat, S n1 = S n2 -> n1 = n2 :=
    fun n1 : nat =>
    fun n2 : nat =>
    fun H0 : S n1 = S n2 =>
    @eq_ind nat (S n1) (fun x : nat => n1 = pred x) eq_refl (S n2) H0
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
      | 0 =>
        fun i0' : FinSet O =>
        @FinSet_case0 (fun i1 : FinSet O => P 1 (FS O i1)) i0'
      | S n0' =>
        fun i0' : FinSet (S n0') =>
        PS (S n0') i0' (FinSet_rectS_fix n0' i0')
      end i'
    end
  .

  Definition safe_nth {A : Type} : forall xs : list A, FinSet (length xs) -> A :=
    fix safe_nth_fix (xs : list A) {struct xs} : FinSet (length xs) -> A :=
    match xs as xs0 return FinSet (length xs0) -> A with
    | [] => FinSet_case0
    | x :: xs' => FinSet_caseS x (safe_nth_fix xs')
    end
  .

  Lemma forallb_true_iff {A : Type} {p : A -> bool} (xs : list A) :
    forallb p xs = true <-> (forall x : A, In x xs -> p x = true).
  Proof with try now firstorder.
    induction xs; simpl...
    rewrite andb_true_iff.
    split...
    intros H0 x H1.
    destruct H0; destruct H1...
    rewrite H1 in H...
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
    intros n H.
    destruct H...
    enough (fold_right max 0 ns >= n)...
  Qed.

  Lemma fold_right_max_0_app :
    forall ns1 : list nat,
    forall ns2 : list nat,
    fold_right_max_0 (ns1 ++ ns2) = max (fold_right_max_0 ns1) (fold_right_max_0 ns2).
  Proof with (lia || eauto).
    unfold fold_right_max_0.
    induction ns1 as [| n1 ns1]; simpl... 
    intros n.
    rewrite IHns1...
  Qed.

  Lemma property1_of_fold_right_max_0 (Phi : nat -> Prop) (Phi_dec : forall i : nat, {Phi i} + {~ Phi i}) :
    forall ns : list nat,
    (forall i : nat, Phi i -> In i ns) ->
    forall n : nat,
    Phi n ->
    fold_right max 0 ns >= n.
  Proof with (lia || eauto).
    induction ns; simpl.
    - intros H n H0.
      contradiction (H n).
    - intros H n H0.
      destruct (Compare_dec.le_lt_dec n a)...
      enough (fold_right max 0 ns >= n)...
      destruct (Phi_dec n).
      + destruct (H n p)...
        enough (forall ks : list nat, forall k : nat, In k ks -> fold_right max 0 ks >= k) by firstorder.
        induction ks; simpl...
        intros k H2.
        destruct H2...
        enough (fold_right Init.Nat.max 0 ks >= k)...
      + apply IHns...
        intros.
        destruct (H i H1)...
        subst.
        contradiction.
  Qed.

  Lemma property2_of_fold_right_max_0 :
    forall ns : list nat,
    forall n : nat,
    fold_right max 0 ns > n <-> (exists i : nat, In i ns /\ i > n).
  Proof with (lia || eauto).
    induction ns; simpl.
    - split...
      now firstorder.
    - intros n.
      destruct (Compare_dec.le_lt_dec a (fold_right Init.Nat.max 0 ns)); split...
      + intros H.
        assert (H0 : fold_right Init.Nat.max 0 ns > n)...
        destruct (proj1 (IHns n) H0) as [i [H1 H2]].
        now firstorder.
      + intros [i [[H | H] H0]].
        * subst...
        * enough (fold_right max 0 ns > n)...
          apply IHns...
      + intros H.
        exists a...
      + intros [i [[H | H] H0]].
        * subst...
        * enough (fold_right Init.Nat.max 0 ns > n)...
          apply IHns...
  Qed.

  Lemma property3_of_fold_right_max_0 :
    forall ns1 : list nat,
    forall ns2 : list nat,
    fold_right max 0 (ns1 ++ ns2) = max (fold_right max 0 ns1) (fold_right max 0 ns2).
  Proof.
    apply fold_right_max_0_app.
  Qed.

  Lemma property4_of_fold_right_max_0 :
    forall ns : list nat,
    forall n : nat,
    In n ns ->
    fold_right max 0 ns >= n.
  Proof with (lia || eauto).
    induction ns; simpl...
    intros n H.
    destruct H...
    enough (fold_right max 0 ns >= n)...
  Qed.

  Lemma property5_of_fold_right_max_0 :
    forall ns1 : list nat,
    forall ns2 : list nat,
    (forall n : nat, In n ns1 -> In n ns2) ->
    fold_right max 0 ns1 <= fold_right max 0 ns2.
  Proof with (lia || eauto).
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
    intros.
    enough (fold_right max 0 ns1 <= fold_right max 0 ns2 /\ fold_right max 0 ns2 <= fold_right max 0 ns1) by lia.
    split; apply property5_of_fold_right_max_0...
  Qed.

  Definition case_eq {A : Type} : forall x : A, forall y : A, forall H : x = y, forall phi : forall x0 : A, x0 = y -> Type, phi y eq_refl -> phi x H :=
    fun x : A =>
    fun y : A =>
    fun H : eq x y =>
    match H as H0 in eq _ y0 return forall phi0 : forall x0 : A, x0 = y0 -> Type, phi0 y0 eq_refl -> phi0 x H0 with
    | eq_refl =>
      fun phi : forall x0 : A, x0 = x -> Type =>
      fun phi_y : phi x eq_refl =>
      phi_y
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

Module MyCoinductive.

  Set Primitive Projections.

  Import MyUniverses.

  Definition SmallerUniverse : InferiorUniverse :=
    Type
  .

  Record Container : SuperiorUniverse :=
    { shape : SmallerUniverse; position : shape -> InferiorUniverse }
  .

  Definition runContainer : Container -> InferiorUniverse -> InferiorUniverse :=
    fun c : Container =>
    fun X : InferiorUniverse =>
    {s : shape c & (position c s -> X)}
  .

  CoInductive M (c : Container) : InferiorUniverse :=
    { observe : runContainer c (M c) }
  .

End MyCoinductive.
