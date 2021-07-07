Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Basics.

Global Create HintDb my_hints.

Module MyUtilities.

  Definition case_eq {A : Type} : forall x : A, forall y : A, forall phi : forall x0 : A, x0 = y -> Type, phi y eq_refl -> forall H : x = y, phi x H :=
    fun x : A =>
    fun y : A =>
    fun phi : forall x0 : A, x0 = y -> Type =>
    fun phi_y : phi y eq_refl =>
    fun H : eq x y =>
    match H as H0 in eq _ y0 return forall phi0 : forall x0 : A, x0 = y0 -> Type, phi0 y0 eq_refl -> phi0 x H0 with
    | eq_refl =>
      fun phi0 : forall x0 : A, x0 = x -> Type =>
      fun phi_y0 : phi0 x eq_refl =>
      phi_y0
    end phi phi_y
  .

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
    { intros x y; constructor.
      - intros H.
        induction H...
        destruct IHle as [z H0].
        exists (S z)...
      - intros H.
        destruct H as [z H]...
    }
    intros a b q r H1 H2.
    assert (H0 : a = b * (a / b) + (a mod b)) by now apply (Nat.div_mod a b); lia.
    assert (H3 : 0 <= a mod b < b) by now apply (Nat.mod_bound_pos a b); lia.
    assert (H4 : ~ q > a / b).
    { intros H4.
      enough (H5 : exists z : nat, q = S (a / b + z))...
      destruct H5 as [z H5].
      enough (b * q + r >= b * S (a / b) + r)...
    }
    assert (H5 : ~ q < a / b).
    { intros H5.
      enough (H6 : exists z : nat, a / b = S (q + z))...
      destruct H6 as [z H6].
      enough (b * q + a mod b >= b * S (a / b) + a mod b)...
    }
    enough (q = a / b)...
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
        destruct (cantor_pairing (z + sum_from_0_to z + 0)) eqn: H0.
        assert (H1 : (0, z) = cantor_pairing (sum_from_0_to z + z))...
        rewrite Nat.add_0_r, Nat.add_comm in H0.
        rewrite H0 in H1.
        inversion H1; subst...
      + intros x H.
        enough (H0 : (S x, y) = cantor_pairing (sum_from_0_to (S z) + y)).
        { assert (H1 : z + sum_from_0_to z + S y = sum_from_0_to (S z) + y) by now simpl...
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

  Definition S_0 {A : Type} : forall n : nat, S n = 0 -> A :=
    fun n : nat =>
    fun H0 : S n = 0 =>
    let H1 : 0 = S n := @eq_ind nat (S n) (fun x : nat => x = S n) eq_refl 0 H0 in
    let H2 : False := @eq_ind nat 0 (fun x : nat => if Nat.eqb x 0 then True else False) I (S n) H1 in
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

  Definition FinSet_case0 {P : FinSet 0 -> Type} : forall i : FinSet 0, P i :=
    fun i : FinSet 0 =>
    match i as i0 in FinSet Sn return Sn = 0 -> P i with
    | FZ n => S_0 n
    | FS n i' => S_0 n
    end eq_refl
  .

  Definition FinSet_caseS {n : nat} {P : FinSet (S n) -> Type} : P (FZ n) -> (forall i' : FinSet n, P (FS n i')) -> (forall i : FinSet (S n), P i) :=
    fun PZ : P (FZ n) =>
    fun PS : forall i' : FinSet n, P (FS n i') =>
    fun i : FinSet (S n) =>
    match i as i0 in FinSet Sn0 return (match Sn0 as Sn1 return FinSet Sn1 -> Type with 0 => FinSet_case0 | S n0 => fun i1 : FinSet (S n0) => forall P0 : FinSet (S n0) -> Type, P0 (FZ n0) -> (forall i' : FinSet n0, P0 (FS n0 i')) -> P0 i1 end) i0 with
    | FZ n0 => fun P0 : FinSet (S n0) -> Type => fun PZ0 : P0 (FZ n0) => fun PS0 : forall i' : FinSet n0, P0 (FS n0 i') => PZ0
    | FS n0 i' => fun P0 : FinSet (S n0) -> Type => fun PZ0 : P0 (FZ n0) => fun PS0 : forall i' : FinSet n0, P0 (FS n0 i') => PS0 i'
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
      | 0 => fun i0' : FinSet 0 => @FinSet_case0 (fun i1 : FinSet 0 => P 1 (FS 0 i1)) i0'
      | S n0' => fun i0' : FinSet (S n0') => PS (S n0') i0' (FinSet_rectS_fix n0' i0')
      end i'
    end
  .

  Lemma forallb_true_iff {A : Type} {p : A -> bool} (xs : list A) :
    forallb p xs = true <-> forall x : A, In x xs -> p x = true.
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
        destruct (proj1 (IHns n) H0) as [i].
        now firstorder.
      + intros H.
        destruct H as [i].
        destruct H.
        destruct H.
        * subst...
        * enough (fold_right max 0 ns > n)...
          apply IHns...
      + intros H.
        exists a...
      + intros H.
        destruct H as [i].
        destruct H.
        destruct H.
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

End MyUtilities.

Module MyStructures.

  Import ListNotations.

  Definition ensemble : Type -> Type :=
    fun A : Type =>
    arrow A Prop
  .

  Definition member {A : Type} : A -> ensemble A -> Prop :=
    fun x : A =>
    fun xs : ensemble A =>
    xs x
  .

  Global Hint Unfold member : my_hints.

  Global Notation "x '\in' xs" := (member x xs) (at level 70, no associativity) : type_scope.

  Definition isSubsetOf {A : Type} : ensemble A -> ensemble A -> Prop :=
    fun xs1 : ensemble A =>
    fun xs2 : ensemble A =>
    forall x : A,
    member x xs1 ->
    member x xs2
  .

  Global Hint Unfold isSubsetOf : my_hints.

  Global Notation "xs1 '\subseteq' xs2" := (isSubsetOf xs1 xs2) (at level 70, no associativity) : type_scope.

  Inductive finite {A : Type} : list A -> ensemble A :=
  | in_finite {x : A} :
    forall xs : list A,
    In x xs ->
    member x (finite xs)
  .

  Global Hint Constructors finite : my_hints.

  Definition empty {A : Type} : ensemble A :=
    finite []
  .

  Lemma in_empty_iff {A : Type} :
    forall x : A,
    member x empty <-> False.
  Proof with eauto with *.
    intros x.
    split...
    intros H.
    inversion H; subst...
  Qed.

  Global Hint Resolve in_empty_iff : my_hints.

  Definition singleton {A : Type} : A -> ensemble A :=
    fun x : A => finite [x]
  .

  Lemma in_singleton_iff {A : Type} :
    forall x : A,
    forall x1 : A,
    member x (singleton x1) <-> x1 = x.
  Proof with eauto with *.
    intros x x1.
    split.
    - intros H.
      inversion H; subst.
      destruct H0 as [H0 | []]...
    - intros H.
      subst...
  Qed.

  Global Hint Resolve in_singleton_iff : my_hints.

  Inductive unions {A : Type} : ensemble (ensemble A) -> ensemble A :=
  | in_unions {x : A} :
    forall xs : ensemble A,
    forall xss : ensemble (ensemble A),
    member x xs ->
    member xs xss ->
    member x (unions xss)
  .

  Global Hint Constructors unions : my_hints.

  Definition union {A : Type} : ensemble A -> ensemble A -> ensemble A :=
    fun xs1 : ensemble A =>
    fun xs2 : ensemble A =>
    unions (finite [xs1; xs2])
  .

  Lemma in_union_iff {A : Type} :
    forall xs1 : ensemble A,
    forall xs2 : ensemble A,
    forall x : A,
    member x (union xs1 xs2) <-> (member x xs1 \/ member x xs2).
  Proof with eauto with *.
    intros xs1 xs2 x.
    split.
    - intros H.
      inversion H; subst.
      inversion H1; subst.
      destruct H2 as [H2 | [H2 | []]]; subst...
    - intros [H | H]; [apply (in_unions xs1) | apply (in_unions xs2)]...
  Qed.

  Global Hint Resolve in_union_iff : my_hints.

  Inductive intersection {A : Type} : ensemble A -> ensemble A -> ensemble A :=
  | in_intersection {x : A} :
    forall xs1 : ensemble A,
    forall xs2 : ensemble A,
    member x xs1 ->
    member x xs2 ->
    member x (intersection xs1 xs2)
  .

  Global Hint Constructors intersection : my_hints.

  Inductive full {A : Type} : ensemble A :=
  | in_full {x : A} :
    member x full
  .

  Global Hint Constructors full : my_hints.

  Inductive image {A : Type} {B : Type} : (A -> B) -> ensemble A -> ensemble B :=
  | in_image {x : A} :
    forall f : A -> B,
    forall xs : ensemble A,
    member x xs ->
    member (f x) (image f xs)
  .

  Global Hint Constructors image : my_hints.

  Inductive preimage {A : Type} {B : Type} : (A -> B) -> ensemble B -> ensemble A :=
  | in_preimage {x : A} :
    forall f : A -> B,
    forall ys : ensemble B,
    member (f x) ys ->
    member x (preimage f ys)
  .

  Global Hint Constructors preimage : my_hints.

  Definition nonempty {A : Type} : ensemble A -> Prop :=
    fun xs : ensemble A =>
    exists x : A, member x xs
  .

  Global Hint Unfold nonempty : my_hints.

  Class isSetoid (A : Type) : Type :=
    { eqProp : A -> A -> Prop
    ; Setoid_requiresEquivalence :> Equivalence eqProp
    }
  .

  Global Notation "x == y" := (eqProp x y) (at level 70, no associativity) : type_scope.

  Lemma Setoid_refl {A : Type} `{A_isSetoid : isSetoid A} :
    forall x1 : A,
    x1 == x1.
  Proof.
    apply Setoid_requiresEquivalence.
  Qed.

  Global Hint Resolve Setoid_refl : my_hints.

  Lemma Setoid_sym {A : Type} `{A_isSetoid : isSetoid A} :
    forall x1 : A,
    forall x2 : A,
    x1 == x2 ->
    x2 == x1.
  Proof.
    apply Setoid_requiresEquivalence.
  Qed.

  Global Hint Resolve Setoid_sym : my_hints.

  Lemma Setoid_trans {A : Type} `{A_isSetoid : isSetoid A} :
    forall x1 : A,
    forall x2 : A,
    forall x3 : A,
    x1 == x2 ->
    x2 == x3 ->
    x1 == x3.
  Proof.
    apply Setoid_requiresEquivalence.
  Qed.

  Global Hint Resolve Setoid_trans : my_hints.

  Definition preservesSetoid {A : Type} {B : Type} `{A_isSetoid : isSetoid A} `{B_isSetoid : isSetoid B} : (A -> B) -> Prop :=
    fun f : A -> B =>
    forall x1 : A,
    forall x2 : A,
    x1 == x2 ->
    f x1 == f x2
  .

  Global Hint Unfold preservesSetoid : my_hints.

  Global Program Instance arrow_isSetoid {A : Type} {B : Type} (B_requiresSetoid : isSetoid B) : isSetoid (A -> B) :=
    { eqProp :=
      fun f1 : A -> B =>
      fun f2 : A -> B =>
      forall x : A,
      f1 x == f2 x
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Global Program Instance ensemble_isSetoid {A : Type} : isSetoid (ensemble A) :=
    { eqProp :=
      fun X1 : ensemble A =>
      fun X2 : ensemble A =>
      forall x : A,
      member x X1 <-> member x X2
    }
  .

  Next Obligation with firstorder with my_hints.
    split...
  Qed.

  Global Program Instance direct_product_of_Setoids_isSetoid {A : Type} {B : Type} (A_requiresSetoid : isSetoid A) (B_requiresSetoid : isSetoid B) : isSetoid (A * B) :=
    { eqProp :=
      fun p1 : A * B =>
      fun p2 : A * B =>
      fst p1 == fst p2 /\ snd p1 == snd p2
    }
  .

  Next Obligation with eauto with *.
    split.
    - intros [x1 y1]...
    - intros [x1 y1] [x2 y2] [H H0]...
    - intros [x1 y1] [x2 y2] [x3 y3] [H H0] [H1 H2]...
  Qed.

  Class isPoset (A : Type) : Type :=
    { leProp : A -> A -> Prop
    ; Poset_requiresSetoid :> isSetoid A
    ; Poset_requiresPreOrder :> PreOrder leProp
    ; Poset_requiresPartialOrder :> PartialOrder eqProp leProp
    }
  .

  Global Notation "x =< y" := (leProp x y) (at level 70, no associativity) : type_scope.

  Lemma Poset_refl {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    x1 =< x1.
  Proof.
    apply Poset_requiresPreOrder.
  Qed.

  Global Hint Resolve Poset_refl : my_hints.

  Lemma Poset_refl1 {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    forall x2 : A,
    x1 == x2 ->
    x1 =< x2.
  Proof.
    apply Poset_requiresPartialOrder.
  Qed.

  Global Hint Resolve Poset_refl1 : my_hints.

  Lemma Poset_refl2 {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    forall x2 : A,
    x1 == x2 ->
    x2 =< x1.
  Proof.
    apply Poset_requiresPartialOrder.
  Qed.

  Global Hint Resolve Poset_refl2 : my_hints.

  Lemma Poset_asym {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    forall x2 : A,
    x1 =< x2 ->
    x2 =< x1 ->
    x1 == x2.
  Proof.
    intros x1 x2 H H0.
    apply Poset_requiresPartialOrder.
    split.
    - apply H.
    - apply H0.
  Qed.

  Global Hint Resolve Poset_asym : my_hints.

  Lemma Poset_trans {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    forall x2 : A,
    forall x3 : A,
    x1 =< x2 ->
    x2 =< x3 ->
    x1 =< x3.
  Proof.
    apply Poset_requiresPreOrder.
  Qed.

  Global Hint Resolve Poset_trans : my_hints.

  Definition isMonotonicMap {A : Type} {B : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} : (A -> B) -> Prop :=
    fun f : A -> B =>
    forall x1 : A,
    forall x2 : A,
    x1 =< x2 ->
    f x1 =< f x2
  .

  Global Hint Unfold isMonotonicMap : my_hints.

  Lemma MonotonicMap_preservesSetoid {A : Type} {B : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} :
    forall f : A -> B,
    isMonotonicMap f ->
    preservesSetoid f.
  Proof with eauto with *.
    unfold isMonotonicMap, preservesSetoid.
    intros f H x1 x2 H0.
    apply Poset_asym...
  Qed.

  Global Hint Unfold MonotonicMap_preservesSetoid : my_hints.

  Definition isSupremum {A : Type} `{A_isPoset : isPoset A} : A -> ensemble A -> Prop :=
    fun sup_X : A =>
    fun X : ensemble A =>
    forall a : A,
    sup_X =< a <-> (forall x : A, member x X -> x =< a)
  .

  Global Hint Unfold isSupremum : my_hints.

  Definition isInfimum {A : Type} `{A_isPoset : isPoset A} : A -> ensemble A -> Prop :=
    fun inf_X : A =>
    fun X : ensemble A =>
    forall a : A,
    a =< inf_X <-> (forall x : A, member x X -> a =< x)
  .

  Global Hint Unfold isInfimum : my_hints.

  Global Program Instance ensemble_isPoset {A : Type} : isPoset (ensemble A) :=
    { leProp := isSubsetOf
    ; Poset_requiresSetoid := ensemble_isSetoid
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Next Obligation with firstorder.
    split...
  Qed.

  Class isTopologicalSpace (A : Type) : Type :=
    { isOpen : ensemble A -> Prop
    ; open_for_full :
      isOpen full
    ; open_for_unions :
      forall xss : ensemble (ensemble A),
      (forall xs : ensemble A, member xs xss -> isOpen xs) ->
      isOpen (unions xss)
    ; open_for_intersection :
      forall xs1 : ensemble A,
      forall xs2 : ensemble A,
      isOpen xs1 ->
      isOpen xs2 ->
      isOpen (intersection xs1 xs2)
    }
  .

  Global Hint Resolve open_for_full : my_hints.

  Global Hint Resolve open_for_unions : my_hints.

  Global Hint Resolve open_for_intersection : my_hints.

  Definition isClosed {A : Type} `{A_isTopologicalSpace : isTopologicalSpace A} : ensemble A -> Prop :=
    fun X : ensemble A =>
    isOpen (fun x : A => ~ member x X)
  .

  Global Hint Unfold isClosed : my_hints.

  Definition isContinuousMap {A : Type} {B : Type} `{A_isTopologicalSpace : isTopologicalSpace A} `{B_isTopologicalSpace : isTopologicalSpace B} : (A -> B) -> Prop :=
    fun f : A -> B =>
    forall ys : ensemble B,
    isOpen ys ->
    isOpen (preimage f ys)
  .

  Global Hint Unfold isContinuousMap : my_hints.

  Inductive sig' {A : Type} : (A -> Prop) -> Type :=
  | exist' {P : A -> Prop} :
    forall x : A,
    P x ->
    sig' P
  .

  Global Hint Constructors sig' : my_hints.

  Definition proj1_sig' {A : Type} {P : A -> Prop} : sig' P -> A :=
    fun sigP : sig' P =>
    match sigP with
    | exist' x H => x
    end
  .

  Definition proj2_sig' {A : Type} {P : A -> Prop} : forall sigP : sig' P, P (proj1_sig' sigP) :=
    fun sigP : sig' P =>
    match sigP with
    | exist' x H => H
    end
  .

  Global Notation "A >=> B" := (@sig' (A -> B) (fun f : A -> B => isContinuousMap f)) (at level 25, no associativity) : type_scope.

  Global Program Instance ContinuousMap_isSetoid {A : Type} {B : Type} (A_requiresTopologicalSpace : isTopologicalSpace A) (B_requiresTopologicalSpace : isTopologicalSpace B) (B_requiresSetoid : isSetoid B) : isSetoid (A >=> B) :=
    { eqProp :=
      fun f1 : A >=> B =>
      fun f2 : A >=> B =>
      forall x : A,
      proj1_sig' f1 x == proj1_sig' f2 x
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

End MyStructures.
