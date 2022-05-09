Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeUtil.

Module MyFin.

  Lemma Fin_eta {n : nat} (i : Fin n) :
    i =
    match n as m return Fin m -> Fin m with
    | zero => Fin_case0
    | suc n' => Fin_caseS (@FZ n') (@FS n')
    end i.
  Proof. destruct i; reflexivity. Defined.

  Definition evalFin {n : nat} (i : Fin n) : nat := proj1_sig (runFin i).

  Lemma evalFin_unfold {n : nat} (i : Fin n) :
    evalFin i =
    match i with
    | FZ => O
    | FS i' => S (evalFin i')
    end.
  Proof. destruct i; reflexivity. Defined.

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

End MyFin.

Module MyVec.

  Import MyFin.

  Global Open Scope vector_scope.

  Fixpoint vector_indexing {A : Type} {n : nat} (xs : vector A n) {struct xs} : Fin n -> A :=
    match xs with
    | [] => Fin_case0
    | x :: xs => Fin_caseS x (vector_indexing xs)
    end
  .

  Global Infix " !! " := vector_indexing (at level 65, left associativity) : vector_scope.

  Lemma vector_indexing_unfold {A : Type} {n : nat} (xs : vector A n) :
    forall i : Fin n,
    xs !! i =
    match i in Fin m return vector A m -> A with
    | @FZ n' => fun v : vector A (S n') => vector_head v
    | @FS n' i' => fun v : vector A (S n') => vector_tail v !! i'
    end xs.
  Proof.
    destruct xs as [ | n' x' xs']; [introFin0 | introFinS i'].
    - exact (eq_reflexivity x').
    - exact (eq_reflexivity (xs' !! i')).
  Defined.

  Global Instance vector_isSetoid (A : Hask.t) (n : nat) {requiresSetoid : isSetoid A} : isSetoid (vector A n) :=
    { eqProp (lhs : vector A n) (rhs : vector A n) := forall i : Fin n, lhs !! i == rhs !! i
    ; eqProp_Equivalence := equivalence_relation_on_image vector_indexing (arrow_isSetoid requiresSetoid)
    }
  .

  Fixpoint vector_map {A : Type} {B : Type} {n : nat} (f : A -> B) (xs : vector A n) {struct xs} : vector B n :=
    match xs with
    | [] => []
    | x :: xs => f x :: vector_map f xs
    end
  .

  Lemma vector_map_spec {A : Type} {B : Type} {n : nat} (f : A -> B) (xs : vector A n)
    : forall i : Fin n, f (xs !! i) = vector_map f xs !! i.
  Proof.
    induction xs as [ | n x xs IH]; [introFin0 | introFinS i].
    all: rewrite vector_indexing_unfold.
    - exact (eq_reflexivity (f x)).
    - exact (IH i).
  Qed.

  Fixpoint diagonal {A : Type} {n : nat} {struct n} : vector (vector A n) n -> vector A n :=
    match n with
    | O => fun xss : vector (vector A O) O => []
    | S n' => fun xss : vector (vector A (S n')) (S n') => vector_head (vector_head xss) :: diagonal (n := n') (vector_map vector_tail (vector_tail xss))
    end
  .

  Lemma diagonal_spec {A : Type} {n : nat} (xss : vector (vector A n) n)
    : forall i : Fin n, xss !! i !! i = diagonal xss !! i.
  Proof.
    revert xss; induction n as [ | n IH].
    - introVNil; introFin0.
    - introVCons xs xss; introFinS i; simpl.
      + now rewrite vector_indexing_unfold.
      + rewrite vector_indexing_unfold, <- IH.
        now rewrite vector_map_spec with (f := vector_tail) (xs := xss) (i := i).
  Qed.

  Fixpoint replicate {A : Type} {n : nat} {struct n} : A -> vector A n :=
    match n with
    | O => fun x : A => []
    | S n' => fun x : A => x :: replicate (n := n') x
    end
  .

  Lemma replicate_spec {A : Type} {n : nat} (x : A)
    : forall i : Fin n, x = replicate x !! i.
  Proof.
    induction n; [introFin0 | introFinS i]; simpl; eauto.
  Qed.

  Ltac reduce_monad_methods_of_vector :=
    first
    [ rewrite <- diagonal_spec
    | rewrite <- vector_map_spec
    | rewrite <- replicate_spec
    ]
  .

  Section VectorIsMonad.

  Definition vec_n (n : nat) (X : Hask.t) : Hask.t := vector X n.

  Global Instance vec_isMonad (n : nat) : isMonad (vec_n n) :=
    { pure {A : Hask.t} (x : A) := replicate x
    ; bind {A : Hask.t} {B : Hask.t} (xs : vec_n n A) (k : A -> vec_n n B) := diagonal (vector_map k xs)
    }
  .

  Local Instance vec_isSetoid1 (n : nat) : isSetoid1 (vec_n n) :=
    { liftSetoid1 {A : Hask.t} (requiresSetoid : isSetoid A) := vector_isSetoid A n (requiresSetoid := requiresSetoid)
    }
  .

  Global Instance vec_obeysMonadLaws (n : nat)
    : LawsOfMonad (vec_n n) (requiresSetoid1 := vec_isSetoid1 n) (requiresMonad := vec_isMonad n).
  Proof. split; cbn; intros; (repeat reduce_monad_methods_of_vector); congruence. Qed.

  Theorem vector_extensional_equality {A : Type} {n : nat} (xs1 : vector A n) (xs2 : vector A n)
    : xs1 = xs2 <-> ⟪ POINTWISE_EQUALITY : forall i : Fin n, xs1 !! i = xs2 !! i ⟫.
  Proof.
    change (eq xs1 xs2 <-> eqProp (isSetoid := freeSetoidFromSetoid1 (vec_n n) A (requiresSetoid1 := vec_isSetoid1 n)) xs1 xs2); split.
    - congruence.
    - revert xs1 xs2; induction n as [ | n IH].
      + introVNil; introVNil; intros hyp_eq.
        exact (eq_reflexivity (@VNil A)).
      + introVCons x1 xs1; introVCons x2 xs2; intros hyp_eq.
        assert (x1_eq_x2 : x1 = x2) by exact (hyp_eq FZ).
        assert (xs1_eq_xs2 : xs1 = xs2) by exact (IH xs1 xs2 (fun i : Fin n => hyp_eq (FS i))).
        exact (eq_congruence2 (@VCons A n) x1 x2 x1_eq_x2 xs1 xs2 xs1_eq_xs2).
  Qed.

  End VectorIsMonad.

  Definition vector_zipWith {A : Type} {B : Type} {C : Type} {n : nat} (f : A -> B -> C) (xs : vector A n) (ys : vector B n) : vector C n :=
    bind (isMonad := vec_isMonad n) xs (fun x : A => bind (isMonad := vec_isMonad n) ys (fun y : B => pure (isMonad := vec_isMonad n) (f x y)))
  .

  Lemma vector_zipWith_spec {A : Type} {B : Type} {C : Type} {n : nat} (f : A -> B -> C) (xs : vector A n) (ys : vector B n)
    : forall i : Fin n, f (xs !! i) (ys !! i) = vector_zipWith f xs ys !! i.
  Proof. cbn; ii; (repeat reduce_monad_methods_of_vector); reflexivity. Qed.

  Fixpoint vector_range {n : nat} {struct n} : nat -> vector nat n :=
    match n with
    | O => fun m : nat => []
    | S n' => fun m : nat => m :: vector_range (n := n') (S m)
    end
  .

  Lemma vector_range_spec {n : nat} (m : nat)
    : forall i : Fin n, evalFin i + m = vector_range m !! i.
  Proof.
    revert m; induction n as [ | n IH]; intros m; [introFin0 | introFinS i].
    - reflexivity.
    - rewrite evalFin_unfold; simpl.
      rewrite <- IH with (m := S m) (i := i).
      eapply Nat.add_succ_comm.
  Qed.

End MyVec.
