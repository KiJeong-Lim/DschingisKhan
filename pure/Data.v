Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Basics.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module MyCategories.

  Import MyUtilities BasicSetoidTheory.

  Global Existing Instance arrow_isSetoid.

  Polymorphic Class isMonad (M : Type -> Type) : Type :=
    { pure {A : Type} : A \to M A
    ; bind {A : Type} {B : Type} : M A -> A \to M B -> M B
    }
  .

  Global Infix " >>= " := bind (at level 90, left associativity) : function_scope.

  Polymorphic Definition fmult {A : Type} {B : Type} {C : Type} (f1 : B \to C) (f2 : A \to B) : A \to C :=
    fun x : A => f1 (f2 x)
  .

  Polymorphic Definition funit {A : Type} : A \to A :=
    fun x : A => x
  .

  Polymorphic Definition kmult {A : Type} {B : Type} {C : Type} {M : Type -> Type} `{M_isMonad : isMonad M} (k1 : B \to M C) (k2 : A \to M B) : A \to M C :=
    fun x : A => bind (k2 x) k1
  .

  Polymorphic Definition kunit {A : Type} {M : Type -> Type} `{M_isMonad : isMonad M} : A \to M A :=
    fun x : A => pure x
  .

  Polymorphic Class isFunctor (F : Type -> Type) : Type :=
    { fmap {_from : Type} {_to : Type} : (_from \to _to) -> (F _from \to F _to)
    }
  .

  Global Infix " `fmult` " := fmult (at level 25, right associativity) : function_scope.
  Global Infix " `kmult` " := kmult (at level 25, right associativity) : function_scope.

  Polymorphic Class isSetoid1 (F : Type -> Type) : Type :=
    { liftSetoid1 {X : Type} :> isSetoid (F X)
    }
  .

  Polymorphic Class obeysFunctorLaws {F : Type -> Type} `{eq1 : isSetoid1 F} `(F_isFunctor : isFunctor F) : Prop :=
    { fmap_fmult_comm {A : Type} {B : Type} {C : Type} :
      forall f1 : B \to C,
      forall f2 : A \to B,
      fmap (_from := A) (_to := C) (f1 `fmult` f2) == fmap (_from := B) (_to := C) f1 `fmult` fmap (_from := A) (_to := B) f2
    ; fmap_funit_comm {A : Type} :
      fmap (_from := A) (_to := A) funit == funit
    }
  .

  Polymorphic Class obeysMonadLaws {M : Type -> Type} `{eq1 : isSetoid1 M} `(M_isMonad : isMonad M) : Prop :=
    { bind_assoc {A : Type} {B : Type} {C : Type} :
      forall m : M A,
      forall k1 : A \to M B,
      forall k2 : B \to M C,
      bind (bind m k1) k2 == bind m (fun x : A => bind (k1 x) k2)
    ; bind_pure_l {A : Type} {B : Type} :
      forall k : A \to M B,
      forall x : A,
      bind (pure x) k == k x
    ; bind_pure_r {A : Type} :
      forall m : M A,
      bind m pure == m
    ; bind_preserves_eq_on_fst_arg {A : Type} {B : Type} :
      forall m1 : M A,
      forall m2 : M A,
      m1 == m2 ->
      forall k : A \to M B,
      bind m1 k == bind m2 k
    ; bind_preserves_eq_on_snd_arg {A : Type} {B : Type} :
      forall k1 : A \to M B,
      forall k2 : A \to M B,
      k1 == k2 ->
      forall m : M A,
      bind m k1 == bind m k2
    }
  .

  Global Polymorphic Instance Monad_isFunctor {M : Type -> Type} `(M_isMonad : isMonad M) : isFunctor M :=
    { fmap {A : Type} {B : Type} :=
      fun f : A -> B =>
      fun m : M A =>
      bind m (pure `fmult` f)
    }
  .

  Global Polymorphic Instance MonadLaws_guarantees_FunctorLaws {M : Type -> Type} `{eq1 : isSetoid1 M} `{M_isMonad : isMonad M} `(M_obeysMonadLaws : @obeysMonadLaws M eq1 M_isMonad) :
    obeysFunctorLaws (eq1 := eq1) (Monad_isFunctor M_isMonad).
  Proof with eauto with *. (* Thanks to Soonwon Moon *)
    enough (claim1 : forall A : Type, forall e : M A, fmap (fun x : A => x) e == e).
    enough (claim2 : forall A : Type, forall B : Type, forall C : Type, forall f1 : B -> C, forall f2 : A -> B, forall e : M A, fmap (f1 `fmult` f2) e == (fmap f1 `fmult` fmap f2) e).
    - constructor...
    - intros A B C f g m.
      symmetry.
      (* Soonwon's Advice:
        (map f . map g) m
        m >>= pure . g >>= pure . f
        m >>= \x -> pure (g x) >>= pure . f
        m >>= \x -> (pure . f) (g x)
        m >>= \x -> pure (f (g x))
        m >>= pure . (f . g)
        map (f . g) m
      *)
      simpl.
      unfold fmult at 1.
      transitivity (m >>= (fun x : A => pure (g x) >>= pure `fmult` f)).
      { rewrite bind_assoc.
        apply bind_preserves_eq_on_snd_arg...
      }
      transitivity (m >>= (fun x : A => (pure `fmult` f) (g x))).
      { apply bind_preserves_eq_on_snd_arg.
        intros x.
        rewrite bind_pure_l...
      }
      reflexivity.
    - intros A e.
      transitivity (bind e (fun x : A => pure x))...
      apply bind_pure_r.
  Qed.

  Global Notation " F1 '-<' F2 " := (forall X : Type, F1 X -> F2 X) (at level 100, no associativity) : type_scope.

  Section OptionIsMonad.

  Global Instance option_isMonad : isMonad option :=
    { pure {A : Type} :=
      fun x : A =>
      Some x
    ; bind {A : Type} {B : Type} :=
      fun m : option A =>
      fun k : A -> option B =>
      maybe None k m
    }
  .

  End OptionIsMonad.

  Section StateTIsMonadTrans.

  Polymorphic Definition stateT (ST : Type) (M : Type -> Type) (X : Type) : Type :=
    ST \to M (prod X ST)
  .

  Polymorphic Definition StateT {ST : Type} {M : Type -> Type} {X : Type} : (ST \to M (prod X ST)) -> stateT ST M X :=
    @funit (stateT ST M X)
  .

  Polymorphic Definition runStateT {ST : Type} {M : Type -> Type} {X : Type} : stateT ST M X -> (ST \to M (prod X ST)) :=
    @funit (stateT ST M X)
  .

  Global Polymorphic Instance stateT_ST_M_isMonad (ST : Type) (M : Type -> Type) `(M_isMonad : isMonad M) : isMonad (stateT ST M) :=
    { pure _ := StateT `fmult` curry pure
    ; bind _ _ := fun m k => StateT (uncurry (runStateT `fmult` k) `kmult` runStateT m)
    }
  .

  Polymorphic Definition lift_stateT {ST : Type} {E : Type -> Type} `{E_isFunctor : isFunctor E} : E -< stateT ST E :=
    fun X : Type =>
    fun e : E X =>
    StateT (fun s : ST => fmap (fun x : X => (x, s)) e)
  .

  End StateTIsMonadTrans.

  Polymorphic Inductive sum1 (F1 : Type -> Type) (F2 : Type -> Type) (X : Type) : Type :=
  | inl1 : F1 X -> sum1 F1 F2 X
  | inr1 : F2 X -> sum1 F1 F2 X
  .

  Global Arguments inl1 {F1} {F2} {X}.
  Global Arguments inr1 {F1} {F2} {X}.

  Global Infix " +' " := sum1 (at level 60, no associativity) : type_scope.

  Global Polymorphic Instance sum1_F1_F2_isFunctor (F1 : Type -> Type) (F2 : Type -> Type) `(F1_isFunctor : isFunctor F1) `(F2_isFunctor : isFunctor F2) : isFunctor (sum1 F1 F2) :=
    { fmap {A : Type} {B : Type} :=
      fun f : A \to B =>
      sum1_rect F1 F2 A (fun _ => sum1 F1 F2 B) (fun l : F1 A => inl1 (fmap f l)) (fun r : F2 A => inr1 (fmap f r))
    }
  .

  Global Declare Scope monad_scope.

  Global Notation " '\do' x '<-' m1 ';' m2 " := (bind m1 (fun x => m2)) (at level 90, left associativity) : monad_scope.
  Global Notation " '\do' m1 ';' m2 " := (bind m1 (fun _ => m2)) (at level 90, left associativity) : monad_scope.
  Global Notation " 'ret' x ';' " := (pure x) (at level 0, x at level 0, no associativity) : monad_scope.

  Global Open Scope monad_scope.

End MyCategories.

Module MyVectors.

  Import EqFacts MyUtilities BasicSetoidTheory MyCategories.

  Inductive vector (A : Type) : nat -> Type :=
  | Vnil : vector A (O)
  | Vcons (n : nat) (x : A) (xs : vector A n) : vector A (S n)
  .

  Global Arguments Vnil {A}.
  Global Arguments Vcons {A}.

  Local Notation " '[]' " := (@Vnil _).
  Local Notation " x '::' xs " := (@Vcons _ _ x xs).

  Section VectorAccessories.

  Context {A : Type}.

  Definition castVec {n : nat} : forall n' : nat, n = n' -> vector A n -> vector A n' :=
    fun n' : nat =>
    fun n_eq_n' : n = n' =>
    match n_eq_n' in eq _ m return vector A n -> vector A m with
    | eq_refl => fun xs : vector A n => xs
    end
  .

  Lemma caseVnil {phi : vector A (O) -> Type}
    (H_nil : phi Vnil)
    (v_nil : vector A (O))
    : phi v_nil.
  Proof.
    refine (
      match v_nil as v in vector _ ze return forall H : ze = 0, phi (castVec 0 H v) with
      | Vnil => fun ze_is_O : O = 0 => _
      | Vcons n' x xs' => fun H_false : S n' = 0 => S_eq_0_elim n' H_false
      end (eq_reflexivity 0)
    ).
    replace (ze_is_O) with (eq_reflexivity 0).
    - exact (H_nil).
    - apply eqnat_proof_irrelevance.
  Defined.

  Lemma caseVcons {n : nat} {phi : vector A (S n) -> Type}
    (H_cons : forall x : A, forall xs : vector A n, phi (x :: xs))
    (v_cons : vector A (S n))
    : phi v_cons.
  Proof.
    refine (
      match v_cons as v in vector _ sc return forall H : sc = S n, phi (castVec (S n) H v) with
      | Vnil => fun H_false : 0 = S n => S_eq_0_elim n (eq_symmetry 0 (S n) H_false)
      | Vcons n' x xs' => fun sc_is_S_n : S n' = S n => _
      end (eq_reflexivity (S n))
    ).
    pose proof (S_eq_S_elim n n' (eq_symmetry (S n') (S n) sc_is_S_n)) as n_eq_n'; subst n'.
    replace (sc_is_S_n) with (eq_reflexivity (S n)).
    - exact (H_cons x xs').
    - apply eqnat_proof_irrelevance.
  Defined.

  Definition vidx : forall n : nat, vector A n -> FinSet n -> A :=
    fix vidx_fix (n : nat) (xs : vector A n) {struct xs} : FinSet n -> A :=
    match xs with
    | Vnil => FinSet_case0
    | Vcons n' x xs' => FinSet_caseS x (vidx_fix n' xs')
    end
  .

  Context {B : Type}.

  Definition vmap (f : A -> B) : forall n : nat, vector A n -> vector B n :=
    fix vmap_fix (n : nat) (xs : vector A n) {struct xs} : vector B n :=
    match xs with
    | Vnil => Vnil
    | Vcons n' x xs' => Vcons n' (f x) (vmap_fix n' xs')
    end
  .

  End VectorAccessories.

  Global Ltac isVnil :=
    let xs' := fresh "xs" in
    intros xs'; pattern xs'; revert xs'; eapply caseVnil
  .

  Global Ltac isVcons x xs :=
    let xs' := fresh "xs" in
    intros xs'; pattern xs'; revert xs'; eapply caseVcons; intros x xs
  .

  Definition vector_head {A : Type} {n' : nat} : vector A (S n') -> A :=
    fun xs : vector A (S n') =>
    match xs in vector _ S_n' return S n' = S_n' -> A with
    | [] => S_eq_0_elim n'
    | x :: xs' => fun _ => x
    end (eq_reflexivity (S n'))
  .

  Definition vector_tail {A : Type} {n' : nat} : vector A (S n') -> vector A n' :=
    fun xs : vector A (S n') =>
    match xs in vector _ S_n' return S n' = S_n' -> vector A (pred S_n') with
    | [] => S_eq_0_elim n'
    | x :: xs' => fun _ => xs'
    end (eq_reflexivity (S n'))
  .

  Lemma Vcons_inj {A : Type} {n' : nat} (x1 : A) (x2 : A) (xs1 : vector A n') (xs2 : vector A n')
    (H_cons_eq : x1 :: xs1 = x2 :: xs2)
    : x1 = x2 /\ xs1 = xs2.
  Proof.
    split.
    - exact (eq_congruence vector_head (x1 :: xs1) (x2 :: xs2) H_cons_eq).
    - exact (eq_congruence vector_tail (x1 :: xs1) (x2 :: xs2) H_cons_eq).
  Qed.

  Lemma Vcons_eta {A : Type} {n' : nat} :
    forall v_cons : vector A (S n'),
    vector_head v_cons :: vector_tail v_cons = v_cons.
  Proof.
    isVcons x xs. exact (eq_reflexivity (x :: xs)).
  Qed.

  Lemma vector_zip_rect {A : Type} {B : Type} {psi : forall n : nat, vector A n -> vector B n -> Type}
    (H_nil : psi (O) [] [])
    (H_cons : forall n' : nat, forall x : A, forall y : B, forall xs' : vector A n', forall ys' : vector B n', psi n' xs' ys' -> psi (S n') (x :: xs') (y :: ys'))
    : forall n : nat, forall xs : vector A n, forall ys : vector B n, psi n xs ys.
  Proof.
    induction xs as [ | n x xs IH].
    - isVnil. exact (H_nil).
    - isVcons y ys. exact (H_cons n x y xs ys (IH ys)).
  Defined.

  Definition vector_indexing {A : Type} {n : nat} : vector A n -> FinSet n -> A :=
    vidx n
  .

  Global Infix " !! " := vector_indexing (at level 65, no associativity).

  Lemma vector_indexing_unfold {A : Type} {n : nat} (xs : vector A n) :
    forall i : FinSet n,
    xs !! i =
    match i in FinSet S_n' return vector A S_n' -> A with
    | FZ n' => fun xs' : vector A (S n') => vector_head xs'
    | FS n' i' => fun xs' : vector A (S n') => vector_tail xs' !! i'
    end xs.
  Proof.
    destruct xs as [ | n' x xs']; [eapply FinSet_case0 | eapply FinSet_caseS].
    - exact (eq_reflexivity x).
    - exact (fun i' : FinSet n' => eq_reflexivity (xs' !! i')).
  Qed.

  Lemma vector_ext_eq {A : Type} {n : nat} (xs1 : vector A n) (xs2 : vector A n)
    (H_EXT_EQ : forall i : FinSet n, xs1 !! i = xs2 !! i)
    : xs1 = xs2.
  Proof.
    revert xs1 xs2 H_EXT_EQ.
    induction xs1 as [ | n x1 xs1 IH].
    - isVnil. intros H_ext_eq.
      reflexivity.
    - isVcons x2 xs2. intros H_ext_eq.
      assert (x1_eq_x2 : vector_head (x1 :: xs1) = vector_head (x2 :: xs2)).
      { exact (H_ext_eq (@FZ n)). }
      assert (xs1_eq_xs2 : vector_tail (x1 :: xs1) = vector_tail (x2 :: xs2)).
      { apply IH. exact (fun i : FinSet n => H_ext_eq (@FS n i)). }
      simpl in *; congruence.
  Qed.

  Definition vector_map {A : Type} {B : Type} {n : nat} : (A -> B) -> vector A n -> vector B n :=
    fun f : A -> B =>
    vmap f n
  .

  Lemma vector_map_spec {A : Type} {B : Type} {n : nat} (f : A -> B) (xs : vector A n)
    : forall i : FinSet n, f (xs !! i) = vector_map f xs !! i.
  Proof.
    induction xs as [ | n x xs IH]; [eapply FinSet_case0 | eapply FinSet_caseS].
    - rewrite vector_indexing_unfold. reflexivity.
    - intros i'. rewrite vector_indexing_unfold. exact (IH i').
  Qed.

  Fixpoint diagonal {A : Type} {n : nat} {struct n} : vector (vector A n) n -> vector A n :=
    match n with
    | O => fun xss : vector (vector A O) O => []
    | S n' => fun xss : vector (vector A (S n')) (S n') => vector_head (vector_head xss) :: diagonal (n := n') (vector_map vector_tail (vector_tail xss))
    end
  .

  Lemma diagonal_spec {A : Type} {n : nat} (xss : vector (vector A n) n)
    : forall i : FinSet n, (xss !! i) !! i = diagonal xss !! i.
  Proof.
    revert xss; induction n as [ | n IH].
    - isVnil. eapply FinSet_case0.
    - isVcons xs xss. eapply FinSet_caseS.
      + now rewrite vector_indexing_unfold.
      + intros i. rewrite vector_indexing_unfold. simpl. rewrite <- IH.
        now rewrite vector_map_spec with (f := vector_tail) (xs := xss) (i := i).
  Qed.

  Fixpoint replicate {A : Type} {n : nat} {struct n} : A -> vector A n :=
    match n with
    | O => fun x : A => []
    | S n' => fun x : A => x :: replicate (n := n') x
    end
  .

  Lemma replicate_spec {A : Type} {n : nat} (x : A)
    : forall i : FinSet n, x = replicate x !! i.
  Proof.
    induction n as [ | n IH]; [eapply FinSet_case0 | eapply FinSet_caseS]; eauto.
  Qed.

  Section VectorIsMonad.

  Variable n : nat.

  Definition vec_n : Type -> Type :=
    fun A : Type =>
    vector A n
  .

  Global Instance vec_isMonad : isMonad vec_n :=
    { pure {A : Type} :=
      fun x : A =>
      replicate x
    ; bind {A : Type} {B : Type} :=
      fun m : vec_n A =>
      fun k : A -> vec_n B =>
      diagonal (vector_map k m)
    }
  .

  Global Instance vec_isSetoid1 : isSetoid1 vec_n :=
    { liftSetoid1 {A : Type} :=
      {| eqProp := @eq (vec_n A); Setoid_requiresEquivalence := @eq_equivalence (vec_n A) |}
    }
  .

  Global Instance vec_obeysMonadLaws :
    obeysMonadLaws vec_isMonad.
  Proof.
    split; cbn; intros; eapply vector_ext_eq; intros i.
    all: repeat (first [rewrite <- diagonal_spec | rewrite <- vector_map_spec | rewrite <- replicate_spec]).
    all: congruence || eauto.
  Qed.

  End VectorIsMonad.

  Definition vector_zip {A : Type} {B : Type} {n : nat} : vector A n -> vector B n -> vector (A * B) n :=
    fun xs : vec_n n A =>
    fun ys : vec_n n B =>
    \do x <- xs;
    \do y <- ys;
    ret (x, y);
  .

  Lemma vector_zip_spec {A : Type} {B : Type} {n : nat} (xs : vector A n) (ys : vector B n)
    : forall i : FinSet n, (xs !! i, ys !! i) = vector_zip xs ys !! i.
  Proof.
    cbn. intros i. now repeat (first [rewrite <- diagonal_spec | rewrite <- vector_map_spec | rewrite <- replicate_spec]).
  Qed.

  Fixpoint vector_range (start : nat) (n : nat) {struct n} : vector nat n :=
    match n with
    | O => []
    | S n' => start :: vector_range (1 + start) n'
    end
  .

  Lemma vector_range_spec (start : nat) (n : nat)
    : forall i : FinSet n, evalFinSet i + start = vector_range start n !! i.
  Proof.
    revert start; induction n as [ | n IH]; intros start; [eapply FinSet_case0 | eapply FinSet_caseS].
    - reflexivity.
    - intros i'. rewrite evalFinSet_caseFS.
      simpl; rewrite <- IH with (start := S start) (i := i').
      apply Nat.add_succ_comm.
  Qed.

End MyVectors.
