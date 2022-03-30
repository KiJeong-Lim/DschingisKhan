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

  Polymorphic Class obeysFunctorLaws {F : Type -> Type} `{eq1 : isSetoid1 F} (F_isFunctor : isFunctor F) : Prop :=
    { fmap_fmult_comm {A : Type} {B : Type} {C : Type} :
      forall f1 : B \to C,
      forall f2 : A \to B,
      fmap (_from := A) (_to := C) (f1 `fmult` f2) == fmap (_from := B) (_to := C) f1 `fmult` fmap (_from := A) (_to := B) f2
    ; fmap_funit_comm {A : Type} :
      fmap (_from := A) (_to := A) funit == funit
    }
  .

  Polymorphic Class obeysMonadLaws {M : Type -> Type} `{eq1 : isSetoid1 M} (M_isMonad : isMonad M) : Prop :=
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

  Global Polymorphic Instance stateT_liftMonad (ST : Type) (M : Type -> Type) `(M_isMonad : isMonad M) : isMonad (stateT ST M) :=
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
      fun f : A \to B => sum1_rect F1 F2 A (fun _ : sum1 F1 F2 A => sum1 F1 F2 B) (fun l : F1 A => inl1 (fmap (F := F1) f l)) (fun r : F2 A => inr1 (fmap (F := F2) f r))
    }
  .

  Polymorphic Class isMonadIter (M : Type -> Type) `{M_isMonad : isMonad M} : Type :=
    { monadic_iter {I : Type} {R : Type} : (I \to M (sum I R)) -> (I \to M R)
    }
  .

  Definition sum_prod_distr {A : Type} {B : Type} {C : Type} : sum A B * C -> prod A C + prod B C :=
    fun pr : sum A B * C =>
    match pr with
    | (inl x, z) => inl (x, z)
    | (inr y, z) => inr (y, z)
    end
  .

  Global Polymorphic Instance stateT_liftMonadIter (ST : Type) (M : Type -> Type) `{M_isMonadIter : isMonadIter M} : isMonadIter (stateT ST M) :=
    { monadic_iter {I : Type} {R : Type} (kont : I \to stateT ST M (sum I R)) :=
      fun x0 : I => StateT (fun s0 : ST => monadic_iter ((pure `fmult` sum_prod_distr) `kmult` uncurry (runStateT `fmult` kont)) (x0, s0))
    }
  .

  Global Declare Scope monad_scope.
  Open Scope monad_scope.

  Global Notation " '\do' x '<-' m1 ';' m2 " := (bind m1 (fun x => m2)) (at level 90, left associativity) : monad_scope.
  Global Notation " '\do' m1 ';' m2 " := (bind m1 (fun _ => m2)) (at level 90, left associativity) : monad_scope.
  Global Notation " 'ret' x ';' " := (pure x) (at level 0, x at level 0, no associativity) : monad_scope.

End MyCategories.

Module DataStructures.

  Global Declare Scope my_data_structrue_scope.
  Open Scope my_data_structrue_scope.

End DataStructures.

Module MyVectors.

  Import EqFacts MyUtilities BasicSetoidTheory MyCategories DataStructures.

  Inductive vector (A : Type) : nat -> Type :=
  | VNil : vector A (O)
  | VCons (n : nat) (x : A) (xs : vector A n) : vector A (S n)
  .

  Global Arguments VNil {A}.
  Global Arguments VCons {A}.

  Global Notation " '[]' " := (@VNil _) (at level 0, no associativity) : my_data_structrue_scope.
  Global Notation " x '::' xs " := (@VCons _ _ x xs) (at level 60, right associativity) : my_data_structrue_scope.
  Bind Scope my_data_structrue_scope with vector.

  Section VectorAccessories.

  Context {A : Type}.

  Definition vector_casting {n : nat} {m : nat} (H_EQ : n = m) : vector A n -> vector A m :=
    match H_EQ in eq _ n0 return vector A n -> vector A n0 with
    | eq_refl => fun xs : vector A n => xs
    end
  .

  Lemma caseOfVNil {phi : vector A (O) -> Type}
    (H_VNil : phi VNil)
    : forall xs : vector A (O), phi xs.
  Proof.
    refine (
      fun xs : vector A (O) =>
      match xs as xs0 in vector _ ze return forall H_EQ : ze = O, phi (vector_casting H_EQ xs0) with
      | VNil => fun H_EQ : O = O => _
      | VCons n' x' xs' => fun H_false : S n' = O => S_eq_0_elim n' H_false
      end (eq_reflexivity O)
    ).
    replace (H_EQ) with (eq_reflexivity O).
    - exact (H_VNil).
    - apply eqnat_proof_irrelevance.
  Defined.

  Lemma caseOfVCons {n : nat} {phi : vector A (S n) -> Type}
    (H_VCons : forall x : A, forall xs' : vector A n, phi (x :: xs'))
    : forall xs : vector A (S n), phi xs.
  Proof.
    refine (
      fun xs : vector A (S n) =>
      match xs as xs0 in vector _ sc return forall H_EQ : sc = S n, phi (vector_casting H_EQ xs0) with
      | VNil => fun H_false : O = S n => S_eq_0_elim n (eq_symmetry O (S n) H_false)
      | VCons n' x' xs' => fun H_EQ : S n' = S n => (fun n_eq_n' : n' = n => _) (S_eq_S_elim n' n H_EQ)
      end (eq_reflexivity (S n))
    ).
    subst n'; replace (H_EQ) with (eq_reflexivity (S n)).
    - exact (H_VCons x' xs').
    - apply eqnat_proof_irrelevance.
  Defined.

  Definition vector_head {n : nat} (xs : vector A (S n)) : A :=
    match xs in vector _ S_n return S n = S_n -> A with
    | VNil => S_eq_0_elim n
    | VCons n' x xs' => fun H_EQ : S n = S n' => x
    end eq_refl
  .

  Definition vector_tail {n : nat} (xs : vector A (S n)) : vector A n :=
    match xs in vector _ S_n return S n = S_n -> vector A (pred S_n) with
    | VNil => S_eq_0_elim n
    | VCons n' x xs' => fun H_EQ : S n = S n' => xs'
    end eq_refl
  .

  Definition vidx : forall n : nat, vector A n -> FinSet n -> A :=
    fix vidx_fix (n : nat) (xs : vector A n) {struct xs} : FinSet n -> A :=
    match xs with
    | VNil => FinSet_case0
    | VCons n' x xs' => FinSet_caseS x (vidx_fix n' xs')
    end
  .

  Context {B : Type}.

  Definition vmap (f : A -> B) : forall n : nat, vector A n -> vector B n :=
    fix vmap_fix (n : nat) (xs : vector A n) {struct xs} : vector B n :=
    match xs with
    | VNil => VNil
    | VCons n' x xs' => VCons n' (f x) (vmap_fix n' xs')
    end
  .

  End VectorAccessories.

  Global Tactic Notation " introVNil " :=
    intro_pattern_revert; eapply caseOfVNil
  .

  Global Tactic Notation " introVCons " ident( _hd ) ident( _tl ) :=
    intro_pattern_revert; eapply caseOfVCons; intros _hd _tl
  .

  Definition vector_indexing {A : Type} {n : nat} : vector A n -> FinSet n -> A :=
    vidx n
  .

  Global Infix " !! " := vector_indexing (at level 65, left associativity).

  Lemma vector_indexing_unfold {A : Type} {n : nat} (xs : vector A n) :
    forall i : FinSet n,
    xs !! i =
    match i in FinSet S_n' return vector A S_n' -> A with
    | FZ n' => fun xs0 : vector A (S n') => vector_head xs0
    | FS n' i' => fun xs0 : vector A (S n') => vector_tail xs0 !! i'
    end xs.
  Proof.
    destruct xs as [ | n' x' xs']; [eapply FinSet_case0 | eapply FinSet_caseS].
    - exact (eq_reflexivity x').
    - exact (fun i' : FinSet n' => eq_reflexivity (xs' !! i')).
  Qed.

  Theorem vector_ext_eq {A : Type} {n : nat} (xs1 : vector A n) (xs2 : vector A n)
    (H_EXT_EQ : forall i : FinSet n, xs1 !! i = xs2 !! i)
    : xs1 = xs2.
  Proof.
    revert xs1 xs2 H_EXT_EQ; induction n as [ | n IH].
    - introVNil; introVNil; intros H_EXT_EQ.
      exact (eq_reflexivity (@VNil A)).
    - introVCons x1 xs1; introVCons x2 xs2; intros H_EXT_EQ.
      assert (x1_eq_x2 : x1 = x2) by exact (H_EXT_EQ (FZ n)).
      assert (xs1_eq_xs2 : xs1 = xs2) by exact (IH xs1 xs2 (fun i : FinSet n => H_EXT_EQ (FS n i))).
      exact (eq_congruence2 (@VCons A n) x1 x2 x1_eq_x2 xs1 xs2 xs1_eq_xs2).
  Qed.

  Definition vector_map {A : Type} {B : Type} {n : nat} (f : A -> B) : vector A n -> vector B n :=
    vmap f n
  .

  Lemma vector_map_spec {A : Type} {B : Type} {n : nat} (f : A -> B) (xs : vector A n)
    : forall i : FinSet n, f (xs !! i) = vector_map f xs !! i.
  Proof.
    induction xs as [ | n x xs IH]; [eapply FinSet_case0 | eapply FinSet_caseS].
    - rewrite vector_indexing_unfold. exact (eq_reflexivity (f x)).
    - intros i. rewrite vector_indexing_unfold. exact (IH i).
  Qed.

  Fixpoint diagonal {A : Type} {n : nat} {struct n} : vector (vector A n) n -> vector A n :=
    match n with
    | O => fun xss : vector (vector A O) O => []
    | S n' => fun xss : vector (vector A (S n')) (S n') => vector_head (vector_head xss) :: diagonal (n := n') (vector_map vector_tail (vector_tail xss))
    end
  .

  Lemma diagonal_spec {A : Type} {n : nat} (xss : vector (vector A n) n)
    : forall i : FinSet n, xss !! i !! i = diagonal xss !! i.
  Proof.
    revert xss; induction n as [ | n IH].
    - introVNil. eapply FinSet_case0.
    - introVCons xs xss. eapply FinSet_caseS; simpl.
      + now rewrite vector_indexing_unfold.
      + intros i. rewrite vector_indexing_unfold, <- IH.
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
    induction n; [eapply FinSet_case0 | eapply FinSet_caseS]; eauto.
  Qed.

  Global Ltac reduce_monad_methods_of_vector :=
    first
    [ rewrite <- diagonal_spec
    | rewrite <- vector_map_spec
    | rewrite <- replicate_spec
    ]
  .

  Section VectorIsMonad.

  Variable n : nat.

  Definition vec_n (X : Type) : Type :=
    vector X n
  .

  Global Instance vec_isMonad : isMonad vec_n :=
    { pure {A : Type} := fun x : A => replicate x
    ; bind {A : Type} {B : Type} := fun m : vec_n A => fun k : A -> vec_n B => diagonal (vector_map k m)
    }
  .

  Global Instance vec_isSetoid1 : isSetoid1 vec_n :=
    { liftSetoid1 {X : Type} := {| eqProp := @eq (vec_n X); Setoid_requiresEquivalence := eq_equivalence |}
    }
  .

  Global Instance vec_obeysMonadLaws :
    obeysMonadLaws vec_isMonad.
  Proof.
    split; cbn; intros; eapply vector_ext_eq; intros ?; (repeat reduce_monad_methods_of_vector); congruence.
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
    cbn; intros i; (repeat reduce_monad_methods_of_vector); exact (eq_reflexivity (xs !! i, ys !! i)).
  Qed.

  Fixpoint vector_range {n : nat} {struct n} : nat -> vector nat n :=
    match n with
    | O => fun m : nat => []
    | S n' => fun m : nat => m :: vector_range (n := n') (S m)
    end
  .

  Lemma vector_range_spec {n : nat} (m : nat)
    : forall i : FinSet n, evalFinSet i + m = vector_range m !! i.
  Proof.
    revert m; induction n as [ | n IH]; intros m; [eapply FinSet_case0 | eapply FinSet_caseS].
    - reflexivity.
    - intros i. rewrite evalFinSet_caseFS.
      simpl; rewrite <- IH with (m := S m) (i := i).
      apply Nat.add_succ_comm.
  Qed.

End MyVectors.

Module MyBinaryTrees.

  Import EqFacts MyUtilities DataStructures.

  Inductive bintree (A : Type) : Type :=
  | BtNil : bintree A
  | BtNode (lchild : bintree A) (key : A) (rchild : bintree A) : bintree A 
  .

  Global Arguments BtNil {A}.
  Global Arguments BtNode {A}.

  Global Notation " '[^]' " := (@BtNil _) (at level 0) : my_data_structrue_scope.
  Global Notation " '[^'  lchild ']++<' key '>++[' rchild  '^]' " := (@BtNode _ lchild key rchild) (lchild at level 60, key at level 65, rchild at level 60, at level 0) : my_data_structrue_scope.
  Bind Scope my_data_structrue_scope with bintree.

End MyBinaryTrees.
