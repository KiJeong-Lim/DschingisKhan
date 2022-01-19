Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.pure.DomainTheory.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.
Require Import DschingisKhan.classical.ExclusiveMiddle.

Module MyCategories.

  Import MyUtilities BasicSetoidTheory.

  Global Declare Scope monad_scope.

  Polymorphic Class isMonad (M : Type -> Type) : Type :=
    { pure {A : Type} : A -> M A
    ; bind {A : Type} {B : Type} : M A -> (A -> M B) -> M B
    }
  .

  Global Infix " >>= " := bind (at level 90, left associativity) : function_scope.

  Global Notation " '\do' x '<-' m1 ';' m2 " := (bind m1 (fun x => m2)) (at level 90, left associativity) : monad_scope.
  Global Notation " '\do' m1 ';' m2 " := (bind m1 (fun _ => m2)) (at level 90, left associativity) : monad_scope.
  Global Notation " 'ret' x ';' " := (pure x) (at level 0, x at level 0, no associativity) : monad_scope.

  Polymorphic Definition from_to_ (A : Type) (B : Type) : Type :=
    A -> B
  .

  Local Polymorphic Program Instance lift_eqProp (A : Type) (B : Type) `{B_isSetoid : isSetoid B} : isSetoid (from_to_ A B) :=
    { eqProp :=
      fun f1 : from_to_ A B =>
      fun f2 : from_to_ A B =>
      forall x : A,
      f1 x == f2 x
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Local Infix " '\to' " := from_to_ (at level 100, right associativity) : type_scope.

  Polymorphic Definition fmult {A : Type} {B : Type} {C : Type} (f1 : B \to C) (f2 : A \to B) : A \to C :=
    fun x : A => f1 (f2 x)
  .

  Polymorphic Definition funit {A : Type} : A \to A :=
    fun x : A => x
  .

  Polymorphic Definition kmult {A : Type} {B : Type} {C : Type} {M : Type -> Type} `{M_isMonad : isMonad M} (k1 : B \to M C) (k2 : A \to M B) : A \to M C :=
    fun x : A => k2 x >>= k1
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
    { eqProp1 {X : Type} :> isSetoid (F X)
    }
  .

  Polymorphic Class obeysFunctorLaws {F : Type -> Type} `{eq1 : isSetoid1 F} `(F_isFunctor : isFunctor F) : Prop :=
    { fmap_fmult_comm {A : Type} {B : Type} {C : Type} :
      forall f1 : B \to C,
      forall f2 : A \to B,
      fmap (_from := A) (_to := C) (f1 `fmult` f2) == (fmap (_from := B) (_to := C) f1 `fmult` fmap (_from := A) (_to := B) f2)
    ; fmap_funit_comm {A : Type} :
      fmap (_from := A) (_to := A) funit == funit
    }
  .

  Polymorphic Class obeysMonadLaws {M : Type -> Type} `{eq1 : isSetoid1 M} `(M_isMonad : isMonad M) : Prop :=
    { bind_assoc {A : Type} {B : Type} {C : Type} :
      forall m : M A,
      forall k1 : A -> M B,
      forall k2 : B -> M C,
      ((m >>= k1) >>= k2) == (m >>= (fun x : A => k1 x >>= k2))
    ; bind_pure_l {A : Type} {B : Type} :
      forall k : A -> M B,
      forall x : A,
      bind (pure x) k == k x
    ; bind_pure_r {A : Type} :
      forall m : M A,
      bind m pure == m
    ; bind_preserves_eq_on_fst {A : Type} {B : Type} :
      forall m1 : M A,
      forall m2 : M A,
      m1 == m2 ->
      forall k : A \to M B,
      (m1 >>= k) == (m2 >>= k)
    ; bind_preserves_eq_on_snd {A : Type} {B : Type} :
      forall k1 : A \to M B,
      forall k2 : A \to M B,
      k1 == k2 ->
      forall m : M A,
      (m >>= k1) == (m >>= k2)
    }
  .

  Global Polymorphic Instance Monad_isFunctor {M : Type -> Type} `(M_isMonad : isMonad M) : isFunctor M :=
    { fmap {A : Type} {B : Type} :=
      fun f : A -> B =>
      fun m : M A =>
      bind m (pure `fmult` f)
    }
  .

  Global Polymorphic Instance MonadLaws_guarantees_FunctorLaws {M : Type -> Type} `{eq1 : isSetoid1 M} `(M_isMonad : isMonad M) (M_obeysMonadLaws : obeysMonadLaws (eq1 := eq1) M_isMonad) :
    obeysFunctorLaws (eq1 := eq1) (Monad_isFunctor M_isMonad).
  Proof with eauto. (* Thanks to Soonwon Moon *)
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
        apply bind_preserves_eq_on_snd.
        reflexivity.
      }
      transitivity (m >>= (fun x : A => (pure `fmult` f) (g x))).
      { apply bind_preserves_eq_on_snd.
        intros x.
        rewrite bind_pure_l.
        reflexivity.
      }
      reflexivity.
    - intros A e.
      transitivity (bind e (fun x : A => pure x)).
      + reflexivity.
      + apply bind_pure_r.
  Qed.

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

  Polymorphic Definition stateT (ST : Type) (M : Type -> Type) (X : Type) : Type :=
    ST -> M (X * ST)%type
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

  Global Notation " F1 '-<' F2 " := (forall X : Type, F1 X -> F2 X) (at level 100, no associativity) : type_scope.

  Polymorphic Definition lift_stateT {ST : Type} {E : Type -> Type} `{E_isFunctor : isFunctor E} : E -< stateT ST E :=
    fun X : Type =>
    fun e : E X =>
    StateT (fun s : ST => fmap (fun x : X => (x, s)) e)
  .

  Polymorphic Inductive sum1 (F1 : Type -> Type) (F2 : Type -> Type) (X : Type) : Type :=
  | inl1 : F1 X -> sum1 F1 F2 X
  | inr1 : F2 X -> sum1 F1 F2 X
  .

  Global Arguments inl1 {F1} {F2} {X}.
  Global Arguments inr1 {F1} {F2} {X}.

  Global Infix " +' " := sum1 (at level 60, no associativity) : type_scope.

  Global Polymorphic Instance sum1_F1_F2_isFunctor (F1 : Type -> Type) (F2 : Type -> Type) `(F1_isFunctor : isFunctor F1) `(F2_isFunctor : isFunctor F2) : isFunctor (sum1 F1 F2) :=
    { fmap {A : Type} {B : Type} :=
      fun f : from_to_ A B =>
      sum1_rect F1 F2 A (fun _ => sum1 F1 F2 B) (fun l : F1 A => inl1 (fmap f l)) (fun r : F2 A => inr1 (fmap f r))
    }
  .

  Global Open Scope monad_scope.

End MyCategories.

Module InteractionTree. (* Reference: "https://sf.snu.ac.kr/publications/itrees.pdf" *)

  Import MyCategories.

  Variant itreeF (itree_E_R : Type) (E : Type -> Type) (R : Type) : Type :=
  | RetF (r : R) : itreeF itree_E_R E R
  | TauF (t : itree_E_R) : itreeF itree_E_R E R
  | VisF (X : Type) (e : E X) (k : X -> itree_E_R) : itreeF itree_E_R E R
  .

  Set Primitive Projections.

  CoInductive itree (E : Type -> Type) (R : Type) : Type :=
    go { observe : itreeF (itree E R) E R }
  .

  Unset Primitive Projections.

  Global Arguments RetF {itree_E_R} {E} {R} (r).
  Global Arguments TauF {itree_E_R} {E} {R} (t).
  Global Arguments VisF {itree_E_R} {E} {R} (X) (e) (k).

  Global Arguments go {E} {R}.
  Global Arguments observe {E} {R}.

  Global Notation Ret r := (go (RetF r)).
  Global Notation Tau t := (go (TauF t)).
  Global Notation Vis X e k := (go (VisF X e k)).

  Section ITREE_BIND. (* Reference: "https://github.com/DeepSpec/InteractionTrees/blob/5fe86a6bb72f85b5fcb125da10012d795226cf3a/theories/Core/ITreeMonad.v" *)

  Context {E : Type -> Type} {R1 : Type} {R2 : Type}.

  Variable from_leaf : R1 -> itree E R2.

  Definition expand_leaves_progress (CIH : itree E R1 -> itree E R2) (ot : itreeF (itree E R1) E R1) : itree E R2 :=
    match ot with
    | RetF r => from_leaf r
    | TauF t => Tau (CIH t)
    | VisF X e k => Vis X e (fun x : X => CIH (k x))
    end
  .

  CoFixpoint expand_leaves (t : itree E R1) : itree E R2 :=
    expand_leaves_progress expand_leaves (observe t)
  .

  End ITREE_BIND.

  Global Instance itree_E_isMonad (E : Type -> Type) : isMonad (itree E) :=
    { pure {R : Type} :=
      fun r : R =>
      Ret r
    ; bind {R1 : Type} {R2 : Type} :=
      fun m : itree E R1 =>
      fun k : R1 -> itree E R2 =>
      expand_leaves k m
    }
  .

  Definition burn_tau {E : Type -> Type} {R : Type} : nat -> itree E R -> itree E R :=
    fix burn_tau_fix (n : nat) (t : itree E R) {struct n} : itree E R :=
    match n with
    | O => t
    | S n' =>
      match observe t with
      | RetF r => Ret r
      | TauF t' => burn_tau_fix n' t'
      | VisF X e k => Vis X e k
      end
    end
  .

  Definition itree_trigger {E : Type -> Type} : E -< itree E :=
    fun R : Type =>
    fun e : E R =>
    Vis R e (fun x : R => Ret x)
  .

  Definition itree_iter {E : Type -> Type} {R : Type} {I : Type} (step : I -> itree E (I + R)) : I -> itree E R :=
    cofix itree_iter_cofix (i : I) : itree E R :=
    expand_leaves (@sum_rect I R (fun _ => itree E R) (fun l : I => Tau (itree_iter_cofix l)) (fun r : R => Ret r)) (step i)
  .

  Definition itree_interpret_stateT {E : Type -> Type} {E' : Type -> Type} {ST : Type} (handle : E -< stateT ST (itree E')) : itree E -< stateT ST (itree E') :=
    fun R : Type =>
    let iter := curry `fmult` itree_iter (E := E') (R := R * ST) (I := itree E R * ST) `fmult` uncurry in
    iter (fun t0 : itree E R => fun s : ST =>
      match observe t0 with
      | RetF r => ret (inr (r, s));
      | TauF t => ret (inl (t, s));
      | VisF X e k => \do h_res <- handle X e s; ret (inl (k (fst h_res), snd h_res));
      end
    )
  .

  Inductive callE (A : Type) (B : Type) : Type -> Type :=
  | Call (arg : A) : callE A B B
  .

  Global Arguments Call {A} {B}.

  Section RECURSION. (* Reference: "https://github.com/DeepSpec/InteractionTrees/blob/5fe86a6bb72f85b5fcb125da10012d795226cf3a/theories/Interp/Recursion.v" *)

  Local Notation endo X := (X -> X).

  Definition itree_interpret_mrec {E : Type -> Type} {E' : Type -> Type} (ctx : E -< itree (E +' E')) : itree (E +' E') -< itree E' :=
    fun R : Type =>
    let iter := itree_iter (E := E') (R := R) (I := itree (E +' E') R) in
    iter (fun t0 : itree (E +' E') R =>
      match observe t0 with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl t)
      | VisF X e k =>
        match e with
        | inl1 l => Ret (inl (ctx X l >>= k))
        | inr1 r => Vis X r (fun x : X => Ret (inl (k x)))
        end
      end
    )
  .

  Definition itree_mrec {E : Type -> Type} {E' : Type -> Type} (ctx : E -< itree (E +' E')) : E -< itree E' :=
    fun R : Type =>
    fun e : E R =>
    itree_interpret_mrec (E := E) (E' := E') ctx R (ctx R e)
  .

  Definition itree_trigger_inl1 {E : Type -> Type} {E' : Type -> Type} : E -< itree (E +' E') :=
    fun R : Type =>
    fun e : E R =>
    itree_trigger (E := E +' E') R (inl1 e)
  .

  Definition itree_mrec_fix {E : Type -> Type} {E' : Type -> Type} (ctx : endo (E -< itree (E +' E'))) : E -< itree E' :=
    itree_mrec (E := E) (E' := E') (ctx itree_trigger_inl1)
  .

  Definition calling {E : Type -> Type} {A : Type} {B : Type} (callee : A -> itree E B) : callE A B -< itree E :=
    fun R : Type =>
    fun e : callE A B R =>
    match e in callE _ _ X return itree E X with
    | Call arg => callee arg
    end
  .

  Definition itree_rec {E : Type -> Type} {A : Type} {B : Type} (body : A -> itree (callE A B +' E) B) (arg : A) : itree E B :=
    itree_mrec (E := callE A B) (E' := E) (calling body) B (Call arg)
  .

  Definition itree_call {E : Type -> Type} {A : Type} {B : Type} (arg : A) : itree (callE A B +' E) B :=
    itree_trigger (E := callE A B +' E) B (inl1 (Call arg))
  .

  Definition itree_rec_fix {E : Type -> Type} {A : Type} {B : Type} (body : endo (A -> itree (callE A B +' E) B)) (arg : A) : itree E B :=
    itree_rec (E := E) (A := A) (B := B) (body itree_call) arg
  .

  End RECURSION.

End InteractionTree.

Module InteractionTreeTheory.

  Import EqFacts BasicSetoidTheory MyEnsemble BasicPosetTheory ConstructiveCoLaTheory PowerSetCoLa MyCategories InteractionTree.

  Section ITREE_EQUALITY. (* Reference: "https://github.com/snu-sf/InteractionTrees/blob/72d78f8b08a86c4609a27c4f8bce1ae876fbc22e/theories/Eq/Eq.v" *)

  Context {E : Type -> Type} {R : Type}.

  Variant eq_itreeF (sim : itree E R -> itree E R -> Prop) : itreeF (itree E R) E R -> itreeF (itree E R) E R -> Prop :=
  | EqRet (r1 : R) (r2 : R) (H_rel : r1 = r2) :
    eq_itreeF sim (RetF r1) (RetF r2)
  | EqTau (t1 : itree E R) (t2 : itree E R) (H_rel : sim t1 t2) :
    eq_itreeF sim (TauF t1) (TauF t2)
  | EqVis (X : Type) (e : E X) (k1 : X -> itree E R) (k2 : X -> itree E R) (H_rel : forall x : X, sim (k1 x) (k2 x)) :
    eq_itreeF sim (VisF X e k1) (VisF X e k2)
  .

  Local Hint Constructors eq_itreeF : core.

  Definition eqITreeF (sim : ensemble (itree E R * itree E R)) : ensemble (itree E R * itree E R) :=
    uncurry (fun t1 : itree E R => fun t2 : itree E R => eq_itreeF (curry sim) (observe t1) (observe t2))
  .

  Lemma eqITreeF_isMonotonic :
    isMonotonicMap eqITreeF.
  Proof with eauto.
    unfold eqITreeF, uncurry.
    intros R1 R2 H_R1_le_R2.
    intros [? ?] [r1 r2 REL | t1 t2 REL | X e k1 k2 REL]; [pose (REL) | pose (H_R1_le_R2 (t1, t2) REL) | pose (fun x : X => H_R1_le_R2 (k1 x, k2 x) (REL x))]...
  Qed.

  Local Hint Resolve eqITreeF_isMonotonic : core.

  Definition eqITree (t1 : itree E R) (t2 : itree E R) : Prop :=
    member (t1, t2) (proj1_sig (nu (exist isMonotonicMap eqITreeF eqITreeF_isMonotonic)))
  .

  Lemma not_in_bot :
    forall t1 : itree E R,
    forall t2 : itree E R,
    ~ member (t1, t2) bot.
  Proof.
    intros t1 t2 H_in.
    unfold bot in H_in.
    simpl in H_in.
    apply in_unions_iff in H_in.
    destruct H_in as [X [H_in_X H_X_in]].
    apply in_finite_iff in H_X_in.
    inversion H_X_in.
  Qed.

  Definition or_plus (REL1 : ensemble (itree E R * itree E R)) (REL2 : ensemble (itree E R * itree E R)) : ensemble (itree E R * itree E R) :=
    union REL1 REL2
  .

  Lemma or_plus_is :
    ConstructiveCoLaTheory.or_plus = or_plus.
  Proof.
    reflexivity.
  Defined.

  Local Hint Rewrite or_plus_is : core.

  Definition MyUnion (REL1 : ensemble (itree E R * itree E R)) (REL2 : ensemble (itree E R * itree E R)) : ensemble (itree E R * itree E R) :=
    fun two_trees : itree E R * itree E R =>
    member two_trees REL1 \/ member two_trees REL2
  .

  Lemma or_plus_eq_MyUnion (REL1 : ensemble (itree E R * itree E R)) (REL2 : ensemble (itree E R * itree E R)) :
    or_plus REL1 REL2 == MyUnion REL1 REL2.
  Proof.
    exact (fun two_trees : itree E R * itree E R => in_union_iff two_trees REL1 REL2).
  Qed.

  Local Hint Resolve or_plus_eq_MyUnion : core.

  Definition rel_id : ensemble (itree E R * itree E R) :=
    uncurry eq
  .

  Lemma eqITree_refl :
    isSubsetOf rel_id (PaCo eqITreeF bot).
  Proof with eauto with *.
    apply PaCo_acc...
    set (REL := or_plus bot rel_id).
    transitivity (eqITreeF (or_plus (PaCo eqITreeF REL) REL)).
    - intros [lhs rhs] H_lhs_eq_rhs.
      unfold eqITreeF, member.
      unfold uncurry at 1.
      unfold member, rel_id, uncurry in H_lhs_eq_rhs.
      destruct (observe lhs) as [r1 | t1 | X1 e1 k1] eqn: H_lhs_obs;
      destruct (observe rhs) as [r2 | t2 | X2 e2 k2] eqn: H_rhs_obs;
      try congruence.
      + constructor 1.
        congruence.
      + constructor 2.
        unfold curry, uncurry.
        apply in_union_iff; right.
        apply in_union_iff; right.
        congruence.
      + assert (claim1 : @eq (itreeF (itree E R) E R) (VisF X1 e1 k1) (VisF X2 e2 k2)) by congruence.
        rewrite claim1.
        constructor 3.
        unfold curry, uncurry.
        intros x.
        apply in_union_iff; right.
        apply in_union_iff; right.
        congruence.
    - fold (MyUnion bot rel_id).
      transitivity (PaCo eqITreeF (or_plus bot (uncurry eq))).
      + apply PaCo_fold.
      + apply (PaCo_preserves_monotonicity eqITreeF eqITreeF_isMonotonic)...
  Qed.

  Local Instance eqITree_Reflexive :
    Reflexive eqITree.
  Proof.
    intros t1.
    apply PaCo_init.
    exact (eqITree_refl (t1, t1) eq_refl).
  Qed.

  Definition rel_flip (REL1 : ensemble (itree E R * itree E R)) : ensemble (itree E R * itree E R) :=
    fun two_trees : itree E R * itree E R =>
    member (snd two_trees, fst two_trees) REL1
  .

  Lemma eqITree_sym :
    isSubsetOf (rel_flip (PaCo eqITreeF bot)) (PaCo eqITreeF bot).
  Proof with eauto with *.
    apply PaCo_acc...
    set (REL := MyUnion bot (rel_flip (PaCo eqITreeF bot))).
    transitivity (eqITreeF (or_plus (PaCo eqITreeF REL) REL)); [ | apply PaCo_fold].
    intros [lhs rhs] H_lhs_eq_rhs.
    unfold member, rel_flip in H_lhs_eq_rhs.
    simpl in H_lhs_eq_rhs.
    apply PaCo_unfold in H_lhs_eq_rhs...
    replace (ConstructiveCoLaTheory.or_plus) with or_plus in H_lhs_eq_rhs...
    unfold eqITreeF in H_lhs_eq_rhs.
    unfold eqITreeF.
    unfold uncurry, curry, member in *.
    destruct H_lhs_eq_rhs as [r1 r2 H_rel | t1 t2 H_rel | X e k1 k2 H_rel].
    - constructor 1.
      congruence.
    - apply in_union_iff in H_rel.
      destruct H_rel as [H_rel | H_rel]; [ | contradiction (not_in_bot t1 t2 H_rel)].
      constructor 2.
      apply in_union_iff; right.
      right...
    - constructor 3.
      intros x.
      assert (claim1 := H_rel x).
      apply in_union_iff in claim1.
      destruct claim1 as [claim1 | claim1]; [ | contradiction (not_in_bot (k1 x) (k2 x) claim1)].
      apply in_union_iff; right.
      right...
  Qed.

  Local Instance eqITree_Symmetric :
    Symmetric eqITree.
  Proof.
    intros t1 t2.
    intros H_t1_eq_t2.
    apply PaCo_init in H_t1_eq_t2.
    apply PaCo_init.
    exact (eqITree_sym (t2, t1) H_t1_eq_t2).
  Qed.

  Definition rel_comp (REL1 : ensemble (itree E R * itree E R)) (REL2 : ensemble (itree E R * itree E R)) : ensemble (itree E R * itree E R) :=
    fun two_trees : itree E R * itree E R =>
    exists t : itree E R, member (fst two_trees, t) REL1 /\ member (t, snd two_trees) REL2
  .

  Lemma eqITree_trans :
    isSubsetOf (rel_comp (PaCo eqITreeF bot) (PaCo eqITreeF bot)) (PaCo eqITreeF bot).
  Proof with eauto with *.
    apply PaCo_acc...
    set (REL := MyUnion bot (rel_comp (PaCo eqITreeF bot) (PaCo eqITreeF bot))).
    assert (claim1 : isSubsetOf (eqITreeF (or_plus (PaCo eqITreeF bot) bot)) (eqITreeF (or_plus (PaCo eqITreeF REL) REL))).
    { apply (eqITreeF_isMonotonic (or_plus (PaCo eqITreeF bot) bot) (or_plus (PaCo eqITreeF REL) REL)).
      intros [t1 t2] H_in.
      apply in_union_iff in H_in.
      destruct H_in as [H_in | H_in].
      - apply in_union_iff.
        left.
        apply (PaCo_preserves_monotonicity eqITreeF eqITreeF_isMonotonic bot REL)...
      - contradiction (not_in_bot t1 t2 H_in).
    }
    transitivity (eqITreeF (or_plus (PaCo eqITreeF REL) REL)); [ | apply PaCo_fold].
    intros [lhs rhs] H_lhs_eq_rhs.
    unfold rel_comp, member in H_lhs_eq_rhs.
    simpl in H_lhs_eq_rhs.
    destruct H_lhs_eq_rhs as [t [H_lhs_eq_t H_t_eq_rhs]].
    apply PaCo_unfold in H_lhs_eq_t...
    replace (ConstructiveCoLaTheory.or_plus) with or_plus in H_lhs_eq_t...
    apply PaCo_unfold in H_t_eq_rhs...
    replace (ConstructiveCoLaTheory.or_plus) with or_plus in H_t_eq_rhs...
    unfold eqITreeF in H_lhs_eq_t, H_t_eq_rhs.
    unfold eqITreeF.
    unfold uncurry, curry, member in *.
    destruct (observe t) as [r3 | t3 | X3 e3 k3] eqn: H_t_obs.
    - inversion H_lhs_eq_t; subst.
      inversion H_t_eq_rhs; subst.
      rename H0 into H_lhs_obs, H into H_rhs_obs.
      constructor 1.
      congruence.
    - inversion H_lhs_eq_t; subst.
      rename H_rel into H_rel1.
      inversion H_t_eq_rhs; subst.
      rename H_rel into H_rel2.
      apply in_union_iff in H_rel1, H_rel2.
      destruct H_rel1 as [H_rel1 | H_rel1]; [ | contradiction (not_in_bot t1 t3 H_rel1)].
      destruct H_rel2 as [H_rel2 | H_rel2]; [ | contradiction (not_in_bot t3 t2 H_rel2)].
      rename H0 into H_lhs_obs, H into H_rhs_obs.
      constructor 2.
      apply in_union_iff; right.
      right.
      exists t3.
      split; unfold eqITreeF, member; simpl...
    - rewrite <- H_t_obs in H_lhs_eq_t, H_t_eq_rhs.
      revert H_t_obs.
      destruct H_t_eq_rhs as [r2' r2 H_rel2 | t2' t2 H_rel2 | X2 e2 k2' k2 H_rel2]; try congruence.
      intros H_t_obs.
      rewrite H_t_obs in H_lhs_eq_t.
      destruct H_lhs_eq_t as [r1 r1' H_rel1 | t1 t1' H_rel1 | X1 e1 k1 k1' H_rel1]; try congruence.
      assert (H_X_eq_X : X1 = X2) by now symmetry; apply (eq_congruence (fun ot : itreeF (itree E R) E R => match ot with | VisF X e k => X | _ => X1 end) _ _ H_t_obs).
      subst X2.
      rename X1 into X.
      enough (H_e_eq_e : e1 = e2).
      enough (H_k_eq_k : k1' = k2').
      subst e2.
      rename e1 into e.
      subst k2'.
      rename k1' into k.
      constructor 3.
      intros x.
      assert (claim2 := H_rel1 x).
      assert (claim3 := H_rel2 x).
      apply in_union_iff in claim2, claim3.
      destruct claim2 as [claim2 | claim2]; [ | contradiction (not_in_bot (k1 x) (k x) claim2)].
      destruct claim3 as [claim3 | claim3]; [ | contradiction (not_in_bot (k x) (k2 x) claim3)].
      apply in_union_iff; right.
      right.
      exists (k x).
      split; unfold eqITreeF, member; simpl...
      { inversion H_t_obs.
        apply (ExclusiveMiddle.existT_inj2_eq Type (fun X : Type => X -> itree E R) X k1' k2')...
      }
      { inversion H_t_obs.
        apply (ExclusiveMiddle.existT_inj2_eq Type (fun X : Type => E X) X e1 e2)...
      }
  Qed.

  Local Instance eqITree_Transitive :
    Transitive eqITree.
  Proof.
    intros t1 t2 t3 H_t1_eq_t2 H_t2_eq_t3.
    apply PaCo_init in H_t1_eq_t2, H_t2_eq_t3.
    apply PaCo_init.
    exact (eqITree_trans (t1, t3) (ex_intro _ t2 (conj H_t1_eq_t2 H_t2_eq_t3))).
  Qed.

  End ITREE_EQUALITY.

  Global Add Parametric Relation {E : Type -> Type} {R : Type} : (itree E R) (eqITree (E := E) (R := R))
    reflexivity proved by (eqITree_Reflexive (E := E) (R := R))
    symmetry proved by (eqITree_Symmetric (E := E) (R := R))
    transitivity proved by (eqITree_Transitive (E := E) (R := R))
  as eqITree_Equivalence.

  Global Instance itree_E_R_isSetoid {E : Type -> Type} {R : Type} : isSetoid (itree E R) :=
    { eqProp := eqITree (E := E) (R := R)
    ; Setoid_requiresEquivalence := eqITree_Equivalence (E := E) (R := R)
    }
  .

  Local Hint Resolve eqITreeF_isMonotonic : core.

  Lemma bot_is_empty {A : Type} :
    forall x : A,
    ~ member x bot.
  Proof.
    intros x.
    assert (clami1 := @in_empty_iff (ensemble A)).
    intros H_x_in.
    apply in_unions_iff in H_x_in.
    firstorder.
  Qed.

  Local Hint Resolve bot_is_empty : core.

  Lemma eqITree_intro_obs_eq_obs {E : Type -> Type} {R : Type} :
    forall lhs : itree E R,
    forall rhs : itree E R,
    observe lhs = observe rhs ->
    lhs == rhs.
  Proof with eauto.
    intros lhs rhs H_obs_eq_obs.
    apply PaCo_init.
    apply PaCo_fold.
    assert (claim1 := eqITree_Reflexive lhs).
    apply PaCo_init in claim1.
    apply PaCo_unfold in claim1...
    unfold eqITreeF, member, curry, uncurry in *.
    congruence.
  Qed.

  Lemma itree_eta {E : Type -> Type} {R : Type} :
    forall t : itree E R,
    go (observe t) == t.
  Proof with eauto with *.
    intros t.
    assert (claim1 := eqITree_intro_obs_eq_obs t (go (observe t)))...
  Qed.

  Definition rel_image {E : Type -> Type} {R1 : Type} {R2 : Type} (k : R1 -> itree E R2) (REL1 : ensemble (itree E R1 * itree E R1)) : ensemble (itree E R2 * itree E R2) :=
    image (fun two_trees : itree E R1 * itree E R1 => (fst two_trees >>= k, snd two_trees >>= k)) REL1
  .

  Lemma expand_leaves_preserves_snd_arg {E : Type -> Type} {R1 : Type} {R2 : Type} :
    forall k : R1 -> itree E R2,
    isSubsetOf (rel_image k (PaCo eqITreeF bot)) (PaCo eqITreeF bot).
  Proof with eauto with *.
    intros k0.
    assert (claim1 : forall t : itree E R1, observe (expand_leaves k0 t) = observe (expand_leaves_progress k0 (expand_leaves k0) (observe t))) by reflexivity.
    apply PaCo_acc...
    set (REL := MyUnion bot (rel_image k0 (PaCo eqITreeF bot))).
    transitivity (eqITreeF (or_plus (PaCo eqITreeF REL) REL)); [ | apply PaCo_fold].
    intros [k0_lhs k0_rhs] H_k0_lhs_eq_k0_rhs.
    unfold member, rel_image in H_k0_lhs_eq_k0_rhs.
    simpl in H_k0_lhs_eq_k0_rhs.
    apply in_image_iff in H_k0_lhs_eq_k0_rhs.
    destruct H_k0_lhs_eq_k0_rhs as [[lhs rhs] [H_eq H_lhs_eq_rhs]].
    assert (H_lhs_is := eq_congruence fst _ _ H_eq).
    assert (H_rhs_is := eq_congruence snd _ _ H_eq).
    simpl in H_lhs_is, H_rhs_is.
    subst k0_lhs k0_rhs.
    apply PaCo_unfold in H_lhs_eq_rhs...
    unfold eqITree in H_lhs_eq_rhs.
    assert (claim5 : isSubsetOf (or_plus (PaCo eqITreeF bot) bot) (or_plus (PaCo eqITreeF REL) REL)).
    { intros x H_x_in.
      apply in_union_iff in H_x_in.
      apply in_union_iff.
      destruct H_x_in as [H_x_in | H_x_in].
      - left.
        apply (PaCo_preserves_monotonicity eqITreeF eqITreeF_isMonotonic bot)...
      - contradiction (bot_is_empty x H_x_in).
    }
    unfold eqITree.
    unfold eqITreeF, member, curry, uncurry in *.
    replace (ConstructiveCoLaTheory.or_plus) with (or_plus (E := E) (R := R1)) in H_lhs_eq_rhs...
    rewrite (claim1 lhs).
    rewrite (claim1 rhs).
    destruct H_lhs_eq_rhs as [r1 r2 H_rel | t1 t2 H_rel | X e k1 k2 H_rel].
    - simpl.
      assert (claim3 : member (k0 r1, k0 r2) rel_id) by congruence.
      assert (claim4 := @eqITree_refl E R2 (k0 r1, k0 r2) claim3).
      apply PaCo_unfold in claim4...
      replace (ConstructiveCoLaTheory.or_plus) with (or_plus (E := E) (R := R2)) in claim4...
      apply (eqITreeF_isMonotonic (or_plus (PaCo eqITreeF bot) bot) _ claim5 (k0 r1, k0 r2) claim4).
    - simpl.
      constructor 2.
      apply in_union_iff; right.
      apply in_union_iff in H_rel.
      destruct H_rel as [H_rel | H_rel]; [ | contradiction (not_in_bot t1 t2 H_rel)].
      right...
    - simpl.
      constructor 3.
      intros x.
      apply in_union_iff; right.
      assert (claim2 := H_rel x).
      apply in_union_iff in claim2.
      destruct claim2 as [claim2 | claim2]; [ | contradiction (not_in_bot (k1 x) (k2 x) claim2)].
      right...
  Qed.

  Global Add Parametric Morphism {E : Type -> Type} {R1 : Type} {R2 : Type} :
    bind with signature (eqITree (E := E) (R := R1) ==> eq ==> eqITree (E := E) (R := R2))
  as itree_bind_preserves_eq_on_fst_arg.
  Proof with eauto with *.
    intros lhs rhs H_lhs_eq_rhs k.
    apply PaCo_init.
    apply PaCo_init in H_lhs_eq_rhs.
    apply (expand_leaves_preserves_snd_arg k (lhs >>= k, rhs >>= k)).
    unfold rel_image.
    apply in_image_iff.
    exists (lhs, rhs)...
  Qed.

  Section REWRITE_BIND.

  Context {E : Type -> Type}.

  Let _bind {R1 : Type} {R2 : Type} : itree E R1 -> (R1 -> itree E R2) -> itree E R2 :=
    fun t0 : itree E R1 =>
    fun k0 : R1 -> itree E R2 =>
    match observe t0 with
    | RetF r => k0 r
    | TauF t => Tau (t >>= k0)
    | VisF X e k => Vis X e (fun x : X => k x >>= k0)
    end
  .

  Section BIND_CASES.

  Polymorphic Context {R1 : Type} {R2 : Type}.

  Polymorphic Variable k0 : R1 -> itree E R2.

  Polymorphic Lemma unfold_itree_bind (t0 : itree E R1) :
    (t0 >>= k0) == _bind t0 k0.
  Proof.
    apply eqITree_intro_obs_eq_obs.
    reflexivity.
  Qed.

  Polymorphic Lemma itree_bind_Ret (r : R1) :
    bind (Ret r) k0 == k0 r.
  Proof.
    apply eqITree_intro_obs_eq_obs.
    reflexivity.
  Qed.

  Polymorphic Lemma itree_bind_Tau (t : itree E R1) :
    bind (Tau t) k0 == Tau (bind t k0).
  Proof.
    apply unfold_itree_bind with (t0 := Tau t).
  Qed.

  Polymorphic Lemma itree_bind_Vis (X : Type) (e : E X) (k : X -> itree E R1) :
    bind (Vis X e k) k0 == Vis X e (fun x : X => bind (k x) k0).
  Proof.
    rewrite unfold_itree_bind with (t0 := Vis X e k).
    apply PaCo_init.
    apply PaCo_fold.
    constructor 3.
    intros x.
    apply in_union_iff; left.
    apply eqITree_refl.
    reflexivity.
  Qed.

  Polymorphic Lemma itree_bind_trigger (e : E R1) :
    bind (itree_trigger R1 e) k0 == Vis R1 e k0.
  Proof.
    rewrite unfold_itree_bind with (t0 := itree_trigger R1 e).
    apply PaCo_init.
    apply PaCo_fold.
    constructor 3.
    intros r.
    apply in_union_iff; left.
    assert (claim1 := itree_bind_Ret r).
    apply PaCo_init in claim1.
    exact claim1.
  Qed.

  End BIND_CASES.

  Lemma unfold_expand_leaves {R1 : Type} {R2 : Type} :
    forall k : R1 -> itree E R2,
    forall t : itree E R1,
    observe (expand_leaves k t) = observe (expand_leaves_progress k (expand_leaves k) (observe t)).
  Proof.
    reflexivity.
  Qed.

  Lemma itree_bind_assoc {R1 : Type} {R2 : Type} {R3 : Type} :
    forall m : itree E R1,
    forall k1 : R1 -> itree E R2,
    forall k2 : R2 -> itree E R3,
    ((m >>= k1) >>= k2) == (m >>= (fun x1 : R1 => k1 x1 >>= k2)).
  Proof with eauto with *.
    intros t_0 k_1 k_2.
    revert t_0.
    set (focus_rel := image (fun two_trees : itree E R1 * itree E R1 => ((fst two_trees >>= k_1) >>= k_2, snd two_trees >>= (fun x : R1 => k_1 x >>= k_2)))).
    enough (it_is_sufficient_to_show : isSubsetOf (focus_rel (PaCo eqITreeF bot)) (PaCo eqITreeF bot)).
    { intros t0.
      apply PaCo_init.
      assert (claim1 : t0 == t0) by reflexivity.
      apply PaCo_init in claim1.
      apply it_is_sufficient_to_show.
      apply in_image_iff.
      exists (t0, t0)...
    }
    apply PaCo_acc...
    assert (claim1 : forall A : Type, forall x : ensemble A, bot =< x)...
    set (REL := MyUnion bot (focus_rel (PaCo eqITreeF bot))).
    assert (claim2 : or_plus (PaCo eqITreeF bot) bot =< or_plus (PaCo eqITreeF REL) REL).
    { intros x H_x_in.
      apply in_union_iff in H_x_in.
      destruct H_x_in as [H_x_in | H_x_in].
      - apply in_union_iff; left.
        apply (PaCo_preserves_monotonicity eqITreeF eqITreeF_isMonotonic bot REL)...
      - contradiction (bot_is_empty x).
    }
    transitivity (eqITreeF (or_plus (PaCo eqITreeF REL) REL)); [ | apply PaCo_fold].
    intros [f_lhs f_rhs] H_f_lhs_eq_f_rhs.
    apply in_image_iff in H_f_lhs_eq_f_rhs.
    destruct H_f_lhs_eq_f_rhs as [[lhs rhs] [H_eq H_in]].
    assert (f_lhs_is := eq_congruence fst _ _ H_eq).
    assert (f_rhs_is := eq_congruence snd _ _ H_eq).
    simpl in f_lhs_is, f_rhs_is.
    subst f_lhs f_rhs.
    apply PaCo_unfold in H_in...
    replace (ConstructiveCoLaTheory.or_plus) with (or_plus (E := E) (R := R1)) in H_in...
    unfold eqITree in H_in.
    unfold eqITreeF, member, uncurry, curry in *.
    do 3 rewrite unfold_expand_leaves.
    destruct H_in as [r1 r2 H_rel | t1 t2 H_rel | X e k1 k2 H_rel].
    - simpl.
      rewrite <- unfold_expand_leaves.
      subst r2.
      assert (claim3 := eqITree_refl (expand_leaves k_2 (k_1 r1), expand_leaves k_2 (k_1 r1)) eq_refl).
      apply PaCo_unfold in claim3...
      replace (ConstructiveCoLaTheory.or_plus) with (or_plus (E := E) (R := R3)) in claim3...
      apply (eqITreeF_isMonotonic _ _ claim2 _ claim3).
    - simpl.
      constructor 2.
      apply in_union_iff; right.
      apply in_union_iff in H_rel.
      destruct H_rel as [H_rel | H_rel]; [ | contradiction (bot_is_empty (t1, t2))].
      replace (expand_leaves k_2 (expand_leaves k_1 t1)) with ((t1 >>= k_1) >>= k_2)...
      replace (expand_leaves (fun x : R1 => expand_leaves k_2 (k_1 x)) t2) with (t2 >>= (fun x : R1 => k_1 x >>= k_2))...
      right.
      apply in_image_iff.
      exists (t1, t2)...
    - simpl.
      constructor 3.
      intros x0.
      assert (claim4 := H_rel x0).
      apply in_union_iff in claim4.
      destruct claim4 as [claim4 | claim4]; [ | contradiction (bot_is_empty (k1 x0, k2 x0))].
      apply in_union_iff; right.
      right.
      apply in_image_iff.
      exists (k1 x0, k2 x0)...
  Qed.

  Lemma itree_bind_pure_l {R1 : Type} {R2 : Type} :
    forall k : R1 -> itree E R2,
    forall x : R1,
    bind (pure x) k == k x.
  Proof.
    intros k x.
    exact (itree_bind_Ret k x).
  Qed.

  Lemma itree_bind_pure_r {R1 : Type} :
    forall m : itree E R1,
    bind m pure == m.
  Proof with eauto with *.
    set (focus := fun two_trees : itree E R1 * itree E R1 => ((fst two_trees >>= pure), snd two_trees)).
    set (focus_rel := image focus).
    enough (it_is_sufficient_to_show : isSubsetOf (focus_rel (PaCo eqITreeF bot)) (PaCo eqITreeF bot)).
    { intros t0.
      apply PaCo_init.
      assert (claim1 : t0 == t0) by reflexivity.
      apply PaCo_init in claim1.
      apply it_is_sufficient_to_show.
      apply in_image_iff.
      exists (t0, t0)...
    }
    apply PaCo_acc...
    assert (claim1 : forall A : Type, forall x : ensemble A, bot =< x)...
    set (REL := MyUnion bot (focus_rel (PaCo eqITreeF bot))).
    assert (claim2 : or_plus (PaCo eqITreeF bot) bot =< or_plus (PaCo eqITreeF REL) REL).
    { intros x H_x_in.
      apply in_union_iff in H_x_in.
      destruct H_x_in as [H_x_in | H_x_in].
      - apply in_union_iff; left.
        apply (PaCo_preserves_monotonicity eqITreeF eqITreeF_isMonotonic bot REL)...
      - contradiction (bot_is_empty x).
    }
    transitivity (eqITreeF (or_plus (PaCo eqITreeF REL) REL)); [ | apply PaCo_fold].
    intros [f_lhs f_rhs] H_f_lhs_eq_f_rhs.
    apply in_image_iff in H_f_lhs_eq_f_rhs.
    destruct H_f_lhs_eq_f_rhs as [[lhs rhs] [H_eq H_in]].
    assert (f_lhs_is := eq_congruence fst _ _ H_eq).
    assert (f_rhs_is := eq_congruence snd _ _ H_eq).
    simpl in f_lhs_is, f_rhs_is.
    subst f_lhs f_rhs.
    apply PaCo_unfold in H_in...
    replace (ConstructiveCoLaTheory.or_plus) with (or_plus (E := E) (R := R1)) in H_in...
    unfold eqITree in H_in.
    unfold eqITreeF, member, uncurry, curry in *.
    rewrite unfold_expand_leaves.
    destruct H_in as [r1 r2 H_rel | t1 t2 H_rel | X e k1 k2 H_rel].
    - constructor 1...
    - constructor 2.
      apply in_union_iff; right.
      right.
      apply in_union_iff in H_rel.
      destruct H_rel as [H_rel | H_rel]; [ | contradiction (bot_is_empty (t1, t2))].
      apply in_image_iff.
      exists (t1, t2)...
    - constructor 3.
      intros x0.
      assert (claim4 := H_rel x0).
      apply in_union_iff in claim4.
      destruct claim4 as [claim4 | claim4]; [ | contradiction (bot_is_empty (k1 x0, k2 x0))].
      apply in_union_iff; right.
      right.
      apply in_image_iff.
      exists (k1 x0, k2 x0)...
  Qed.

  End REWRITE_BIND.

  Global Add Parametric Morphism {E : Type -> Type} {R1 : Type} {R2 : Type} :
    bind with signature (eq ==> @arrow_eqProp (R1) (itree E R2) (itree_E_R_isSetoid (E := E) (R := R2)) ==> eqITree (E := E) (R := R2))
  as itree_bind_preserves_eq_on_snd_arg.
  Proof with eauto with *.
    intros t_0 k_1 k_2 H_k_1_eq_k_2.
    unfold arrow_eqProp in H_k_1_eq_k_2.
    revert t_0.
    set (focus := fun two_trees : itree E R1 * itree E R1 => (bind (fst two_trees) k_1, bind (snd two_trees) k_2)).
    set (focus_rel := image focus).
    enough (it_is_sufficient_to_show : isSubsetOf (focus_rel (PaCo eqITreeF bot)) (PaCo eqITreeF bot)).
    { intros t0.
      apply PaCo_init.
      assert (claim1 : t0 == t0) by reflexivity.
      apply PaCo_init in claim1.
      apply it_is_sufficient_to_show.
      apply in_image_iff.
      exists (t0, t0)...
    }
    apply PaCo_acc...
    assert (claim1 : forall A : Type, forall x : ensemble A, bot =< x)...
    set (REL := MyUnion bot (focus_rel (PaCo eqITreeF bot))).
    assert (claim2 : or_plus (PaCo eqITreeF bot) bot =< or_plus (PaCo eqITreeF REL) REL).
    { intros x H_x_in.
      apply in_union_iff in H_x_in.
      destruct H_x_in as [H_x_in | H_x_in].
      - apply in_union_iff; left.
        apply (PaCo_preserves_monotonicity eqITreeF eqITreeF_isMonotonic bot REL)...
      - contradiction (bot_is_empty x).
    }
    replace ((fun a : itree E R2 * itree E R2 => member a bot \/ member a (focus_rel (PaCo eqITreeF bot)))) with REL...
    intros [f_lhs f_rhs] H_f_lhs_eq_f_rhs.
    apply PaCo_fold.
    apply in_image_iff in H_f_lhs_eq_f_rhs.
    destruct H_f_lhs_eq_f_rhs as [[lhs rhs] [H_eq H_in]].
    assert (f_lhs_is := eq_congruence fst _ _ H_eq).
    assert (f_rhs_is := eq_congruence snd _ _ H_eq).
    simpl in f_lhs_is, f_rhs_is.
    subst f_lhs f_rhs.
    apply PaCo_unfold in H_in...
    replace (ConstructiveCoLaTheory.or_plus) with (or_plus (E := E) (R := R1)) in H_in...
    replace (ConstructiveCoLaTheory.or_plus) with (or_plus (E := E) (R := R2))...
    unfold eqITree.
    unfold eqITreeF, member, uncurry, curry in *.
    do 2 rewrite unfold_expand_leaves.
    destruct H_in as [r1 r2 H_rel | t1 t2 H_rel | X e k1 k2 H_rel]; simpl.
    - subst r2.
      rename r1 into r.
      assert (claim3 := H_k_1_eq_k_2 r).
      apply PaCo_init in claim3.
      apply PaCo_unfold in claim3...
      replace (ConstructiveCoLaTheory.or_plus) with (or_plus (E := E) (R := R2)) in claim3...
      apply (eqITreeF_isMonotonic _ _ claim2 _ claim3).
    - simpl.
      constructor 2.
      apply in_union_iff; right.
      apply in_union_iff in H_rel.
      destruct H_rel as [H_rel | H_rel]; [ | contradiction (bot_is_empty (t1, t2))].
      replace (expand_leaves k_2 t2) with (bind t2 k_2)...
      replace (expand_leaves k_1 t1) with (bind t1 k_1)...
      right.
      apply in_image_iff.
      exists (t1, t2)...
    - simpl.
      constructor 3.
      intros x0.
      assert (claim4 := H_rel x0).
      apply in_union_iff in claim4.
      destruct claim4 as [claim4 | claim4]; [ | contradiction (bot_is_empty (k1 x0, k2 x0))].
      apply in_union_iff; right.
      right.
      apply in_image_iff.
      exists (k1 x0, k2 x0)...
  Qed.

  Global Instance itree_E_isSetoid1 {E : Type -> Type} : isSetoid1 (itree E) :=
    { eqProp1 {R : Type} := itree_E_R_isSetoid (E := E) (R := R)
    }
  .

  Global Instance itree_E_obeysMonadLaws (E : Type -> Type) : obeysMonadLaws (itree_E_isMonad E) :=
    { bind_assoc {R1 : Type} {R2 : Type} {R3 : Type} := itree_bind_assoc (E := E) (R1 := R1) (R2 := R2) (R3 := R3)
    ; bind_pure_l {R1 : Type} {R2 : Type} := itree_bind_pure_l (E := E) (R1 := R1) (R2 := R2)
    ; bind_pure_r {R1 : Type} := itree_bind_pure_r (E := E) (R1 := R1)
    ; bind_preserves_eq_on_fst {R1 : Type} {R2 : Type} :=
      fun m1 : itree E R1 =>
      fun m2 : itree E R1 =>
      fun H_m1_eq_m2 : m1 == m2 =>
      fun k : R1 -> itree E R2 =>
      @itree_bind_preserves_eq_on_fst_arg E R1 R2 m1 m2 H_m1_eq_m2 k k eq_refl
    ; bind_preserves_eq_on_snd {R1 : Type} {R2 : Type} :=
      fun k1 : R1 -> itree E R2 =>
      fun k2 : R1 -> itree E R2 =>
      fun H_k1_eq_k2 : forall x : R1, k1 x == k2 x =>
      fun m : itree E R1 => 
      @itree_bind_preserves_eq_on_snd_arg E R1 R2 m m eq_refl k1 k2 H_k1_eq_k2
    }
  .

  Local Notation Handler E F := (forall X : Type, E X -> itree F X).

End InteractionTreeTheory.
