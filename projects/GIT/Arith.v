Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import DschingisKhan.pure.DomainTheory.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.
Require Import DschingisKhan.classical.ExclusiveMiddle.

Module MyCategories.

  Import MyUtilities.

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

  Global Open Scope monad_scope.

  Polymorphic Class isFunctor (F : Type -> Type) : Type :=
    { fmap {A : Type} {B : Type} : (A -> B) -> F A -> F B
    }
  .

  Global Polymorphic Instance Monad_isFunctor {M : Type -> Type} `(M_isMonad : isMonad M) : isFunctor M :=
    { fmap {A : Type} {B : Type} :=
      fun f : A -> B =>
      fun m : M A =>
      \do x <- m;
      ret (f x);
    }
  .

  Polymorphic Definition fcat {A : Type} {B : Type} {C : Type} (f1 : B -> C) (f2 : A -> B) : (A -> C) :=
    fun x : A =>
    f1 (f2 x)
  .

  Polymorphic Definition kcat {A : Type} {B : Type} {C : Type} {M : Type -> Type} `{M_isMonad : isMonad M} (k1 : B -> M C) (k2 : A -> M B) : (A -> M C) :=
    fun x : A =>
    k2 x >>= k1
  .

  Global Infix " `fcat` " := fcat (at level 25, right associativity) : function_scope.
  Global Infix " `kcat` " := kcat (at level 25, right associativity) : function_scope.

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

  Polymorphic Definition StateT {ST : Type} {M : Type -> Type} {X : Type} : (ST -> M (prod X ST)) -> stateT ST M X :=
    @id (stateT ST M X)
  .

  Polymorphic Definition runStateT {ST : Type} {M : Type -> Type} {X : Type} : stateT ST M X -> (ST -> M (prod X ST)) :=
    @id (stateT ST M X)
  .

  Global Polymorphic Instance stateT_ST_M_isMonad (ST : Type) (M : Type -> Type) `(M_isMonad : isMonad M) : isMonad (stateT ST M) :=
    { pure _ := StateT `fcat` curry pure
    ; bind _ _ := fun m k => StateT (uncurry (runStateT `fcat` k) `kcat` runStateT m)
    }
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
      fun f : A -> B =>
      sum1_rect F1 F2 A (fun _ => sum1 F1 F2 B) (fun l : F1 A => inl1 (fmap f l)) (fun r : F2 A => inr1 (fmap f r))
    }
  .

  Global Notation " F1 '-<' F2 " := (forall X : Type, F1 X -> F2 X) (at level 100, no associativity) : type_scope.

  Polymorphic Definition lift_stateT {ST : Type} {E : Type -> Type} `{E_isFunctor : isFunctor E} : E -< stateT ST E :=
    fun X : Type =>
    fun e : E X =>
    StateT (fun s : ST => fmap (fun x : X => (x, s)) e)
  .

End MyCategories.

Module InteractionTreeDefns. (* Reference: "https://sf.snu.ac.kr/publications/itrees.pdf" *)

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
    let iter := curry `fcat` itree_iter (E := E') (R := R * ST) (I := itree E R * ST) `fcat` uncurry in
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

End InteractionTreeDefns.

Module InteractionTreesTheory.

  Import EqFacts BasicSetoidTheory MyEnsemble BasicPosetTheory ConstructiveCoLaTheory PowerSetCoLa MyCategories InteractionTreeDefns.

  Section ITREE_EQUALITY. (* Reference: "https://github.com/snu-sf/InteractionTrees/blob/72d78f8b08a86c4609a27c4f8bce1ae876fbc22e/theories/Eq/Eq.v" *)

  Context {E : Type -> Type} {R : Type}.

  Definition VisF_eq_elim (X1 : Type) (X2 : Type) (e1 : E X1) (e2 : E X2) (k1 : X1 -> itree E R) (k2 : X2 -> itree E R) : @eq (itreeF (itree E R) E R) (VisF X1 e1 k1) (VisF X2 e2 k2) -> X1 = X2 :=
    let pop_X_in_VisF (ot : itreeF (itree E R) E R) : Type :=
      match ot return Type with
      | RetF r => X1
      | TauF t => X1
      | VisF X e k => X
      end
    in
    eq_congruence pop_X_in_VisF (VisF X1 e1 k1) (VisF X2 e2 k2)
  .

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
    fun two_trees : itree E R * itree E R => member (snd two_trees, fst two_trees) REL1
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

  Definition comp (REL1 : ensemble (itree E R * itree E R)) (REL2 : ensemble (itree E R * itree E R)) : ensemble (itree E R * itree E R) :=
    fun two_trees : itree E R * itree E R =>
    exists t : itree E R, member (fst two_trees, t) REL1 /\ member (t, snd two_trees) REL2
  .

  Lemma eqITree_trans :
    isSubsetOf (comp (PaCo eqITreeF bot) (PaCo eqITreeF bot)) (PaCo eqITreeF bot).
  Proof with eauto with *.
    apply PaCo_acc...
    set (REL := MyUnion bot (comp (PaCo eqITreeF bot) (PaCo eqITreeF bot))).
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
    unfold comp, member in H_lhs_eq_rhs.
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
      assert (X1_eq_X2 := VisF_eq_elim X2 X1 e2 e1 k2' k1' H_t_obs).
      subst X2.
      rename X1 into X.
      enough (H_e_eq_e : e1 = e2).
      enough (H_k_eq_k : k1' = k2').
      { subst e2.
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
      }
      all: inversion H_t_obs; symmetry.
      apply (ExclusiveMiddle.existT_inj2_eq Type (fun X : Type => X -> itree E R) X k2' k1')...
      apply (ExclusiveMiddle.existT_inj2_eq Type (fun X : Type => E X) X e2 e1)...
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

  Add Parametric Relation {E : Type -> Type} {R : Type} : (itree E R) (eqITree (E := E) (R := R))
    reflexivity proved by (eqITree_Reflexive (E := E) (R := R))
    symmetry proved by (eqITree_Symmetric (E := E) (R := R))
    transitivity proved by (eqITree_Transitive (E := E) (R := R))
  as eqITree_Equivalence.

  Global Instance itree_isSetoid {E : Type -> Type} {R : Type} : isSetoid (itree E R) :=
    { eqProp := eqITree (E := E) (R := R)
    ; Setoid_requiresEquivalence := eqITree_Equivalence (E := E) (R := R)
    }
  .

  Section INTERPRET_FACTS. (* Reference: "https://github.com/snu-sf/InteractionTrees/blob/CompCertM/theories/Interp/InterpFacts.v" *)

  End INTERPRET_FACTS.

End InteractionTreesTheory.
