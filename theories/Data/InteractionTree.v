Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.

Module InteractionTrees.

  Global Notation " E -< F " := (forall X : Type, E X -> F X) (at level 100, no associativity) : type_scope.

  Variant itreeF {itree_E_R : Type} (E : Type -> Type) (R : Type) : Type :=
  | RetF (r : R) : itreeF E R
  | TauF (t : itree_E_R) : itreeF E R
  | VisF (X : Type) (e : E X) (k : X -> itree_E_R) : itreeF E R
  .

  Set Primitive Projections.

  CoInductive itree (E : Type -> Type) (R : Type) : Type :=
    go { observe : itreeF (itree_E_R := itree E R) E R }
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

  Section ITREE_MONAD. (* Reference: "https://github.com/DeepSpec/InteractionTrees/blob/5fe86a6bb72f85b5fcb125da10012d795226cf3a/theories/Core/ITreeMonad.v" *)

  Context {E : Type -> Type}.

  Definition itree_pure {R : Type} (r : R) : itree E R := Ret r.

  Context {R1 : Type} {R2 : Type}.

  Definition itree_bindGuard (k0 : R1 -> itree E R2) (ot0 : itreeF E R1) (CIH : itree E R1 -> itree E R2) : itree E R2 :=
    match ot0 with
    | RetF r => k0 r
    | TauF t => Tau (CIH t)
    | VisF X e k => Vis X e (fun x : X => CIH (k x))
    end
  .

  Definition itree_bindAux (k : R1 -> itree E R2) : itree E R1 -> itree E R2 :=
    cofix itree_bindAux_cofix (t : itree E R1) : itree E R2 :=
    itree_bindGuard k (observe t) itree_bindAux_cofix
  .

  Definition itree_bind (m : itree E R1) (k : R1 -> itree E R2) : itree E R2 := itree_bindAux k m.

  Lemma observe_itree_bind (t0 : itree E R1) (k0 : R1 -> itree E R2)
    : observe (itree_bind t0 k0) = observe (itree_bindGuard k0 (observe t0) (fun t : itree E R1 => itree_bind t k0)).
  Proof. exact (eq_refl). Defined.

  End ITREE_MONAD.

  Global Instance itree_E_isMonad (E : Type -> Type) : isMonad (itree E) :=
    { pure {R : Type} := itree_pure (E := E) (R := R)
    ; bind {R1 : Type} {R2 : Type} := itree_bind (E := E) (R1 := R1) (R2 := R2)
    }
  .

  Definition itree_tick {E : Type -> Type} : itree E unit := Tau (Ret tt).

  Definition itree_trigger {E : Type -> Type} : E -< itree E := fun R : Type => fun e : E R => Vis R e (fun x : R => Ret x).

  Definition itree_iter {E : Type -> Type} {I : Type} {R : Type} (step : I -> itree E (I + R)%type) : I -> itree E R :=
    cofix itree_iter_cofix (i : I) : itree E R :=
    itree_bindAux (sum_rect (fun _ : I + R => itree E R) (fun l : I => Tau (itree_iter_cofix l)) (fun r : R => Ret r)) (step i)
  .

  Global Polymorphic Instance itree_E_isMonadIter (E : Type -> Type) : isMonadIter (itree E) :=
    { iterMonad {I : Type} {R : Type} := itree_iter (E := E) (I := I) (R := R)
    }
  .

  Definition itree_interpret {E : Type -> Type} {M : Type -> Type} {M_isMonad : isMonad M} {M_isMonadIter : isMonadIter M} (handle : E =====> M) : itree E =====> M :=
    fun R : Type =>
    iterMonad (M := M) (I := itree E R) (R := R) (
      fun t0 : itree E R =>
      match observe t0 with
      | RetF r => pure (inr r)
      | TauF t => pure (inl t)
      | VisF X e k => bind (handle X e) (fun x : X => pure (inl (k x)))
      end
    )
  .

  Definition itree_interpret_stateT {E : Type -> Type} {E' : Type -> Type} {ST : Type} (handle : E =====> stateT ST (itree E')) : itree E =====> stateT ST (itree E') :=
    itree_interpret (E := E) (M := stateT ST (itree E')) (M_isMonadIter := stateT_ST_isMonadIter ST (itree E')) handle
  .

  Inductive callE (I : Type) (R : Type) : Type -> Type :=
  | Call (arg : I) : callE I R R
  .

  Global Arguments Call {I} {R}.

  Section RECURSION. (* Reference: "https://github.com/DeepSpec/InteractionTrees/blob/5fe86a6bb72f85b5fcb125da10012d795226cf3a/theories/Interp/Recursion.v" *)

  Definition itree_interpret_mrec {E1 : Type -> Type} {E2 : Type -> Type} (ctx : E1 =====> itree (E1 +' E2)) : itree (E1 +' E2) =====> itree E2 :=
    fun R : Type =>
    itree_iter (E := E2) (I := itree (E1 +' E2) R) (R := R) (
      fun t0 : itree (E1 +' E2) R =>
      match observe t0 with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl t)
      | VisF X e k =>
        match e with
        | inl1 e1 => Ret (inl (bind (ctx X e1) k))
        | inr1 e2 => Vis X e2 (fun x : X => pure (inl (k x)))
        end
      end
    )
  .

  Definition itree_mrec {E : Type -> Type} {E' : Type -> Type} (ctx : E =====> itree (E +' E')) : E =====> itree E' :=
    fun R : Type =>
    fun e : E R =>
    itree_interpret_mrec (E1 := E) (E2 := E') ctx R (ctx R e)
  .

  Definition itree_trigger_inl1 {E : Type -> Type} {E' : Type -> Type} : E -< itree (E +' E') :=
    fun R : Type =>
    fun e : E R =>
    itree_trigger (E := E +' E') R (inl1 e)
  .

  Local Notation endo X := (X -> X).

  Definition itree_mrec_fix {E : Type -> Type} {E' : Type -> Type} (ctx : endo (E -< itree (E +' E'))) : E -< itree E' :=
    itree_mrec (E := E) (E' := E') (ctx itree_trigger_inl1)
  .

  Definition itree_app {E : Type -> Type} {I : Type} {R : Type} (callee : I -> itree E R) : callE I R =====> itree E :=
    fun X : Type =>
    fun e : callE I R X =>
    match e in callE _ _ x return itree E x with
    | Call arg => callee arg
    end
  .

  Definition itree_rec {E : Type -> Type} {I : Type} {R : Type} (body : I -> itree (callE I R +' E) R) (arg : I) : itree E R :=
    itree_mrec (E := callE I R) (E' := E) (itree_app body) R (Call arg)
  .

  Definition itree_call {E : Type -> Type} {I : Type} {R : Type} (arg : I) : itree (callE I R +' E) R :=
    itree_trigger_inl1 (E := callE I R) (E' := E) R (Call arg)
  .

  Definition itree_rec_fix {E : Type -> Type} {I : Type} {R : Type} (body : endo (I -> itree (callE I R +' E) R)) : I -> itree E R :=
    itree_rec (E := E) (I := I) (R := R) (body itree_call)
  .

  End RECURSION.

End InteractionTrees.
