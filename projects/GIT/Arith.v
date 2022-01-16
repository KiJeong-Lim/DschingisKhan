Require Import Coq.Lists.List.
Require Import DschingisKhan.pure.DomainTheory.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module MyCategories.

  Import MyUtilities.

  Global Declare Scope monad_scope.

  Class isFunctor (F : Type -> Type) : Type :=
    { fmap {A : Type} {B : Type} : (A -> B) -> F A -> F B
    }
  .

  Class isMonad (M : Type -> Type) : Type :=
    { pure {A : Type} : A -> M A
    ; bind {A : Type} {B : Type} : M A -> (A -> M B) -> M B
    }
  .

  Global Notation " m '>>=' k " := (bind m k) (at level 90, left associativity).

  Definition fcat {A : Type} {B : Type} {C : Type} : (B -> C) -> (A -> B) -> (A -> C) :=
    fun f1 : B -> C =>
    fun f2 : A -> B =>
    fun x : A =>
    f1 (f2 x)
  .

  Definition kcat {A : Type} {B : Type} {C : Type} {M : Type -> Type} `{M_isMonad : isMonad M} : (B -> M C) -> (A -> M B) -> (A -> M C) :=
    fun k1 : B -> M C =>
    fun k2 : A -> M B =>
    fun x : A =>
    k2 x >>= k1
  .

  Global Infix " `fcat` " := fcat (at level 45, right associativity).

  Global Infix " `kcat` " := kcat (at level 45, right associativity).

  Global Notation " '\do' x '<-' m1 ';' m2 " := (bind m1 (fun x => m2)) (at level 90, left associativity) : monad_scope.

  Global Notation " '\do' m1 ';' m2 " := (bind m1 (fun _ => m2)) (at level 90, left associativity) : monad_scope.

  Global Notation " 'ret' x ';' " := (pure x) (at level 0, x at level 0, no associativity) : monad_scope.

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

  Definition stateT (ST : Type) (M : Type -> Type) (X : Type) : Type :=
    ST -> M (prod X ST)
  .

  Definition StateT {ST : Type} {M : Type -> Type} {X : Type} : (ST -> M (prod X ST)) -> stateT ST M X :=
    id
  .

  Definition runStateT {ST : Type} {M : Type -> Type} {X : Type} : stateT ST M X -> (ST -> M (prod X ST)) :=
    id
  .

  Global Instance stateT_ST_M_isMonad (ST : Type) (M : Type -> Type) `(M_isMonad : isMonad M) : isMonad (stateT ST M) :=
    { pure _ := StateT `fcat` curry pure
    ; bind _ _ := fun m k => StateT (uncurry (runStateT `fcat` k) `kcat` runStateT m)
    }
  .

  Inductive sum1 (F1 : Type -> Type) (F2 : Type -> Type) (X : Type) : Type :=
  | inl1 : F1 X -> sum1 F1 F2 X
  | inr1 : F2 X -> sum1 F1 F2 X
  .

  Global Arguments inl1 {F1} {F2} {X}.
  Global Arguments inr1 {F1} {F2} {X}.

  Global Notation " F1 '+1' F2 " := (sum1 F1 F2) (at level 60, no associativity) : type_scope.

  Global Instance sum1_F1_F2_isFunctor (F1 : Type -> Type) (F2 : Type -> Type) `{F1_isFunctor : isFunctor F1} `{F2_isFunctor : isFunctor F2} : isFunctor (sum1 F1 F2) :=
    { fmap {A : Type} {B : Type} :=
      fun f : A -> B =>
      sum1_rect F1 F2 A (fun _ => sum1 F1 F2 B) (fun H_l : F1 A => inl1 (fmap f H_l)) (fun H_r : F2 A => inr1 (fmap f H_r))
    }
  .

  Global Notation " F1 '-<' F2 " := (forall X : Type, F1 X -> F2 X) (at level 100, no associativity) : type_scope.

  Local Open Scope monad_scope.

  Definition lift_stateT {M : Type -> Type} `{M_isMonad : isMonad M} [ST : Type] : M -< stateT ST M :=
    fun X : Type =>
    fun m : M X =>
    StateT (fun s : ST =>
      \do x <- m;
      ret (x, s);
    )
  .

End MyCategories.

Module InteractionTrees. (* Reference: "https://sf.snu.ac.kr/publications/itrees.pdf" *)

  Import ListNotations MyCategories ConstructiveCoLaTheory.

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

  Local Open Scope monad_scope.

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

  Definition expand_leaves_aux (CIH : itree E R1 -> itree E R2) (ot : itreeF (itree E R1) E R1) : itree E R2 :=
    match ot with
    | RetF r => from_leaf r
    | TauF t => Tau (CIH t)
    | VisF X e k => Vis X e (fun x : X => CIH (k x))
    end
  .

  CoFixpoint expand_leaves (t : itree E R1) : itree E R2 :=
    expand_leaves_aux expand_leaves (observe t)
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

  Definition itree_iter {E : Type -> Type} {R : Type} {I : Type} (step : I -> itree E (I + R)) : I -> itree E R :=
    cofix itree_iter_cofix (i : I) : itree E R :=
    expand_leaves (@sum_rect I R (fun _ => itree E R) (fun l : I => Tau (itree_iter_cofix l)) (fun r : R => Ret r)) (step i)
  .

  Definition itree_iter_stateT {E : Type -> Type} {E' : Type -> Type} {ST : Type} {R : Type} : (itree E R -> ST -> itree E' (itree E R * ST + R * ST)) -> (itree E R -> stateT ST (itree E') R) :=
    curry `fcat` itree_iter (E := E') (R := R * ST) (I := itree E R * ST) `fcat` uncurry
  .

  Definition itree_interpret_stateT {E : Type -> Type} {E' : Type -> Type} {ST : Type} (handle : E -< stateT ST (itree E')) : itree E -< stateT ST (itree E') :=
    fun R : Type =>
    itree_iter_stateT (fun t0 : itree E R => fun s : ST =>
      match observe t0 with
      | RetF r => ret (inr (r, s));
      | TauF t => ret (inl (t, s));
      | VisF X e k => \do h_res <- handle X e s; ret (inl (k (fst h_res), snd h_res));
      end
    )
  .

  Definition itree_trigger {E : Type -> Type} : E -< itree E :=
    fun R : Type =>
    fun e : E R =>
    Vis R e (fun x : R => Ret x)
  .

  Inductive callE (A : Type) (B : Type) : Type -> Type :=
  | Call (arg : A) : callE A B B
  .

  Global Arguments Call {A} {B}.

  Section RECURSION. (* Reference: "https://github.com/DeepSpec/InteractionTrees/blob/5fe86a6bb72f85b5fcb125da10012d795226cf3a/theories/Interp/Recursion.v" *)

  Definition itree_interpret_mrec {E : Type -> Type} {E' : Type -> Type} (ctx : E -< itree (E +1 E')) : itree (E +1 E') -< itree E' :=
    fun R : Type =>
    itree_iter (E := E') (R := R) (I := itree (E +1 E') R) (fun t0 : itree (E +1 E') R =>
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

  Definition itree_mrec {E : Type -> Type} {E' : Type -> Type} (ctx : E -< itree (E +1 E')) : E -< itree E' :=
    fun R : Type =>
    fun e : E R =>
    itree_interpret_mrec ctx R (ctx R e)
  .

  Definition itree_trigger_inl1 {E : Type -> Type} {E' : Type -> Type} : E -< itree (E +1 E') :=
    fun R : Type =>
    fun e : E R =>
    itree_trigger (E := E +1 E') R (inl1 e)
  .

  Local Notation endo T := (T -> T).

  Definition itree_mrec_fix {E : Type -> Type} {E' : Type -> Type} (ctx : endo (E -< itree (E +1 E'))) : E -< itree E' :=
    itree_mrec (ctx itree_trigger_inl1)
  .

  Definition calling {A : Type} {B : Type} {E : Type -> Type} (callee : A -> itree E B) : callE A B -< itree E :=
    fun R : Type =>
    fun e : callE A B R =>
    match e in callE _ _ X return itree E X with
    | Call arg => callee arg
    end
  .

  Definition itree_rec {E : Type -> Type} {A B : Type} (body : A -> itree (callE A B +1 E) B) : A -> itree E B :=
    fun arg : A =>
    itree_mrec (calling body) B (Call arg)
  .

  Definition itree_call {E : Type -> Type} {A : Type} {B : Type} : A -> itree (callE A B +1 E) B :=
    fun arg : A =>
    itree_trigger B (inl1 (Call arg))
  .

  Definition itree_rec_fix {E : Type -> Type} {A : Type} {B : Type} (body : endo (A -> itree (callE A B +1 E) B)) : A -> itree E B :=
    itree_rec (body itree_call)
  .

  End RECURSION.

End InteractionTrees.
