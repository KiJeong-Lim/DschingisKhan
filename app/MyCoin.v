Require Import Coq.Program.Basics.
Require Import DschingisKhan.pure.DomainTheory.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module MyCoInductive.

  Set Primitive Projections.

  Import BasicSetoidTheory BasicPosetTheory MyEnsemble PosetTheory ConstructiveDomainTheory PowerSetLattice.

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

  (* Section 1 *)

  Record Container (Idx_in : Type) (Idx_out : Type) : Type :=
    { _Coefficient : Idx_out -> Type
    ; _GetDegreeOf : forall o : Idx_out, _Coefficient o -> Type
    ; _ObtainIndex : forall o : Idx_out, forall a : _Coefficient o, _GetDegreeOf o a -> Idx_in
    }
  .

  Definition coefficient {Idx_in : Type} {Idx_out : Type} : Container Idx_in Idx_out -> Idx_out -> Type :=
    _Coefficient Idx_in Idx_out
  .

  Definition getDegreeOf {Idx_in : Type} {Idx_out : Type} : forall c : Container Idx_in Idx_out, forall o : Idx_out, coefficient c o -> Type :=
    _GetDegreeOf Idx_in Idx_out
  .

  Definition obtainIndex {Idx_in : Type} {Idx_out : Type} : forall c : Container Idx_in Idx_out, forall o : Idx_out, forall a : coefficient c o, getDegreeOf c o a -> Idx_in :=
    _ObtainIndex Idx_in Idx_out
  .

  Global Notation "c ->coefficient " := (coefficient c) (at level 5, left associativity) : type_scope.

  Global Notation "c ->getDegreeOf " := (getDegreeOf c) (at level 5, left associativity) : type_scope.

  Global Notation "c ->obtainIndex " := (obtainIndex c) (at level 5, left associativity) : type_scope.

  Definition runContainer {Idx_in : Type} {Idx_out : Type} : Container Idx_in Idx_out -> (Idx_in -> Type) -> (Idx_out -> Type) :=
    fun c : Container Idx_in Idx_out =>
    fun X_i : Idx_in -> Type =>
    fun o : Idx_out =>
    {a : c->coefficient o & forall n : c->getDegreeOf o a, X_i (c->obtainIndex o a n)}
  .

  Global Notation "c ->runContainer " := (runContainer c) (at level 5, left associativity) : type_scope.

  Variant bisimilarity {Idx_in : Type} {Idx_out : Type} : forall c : Container Idx_in Idx_out, forall LHS : Idx_in -> Type, forall RHS : Idx_in -> Type, (forall i : Idx_in, LHS i -> RHS i -> Prop) -> (forall o : Idx_out, c->runContainer LHS o -> c->runContainer RHS o -> Prop) :=
  | Bisimilar :
    forall c : Container Idx_in Idx_out,
    forall LHS : Idx_in -> Type,
    forall RHS : Idx_in -> Type,
    forall R : forall i : Idx_in, LHS i -> RHS i -> Prop,
    forall o : Idx_out,
    forall lhs : c->runContainer LHS o,
    forall rhs : c->runContainer RHS o,
    forall projT1_eqn : projT1 lhs = projT1 rhs,
    forall projT2_sim : forall n : c->getDegreeOf o (projT1 lhs), R (c->obtainIndex o (projT1 rhs) (eq_rect (projT1 lhs) (c->getDegreeOf o) n (projT1 rhs) projT1_eqn)) (match projT1_eqn as H in eq _ projT1rhs return LHS (c->obtainIndex o projT1rhs (eq_rect (projT1 lhs) (c->getDegreeOf o) n projT1rhs H)) with eq_refl => projT2 lhs n end) (projT2 rhs (eq_rect (projT1 lhs) (c->getDegreeOf o) n (projT1 rhs) projT1_eqn)),
    bisimilarity c LHS RHS R o lhs rhs
  .

  Definition bisimilarity_intro {Idx_in : Type} {Idx_out : Type} {c : Container Idx_in Idx_out} {LHS : Idx_in -> Type} {RHS : Idx_in -> Type} {R : forall i : Idx_in, LHS i -> RHS i -> Prop} {o : Idx_out} {lhs : c->runContainer LHS o} {rhs : c->runContainer RHS o} : forall projT1_eqn : projT1 lhs = projT1 rhs, (forall n : c->getDegreeOf o (projT1 lhs), R (c->obtainIndex o (projT1 rhs) (eq_rect (projT1 lhs) (c->getDegreeOf o) n (projT1 rhs) projT1_eqn)) (match projT1_eqn as H in eq _ projT1rhs return LHS (c->obtainIndex o projT1rhs (eq_rect (projT1 lhs) (c->getDegreeOf o) n projT1rhs H)) with eq_refl => projT2 lhs n end) (projT2 rhs (eq_rect (projT1 lhs) (c->getDegreeOf o) n (projT1 rhs) projT1_eqn))) -> bisimilarity c LHS RHS R o lhs rhs := 
    Bisimilar c LHS RHS R o lhs rhs
  .

  Definition bisimilarity_elim {Idx_in : Type} {Idx_out : Type} {c : Container Idx_in Idx_out} {LHS : Idx_in -> Type} {RHS : Idx_in -> Type} {R : forall i : Idx_in, LHS i -> RHS i -> Prop} {o : Idx_out} {lhs : c->runContainer LHS o} {rhs : c->runContainer RHS o} : bisimilarity c LHS RHS R o lhs rhs -> exists projT1_eqn : projT1 lhs = projT1 rhs, (forall n : c->getDegreeOf o (projT1 lhs), R (c->obtainIndex o (projT1 rhs) (eq_rect (projT1 lhs) (c->getDegreeOf o) n (projT1 rhs) projT1_eqn)) (match projT1_eqn as H in eq _ projT1rhs return LHS (c->obtainIndex o projT1rhs (eq_rect (projT1 lhs) (c->getDegreeOf o) n projT1rhs H)) with eq_refl => projT2 lhs n end) (projT2 rhs (eq_rect (projT1 lhs) (c->getDegreeOf o) n (projT1 rhs) projT1_eqn))) :=
    fun Hb : bisimilarity c LHS RHS R o lhs rhs =>
    match Hb as Hb' in bisimilarity c' LHS' RHS' R' o' lhs' rhs' return exists projT1_eqn' : projT1 lhs' = projT1 rhs', (forall n : c'->getDegreeOf o' (projT1 lhs'), R' (c'->obtainIndex o' (projT1 rhs') (eq_rect (projT1 lhs') (c'->getDegreeOf o') n (projT1 rhs') projT1_eqn')) (match projT1_eqn' as H in eq _ projT1rhs return LHS' (c'->obtainIndex o' projT1rhs (eq_rect (projT1 lhs') (c'->getDegreeOf o') n projT1rhs H)) with eq_refl => projT2 lhs' n end) (projT2 rhs' (eq_rect (projT1 lhs') (c'->getDegreeOf o') n (projT1 rhs') projT1_eqn'))) with
    | Bisimilar c' LHS' RHS' R' o' lhs' rhs' projT1_eqn' projT2_sim' => ex_intro _ projT1_eqn' projT2_sim'
    end
  .

  (* Section 2 *)

  Definition mapContainer {Idx : Type} {src : Idx -> Type} {tgt : Idx -> Type} : forall c : Container Idx Idx, (forall i : Idx, src i -> tgt i) -> (forall o : Idx, c->runContainer src o -> c->runContainer tgt o) :=
    fun c : Container Idx Idx =>
    fun hom : forall i : Idx, src i -> tgt i =>
    fun o : Idx =>
    fun input : c->runContainer src o =>
    match input with
    | existT _ coeff pow => existT _ coeff (fun n : c->getDegreeOf o coeff => hom (c->obtainIndex o coeff n) (pow n))
    end
  .

  Global Notation "c ->mapContainer " := (mapContainer c) (at level 5, left associativity) : type_scope.

  CoInductive _M (Idx : Type) (c : Container Idx Idx) (i : Idx) : Type :=
    _FoldM { _UnfoldM : c->runContainer (_M Idx c) i }
  .

  Definition myM {Idx : Type} : Container Idx Idx -> Idx -> Type :=
    _M Idx
  .

  Definition myFoldM {Idx : Type} : forall c : Container Idx Idx, forall i : Idx, c->runContainer (myM c) i -> myM c i :=
    _FoldM Idx
  .

  Definition myUnfoldM {Idx : Type} : forall c : Container Idx Idx, forall i : Idx, myM c i -> c->runContainer (myM c) i:=
    _UnfoldM Idx
  .

  CoFixpoint cofixM {Idx : Type} {X : Idx -> Type} : forall c : Container Idx Idx, (forall i : Idx, X i -> c->runContainer X i) -> (forall i : Idx, X i -> myM c i) :=
    fun c : Container Idx Idx =>
    fun coalg : forall i : Idx, X i -> c->runContainer X i =>
    fun i : Idx =>
    fun src : X i =>
    myFoldM c i ((c->mapContainer (cofixM c coalg) i) (coalg i src))
  .

  Definition bisimF {Idx : Type} : forall c : Container Idx Idx, ensemble {i : Idx & prod (myM c i) (myM c i)} -> ensemble {i : Idx & prod (myM c i) (myM c i)} :=
    fun c : Container Idx Idx =>
    fun R : {i : Idx & prod (myM c i) (myM c i)} -> Prop =>
    uncurry' (fun i : Idx => fun lhs : myM c i => fun rhs : myM c i => bisimilarity c (myM c) (myM c) (curry' R) i (myUnfoldM c i lhs) (myUnfoldM c i rhs))
  .

  Lemma bisimF_isMonotonic {Idx : Type} :
    forall c : Container Idx Idx,
    isMonotonicMap (bisimF c).
  Proof.
    intros c R1 R2 H_incl [i [lhs rhs]] Hb.
    simpl in *.
    destruct (bisimilarity_elim Hb) as [projT1_eqn projT2_sim].
    apply (bisimilarity_intro projT1_eqn).
    intros n.
    apply H_incl, (projT2_sim n).
  Qed.

  Definition bisim {Idx : Type} : forall c : Container Idx Idx, ensemble {i : Idx & prod (myM c i) (myM c i)} >=> ensemble {i : Idx & prod (myM c i) (myM c i)} :=
    fun c : Container Idx Idx =>
    paco (exist isMonotonicMap (bisimF c) (bisimF_isMonotonic c))
  .

  (* Section 3 *)

End MyCoInductive.
