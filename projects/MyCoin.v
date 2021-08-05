Require Import Coq.Program.Basics.
Require Import DschingisKhan.pure.DomainTheory.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module MyCoInductive.

  Set Primitive Projections.

  Import MyUtilities BasicSetoidTheory MyEnsemble BasicPosetTheory ConstructiveCoLaTheory PowerSetCoLa.

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

  Global Notation " c '->coefficient' " := (coefficient c) (at level 5, left associativity) : type_scope.

  Global Notation " c '->getDegreeOf' " := (getDegreeOf c) (at level 5, left associativity) : type_scope.

  Global Notation " c '->obtainIndex' " := (obtainIndex c) (at level 5, left associativity) : type_scope.

  Definition runContainer {Idx_in : Type} {Idx_out : Type} : Container Idx_in Idx_out -> (Idx_in -> Type) -> (Idx_out -> Type) :=
    fun c : Container Idx_in Idx_out =>
    fun X_i : Idx_in -> Type =>
    fun o : Idx_out =>
    {a : c->coefficient o & forall n : c->getDegreeOf o a, X_i (c->obtainIndex o a n)}
  .

  Global Notation " c '->runContainer' " := (runContainer c) (at level 5, left associativity) : type_scope.

  Section GeneralBisimilarityMap.

  Context {Idx_in : Type} {Idx_out : Type} {c : Container Idx_in Idx_out} {LHS : Idx_in -> Type} {RHS : Idx_in -> Type}.

  Variant BisimilarityF (sim : forall i : Idx_in, LHS i -> RHS i -> Prop) : (forall o : Idx_out, c->runContainer LHS o -> c->runContainer RHS o -> Prop) :=
  | Bisimilar1 :
    forall o : Idx_out,
    forall a : c->coefficient o,
    forall lhs_snd : forall n : c->getDegreeOf o a, LHS (c->obtainIndex o a n),
    forall rhs_snd : forall n : c->getDegreeOf o a, RHS (c->obtainIndex o a n),
    (forall n : c->getDegreeOf o a, sim (c->obtainIndex o a n) (lhs_snd n) (rhs_snd n)) -> 
    BisimilarityF sim o (existT _ a lhs_snd) (existT _ a rhs_snd)
  .

  Context {sim : forall i : Idx_in, LHS i -> RHS i -> Prop} {o : Idx_out}.

  Definition BisimilarityF_intro : forall a : c->coefficient o, forall lhs_snd : forall n : c->getDegreeOf o a, LHS (c->obtainIndex o a n), forall rhs_snd : forall n : c->getDegreeOf o a, RHS (c->obtainIndex o a n), (forall n : c->getDegreeOf o a, sim (c->obtainIndex o a n) (lhs_snd n) (rhs_snd n)) -> BisimilarityF sim o (existT _ a lhs_snd) (existT _ a rhs_snd) :=
    Bisimilar1 sim o
  .

  Definition BisimilarityF_elim {lhs : c->runContainer LHS o} {rhs : c->runContainer RHS o} : BisimilarityF sim o lhs rhs -> exists a : c->coefficient o, exists lhs_snd : forall n : c->getDegreeOf o a, LHS (c->obtainIndex o a n), exists rhs_snd : forall n : c->getDegreeOf o a, RHS (c->obtainIndex o a n), (forall n : c->getDegreeOf o a, sim (c->obtainIndex o a n) (lhs_snd n) (rhs_snd n)) /\ lhs = existT _ a lhs_snd /\ rhs = existT _ a rhs_snd :=
    fun Hb : BisimilarityF sim o lhs rhs =>
    match Hb with
    | Bisimilar1 _ o' a' lhs_snd' rhs_snd' H_sim' => ex_intro _ a' (ex_intro _ lhs_snd' (ex_intro _ rhs_snd' (conj H_sim' (conj eq_refl eq_refl))))
    end
  .

  End GeneralBisimilarityMap.

  Definition mapContainer {Idx : Type} {src : Idx -> Type} {tgt : Idx -> Type} : forall c : Container Idx Idx, (forall i : Idx, src i -> tgt i) -> (forall o : Idx, c->runContainer src o -> c->runContainer tgt o) :=
    fun c : Container Idx Idx =>
    fun hom : forall i : Idx, src i -> tgt i =>
    fun o : Idx =>
    fun input : c->runContainer src o =>
    match input with
    | existT _ a pow => existT _ a (fun n : c->getDegreeOf o a => hom (c->obtainIndex o a n) (pow n))
    end
  .

  Global Notation " c '->mapContainer' " := (mapContainer c) (at level 5, left associativity) : type_scope.

  CoInductive _M (Idx : Type) (c : Container Idx Idx) (i : Idx) : Type :=
    fold_M { unfold_M : c->runContainer (_M Idx c) i }
  .

  Definition myM {Idx : Type} : Container Idx Idx -> Idx -> Type :=
    _M Idx
  .

  Global Notation " c '->myM' " := (myM c) (at level 5, left associativity) : type_scope.

  Definition fold_myM {Idx : Type} : forall c : Container Idx Idx, forall i : Idx, c->runContainer c->myM i -> c->myM i :=
    fold_M Idx
  .

  Global Notation " c '->fold_myM' " := (fold_myM c) (at level 5, left associativity) : type_scope.

  Definition unfold_myM {Idx : Type} : forall c : Container Idx Idx, forall i : Idx, c->myM i -> c->runContainer c->myM i:=
    unfold_M Idx
  .

  Global Notation " c '->unfold_myM' " := (unfold_myM c) (at level 5, left associativity) : type_scope.

  Definition acc_myM {Idx : Type} {X_i : Idx -> Type} : forall c : Container Idx Idx, (forall i : Idx, X_i i -> c->runContainer X_i i) -> (forall i : Idx, X_i i -> c->myM i) :=
    fun c : Container Idx Idx =>
    fun coalg : forall i : Idx, X_i i -> c->runContainer X_i i =>
    cofix acc_myM_cofix : forall i : Idx, X_i i -> c->myM i :=
    fun i : Idx =>
    fun src : X_i i =>
    c->fold_myM i (c->mapContainer acc_myM_cofix i (coalg i src))
  .

  Global Notation " c '->acc_myM' " := (acc_myM c) (at level 5, left associativity) : type_scope.

  Section GeneralBisimilarity.

  Context {Idx : Type} (c : Container Idx Idx).

  Definition bisimF : ensemble {i : Idx & prod (c->myM i) (c->myM i)} -> ensemble {i : Idx & prod (c->myM i) (c->myM i)} :=
    fun sim : {i : Idx & prod (c->myM i) (c->myM i)} -> Prop =>
    uncurry' (fun i : Idx => fun lhs : c->myM i => fun rhs : c->myM i => @BisimilarityF Idx Idx c c->myM c->myM (curry' sim) i (c->unfold_myM i lhs) (c->unfold_myM i rhs))
  .

  Lemma bisimF_isMonotonicMap :
    isMonotonicMap bisimF.
  Proof with eauto.
    intros sim1 sim2 H_incl [i [lhs rhs]] Hb.
    simpl in *.
    destruct (BisimilarityF_elim Hb) as [a [lhs_snd [rhs_snd [H_sim [Heq1 Heq2]]]]].
    rewrite Heq1, Heq2.
    apply (BisimilarityF_intro a lhs_snd rhs_snd).
    intros n.
    apply H_incl.
    exact (H_sim n).
  Qed.

  Definition bisim : ensemble {i : Idx & prod (c->myM i) (c->myM i)} >=> ensemble {i : Idx & prod (c->myM i) (c->myM i)} :=
    paco (exist isMonotonicMap bisimF bisimF_isMonotonicMap)
  .

  End GeneralBisimilarity.

End MyCoInductive.
