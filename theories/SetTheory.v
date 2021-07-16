Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.theories.MyStructures.
Require Import DschingisKhan.theories.MyUtilities.

Global Create HintDb aczel_hint.

Module Aczel.

  Import BasicSetoidTheory BasicPosetTheory MyUtilities.

  Inductive Tree : Type :=
  | RootNode (children : Type) (childtrees : children -> Tree) : Tree
  .

  Definition childrenOf : Tree -> Type :=
    fun t : Tree =>
    match t with
    | RootNode children _ => children
    end
  .

  Definition childTreeOf {t : Tree} : childrenOf t -> Tree :=
    match t with
    | RootNode _ childtrees => childtrees
    end
  .

  Definition AczelSet : Type :=
    Tree
  .

  Definition ext_eq : AczelSet -> AczelSet -> Prop :=
    fix ext_eq_fix (t1 : Tree) {struct t1} : Tree -> Prop :=
    match t1 with
    | RootNode children1 childtrees1 =>
      fun t2 : Tree =>
      match t2 with
      | RootNode children2 childtrees2 =>
        let goal1 : Prop := forall child1 : children1, exists child2 : children2, ext_eq_fix (childtrees1 child1) (childtrees2 child2) in
        let goal2 : Prop := forall child2 : children2, exists child1 : children1, ext_eq_fix (childtrees1 child1) (childtrees2 child2) in
        goal1 /\ goal2
      end
    end
  .

  Lemma ext_eq_refl :
    forall X : AczelSet,
    ext_eq X X.
  Proof with eauto with *.
    induction X as [children1 childtrees1 IH].
    split...
  Qed.

  Global Hint Resolve ext_eq_refl : aczel_hint.

  Lemma ext_eq_sym :
    forall X : AczelSet,
    forall Y : AczelSet,
    ext_eq X Y ->
    ext_eq Y X.
  Proof with eauto with *.
    induction X as [children1 childtrees1 IH].
    intros [children2 childtrees2] [H H0].
    split.
    - intros child2.
      destruct (H0 child2) as [child1 H1].
      exists child1...
    - intros child1.
      destruct (H child1) as [child2 H1].
      exists child2...
  Qed.

  Global Hint Resolve ext_eq_sym : aczel_hint.

  Lemma ext_eq_trans :
    forall X : AczelSet,
    forall Y : AczelSet,
    forall Z : AczelSet,
    ext_eq X Y ->
    ext_eq Y Z ->
    ext_eq X Z.
  Proof with eauto with *.
    intros X Y.
    revert Y X.
    induction Y as [children2 childtrees2 IH].
    intros [children1 childtrees1] [children3 childtrees3] [H H0] [H1 H2].
    split.
    - intros child1.
      destruct (H child1) as [child2 H3].
      destruct (H1 child2) as [child3 H4].
      exists child3...
    - intros child3.
      destruct (H2 child3) as [child2 H3].
      destruct (H0 child2) as [child1 H4].
      exists child1...
  Qed.

  Global Hint Resolve ext_eq_trans : aczel_hint.

  Global Instance ext_eq_Equivalence : Equivalence ext_eq :=
    { Equivalence_Reflexive := ext_eq_refl
    ; Equivalence_Symmetric := ext_eq_sym
    ; Equivalence_Transitive := ext_eq_trans
    }
  .

  Global Instance AczelSet_isSetoid : isSetoid AczelSet :=
    { eqProp := ext_eq
    ; Setoid_requiresEquivalence := ext_eq_Equivalence
    }
  .

  Definition elem : AczelSet -> AczelSet -> Prop :=
    fun X : AczelSet =>
    fun Y : AczelSet =>
    exists key : childrenOf Y, ext_eq X (childTreeOf key)
  .

  Lemma X_eq_Y_in_Z_implies :
    forall X : AczelSet,
    forall Y : AczelSet,
    forall Z : AczelSet,
    ext_eq X Y ->
    elem Y Z ->
    elem X Z.
  Proof with eauto with *.
    intros X Y Z H [child_Z H0].
    exists child_Z...
  Qed.

  Global Hint Resolve X_eq_Y_in_Z_implies : aczel_hint.

  Lemma X_in_Y_eq_Z_implies :
    forall X : AczelSet,
    forall Y : AczelSet,
    forall Z : AczelSet,
    elem X Y ->
    ext_eq Y Z ->
    elem X Z.
  Proof with eauto with *.
    intros X Y Z.
    revert Z X Y.
    induction Z as [children3 childtrees3 IH].
    intros X [children2 childtrees2] [key H] [H0 H1].
    simpl in *.
    destruct (H0 key) as [new_key H2].
    exists new_key...
  Qed.

  Global Hint Resolve X_in_Y_eq_Z_implies : aczel_hint.

  Lemma elem_intro :
    forall X : AczelSet,
    forall child_X : childrenOf X,
    elem (childTreeOf child_X) X.
  Proof with eauto with *.
    intros X child_X.
    exists child_X...
  Qed.

  Global Hint Resolve elem_intro : aczel_hint.

  Lemma ext_eq_intro :
    forall X : AczelSet,
    forall Y : AczelSet,
    (forall Z : AczelSet, elem Z X <-> elem Z Y) ->
    ext_eq X Y.
  Proof with eauto with *.
    induction X as [children1 childtrees1 IH].
    intros [children2 childtrees2] H.
    split.
    - intros child1.
      assert (H0 : elem (childtrees1 child1) (RootNode children1 childtrees1)) by apply elem_intro.
      destruct (proj1 (H (childtrees1 child1)) H0) as [key H1].
      simpl in *.
      exists key...
    - intros child2.
      assert (H0 : elem (childtrees2 child2) (RootNode children2 childtrees2)) by apply elem_intro.
      destruct (proj2 (H (childtrees2 child2)) H0) as [key H2].
      simpl in *.
      exists key...
  Qed.

  Global Hint Resolve ext_eq_intro : aczel_hint.

  Lemma ext_eq_iff :
    forall X : AczelSet,
    forall Y : AczelSet,
    ext_eq X Y <-> (forall Z : AczelSet, elem Z X <-> elem Z Y).
  Proof with eauto with *.
    intros X Y.
    split...
  Qed.

  Definition subseteq : AczelSet -> AczelSet -> Prop := 
    fun X : AczelSet =>
    fun Y : AczelSet =>
    forall Z : AczelSet,
    elem Z X ->
    elem Z Y
  .

  Global Hint Unfold subseteq : aczel_hint.

  Global Program Instance AczelSet_isPoset : isPoset AczelSet :=
    { leProp := subseteq
    ; Poset_requiresSetoid := AczelSet_isSetoid
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Next Obligation with eauto with *.
    assert (claim1 : forall X : AczelSet, forall Y : AczelSet, (subseteq X Y /\ subseteq Y X) <-> (forall Z : AczelSet, elem Z X <-> elem Z Y)) by firstorder.
    split; unfold relation_conjunction, flip, predicate_intersection, pointwise_extension.
    - intros H.
      apply claim1...
    - intros H...
      apply ext_eq_iff, claim1...
  Qed.

  Definition unions {I : Type} : (I -> AczelSet) -> AczelSet :=
    fun X_i : I -> Tree =>
    let children : Type := {i : I & childrenOf (X_i i)} in
    let childtrees : children -> Tree := fun child : children => @childTreeOf (X_i (projT1 child)) (projT2 child) in
    RootNode children childtrees
  .

  Lemma in_unions_iff :
    forall I : Type,
    forall X_i : I -> AczelSet,
    forall x : AczelSet,
    elem x (unions X_i) <-> (exists i : I, elem x (X_i i)).
  Proof with eauto with *.
    intros I X_i x.
    split.
    - intros [[i child_i] H0].
      simpl in *.
      exists i...
    - intros [i [child_i H]].
      exists (existT _ i child_i)...
  Qed.

  Definition fromList : list AczelSet -> AczelSet :=
    fun Xs : list AczelSet =>
    RootNode (FinSet (length Xs)) (safe_nth Xs)
  .

  Lemma in_fromList_iff :
    forall Xs : list AczelSet,
    forall x : AczelSet,
    elem x (fromList Xs) <-> (exists i : FinSet (length Xs), ext_eq x (safe_nth Xs i)).
  Proof with eauto with *.
    intros Xs x.
    split.
    - intros [key H]...
    - intros [i H].
      exists i...
  Qed.

  Definition Power : AczelSet -> AczelSet :=
    fun X : AczelSet =>
    RootNode (childrenOf X -> Prop) (fun phi : childrenOf X -> Prop => RootNode {child_X : childrenOf X | phi child_X} (fun x : @sig (childrenOf X) phi => childTreeOf (proj1_sig x)))
  .

  Lemma in_Power_iff :
    forall X : AczelSet,
    forall x : AczelSet,
    elem x (Power X) <-> subseteq x X.
  Proof with eauto with *.
    intros X x.
    split.
    - intros [child_X H].
      enough (claim1 : subseteq (childTreeOf child_X) X)...
      intros z [key H0].
      exists (proj1_sig key)...
    - intros H.
      exists (fun child_X : childrenOf X => elem (childTreeOf child_X) x).
      simpl.
      destruct x as [children childtrees].
      simpl in *.
      split.
      + intros child1.
        assert (H0 := elem_intro (RootNode children childtrees) child1).
        destruct (H (childtrees child1) H0) as [child_X H1].
        assert (H2 : elem (childTreeOf child_X) (RootNode children childtrees))...
        exists (exist _ child_X H2)...
      + intros [child_X [key H0]].
        simpl in *.
        exists key...
  Qed.

  Definition isTransitiveSet : AczelSet -> Prop :=
    fun A : AczelSet =>
    forall x : AczelSet,
    elem x A ->
    forall y : AczelSet,
    elem y x ->
    elem y A
  .

  Global Hint Unfold isTransitiveSet : aczel_hint.

  Definition respect_ext_eq : (AczelSet -> Prop) -> Prop :=
    fun phi : AczelSet -> Prop =>
    forall X : AczelSet,
    phi X ->
    forall Y : AczelSet,
    ext_eq X Y ->
    phi Y
  .

  Global Hint Unfold respect_ext_eq : aczel_hint.

  Lemma ext_eq_closure_respect_ext_eq :
    forall phi : AczelSet -> Prop,
    respect_ext_eq (fun X : AczelSet => exists Y : AczelSet, phi Y /\ ext_eq X Y).
  Proof with eauto with *.
    intros phi X [Z [H H0]] Y H1...
  Qed.

  Inductive isOrdinal : AczelSet -> Prop :=
  | transitive_set_of_transtive_sets :
    forall alpha : AczelSet,
    isTransitiveSet alpha ->
    (forall beta : AczelSet, elem beta alpha -> isTransitiveSet beta) ->
    isOrdinal alpha
  .

  Global Hint Constructors isOrdinal : aczel_hint.

  Lemma isOrdinal_elem_isOrdinal :
    forall Y : AczelSet,
    isOrdinal Y ->
    forall X : AczelSet,
    elem X Y ->
    isOrdinal X.
  Proof with eauto with *.
    intros Y H.
    induction H as [alpha H IH]...
  Qed.

  Global Hint Resolve isOrdinal_elem_isOrdinal : aczel_hint.

  Lemma transfinite_induction_prototype (phi : AczelSet -> Prop) :
    respect_ext_eq phi ->
    (forall alpha : AczelSet, (forall beta : AczelSet, elem beta alpha -> phi beta) -> isOrdinal alpha -> phi alpha) ->
    forall gamma : AczelSet,
    isOrdinal gamma ->
    phi gamma.
  Proof with eauto with *.
    intros ext_cong ind_claim.
    induction gamma as [children childtrees IH].
    intros H.
    apply ind_claim...
    intros beta H0.
    assert (H1 : isOrdinal beta) by now apply (isOrdinal_elem_isOrdinal (RootNode children childtrees)).
    destruct H0 as [key H0].
    apply (ext_cong (childTreeOf key))...
    apply (IH key)...
  Qed.

End Aczel.
