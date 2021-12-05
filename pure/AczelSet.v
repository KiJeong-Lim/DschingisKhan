Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module ConstructiveTheoryOfAczelTree. (* Thanks to Hanul Jeon *)

  Import MyUtilities MyUniverses BasicSetoidTheory BasicPosetTheory.

  Global Create HintDb aczel_hint.

  Inductive Tree : SuperiorUniverse :=
    RootNode 
    { childrenOf : InferiorUniverse
    ; childTreeOf : childrenOf -> Tree
    }
  .

  Definition AczelSet : SuperiorUniverse :=
    Tree
  .

  Definition ext_eq : AczelSet -> AczelSet -> Prop :=
    fix ext_eq_fix (t1 : Tree) {struct t1} : Tree -> Prop :=
    match t1 return Tree -> Prop with
    | RootNode children1 childtrees1 =>
      fun t2 : Tree =>
      match t2 return Prop with
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
    induction X as [children1 childtrees1 IH]; simpl...
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
      destruct (H0 child2) as [child1 H1]...
    - intros child1.
      destruct (H child1) as [child2 H1]...
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
      destruct (H1 child2) as [child3 H4]...
    - intros child3.
      destruct (H2 child3) as [child2 H3].
      destruct (H0 child2) as [child1 H4]...
  Qed.

  Global Hint Resolve ext_eq_trans : aczel_hint.

  Global Instance ext_eq_Reflexive : Reflexive ext_eq :=
    ext_eq_refl
  .

  Global Instance ext_eq_Symmetric : Symmetric ext_eq :=
    ext_eq_sym
  .

  Global Instance ext_eq_Transitive : Transitive ext_eq :=
    ext_eq_trans
  .

  Global Instance ext_eq_Equivalence : Equivalence ext_eq :=
    { Equivalence_Reflexive := ext_eq_Reflexive
    ; Equivalence_Symmetric := ext_eq_Symmetric
    ; Equivalence_Transitive := ext_eq_Transitive
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
    exists key : childrenOf Y, ext_eq X (childTreeOf Y key)
  .

  Global Hint Unfold elem : aczel_hint.

  Lemma eq_in_in :
    forall X : AczelSet,
    forall Y : AczelSet,
    forall Z : AczelSet,
    ext_eq X Y ->
    elem Y Z ->
    elem X Z.
  Proof with eauto with *.
    intros X Y Z H [child_Z H0]...
  Qed.

  Global Hint Resolve eq_in_in : aczel_hint.

  Lemma in_eq_in :
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
    destruct (H0 key) as [new_key H2]...
  Qed.

  Global Hint Resolve in_eq_in : aczel_hint.

  Add Parametric Morphism :
    elem with signature (ext_eq ==> ext_eq ==> iff)
  as elem_with_ext_eq_ext_eq_iff.
  Proof with eauto with *.
    intros x1 x2 H y1 y2 H0.
    transitivity (elem x1 y2); split...
  Qed.

  Lemma elem_intro :
    forall X : AczelSet,
    forall child_X : childrenOf X,
    elem (childTreeOf X child_X) X.
  Proof with eauto with *.
    intros X child_X...
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
    split; intros child.
    - assert (claim1 : elem (childtrees1 child) (RootNode children1 childtrees1)) by apply elem_intro.
      destruct (proj1 (H (childtrees1 child)) claim1) as [key H0]...
    - assert (claim2 : elem (childtrees2 child) (RootNode children2 childtrees2)) by apply elem_intro.
      destruct (proj2 (H (childtrees2 child)) claim2) as [key H0]...
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

  Global Instance subseteq_Reflexive :
    Reflexive subseteq.
  Proof with eauto with *.
    intros x1...
  Qed.

  Global Instance subseteq_Transtive :
    Transitive subseteq.
  Proof with eauto with *.
    intros x1 x2 x3 H H0...
  Qed.

  Global Instance subseteq_isPreOrder : PreOrder subseteq :=
    { PreOrder_Reflexive := subseteq_Reflexive
    ; PreOrder_Transitive := subseteq_Transtive
    }
  .

  Global Instance subseteq_isPartialOrder :
    PartialOrder ext_eq subseteq.
  Proof with eauto with *.
    assert (claim1 : forall X : AczelSet, forall Y : AczelSet, (subseteq X Y /\ subseteq Y X) <-> (forall Z : AczelSet, elem Z X <-> elem Z Y)) by firstorder.
    intros x1 x2.
    split; unfold relation_conjunction, flip, predicate_intersection, pointwise_extension; intros H.
    - apply claim1...
    - apply ext_eq_iff, claim1...
  Qed.

  Global Instance AczelSet_isPoset : isPoset AczelSet :=
    { leProp := subseteq
    ; Poset_requiresSetoid := AczelSet_isSetoid
    ; Poset_requiresPreOrder := subseteq_isPreOrder
    ; Poset_requiresPartialOrder := subseteq_isPartialOrder
    }
  .

  Add Parametric Morphism :
    subseteq with signature (ext_eq ==> ext_eq ==> iff)
  as subseteq_with_ext_eq_ext_eq_iff.
  Proof with eauto with *.
    intros x1 x2 H y1 y2 H0.
    transitivity (subseteq x1 y2); split...
  Qed.

  Definition respect_ext_eq : (AczelSet -> Prop) -> Prop :=
    fun phi : AczelSet -> Prop =>
    forall X : AczelSet,
    phi X ->
    forall Y : AczelSet,
    ext_eq X Y ->
    phi Y
  .

  Global Hint Unfold respect_ext_eq : aczel_hint.

  Definition ext_eq_cl : (AczelSet -> Prop) -> (AczelSet -> Prop) :=
    fun phi : AczelSet -> Prop =>
    fun X : AczelSet =>
    exists Y : AczelSet, phi Y /\ ext_eq X Y
  .

  Lemma make_respect_ext_eq :
    forall phi : AczelSet -> Prop,
    respect_ext_eq (ext_eq_cl phi).
  Proof with eauto with *.
    unfold ext_eq_cl.
    intros phi X [Z [H H0]] Y H1...
  Qed.

  Definition filter : AczelSet -> (AczelSet -> Prop) -> AczelSet :=
    fun X : AczelSet =>
    fun cond : AczelSet -> Prop =>
    let children : InferiorUniverse := {child_X : childrenOf X | cond (childTreeOf X child_X)} in
    let childtrees : children -> Tree := fun x : children => childTreeOf X (proj1_sig x) in
    RootNode children childtrees
  .

  Lemma in_filter_iff (phi : AczelSet -> Prop) :
    respect_ext_eq phi ->
    forall X : AczelSet,
    forall x : AczelSet,
    elem x (filter X phi) <-> elem x X /\ phi x.
  Proof with eauto with *.
    intros ext_cong X x.
    split; intros [[key H] H0].
    - simpl in *...
    - assert (H1 := ext_cong x H0 (childTreeOf X key) H).
      exists (exist (fun key_ : childrenOf X => phi (childTreeOf X key_)) key H1)...
  Qed.

  Global Hint Resolve in_filter_iff : aczel_hint.

  Definition fromList : list AczelSet -> AczelSet :=
    fun Xs : list AczelSet =>
    let children : InferiorUniverse := FinSet (length Xs) in
    let childtrees : children -> AczelSet := safe_nth Xs in
    RootNode children childtrees
  .

  Lemma in_fromList_iff :
    forall Xs : list AczelSet,
    forall x : AczelSet,
    elem x (fromList Xs) <-> (exists i : FinSet (length Xs), ext_eq x (safe_nth Xs i)).
  Proof with eauto with *.
    intros Xs x.
    split; [intros [key H] | intros [i H]]...
  Qed.

  Global Hint Resolve fromList : aczel_hint.

  Definition power : AczelSet -> AczelSet :=
    fun X : AczelSet =>
    let children : InferiorUniverse := childrenOf X -> Prop in
    let childtrees : children -> AczelSet := fun phi : children => RootNode {child_X : childrenOf X | phi child_X} (fun x : @sig (childrenOf X) phi => childTreeOf X (proj1_sig x)) in
    RootNode children childtrees
  .

  Lemma in_power_iff :
    forall X : AczelSet,
    forall x : AczelSet,
    elem x (power X) <-> subseteq x X.
  Proof with eauto with *.
    intros X x.
    split.
    - intros [child_X H].
      enough (claim1 : subseteq (childTreeOf (power X) child_X) X)...
      intros z [key H0].
      exists (proj1_sig key)...
    - intros H.
      exists (fun child_X : childrenOf X => elem (childTreeOf X child_X) x).
      simpl.
      destruct x as [children childtrees].
      simpl in *.
      split.
      + intros child1.
        assert (H0 := elem_intro (RootNode children childtrees) child1).
        destruct (H (childtrees child1) H0) as [child_X H1].
        enough (H2 : elem (childTreeOf X child_X) (RootNode children childtrees)) by now exists (exist _ child_X H2)...
      + intros [child_X [key H0]]...
  Qed.

  Global Hint Resolve in_power_iff : aczel_hint.

  Definition unions' : forall I : InferiorUniverse, (I -> AczelSet) -> AczelSet :=
    fun I : InferiorUniverse =>
    fun X_i : I -> Tree =>
    let children : InferiorUniverse := {i : I & childrenOf (X_i i)} in
    let childtrees : children -> Tree := fun child : children => childTreeOf (X_i (projT1 child)) (projT2 child) in
    RootNode children childtrees
  .

  Lemma in_unions'_iff :
    forall I : InferiorUniverse,
    forall X_i : I -> AczelSet,
    forall x : AczelSet,
    elem x (unions' I X_i) <-> (exists i : I, elem x (X_i i)).
  Proof with eauto with *.
    intros I X_i x.
    split.
    - intros [[i child_i] H].
      simpl in *...
    - intros [i [child_i H]].
      exists (existT _ i child_i)...
  Qed.

  Global Hint Resolve in_unions'_iff : aczel_hint.

  Definition unions : AczelSet -> AczelSet :=
    fun Xs : AczelSet =>
    unions' (childrenOf Xs) (childTreeOf Xs)
  .

  Lemma in_unions_iff :
    forall Xs : AczelSet,
    forall x : AczelSet,
    elem x (unions Xs) <-> (exists X_i : AczelSet, elem x X_i /\ elem X_i Xs).
  Proof with eauto with *.
    intros Xs x.
    unfold unions.
    rewrite in_unions'_iff.
    split; [intros [i [X_i H]] | intros [X_i [[child_i H] [i H0]]]]...
  Qed.

  Global Hint Resolve in_unions_iff : aczel_hint.

  Lemma hyp_StrongCollection (build : (AczelSet -> AczelSet -> Prop) -> AczelSet -> AczelSet) (psi : AczelSet -> AczelSet -> Prop) (X : AczelSet) (HYP : forall y : AczelSet, elem y (build psi X) <-> (exists x : AczelSet, elem x X /\ psi x y)) :
    (forall x : AczelSet, elem x X -> exists y : AczelSet, psi x y) ->
    (forall x : AczelSet, elem x X -> exists y : AczelSet, elem y (build psi X) /\ psi x y) /\ (forall y : AczelSet, elem y (build psi X) -> exists x : AczelSet, elem x X /\ psi x y).
  Proof with eauto with *.
    intros H.
    split.
    - intros x H0.
      destruct (H x H0) as [y H1].
      assert (H2 : exists x : AczelSet, elem x X /\ psi x y) by firstorder.
      assert (H3 := proj2 (HYP y) H2)...
    - intros y H0.
      apply (proj1 (HYP y))...
  Qed.

  Section FirstSectionInWhichAxiomOfChoice.

  Hypothesis axiom_of_choice : forall A : Type, forall B : Type, forall psi : A -> B -> Prop, (forall x : A, exists y : B, psi x y) -> (exists f : A -> B, forall x : A, psi x (f x)).

  (* Advise of Hanul Jeon
  Aczel의 Strong Collection의 증명을 스케치해보면
Hanul
Hanul Jeon
우선 forall x:X, exists y phi(x,y)가 성립한다고 합시다
보낸 메시지
네
Hanul
여기서 AC를 적용해서 f : forall x:X, phi(x,f(x))인 f를 찾고
Hanul
base set을 X의 base와 똑같이 잡을 겁니다
Hanul
그리고 원소는 f(x)에 대응하게끔 잡을 거고요
Hanul
Hanul Jeon
문제는 AC가 Coq에서 작동할 것 같지 않다는 거네요
  *)

  Lemma AxiomOfChoice_implies_StrongCollection (psi : AczelSet -> AczelSet -> Prop) (psi_respect_eq_on_fst : forall y : AczelSet, respect_ext_eq (fun x : AczelSet => psi x y)) (psi_respect_eq_on_snd : forall x : AczelSet, respect_ext_eq (fun y : AczelSet => psi x y)) :
    forall X : AczelSet,
    (forall x : AczelSet, elem x X -> exists y : AczelSet, psi x y) ->
    exists Y : AczelSet, (forall x : AczelSet, elem x X -> exists y : AczelSet, elem y Y /\ psi x y) /\ (forall y : AczelSet, elem y Y -> exists x : AczelSet, elem x X /\ psi x y).
  Proof with eauto with *.
    intros X H.
    set (Ground := childrenOf X).
    assert (claim1 : exists f : Ground -> AczelSet, forall x : Ground, psi (childTreeOf X x) (f x)).
    { apply axiom_of_choice with (psi := fun x : Ground => fun y : AczelSet => psi (childTreeOf X x) y).
      intros x... 
    }
    destruct claim1 as [f claim1].
    exists (RootNode Ground f).
    split.
    - intros x [key H0].
      set (y := f key).
      exists y.
      split...
      apply (psi_respect_eq_on_fst y (childTreeOf X key))...
    - intros y [key H0].
      simpl in *.
      exists (childTreeOf X key).
      split...
      apply (psi_respect_eq_on_snd (childTreeOf X key) (f key))...
  Qed.

  End FirstSectionInWhichAxiomOfChoice.

  Definition isTransitiveSet : AczelSet -> Prop :=
    fun z : AczelSet =>
    forall x : AczelSet,
    elem x z ->
    forall y : AczelSet,
    elem y x ->
    elem y z
  .

  Global Hint Unfold isTransitiveSet : aczel_hint.

  Variant isOrdinal (alpha : AczelSet) : Prop :=
  | transitive_set_of_transtive_sets_isOrdinal :
    isTransitiveSet alpha ->
    (forall beta : AczelSet, elem beta alpha -> isTransitiveSet beta) ->
    isOrdinal alpha
  .

  Global Hint Constructors isOrdinal : aczel_hint.

  Lemma isOrdinal_elem_isOrdinal :
    forall alpha : AczelSet,
    isOrdinal alpha ->
    forall beta : AczelSet,
    elem beta alpha ->
    isOrdinal beta.
  Proof with eauto with *.
    intros alpha H.
    inversion H; subst...
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
    assert (H1 := isOrdinal_elem_isOrdinal (RootNode children childtrees) H beta H0).
    destruct H0 as [key H0].
    apply (ext_cong (childTreeOf (RootNode children childtrees) key))...
  Qed.

End ConstructiveTheoryOfAczelTree.
