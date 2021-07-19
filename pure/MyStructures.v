Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.

Global Create HintDb my_hints.

Module BasicSetoidTheory.

  Class isSetoid (A : Type) : Type :=
    { eqProp : A -> A -> Prop
    ; Setoid_requiresEquivalence :> Equivalence eqProp
    }
  .

  Global Notation "x == y" := (eqProp x y) (at level 70, no associativity) : type_scope.

  Lemma Setoid_refl {A : Type} `{A_isSetoid : isSetoid A} :
    forall x1 : A,
    x1 == x1.
  Proof.
    apply Setoid_requiresEquivalence.
  Qed.

  Global Hint Resolve Setoid_refl : my_hints.

  Lemma Setoid_sym {A : Type} `{A_isSetoid : isSetoid A} :
    forall x1 : A,
    forall x2 : A,
    x1 == x2 ->
    x2 == x1.
  Proof.
    apply Setoid_requiresEquivalence.
  Qed.

  Global Hint Resolve Setoid_sym : my_hints.

  Lemma Setoid_trans {A : Type} `{A_isSetoid : isSetoid A} :
    forall x1 : A,
    forall x2 : A,
    forall x3 : A,
    x1 == x2 ->
    x2 == x3 ->
    x1 == x3.
  Proof.
    apply Setoid_requiresEquivalence.
  Qed.

  Global Hint Resolve Setoid_trans : my_hints.

  Add Parametric Relation (A : Type) (A_requiresSetoid : isSetoid A) : A eqProp
    reflexivity proved by Setoid_refl
    symmetry proved by Setoid_sym
    transitivity proved by Setoid_trans
  as Setoid_rel.

  Global Program Instance Prop_isSetoid : isSetoid Prop :=
    { eqProp :=
      fun p : Prop =>
      fun q : Prop =>
      p <-> q
    }
  .

  Next Obligation with tauto.
    split; red...
  Qed.

  Local Program Instance arrow_isSetoid {A : Type} {B : Type} (B_requiresSetoid : isSetoid B) : isSetoid (arrow A B) :=
    { eqProp :=
      fun f1 : A -> B =>
      fun f2 : A -> B =>
      forall x : A,
      f1 x == f2 x
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Local Program Instance SubSetoid {A : Type} {P : A -> Prop} (A_requiresSetoid : isSetoid A) : isSetoid {x : A | P x} :=
    { eqProp :=
      fun x1 : @sig A P =>
      fun x2 : @sig A P =>
      proj1_sig x1 == proj1_sig x2
    }
  .

  Next Obligation with eauto with *.
    split; red...
  Qed.

End BasicSetoidTheory.

Module BasicPosetTheory.

  Import BasicSetoidTheory.

  Class isPoset (A : Type) : Type :=
    { leProp : A -> A -> Prop
    ; Poset_requiresSetoid :> isSetoid A
    ; Poset_requiresPreOrder :> PreOrder leProp
    ; Poset_requiresPartialOrder :> PartialOrder eqProp leProp
    }
  .

  Global Notation "x =< y" := (leProp x y) (at level 70, no associativity) : type_scope.

  Lemma Poset_refl {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    x1 =< x1.
  Proof.
    apply Poset_requiresPreOrder.
  Qed.

  Global Hint Resolve Poset_refl : my_hints.

  Lemma Poset_refl1 {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    forall x2 : A,
    x1 == x2 ->
    x1 =< x2.
  Proof.
    apply Poset_requiresPartialOrder.
  Qed.

  Global Hint Resolve Poset_refl1 : my_hints.

  Lemma Poset_refl2 {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    forall x2 : A,
    x1 == x2 ->
    x2 =< x1.
  Proof.
    apply Poset_requiresPartialOrder.
  Qed.

  Global Hint Resolve Poset_refl2 : my_hints.

  Lemma Poset_asym {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    forall x2 : A,
    x1 =< x2 ->
    x2 =< x1 ->
    x1 == x2.
  Proof.
    intros x1 x2 H H0.
    apply Poset_requiresPartialOrder.
    split.
    - apply H.
    - apply H0.
  Qed.

  Global Hint Resolve Poset_asym : my_hints.

  Lemma Poset_trans {A : Type} `{A_isPoset : isPoset A} :
    forall x1 : A,
    forall x2 : A,
    forall x3 : A,
    x1 =< x2 ->
    x2 =< x3 ->
    x1 =< x3.
  Proof.
    apply Poset_requiresPreOrder.
  Qed.

  Global Hint Resolve Poset_trans : my_hints.

  Definition isMonotonicMap {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} : (D -> D') -> Prop :=
    fun f : D -> D' =>
    forall x1 : D,
    forall x2 : D,
    x1 =< x2 ->
    f x1 =< f x2
  .

  Global Hint Unfold isMonotonicMap : my_hints.

  Lemma MonotonicMap_preservesSetoid {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} :
    forall f : D -> D',
    isMonotonicMap f ->
    forall x1 : D,
    forall x2 : D,
    x1 == x2 ->
    f x1 == f x2.
  Proof with eauto with *.
    intros f H x1 x2 H0.
    apply Poset_asym...
  Qed.

  Global Hint Resolve MonotonicMap_preservesSetoid : my_hints.

  Global Notation "D1 >=> D2" := (@sig (D1 -> D2) (fun f : D1 -> D2 => isMonotonicMap f)) (at level 50, no associativity) : type_scope.

  Add Parametric Morphism (A : Type) (B : Type) (A_requiresPoset : isPoset A) (B_requiresPoset : isPoset B) (f : A -> B) (H : isMonotonicMap f) : 
    f with signature (eqProp ==> eqProp)
  as MonotonicMap_Morphism.
  Proof.
    apply (MonotonicMap_preservesSetoid f H).
  Defined.

  Local Program Instance Prop_isPoset : isPoset Prop :=
    { leProp :=
      fun p : Prop =>
      fun q : Prop =>
      p -> q
    ; Poset_requiresSetoid := Prop_isSetoid
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Next Obligation with eauto with *.
    split...
  Qed.

  Local Program Instance arrow_isPoset {A : Type} {B : Type} (B_requiresPoset : isPoset B) : isPoset (arrow A B) :=
    { leProp :=
      fun f1 : A -> B =>
      fun f2 : A -> B =>
      forall x : A,
      f1 x =< f2 x
    ; Poset_requiresSetoid := arrow_isSetoid (@Poset_requiresSetoid B B_requiresPoset)
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Next Obligation with firstorder with my_hints.
    split; simpl...
  Qed.

  Local Program Instance SubPoset {A : Type} {P : A -> Prop} (A_requiresPoset : isPoset A) : isPoset {x : A | P x} :=
    { leProp :=
      fun x1 : @sig A P =>
      fun x2 : @sig A P =>
      proj1_sig x1 =< proj1_sig x2
    ; Poset_requiresSetoid := SubSetoid (@Poset_requiresSetoid A A_requiresPoset)
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Next Obligation with firstorder with my_hints.
    split; unfold flip...
  Qed.

End BasicPosetTheory.

Module MyEnsemble.

  Definition ensemble : Type -> Type :=
    fun A : Type =>
    arrow A Prop
  .

  Definition member {A : Type} : A -> ensemble A -> Prop :=
    fun x : A =>
    fun X : ensemble A =>
    X x
  .

  Global Notation " x '\in' X " := (member x X) (at level 70, no associativity) : type_scope.

  Global Notation " X1 '\subseteq' X2 " := (forall x : _, member x X1 -> member x X2) (at level 70, no associativity) : type_scope.

  Inductive finite {A : Type} : list A -> ensemble A :=
  | in_finite {xs : list A} :
    forall x : A,
    In x xs ->
    x \in finite xs
  .

  Global Hint Constructors finite : my_hints.

  Global Notation " '\emptyset' " := (finite nil) (at level 0) : type_scope.

  Lemma in_empty_iff {A : Type} :
    forall x : A,
    x \in \emptyset <-> False.
  Proof with eauto.
    intros x.
    replace False with (In x nil)...
    split.
    - intros H.
      inversion H; subst...
    - intros H.
      econstructor...
  Qed.

  Global Notation " '\left\{' x1 '\right\}' " := (finite (cons x1 nil)) (at level 0) : type_scope.

  Lemma in_singleton_iff {A : Type} :
    forall x : A,
    forall x1 : A,
    x \in \left\{ x1 \right\} <-> x1 = x.
  Proof with eauto.
    intros x x1.
    split.
    - intros H.
      inversion H; subst.
      destruct H0 as [H0 | []]; subst...
    - intros H.
      econstructor.
      simpl...
  Qed.

  Global Notation " '\left\{' x1 , x2 , .. , xn '\right\}' " := (finite (cons x1 (cons x2 .. (cons xn nil) ..))) (at level 0) : type_scope.

  Lemma in_finite_iff {A : Type} :
    forall x : A,
    forall xs : list A,
    x \in finite xs <-> In x xs.
  Proof with eauto.
    intros x xs.
    split.
    - intros H.
      inversion H; subst...
    - intros H.
      econstructor...
  Qed.

  Inductive unions {A : Type} : ensemble (ensemble A) -> ensemble A :=
  | in_unions {Xs : ensemble (ensemble A)} :
    forall x : A,
    forall X : ensemble A,
    x \in X ->
    X \in Xs ->
    x \in (unions Xs)
  .

  Global Hint Constructors unions : my_hints.

  Global Notation " '\bigcup' Xs " := (unions Xs) (at level 45, right associativity) : type_scope.

  Lemma in_unions_iff {A : Type} :
    forall x : A,
    forall Xs : ensemble (ensemble A),
    x \in \bigcup Xs <-> exists X : ensemble A, x \in X /\ X \in Xs.
  Proof with eauto.
    intros x Xs.
    split.
    - intros H.
      inversion H; subst...
    - intros [X [H H0]].
      econstructor...
  Qed.

  Definition union {A : Type} : ensemble A -> ensemble A -> ensemble A :=
    fun X1 : ensemble A =>
    fun X2 : ensemble A =>
    unions \left\{ X1 , X2 \right\}
  .

  Global Notation " X1 '\cup' X2 " := (union X1 X2) (at level 65, left associativity) : type_scope.

  Lemma in_union_iff {A : Type} :
    forall x : A,
    forall X1 : ensemble A,
    forall X2 : ensemble A,
    x \in X1 \cup X2 <-> x \in X1 \/ x \in X2.
  Proof with eauto.
    intros x X1 X2.
    unfold union.
    rewrite in_unions_iff.
    split.
    - intros [X [H H0]].
      rewrite in_finite_iff in H0.
      destruct H0 as [H0 | [H0 | []]]; subst...
    - intros [H | H].
      + exists X1.
        rewrite in_finite_iff.
        simpl...
      + exists X2.
        rewrite in_finite_iff.
        simpl...
  Qed.

  Inductive intersection {A : Type} : ensemble A -> ensemble A -> ensemble A :=
  | in_intersection {X1 : ensemble A} {X2 : ensemble A} :
    forall x : A,
    x \in X1 ->
    x \in X2 ->
    x \in intersection X1 X2
  .

  Global Hint Constructors intersection : my_hints.

  Global Notation " X1 '\cap' X2 " := (intersection X1 X2) (at level 60, right associativity) : type_scope.

  Lemma in_intersection_iff {A : Type} :
    forall x : A,
    forall X1 : ensemble A,
    forall X2 : ensemble A,
    x \in X1 \cap X2 <-> x \in X1 /\ x \in X2.
  Proof with eauto.
    intros x X1 X2.
    split.
    - intros H.
      inversion H; subst...
    - intros [H H0].
      econstructor...
  Qed.

  Inductive image {A : Type} {B : Type} : (A -> B) -> ensemble A -> ensemble B :=
  | in_image {X : ensemble A} :
    forall x : A,
    forall f : A -> B,
    x \in X ->
    f x \in image f X
  .

  Global Hint Constructors image : my_hints.

  Global Notation " '{' f '}' '\left[' X '\right]' " := (image f X) (at level 55, no associativity) : type_scope.

  Lemma in_image_iff {A : Type} {B : Type} :
    forall y : B,
    forall f : A -> B,
    forall X : ensemble A,
    y \in {f} \left[ X \right] <-> (exists x : A, y = f x /\ x \in X).
  Proof with eauto.
    intros y f X.
    split.
    - intros H.
      inversion H; subst...
    - intros [x [H H0]].
      subst.
      econstructor...
  Qed.

  Inductive preimage {A : Type} {B : Type} : (A -> B) -> ensemble B -> ensemble A :=
  | in_preimage {Y : ensemble B} :
    forall x : A,
    forall f : A -> B,
    f x \in Y ->
    x \in preimage f Y
  .

  Global Hint Constructors preimage : my_hints.

  Global Notation " '{' f '}' '^{-1}' '\left[' X '\right]' " := (preimage f X) (at level 55, no associativity) : type_scope.

  Lemma in_preimage_iff {A : Type} {B : Type} :
    forall x : A,
    forall f : A -> B,
    forall Y : ensemble B,
    x \in {f}^{-1} \left[ Y \right] <-> f x \in Y.
  Proof with eauto.
    intros x f Y.
    split.
    - intros H.
      inversion H; subst...
    - intros H.
      econstructor...
  Qed.

  Global Ltac membership :=
    let claim := fresh "H" in
    match goal with
    | H : member ?x ?X |- _ => now (assert (claim : X x) by apply H)
    | H : sig ?X |- _ => now (assert (claim : X (proj1_sig H)) by apply (proj2_sig H))
    end
  .
  
  Global Hint Unfold member : my_hints.

  Definition isSubsetOf {A : Type} : ensemble A -> ensemble A -> Prop :=
    fun X1 : ensemble A =>
    fun X2 : ensemble A =>
    forall x : A,
    member x X1 ->
    member x X2
  .

  Global Hint Unfold isSubsetOf : my_hints.

  Definition nonempty {A : Type} : ensemble A -> Prop :=
    fun X : ensemble A =>
    exists x : A, member x X
  .

  Global Hint Unfold nonempty : my_hints.

End MyEnsemble.

Module BasicTopology.

  Import MyEnsemble.

  Class isTopologicalSpace (A : Type) : Type :=
    { isOpen : ensemble A -> Prop
    ; open_full :
      forall xs : ensemble A,
      (forall x : A, member x xs) ->
      isOpen xs
    ; open_unions :
      forall Xs : ensemble (ensemble A),
      (forall X : ensemble A, member X Xs -> isOpen X) ->
      forall xs : ensemble A,
      (forall x : A, member x xs <-> member x (unions Xs)) ->
      isOpen xs
    ; open_intersection :
      forall X1 : ensemble A,
      forall X2 : ensemble A,
      isOpen X1 ->
      isOpen X2 ->
      forall xs : ensemble A,
      (forall x : A, member x xs <-> member x (intersection X1 X2)) ->
      isOpen xs
    }
  .

  Definition isContinuousMap {A : Type} {B : Type} `{A_isTopologicalSpace : isTopologicalSpace A} `{B_isTopologicalSpace : isTopologicalSpace B} : (A -> B) -> Prop :=
    fun f : A -> B =>
    forall ys : ensemble B,
    isOpen ys ->
    isOpen (preimage f ys)
  .

  Global Hint Unfold isContinuousMap : my_hints.

  Global Notation "D1 ~> D2" := ({f : D1 -> D2 | isContinuousMap f}) (at level 50, no associativity) : type_scope.

  Local Program Instance SubspaceTopology {A : Type} {P : A -> Prop} (A_requiresTopologicalSpace : isTopologicalSpace A) : isTopologicalSpace {x : A | P x} :=
    { isOpen :=
      fun O_sub : ensemble (@sig A P) =>
      exists O : ensemble A, isOpen O /\ (forall x : sig P, member (proj1_sig x) O <-> member x O_sub)
    }
  .

  Next Obligation with eauto with *.
    exists (fun x : A => x = x).
    split.
    - apply open_full.
      reflexivity.
    - intros x.
      split...
  Qed.

  Next Obligation with eauto with *.
    set (xss := fun O : ensemble A => isOpen O /\ (exists X : ensemble (@sig A P), member X Xs /\ (forall x : sig P, member (proj1_sig x) O <-> member x X))).
    exists (unions xss).
    split.
    - apply (open_unions xss)...
      intros X [H1 H2]...
    - intros x.
      rewrite in_unions_iff.
      split.
      + intros [X [H1 H2]].
        destruct H2 as [H2 [xs' [H3 H4]]].
        apply H0.
        rewrite in_unions_iff.
        exists xs'.
        split...
        apply H4...
      + intros H1.
        assert (H2 : member x (unions Xs)) by now apply H0.
        rewrite in_unions_iff in H2.
        destruct H2 as [X [H2 H3]].
        destruct (H X H3) as [O [H4 H5]].
        exists O.
        split.
        * apply H5...
        * split... 
  Qed.

  Next Obligation with eauto with *.
    exists (intersection H H0).
    split.
    - apply (open_intersection H H0)...
    - intros x.
      rewrite in_intersection_iff.
      split.
      + intros [H6 H7].
        apply H1.
        rewrite in_intersection_iff.
        split.
        * apply H5...
        * apply H3...
      + intros H6.
        assert (H7 := proj1 (H1 x) H6).
        rewrite in_intersection_iff in H7.
        destruct H7 as [H7 H8].
        split.
        * apply H5...
        * apply H3...
  Qed.

End BasicTopology.
