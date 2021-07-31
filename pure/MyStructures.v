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
      fun P : Prop =>
      fun Q : Prop =>
      P <-> Q
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

Module MyEnsemble.

  Import BasicSetoidTheory.

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

  Variant finite {A : Type} : list A -> ensemble A :=
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

  Global Hint Resolve in_empty_iff : my_hints.

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

  Global Hint Resolve in_singleton_iff : my_hints.

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

  Global Hint Resolve in_finite_iff : my_hints.

  Variant unions {A : Type} : ensemble (ensemble A) -> ensemble A :=
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

  Global Hint Resolve in_unions_iff : my_hints.

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

  Global Hint Resolve in_union_iff : my_hints.

  Variant intersection {A : Type} : ensemble A -> ensemble A -> ensemble A :=
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

  Global Hint Resolve in_intersection_iff : my_hints.

  Variant image {A : Type} {B : Type} : (A -> B) -> ensemble A -> ensemble B :=
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

  Global Hint Resolve in_image_iff : my_hints.

  Variant preimage {A : Type} {B : Type} : (A -> B) -> ensemble B -> ensemble A :=
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

  Global Hint Resolve in_preimage_iff : my_hints.

  Definition completement {A : Type} : ensemble A -> ensemble A :=
    fun X : ensemble A =>
    fun x : A =>
    ~ member x X
  .

  Global Hint Unfold completement : my_hints.

  Global Notation " X '^c' " := (completement X) (at level 15, right associativity) : type_scope.

  Lemma in_complement_iff {A : Type} :
    forall x : A,
    forall X : ensemble A,
    member x (completement X) <-> ~ member x X.
  Proof with reflexivity.
    intros x X...
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

  Global Instance isSubsetOf_PreOrder {A : Type} :
    PreOrder (@isSubsetOf A).
  Proof with eauto with *.
    split...
  Qed.

  Global Instance isSubsetOf_PartialOrder {A : Type} :
    PartialOrder (@eqProp (ensemble A) (arrow_isSetoid Prop_isSetoid)) (@isSubsetOf A).
  Proof with firstorder.
    intros X1 X2...
  Qed.

  Definition nonempty {A : Type} : ensemble A -> Prop :=
    fun X : ensemble A =>
    exists x : A, member x X
  .

  Global Hint Unfold nonempty : my_hints.

End MyEnsemble.

Module BasicPosetTheory.

  Import BasicSetoidTheory MyEnsemble.

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
    f with signature (@eqProp A (@Poset_requiresSetoid A A_requiresPoset) ==> @eqProp B (@Poset_requiresSetoid B B_requiresPoset))
  as MonotonicMap_Morphism.
  Proof.
    exact (MonotonicMap_preservesSetoid f H).
  Defined.

  Local Program Instance Prop_isPoset : isPoset Prop :=
    { leProp :=
      fun P : Prop =>
      fun Q : Prop =>
      P -> Q
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
    intros f1 f2...
  Qed.

  Local Program Instance SubPoset {A : Type} {P : A -> Prop} (A_requiresPoset : isPoset A) : isPoset {x : A | P x} :=
    { leProp :=
      fun x1 : sig P =>
      fun x2 : sig P =>
      proj1_sig x1 =< proj1_sig x2
    ; Poset_requiresSetoid := SubSetoid (@Poset_requiresSetoid A A_requiresPoset)
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Next Obligation with firstorder with my_hints.
    intros [x1 H] [x2 H0]; unfold flip...
  Qed.

  Definition isSupremum {D : Type} `{D_isPoset : isPoset D} : D -> ensemble D -> Prop :=
    fun sup_X : D =>
    fun X : ensemble D =>
    forall d : D,
    sup_X =< d <-> (forall x : D, member x X -> x =< d)
  .

  Global Hint Unfold isSupremum : my_hints.

  Lemma isSupremum_upperbound {D : Type} `{D_isPoset : isPoset D} :
    forall sup_X : D,
    forall X : ensemble D,
    isSupremum sup_X X ->
    forall x : D,
    member x X ->
    x =< sup_X.
  Proof with eauto with *.
    intros sup_X X H x H0.
    apply H...
  Qed.

  Global Hint Resolve isSupremum_upperbound : my_hints.

  Lemma isSupremum_isSubsetOf {D : Type} `{D_isPoset : isPoset D} :
    forall X1 : ensemble D,
    forall X2 : ensemble D,
    isSubsetOf X1 X2 ->
    forall sup_X1 : D,
    isSupremum sup_X1 X1 ->
    forall sup_X2 : D,
    isSupremum sup_X2 X2 ->
    sup_X1 =< sup_X2.
  Proof with eauto with *.
    intros X1 X2 H sup_X1 H0 sup_X2 H1.
    apply H0...
  Qed.

  Global Hint Resolve isSupremum_isSubsetOf : my_hints.

  Lemma isSupremum_ext {D : Type} `{D_isPoset : isPoset D} :
    forall X1 : ensemble D,
    forall X2 : ensemble D,
    (forall x : D, member x X1 <-> member x X2) ->
    forall sup_X1 : D,
    isSupremum sup_X1 X1 ->
    forall sup_X2 : D,
    isSupremum sup_X2 X2 <-> sup_X1 == sup_X2.
  Proof with eauto with *.
    intros X1 X2 H sup_X1 H0 sup_X2.
    assert (claim1 := fun x : D => proj1 (H x)).
    assert (claim2 := fun x : D => proj2 (H x)).
    split...
    intros H1 x.
    split.
    - intros H2 x' H3.
      apply H0...
    - intros H2.
      enough (H3 : sup_X1 =< x) by apply (Poset_trans sup_X2 sup_X1 x (Poset_refl2 sup_X1 sup_X2 H1) H3).
      apply H0...
  Qed.

  Global Hint Resolve isSupremum_ext : my_hints.

  Lemma isSupremum_unique {D : Type} `{D_isPoset : isPoset D} :
    forall X : ensemble D,
    forall sup1 : D,
    isSupremum sup1 X ->
    forall sup2 : D,
    isSupremum sup2 X <-> sup1 == sup2.
  Proof with eauto with *.
    intros X sup1 H sup2...
  Qed.

  Global Hint Resolve isSupremum_unique : my_hints.

  Definition image_sup {D : Type} `{D_isPoset : isPoset D} : ensemble (ensemble D) -> ensemble D :=
    fun Xs : ensemble (ensemble D) =>
    fun sup_X : D =>
    exists X : ensemble D, member X Xs /\ isSupremum sup_X X
  .

  Global Hint Unfold image_sup : my_hints.

  Lemma sup_in_image_sup {D : Type} `{D_isPoset : isPoset D} :
    forall X : ensemble D,
    forall sup_X : D,
    isSupremum sup_X X ->
    forall Xs : ensemble (ensemble D),
    member X Xs ->
    member sup_X (image_sup Xs).
  Proof with eauto with *.
    intros X sup_X H Xs H0...
  Qed.

  Global Hint Resolve sup_in_image_sup : my_hints.

  Lemma sup_image_sup_isGreaterThan {D : Type} `{D_isPoset : isPoset D} :
    forall Xs : ensemble (ensemble D),
    forall sup : D,
    isSupremum sup (image_sup Xs) ->
    forall X : ensemble D,
    member X Xs ->
    forall sup_X : D,
    isSupremum sup_X X ->
    sup_X =< sup.
  Proof with eauto with *.
    intros Xs sup H X H0 sup_X H1...
  Qed.

  Global Hint Resolve sup_image_sup_isGreaterThan : my_hints.

  Lemma isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs {D : Type} `{D_isPoset : isPoset D} :
    forall Xs : ensemble (ensemble D),
    (forall X : ensemble D, member X Xs -> exists sup_X : D, isSupremum sup_X X) ->
    forall sup : D,
    isSupremum sup (unions Xs) <-> isSupremum sup (image_sup Xs).
  Proof with eauto with *.
    intros Xs H sup.
    split.
    - intros H0 x.
      split.
      + intros H1 x' [X [H2 H3]]...
      + intros H1.
        apply H0.
        intros x' H2.
        inversion H2; subst.
        destruct (H X H4) as [sup_xs H5]...
    - intros H0 x.
      split.
      + intros H1 x' H2.
        inversion H2; subst.
        destruct (H X H4) as [sup_X H5]...
      + intros H1.
        apply H0.
        intros x' [X [H2 H3]].
        apply H3...
  Qed.

  Global Hint Resolve isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs : my_hints.

  Definition isInfimum {D : Type} `{D_isPoset : isPoset D} : D -> ensemble D -> Prop :=
    fun inf_X : D =>
    fun X : ensemble D=>
    forall d : D,
    d =< inf_X <-> (forall x : D, member x X -> d =< x)
  .

  Global Hint Unfold isInfimum : my_hints.

  Lemma isInfimum_unique {D : Type} `{D_isPoset : isPoset D} :
    forall X : ensemble D,
    forall inf1 : D,
    isInfimum inf1 X ->
    forall inf2 : D,
    isInfimum inf2 X ->
    inf1 == inf2.
  Proof with eauto with *.
    intros X inf1 H inf2 H0.
    apply Poset_asym.
    - apply H0.
      intros x H1.
      apply H...
    - apply H.
      intros x H1.
      apply H0...
  Qed.

  Global Hint Resolve isInfimum_unique : my_hints.

  Lemma compute_Infimum {D : Type} `{D_isPoset: isPoset D} :
    forall X : ensemble D,
    forall inf_X : D,
    isSupremum inf_X (fun d : D => forall x : D, member x X -> d =< x) ->
    isInfimum inf_X X.
  Proof with eauto with *.
    intros X inf_X H d.
    split.
    - intros H0 x H1.
      transitivity inf_X; [apply H0 | apply H]...
    - intros H0...
  Qed.

  Global Hint Resolve compute_Infimum : my_hints.

  Lemma make_Supremum_to_Infimum_of_upper_bounds {D : Type} `{D_isPoset : isPoset D} :
    forall X : ensemble D,
    forall sup_X : D,
    isSupremum sup_X X ->
    isInfimum sup_X (fun x : D => sup_X =< x).
  Proof with eauto with *.
    intros X sup_X H d.
    split.
    - intros H0 x H1.
      transitivity sup_X...
    - intros H0...
  Qed.

  Definition prefixed_points {D : Type} `{D_isPoset : isPoset D} : (D -> D) -> ensemble D :=
    fun f : D -> D =>
    fun x : D =>
    f x =< x
  .

  Global Hint Unfold prefixed_points : my_hints.

  Definition fixed_points {D : Type} `{D_isSetoid : isSetoid D} : (D -> D) -> ensemble D :=
    fun f : D -> D =>
    fun x : D =>
    x == f x
  .

  Global Hint Unfold fixed_points : my_hints.

  Definition postfixed_points {D : Type} `{D_isPoset : isPoset D} : (D -> D) -> ensemble D :=
    fun f : D -> D =>
    fun x : D =>
    x =< f x
  .

  Global Hint Unfold postfixed_points : my_hints.

  Definition isLeastFixedPoint {D : Type} `{D_isPoset : isPoset D} : D -> (D -> D) -> Prop :=
    fun lfp : D =>
    fun f : D -> D =>
    member lfp (fixed_points f) /\ (forall fix_f : D, member fix_f (fixed_points f) -> lfp =< fix_f)
  .

  Global Hint Unfold isLeastFixedPoint : my_hints.

  Theorem LeastFixedPointOfMonotonicMaps {D : Type} `{D_isPoset : isPoset D} :
    forall f : D -> D,
    isMonotonicMap f ->
    forall lfp : D,
    isInfimum lfp (prefixed_points f) ->
    isLeastFixedPoint lfp f.
  Proof with eauto with *.
    intros f H lfp H0.
    assert (claim1 : f lfp =< lfp).
    { apply H0.
      intros x H1.
      assert (H2 : lfp =< x).
      { transitivity (f x).
        - apply H0...
        - apply H1.
      }
      transitivity (f x)...
    }
    enough (claim2 : lfp =< f lfp).
    { split.
      - apply Poset_asym...
      - intros fix_f H1.
        apply H0...
    }
    apply H0...
  Qed.

  Definition isGreatestFixedPoint {D : Type} `{D_isPoset : isPoset D} : D -> (D -> D) -> Prop :=
    fun gfp : D =>
    fun f : D -> D =>
    member gfp (fixed_points f) /\ (forall fix_f : D, member fix_f (fixed_points f) -> fix_f =< gfp)
  .

  Global Hint Unfold isGreatestFixedPoint : my_hints.

  Lemma GreatestFixedPointOfMonotonicMaps {D : Type} `{D_isPoset : isPoset D} :
    forall f : D -> D,
    isMonotonicMap f ->
    forall gfp : D,
    isSupremum gfp (postfixed_points f) ->
    isGreatestFixedPoint gfp f.
  Proof with eauto with *.
    intros f H gfp H0.
    assert (claim1 : gfp =< f gfp).
    { apply H0.
      intros x H1.
      transitivity (f x)...
    }
    split.
    - apply Poset_asym...
    - intros fix_f H1...
  Qed.

  Definition isSupremumIn {D : Type} `{D_isPoset : isPoset D} : D -> ensemble D -> ensemble D -> Prop :=
    fun sup_X : D =>
    fun X : ensemble D =>
    fun P : ensemble D =>
    member sup_X P /\ (forall d : D, member d P -> sup_X =< d <-> (forall x : D, member x X -> x =< d))
  .

  Lemma isSupremumIn_iff {D : Type} `{D_isPoset : isPoset D} :
    forall P : D -> Prop,
    forall sup_X : sig P,
    forall X : ensemble (sig P),
    isSupremumIn (proj1_sig sup_X) (image (@proj1_sig D P) X) P <-> @isSupremum (sig P) (SubPoset D_isPoset) sup_X X.
  Proof with eauto with *.
    intros P sup_X X.
    split.
    - intros [H H0].
      split.
      + intros H1 x H2.
        apply H0...
        membership.
      + intros H1.
        apply H0.
        * membership.
        * intros x H2.
          apply in_image_iff in H2.
          destruct H2 as [x' [H2 H3]].
          rewrite H2.
          apply H1...
    - intros H.
      split.
      + membership.
      + intros d H0.
        set (d' := exist P d H0).
        assert (H1 : sup_X =< d' <-> (forall x' : @sig D P, member x' X -> x' =< d')) by apply H.
        split.
        * intros H2 x H3.
          apply in_image_iff in H3.
          destruct H3 as [x' [H3 H4]].
          rewrite H3.
          apply H1...
        * intros H2.
          apply H1.
          intros x' H3.
          apply H2...
  Qed.

End BasicPosetTheory.

Module BasicTopology.

  Import MyEnsemble.

  Definition full {A : Type} : ensemble A :=
    fun x : A =>
    x = x
  .

  Global Hint Unfold full : my_hints.

  Class isTopologicalSpace (A : Type) : Type :=
    { isOpen : ensemble A -> Prop
    ; open_full :
      isOpen full
    ; open_unions :
      forall Xs : ensemble (ensemble A),
      (forall X : ensemble A, member X Xs -> isOpen X) ->
      isOpen (unions Xs)
    ; open_intersection :
      forall X1 : ensemble A,
      forall X2 : ensemble A,
      isOpen X1 ->
      isOpen X2 ->
      isOpen (intersection X1 X2)
    }
  .

  Global Hint Resolve open_full : my_hints.

  Global Hint Resolve open_unions : my_hints.

  Global Hint Resolve open_intersection : my_hints.

  Definition isContinuousMap {A : Type} {B : Type} `{A_isTopologicalSpace : isTopologicalSpace A} `{B_isTopologicalSpace : isTopologicalSpace B} : (A -> B) -> Prop :=
    fun f : A -> B =>
    forall ys : ensemble B,
    isOpen ys ->
    isOpen (preimage f ys)
  .

  Global Hint Unfold isContinuousMap : my_hints.

  Global Notation "D1 ~> D2" := ({f : D1 -> D2 | isContinuousMap f}) (at level 50, no associativity) : type_scope.

  Section BuildSubspaceTopology. (* Referring to "https://github.com/Abastro/Coq-Practice/blob/aeca5f68c521fe0bb07f5e12c67156060c402799/src/Topology.v" *)

  Context {A : Type} {P : A -> Prop} (A_requiresTopologicalSpace : isTopologicalSpace A).

  Let is_sub_rep : ensemble A -> ensemble (sig P) -> Prop :=
    fun O : ensemble A =>
    fun O_sub : ensemble (sig P) =>
    forall x : sig P,
    member (proj1_sig x) O <-> member x O_sub
  .

  Definition isOpen_SubspaceTopology : ensemble (sig P) -> Prop :=
    fun O_sub : ensemble (@sig A P) =>
    exists O : ensemble A, isOpen O /\ is_sub_rep O O_sub
  .

  Lemma open_full_SubspaceTopolgy :
    isOpen_SubspaceTopology full.
  Proof with ((now firstorder) || eauto with *).
    unfold isOpen_SubspaceTopology.
    exists full.
    split...
  Qed.

  Lemma open_unions_SubspaceTopology :
    forall Xs : ensemble (ensemble (sig P)),
    (forall X : ensemble (sig P), member X Xs -> isOpen_SubspaceTopology X) ->
    isOpen_SubspaceTopology (unions Xs).
  Proof with ((now firstorder) || eauto with *).
    unfold isOpen_SubspaceTopology.
    intros Xs H.
    exists (unions (fun O : ensemble A => exists O_sub : ensemble (sig P), member O_sub Xs /\ is_sub_rep O O_sub /\ isOpen O)).
    split.
    - apply open_unions.
      unfold member...
    - unfold is_sub_rep.
      intros x.
      do 2 rewrite in_unions_iff.
      unfold member at 2...
  Qed.

  Lemma open_intersection_SubspaceTopology :
    forall X1 : ensemble (sig P),
    forall X2 : ensemble (sig P),
    isOpen_SubspaceTopology X1 ->
    isOpen_SubspaceTopology X2 ->
    isOpen_SubspaceTopology (intersection X1 X2).
  Proof with ((now firstorder) || eauto with *).
    unfold isOpen_SubspaceTopology.
    intros X1 X2 [O1 [H H0]] [O2 [H1 H2]].
    exists (intersection O1 O2).
    split...
    unfold is_sub_rep.
    intros x.
    do 2 rewrite in_intersection_iff...
  Qed.

  End BuildSubspaceTopology.

  Local Instance SubspaceTopology {A : Type} {P : A -> Prop} (A_requiresTopologicalSpace : isTopologicalSpace A) : isTopologicalSpace {x : A | P x} :=
    { isOpen := isOpen_SubspaceTopology A_requiresTopologicalSpace
    ; open_full := open_full_SubspaceTopolgy A_requiresTopologicalSpace
    ; open_unions := open_unions_SubspaceTopology A_requiresTopologicalSpace
    ; open_intersection := open_intersection_SubspaceTopology A_requiresTopologicalSpace
    }
  .

End BasicTopology.
