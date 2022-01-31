Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.pure.FunFacts.
Require Import DschingisKhan.pure.MyUtilities.

Module BasicSetoidTheory.

  Import MyUtilities.

  Class isSetoid (A : Type) : Type :=
    { eqProp : A -> A -> Prop
    ; Setoid_requiresEquivalence :> Equivalence eqProp
    }
  .

  Global Notation " x '==' y " := (eqProp x y) (at level 70, no associativity) : type_scope.

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

  Global Instance bool_isSetoid : isSetoid bool :=
    { eqProp := @eq bool
    ; Setoid_requiresEquivalence := @eq_equivalence bool
    }
  .

  Global Instance nat_isSetoid : isSetoid nat :=
    { eqProp := @eq nat
    ; Setoid_requiresEquivalence := @eq_equivalence nat
    }
  .

  Global Instance Prop_isSetoid : isSetoid Prop :=
    { eqProp := iff
    ; Setoid_requiresEquivalence := iff_equivalence
    }
  .

  Polymorphic Definition from_to_ (A : Type) (B : Type) : Type :=
    forall _ : A, B
  .

  Global Infix " \to " := from_to_ (at level 60, right associativity) : type_scope.

  Polymorphic Definition arrow_eqProp : forall A : Type, forall B : Type, isSetoid B -> A \to B -> A \to B -> Prop :=
    fun A : Type =>
    fun B : Type =>
    fun B_requiresSetoid : isSetoid B =>
    fun f1 : A -> B =>
    fun f2 : A -> B =>
    forall x : A,
    @eqProp B B_requiresSetoid (f1 x) (f2 x)
  .

  Global Polymorphic Instance arrow_Equivalence {A : Type} {B : Type} `{B_isSetoid : isSetoid B} :
    Equivalence (arrow_eqProp A B B_isSetoid).
  Proof with eauto with *.
    unfold arrow_eqProp.
    split...
  Qed.

  Global Polymorphic Instance arrow_isSetoid {A : Type} {B : Type} (B_requiresSetoid : isSetoid B) : isSetoid (A \to B) :=
    { eqProp := arrow_eqProp A B B_requiresSetoid
    ; Setoid_requiresEquivalence := @arrow_Equivalence A B B_requiresSetoid
    }
  .

  Definition SubPoset_eqProp : forall A : Type, forall P : A -> Prop, isSetoid A -> sig P -> sig P -> Prop :=
    fun A : Type =>
    fun P : A -> Prop =>
    fun A_requiresSetoid : isSetoid A =>
    fun x1 : @sig A P =>
    fun x2 : @sig A P =>
    @eqProp A A_requiresSetoid (proj1_sig x1) (proj1_sig x2)
  .

  Global Instance SubPoset_eqProp_Equivalence {A : Type} {P : A -> Prop} `{A_isSetoid : isSetoid A} :
    Equivalence (SubPoset_eqProp A P A_isSetoid).
  Proof with eauto with *.
    unfold SubPoset_eqProp.
    split...
  Qed.

  Local Instance SubSetoid {A : Type} {P : A -> Prop} (A_requiresSetoid : isSetoid A) : isSetoid {x : A | P x} :=
    { eqProp := SubPoset_eqProp A P A_requiresSetoid
    ; Setoid_requiresEquivalence := @SubPoset_eqProp_Equivalence A P A_requiresSetoid
    }
  .

End BasicSetoidTheory.

Module MyEnsemble.

  Import MyUtilities BasicSetoidTheory.

  Polymorphic Definition ensemble : Type -> Type :=
    fun A : Type =>
    A \to Prop
  .

  Definition member {A : Type} : A -> ensemble A -> Prop :=
    fun x : A =>
    fun X : ensemble A =>
    X x
  .

  Global Notation " x '\in' X " := (member x X) (at level 70, no associativity) : type_scope.

  Global Notation " X1 '\subseteq' X2 " := (forall x : _, member x X1 -> member x X2) (at level 70, no associativity) : type_scope.

  Variant finite {A : Type} (xs : list A) : ensemble A :=
  | in_finite :
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

  Variant unions {A : Type} (Xs : ensemble (ensemble A)) : ensemble A :=
  | in_unions :
    forall x : A,
    forall X : ensemble A,
    x \in X ->
    X \in Xs ->
    x \in unions Xs
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

  Variant intersection {A : Type} (X1 : ensemble A) (X2 : ensemble A) : ensemble A :=
  | in_intersection :
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

  Variant image {A : Type} {B : Type} (f : A -> B) (X : ensemble A) : ensemble B :=
  | in_image :
    forall x : A,
    x \in X ->
    f x \in image f X
  .

  Global Hint Constructors image : my_hints.

  Global Notation " '{' f '}' '\left[' X '\right]' " := (image f X) (at level 55, no associativity) : type_scope.

  Lemma in_image_iff {A : Type} {B : Type} :
    forall y : B,
    forall f : A -> B,
    forall X : ensemble A,
    y \in {f}\left[ X \right] <-> (exists x : A, y = f x /\ x \in X).
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

  Variant preimage {A : Type} {B : Type} (f : A -> B) (Y : ensemble B) : ensemble A :=
  | in_preimage :
    forall x : A,
    f x \in Y ->
    x \in preimage f Y
  .

  Global Hint Constructors preimage : my_hints.

  Global Notation " '{' f '}' '^{-1}' '\left[' X '\right]' " := (preimage f X) (at level 55, no associativity) : type_scope.

  Lemma in_preimage_iff {A : Type} {B : Type} :
    forall x : A,
    forall f : A -> B,
    forall Y : ensemble B,
    x \in {f}^{-1}\left[ Y \right] <-> f x \in Y.
  Proof with eauto.
    intros x f Y.
    split.
    - intros H.
      inversion H; subst...
    - intros H.
      econstructor...
  Qed.

  Global Hint Resolve in_preimage_iff : my_hints.

  Definition complement {A : Type} : ensemble A -> ensemble A :=
    fun X : ensemble A =>
    fun x : A =>
    ~ member x X
  .

  Global Hint Unfold complement : my_hints.

  Global Notation " X '^c' " := (complement X) (at level 15, right associativity) : type_scope.

  Lemma in_complement_iff {A : Type} :
    forall x : A,
    forall X : ensemble A,
    member x (complement X) <-> ~ member x X.
  Proof with reflexivity.
    intros x X...
  Qed.

  Global Hint Resolve in_complement_iff : my_hints.

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
    @PreOrder (A \to Prop) (@isSubsetOf A).
  Proof with eauto with *.
    split...
  Qed.

  Global Instance isSubsetOf_PartialOrder {A : Type} :
    PartialOrder (@eqProp (A \to Prop) (@arrow_isSetoid A Prop Prop_isSetoid)) (@isSubsetOf A).
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

  Import ListNotations MyUtilities BasicSetoidTheory MyEnsemble.

  Class isPoset (A : Type) : Type :=
    { leProp : A -> A -> Prop
    ; Poset_requiresSetoid :> isSetoid A
    ; Poset_requiresPreOrder :> PreOrder leProp
    ; Poset_requiresPartialOrder :> PartialOrder eqProp leProp
    }
  .

  Global Notation " x '=<' y " := (leProp x y) (at level 70, no associativity) : type_scope.

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

  Global Notation " D1 '>=>' D2 " := (@sig (D1 \to D2) isMonotonicMap) (at level 100, right associativity) : type_scope.

  Add Parametric Morphism {A : Type} {B : Type} (A_requiresPoset : isPoset A) (B_requiresPoset : isPoset B) (f : A -> B) (f_monotonic : isMonotonicMap f) : 
    f with signature (@eqProp A (@Poset_requiresSetoid A A_requiresPoset) ==> @eqProp B (@Poset_requiresSetoid B B_requiresPoset))
  as MonotonicMap_Morphism.
  Proof.
    exact (MonotonicMap_preservesSetoid f f_monotonic).
  Defined.

  Definition le_PreOrder : @PreOrder nat le :=
    {| PreOrder_Reflexive := @le_reflexivity; PreOrder_Transitive := @le_transitivity |}
  .

  Definition le_PartialOrder : @PartialOrder nat (@eq nat) (@eq_equivalence nat) le le_PreOrder :=
    fun n1 : nat =>
    fun n2 : nat =>
    conj (eq_ind n1 (relation_conjunction le (flip le) n1) (conj (@le_reflexivity n1) (@le_reflexivity n1)) n2) (fun H : relation_conjunction le (flip le) n1 n2 => @le_antisymmetry n1 n2 (proj1 H) (proj2 H))
  .

  Global Instance nat_isPoset : isPoset nat :=
    { leProp := le
    ; Poset_requiresSetoid := nat_isSetoid
    ; Poset_requiresPreOrder := le_PreOrder
    ; Poset_requiresPartialOrder := le_PartialOrder
    }
  .

  Global Instance impl_PreOrder :
    PreOrder impl.
  Proof with eauto with *.
    split...
  Qed.

  Global Instance impl_PartialOrder :
    PartialOrder iff impl.
  Proof with eauto with *.
    split...
  Qed.

  Global Instance Prop_isPoset : isPoset Prop :=
    { leProp := impl
    ; Poset_requiresSetoid := Prop_isSetoid
    ; Poset_requiresPreOrder := impl_PreOrder
    ; Poset_requiresPartialOrder := impl_PartialOrder
    }
  .

  Polymorphic Definition arrow_leProp : forall A : Type, forall B : Type, isPoset B -> A \to B -> A \to B -> Prop :=
    fun A : Type =>
    fun B : Type =>
    fun B_requiresPoset : isPoset B =>
    fun f1 : A -> B =>
    fun f2 : A -> B =>
    forall x : A,
    @leProp B B_requiresPoset (f1 x) (f2 x)
  .

  Global Polymorphic Instance arrow_leProp_PreOrder {A : Type} {B : Type} `{B_isPoset : isPoset B} :
    PreOrder (arrow_leProp A B B_isPoset).
  Proof with eauto with *.
    unfold arrow_leProp.
    split...
  Qed.

  Global Polymorphic Instance arrow_leProp_PartialOrder {A : Type} {B : Type} `{B_isPoset : isPoset B} :
    PartialOrder (arrow_eqProp A B (@Poset_requiresSetoid B B_isPoset)) (arrow_leProp A B B_isPoset).
  Proof with firstorder with my_hints.
    unfold arrow_eqProp, arrow_leProp...
  Qed.

  Global Polymorphic Instance arrow_isPoset {A : Type} {B : Type} (B_requiresPoset : isPoset B) : isPoset (A \to B) :=
    { leProp := arrow_leProp A B B_requiresPoset
    ; Poset_requiresSetoid := arrow_isSetoid (@Poset_requiresSetoid B B_requiresPoset)
    ; Poset_requiresPreOrder := @arrow_leProp_PreOrder A B B_requiresPoset
    ; Poset_requiresPartialOrder := @arrow_leProp_PartialOrder A B B_requiresPoset
    }
  .

  Definition SubPoset_leProp : forall A : Type, forall P : A -> Prop, isPoset A -> sig P -> sig P -> Prop :=
    fun A : Type =>
    fun P : A -> Prop =>
    fun A_requiresPoset : isPoset A =>
    fun x1 : @sig A P =>
    fun x2 : @sig A P =>
    @leProp A A_requiresPoset (proj1_sig x1) (proj1_sig x2)
  .

  Local Instance SubPoset_leProp_PreOrder {A : Type} {P : A -> Prop} `{A_isPoset : isPoset A} :
    PreOrder (SubPoset_leProp A P A_isPoset).
  Proof with eauto with *.
    unfold SubPoset_leProp.
    split...
  Qed.

  Local Instance SubPoset_leProp_PartialOrder {A : Type} {P : A -> Prop} `{A_isPoset : isPoset A} :
    PartialOrder (SubPoset_eqProp A P (@Poset_requiresSetoid A A_isPoset)) (SubPoset_leProp A P A_isPoset).
  Proof with firstorder with my_hints.
    unfold SubPoset_eqProp, SubPoset_leProp.
    intros [x1 H] [x2 H0]; unfold flip...
  Qed.

  Local Instance SubPoset {A : Type} {P : A -> Prop} (A_requiresPoset : isPoset A) : isPoset {x : A | P x} :=
    { leProp := SubPoset_leProp A P A_requiresPoset
    ; Poset_requiresSetoid := SubSetoid (@Poset_requiresSetoid A A_requiresPoset)
    ; Poset_requiresPreOrder := @SubPoset_leProp_PreOrder A P A_requiresPoset
    ; Poset_requiresPartialOrder := @SubPoset_leProp_PartialOrder A P A_requiresPoset
    }
  .

  Definition isSupremum {D : Type} `{D_isPoset : isPoset D} : D -> ensemble D -> Prop :=
    fun sup_X : D =>
    fun X : ensemble D =>
    forall d : D,
    sup_X =< d <-> (forall x : D, member x X -> x =< d)
  .

  Global Hint Unfold isSupremum : my_hints.

  Section PosetTheory.

  Context {D : Type} `{D_isPoset : isPoset D}.

  Local Hint Unfold isSupremum : core.

  Lemma isSupremum_upperbound :
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

  Local Hint Resolve isSupremum_upperbound : core.

  Lemma isSupremum_isSubsetOf :
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

  Local Hint Resolve isSupremum_isSubsetOf : core.

  Lemma isSupremum_ext :
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

  Local Hint Resolve isSupremum_ext : core.

  Lemma isSupremum_unique :
    forall X : ensemble D,
    forall sup1 : D,
    isSupremum sup1 X ->
    forall sup2 : D,
    isSupremum sup2 X <-> sup1 == sup2.
  Proof with eauto with *.
    intros X sup1 H sup2...
  Qed.

  Local Hint Resolve isSupremum_unique : core.

  Definition image_sup : ensemble (ensemble D) -> ensemble D :=
    fun Xs : ensemble (ensemble D) =>
    fun sup_X : D =>
    exists X : ensemble D, member X Xs /\ isSupremum sup_X X
  .

  Local Hint Unfold image_sup : core.

  Lemma sup_in_image_sup :
    forall X : ensemble D,
    forall sup_X : D,
    isSupremum sup_X X ->
    forall Xs : ensemble (ensemble D),
    member X Xs ->
    member sup_X (image_sup Xs).
  Proof with eauto with *.
    intros X sup_X H Xs H0...
  Qed.

  Local Hint Resolve sup_in_image_sup : core.

  Lemma sup_image_sup_isGreaterThan :
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

  Local Hint Resolve sup_image_sup_isGreaterThan : core.

  Lemma isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs :
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

  Local Hint Resolve isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs : core.

  Definition isInfimum : D -> ensemble D -> Prop :=
    fun inf_X : D =>
    fun X : ensemble D=>
    forall d : D,
    d =< inf_X <-> (forall x : D, member x X -> d =< x)
  .

  Local Hint Unfold isInfimum : core.

  Lemma isInfimum_unique :
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

  Local Hint Resolve isInfimum_unique : core.

  Lemma compute_Infimum :
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

  Local Hint Resolve compute_Infimum : core.

  Lemma make_Supremum_to_Infimum_of_upper_bounds :
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

  Definition prefixed_points : (D -> D) -> ensemble D :=
    fun f : D -> D =>
    fun x : D =>
    f x =< x
  .

  Local Hint Unfold prefixed_points : core.

  Definition fixed_points : (D -> D) -> ensemble D :=
    fun f : D -> D =>
    fun x : D =>
    x == f x
  .

  Local Hint Unfold fixed_points : core.

  Definition postfixed_points : (D -> D) -> ensemble D :=
    fun f : D -> D =>
    fun x : D =>
    x =< f x
  .

  Local Hint Unfold postfixed_points : core.

  Definition isLeastFixedPoint : D -> (D -> D) -> Prop :=
    fun lfp : D =>
    fun f : D -> D =>
    member lfp (fixed_points f) /\ (forall fix_f : D, member fix_f (fixed_points f) -> lfp =< fix_f)
  .

  Local Hint Unfold isLeastFixedPoint : core.

  Theorem LeastFixedPointOfMonotonicMaps :
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

  Definition isGreatestFixedPoint : D -> (D -> D) -> Prop :=
    fun gfp : D =>
    fun f : D -> D =>
    member gfp (fixed_points f) /\ (forall fix_f : D, member fix_f (fixed_points f) -> fix_f =< gfp)
  .

  Local Hint Unfold isGreatestFixedPoint : core.

  Lemma GreatestFixedPointOfMonotonicMaps :
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

  Definition isSupremumIn : D -> ensemble D -> ensemble D -> Prop :=
    fun sup_X : D =>
    fun X : ensemble D =>
    fun P : ensemble D =>
    member sup_X P /\ (forall d : D, member d P -> sup_X =< d <-> (forall x : D, member x X -> x =< d))
  .

  Lemma isSupremumIn_iff :
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

  End PosetTheory.

  Global Hint Unfold image_sup isInfimum prefixed_points fixed_points postfixed_points isLeastFixedPoint isGreatestFixedPoint : my_hints.

  Global Hint Resolve isSupremum_upperbound isSupremum_isSubsetOf isSupremum_ext isSupremum_unique sup_in_image_sup sup_image_sup_isGreaterThan isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs isInfimum_unique compute_Infimum : my_hints.

  Section LEXICOGRAPHICAL_ORDER.

  Polymorphic Context {A : Type} `{A_isPoset : isPoset A}.

  Polymorphic Variable compare : A -> A -> comparison.

  Polymorphic Fixpoint lex_compare (xs : list A) (ys : list A) {struct xs} : comparison :=
    match xs with
    | [] =>
      match ys with
      | [] => Eq
      | y :: ys => Lt
      end
    | x :: xs =>
      match ys with
      | [] => Gt
      | y :: ys =>
        match compare x y with
        | Lt => Lt
        | Eq => lex_compare xs ys
        | Gt => Gt
        end
      end
    end
  .

  Polymorphic Definition lex_eq : list A -> list A -> Prop :=
    fun xs : list A =>
    fun ys : list A =>
    lex_compare xs ys = Eq
  .

  Polymorphic Definition lex_le : list A -> list A -> Prop :=
    fun xs : list A =>
    fun ys : list A =>
    lex_compare xs ys = Lt \/ lex_compare xs ys = Eq
  .

  Polymorphic Hypothesis compare_spec_LT : forall lhs : A, forall rhs : A, compare lhs rhs = Lt -> lhs =< rhs /\ ~ lhs == rhs.

  Polymorphic Hypothesis compare_spec_EQ : forall lhs : A, forall rhs : A, compare lhs rhs = Eq -> lhs == rhs.

  Polymorphic Hypothesis compare_spec_GT : forall lhs : A, forall rhs : A, compare lhs rhs = Gt -> rhs =< lhs /\ ~ lhs == rhs.

  Polymorphic Lemma compare_spec :
    forall lhs : A,
    forall rhs : A,
    match compare lhs rhs with
    | Lt => lhs =< rhs /\ ~ lhs == rhs
    | Eq => lhs == rhs
    | Gt => rhs =< lhs /\ ~ lhs == rhs
    end.
  Proof with eauto with *.
    intros lhs rhs; destruct (compare lhs rhs) eqn: H_compare_result...
  Qed.

  Local Polymorphic Instance lex_eq_Equivalence :
    Equivalence lex_eq.
  Proof with discriminate || eauto with *.
    unfold lex_eq. split.
    - intros xs1; induction xs1 as [ | x1 xs1 IH]; simpl...
      assert (claim1 := compare_spec x1 x1).
      destruct (compare x1 x1) eqn: H_compare_result1...
      all: contradiction (proj2 claim1)...
    - intros xs1 xs2; revert xs1 xs2; induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl...
      assert (claim1 := compare_spec x1 x2); assert (claim2 := compare_spec x2 x1).
      destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x1) eqn: H_compare_result2...
      all: contradiction (proj2 claim2)...
    - intros xs1 xs2 xs3; revert xs1 xs3; induction xs2 as [ | x2 xs2 IH]; destruct xs1 as [ | x1 xs1]; destruct xs3 as [ | x3 xs3]; simpl...
      assert (claim1 := compare_spec x1 x2); assert (claim2 := compare_spec x2 x3); assert (claim3 := compare_spec x1 x3).
      destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x3) eqn: H_compare_result2; destruct (compare x1 x3) eqn: H_compare_result3...
      all: contradiction (proj2 claim3)...
  Qed.

  Local Polymorphic Instance list_isSetoid_wrt_lex_eq : isSetoid (list A) :=
    { eqProp := lex_eq
    ; Setoid_requiresEquivalence := lex_eq_Equivalence
    }
  .

  Local Polymorphic Instance lex_le_PreOrder :
    PreOrder lex_le.
  Proof with discriminate || eauto with *.
    assert (lemma1 : forall x1 : A, forall x2 : A, x1 =< x2 -> x2 =< x1 -> x1 == x2).
    { intros x1 x2 H_LE1 H_LE2. apply Poset_requiresPartialOrder. split... }
    assert (lemma2 : forall x1 : A, forall x2 : A, x1 == x2 -> x1 =< x2) by apply Poset_refl1.
    assert (lemma3 : forall x1 : A, forall x2 : A, x1 == x2 -> x2 =< x1) by apply Poset_refl2.
    unfold lex_le. split.
    - intros xs1; right. apply lex_eq_Equivalence.
    - intros xs1 xs2 xs3; revert xs1 xs3; induction xs2 as [ | x2 xs2 IH]; destruct xs1 as [ | x1 xs1]; destruct xs3 as [ | x3 xs3]; simpl...
      intros [H_false | H_false]...
      assert (claim1 := compare_spec x1 x2); assert (claim2 := compare_spec x2 x3); assert (claim3 := compare_spec x1 x3); assert (claim4 := IH xs1 xs3).
      destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x3) eqn: H_compare_result2; destruct (compare x1 x3) eqn: H_compare_result3...
      + contradiction (proj2 claim3)...
      + contradiction (proj2 claim2)...
      + contradiction (proj2 claim3); apply lemma1; [transitivity x2 | exact (proj1 claim3)]. apply lemma2... exact (proj1 claim2).
      + contradiction (proj2 claim2)...
      + contradiction (proj2 claim1)...
      + contradiction (proj2 claim3); apply lemma1; [transitivity x2 | exact (proj1 claim3)]. exact (proj1 claim1). apply lemma2...
      + contradiction (proj2 claim1); apply lemma1; [exact (proj1 claim1) | transitivity x3]. exact (proj1 claim2). apply lemma2...
      + contradiction (proj2 claim1); apply lemma1; [exact (proj1 claim1) | transitivity x3]. exact (proj1 claim2). exact (proj1 claim3).
      + intros ? [? | ?]...
      + intros [? | ?]...
      + intros [? | ?]...
      + intros [? | ?]...
  Qed.

  Polymorphic Lemma lex_le_flip_spec :
    forall lhs : list A,
    forall rhs : list A,
    match lex_compare lhs rhs with
    | Lt => lex_compare rhs lhs = Gt
    | Eq => lex_compare rhs lhs = Eq
    | Gt => lex_compare rhs lhs = Lt
    end.
  Proof with discriminate || eauto with *.
    assert (lemma1 : forall x1 : A, forall x2 : A, x1 =< x2 -> x2 =< x1 -> x1 == x2).
    { intros x1 x2 H_LE1 H_LE2. apply Poset_requiresPartialOrder. split... }
    assert (lemma2 : forall x1 : A, forall x2 : A, x1 == x2 -> x1 =< x2) by apply Poset_refl1.
    assert (lemma3 : forall x1 : A, forall x2 : A, x1 == x2 -> x2 =< x1) by apply Poset_refl2.
    assert (lemma4 : forall xs1 : list A, forall xs2 : list A, lex_compare xs1 xs2 = Lt <-> lex_compare xs2 xs1 = Gt).
    { induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl... split...
      assert (claim1 := compare_spec x1 x2); assert (claim2 := compare_spec x2 x1); assert (claim3 := IH xs2).
      destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x1) eqn: H_compare_result2...
      - contradiction (proj2 claim2)...
      - contradiction (proj2 claim2)...
      - contradiction (proj2 claim1)...
      - contradiction (proj2 claim1). apply lemma1; [exact (proj1 claim1) | exact (proj1 claim2)].
      - contradiction (proj2 claim1)...
      - contradiction (proj2 claim1). apply lemma1; [exact (proj1 claim2) | exact (proj1 claim1)].
    }
    assert (lemma5 : forall xs1 : list A, forall xs2 : list A, lex_compare xs1 xs2 = Eq <-> lex_compare xs2 xs1 = Eq).
    { induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl... split... split...
      assert (claim1 := compare_spec x1 x2); assert (claim2 := compare_spec x2 x1); assert (claim3 := IH xs2).
      destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x1) eqn: H_compare_result2...
      - contradiction (proj2 claim2)...
      - contradiction (proj2 claim2)...
      - contradiction (proj2 claim1)...
      - split...
      - contradiction (proj2 claim1)...
      - split...
    }
    assert (lemma6 : forall xs1 : list A, forall xs2 : list A, lex_compare xs1 xs2 = Gt <-> lex_compare xs2 xs1 = Lt) by firstorder.
    intros lhs rhs; destruct (lex_compare lhs rhs) eqn: H_compare_result; now firstorder.
  Qed.

  Local Polymorphic Instance lex_le_PartialOrder :
    PartialOrder lex_eq lex_le.
  Proof with discriminate || eauto with *.
    intros xs1 xs2; cbn. unfold flip, lex_eq, lex_le.
    assert (claim1 := lex_le_flip_spec xs1 xs2).
    destruct (lex_compare xs1 xs2) eqn: H_compare_result.
    - split...
    - split... intros [? [H_false | H_false]].
      all: rewrite H_false in claim1...
    - split... intros [[? | ?] ?]...
  Qed.

  Local Polymorphic Instance list_isPoset_wrt_lex_le : isPoset (list A) :=
    { leProp := lex_le
    ; Poset_requiresSetoid := list_isSetoid_wrt_lex_eq
    ; Poset_requiresPreOrder := lex_le_PreOrder
    ; Poset_requiresPartialOrder := lex_le_PartialOrder
    }
  .

  End LEXICOGRAPHICAL_ORDER.

End BasicPosetTheory.

Module MyEnsembleNova.

  Import MyUtilities MyEnsemble.

  Definition full {A : Type} : ensemble A :=
    fun x : A =>
    x = x
  .

  Global Hint Unfold full : my_hints.

  Lemma in_full_iff {A : Type} :
    forall x : A,
    member x full <-> True.
  Proof with firstorder.
    unfold full...
  Qed.

  Definition insert {A : Type} : A -> ensemble A -> ensemble A :=
    fun x1 : A =>
    fun xs2 : ensemble A =>
    xs2 \cup \left\{ x1 \right\}
  .

  Global Hint Unfold insert : my_hints.

  Lemma in_insert_iff {A : Type} :
    forall x : A,
    forall x1 : A,
    forall xs2 : ensemble A,
    member x (insert x1 xs2) <-> x = x1 \/ member x xs2.
  Proof with firstorder.
    unfold insert.
    intros x x1 xs2.
    rewrite in_union_iff, in_singleton_iff...
  Qed.

  Definition difference {A : Type} : ensemble A -> ensemble A -> ensemble A :=
    fun xs1 : ensemble A =>
    fun xs2 : ensemble A =>
    xs1 \cap xs2^c
  .

  Global Hint Unfold difference : my_hints.

  Lemma in_difference_iff {A : Type} :
    forall x : A,
    forall xs1 : ensemble A,
    forall xs2 : ensemble A,
    member x (difference xs1 xs2) <-> member x xs1 /\ ~ member x xs2.
  Proof with firstorder.
    unfold difference.
    intros x xs1 xs2.
    rewrite in_intersection_iff, in_complement_iff...
  Qed.

  Definition delete {A : Type} : A -> ensemble A -> ensemble A :=
    fun x1 : A =>
    fun xs2 : ensemble A =>
    xs2 \cap \left\{ x1 \right\}^c
  .

  Global Hint Unfold delete : my_hints.

  Lemma in_delete_iff {A : Type} :
    forall x : A,
    forall x1 : A,
    forall xs2 : ensemble A,
    member x (delete x1 xs2) <-> member x xs2 /\ x <> x1.
  Proof with firstorder.
    unfold delete.
    intros x x1 xs2.
    rewrite in_intersection_iff, in_complement_iff, in_singleton_iff...
  Qed.

  Section ExtraFacts.

  Context {A : Type}.

  Lemma in_append_elim1 :
    forall xs1 : list A,
    forall xs2 : list A,
    forall X : ensemble A,
    (forall x : A, In x xs1 -> member x X) ->
    (forall x : A, In x xs2 -> member x X) ->
    forall x : A,
    In x (xs1 ++ xs2) ->
    member x X.
  Proof with firstorder.
    intros xs1 xs2 X H_incl1 H_incl2 x.
    rewrite in_app_iff...
  Qed.

  Lemma in_append_iff :
    forall xs1 : list A,
    forall xs2 : list A,
    forall X1 : ensemble A,
    forall X2 : ensemble A,
    (forall x : A, In x xs1 <-> member x X1) ->
    (forall x : A, In x xs2 <-> member x X2) ->
    forall x : A,
    In x (xs1 ++ xs2) <-> member x (union X1 X2).
  Proof with firstorder.
    intros xs1 xs2 X1 X2 H_equiv1 H_equiv2 x.
    rewrite in_app_iff, in_union_iff...
  Qed.

  Hypothesis A_eq_dec : forall x1 : A, forall x2 : A, {x1 = x2} + {x1 <> x2}.

  Lemma in_remove_elim1 :
    forall x0 : A,
    forall xs1 : list A,
    forall X2 : ensemble A,
    (forall x : A, In x xs1 -> member x (insert x0 X2)) ->
    forall x : A,
    In x (remove A_eq_dec x0 xs1) ->
    member x X2.
  Proof with firstorder.
    intros x0 xs1 X2 H_incl x H.
    destruct (in_remove A_eq_dec xs1 x x0 H) as [H0 H1].
    assert (H2 := H_incl x H0).
    apply in_insert_iff in H2...
  Qed.

  Lemma in_remove_iff :
    forall x1 : A,
    forall xs2 : list A,
    forall X2 : ensemble A,
    (forall x : A, In x xs2 <-> member x X2) ->
    forall x : A,
    In x (remove A_eq_dec x1 xs2) <-> member x (delete x1 X2).
  Proof with firstorder.
    intros x1 xs2 X2 H x.
    assert (H0 := in_remove A_eq_dec xs2 x x1).
    assert (H1 := in_in_remove A_eq_dec xs2).
    rewrite in_delete_iff...
  Qed.

  End ExtraFacts.

  Lemma insert_intro_isSubsetOf {A : Type} :
    forall x0 : A,
    forall X1 : ensemble A,
    forall X2 : ensemble A,
    isSubsetOf X1 X2 ->
    isSubsetOf (insert x0 X1) (insert x0 X2).
  Proof with firstorder.
    unfold isSubsetOf, insert.
    intros x0 X1 X2 H_incl x.
    do 2 rewrite in_union_iff, in_singleton_iff...
  Qed.

  Global Hint Resolve insert_intro_isSubsetOf : my_hints.

  Lemma isSubsetOf_intro_singleton {A : Type} :
    forall x : A,
    forall X : ensemble A,
    x \in X ->
    \left\{ x \right\} \subseteq X.
  Proof with firstorder.
    intros x X H x0.
    rewrite in_singleton_iff.
    intros Heq.
    subst...
  Qed.

  Global Hint Resolve isSubsetOf_intro_singleton : my_hints.

  Lemma isSubsetOf_intro_empty {A : Type} :
    forall X : ensemble A,
    \emptyset \subseteq X.
  Proof with firstorder.
    intros X x.
    rewrite in_empty_iff...
  Qed.

  Global Hint Resolve isSubsetOf_intro_empty : my_hints.

End MyEnsembleNova.

Module BasicTopology.

  Import MyUtilities BasicSetoidTheory MyEnsemble MyEnsembleNova.

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
    ; open_ext_eq :
      forall X1 : ensemble A,
      isOpen X1 ->
      forall X2 : ensemble A,
      X1 == X2 ->
      isOpen X2
    }
  .

  Global Hint Resolve open_full open_unions open_intersection : my_hints.

  Lemma open_emptyset {A : Type} `{A_isTopologicalSpace : isTopologicalSpace A} :
    isOpen \emptyset.
  Proof with try now firstorder; eauto with *.
    assert (claim1 : isOpen (\bigcup \emptyset)).
    { apply open_unions.
      intros X X_in.
      apply in_empty_iff in X_in...
    }
    apply (open_ext_eq (\bigcup \emptyset) claim1).
    enough (it_is_sufficient_to_show : forall a : A, member a (\bigcup \emptyset) <-> member a \emptyset) by exact it_is_sufficient_to_show.
    assert (claim2 := @in_empty_iff (ensemble A)).
    intros a.
    rewrite in_empty_iff, in_unions_iff...
  Qed.

  Definition isContinuousMap {A : Type} {B : Type} `{A_isTopologicalSpace : isTopologicalSpace A} `{B_isTopologicalSpace : isTopologicalSpace B} : (A -> B) -> Prop :=
    fun f : A -> B =>
    forall ys : ensemble B,
    isOpen ys ->
    isOpen (preimage f ys)
  .

  Global Hint Unfold isContinuousMap : my_hints.

  Global Notation " A '~>' B " := (@sig (A -> B) isContinuousMap) (at level 100, right associativity) : type_scope.

  Section BuildSubspaceTopology. (* Reference: "https://github.com/Abastro/Coq-Practice/blob/aeca5f68c521fe0bb07f5e12c67156060c402799/src/Topology.v" *)

  Context (A : Type) (P : A -> Prop) (A_requiresTopologicalSpace : isTopologicalSpace A).

  Let filter_P : Type :=
    @sig A P
  .

  Let is_subset_rep : ensemble filter_P-> ensemble A -> Prop :=
    fun O_sub : ensemble filter_P =>
    fun O : ensemble A =>
    forall x : filter_P,
    member (proj1_sig x) O <-> member x O_sub
  .

  Definition isOpen_SubspaceTopology : ensemble filter_P -> Prop :=
    fun O_sub : ensemble filter_P =>
    exists O : ensemble A, isOpen O /\ is_subset_rep O_sub O
  .

  Local Hint Unfold isOpen_SubspaceTopology : core.

  Lemma open_full_SubspaceTopolgy :
    isOpen_SubspaceTopology full.
  Proof with try now firstorder; eauto with *.
    exists full...
  Qed.

  Lemma open_unions_SubspaceTopology :
    forall Xs : ensemble (ensemble filter_P),
    (forall X : ensemble filter_P, member X Xs -> isOpen_SubspaceTopology X) ->
    isOpen_SubspaceTopology (unions Xs).
  Proof with try now firstorder; eauto with *.
    intros Xs H.
    exists (unions (fun O : ensemble A => exists O_sub : ensemble filter_P, member O_sub Xs /\ is_subset_rep O_sub O /\ isOpen O)).
    split; [apply open_unions | intros x; do 2 rewrite in_unions_iff]...
  Qed.

  Lemma open_intersection_SubspaceTopology :
    forall X1 : ensemble filter_P,
    forall X2 : ensemble filter_P,
    isOpen_SubspaceTopology X1 ->
    isOpen_SubspaceTopology X2 ->
    isOpen_SubspaceTopology (intersection X1 X2).
  Proof with try now firstorder; eauto with *.
    intros X1 X2 [O1 [H H0]] [O2 [H1 H2]].
    exists (intersection O1 O2).
    split; [apply open_intersection | intros x; do 2 rewrite in_intersection_iff]...
  Qed.

  Lemma open_ext_eq_SubspaceTopology :
    forall X1 : ensemble filter_P,
    isOpen_SubspaceTopology X1 ->
    forall X2 : ensemble filter_P,
    X1 == X2 ->
    isOpen_SubspaceTopology X2.
  Proof with try now firstorder; eauto with *.
    intros X1 [O [O_isOpen O_corresponds_to_X1]] X2 H_X1_eq_X2...
  Qed.

  End BuildSubspaceTopology.

  Local Instance SubspaceTopology {A : Type} (P : A -> Prop) (A_requiresTopologicalSpace : isTopologicalSpace A) : isTopologicalSpace {x : A | P x} :=
    { isOpen := isOpen_SubspaceTopology A P A_requiresTopologicalSpace
    ; open_full := open_full_SubspaceTopolgy A P A_requiresTopologicalSpace
    ; open_unions := open_unions_SubspaceTopology A P A_requiresTopologicalSpace
    ; open_intersection := open_intersection_SubspaceTopology A P A_requiresTopologicalSpace
    ; open_ext_eq := open_ext_eq_SubspaceTopology A P A_requiresTopologicalSpace
    }
  .

End BasicTopology.
