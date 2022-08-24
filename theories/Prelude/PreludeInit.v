Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.

Module Khan. (* Reference: "https://github.com/snu-sf/sflib/blob/master/sflib.v" *)

(** "\S1" *)

  Global Notation compose := compose.
  Global Notation id := id.
  Global Notation " 'id_{'  A  '}' " := (@id A) (A at level 100, at level 0, no associativity) : program_scope.

(** "\S2" *)

  Create HintDb khan_hints.
  Global Hint Unfold flip relation_conjunction impl : khan_hints.

(** "\S3" *)

  Polymorphic Definition REFERENCE_HOLDER {STATEMENT_Type : Type} (REFERENCED_STATEMENT : unit -> STATEMENT_Type) : STATEMENT_Type := REFERENCED_STATEMENT tt.

  Global Notation " '<<' STATEMENT_REFERENCE ':' STATEMENT '>>' " := (REFERENCE_HOLDER (fun STATEMENT_REFERENCE => STATEMENT)) (STATEMENT_REFERENCE name, STATEMENT at level 200, at level 70, no associativity) : type_scope.
  Global Notation " '<<' STATEMENT '>>' " := (<< _ : STATEMENT >>) (STATEMENT at level 200, at level 0, no associativity) : type_scope.
  Global Notation " '⟪' STATEMENT_REFERENCE ':' STATEMENT '⟫' " := (REFERENCE_HOLDER (fun STATEMENT_REFERENCE : unit => match STATEMENT_REFERENCE with tt => STATEMENT end)) (STATEMENT_REFERENCE name, STATEMENT at level 200, at level 0, no associativity) : type_scope.

  Global Tactic Notation "rednw" "in" hyp( H ) :=
    (match type of H with REFERENCE_HOLDER _ -> _ => unfold REFERENCE_HOLDER at 1 in H | _ => idtac end);
    (match type of H with _ -> REFERENCE_HOLDER _ => red in H | REFERENCE_HOLDER _ => red in H | _ => idtac end)
  .

  Global Tactic Notation "desnw'" "in" hyp( H ) :=
    match type of H with
    | REFERENCE_HOLDER (fun z => _) =>
      let H' := fresh z in
      rename H into H'; red in H'
    | ?P /\ ?Q =>
      let x' := match P with REFERENCE_HOLDER (fun z => _) => fresh z | _ => H end in
      let y' := match Q with REFERENCE_HOLDER (fun z => _) => fresh z | _ => fresh H end in
      destruct H as [x' y']; rednw in x'; rednw in y'
    | ?P \/ ?Q =>
      let x' := match P with REFERENCE_HOLDER (fun z => _) => fresh z | _ => H end in
      let y' := match Q with REFERENCE_HOLDER (fun z => _) => fresh z | _ => H end in
      destruct H as [x' | y']; [rednw in x' | rednw in y']
    | ?P <-> ?Q =>
      let x' := match P with REFERENCE_HOLDER (fun z => _) => fresh z | _ => H end in
      let y' := match Q with REFERENCE_HOLDER (fun z => _) => fresh z | _ => fresh H end in
      destruct H as [x' y']; rednw in x'; rednw in y'
    end
  .

  Ltac unnw := unfold REFERENCE_HOLDER in *.
  Ltac desnw' := repeat (match goal with [ H : _ |- _ ] => desnw' in H end).
  Ltac desnw := repeat
    match goal with
    | [ H : exists x, ?P |- _ ] => let x' := fresh x in destruct H as [x' H]
    | [ H : _ |- _ ] => desnw' in H
    end
  .

(** "\S4" *)

  Global Tactic Notation "remove_eqn_if_trivial" hyp( H ) :=
    match type of H with
    | ?x = ?y =>
      tryif has_evar x then idtac else
      tryif has_evar y then idtac else
      tryif unify x y then clear H else idtac
    end
  .

  Ltac ii := repeat intro.
  Ltac iis := ii; autounfold with khan_hints; try esplit.
  Ltac iiss := (repeat iis); cbn in *; desnw.
  Ltac des := repeat
    match goal with
    | [ H : ?x = ?y |- _ ] => first [subst x | subst y | remove_eqn_if_trivial H]
    | [ H : ?P /\ ?Q |- _ ] => destruct H
    | [ H : ?P \/ ?Q |- _ ] => destruct H
    | [ H : ?P <-> ?Q |- _ ] => destruct H
    | [ H : exists x, ?P |- _ ] => let x' := fresh x in destruct H as [x' H]
    | [ H : False |- _ ] => contradiction (H)
    | [ H : True |- _ ] => clear H
    | [ |- let x : ?A := ?t in ?B ] => let x' := fresh x in intros x'
    | [ |- forall x : ?A, ?B ] => let x' := fresh x in intros x'
    | [ |- ?P /\ ?Q ] => split
    | [ |- ?P <-> ?Q ] => split; intro
    end
  .

(** "\S5" *)

  Lemma MODUS_PONENS {HYPOTHESIS : Prop} {CONCLUSION : Prop}
    (ASSUMPTION : HYPOTHESIS)
    (PREMISE : HYPOTHESIS -> CONCLUSION)
    : CONCLUSION.
  Proof. exact (PREMISE ASSUMPTION). Defined.

  Global Tactic Notation "exploit" uconstr( PRF ) "as" simple_intropattern( PAT ) := eapply MODUS_PONENS; [eapply PRF | intros PAT].
  Global Tactic Notation "exploit" uconstr( PRF ) := eapply MODUS_PONENS; [eapply PRF | ].

(** "\S6" *)

  Global Tactic Notation "memo" uconstr( PRF ) "as" ident( REF ) "into" uconstr( PROP ) := refine ((fun REF : PROP => _)(PRF)).
  Global Tactic Notation "memo" uconstr( PRF ) "as" ident( REF ) := refine ((fun REF => _)(PRF)).
  Global Tactic Notation "keep" uconstr( PRF ) "as" ident( REF ) "into" uconstr( PROP ) := refine (let REF : PROP := PRF in _).
  Global Tactic Notation "keep" uconstr( PRF ) "as" ident( REF ) := refine (let REF := PRF in _).

  Ltac intro_pattern_revert := let x := fresh in intro x; pattern x; revert x.

End Khan.

Export Khan.

Module Cat.

  Set Primitive Projections.

  Polymorphic Class isCategory@{objs_lv hom_lv} : Type@{max(objs_lv + 1, hom_lv + 1)} :=
    { objs : Type@{objs_lv}
    ; hom (dom : objs) (cod : objs) : Type@{hom_lv}
    ; compose {obj_l : objs} {obj : objs} {obj_r : objs} (arr_r : hom obj obj_r) (arr_l : hom obj_l obj) : hom obj_l obj_r
    ; id {obj : objs} : hom obj obj
    }
  .

  Unset Primitive Projections.

  Polymorphic Definition Functor_t (src : isCategory) (tgt : isCategory) : Type := src.(objs) -> tgt.(objs).

  Global Infix " -----> " := Functor_t (at level 100, no associativity) : type_scope.

  Section BasicConceptsOfCategoryTheory.

  Context {src : isCategory} {tgt : isCategory}.

  Class isCovariantFunctor (F : src -----> tgt) : Type :=
    { fmap {dom : src.(objs)} {cod : src.(objs)} (arr : src.(hom) dom cod) : tgt.(hom) (F dom) (F cod) }
  .

  Class isContravariantFunctor (F : src -----> tgt) : Type :=
    { contramap {dom : src.(objs)} {cod : src.(objs)} (arr : src.(hom) cod dom) : tgt.(hom) (F dom) (F cod) }
  .

  Class isNaturalTransformation (F_from : src -----> tgt) (F_to : src -----> tgt) : Type :=
    component (obj : src.(objs)) : tgt.(hom) (F_from obj) (F_to obj)
  .

  End BasicConceptsOfCategoryTheory.

  Global Infix " =====> " := isNaturalTransformation (at level 100, no associativity) : type_scope.

End Cat.

Export Cat.

Module Hask.

  Polymorphic Definition t@{lv} : Type@{lv + 1} := Type@{lv}.

  Polymorphic Definition arrow@{dom_lv cod_lv arrow_lv | dom_lv <= arrow_lv, cod_lv <= arrow_lv} (dom : Hask.t@{dom_lv}) (cod : Hask.t@{cod_lv}) : Hask.t@{arrow_lv} := dom -> cod.

  Global Delimit Scope type_scope with t.
  Global Delimit Scope type_scope with arrow.

  Global Polymorphic Instance cat : isCategory :=
    { objs := Hask.t
    ; hom := Hask.arrow
    ; compose (A : Hask.t) (B : Hask.t) (C : Hask.t) := Khan.compose (A := A) (B := B) (C := C)
    ; id (A : Hask.t) := Khan.id (A := A)
    }
  .

End Hask.

Module PreludeInit_MAIN.

  Global Open Scope program_scope.

(** "1. Setoid and Poset" *)

  Class isSetoid (A : Type) : Type :=
    { eqProp (lhs : A) (rhs : A) : Prop
    ; eqProp_Equivalence :> @Equivalence A eqProp
    }
  .

  Global Infix " == " := eqProp (at level 70, no associativity) : type_scope.

  Class isPoset (A : Type) : Type :=
    { leProp (lhs : A) (rhs : A) : Prop
    ; Poset_requiresSetoid :> isSetoid A
    ; leProp_PreOrder :> @PreOrder A leProp
    ; leProp_PartialOrder :> @PartialOrder A eqProp (@eqProp_Equivalence A Poset_requiresSetoid) leProp leProp_PreOrder
    }
  .

  Global Infix " =< " := leProp (at level 70, no associativity) : type_scope.

  Class isSetoid1 (F : Type -> Type) : Type :=
    liftSetoid1 (X : Type) (X_isSetoid : isSetoid X) :> isSetoid (F X)
  .

(** "2. Accessories" *)

  Global Notation " E '~~>' F " := (forall X : Type, E X -> F X) (at level 100, no associativity) : type_scope.
  Global Notation isFunctor := (isCovariantFunctor (src := Hask.cat) (tgt := Hask.cat)).

  Class isMonad (M : Hask.cat -----> Hask.cat) : Type :=
    { pure {A : Hask.t} (x : A) : M A
    ; bind {A : Hask.t} {B : Hask.t} (m : M A) (k : A -> M B) : M B
    }
  .

  Global Infix " >>= " := bind (at level 90, left associativity) : program_scope.

  Section SETOID_ACCESSORIES.

  Context {A : Type} {requiresSetoid : isSetoid A}.

  Lemma eqProp_Reflexive (x : A)
    : x == x.
  Proof. eapply Equivalence_Reflexive; eauto. Qed.

  Lemma eqProp_Symmetric (x : A) (y : A)
    (x_eq_y : x == y)
    : y == x.
  Proof. eapply Equivalence_Symmetric; eauto. Qed.

  Lemma eqProp_Transitive (x : A) (y : A) (z : A)
    (x_eq_y : x == y)
    (y_eq_z : y == z)
    : x == z.
  Proof. eapply Equivalence_Transitive; eauto. Qed.

  End SETOID_ACCESSORIES.

  Global Hint Resolve eqProp_Reflexive eqProp_Symmetric eqProp_Transitive : khan_hints.

  Section POSET_ACCESSORIES.

  Context {A : Type} {requiresPoset : isPoset A}.

  Lemma leProp_Reflexive (x : A)
    : x =< x.
  Proof. eapply PreOrder_Reflexive; eauto. Qed.

  Lemma leProp_Transitive (x : A) (y : A) (z : A)
    (x_le_y : x =< y)
    (y_le_z : y =< z)
    : x =< z.
  Proof. eapply PreOrder_Transitive; eauto. Qed.

  Lemma eqProp_implies_leProp (x : A) (y : A)
    (x_eq_y : x == y)
    : x =< y.
  Proof. now rewrite x_eq_y. Qed.

  Lemma leProp_Antisymmetric (x : A) (y : A)
    (x_le_y : x =< y)
    (y_le_x : y =< x)
    : x == y.
  Proof. now eapply partial_order_equivalence. Qed.

  End POSET_ACCESSORIES.

  Global Hint Resolve leProp_Reflexive eqProp_implies_leProp leProp_Antisymmetric : khan_hints.

(** "3. Basic Instances" *)

  Section ImplFor_eq.

  Local Instance theFinestSetoidOf (A : Type) : isSetoid A :=
    { eqProp := @eq A
    ; eqProp_Equivalence := eq_equivalence
    }
  .

  End ImplFor_eq.

  Section ImplFor_option.

  Global Instance option_isFunctor : isFunctor option :=
    { fmap {A : Hask.t} {B : Hask.t} := option_map (A := A) (B := B) }
  .

  Definition maybe {A : Hask.t} {B : Hask.t} (runNOTHING : B) (runJUST : A -> B) (it : option A) : B :=
    match it with
    | Some x => runJUST x
    | None => runNOTHING
    end
  .

  Global Instance option_isMonad : isMonad option :=
    { pure {A : Hask.t} (x : A) := Some x
    ; bind {A : Hask.t} {B : Hask.t} (m : option A) (k : A -> option B) := maybe None k m
    }
  .

  Definition option_liftProp2 {A : Type} (R : A -> A -> Prop) (lhs : option A) (rhs : option A) : Prop :=
    match lhs, rhs with
    | Some x, Some y => R x y
    | None, None => True
    | _, _ => False
    end
  .

  Lemma option_liftProp2_liftsEquivalence {A : Type} (R : A -> A -> Prop)
    (R_Equivalence : Equivalence R)
    : Equivalence (option_liftProp2 R).
  Proof with try now firstorder using Equivalence.
    unfold option_liftProp2. split.
    - intros [x | ]...
    - intros [x | ] [y | ]...
    - intros [x | ] [y | ] [z | ]...
  Qed.

  Global Program Instance option_isSetoid {A : Type} (requiresSetoid : isSetoid A) : isSetoid (option A) :=
    { eqProp := option_liftProp2 eqProp
    ; eqProp_Equivalence := option_liftProp2_liftsEquivalence eqProp (@eqProp_Equivalence A requiresSetoid)
    }
  .

  End ImplFor_option.

  Section ImplFor_list.

  Import ListNotations.

  Global Instance list_isMonad : isMonad list :=
    { pure {A : Hask.t} (x : A) := [x]
    ; bind {A : Hask.t} {B : Hask.t} (xs : list A) (k : A -> list B) := concat (map k xs)
    }
  .

  End ImplFor_list.

  Section ImplFor_image.

  Definition binary_relation_on_image@{dom_lv cod_lv} {dom : Type@{dom_lv}} {cod : Type@{cod_lv}} (bin_rel : cod -> cod -> Prop) (f : dom -> cod) (lhs : dom) (rhs : dom) : Prop := bin_rel (f lhs) (f rhs).

  Local Instance relation_on_image_liftsEquivalence {dom : Type} {cod : Type} {eq_cod : cod -> cod -> Prop} (f : dom -> cod)
    (requiresEquivalence : Equivalence eq_cod)
    : Equivalence (binary_relation_on_image eq_cod f).
  Proof.
    constructor.
    - intros x1. exact (Equivalence_Reflexive (f x1)).
    - intros x1 x2 H_1EQ2. exact (Equivalence_Symmetric (f x1) (f x2) H_1EQ2).
    - intros x1 x2 x3 H_1EQ2 H_2EQ3. exact (Equivalence_Transitive (f x1) (f x2) (f x3) H_1EQ2 H_2EQ3).
  Defined.

  Local Instance relation_on_image_liftsPreOrder {dom : Type} {cod : Type} {le_cod : cod -> cod -> Prop} (f : dom -> cod)
    (requiresPreOrder : PreOrder le_cod)
    : PreOrder (binary_relation_on_image le_cod f).
  Proof.
    constructor.
    - intros x1. exact (PreOrder_Reflexive (f x1)).
    - intros x1 x2 x3 H_1LE2 H_2LE3. exact (PreOrder_Transitive (f x1) (f x2) (f x3) H_1LE2 H_2LE3).
  Defined.

  Local Instance relation_on_image_liftsPartialOrder {dom : Type} {cod : Type} {eq_cod : cod -> cod -> Prop} {le_cod : cod -> cod -> Prop} (f : dom -> cod)
    {requiresEquivalence : Equivalence eq_cod}
    {requiresPreOrder : PreOrder le_cod}
    (requiresPartialOrder : PartialOrder eq_cod le_cod)
    : PartialOrder (binary_relation_on_image eq_cod f) (binary_relation_on_image le_cod f).
  Proof.
    intros x1 x2. constructor.
    - intros H_EQ. constructor.
      + exact (proj1 (proj1 (partial_order_equivalence (f x1) (f x2)) H_EQ)).
      + exact (proj2 (proj1 (partial_order_equivalence (f x1) (f x2)) H_EQ)).
    - intros H_EQ. apply (proj2 (partial_order_equivalence (f x1) (f x2))). constructor.
      + exact (proj1 H_EQ).
      + exact (proj2 H_EQ).
  Defined.

  Context {dom : Hask.t} {cod : Hask.t}.

  Definition im_eqProp {cod_isSetoid : isSetoid cod} (f : Hask.arrow dom cod) (lhs : dom) (rhs : dom) : Prop := binary_relation_on_image eqProp f lhs rhs.

  Definition im_leProp {cod_isPoset : isPoset cod} (f : Hask.arrow dom cod) (lhs : dom) (rhs : dom) : Prop := binary_relation_on_image leProp f lhs rhs.

  Variable f : Hask.arrow dom cod.

  Local Instance equivalence_relation_on_image
    (cod_isSetoid : isSetoid cod)
    : Equivalence (im_eqProp f).
  Proof. exact (relation_on_image_liftsEquivalence f eqProp_Equivalence). Defined.

  Local Instance preorder_relation_on_image
    (cod_isPoset : isPoset cod)
    : PreOrder (im_leProp f).
  Proof. exact (relation_on_image_liftsPreOrder f leProp_PreOrder). Defined.

  Local Instance partialorder_relation_on_image
    (cod_isPoset : isPoset cod)
    : PartialOrder (im_eqProp f) (im_leProp f).
  Proof. exact (relation_on_image_liftsPartialOrder f leProp_PartialOrder). Defined.

  End ImplFor_image.

  Global Instance subSetoid (A : Hask.t) {requiresSetoid : isSetoid A} {P : A -> Prop} : isSetoid (@sig A P) :=
    { eqProp (lhs : @sig A P) (rhs : @sig A P) := proj1_sig lhs == proj1_sig rhs
    ; eqProp_Equivalence := equivalence_relation_on_image (@proj1_sig A P) requiresSetoid
    }
  .

  Global Instance subPoset (A : Hask.t) {requiresPoset : isPoset A} {P : A -> Prop} : isPoset (@sig A P) :=
    { leProp (lhs : @sig A P) (rhs : @sig A P) := proj1_sig lhs =< proj1_sig rhs
    ; Poset_requiresSetoid := subSetoid A
    ; leProp_PreOrder := preorder_relation_on_image (@proj1_sig A P) requiresPoset
    ; leProp_PartialOrder := partialorder_relation_on_image (@proj1_sig A P) requiresPoset
    }
  .

  Section ImplFor_arrow.

  Variable dom : Hask.t.

  Variable cod : Hask.t.

  Definition arrow_eqProp {cod_isSetoid : isSetoid cod} (lhs : Hask.arrow dom cod) (rhs : Hask.arrow dom cod) : Prop :=
    forall x : dom, lhs x == rhs x
  .

  Local Instance arrow_eqProp_Equivalence
    (cod_isSetoid : isSetoid cod)
    : Equivalence arrow_eqProp.
  Proof.
    split.
    - intros f1 x. exact (Equivalence_Reflexive (f1 x)).
    - intros f1 f2 H_1EQ2 x. exact (Equivalence_Symmetric (f1 x) (f2 x) (H_1EQ2 x)).
    - intros f1 f2 f3 H_1EQ2 H_2EQ3 x. exact (Equivalence_Transitive (f1 x) (f2 x) (f3 x) (H_1EQ2 x) (H_2EQ3 x)).
  Defined.

  Global Instance arrow_isSetoid {cod_isSetoid : isSetoid cod} : isSetoid (Hask.arrow dom cod) :=
    { eqProp := arrow_eqProp (cod_isSetoid := cod_isSetoid)
    ; eqProp_Equivalence := arrow_eqProp_Equivalence cod_isSetoid
    }
  .

  Definition arrow_leProp {cod_isPoset : isPoset cod} (lhs : Hask.arrow dom cod) (rhs : Hask.arrow dom cod) : Prop :=
    forall x : dom, lhs x =< rhs x
  .

  Local Instance arrow_leProp_PreOrder
    (cod_isPoset : isPoset cod)
    : PreOrder arrow_leProp.
  Proof.
    constructor.
    - intros f1 x. exact (PreOrder_Reflexive (f1 x)).
    - intros f1 f2 f3 H_1LE2 H_2LE3 x. exact (PreOrder_Transitive (f1 x) (f2 x) (f3 x) (H_1LE2 x) (H_2LE3 x)).
  Defined.

  Local Instance arrow_leProp_PartialOrder
    (cod_isPoset : isPoset cod)
    : PartialOrder arrow_eqProp arrow_leProp.
  Proof.
    intros f1 f2. constructor.
    - intros H_EQ. constructor.
      + intros x. exact (proj1 (proj1 (partial_order_equivalence (f1 x) (f2 x)) (H_EQ x))).
      + intros x. exact (proj2 (proj1 (partial_order_equivalence (f1 x) (f2 x)) (H_EQ x))).
    - intros H_EQ x. apply (proj2 (partial_order_equivalence (f1 x) (f2 x))). constructor.
      + exact (proj1 H_EQ x).
      + exact (proj2 H_EQ x).
  Defined.

  Local Instance arrow_isPoset {cod_isPoset : isPoset cod} : isPoset (Hask.arrow dom cod) :=
    { leProp := arrow_leProp
    ; Poset_requiresSetoid := arrow_isSetoid
    ; leProp_PreOrder := arrow_leProp_PreOrder cod_isPoset
    ; leProp_PartialOrder := arrow_leProp_PartialOrder cod_isPoset
    }
  .

  End ImplFor_arrow.

  Global Arguments arrow_eqProp {dom} {cod} {cod_isSetoid}.
  Global Arguments arrow_leProp {dom} {cod} {cod_isPoset}.
  Global Arguments arrow_isSetoid (dom) (cod) {cod_isSetoid}.
  Global Arguments arrow_isPoset (dom) (cod) {cod_isPoset}.

  Section ImplFor_ensemble.

  Global Instance Prop_isSetoid : isSetoid Prop :=
    { eqProp := iff
    ; eqProp_Equivalence := iff_equivalence
    }
  .

  Local Instance impl_PreOrder
    : PreOrder impl.
  Proof. iiss; eauto. Qed.

  Local Instance impl_PartialOrder
    : PartialOrder iff impl.
  Proof. iiss; eauto. Qed.

  Local Instance Prop_isPoset : isPoset Prop :=
    { leProp := impl
    ; Poset_requiresSetoid := Prop_isSetoid
    ; leProp_PreOrder := impl_PreOrder
    ; leProp_PartialOrder := impl_PartialOrder
    }
  .

  Polymorphic Definition ensemble@{lv} : Type@{lv} -> Type@{lv} := fun X : Hask.t@{lv} => Hask.arrow@{lv lv lv} X Prop.

  Definition member {A : Hask.t} (x : A) (xs : ensemble A) : Prop := xs x.

  Global Add Parametric Morphism (A : Type) :
    (@member A) with signature (eq ==> eqProp ==> iff)
    as member_compatWith_eqProp_on_2nd_arg.
  Proof. intros z X Y H_EQ. exact (H_EQ z). Qed.

  Definition isSameSetAs {A : Type} (lhs : ensemble A) (rhs : ensemble A) : Prop :=
    forall x : A, member x lhs <-> member x rhs
  .

  Global Instance ensemble_isSetoid (A : Type) : isSetoid (ensemble A) :=
    { eqProp := @isSameSetAs A
    ; eqProp_Equivalence := @arrow_eqProp_Equivalence A Prop Prop_isSetoid
    }
  .

  Definition isSubsetOf {A : Type} (lhs : ensemble A) (rhs : ensemble A) : Prop :=
    forall x : A, member x lhs -> member x rhs
  .

  Global Instance ensemble_isPoset (A : Type) : isPoset (ensemble A) :=
    { leProp := @isSubsetOf A
    ; Poset_requiresSetoid := ensemble_isSetoid A
    ; leProp_PreOrder := arrow_leProp_PreOrder A Prop Prop_isPoset
    ; leProp_PartialOrder := arrow_leProp_PartialOrder A Prop Prop_isPoset
    }
  .

  Global Instance isSubsetOf_PreOrder (A : Type) : PreOrder (@isSubsetOf A) :=
    @leProp_PreOrder (ensemble A) (ensemble_isPoset A)
  .

  Global Instance isSubsetOf_PartialOrder (A : Type) : PartialOrder eqProp (@isSubsetOf A) :=
    @leProp_PartialOrder (ensemble A) (ensemble_isPoset A)
  .

  End ImplFor_ensemble.

  Global Arguments ensemble (X)%type.
  Global Arguments isSameSetAs {A} (lhs) (rhs) : simpl never.
  Global Arguments isSubsetOf {A} (lhs) (rhs) : simpl never.

  Section ImplFor_pair.

  Variable fsts : Hask.t.

  Variable snds : Hask.t.

  Definition pair_eqProp {fsts_isSetoid : isSetoid fsts} {snds_isSetoid : isSetoid snds} (lhs : fsts * snds) (rhs : fsts * snds) : Prop :=
    fst lhs == fst rhs /\ snd lhs == snd rhs
  .

  Local Instance pair_eqProp_Equivalence
    (fsts_isSetoid : isSetoid fsts)
    (snds_isSetoid : isSetoid snds)
    : Equivalence pair_eqProp.
  Proof.
    constructor.
    - intros p1. constructor.
      + exact (Equivalence_Reflexive (fst p1)).
      + exact (Equivalence_Reflexive (snd p1)).
    - intros p1 p2 H_1EQ2. constructor.
      + exact (Equivalence_Symmetric (fst p1) (fst p2) (proj1 H_1EQ2)).
      + exact (Equivalence_Symmetric (snd p1) (snd p2) (proj2 H_1EQ2)).
    - intros p1 p2 p3 H_1EQ2 H_2EQ3. constructor.
      + exact (Equivalence_Transitive (fst p1) (fst p2) (fst p3) (proj1 H_1EQ2) (proj1 H_2EQ3)).
      + exact (Equivalence_Transitive (snd p1) (snd p2) (snd p3) (proj2 H_1EQ2) (proj2 H_2EQ3)).
  Defined.

  Global Instance pair_isSetoid {fsts_isSetoid : isSetoid fsts} {snds_isSetoid : isSetoid snds} : isSetoid (fsts * snds) :=
    { eqProp := pair_eqProp
    ; eqProp_Equivalence := pair_eqProp_Equivalence fsts_isSetoid snds_isSetoid
    }
  .

  Definition pair_leProp {fsts_isPoset : isPoset fsts} {snds_isPoset : isPoset snds} (lhs : fsts * snds) (rhs : fsts * snds) : Prop :=
    fst lhs =< fst rhs /\ snd lhs =< snd rhs
  .

  Local Instance pair_leProp_PreOrder
    (fsts_isPoset : isPoset fsts)
    (snds_isPoset : isPoset snds)
    : PreOrder pair_leProp.
  Proof.
    constructor.
    - intros p1. constructor.
      + exact (PreOrder_Reflexive (fst p1)).
      + exact (PreOrder_Reflexive (snd p1)).
    - intros p1 p2 p3 H_1LE2 H_2LE3. constructor.
      + exact (PreOrder_Transitive (fst p1) (fst p2) (fst p3) (proj1 H_1LE2) (proj1 H_2LE3)).
      + exact (PreOrder_Transitive (snd p1) (snd p2) (snd p3) (proj2 H_1LE2) (proj2 H_2LE3)).
  Defined.

  Local Instance pair_leProp_PartialOrder
    (fsts_isPoset : isPoset fsts)
    (snds_isPoset : isPoset snds)
    : PartialOrder pair_eqProp pair_leProp.
  Proof.
    intros p1 p2. constructor.
    - intros H_EQ. constructor.
      + constructor.
        { exact (proj1 (proj1 (partial_order_equivalence (fst p1) (fst p2)) (proj1 H_EQ))). }
        { exact (proj1 (proj1 (partial_order_equivalence (snd p1) (snd p2)) (proj2 H_EQ))). }
      + constructor.
        { exact (proj2 (proj1 (partial_order_equivalence (fst p1) (fst p2)) (proj1 H_EQ))). }
        { exact (proj2 (proj1 (partial_order_equivalence (snd p1) (snd p2)) (proj2 H_EQ))). }
    - intros H_EQ. constructor.
      + apply (proj2 (partial_order_equivalence (fst p1) (fst p2))). constructor.
        { exact (proj1 (proj1 H_EQ)). }
        { exact (proj1 (proj2 H_EQ)). }
      + apply (proj2 (partial_order_equivalence (snd p1) (snd p2))). constructor.
        { exact (proj2 (proj1 H_EQ)). }
        { exact (proj2 (proj2 H_EQ)). }
  Defined.

  Local Instance pair_isPoset {fsts_isPoset : isPoset fsts} {snds_isPoset : isPoset snds} : isPoset (fsts * snds) :=
    { leProp := pair_leProp
    ; Poset_requiresSetoid := pair_isSetoid
    ; leProp_PreOrder := pair_leProp_PreOrder fsts_isPoset snds_isPoset
    ; leProp_PartialOrder := pair_leProp_PartialOrder fsts_isPoset snds_isPoset
    }
  .

  End ImplFor_pair.

  Global Arguments pair_eqProp {fsts} {snds} {fsts_isSetoid} {snds_isSetoid}.
  Global Arguments pair_leProp {fsts} {snds} {fsts_isPoset} {snds_isPoset}.
  Global Arguments pair_isSetoid (fsts) (snds) {fsts_isSetoid} {snds_isSetoid}.
  Global Arguments pair_isPoset (fsts) (snds) {fsts_isPoset} {snds_isPoset}.

  Section ImplFor_kleisli.

  Variable M : Hask.cat -----> Hask.cat.

  Definition kleisli (dom : Hask.t) (cod : Hask.t) : Type := dom -> M cod.

  Variable requiresMonad : isMonad M.

  Definition kempty {obj : Hask.t} : kleisli obj obj := fun x => pure x.

  Definition kappend {obj_l : Hask.t} {obj : Hask.t} {obj_r : Hask.t} (k_r : kleisli obj obj_r) (k_l : kleisli obj_l obj) : kleisli obj_l obj_r := fun x_l => k_l x_l >>= fun x_r => k_r x_r.

  End ImplFor_kleisli.

  Global Arguments kleisli (M)%type (dom)%type (cod)%type.
  Global Arguments kempty {M} {requiresMonad} {obj}.
  Global Arguments kappend {M} {requiresMonad} {obj_l} {obj} {obj_r}.

  Global Infix " <=< " := kappend (at level 40, left associativity) : program_scope.

  Section TypeclassesForProgrammers.

  Definition fmap {F : Hask.cat -----> Hask.cat} {F_isFunctor : isFunctor F} {A : Hask.t} {B : Hask.t} : Hask.arrow A B -> Hask.arrow (F A) (F B) := Cat.fmap (F := F) (dom := A) (cod := B).

  Local Instance freeSetoidFromSetoid1 (F : Hask.cat -----> Hask.cat) (X : Hask.t) {requiresSetoid1 : isSetoid1 F} : isSetoid (F X) := liftSetoid1 X (theFinestSetoidOf X).

  Class LawsOfFunctor (F : Hask.cat -----> Hask.cat) {requiresSetoid1 : isSetoid1 F} {requiresFunctor : isFunctor F} : Prop :=
    { fmap_compatWith_compose {obj_l : Hask.t} {obj : Hask.t} {obj_r : Hask.t} (arr_r : obj -> obj_r) (arr_l : obj_l -> obj)
      : fmap (arr_r ∘ arr_l) == (fmap arr_r ∘ fmap arr_l)
    ; fmap_compatWith_id {obj : Hask.t}
      : fmap id_{ obj } == id_{ F obj }
    }
  .

  Class LawsOfMonad (M : Hask.cat -----> Hask.cat) {requiresSetoid1 : isSetoid1 M} {requiresMonad : isMonad M} : Prop :=
    { bind_assoc {A : Hask.t} {B : Hask.t} {C : Hask.t}
      (m0 : M A)
      (k1 : kleisli M A B)
      (k2 : kleisli M B C)
      : (m0 >>= k1 >>= k2) == (m0 >>= fun x1 => k1 x1 >>= k2)
    ; pure_left_id_bind {A : Hask.t} {B : Hask.t}
      (k : kleisli M A B)
      (x : A)
      : (pure x >>= k) == k x
    ; pure_right_id_bind {A : Hask.t}
      (m : M A)
      : (m >>= pure) == m
    ; bind_compatWith_eqProp_on_1st_arg {A : Hask.t} {B : Hask.t}
      (m1 : M A)
      (m2 : M A)
      (HYP_FST_ARG_EQ : m1 == m2)
      (k0 : kleisli M A B)
      : (m1 >>= k0) == (m2 >>= k0)
    ; bind_compatWith_eqProp_on_2nd_arg {A : Hask.t} {B : Hask.t}
      (k1 : kleisli M A B)
      (k2 : kleisli M A B)
      (HYP_SND_ARG_EQ : k1 == k2)
      (m0 : M A)
      : (m0 >>= k1) == (m0 >>= k2)
    }
  .

  Class isMonadTrans (T : (Hask.cat -----> Hask.cat) -> (Hask.cat -----> Hask.cat)) : Type :=
    { liftMonad (M : Hask.cat -----> Hask.cat) (M_isMonad : isMonad M) :> M =====> T M }
  .

  Global Arguments liftMonad {T} {isMonadTrans} {M} {M_isMonad} {obj}.

  Class isMonadIter (M : Hask.cat -----> Hask.cat) {requiresMonad : isMonad M} : Type :=
    { iterMonad {I : Hask.t} {R : Hask.t} (step : kleisli M I (I + R)) : kleisli M I R }
  .

  Global Add Parametric Morphism (M : Hask.cat -----> Hask.cat) {requiresSetoid1 : isSetoid1 M} {requiresMonad : isMonad M} {obeysMonadLaws : @LawsOfMonad M requiresSetoid1 requiresMonad} {A : Hask.t} {B : Hask.t} :
    (@bind M requiresMonad A B) with signature (eqProp ==> eqProp ==> eqProp)
    as bind_lifts_eqProp.
  Proof. ii; etransitivity; [eapply bind_compatWith_eqProp_on_1st_arg | eapply bind_compatWith_eqProp_on_2nd_arg]; eauto. Qed.

  Local Instance Monad_isFunctor (M : Hask.cat -----> Hask.cat) {requiresMonad : isMonad M} : isFunctor M :=
    { fmap {dom : Type} {cod : Type} (f : dom -> cod) (m : M dom) := bind m (fun x : dom => pure (f x)) }
  .

  Global Instance LawsOfMonad_guarantees_LawsOfFunctor (M : Hask.cat -----> Hask.cat)
    {requiresSetoid1 : isSetoid1 M}
    {requiresMonad : isMonad M}
    {obeysMonadLaws : LawsOfMonad M (requiresSetoid1 := requiresSetoid1) (requiresMonad := requiresMonad)}
    : LawsOfFunctor M (requiresSetoid1 := requiresSetoid1) (requiresFunctor := Monad_isFunctor M).
  Proof. (* Thanks to Soonwon Moon *)
    split.
    - ii. symmetry.
      (* Soonwon's Advice:
        (map f . map g) m
        m >>= pure . g >>= pure . f
        m >>= \x -> pure (g x) >>= pure . f
        m >>= \x -> (pure . f) (g x)
        m >>= \x -> pure (f (g x))
        m >>= pure . (f . g)
        map (f . g) m
      *)
      cbn. rewrite bind_assoc.
      eapply bind_compatWith_eqProp_on_2nd_arg.
      ii. rewrite pure_left_id_bind. reflexivity.
    - ii. eapply pure_right_id_bind.
  Qed.

  End TypeclassesForProgrammers.

  Definition stateT (ST : Hask.t) (M : Hask.cat -----> Hask.cat) : Hask.cat -----> Hask.cat := fun X : Hask.t => ST -> M (prod X ST).

  Global Arguments stateT (ST)%type (M) (X)%type.

  Definition StateT {ST : Hask.t} {M : Hask.cat -----> Hask.cat} {X : Hask.t} : Hask.arrow (ST -> M (X * ST)%type) (stateT ST M X) := id.

  Definition runStateT {ST : Hask.t} {M : Hask.cat -----> Hask.cat} {X : Hask.t} : Hask.arrow (stateT ST M X) (ST -> M (X * ST)%type) := id.

  Global Instance stateT_isMonad (ST : Hask.t) (M : Hask.cat -----> Hask.cat) {M_isMonad : isMonad M} : isMonad (stateT ST M) :=
    { pure _ := StateT ∘ curry kempty
    ; bind _ _ := fun m k => StateT (uncurry (runStateT ∘ k) <=< runStateT m)
    }
  .

  Global Instance stateT_isMonadTrans (ST : Hask.t) : isMonadTrans (stateT ST) :=
    { liftMonad (M : Hask.cat -----> Hask.cat) (M_isMonad : isMonad M) (X : Hask.t) (m : M X) := StateT (fun s : ST => fmap (F_isFunctor := Monad_isFunctor M) (fun x : X => (x, s)) m) }
  .

  Definition either {A : Type} {B : Type} {C : Type} (runLEFT : A -> C) (runRIGHT : B -> C) (it : A + B) : C :=
    match it with
    | inl LEFT => runLEFT LEFT
    | inr RIGHT => runRIGHT RIGHT
    end
  .

  Definition prod_ldistr_sum {A : Type} {B : Type} {C : Type} (it : A * (B + C)) : (A * B) + (A * C) :=
    either (fun y : B => inl (fst it, y)) (fun z : C => inr (fst it, z)) (snd it)
  .

  Definition prod_rdistr_sum {A : Type} {B : Type} {C : Type} (it : (A + B) * C) : (A * C) + (B * C) :=
    either (fun x : A => inl (x, snd it)) (fun y : B => inr (y, snd it)) (fst it)
  .

  Global Instance stateT_isMonadIter (ST : Hask.t) (M : Hask.cat -----> Hask.cat) {M_isMonad : isMonad M} {M_isMonadIter : isMonadIter M} : isMonadIter (stateT ST M) :=
    { iterMonad {I : Hask.t} {R : Hask.t} (step : I -> stateT ST M (I + R)) := curry (iterMonad (kempty ∘ prod_rdistr_sum <=< uncurry step)) }
  .

  Inductive sum1 (FL : Hask.cat -----> Hask.cat) (FR : Hask.cat -----> Hask.cat) (X : Hask.t) : Hask.t :=
  | inl1 (LEFT : FL X) : sum1 FL FR X
  | inr1 (RIGHT : FR X) : sum1 FL FR X
  .

  Global Arguments inl1 {FL} {FR} {X}.
  Global Arguments inr1 {FL} {FR} {X}.

  Global Infix " +' " := sum1 (at level 60, no associativity) : type_scope.

  Global Instance sum1_isFunctor (FL : Hask.cat -----> Hask.cat) (FR : Hask.cat -----> Hask.cat) {FL_isFunctor : isFunctor FL} {FR_isFunctor : isFunctor FR} : isFunctor (FL +' FR) :=
    { fmap {A : Type} {B : Type} (f : A -> B) := @sum1_rect _ _ _ (fun _ : sum1 FL FR A => sum1 FL FR B) (fun LEFT : FL A => inl1 (fmap f LEFT)) (fun RIGHT : FR A => inr1 (fmap f RIGHT)) }
  .

  Inductive void1 (X : Hask.t) : Hask.t :=
  .

  Global Instance void1_isFunctor : isFunctor void1 :=
    { fmap {A : Type} {B : Type} (f : A -> B) := @void1_rect _ (fun _ : void1 A => void1 B) }
  .

(** "4. Extras" *)

  Definition liftM2 {M : Type -> Type} {M_isMonad : isMonad M} {A : Type} {B : Type} {C : Type} (f : A -> B -> C) (m1 : M A) (m2 : M B) : M C :=
    m1 >>= fun x1 : A => m2 >>= fun x2 : B => pure (f x1 x2)
  .

  Section MyPair.

  Set Primitive Projections.

  Record Pair (A : Type) (B : Type) : Type := { getFst : A; getSnd : B }.

  Unset Primitive Projections.

  End MyPair.

  Global Arguments getFst {A} {B}.
  Global Arguments getSnd {A} {B}.
  Global Notation mkPair x y := ({| getFst := x; getSnd := y |}).
  Global Infix " \times " := Pair (at level 60, right associativity) : type_scope.

End PreludeInit_MAIN.

Export PreludeInit_MAIN.
