Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.

Module BasicTactics.

  Global Ltac ii := repeat intro.

  Lemma MODUS_PONENS {HYPOTHESIS : Prop} {CONCLUSION : Prop}
    (ASSUMPTION : HYPOTHESIS)
    (PREMISE : HYPOTHESIS -> CONCLUSION)
    : CONCLUSION.
  Proof. exact (PREMISE ASSUMPTION). Defined.

  Global Tactic Notation " exploit " constr( PRF ) "as" simple_intropattern( PAT ) :=
    eapply MODUS_PONENS; [eapply PRF | intros PAT]
  .

  Global Create HintDb khan_hints.

  Global Hint Unfold flip : khan_hints.

End BasicTactics.

Export BasicTactics.

Module BasicCategoryTheory.

  Polymorphic Class Category (objs : Type) : Type :=
    { hom (dom : objs) (cod : objs) : Type
    ; compose {obj_l : objs} {obj : objs} {obj_r : objs} (arr_r : hom obj obj_r) (arr_l : hom obj_l obj) : hom obj_l obj_r
    ; id {obj : objs} : hom obj obj
    }
  .

  Polymorphic Definition isObjectMap {src_objs : Type} {tgt_objs : Type} (src_cat : Category src_objs) (tgt_cat : Category tgt_objs) : Type := src_objs -> tgt_objs.

  Global Infix " -----> " := isObjectMap (at level 100, no associativity) : type_scope.

  Section BasicConceptsOfCategoryTheory.

  Polymorphic Context {src_objs : Type} {tgt_objs : Type} {src_cat : Category src_objs} {tgt_cat : Category tgt_objs}.

  Polymorphic Class CovariantFunctor (F : src_cat -----> tgt_cat) : Type :=
    { fmap {dom : src_objs} {cod : src_objs} (arr : hom dom cod) : hom (F dom) (F cod)
    }
  .

  Polymorphic Class ContravariantFunctor (F : src_cat -----> tgt_cat) : Type :=
    { contramap {dom : src_objs} {cod : src_objs} (arr : hom cod dom) : hom (F dom) (F cod)
    }
  .

  Polymorphic Definition NaturalTransformation (F_from : src_cat -----> tgt_cat) (F_to : src_cat -----> tgt_cat) : Type :=
    forall obj : src_objs, hom (F_from obj) (F_to obj)
  .

  End BasicConceptsOfCategoryTheory.

  Global Infix " =====> " := NaturalTransformation (at level 100, no associativity) : type_scope.

  Polymorphic Definition isComponentOf {src_objs : Type} {tgt_objs : Type} {src_cat : Category src_objs} {tgt_cat : Category tgt_objs} {F_from : src_cat -----> tgt_cat} {F_to : src_cat -----> tgt_cat} (eta : F_from =====> F_to) (at_obj : src_objs) : hom (F_from at_obj) (F_to at_obj) := eta at_obj.

End BasicCategoryTheory.

Module Hask.

  Universe Univ_lv.

  Definition Univ : Type@{Univ_lv + 1} := Type@{Univ_lv}.

  Polymorphic Definition t : Univ := Type.

  Bind Scope type_scope with Hask.t.

  Polymorphic Definition arrow (dom : Hask.t) (cod : Hask.t) : Hask.t := dom -> cod.

  Global Polymorphic Instance cat : BasicCategoryTheory.Category Hask.t :=
    { hom (dom : Hask.t) (cod : Hask.t) := Hask.arrow dom cod
    ; compose {A : Hask.t} {B : Hask.t} {C : Hask.t} := compose (A := A) (B := B) (C := C)
    ; id {A : Hask.t} := id (A := A)
    }
  .

End Hask.

Module BasicTypeClasses.

  Import BasicCategoryTheory.

  Local Open Scope program_scope.

  Polymorphic Class isSetoid (A : Type) : Type :=
    { eqProp (lhs : A) (rhs : A) : Prop
    ; eqProp_Equivalence :> @Equivalence A eqProp
    }
  .

  Global Infix " == " := eqProp (at level 70, no associativity) : type_scope.

  Polymorphic Class isPoset (A : Type) : Type :=
    { leProp (lhs : A) (rhs : A) : Prop
    ; Poset_requiresSetoid :> isSetoid A
    ; leProp_PreOrder :> @PreOrder A leProp
    ; leProp_PartialOrder :> @PartialOrder A eqProp (@eqProp_Equivalence A Poset_requiresSetoid) leProp leProp_PreOrder
    }
  .

  Global Infix " =< " := leProp (at level 70, no associativity) : type_scope.

  Polymorphic Class isSetoid1 (F : Type -> Type) : Type :=
    { liftSetoid1 {X : Type} (X_isSetoid : isSetoid X) :> isSetoid (F X)
    }
  .

  Polymorphic Class CategoryWithEquality {objs : Type} (cat : Category objs) : Type :=
    { hom_isSetoid {dom : objs} {cod : objs} :> isSetoid (hom dom cod)
    ; compose_assoc {A : objs} {B : objs} {C : objs} {D : objs}
      (arr_l : hom C D)
      (arr : hom B C)
      (arr_r : hom A B)
      : compose arr_l (compose arr arr_r) == compose (compose arr_l arr) arr_r
    ; compose_id_l {A : objs} {B : objs}
      (arr_r : hom A B)
      : compose id arr_r == arr_r
    ; compose_id_r {A : objs} {B : objs}
      (arr_l : hom A B)
      : compose arr_l id == arr_l
    ; compose_fst_arg {A : objs} {B : objs} {C : objs}
      (arr_r0 : hom A B)
      (arr_l1 : hom B C)
      (arr_l2 : hom B C)
      (H_FST_ARG : arr_l1 == arr_l2)
      : compose arr_l1 arr_r0 == compose arr_l2 arr_r0 
    ; compose_snd_arg {A : objs} {B : objs} {C : objs}
      (arr_l0 : hom B C)
      (arr_r1 : hom A B)
      (arr_r2 : hom A B)
      (H_SND_ARG : arr_r1 == arr_r2)
      : compose arr_l0 arr_r1 == compose arr_l0 arr_r2 
    }
  .

  Polymorphic Class CovariantFunctorWithEquality {src_objs : Type} {tgt_objs : Type} {src_cat : Category src_objs} {tgt_cat : Category tgt_objs} {tgt_cat_with_eq : CategoryWithEquality (objs := tgt_objs) tgt_cat} (F : src_cat -----> tgt_cat) {F_isFunctor : CovariantFunctor F} : Prop :=
    { covarianceMap_commutes_with_compose {obj_l : src_objs} {obj : src_objs} {obj_r : src_objs}
      (arr_r : hom obj obj_r)
      (arr_l : hom obj_l obj)
      : fmap (dom := obj_l) (cod := obj_r) (compose arr_r arr_l) == compose (fmap arr_r) (fmap arr_l)
    ; covarianceMap_commutes_with_id {obj : src_objs}
      : fmap (dom := obj) (cod := obj) id == id
    }
  .

  Polymorphic Class ContravarinatFunctorWithEquality {src_objs : Type} {tgt_objs : Type} {src_cat : Category src_objs} {tgt_cat : Category tgt_objs} {tgt_cat_with_eq : CategoryWithEquality (objs := tgt_objs) tgt_cat} (F : src_cat -----> tgt_cat) {F_isFunctor : ContravariantFunctor F} : Prop :=
    { contravarianceMap_commutes_with_compose {obj_l : src_objs} {obj : src_objs} {obj_r : src_objs}
      (arr_l : hom obj_l obj)
      (arr_r : hom obj obj_r)
      : contramap (dom := obj_r) (cod := obj_l) (compose arr_r arr_l) == compose (contramap arr_l) (contramap arr_r)
    ; contravarianceMap_commutes_with_id {obj : src_objs}
      : contramap (dom := obj) (cod := obj) id == id
    }
  .

  Global Add Parametric Morphism (objs : Type) (cat : Category objs) (cat_with_eq : CategoryWithEquality (objs := objs) cat) (A : objs) (B : objs) (C : objs) :
    (@compose objs cat A B C) with signature (eqProp ==> eqProp ==> eqProp)
    as compose_lifts_eqProp.
  Proof. ii; etransitivity; [eapply compose_fst_arg | eapply compose_snd_arg]; eauto. Qed.

  Global Notation isFunctor := (CovariantFunctor (src_cat := Hask.cat) (tgt_cat := Hask.cat)).

  Polymorphic Class isMonad (M : Hask.cat -----> Hask.cat) : Type :=
    { pure {A : Hask.t} (x : A) : M A
    ; bind {A : Hask.t} {B : Hask.t} (m : M A) (k : A -> M B) : M B
    }
  .

  Global Infix " >>= " := bind (at level 90, left associativity) : program_scope.

  Global Hint Resolve eqProp_Equivalence : khan_hints.

  Global Hint Resolve Poset_requiresSetoid : khan_hints.

  Global Hint Resolve leProp_PreOrder : khan_hints.

  Global Hint Resolve leProp_PartialOrder : khan_hints.

End BasicTypeClasses.

Module BasicInstances.

  Import BasicCategoryTheory BasicTypeClasses.

  Local Open Scope program_scope.

  Section ImplFor_eq.

  Local Instance theFinestSetoidOf (A : Type) : isSetoid A :=
    { eqProp := @eq A
    ; eqProp_Equivalence := eq_equivalence
    }
  .

  End ImplFor_eq.

  Section ImplFor_option.

  Global Instance option_isFunctor : isFunctor option :=
    { fmap {A : Hask.t} {B : Hask.t} := option_map (A := A) (B := B)
    }
  .

  Definition maybe {A : Hask.t} {B : Hask.t} (d : B) (f : A -> B) (m : option A) : B :=
    match m with
    | Some x => f x
    | None => d
    end
  .

  Global Instance option_isMonad : isMonad option :=
    { pure {A : Hask.t} (x : A) := Some x
    ; bind {A : Hask.t} {B : Hask.t} (m : option A) (k : A -> option B) := maybe None k m
    }
  .

  End ImplFor_option.

  Section ImplFor_image.

  Context {dom : Hask.t} {cod : Hask.t}.

  Definition im_eqProp {cod_isSetoid : isSetoid cod} (f : Hask.arrow dom cod) (lhs : dom) (rhs : dom) : Prop := f lhs == f rhs.

  Definition im_leProp {cod_isPoset : isPoset cod} (f : Hask.arrow dom cod) (lhs : dom) (rhs : dom) : Prop := f lhs =< f rhs.

  Variable f : Hask.arrow dom cod.

  Local Polymorphic Instance equivalence_relation_by_image
    (cod_isSetoid : isSetoid cod)
    : Equivalence (im_eqProp f).
  Proof.
    constructor.
    - intros x1. exact (Equivalence_Reflexive (f x1)).
    - intros x1 x2 H_1EQ2. exact (Equivalence_Symmetric (f x1) (f x2) H_1EQ2).
    - intros x1 x2 x3 H_1EQ2 H_2EQ3. exact (Equivalence_Transitive (f x1) (f x2) (f x3) H_1EQ2 H_2EQ3).
  Defined.

  Local Polymorphic Instance preorder_relation_by_image
    (cod_isPoset : isPoset cod)
    : PreOrder (im_leProp f).
  Proof.
    constructor.
    - intros x1. exact (PreOrder_Reflexive (f x1)).
    - intros x1 x2 x3 H_1LE2 H_2LE3. exact (PreOrder_Transitive (f x1) (f x2) (f x3) H_1LE2 H_2LE3).
  Defined.

  Local Polymorphic Instance partialorder_relation_by_image
    (cod_isPoset : isPoset cod)
    : PartialOrder (im_eqProp f) (im_leProp f).
  Proof.
    intros x1 x2. constructor.
    - intros H_EQ. constructor.
      + exact (proj1 (proj1 (partial_order_equivalence (f x1) (f x2)) H_EQ)).
      + exact (proj2 (proj1 (partial_order_equivalence (f x1) (f x2)) H_EQ)).
    - intros H_EQ. apply (proj2 (partial_order_equivalence (f x1) (f x2))). constructor.
      + exact (proj1 H_EQ).
      + exact (proj2 H_EQ).
  Defined.

  End ImplFor_image.

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

  Global Arguments arrow_eqProp {dom} {cod}.
  Global Arguments arrow_leProp {dom} {cod}.

  Section ImplFor_ensemble.

  Global Instance Prop_isSetoid : isSetoid Prop :=
    { eqProp := iff
    ; eqProp_Equivalence := iff_equivalence
    }
  .

  Local Instance impl_PreOrder
    : PreOrder impl.
  Proof. unfold impl; split; ii; tauto. Qed.

  Local Instance impl_PartialOrder
    : PartialOrder iff impl.
  Proof. unfold impl; intros p1 p2; split; unfold relation_conjunction, flip; cbn; tauto. Qed.

  Local Instance Prop_isPoset : isPoset Prop :=
    { leProp := impl
    ; Poset_requiresSetoid := Prop_isSetoid
    ; leProp_PreOrder := impl_PreOrder
    ; leProp_PartialOrder := impl_PartialOrder
    }
  .

  Definition ensemble : Hask.cat -----> Hask.cat := fun X : Hask.t => Hask.arrow X Prop.

  Global Instance ensemble_isPoset (X : Hask.t) : isPoset (ensemble X) := arrow_isPoset X Prop.

  Context {A : Hask.t}.

  Definition member (x : A) (xs : ensemble A) : Prop := xs x.

  Definition isSubsetOf (xs1 : ensemble A) (xs2 : ensemble A) : Prop :=
    forall x : A, member x xs1 -> member x xs2
  .

  Lemma isSubsetOf_iff (xs1 : ensemble A) (xs2 : ensemble A)
    : isSubsetOf xs1 xs2 <-> xs1 =< xs2.
  Proof. reflexivity. Qed.

  End ImplFor_ensemble.

  Global Opaque ensemble member.

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

  Global Arguments pair_eqProp {fsts} {snds}.
  Global Arguments pair_leProp {fsts} {snds}.

  Section ImplFor_kleisli.

  Definition kleisli_objs (M : Hask.cat -----> Hask.cat) : Hask.Univ := Hask.t.

  Variable M : Hask.cat -----> Hask.cat.

  Definition kleisli (dom : Hask.t) (cod : Hask.t) : kleisli_objs M := Hask.arrow dom (M cod).

  Context {M_isMonad : isMonad M}.

  Local Instance kleisliCategory : Category (kleisli_objs M) :=
    { hom (dom : Hask.t) (cod : Hask.t) := kleisli dom cod
    ; compose {obj_l : Hask.t} {obj : Hask.t} {obj_r : Hask.t} (k_r : kleisli obj obj_r) (k_l : kleisli obj_l obj) := fun x_l => k_l x_l >>= fun x_r => k_r x_r
    ; id {obj : Hask.t} := fun x => pure x
    }
  .

  End ImplFor_kleisli.

End BasicInstances.

Module MyEnsembles.

  Import ListNotations BasicCategoryTheory BasicTypeClasses BasicInstances.

  Inductive _union {A : Hask.t} (Xl : ensemble A) (Xr : ensemble A) (x : A) : Prop :=
  | In_union_l
    (x_in_Xl : member x Xl)
    : member x (_union Xl Xr)
  | In_union_r
    (x_in_Xr : member x Xr)
    : member x (_union Xl Xr)
  .

  Inductive _unions_i {A : Hask.t} {I : Hask.t} (Xs : Hask.arrow I (ensemble A)) (x : A) : Prop :=
  | In_unions_i (i : I)
    (x_in_Xs_i : member x (Xs i))
    : member x (_unions_i Xs)
  .

  Inductive _unions {A : Hask.t} (Xs : ensemble (ensemble A)) (x : A) : Prop :=
  | In_unions (X : ensemble A)
    (x_in_X : member x X)
    (X_in_Xs : member X Xs)
    : member x (_unions Xs)
  .

  Inductive _image {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (X : ensemble A) (y : B) : Prop :=
  | In_image (x : A)
    (y_eq_f_x : y = f x)
    : member y (_image f X)
  .

  Inductive _preimage {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (Y : ensemble B) (x : A) : Prop :=
  | In_preimage
    (f_x_in_Y : member (f x) Y)
    : member x (_preimage f Y)
  .

  Inductive _finite {A : Hask.t} (xs : list A) (x : A) : Prop :=
  | In_finite
    (x_in_xs : In x xs)
    : member x (_finite xs)
  .

  Inductive _intersection {A : Hask.t} (Xl : ensemble A) (Xr : ensemble A) (x : A) : Prop :=
  | In_intersection
    (x_in_Xl : member x Xl)
    (x_in_Xr : member x Xr)
    : member x (_intersection Xl Xr)
  .

  Inductive _full {A : Hask.t} (x : A) : Prop :=
  | In_full
    : member x (_full)
  .

  Definition union {A : Hask.t} (Xl : ensemble A) (Xr : ensemble A) : ensemble A := _union Xl Xr.

  Definition unions_i {A : Hask.t} {I : Hask.t} (Xs : Hask.arrow I (ensemble A)) : ensemble A := _unions_i Xs.

  Definition unions {A : Hask.t} (Xs : ensemble (ensemble A)) : ensemble A := _unions Xs.

  Definition image {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (X : ensemble A) : ensemble B := _image f X.

  Definition preimage {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (Y : ensemble B) : ensemble A := _preimage f Y.

  Definition finite {A : Hask.t} (xs : list A) : ensemble A := _finite xs.

  Definition intersection {A : Hask.t} (Xl : ensemble A) (Xr : ensemble A) : ensemble A := _intersection Xl Xr.

  Definition full {A : Hask.t} : ensemble A := _full.

  Global Opaque union unions_i unions image preimage finite intersection full.

  Local Instance Powerset_CovariantFunctor : CovariantFunctor ensemble :=
    { fmap {A : Hask.t} {B : Hask.t} := image (A := A) (B := B)
    }
  .

  Local Instance Powerset_ContravariantFunctor : ContravariantFunctor ensemble :=
    { contramap {B : Hask.t} {A : Hask.t} := preimage (A := A) (B := B)
    }
  .

End MyEnsembles.

Module BasicMathematicalStructures.

  Import BasicCategoryTheory BasicTypeClasses BasicInstances MyEnsembles.

  Local Open Scope program_scope.

  (** "1. Functor and Monad" *)

  Global Notation " 'id_{' A  '}' " := (fun x : A => x) (at level 0, no associativity) : program_scope.

  Polymorphic Definition fmap {F : Hask.cat -----> Hask.cat} {F_isFunctor : isFunctor F} {A : Hask.t} {B : Hask.t} : hom (objs := Hask.t) (Hask.arrow A B) (Hask.arrow (F A) (F B)) :=
    BasicCategoryTheory.fmap (F := F) (dom := A) (cod := B)
  .

  Global Notation " 'BasicCategoryTheory.fmap' " := BasicCategoryTheory.fmap.

  Local Polymorphic Instance freeSetoidFromSetoid1 (F : Hask.t -> Hask.t) (X : Hask.t) {F_isSetoid1 : isSetoid1 F} : isSetoid (F X) :=
    liftSetoid1 (F := F) (theFinestSetoidOf X)
  .

  Polymorphic Class LawsOfFunctor (F : Hask.cat -----> Hask.cat) {F_isSetoid1 : isSetoid1 F} {F_isFunctor : isFunctor F} : Prop :=
    { fmap_commutes_with_compose {obj_l : Hask.t} {obj : Hask.t} {obj_r : Hask.t}
      (arr_r : obj -> obj_r)
      (arr_l : obj_l -> obj)
      : fmap (arr_r ∘ arr_l) == (fmap arr_r ∘ fmap arr_l)
    ; fmap_commutes_with_id {obj : Hask.t}
      : fmap id_{ obj } == id_{ F obj }
    }
  .

  Polymorphic Class LawsOfMonad (M : Hask.cat -----> Hask.cat) {M_isSetoid1 : isSetoid1 M} {M_isMonad : isMonad M} : Prop :=
    { bind_assoc {A : Hask.t} {B : Hask.t} {C : Hask.t}
      (m0 : M A)
      (k1 : kleisli M A B)
      (k2 : kleisli M B C)
      : (m0 >>= k1 >>= k2) == (m0 >>= fun x1 => k1 x1 >>= k2)
    ; bind_pure_l {A : Hask.t} {B : Hask.t}
      (k : kleisli M A B)
      (x : A)
      : (pure x >>= k) == k x
    ; bind_pure_r {A : Hask.t}
      (m : M A)
      : (m >>= pure) == m
    ; bind_fst_arg {A : Hask.t} {B : Hask.t}
      (m1 : M A)
      (m2 : M A)
      (H_FST_ARG : m1 == m2)
      (k0 : kleisli M A B)
      : (m1 >>= k0) == (m2 >>= k0)
    ; bind_snd_arg {A : Hask.t} {B : Hask.t}
      (k1 : kleisli M A B)
      (k2 : kleisli M A B)
      (H_SND_ARG : k1 == k2)
      (m0 : M A)
      : (m0 >>= k1) == (m0 >>= k2)
    }
  .

  Global Add Parametric Morphism (M : Hask.cat -----> Hask.cat) (M_isSetoid1 : isSetoid1 M) (M_isMonad : isMonad M) (M_obeysMonadLaws : @LawsOfMonad M M_isSetoid1 M_isMonad) (A : Hask.t) (B : Hask.t) :
    (@bind M M_isMonad A B) with signature (eqProp ==> eqProp ==> eqProp)
    as bind_lifts_eqProp.
  Proof. ii; etransitivity; [eapply bind_fst_arg | eapply bind_snd_arg]; eauto. Qed.

  Local Polymorphic Instance mkFunctorFromMonad (M : Hask.cat -----> Hask.cat) {M_isMonad : isMonad M} : isFunctor M :=
    { fmap {dom : Hask.t} {cod : Hask.t} (f : hom dom cod) (m : M dom) := bind m (fun x : dom => pure (f x))
    }
  .

  Global Polymorphic Instance LawsOfMonad_guarantees_LawsOfFunctor (M : Hask.cat -----> Hask.cat)
    {M_isSetoid1 : isSetoid1 M}
    {M_isMonad : isMonad M}
    (M_obeysMonadLaws : LawsOfMonad M (M_isSetoid1 := M_isSetoid1) (M_isMonad := M_isMonad))
    : LawsOfFunctor M (F_isSetoid1 := M_isSetoid1) (F_isFunctor := @mkFunctorFromMonad M M_isMonad).
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
      cbn. rewrite bind_assoc. eapply bind_snd_arg.
      ii. rewrite bind_pure_l. reflexivity.
    - ii. eapply bind_pure_r.
  Qed.

  (** "2. CPO and CoLa" *)

  Definition isSupremumOf {D : Hask.t} {D_isPoset : isPoset D} (sup_X : D) (X : ensemble D) : Prop :=
    forall upper_bound : D, (forall x : D, member x X -> x =< upper_bound) <-> sup_X =< upper_bound
  .

  Class isCoLa (D : Hask.t) {D_isPoset : isPoset D} : Type :=
    { CoLa_requiresCompleteLattice (X : ensemble D) : {sup_X : D | isSupremumOf sup_X X}
    }
  .

  Definition isDirectedSubset {D : Hask.t} {D_isPoset : isPoset D} (X : ensemble D) : Prop :=
    forall x1 : D, member x1 X ->
    forall x2 : D, member x2 X ->
    exists x3 : D, member x3 X /\ (x1 =< x3 /\ x2 =< x3)
  .

  Class isCPO (D : Hask.t) {D_isPoset : isPoset D} : Type :=
    { CPO_requiresCompletePartialOrder (X : ensemble D) (X_isDirected : isDirectedSubset X) : {sup_X : D | isSupremumOf sup_X X}
    }
  .

  (** "3. Topology" *)

  Class isTopologicalSpace (A : Type) : Type :=
    { isOpen (X : ensemble A) : Prop
    ; fullOpen
      : isOpen full
    ; unionsOpen
      (Xs : ensemble (ensemble A))
      (every_member_of_Xs_isOpen : forall X : ensemble A, member X Xs -> isOpen X)
      : isOpen (unions Xs)
    ; intersectionOpen
      (X1 : ensemble A)
      (X2 : ensemble A)
      (X1_isOpen : isOpen X1)
      (X2_isOpen : isOpen X2)
      : isOpen (intersection X1 X2)
    ; open_ext_eq
      (X1 : ensemble A)
      (X2 : ensemble A)
      (X1_isOpen : isOpen X1)
      (X1_eq_X2 : X1 == X2)
      : isOpen X2
    }
  .

  (** "4. Monoid, Group, Ring and Field" *)

  Polymorphic Class isMonoid (M : Hask.t) {M_isSetoid : isSetoid M} : Type :=
    { plu (x1 : M) (x2 : M) : M
    ; zer : M
    ; plu_assoc (x1 : M) (x2 : M) (x3 : M)
      : plu x1 (plu x2 x3) == plu (plu x1 x2) x3
    ; zer_left_id_plu (x : M)
      : plu zer x == x
    ; zer_right_id_plu (x : M)
      : plu x zer == x
    ; plu_lift_eqProp (x1 : M) (x2 : M) (x3 : M) (x4 : M)
      (H_FST_ARG : x1 == x2)
      (H_SND_ARG : x3 == x4)
      : plu x1 x3 == plu x2 x4
    }
  .

  Polymorphic Class isGroup (G : Hask.t) {G_isSetoid : isSetoid G} {G_isMonoid : @isMonoid G G_isSetoid} : Type :=
    { neg (x : G) : G
    ; neg_left_inv_plu (x : G)
      : plu (neg x) x == zer
    ; neg_right_inv_plu (x : G)
      : plu x (neg x) == zer
    ; neg_lift_eqProp (x1 : G) (x2 : G)
      (H_FST_ARG : x1 == x2)
      : neg x1 == neg x2
    }
  .

  Polymorphic Class isRing (R : Hask.t) {R_isSetoid : isSetoid R} {R_isMonoid : @isMonoid R R_isSetoid} {R_isGroup : @isGroup R R_isSetoid R_isMonoid} : Type :=
    { mul (x1 : R) (x2 : R) : R
    ; mul_assoc (x1 : R) (x2 : R) (x3 : R)
      : mul x1 (mul x2 x3) == mul (plu x1 x2) x3
    ; mul_left_distr_plu (x1 : R) (x2 : R) (x3 : R)
      : mul (plu x1 x2) x3 == plu (mul x1 x3) (mul x2 x3)
    ; mul_right_distr_plu (x1 : R) (x2 : R) (x3 : R)
      : mul x1 (plu x2 x3) == plu (mul x1 x3) (mul x2 x3)
    ; mul_lift_eqProp (x1 : R) (x2 : R) (x3 : R) (x4 : R)
      (H_FST_ARG : x1 == x2)
      (H_SND_ARG : x3 == x4)
      : mul x1 x3 == mul x2 x4
    }
  .

  Polymorphic Class isField (K : Hask.t) {K_isSetoid : isSetoid K} {K_isMonoid : @isMonoid K K_isSetoid} {K_isGroup : @isGroup K K_isSetoid K_isMonoid} {K_isRing : @isRing K K_isSetoid K_isMonoid K_isGroup} : Type :=
    { unity : K
    ; recip (x : K) : K
    ; unity_left_id_mul (x : K)
      : mul unity x == x
    ; unity_right_id_mul (x : K)
      : mul x unity == x
    ; unity_NOT_zer
      : ~ unity == zer
    ; recip_left_inv_mul (x : K)
      (x_NOT_zer : ~ x == zer)
      : mul (recip x) x == unity
    ; recip_right_inv_mul (x : K)
      (x_NOT_zer : ~ x == zer)
      : mul x (recip x) == unity
    ; recip_lift_eqProp (x1 : K) (x2 : K)
      (x1_NOT_zer : ~ x1 == zer)
      (x2_NOT_zer : ~ x2 == zer)
      (H_FST_ARG : x1 == x2)
      : recip x1 == recip x2
    }
  .

End BasicMathematicalStructures.

Include BasicTactics.
