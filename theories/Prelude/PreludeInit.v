Require Export Coq.Classes.RelationClasses.
Require Export Coq.Lists.List.
Require Export Coq.Program.Basics.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Setoids.Setoid.

Module Khan.

  (** "\S0. Notations" *)

  Global Notation compose := compose.
  Global Notation id := id.
  Global Notation " 'id_{' A  '}' " := (@id A) (A at level 100, at level 0, no associativity) : program_scope.

  (* Reserved *)
  Global Reserved Infix " == " (at level 70, no associativity).
  Global Reserved Infix " =< " (at level 70, no associativity).
  Global Reserved Infix " \in " (at level 70, no associativity).

  (** "\S1. Reference Holder" *)

  Polymorphic Definition REFERENCE_HOLDER {STATEMENT_Type : Type} (REFERENCED_STATEMENT : unit -> STATEMENT_Type) : STATEMENT_Type := REFERENCED_STATEMENT tt.

  Global Notation " '<<' STATEMENT_REFERENCE ':' STATEMENT '>>' " := (REFERENCE_HOLDER (fun STATEMENT_REFERENCE : unit => match STATEMENT_REFERENCE with | tt => STATEMENT end)) (STATEMENT_REFERENCE name, STATEMENT at level 200, at level 70, no associativity) : type_scope.

  Global Ltac unnw := unfold REFERENCE_HOLDER in *.

  (** "\S2. Hint Database" *)

  Global Create HintDb khan_hints.

  Global Hint Unfold flip : khan_hints.
  Global Hint Unfold relation_conjunction : khan_hints.
  Global Hint Unfold REFERENCE_HOLDER : khan_hints.

  (** "\S3. Introduction Tactics" *)

  Global Ltac ii := (repeat intro).

  (** "\S4. Exploit Tactics" *)

  Lemma MODUS_PONENS {HYPOTHESIS : Prop} {CONCLUSION : Prop}
    (ASSUMPTION : HYPOTHESIS)
    (PREMISE : HYPOTHESIS -> CONCLUSION)
    : CONCLUSION.
  Proof. exact (PREMISE ASSUMPTION). Defined.

  Global Tactic Notation " exploit " constr( PRF ) "as" simple_intropattern( PAT ) :=
    eapply MODUS_PONENS; [eapply PRF | intros PAT]
  .

End Khan.

Export Khan.

Module Cat.

  Polymorphic Class isCategory (objs : Type) : Type :=
    { hom (dom : objs) (cod : objs) : Type
    ; compose {obj_l : objs} {obj : objs} {obj_r : objs} (arr_r : hom obj obj_r) (arr_l : hom obj_l obj) : hom obj_l obj_r
    ; id {obj : objs} : hom obj obj
    }
  .

  Polymorphic Definition ObjectMap {src_objs : Type} {tgt_objs : Type} (src_cat : isCategory src_objs) (tgt_cat : isCategory tgt_objs) : Type := src_objs -> tgt_objs.

  Global Bind Scope type_scope with ObjectMap isCategory hom.

  Global Infix " -----> " := ObjectMap (at level 100, no associativity) : type_scope.

  Section BasicConceptsOfCategoryTheory.

  Polymorphic Context {src_objs : Type} {tgt_objs : Type} {src_cat : isCategory src_objs} {tgt_cat : isCategory tgt_objs}.

  Polymorphic Class isCovariantFunctor (F : src_cat -----> tgt_cat) : Type :=
    { fmap {dom : src_objs} {cod : src_objs} (arr : hom dom cod) : hom (F dom) (F cod)
    }
  .

  Polymorphic Class isContravariantFunctor (F : src_cat -----> tgt_cat) : Type :=
    { contramap {dom : src_objs} {cod : src_objs} (arr : hom cod dom) : hom (F dom) (F cod)
    }
  .

  Polymorphic Class isNaturalTransformation (F_from : src_cat -----> tgt_cat) (F_to : src_cat -----> tgt_cat) : Type := component (obj : src_objs) : hom (F_from obj) (F_to obj).

  End BasicConceptsOfCategoryTheory.

  Global Infix " =====> " := isNaturalTransformation (at level 100, no associativity) : type_scope.

  Global Arguments component {src_objs} {tgt_objs} {src_cat} {tgt_cat} {F_from} {F_to} {_} {obj}.

End Cat.

Export Cat.

Module Hask.

  Universe Univ_lv.

  Monomorphic Definition Univ : Type@{Univ_lv + 1} := Type@{Univ_lv}.

  Polymorphic Definition t : Hask.Univ := Type.

  Polymorphic Definition arrow (dom : Hask.t) (cod : Hask.t) : Hask.t := dom -> cod.

  Global Bind Scope type_scope with Hask.Univ Hask.t Hask.arrow.

  Global Polymorphic Instance cat : isCategory Hask.t :=
    { hom (dom : Hask.t) (cod : Hask.t) := Hask.arrow dom cod
    ; compose {A : Hask.t} {B : Hask.t} {C : Hask.t} := Khan.compose (A := A) (B := B) (C := C)
    ; id {A : Hask.t} := Khan.id (A := A)
    }
  .

End Hask.

Module PreludeInit_main.

  Local Open Scope program_scope.

  (** "1. Setoid and Poset" *)

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

  (** "2. Category and Functor with Equality" *)

  Polymorphic Class isCategory_withLaws (objs : Type) : Type :=
    { Category_withLaws_requiresCategory_asSelf :> isCategory objs
    ; hom_isSetoid {dom : objs} {cod : objs} :> isSetoid (hom dom cod)
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

  Global Coercion Category_withLaws_requiresCategory_asSelf : isCategory_withLaws >-> isCategory.

  Section FUNCTOR_WITH_LAWS.

  Context {src_objs : Type} {tgt_objs : Type}.

  Polymorphic Class CovariantFunctor_Laws {src_cat : isCategory src_objs} {tgt_cat : isCategory_withLaws tgt_objs} (F : src_cat -----> tgt_cat) {F_isFunctor : isCovariantFunctor F} : Prop :=
    { covarianceMap_commutes_with_compose {obj_l : src_objs} {obj : src_objs} {obj_r : src_objs}
      (arr_r : hom obj obj_r)
      (arr_l : hom obj_l obj)
      : fmap (dom := obj_l) (cod := obj_r) (compose arr_r arr_l) == compose (fmap arr_r) (fmap arr_l)
    ; covarianceMap_commutes_with_id {obj : src_objs}
      : fmap (dom := obj) (cod := obj) id == id
    }
  .

  Polymorphic Class ContravariantFunctor_Laws {src_cat : isCategory src_objs} {tgt_cat : isCategory_withLaws tgt_objs} (F : src_cat -----> tgt_cat) {F_isFunctor : isContravariantFunctor F} : Prop :=
    { contravarianceMap_commutes_with_compose {obj_l : src_objs} {obj : src_objs} {obj_r : src_objs}
      (arr_l : hom obj_l obj)
      (arr_r : hom obj obj_r)
      : contramap (dom := obj_r) (cod := obj_l) (compose arr_r arr_l) == compose (contramap arr_l) (contramap arr_r)
    ; contravarianceMap_commutes_with_id {obj : src_objs}
      : contramap (dom := obj) (cod := obj) id == id
    }
  .

  End FUNCTOR_WITH_LAWS.

  (** "3. Accessories" *)

  Global Hint Resolve eqProp_Equivalence : khan_hints.
  Global Hint Resolve Poset_requiresSetoid : khan_hints.
  Global Hint Resolve leProp_PreOrder : khan_hints.
  Global Hint Resolve leProp_PartialOrder : khan_hints.

  Global Add Parametric Morphism (objs : Type) {cat : isCategory_withLaws objs} {A : objs} {B : objs} {C : objs} :
    (@compose objs cat A B C) with signature (eqProp ==> eqProp ==> eqProp)
    as compose_lifts_eqProp.
  Proof. ii; etransitivity; [eapply compose_fst_arg | eapply compose_snd_arg]; eauto. Qed.

  Global Notation isFunctor := (isCovariantFunctor (src_cat := Hask.cat) (tgt_cat := Hask.cat)).

  Polymorphic Class isMonad (M : Hask.cat -----> Hask.cat) : Type :=
    { pure {A : Hask.t} (x : A) : M A
    ; bind {A : Hask.t} {B : Hask.t} (m : M A) (k : A -> M B) : M B
    }
  .

  Global Infix " >>= " := bind (at level 90, left associativity) : program_scope.

  (** "4. Basic Instances" *)

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

  Lemma equivalence_relation_by_image
    (cod_isSetoid : isSetoid cod)
    : Equivalence (im_eqProp f).
  Proof.
    constructor.
    - intros x1. exact (Equivalence_Reflexive (f x1)).
    - intros x1 x2 H_1EQ2. exact (Equivalence_Symmetric (f x1) (f x2) H_1EQ2).
    - intros x1 x2 x3 H_1EQ2 H_2EQ3. exact (Equivalence_Transitive (f x1) (f x2) (f x3) H_1EQ2 H_2EQ3).
  Defined.

  Lemma preorder_relation_by_image
    (cod_isPoset : isPoset cod)
    : PreOrder (im_leProp f).
  Proof.
    constructor.
    - intros x1. exact (PreOrder_Reflexive (f x1)).
    - intros x1 x2 x3 H_1LE2 H_2LE3. exact (PreOrder_Transitive (f x1) (f x2) (f x3) H_1LE2 H_2LE3).
  Defined.

  Lemma partialorder_relation_by_image
    (cod_isPoset : isPoset cod)
    : @PartialOrder _ (im_eqProp f) (equivalence_relation_by_image _) (im_leProp f) (preorder_relation_by_image _).
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
  Global Arguments arrow_isSetoid {dom} {cod}.
  Global Arguments arrow_isPoset {dom} {cod}.

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

  Definition member {A : Hask.t} (x : A) (xs : ensemble A) : Prop := xs x.

  Global Opaque ensemble member.

  Definition isSameSetAs {A : Hask.t} (lhs : ensemble A) (rhs : ensemble A) : Prop :=
    forall x : A, member x lhs <-> member x rhs
  .

  Global Instance ensemble_isSetoid (A : Hask.t) : isSetoid (ensemble A) :=
    { eqProp := @isSameSetAs A
    ; eqProp_Equivalence := @arrow_eqProp_Equivalence A Prop Prop_isSetoid
    }
  .

  Lemma unfold_ensemble_isSetoid {A : Hask.t}
    : ensemble_isSetoid A = @arrow_isSetoid A Prop Prop_isSetoid.
  Proof. reflexivity. Qed.

  Definition isSubsetOf {A : Hask.t} (lhs : ensemble A) (rhs : ensemble A) : Prop :=
    forall x : A, member x lhs -> member x rhs
  .

  Global Instance ensemble_isPoset (A : Hask.t) : isPoset (ensemble A) :=
    { leProp := @isSubsetOf A
    ; Poset_requiresSetoid := ensemble_isSetoid A
    ; leProp_PreOrder := arrow_leProp_PreOrder A Prop Prop_isPoset
    ; leProp_PartialOrder := arrow_leProp_PartialOrder A Prop Prop_isPoset
    }
  .

  Lemma unfold_ensemble_isPoset {A : Hask.t}
    : ensemble_isPoset A = @arrow_isPoset A Prop Prop_isPoset.
  Proof. reflexivity. Qed.

  End ImplFor_ensemble.

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
  Global Arguments pair_isSetoid {fsts} {snds}.
  Global Arguments pair_isPoset {fsts} {snds}.

  Section ImplFor_kleisli.

  Definition kleisli_objs (M : Hask.cat -----> Hask.cat) : Hask.Univ := Hask.t.

  Variable M : Hask.cat -----> Hask.cat.

  Definition kleisli (dom : Hask.t) (cod : Hask.t) : kleisli_objs M := Hask.arrow dom (M cod).

  Variable requiresMonad : isMonad M.

  Definition kempty {obj : Hask.t} : kleisli obj obj :=
    fun x => pure x
  .

  Definition kappend {obj_l : Hask.t} {obj : Hask.t} {obj_r : Hask.t} (k_r : kleisli obj obj_r) (k_l : kleisli obj_l obj) : kleisli obj_l obj_r :=
    fun x_l => k_l x_l >>= fun x_r => k_r x_r
  .

  Local Instance kleisliCategory : isCategory (kleisli_objs M) :=
    { hom (dom : Hask.t) (cod : Hask.t) := kleisli dom cod
    ; compose {obj_l : Hask.t} {obj : Hask.t} {obj_r : Hask.t} := kappend (obj_l := obj_l) (obj := obj) (obj_r := obj_r)
    ; id {obj : Hask.t} := kempty (obj := obj)
    }
  .

  End ImplFor_kleisli.

  Global Arguments kempty {M} {requiresMonad} {_}.
  Global Arguments kappend {M} {requiresMonad} {_} {_} {_}.
  Global Arguments kleisliCategory (M) {requiresMonad}.

  Global Infix " <=< " := kappend (at level 40, left associativity) : program_scope.

  Section ProgrammersTypeclasses.

  Polymorphic Definition fmap {F : Hask.cat -----> Hask.cat} {F_isFunctor : isFunctor F} {A : Hask.t} {B : Hask.t} : hom (objs := Hask.t) (Hask.arrow A B) (Hask.arrow (F A) (F B)) :=
    Cat.fmap (F := F) (dom := A) (cod := B)
  .

  Local Polymorphic Instance freeSetoidFromSetoid1 (F : Hask.cat -----> Hask.cat) (X : Hask.t) {requiresSetoid1 : isSetoid1 F} : isSetoid (F X) :=
    liftSetoid1 (F := F) (theFinestSetoidOf X)
  .

  Polymorphic Class LawsOfFunctor (F : Hask.cat -----> Hask.cat) {requiresSetoid1 : isSetoid1 F} {requiresFunctor : isFunctor F} : Prop :=
    { fmap_commutes_with_compose {obj_l : Hask.t} {obj : Hask.t} {obj_r : Hask.t}
      (arr_r : obj -> obj_r)
      (arr_l : obj_l -> obj)
      : fmap (arr_r ∘ arr_l) == (fmap arr_r ∘ fmap arr_l)
    ; fmap_commutes_with_id {obj : Hask.t}
      : fmap id_{ obj } == id_{ F obj }
    }
  .

  Polymorphic Class LawsOfMonad (M : Hask.cat -----> Hask.cat) {requiresSetoid1 : isSetoid1 M} {requiresMonad : isMonad M} : Prop :=
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

  Polymorphic Class isMonadTrans (T : (Hask.cat -----> Hask.cat) -> (Hask.cat -----> Hask.cat)) : Type :=
    { liftMonad {M : Hask.cat -----> Hask.cat} {M_isMonad : isMonad M} : M =====> T M
    }
  .

  Global Arguments liftMonad {T} {_} {M} {M_isMonad} {_}.

  Polymorphic Class isMonadIter (M : Hask.cat -----> Hask.cat) {requiresMonad : isMonad M} : Type :=
    { iterMonad {I : Hask.t} {R : Hask.t} (step : I -> M (I + R)%type) : I -> M R
    }
  .

  Global Add Parametric Morphism (M : Hask.cat -----> Hask.cat) {requiresSetoid1 : isSetoid1 M} {requiresMonad : isMonad M} {obeysMonadLaws : @LawsOfMonad M requiresSetoid1 requiresMonad} {A : Hask.t} {B : Hask.t} :
    (@bind M requiresMonad A B) with signature (eqProp ==> eqProp ==> eqProp)
    as bind_lifts_eqProp.
  Proof. ii; etransitivity; [eapply bind_fst_arg | eapply bind_snd_arg]; eauto. Qed.

  Local Polymorphic Instance Monad_isFunctor (M : Hask.cat -----> Hask.cat) {requiresMonad : isMonad M} : isFunctor M :=
    { fmap {dom : Hask.t} {cod : Hask.t} (f : hom dom cod) (m : M dom) := bind m (fun x : dom => pure (f x))
    }
  .

  Global Polymorphic Instance LawsOfMonad_guarantees_LawsOfFunctor (M : Hask.cat -----> Hask.cat)
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
      cbn. rewrite bind_assoc. eapply bind_snd_arg.
      ii. rewrite bind_pure_l. reflexivity.
    - ii. eapply bind_pure_r.
  Qed.

  End ProgrammersTypeclasses.

  Polymorphic Definition stateT (ST : Hask.t) (M : Hask.cat -----> Hask.cat) : Hask.cat -----> Hask.cat := fun X : Hask.t => ST -> M (prod X ST).

  Polymorphic Definition StateT {ST : Hask.t} {M : Hask.cat -----> Hask.cat} {X : Hask.t} : Hask.arrow (ST -> M (X * ST)%type) (stateT ST M X) := id_{ stateT ST M X }.

  Polymorphic Definition runStateT {ST : Hask.t} {M : Hask.cat -----> Hask.cat} {X : Hask.t} : Hask.arrow (stateT ST M X) (ST -> M (X * ST)%type) := id_{ stateT ST M X }.

  Global Polymorphic Instance stateT_ST_M_isMonad (ST : Hask.t) (M : Hask.cat -----> Hask.cat) {M_isMonad : isMonad M} : isMonad (stateT ST M) :=
    { pure _ := StateT ∘ curry kempty
    ; bind _ _ := fun m k => StateT (uncurry (runStateT ∘ k) <=< runStateT m)
    }
  .

  Global Polymorphic Instance stateT_ST_isMonadTrans (ST : Hask.t) : isMonadTrans (stateT ST) :=
    { liftMonad {M : Hask.cat -----> Hask.cat} {M_isMonad : isMonad M} (X : Hask.t) := fun m : M X => StateT (fun s : ST => fmap (F_isFunctor := Monad_isFunctor M) (fun x : X => (x, s)) m)
    }
  .

  Polymorphic Definition sum_prod_distr_l {A : Hask.t} {B : Hask.t} {C : Hask.t} (it : (A + B) * C) : (A * C) + (B * C) :=
    match it with
    | (inl x, z) => inl (x, z)
    | (inr y, z) => inr (y, z)
    end
  .

  Global Polymorphic Instance stateT_ST_isMonadIter (ST : Hask.t) (M : Hask.cat -----> Hask.cat) {M_isMonad : isMonad M} {M_isMonadIter : isMonadIter M} : isMonadIter (stateT ST M) :=
    { iterMonad {I : Hask.t} {R : Hask.t} (step : I -> stateT ST M (I + R)%type) := curry (iterMonad (kempty ∘ sum_prod_distr_l <=< uncurry step))
    }
  .

  Polymorphic Inductive sum1 (FL : Hask.cat -----> Hask.cat) (FR : Hask.cat -----> Hask.cat) (X : Hask.t) : Hask.t :=
  | inl1 : FL X -> sum1 FL FR X
  | inr1 : FR X -> sum1 FL FR X
  .

  Global Arguments inl1 {FL} {FR} {X}.
  Global Arguments inr1 {FL} {FR} {X}.

  Global Infix " +' " := sum1 (at level 60, no associativity) : type_scope.

  Global Instance sum1_FL_FR_isFunctor (FL : Hask.cat -----> Hask.cat) (FR : Hask.cat -----> Hask.cat) {FL_isFunctor : isFunctor FL} {FR_isFunctor : isFunctor FR} : isFunctor (sum1 FL FR) :=
    { fmap {A : Hask.t} {B : Hask.t} := fun f : Hask.arrow A B => sum1_rect FL FR A (fun _ : sum1 FL FR A => sum1 FL FR B) (fun l : FL A => inl1 (fmap f l)) (fun r : FR A => inr1 (fmap f r))
    }
  .

End PreludeInit_main.

Export PreludeInit_main.

Module E.

  Import ListNotations.

  Local Open Scope program_scope.

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
    (x_in_X : member x X)
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

  Inductive _empty {A : Hask.t} (x : A) : Prop :=
  .

  Local Hint Constructors _union _unions_i _unions _image _preimage _finite _intersection _full _empty : core.

  Global Infix " \in " := member (at level 70, no associativity) : type_scope.

  Definition union {A : Hask.t} (Xl : ensemble A) (Xr : ensemble A) : ensemble A := _union Xl Xr.

  Lemma in_union_iff {A : Hask.t} (Xl : ensemble A) (Xr : ensemble A)
    : forall x : A, x \in union Xl Xr <-> (x \in Xl \/ x \in Xr).
  Proof. intros x; split; intros [H_l | H_r]; eauto. Qed.

  Definition unions_i {A : Hask.t} {I : Hask.t} (Xs : Hask.arrow I (ensemble A)) : ensemble A := _unions_i Xs.

  Lemma in_unions_i_iff {A : Hask.t} {I : Hask.t} (Xs : Hask.arrow I (ensemble A))
    : forall x : A, x \in unions_i Xs <-> (exists i : I, x \in Xs i).
  Proof. intros x; split; intros [i H_i]; eauto. Qed.

  Definition unions {A : Hask.t} (Xs : ensemble (ensemble A)) : ensemble A := _unions Xs.

  Lemma in_unions_iff {A : Hask.t} (Xs : ensemble (ensemble A))
    : forall x : A, x \in unions Xs <-> (exists X : ensemble A, x \in X /\ X \in Xs).
  Proof. intros x; split; [intros [X H_X H_Xs] | intros [X [H_X H_Xs]]]; eauto. Qed.

  Definition image {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (X : ensemble A) : ensemble B := _image f X.

  Lemma in_image_iff {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (X : ensemble A)
    : forall y : B, y \in image f X <-> (exists x : A, y = f x /\ x \in X).
  Proof. intros y; split; [intros [x H_x H_y] | intros [x [H_x H_y]]]; eauto. Qed.

  Definition preimage {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (Y : ensemble B) : ensemble A := _preimage f Y.

  Lemma in_preimage_iff {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (Y : ensemble B)
    : forall x : A, x \in preimage f Y <-> (exists y : B, y = f x /\ y \in Y).
  Proof. intros y; split; [intros [H_x] | intros [x [H_x H_y]]; subst]; eauto. Qed.

  Definition finite {A : Hask.t} (xs : list A) : ensemble A := _finite xs.

  Lemma in_finite_iff {A : Hask.t} (xs : list A)
    : forall x : A, x \in finite xs <-> (In x xs).
  Proof. intros x; split; [intros [H_x] | intros H_x]; eauto. Qed.

  Definition intersection {A : Hask.t} (Xl : ensemble A) (Xr : ensemble A) : ensemble A := _intersection Xl Xr.

  Lemma in_intersection_iff {A : Hask.t} (Xl : ensemble A) (Xr : ensemble A)
    : forall x : A, x \in intersection Xl Xr <-> (x \in Xl /\ x \in Xr).
  Proof. intros x; split; intros [H_l H_r]; eauto. Qed.

  Definition full {A : Hask.t} : ensemble A := _full.

  Lemma in_full_iff {A : Hask.t}
    : forall x : A, x \in full <-> (True).
  Proof. intros x; split; eauto. Qed.

  Definition empty {A : Hask.t} : ensemble A := _empty.

  Lemma in_empty_iff {A : Hask.t}
    : forall x : A, x \in empty <-> (False).
  Proof. intros x; split; intros []. Qed.

  Definition complement {A : Hask.t} (X : ensemble A) : ensemble A := fun x : A => ~ x \in X.

  Lemma in_complement_iff {A : Hask.t} (X : ensemble A)
    : forall x : A, x \in complement X <-> (~ x \in X).
  Proof. reflexivity. Qed.

  Definition singleton {A : Hask.t} (z : A) : ensemble A := finite [z].

  Lemma in_singleton_iff {A : Hask.t} (z : A)
    : forall x : A, x \in singleton z <-> (x = z).
  Proof. intros x. unfold singleton. rewrite in_finite_iff. split; [intros [H | []] | intros []; left]; eauto. Qed.

  Definition delete {A : Hask.t} (z : A) (X : ensemble A) : ensemble A := intersection (complement (singleton z)) X.

  Lemma in_delete_iff {A : Hask.t} (z : A) (X : ensemble A)
    : forall x : A, x \in delete z X <-> (x <> z /\ x \in X).
  Proof. intros x. unfold delete. rewrite in_intersection_iff, in_complement_iff, in_singleton_iff. tauto. Qed.

  Definition insert {A : Hask.t} (z : A) (X : ensemble A) : ensemble A := union (singleton z) X.

  Lemma in_insert_iff {A : Hask.t} (z : A) (X : ensemble A)
    : forall x : A, x \in insert z X <-> (x = z \/ x \in X).
  Proof. intros x. unfold insert. rewrite in_union_iff, in_singleton_iff. tauto. Qed.

  Global Opaque union unions_i unions image preimage finite intersection full empty complement singleton delete insert.

  Local Instance Powerset_isCovariantFunctor : isCovariantFunctor ensemble :=
    { fmap {A : Hask.t} {B : Hask.t} := image (A := A) (B := B)
    }
  .

  Local Instance Powerset_isContravariantFunctor : isContravariantFunctor ensemble :=
    { contramap {B : Hask.t} {A : Hask.t} := preimage (A := A) (B := B)
    }
  .

End E.
