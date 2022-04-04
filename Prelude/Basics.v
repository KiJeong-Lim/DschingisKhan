Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.

Module BasicCategoryTheory.

  Polymorphic Class Category (objs : Type) : Type :=
    { hom (dom : objs) (cod : objs) : Type
    ; compose {obj_l : objs} {obj : objs} {obj_r : objs} : hom obj obj_r -> hom obj_l obj -> hom obj_l obj_r
    ; id {obj : objs} : hom obj obj
    }
  .

  Polymorphic Definition objectMap {src_objs : Type} {tgt_objs : Type} (src_cat : Category src_objs) (tgt_cat : Category tgt_objs) : Type := src_objs -> tgt_objs.

  Global Infix " -----> " := objectMap (at level 100, no associativity) : type_scope.

  Section BasicConceptsOfCategoryTheory.

  Polymorphic Context {src_objs : Type} {tgt_objs : Type} {src_cat : Category src_objs} {tgt_cat : Category tgt_objs}.

  Polymorphic Class CovariantFunctor (F : src_cat -----> tgt_cat) : Type :=
    { fmap {dom : src_objs} {cod : src_objs} : hom dom cod -> hom (F dom) (F cod)
    }
  .

  Polymorphic Class ContravariantFunctor (F : src_cat -----> tgt_cat) : Type :=
    { contramap {dom : src_objs} {cod : src_objs} : hom cod dom -> hom (F dom) (F cod)
    }
  .

  Polymorphic Definition functorMap (F_from : src_cat -----> tgt_cat) (F_to : src_cat -----> tgt_cat) : Type :=
    forall obj : src_objs, hom (F_from obj) (F_to obj)
  .

  Polymorphic Class NaturalTransformation (F_from : src_cat -----> tgt_cat) (F_to : src_cat -----> tgt_cat) : Type :=
    { component {at_obj : src_objs} : hom (F_from at_obj) (F_to at_obj)
    }
  .

  End BasicConceptsOfCategoryTheory.

  Global Infix " =====> " := functorMap (at level 100, no associativity) : type_scope.

End BasicCategoryTheory.

Module Hask.

  Universe Univ_lv.

  Definition Univ : Type@{Univ_lv + 1} := Type@{Univ_lv}.

  Polymorphic Definition t : Univ := Type.

  Global Polymorphic Instance cat : BasicCategoryTheory.Category t :=
    { hom (dom : t) (cod : t) := dom -> cod
    ; compose {A : t} {B : t} {C : t} := compose (A := A) (B := B) (C := C)
    ; id {A : t} := id (A := A)
    }
  .

  Bind Scope type_scope with t.

End Hask.

Module MyTypeClasses.

  Import BasicCategoryTheory.

  Local Open Scope program_scope.

  Polymorphic Class isSetoid (A : Type) : Type :=
    { eqProp : A -> A -> Prop
    ; eqProp_Equivalence :> @Equivalence A eqProp
    }
  .

  Global Infix " == " := eqProp (at level 70, no associativity) : type_scope.

  Global Add Parametric Relation (A : Type) (A_isSetoid : isSetoid A) : A (@eqProp A A_isSetoid)
    reflexivity proved by (@Equivalence_Reflexive A eqProp eqProp_Equivalence)
    symmetry proved by (@Equivalence_Symmetric A eqProp eqProp_Equivalence)
    transitivity proved by (@Equivalence_Transitive  A eqProp eqProp_Equivalence)
  as eqProp_is_an_equivalence_relation.

  Polymorphic Class isPoset (A : Type) : Type :=
    { leProp : A -> A -> Prop
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
    ; compose_assoc {A : objs} {B : objs} {C : objs} {D : objs} :
      forall f : hom C D,
      forall g : hom B C,
      forall h : hom A B,
      compose f (compose g h) == compose (compose f g) h
    ; compose_id_l {A : objs} {B : objs} :
      forall f : hom A B,
      compose id f == f
    ; compose_id_r {A : objs} {B : objs} :
      forall f : hom A B,
      compose f id == f
    ; compose_fst_arg {A : objs} {B : objs} {C : objs} :
      forall f : hom B C,
      forall g : hom B C,
      forall h : hom A B,
      f == g ->
      compose f h == compose g h 
    ; compose_snd_arg {A : objs} {B : objs} {C : objs} :
      forall f : hom B C,
      forall g : hom A B,
      forall h : hom A B,
      g == h ->
      compose f g == compose f h 
    }
  .

  Global Add Parametric Morphism (objs : Type) (cat : Category objs) (cat_with_eq : CategoryWithEquality (objs := objs) cat) (A : objs) (B : objs) (C : objs) :
    (@compose objs cat A B C) with signature (eqProp ==> eqProp ==> eqProp)
  as compose_lifts_eqProp.
  Proof.
    intros f1 f2 H_f1_eq_f2 g1 g2 H_g1_eq_g2.
    transitivity (compose f2 g1).
    - eapply compose_fst_arg; exact (H_f1_eq_f2).
    - eapply compose_snd_arg; exact (H_g1_eq_g2).
  Qed.

  Local Polymorphic Instance theFinestSetoidOf (A : Type) : isSetoid A :=
    { eqProp := @eq A
    ; eqProp_Equivalence := eq_equivalence
    }
  .

  Global Notation isFunctor := (CovariantFunctor (src_cat := Hask.cat) (tgt_cat := Hask.cat)).

  Polymorphic Class isMonad (M : Hask.cat -----> Hask.cat) : Type :=
    { pure {A : Hask.t} : A -> M A
    ; bind {A : Hask.t} {B : Hask.t} : M A -> (A -> M B) -> M B
    }
  .

  Global Infix " >>= " := bind (at level 90, left associativity) : program_scope.

End MyTypeClasses.

Module BasicInstances.

  Import BasicCategoryTheory MyTypeClasses.

  Local Open Scope program_scope.

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
    { pure {A : Hask.t} := fun x : A => Some x
    ; bind {A : Hask.t} {B : Hask.t} := fun m : option A => fun k : A -> option B => maybe None k m
    }
  .

  Polymorphic Definition TArr (dom : Hask.t) (cod : Hask.t) : Hask.t := hom dom cod.

  Polymorphic Definition TArr_eqProp {dom : Hask.t} {cod : Hask.t} {cod_isSetoid : isSetoid cod} (lhs : TArr dom cod) (rhs : TArr dom cod) : Prop :=
    forall i : dom, lhs i == rhs i
  .

  Polymorphic Lemma TArr_eqProp_Equivalence {dom : Hask.t} {cod : Hask.t}
    (cod_isSetoid : isSetoid cod)
    : Equivalence (TArr_eqProp (dom := dom) (cod := cod) (cod_isSetoid := cod_isSetoid)).
  Proof. split; (repeat intro); [reflexivity | symmetry | etransitivity]; eauto. Qed.

  Global Polymorphic Instance TArr_isSetoid (dom : Hask.t) (cod : Hask.t) {cod_isSetoid : isSetoid cod} : isSetoid (TArr dom cod) :=
    { eqProp := TArr_eqProp (dom := dom) (cod := cod) (cod_isSetoid := cod_isSetoid)
    ; eqProp_Equivalence := TArr_eqProp_Equivalence (dom := dom) (cod := cod) cod_isSetoid
    }
  .

  Local Instance Prop_isSetoid : isSetoid Prop :=
    { eqProp := iff
    ; eqProp_Equivalence := iff_equivalence
    }
  .

  Polymorphic Definition ensemble (X : Hask.t) : Hask.t := TArr X Prop.

  Local Polymorphic Instance ensemble_isSetoid (X : Hask.t) : isSetoid (ensemble X) := TArr_isSetoid X Prop.

  Polymorphic Definition kleisli_objs (M : Hask.cat -----> Hask.cat) : Hask.Univ := Hask.t.

  Polymorphic Definition kleisli (M : Hask.cat -----> Hask.cat) (dom : Hask.t) (cod : Hask.t) : kleisli_objs M := TArr dom (M cod).

  Local Polymorphic Instance kleisliCategory (M : Hask.cat -----> Hask.cat) {M_isMonad : isMonad M} : Category (kleisli_objs M) :=
    { hom (dom : Hask.t) (cod : Hask.t) := kleisli M dom cod
    ; compose {A : Hask.t} {B : Hask.t} {C : Hask.t} (k1 : kleisli M B C) (k2 : kleisli M A B) := fun x2 : A => k2 x2 >>= fun x1 : B => k1 x1
    ; id {A : Hask.t} := fun x0 : A => pure x0
    }
  .

  Local Polymorphic Instance mkFunctorFromMonad (M : Hask.cat -----> Hask.cat) {M_isMonad : isMonad M} : isFunctor M :=
    { fmap {dom : Hask.t} {cod : Hask.t} (f : dom -> cod) (m : M dom) := bind m (fun x : dom => pure (f x))
    }
  .

End BasicInstances.

Module MyMathematicalStructures.

  Import BasicCategoryTheory MyTypeClasses BasicInstances.

  Local Open Scope program_scope.

  Global Notation " 'id_{' A  '}' " := (BasicCategoryTheory.id (objs := Hask.t) (obj := A)) (at level 0, no associativity) : program_scope.

  Polymorphic Definition fmap {F : Hask.cat -----> Hask.cat} {F_isFunctor : isFunctor F} {A : Hask.t} {B : Hask.t} : hom (objs := Hask.t) (TArr A B) (TArr (F A) (F B)) :=
    BasicCategoryTheory.fmap (F := F) (dom := A) (cod := B)
  .

  Local Polymorphic Instance freeSetoidFromSetoid1 (F : Hask.t -> Hask.t) (X : Hask.t) {F_isSetoid1 : isSetoid1 F} : isSetoid (F X) :=
    liftSetoid1 (F := F) (theFinestSetoidOf X)
  .

  Polymorphic Class LawsOfFunctor (F : Hask.cat -----> Hask.cat) {F_isSetoid1 : isSetoid1 F} {F_isFunctor : isFunctor F} : Prop :=
    { fmap_commutes_with_compose {A : Hask.t} {B : Hask.t} {C : Hask.t} :
      forall f1 : A -> B,
      forall f2 : B -> C,
      fmap (f2 ∘ f1) == (fmap f2 ∘ fmap f1)
    ; fmap_commutes_with_id {A : Hask.t} :
      fmap id_{ A } == id_{ F A }
    }
  .

  Polymorphic Class LawsOfMonad (M : Hask.cat -----> Hask.cat) {M_isSetoid1 : isSetoid1 M} {M_isMonad : isMonad M} : Prop :=
    { bind_assoc {A : Hask.t} {B : Hask.t} {C : Hask.t} :
      forall m0 : M A,
      forall k1 : kleisli M A B,
      forall k2 : kleisli M B C,
      (m0 >>= k1 >>= k2) == (m0 >>= fun x1 : A => k1 x1 >>= k2)
    ; bind_pure_l {A : Hask.t} {B : Hask.t} :
      forall k : kleisli M A B,
      forall x : A,
      (pure x >>= k) == k x
    ; bind_pure_r {A : Hask.t} :
      forall m : M A,
      (m >>= pure) == m
    ; bind_fst_arg {A : Hask.t} {B : Hask.t} :
      forall m1 : M A,
      forall m2 : M A,
      m1 == m2 ->
      forall k0 : kleisli M A B,
      (m1 >>= k0) == (m2 >>= k0)
    ; bind_snd_arg {A : Hask.t} {B : Hask.t} :
      forall k1 : kleisli M A B,
      forall k2 : kleisli M A B,
      k1 == k2 ->
      forall m0 : M A,
      (m0 >>= k1) == (m0 >>= k2)
    }
  .

  Global Add Parametric Morphism (M : Hask.cat -----> Hask.cat) (M_isSetoid1 : isSetoid1 M) (M_isMonad : isMonad M) (M_obeysMonadLaws : @LawsOfMonad M M_isSetoid1 M_isMonad) (A : Hask.t) (B : Hask.t) :
    (@bind M M_isMonad A B) with signature (eqProp ==> eqProp ==> eqProp)
  as bind_lifts_eqProp.
  Proof.
    intros m1 m2 H_m1_eq_m2 k1 k2 H_k1_eq_k2.
    transitivity (m2 >>= k1).
    - eapply bind_fst_arg; exact (H_m1_eq_m2).
    - eapply bind_snd_arg; exact (H_k1_eq_k2).
  Qed.

End MyMathematicalStructures.
