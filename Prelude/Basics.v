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

  Polymorphic Definition isObjectMap {src_objs : Type} {tgt_objs : Type} (src_cat : Category src_objs) (tgt_cat : Category tgt_objs) : Type := src_objs -> tgt_objs.

  Global Infix " -----> " := isObjectMap (at level 100, no associativity) : type_scope.

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

  Polymorphic Definition arrow (dom : t) (cod : t) : t := dom -> cod.

  Global Polymorphic Instance cat : BasicCategoryTheory.Category t :=
    { hom (dom : t) (cod : t) := arrow dom cod
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
      forall f1 : hom C D,
      forall f2 : hom B C,
      forall f3 : hom A B,
      compose f1 (compose f2 f3) == compose (compose f1 f2) f3
    ; compose_id_l {A : objs} {B : objs} :
      forall f1 : hom A B,
      compose id f1 == f1
    ; compose_id_r {A : objs} {B : objs} :
      forall f1 : hom A B,
      compose f1 id == f1
    ; compose_fst_arg {A : objs} {B : objs} {C : objs} :
      forall f1 : hom B C,
      forall f2 : hom B C,
      forall f3 : hom A B,
      f1 == f2 ->
      compose f1 f3 == compose f2 f3 
    ; compose_snd_arg {A : objs} {B : objs} {C : objs} :
      forall f1 : hom B C,
      forall f2 : hom A B,
      forall f3 : hom A B,
      f2 == f3 ->
      compose f1 f2 == compose f1 f3 
    }
  .

  Polymorphic Class CovarinatFunctorWithEquality {src_objs : Type} {tgt_objs : Type} {src_cat : Category src_objs} {tgt_cat : Category tgt_objs} {tgt_cat_with_eq : CategoryWithEquality (objs := tgt_objs) tgt_cat} (F : src_cat -----> tgt_cat) (F_isFunctor : CovariantFunctor F) : Prop :=
    { covaraince_map_commutes_with_compose {A : src_objs} {B : src_objs} {C : src_objs} :
      forall f1 : hom B C,
      forall f2 : hom A B,
      fmap (dom := A) (cod := C) (compose f1 f2) == compose (fmap f1) (fmap f2)
    ; covaraince_map_commutes_with_id {A : src_objs} :
      fmap (dom := A) (cod := A) id == id
    }
  .

  Polymorphic Class ContravarinatFunctorWithEquality {src_objs : Type} {tgt_objs : Type} {src_cat : Category src_objs} {tgt_cat : Category tgt_objs} {tgt_cat_with_eq : CategoryWithEquality (objs := tgt_objs) tgt_cat} (F : src_cat -----> tgt_cat) (F_isFunctor : ContravariantFunctor F) : Prop :=
    { contravaraince_map_commutes_with_compose {A : src_objs} {B : src_objs} {C : src_objs} :
      forall f1 : hom B C,
      forall f2 : hom A B,
      contramap (dom := C) (cod := A) (compose f1 f2) == compose (contramap f2) (contramap f1)
    ; contravaraince_map_commutes_with_id {A : src_objs} :
      contramap (dom := A) (cod := A) id == id
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

  Polymorphic Definition arrow_eqProp {dom : Hask.t} {cod : Hask.t} {cod_isSetoid : isSetoid cod} (lhs : Hask.arrow dom cod) (rhs : Hask.arrow dom cod) : Prop :=
    forall i : dom, lhs i == rhs i
  .

  Polymorphic Lemma arrow_eqProp_Equivalence {dom : Hask.t} {cod : Hask.t}
    (cod_isSetoid : isSetoid cod)
    : Equivalence (arrow_eqProp (dom := dom) (cod := cod) (cod_isSetoid := cod_isSetoid)).
  Proof. split; (repeat intro); [reflexivity | symmetry | etransitivity]; eauto. Qed.

  Global Polymorphic Instance arrow_dom_cod_isSetoid (dom : Hask.t) (cod : Hask.t) {cod_isSetoid : isSetoid cod} : isSetoid (Hask.arrow dom cod) :=
    { eqProp := arrow_eqProp (dom := dom) (cod := cod) (cod_isSetoid := cod_isSetoid)
    ; eqProp_Equivalence := arrow_eqProp_Equivalence (dom := dom) (cod := cod) cod_isSetoid
    }
  .

  Local Instance Prop_isSetoid : isSetoid Prop :=
    { eqProp := iff
    ; eqProp_Equivalence := iff_equivalence
    }
  .

  Polymorphic Definition ensemble (X : Hask.t) : Hask.t := Hask.arrow X Prop.

  Local Polymorphic Instance ensemble_isSetoid (X : Hask.t) : isSetoid (ensemble X) := arrow_dom_cod_isSetoid X Prop.

  Polymorphic Definition kleisli_objs (M : Hask.cat -----> Hask.cat) : Hask.Univ := Hask.t.

  Polymorphic Definition kleisli (M : Hask.cat -----> Hask.cat) (dom : Hask.t) (cod : Hask.t) : kleisli_objs M := Hask.arrow dom (M cod).

  Local Polymorphic Instance kleisliCategory (M : Hask.cat -----> Hask.cat) {M_isMonad : isMonad M} : Category (kleisli_objs M) :=
    { hom (dom : Hask.t) (cod : Hask.t) := kleisli M dom cod
    ; compose {A : Hask.t} {B : Hask.t} {C : Hask.t} (k1 : kleisli M B C) (k2 : kleisli M A B) := fun x2 : A => k2 x2 >>= fun x1 : B => k1 x1
    ; id {A : Hask.t} := fun x0 : A => pure x0
    }
  .

  Local Polymorphic Instance mkFunctorFromMonad (M : Hask.cat -----> Hask.cat) {M_isMonad : isMonad M} : isFunctor M :=
    { fmap {dom : Hask.t} {cod : Hask.t} (f : hom dom cod) (m : M dom) := bind m (fun x : dom => pure (f x))
    }
  .

  Section THE_FINEST_SETOID.

  Local Polymorphic Instance theFinestSetoidOf (A : Type) : isSetoid A :=
    { eqProp := @eq A
    ; eqProp_Equivalence := eq_equivalence
    }
  .

  End THE_FINEST_SETOID.

End BasicInstances.

Module MyMathematicalStructures.

  Import BasicCategoryTheory MyTypeClasses BasicInstances.

  Local Open Scope program_scope.

  Global Notation " 'id_{' A  '}' " := (fun x : A => x) (at level 0, no associativity) : program_scope.

  Polymorphic Definition fmap {F : Hask.cat -----> Hask.cat} {F_isFunctor : isFunctor F} {A : Hask.t} {B : Hask.t} : hom (objs := Hask.t) (Hask.arrow A B) (Hask.arrow (F A) (F B)) :=
    BasicCategoryTheory.fmap (F := F) (dom := A) (cod := B)
  .

  Global Notation " 'BasicCategoryTheory.fmap' " := BasicCategoryTheory.fmap.

  Local Polymorphic Instance freeSetoidFromSetoid1 (F : Hask.t -> Hask.t) (X : Hask.t) {F_isSetoid1 : isSetoid1 F} : isSetoid (F X) :=
    liftSetoid1 (F := F) (theFinestSetoidOf X)
  .

  Polymorphic Class LawsOfFunctor (F : Hask.cat -----> Hask.cat) {F_isSetoid1 : isSetoid1 F} {F_isFunctor : isFunctor F} : Prop :=
    { fmap_commutes_with_compose {A : Hask.t} {B : Hask.t} {C : Hask.t} :
      forall f1 : B -> C,
      forall f2 : A -> B,
      fmap (f1 ∘ f2) == (fmap f1 ∘ fmap f2)
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
