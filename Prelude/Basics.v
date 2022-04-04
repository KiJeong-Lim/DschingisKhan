Require Import Coq.Classes.RelationClasses.
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
  Proof. tauto. Qed.

  Global Tactic Notation " exploit " constr( PRF ) "as" simple_intropattern( PAT ) :=
    eapply MODUS_PONENS; [ eapply PRF | intros PAT ]
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
      (f1 : hom C D)
      (f2 : hom B C)
      (f3 : hom A B)
      : compose f1 (compose f2 f3) == compose (compose f1 f2) f3
    ; compose_id_l {A : objs} {B : objs}
      (f1 : hom A B)
      : compose id f1 == f1
    ; compose_id_r {A : objs} {B : objs}
      (f1 : hom A B)
      : compose f1 id == f1
    ; compose_fst_arg {A : objs} {B : objs} {C : objs}
      (f1 : hom B C)
      (f2 : hom B C)
      (f3 : hom A B)
      (H_FST_ARG_EQ : f1 == f2)
      : compose f1 f3 == compose f2 f3 
    ; compose_snd_arg {A : objs} {B : objs} {C : objs}
      (f1 : hom B C)
      (f2 : hom A B)
      (f3 : hom A B)
      (H_SND_ARG_EQ : f2 == f3)
      : compose f1 f2 == compose f1 f3 
    }
  .

  Polymorphic Class CovarinatFunctorWithEquality {src_objs : Type} {tgt_objs : Type} {src_cat : Category src_objs} {tgt_cat : Category tgt_objs} {tgt_cat_with_eq : CategoryWithEquality (objs := tgt_objs) tgt_cat} (F : src_cat -----> tgt_cat) (F_isFunctor : CovariantFunctor F) : Prop :=
    { covarianceMap_commutes_with_compose {obj_l : src_objs} {obj : src_objs} {obj_r : src_objs}
      (arr_r : hom obj obj_r)
      (arr_l : hom obj_l obj)
      : fmap (dom := obj_l) (cod := obj_r) (compose arr_r arr_l) == compose (fmap arr_r) (fmap arr_l)
    ; covarianceMap_commutes_with_id {obj : src_objs}
      : fmap (dom := obj) (cod := obj) id == id
    }
  .

  Polymorphic Class ContravarinatFunctorWithEquality {src_objs : Type} {tgt_objs : Type} {src_cat : Category src_objs} {tgt_cat : Category tgt_objs} {tgt_cat_with_eq : CategoryWithEquality (objs := tgt_objs) tgt_cat} (F : src_cat -----> tgt_cat) (F_isFunctor : ContravariantFunctor F) : Prop :=
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

  Section ImplFor_arrow.

  Context {dom : Hask.t} {cod : Hask.t}.

  Definition arrow_eqProp {cod_isSetoid : isSetoid cod} (lhs : Hask.arrow dom cod) (rhs : Hask.arrow dom cod) : Prop :=
    forall x : dom, lhs x == rhs x
  .

  Local Instance arrow_eqProp_Equivalence
    (cod_isSetoid : isSetoid cod)
    : Equivalence (arrow_eqProp (cod_isSetoid := cod_isSetoid)).
  Proof. split; ii; [reflexivity | symmetry | etransitivity]; eauto. Qed.

  Global Instance arrow_dom_cod_isSetoid {cod_isSetoid : isSetoid cod} : isSetoid (Hask.arrow dom cod) :=
    { eqProp := arrow_eqProp (cod_isSetoid := cod_isSetoid)
    ; eqProp_Equivalence := arrow_eqProp_Equivalence cod_isSetoid
    }
  .

  Definition arrow_leProp {cod_isPoset : isPoset cod} (lhs : Hask.arrow dom cod) (rhs : Hask.arrow dom cod) : Prop :=
    forall x : dom, lhs x =< rhs x
  .

  Local Instance arrow_leProp_PreOrder
    (cod_isPoset : isPoset cod)
    : PreOrder (arrow_leProp (cod_isPoset := cod_isPoset)).
  Proof. split; ii; [reflexivity | etransitivity]; eauto. Qed.

  Local Instance arrow_leProp_PartialOrder
    (cod_isPoset : isPoset cod)
    : PartialOrder eqProp (arrow_leProp (cod_isPoset := cod_isPoset)).
  Proof with eauto with *.
    intros f1 f2; split; [intros H_EQ | intros [H_LE H_GE]].
    - split; intros x; apply leProp_PartialOrder; exploit (H_EQ x) as H_EQ_x...
    - intros x; apply leProp_PartialOrder; split...
  Qed.

  Global Instance arrow_dom_cod_isPoset {cod_isPoset : isPoset cod} : isPoset (Hask.arrow dom cod) :=
    { leProp := arrow_leProp
    ; Poset_requiresSetoid := arrow_dom_cod_isSetoid
    ; leProp_PreOrder := arrow_leProp_PreOrder cod_isPoset
    ; leProp_PartialOrder := arrow_leProp_PartialOrder cod_isPoset
    }
  .

  End ImplFor_arrow.

  Section ImplFor_ensemble.

  Local Instance Prop_isSetoid : isSetoid Prop :=
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

  Definition ensemble (X : Hask.t) : Hask.t := Hask.arrow X Prop.

  Global Instance ensemble_isPoset (X : Hask.t) : isPoset (ensemble X) :=
    arrow_dom_cod_isPoset (dom := X) (cod := Prop) (cod_isPoset := Prop_isPoset)
  .

  Definition member {A : Hask.t} (x : A) (xs : ensemble A) : Prop := xs x.

  Definition isSubsetOf {A : Hask.t} (xs1 : ensemble A) (xs2 : ensemble A) : Prop :=
    forall x : A, member x xs1 -> member x xs2
  .

  Lemma isSubsetOf_iff {A : Hask.t} (xs1 : ensemble A) (xs2 : ensemble A)
    : isSubsetOf xs1 xs2 <-> xs1 =< xs2.
  Proof. reflexivity. Qed.

  End ImplFor_ensemble.

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

Module BasicMathematicalStructures.

  Import BasicCategoryTheory BasicTypeClasses BasicInstances.

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
      : (m0 >>= k1 >>= k2) == (m0 >>= fun x1 : A => k1 x1 >>= k2)
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
      (H_FST_ARG_EQ : m1 == m2)
      (k0 : kleisli M A B)
      : (m1 >>= k0) == (m2 >>= k0)
    ; bind_snd_arg {A : Hask.t} {B : Hask.t}
      (k1 : kleisli M A B)
      (k2 : kleisli M A B)
      (H_SND_ARG_EQ : k1 == k2)
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

End BasicMathematicalStructures.
