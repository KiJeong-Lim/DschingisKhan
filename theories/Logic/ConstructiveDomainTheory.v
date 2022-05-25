Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Math.BasicPosetTheory.

Module BasicCoLaTheory.

  Import MathProps MathClasses BasicPosetTheory DomainTheoryHelper.

  Local Existing Instances pair_isPoset arrow_isPoset.

  Global Hint Constructors _image _finite : poset_hints.

  Definition getInfimumOf_inCoLa {D : Type} {requiresPoset : isPoset D} {requiresCoLa : isCoLa D} (X : ensemble D) : {inf_X : D | isInfimumOf inf_X X} :=
    let inf_X : D := proj1_sig (getSupremumOf_inCoLa (LowerBoundsOf X)) in
    @exist D (fun inf : D => isInfimumOf inf X) inf_X (proj2 (SupremumOfLowerBounds_isInfimum inf_X X) (proj2_sig (getSupremumOf_inCoLa (LowerBoundsOf X))))
  .

  Definition MonotonicMaps (dom : Type) (cod : Type) {dom_requiresPoset : isPoset dom} {cod_requiresPoset : isPoset cod} : Type :=
    @sig (Hask.arrow dom cod) (fun f : dom -> cod => isMonotonicMap f)
  .

  Local Notation " ⟬ dom ⟶ cod ⟭ " := (MonotonicMaps dom cod) : type_scope.

  Local Instance MonotonicMaps_asPoset (dom : Type) (cod : Type) {dom_requiresPoset : isPoset dom} {cod_requiresPoset : isPoset cod} : isPoset ⟬ dom ⟶ cod ⟭ :=
    subPoset (Hask.arrow dom cod) (requiresPoset := arrow_isPoset cod_requiresPoset)
  .

  Definition supOfMonotonicMaps {dom : Type} {cod : Type} {dom_requiresPoset : isPoset dom} {cod_requiresPoset : isPoset cod} {dom_requiresCoLa : isCoLa dom} {cod_requiresCoLa : isCoLa cod} (fs : ensemble ⟬ dom ⟶ cod ⟭) : dom -> cod :=
    fun x : dom => proj1_sig (getSupremumOf_inCoLa (image (fun f_i : ⟬ dom ⟶ cod ⟭ => proj1_sig f_i x) fs))
  .

  Lemma supOfMonotonicMaps_proj2_sig {dom : Type} {cod : Type} {dom_requiresPoset : isPoset dom} {cod_requiresPoset : isPoset cod} {dom_requiresCoLa : isCoLa dom} {cod_requiresCoLa : isCoLa cod} (fs : ensemble ⟬ dom ⟶ cod ⟭)
    : forall x : dom, isSupremumOf (supOfMonotonicMaps fs x) (image (fun f_i : ⟬ dom ⟶ cod ⟭ => proj1_sig f_i x) fs).
  Proof. exact (fun x : dom => proj2_sig (getSupremumOf_inCoLa (image (fun f_i : ⟬ dom ⟶ cod ⟭ => proj1_sig f_i x) fs))). Qed.

  Lemma supOfMonotonicMaps_isMonotonicMap {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCoLa : isCoLa dom} {cod_isCoLa : isCoLa cod} (fs : ensemble ⟬ dom ⟶ cod ⟭)
    : isMonotonicMap (supOfMonotonicMaps fs).
  Proof.
    intros x x' x_le_x'. simpl. eapply supOfMonotonicMaps_proj2_sig with (x := x). red.
    intros y y_in. apply in_image_iff in y_in. destruct y_in as [f [y_eq f_in]]. subst y.
    transitivity (proj1_sig f x'); [eapply (proj2_sig f) | eapply supOfMonotonicMaps_proj2_sig with (x := x')]; eauto with *.
  Qed.

  Definition SupOfMonotonicMaps {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCoLa : isCoLa dom} {cod_isCoLa : isCoLa cod} (fs : ensemble ⟬ dom ⟶ cod ⟭) : ⟬ dom ⟶ cod ⟭ :=
    @exist (dom -> cod) isMonotonicMap (supOfMonotonicMaps fs) (supOfMonotonicMaps_isMonotonicMap fs)
  .

  Lemma SupOfMonotonicMaps_isSupremum {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCoLa : isCoLa dom} {cod_isCoLa : isCoLa cod}
    : forall fs : ensemble ⟬ dom ⟶ cod ⟭, isSupremumOf (SupOfMonotonicMaps fs) fs.
  Proof with eauto with *.
    unfold SupOfMonotonicMaps; intros fs f. split; intros ?; desnw.
    - intros f_i f_i_in. rewrite <- SUPREMUM_LE_UPPER_BOUND.
      intros x. simpl. eapply supOfMonotonicMaps_proj2_sig with (x := x)...
    - intros x. simpl. eapply supOfMonotonicMaps_proj2_sig with (x := x).
      intros y y_in. apply in_image_iff in y_in. destruct y_in as [f_i [y_eq f_i_in]]. subst y.
      revert x. change (f_i =< f)...
  Qed.

  Local Instance MonotonicMaps_asCoLa (dom : Type) (cod : Type) {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} {dom_isCoLa : isCoLa dom} {cod_isCoLa : isCoLa cod} : isCoLa ⟬ dom ⟶ cod ⟭ :=
    fun fs : ensemble ⟬ dom ⟶ cod ⟭ => @exist ⟬ dom ⟶ cod ⟭ (fun sup_fs : ⟬ dom ⟶ cod ⟭ => isSupremumOf sup_fs fs) (SupOfMonotonicMaps fs) (SupOfMonotonicMaps_isSupremum fs)
  .

  Lemma getLeastFixedPoint_inCoLa {D : Type} {requiresPoset : isPoset D} {requiresCoLa : isCoLa D} (f : D -> D)
    (f_isMonotonic : isMonotonicMap f)
    : {lfp_f : D | isInfimumOf lfp_f (PrefixedPoints f) /\ isLeastFixedPointOf lfp_f f}.
  Proof.
    assert (IS_INFIMUM : isInfimumOf (proj1_sig (getInfimumOf_inCoLa (PrefixedPoints f))) (PrefixedPoints f)) by exact (proj2_sig (getInfimumOf_inCoLa (PrefixedPoints f))).
    exists (proj1_sig (getInfimumOf_inCoLa (PrefixedPoints f))). split.
    - exact (IS_INFIMUM).
    - eapply theLeastFixedPointOfMonotonicMap.
      + exact (f_isMonotonic).
      + exact (IS_INFIMUM).
  Defined.

  Lemma getGreatestFixedPoint_inCoLa {D : Type} {requiresPoset : isPoset D} {requiresCoLa : isCoLa D} (f : D -> D)
    (f_isMonotonic : isMonotonicMap f)
    : {gfp_f : D | isSupremumOf gfp_f (PostfixedPoints f) /\ isGreatestFixedPointOf gfp_f f}.
  Proof.
    assert (IS_SUPREMUM : isSupremumOf (proj1_sig (getSupremumOf_inCoLa (PostfixedPoints f))) (PostfixedPoints f)) by exact (proj2_sig (getSupremumOf_inCoLa (PostfixedPoints f))).
    exists (proj1_sig (getSupremumOf_inCoLa (PostfixedPoints f))). split.
    - exact (IS_SUPREMUM).
    - eapply theGreatestFixedPointOfMonotonicMap.
      + exact (f_isMonotonic).
      + exact (IS_SUPREMUM).
  Defined.

  Definition nu {D : Type} {requiresPoset : isPoset D} {requiresCoLa : isCoLa D (requiresPoset := requiresPoset)} (f : ⟬ D ⟶ D ⟭) : {gfp_f : D | isGreatestFixedPointOf gfp_f (proj1_sig f)} :=
    let nu_f_proj1_sig : D := proj1_sig (getSupremumOf_inCoLa (PostfixedPoints (proj1_sig f))) in
    let IS_SUPREMUM : isSupremumOf nu_f_proj1_sig (PostfixedPoints (proj1_sig f)) := proj2_sig (getSupremumOf_inCoLa (PostfixedPoints (proj1_sig f))) in
    @exist D (fun gfp_f : D => isGreatestFixedPointOf gfp_f (proj1_sig f)) nu_f_proj1_sig (theGreatestFixedPointOfMonotonicMap (proj1_sig f) nu_f_proj1_sig (proj2_sig f) IS_SUPREMUM)
  .

  Corollary nu_isSupremumOf_PostfixedPoints {D : Type} {requiresPoset : isPoset D} {requiresCoLa : isCoLa D (requiresPoset := requiresPoset)} (f : ⟬ D ⟶ D ⟭)
    : isSupremumOf (proj1_sig (nu f)) (PostfixedPoints (proj1_sig f)).
  Proof. exact (proj2_sig (getSupremumOf_inCoLa (PostfixedPoints (proj1_sig f)))). Qed.

  Corollary nu_f_isGreatestFixedPointOf_f {D : Type} {requiresPoset : isPoset D} {requiresCoLa : isCoLa D (requiresPoset := requiresPoset)} (f : ⟬ D ⟶ D ⟭)
    : isGreatestFixedPointOf (proj1_sig (nu f)) (proj1_sig f).
  Proof. eapply theGreatestFixedPointOfMonotonicMap; [exact (proj2_sig f) | exact (nu_isSupremumOf_PostfixedPoints f)]. Qed.

  Section PACO_METATHEORY.

  Import ListNotations MathNotations.

  Class ExtraColaMethods (D : Type) {requiresPoset : isPoset D} : Type :=
    { cola_union (d_left : D) (d_right : D) : D
    ; cola_empty : D
    ; cola_union_spec (d_left : D) (d_right : D)
      : isSupremumOf (cola_union d_left d_right) (finite [d_left; d_right])
    ; cola_empty_spec
      : isSupremumOf (cola_empty) (empty)
    }
  .

  Context {D : Type} {requiresPoset : isPoset D}.

  Lemma le_cola_union_introl {hasExtraColaMethods : ExtraColaMethods D} (x1 : D) (x2 : D)
    : forall x : D, x =< x1 -> x =< cola_union x1 x2.
  Proof. intros x x_le; rewrite x_le. eapply cola_union_spec; eauto with *. Qed.

  Lemma le_cola_union_intror {hasExtraColaMethods : ExtraColaMethods D} (x1 : D) (x2 : D)
    : forall x : D, x =< x2 -> x =< cola_union x1 x2.
  Proof. intros x x_le; rewrite x_le. eapply cola_union_spec; eauto with *. Qed.

  Lemma cola_union_le_elim_l {hasExtraColaMethods : ExtraColaMethods D} (x1 : D) (x2 : D)
    : forall x : D, cola_union x1 x2 =< x -> x1 =< x.
  Proof. intros x le_x. apply cola_union_spec in le_x. eauto with *. Qed.

  Lemma cola_union_le_elim_r {hasExtraColaMethods : ExtraColaMethods D} (x1 : D) (x2 : D)
    : forall x : D, cola_union x1 x2 =< x -> x2 =< x.
  Proof. intros x le_x. apply cola_union_spec in le_x. eauto with *. Qed.

  Lemma cola_union_le_intro {hasExtraColaMethods : ExtraColaMethods D} (x1 : D) (x2 : D)
    : forall x : D, x1 =< x -> x2 =< x -> cola_union x1 x2 =< x.
  Proof.
    ii; eapply cola_union_spec. intros d d_in. apply in_finite_iff in d_in.
    destruct d_in as [d_eq_x1 | [d_eq_x2 | []]]; subst d; eauto with *.
  Qed.

  Lemma cola_empty_le_intro {hasExtraColaMethods : ExtraColaMethods D}
    : forall x : D, cola_empty =< x.
  Proof.
    ii; eapply cola_empty_spec. intros d d_in. apply in_empty_iff in d_in.
    destruct d_in as [].
  Qed.

  Local Hint Resolve le_cola_union_introl le_cola_union_intror cola_union_le_intro cola_empty_le_intro : core.

  Lemma PostfixedPoint_le_GreatestFixedPoint {requiresCoLa : isCoLa D} (f : ⟬ D ⟶ D ⟭) (x : D)
    (IS_POSTFIXEDPOINT : x =< proj1_sig f x)
    : x =< proj1_sig (nu f).
  Proof. eapply nu_isSupremumOf_PostfixedPoints; eauto with *. Qed.

  Lemma StrongCoinduction {requiresCoLa : isCoLa D} {hasExtraColaMethods : ExtraColaMethods D} (f : ⟬ D ⟶ D ⟭) (x : D)
    : x =< proj1_sig (nu f) <-> x =< proj1_sig f (cola_union x (proj1_sig (nu f))).
  Proof with eauto with *.
    assert (claim1 : proj1_sig f (proj1_sig (nu f)) =< proj1_sig f (cola_union x (proj1_sig (nu f)))).
    { eapply (proj2_sig f). eapply cola_union_spec... }
    pose proof (proj2_sig (nu f)) as [claim2 claim3]. split.
    - intros x_le. rewrite x_le at 1. transitivity (proj1_sig f (proj1_sig (nu f)))...
    - intros x_le. unnw. exploit (cola_union_le_intro x (proj1_sig (nu f)) _ x_le) as claim4.
      + do 2 red in claim2. rewrite claim2 at 1. eapply (proj2_sig f). eapply le_cola_union_intror...
      + rewrite x_le. eapply PostfixedPoint_le_GreatestFixedPoint. eapply (proj2_sig f)...
  Qed.

  Definition G_aux0 {hasExtraColaMethods : ExtraColaMethods D} (f : ⟬ D ⟶ D ⟭) (x : D) : D -> D :=
    fun y : D => proj1_sig f (cola_union x y)
  .

  Lemma G_aux0_isMonotionicMap {hasExtraColaMethods : ExtraColaMethods D} (f : ⟬ D ⟶ D ⟭) (x : D)
    : isMonotonicMap (G_aux0 f x).
  Proof.
    intros x1 x2 x1_le_x2. eapply (proj2_sig f).
    eapply cola_union_le_intro; [eapply le_cola_union_introl | rewrite x1_le_x2; eapply le_cola_union_intror]; eauto with *.
  Qed.

  Definition G_aux {hasExtraColaMethods : ExtraColaMethods D} (f : ⟬ D ⟶ D ⟭) (x : D) : ⟬ D ⟶ D ⟭ :=
    @exist (D -> D) isMonotonicMap (G_aux0 f x) (G_aux0_isMonotionicMap f x)
  .

  Context {requiresCoLa : isCoLa D} {hasExtraColaMethods : ExtraColaMethods D}.

  Definition G0 (f : ⟬ D ⟶ D ⟭) (x : D) : D := proj1_sig (nu (G_aux f x)).

  Lemma G0_isMonotonicMap (f : ⟬ D ⟶ D ⟭)
    : isMonotonicMap (G0 f).
  Proof with eauto with *.
    intros x1 x2 x1_le_x2. eapply StrongCoinduction. simpl in *.
    assert (claim1 : G0 f x1 == proj1_sig f (cola_union x1 (G0 f x1))) by eapply (proj2_sig (nu (G_aux f x1))).
    rewrite claim1 at 1. eapply (proj2_sig f). transitivity (cola_union x2 (G0 f x1)).
    - eapply cola_union_le_intro.
      + rewrite x1_le_x2 at 1. eapply le_cola_union_introl...
      + eapply le_cola_union_intror...
    - eapply cola_union_le_intro...
  Qed.

  Definition G1 (f : ⟬ D ⟶ D ⟭) : ⟬ D ⟶ D ⟭ := @exist (D -> D) isMonotonicMap (G0 f) (G0_isMonotonicMap f).

  Lemma G1_isMontonicMap
    : isMonotonicMap G1.
  Proof.
    intros f1 f2 f1_le_f2 x0. simpl. unfold G0.
    pose proof (nu_isSupremumOf_PostfixedPoints (G_aux f1 x0)) as claim1.
    pose proof (nu_isSupremumOf_PostfixedPoints (G_aux f2 x0)) as claim2.
    eapply claim1. ii; desnw. do 2 red in H_IN. eapply claim2; eauto with *.
    do 3 red. revert H_IN. unfold G_aux, G_aux0. simpl. intros x_le.
    rewrite x_le at 1. eapply f1_le_f2.
  Qed.

  Definition G : ⟬ ⟬ D ⟶ D ⟭ ⟶ ⟬ D ⟶ D ⟭ ⟭ :=
    @exist (⟬ D ⟶ D ⟭ -> ⟬ D ⟶ D ⟭) isMonotonicMap G1 G1_isMontonicMap
  .

  Variant ParameterizedGreatestFixedPointSpec (f : ⟬ D ⟶ D ⟭) (G_f : ⟬ D ⟶ D ⟭) : Prop :=
  | verifyParameterizedGreatestFixedPointSpec
    (INIT_COFIXPOINT : proj1_sig (nu f) == proj1_sig G_f cola_empty)
    (UNFOLD_COFIXPOINT : forall x : D, proj1_sig G_f x == proj1_sig f (cola_union x (proj1_sig G_f x)))
    (ACCUM_COFIXPOINT : forall x : D, forall y : D, y =< proj1_sig G_f x <-> y =< proj1_sig G_f (cola_union x y))
    : ParameterizedGreatestFixedPointSpec f G_f
  .

  Theorem G_specification (f : ⟬ D ⟶ D ⟭)
    : ParameterizedGreatestFixedPointSpec f (proj1_sig G f).
  Proof with eauto with *.
    pose proof (nu_isSupremumOf_PostfixedPoints (G_aux f cola_empty)) as claim1.
    pose proof (nu_isSupremumOf_PostfixedPoints f) as claim2.
    pose proof (fun x : D => proj1 (nu_f_isGreatestFixedPointOf_f (G_aux f x))) as claim3.
    split.
    - eapply leProp_Antisymmetric.
      + eapply claim2. ii; desnw. eapply claim1...
        do 3 red. do 2 red in H_IN. rewrite H_IN at 1. eapply (proj2_sig f)...
      + eapply claim1. ii; desnw. eapply claim2...
        do 3 red. do 2 red in H_IN. rewrite H_IN at 1. eapply (proj2_sig f)...
    - exact (claim3).
    - iis; intros y_le.
      + rewrite y_le at 1. eapply G0_isMonotonicMap...
      + rewrite y_le at 1. eapply PostfixedPoint_le_GreatestFixedPoint.
        transitivity (proj1_sig f (cola_union (cola_union x y) (proj1_sig (proj1_sig G f) (cola_union x y)))).
        { eapply eqProp_implies_leProp. exact (claim3 (cola_union x y)). }
        { eapply (proj2_sig f). eapply cola_union_le_intro... }
  Qed.

  Theorem G_compositionality (f : ⟬ D ⟶ D ⟭) (r : D) (r1 : D) (r2 : D) (g1 : D) (g2 : D)
    (g1_le_G_f_r1 : g1 =< proj1_sig (proj1_sig G f) r1)
    (g2_le_G_f_r2 : g2 =< proj1_sig (proj1_sig G f) r2)
    (r1_le : r1 =< cola_union r g2)
    (r2_le : r2 =< cola_union r g1)
    : cola_union g1 g2 =< proj1_sig (proj1_sig G f) r.
  Proof with eauto with *.
    assert (claim1 : g1 =< proj1_sig (proj1_sig G f) (cola_union r (cola_union g1 g2))).
    { rewrite g1_le_G_f_r1 at 1. eapply G0_isMonotonicMap. rewrite r1_le. eapply cola_union_le_intro... }
    assert (claim2 : g2 =< proj1_sig (proj1_sig G f) (cola_union r (cola_union g1 g2))).
    { rewrite g2_le_G_f_r2 at 1. eapply G0_isMonotonicMap. rewrite r2_le. eapply cola_union_le_intro... }
    pose proof (G_specification f) as [? ? ?]. eapply ACCUM_COFIXPOINT...
  Qed.

  Theorem G_characterization (f : ⟬ D ⟶ D ⟭) (G_f : ⟬ D ⟶ D ⟭)
    (G_f_spec : ParameterizedGreatestFixedPointSpec f G_f)
    : G_f == proj1_sig G f.
  Proof with eauto with *. (* Thanks to SoonWon Moon *)
    destruct G_f_spec as [INIT_COFIXPOINT' UNFOLD_COFIXPOINT' ACCUM_COFIXPOINT'].
    assert (claim1 : forall x : D, proj1_sig G_f x =< proj1_sig (proj1_sig G f) x).
    { ii. eapply PostfixedPoint_le_GreatestFixedPoint... }
    pose proof (G_specification f) as [? ? ?].
    assert (claim2 : forall x : D, proj1_sig (proj1_sig G f) x =< proj1_sig G_f (cola_union x (proj1_sig (proj1_sig G f) x))).
    { ii. rewrite UNFOLD_COFIXPOINT with (x := x) at 1. rewrite UNFOLD_COFIXPOINT'. eapply (proj2_sig f). eapply cola_union_le_intro... }
    ii. eapply leProp_Antisymmetric.
    - eapply claim1.
    - eapply ACCUM_COFIXPOINT'...
  Qed.

  End PACO_METATHEORY.

  Lemma CoinductionPrinciple {D : Type} {requiresPoset : isPoset D} {requiresCoLa : isCoLa D} (b : ⟬ D ⟶ D ⟭)
    : forall x : D, x =< proj1_sig (nu b) <-> << COIND : exists y : D, x =< y /\ y =< proj1_sig b y >>.
  Proof.
    pose proof (nu_f_isGreatestFixedPointOf_f b) as [claim1 claim2].
    pose proof (nu_isSupremumOf_PostfixedPoints b) as claim3.
    unnw. iis.
    - intros x_le_nu_b. exists (proj1_sig (nu b)). split; trivial.
      eapply eqProp_implies_leProp, claim1.
    - intros [y [x_le_y y_le_b_y]]. rewrite x_le_y.
      eapply claim3; eauto with *.
  Qed.

  Theorem KnasterTarski {D : Type} {requiresPoset : isPoset D} {requiresCoLa : isCoLa D} (f : ⟬ D ⟶ D ⟭) (W : ensemble D)
    (W_is_a_set_of_fixed_points_of_f : isSubsetOf W (FixedPoints (proj1_sig f)))
    : {fix_f : D | isSupremumIn fix_f W (FixedPoints (proj1_sig f))}.
  Proof with eauto with *. (* Referring to "https://www.cs.utexas.edu/users/misra/Notes.dir/KnasterTarski.pdf" written by Jayadev Misra *)
    pose proof (getSupremumOf_inCoLa W) as [q q_is_lub_of_W].
    keep (fun w : D => q =< w) as W_hat into (ensemble D).
    assert (q_is_glb_of_W_hat : isInfimumOf q W_hat) by exact (Supremum_isInfimumOf_itsUpperBounds W q q_is_lub_of_W).
    assert (q_in_W_hat : member q W_hat) by exact (leProp_Reflexive q).
    assert (W_hat_closed_under_f : forall x : D, member x W_hat -> member (proj1_sig f x) W_hat).
    { intros x q_le_x. eapply q_is_lub_of_W.
      intros w w_in_W. transitivity (proj1_sig f w).
      - eapply eqProp_implies_leProp, W_is_a_set_of_fixed_points_of_f...
      - eapply (proj2_sig f). transitivity (q); trivial. eapply q_is_lub_of_W...
    }
    assert (q_le_f_q : q =< proj1_sig f q) by exact (W_hat_closed_under_f q q_in_W_hat).
    pose proof (getInfimumOf_inCoLa (intersection (PrefixedPoints (proj1_sig f)) W_hat)) as [fix_f fix_f_isInfimum].
    enough (claim1 : proj1_sig f fix_f =< fix_f).
    enough (claim2 : q =< fix_f).
    enough (claim3 : fix_f == proj1_sig f fix_f).
    - exists (fix_f). split; unnw.
      + exact (claim3).
      + intros [x x_in]. simpl. split.
        { intros fix_f_le_x d d_in. transitivity (q).
          - eapply q_is_lub_of_W...
          - transitivity (fix_f)...
        }
        { intros x_is_upper_bound_of_W. eapply fix_f_isInfimum... split.
          - eapply eqProp_implies_leProp. now symmetry.
          - eapply q_is_lub_of_W...
        }
    - eapply leProp_Antisymmetric; trivial.
      eapply fix_f_isInfimum... eapply in_intersection_iff.
      split; [eapply (proj2_sig f) | eapply W_hat_closed_under_f]... 
    - eapply fix_f_isInfimum. ii; desnw.
      apply in_intersection_iff in H_IN. destruct H_IN as [f_x_le_x q_le_x]...
    - eapply fix_f_isInfimum. intros x x_in.
      apply in_intersection_iff in x_in. destruct x_in as [f_x_le_x q_le_x].
      do 2 red in f_x_le_x. rewrite <- f_x_le_x. eapply (proj2_sig f).
      eapply fix_f_isInfimum... eapply in_intersection_iff...
  Qed.

  Corollary FixedPoints_asCoLa {D : Type} {requiresPoset : isPoset D} {requiresCoLa : isCoLa D} (f : ⟬ D ⟶ D ⟭)
    : isCoLa (@sig D (FixedPoints (proj1_sig f))) (requiresPoset := subPoset D).
  Proof.
    intros X.
    assert (claim1 : isSubsetOf (image (@proj1_sig D (FixedPoints (proj1_sig f))) X) (FixedPoints (proj1_sig f))).
    { intros z z_in. apply in_image_iff in z_in. destruct z_in as [[x x_eq_f_x] [z_eq x_in]].
      subst z; simpl in *. exact (x_eq_f_x).
    }
    pose proof (KnasterTarski f (image (@proj1_sig D (FixedPoints (proj1_sig f))) X) claim1) as [sup_X IS_SUPREMUM].
    exists (@exist D (fun x : D => FixedPoints (proj1_sig f) x) sup_X (proj1 IS_SUPREMUM)).
    rewrite <- isSupremumIn_iff. exact (IS_SUPREMUM).
  Qed.

End BasicCoLaTheory.

Module ParameterizedCoinduction. (* Reference: "The Power of Parameterization in Coinductive Proof" *)

  Import ListNotations MathProps MathClasses BasicPosetTheory BasicCoLaTheory.

  Local Existing Instances pair_isPoset arrow_isPoset MonotonicMaps_asPoset MonotonicMaps_asCoLa.

  Section PACO_implementation.

  Context {A : Type}.

  Lemma cola_union_spec_forEnsembles (X1 : ensemble A) (X2 : ensemble A)
    : isSupremumOf (@union A X1 X2) (finite [X1; X2]).
  Proof.
    iis.
    - intros H_SUBSET X X_in. apply in_finite_iff in X_in. destruct X_in as [X_eq | [X_eq | []]]; subst X.
      + intros x x_in; eapply H_SUBSET. left; trivial.
      + intros x x_in; eapply H_SUBSET. right; trivial.
    - intros H_IN x x_in. apply in_union_iff in x_in. destruct x_in as [x_in | x_in].
      + eapply H_IN with (x := X1); trivial. eapply in_finite_iff. simpl. tauto.
      + eapply H_IN with (x := X2); trivial. eapply in_finite_iff. simpl. tauto.
  Qed.

  Lemma cola_empty_spec_forEnsembles
    : isSupremumOf (@empty A) empty.
  Proof.
    iis.
    - intros H_SUBSET X X_in. inversion X_in.
    - intros H_IN x x_in. inversion x_in.
  Qed.

  Global Instance ensemble_hasExtraColaMethods : ExtraColaMethods (ensemble A) :=
    { cola_union := union
    ; cola_empty := empty
    ; cola_union_spec := cola_union_spec_forEnsembles
    ; cola_empty_spec := cola_empty_spec_forEnsembles
    }
  .

  Let D : Type := ensemble A.

  Variant paco' {paco_F : D -> D} (F : D -> D) (X : D) : D :=
  | mk_paco' (WITNESS : D)
    (INCL : isSubsetOf WITNESS (cola_union (paco_F X) X))
    : isSubsetOf (F WITNESS) (paco' F X)
  .

  Set Primitive Projections.

  CoInductive paco (F : D -> D) (X : D) (x : A) : Prop :=
    Fold_paco { unfold_paco : member x (paco' (paco_F := paco F) F X) }
  .

  Unset Primitive Projections.

  End PACO_implementation.

  Global Arguments paco' {A} (paco_F) (F) (X).
  Global Arguments paco {A} (F) (X) (x).

  Section PACO_theory.

  Context {A : Type}.

  End PACO_theory.

End ParameterizedCoinduction.
