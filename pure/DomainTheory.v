Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module ConstructiveCoLaTheory. (* Reference: "The Power of Parameterization in Coinductive Proof" *)

  Import ListNotations MyUtilities BasicSetoidTheory MyEnsemble BasicPosetTheory.

  Global Program Instance DirectProductOfSetoid {D : Type} {D' : Type} (D_requiresSetoid : isSetoid D) (D'_requiresSetoid : isSetoid D') : isSetoid (D * D') :=
    { eqProp :=
      fun p1 : D * D' =>
      fun p2 : D * D' =>
      fst p1 == fst p2 /\ snd p1 == snd p2
    }
  .

  Next Obligation with eauto with *.
    split.
    - intros [x1 y1]...
    - intros [x1 y1] [x2 y2] [H H0]...
    - intros [x1 y1] [x2 y2] [x3 y3] [H H0] [H1 H2]...
  Qed.

  Global Program Instance DirectProductOfPoset {D : Type} {D' : Type} (D_requiresPoset : isPoset D) (D'_requiresPoset : isPoset D') : isPoset (D * D') :=
    { leProp :=
      fun p1 : D * D' =>
      fun p2 : D * D' =>
      fst p1 =< fst p2 /\ snd p1 =< snd p2
    ; Poset_requiresSetoid := DirectProductOfSetoid (@Poset_requiresSetoid D D_requiresPoset) (@Poset_requiresSetoid D' D'_requiresPoset)
    }
  .

  Next Obligation with eauto with *.
    split.
    - intros [x1 y1]...
    - intros [x1 y1] [x2 y2] [x3 y3] [H H0] [H1 H2]...
  Qed.

  Next Obligation with firstorder with my_hints.
    intros [x1 y1] [x2 y2]...
  Qed.

  Class isCompleteLattice {D : Type} (D_isPoset : isPoset D) : Type :=
    { supremum_always_exists_in_CompleteLattice :
      forall X : ensemble D,
      {sup_X : D | isSupremum sup_X X}
    }
  .

  Definition infimum_always_exists_in_CompleteLattice {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : forall X : ensemble D, {inf_X : D | isInfimum inf_X X} :=
    fun X : ensemble D =>
    match supremum_always_exists_in_CompleteLattice (fun d : D => forall x : D, member x X -> d =< x) with
    | exist _ inf_X inf_X_isInfimum_X => exist _ inf_X (compute_Infimum X inf_X inf_X_isInfimum_X)
    end
  .

  Global Instance fish_isPoset {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} (D_requiresCompleteLattice : isCompleteLattice D_isPoset) (D'_requiresCompleteLattice : isCompleteLattice D'_isPoset) : isPoset (D >=> D') :=
    @SubPoset (D -> D') (@isMonotonicMap D D' D_isPoset D'_isPoset) (arrow_isPoset D'_isPoset)
  .

  Lemma const_isMonotonic {D : Type} `{D_isPoset : isPoset D} :
    forall d : D,
    isMonotonicMap (const d).
  Proof with eauto with *.
    unfold isMonotonicMap...
  Qed.

  Definition const_m {D : Type} `{D_isPoset : isPoset D} : D -> (D >=> D) :=
    fun d : D =>
    exist isMonotonicMap (const d) (const_isMonotonic d)
  .

  Lemma id_isMonotonic {D1 : Type} `{D1_isPoset : isPoset D1} :
    isMonotonicMap (fun x : D1 => x).
  Proof with eauto with *.
    unfold isMonotonicMap...
  Qed.

  Definition id_m {D1 : Type} `{D1_isPoset : isPoset D1} : D1 >=> D1 :=
    exist isMonotonicMap (fun x : D1 => x) id_isMonotonic
  .

  Lemma compose_isMonotonic {D1 : Type} {D2 : Type} {D3 : Type} {D1_isPoset : isPoset D1} {D2_isPoset : isPoset D2} {D3_isPoset : isPoset D3} :
    forall f : D1 -> D2,
    isMonotonicMap f ->
    forall g : D2 -> D3,
    isMonotonicMap g ->
    isMonotonicMap (fun x : D1 => g (f x)).
  Proof with eauto with *.
    unfold isMonotonicMap...
  Qed.

  Definition compose_m {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} : (D2 >=> D3) -> (D1 >=> D2) -> (D1 >=> D3) :=
    fun g : D2 >=> D3 =>
    fun f : D1 >=> D2 =>
    exist isMonotonicMap (fun x : D1 => proj1_sig g (proj1_sig f x)) (compose_isMonotonic (proj1_sig f) (proj2_sig f) (proj1_sig g) (proj2_sig g))
  .

  Definition supOfMonotonicMaps {D : Type} {D' : Type} `{D_isCompleteLattice : isCompleteLattice D} `{D'_isCompleteLattice : isCompleteLattice D'} : ensemble (D >=> D') -> D -> D' :=
    fun fs : ensemble (D >=> D') =>
    fun x : D =>
    proj1_sig (supremum_always_exists_in_CompleteLattice (image (fun f_i : D >=> D' => proj1_sig f_i x) fs))
  .

  Lemma supOfMonotonicMaps_isMonotonic {D : Type} {D' : Type} `{D_isCompleteLattice : isCompleteLattice D} `{D'_isCompleteLattice : isCompleteLattice D'} :
    forall fs : ensemble (D >=> D'),
    isMonotonicMap (supOfMonotonicMaps fs).
  Proof with eauto with *.
    intros fs x1 x2 H.
    unfold supOfMonotonicMaps.
    destruct (supremum_always_exists_in_CompleteLattice (image (fun f_i : D >=> D' => proj1_sig f_i x1) fs)) as [sup1 H0].
    destruct (supremum_always_exists_in_CompleteLattice (image (fun f_i : D >=> D' => proj1_sig f_i x2) fs)) as [sup2 H1].
    simpl.
    apply H0.
    intros x H2.
    inversion H2; subst.
    rename x0 into f_i.
    transitivity (proj1_sig f_i x2).
    - apply (proj2_sig f_i)...
    - apply H1...
  Qed.

  Definition supremum_m {D : Type} {D' : Type} `{D_isCompleteLattice : isCompleteLattice D} `{D'_isCompleteLattice : isCompleteLattice D'} : ensemble (D >=> D') -> (D >=> D') :=
    fun F : ensemble (D >=> D') =>
    exist isMonotonicMap (supOfMonotonicMaps F) (supOfMonotonicMaps_isMonotonic F)
  .

  Lemma supOfMonotonicMaps_isSupremum {D : Type} {D' : Type} `{D_isCompleteLattice : isCompleteLattice D} `{D'_isCompleteLattice : isCompleteLattice D'} :
    forall fs : ensemble (D >=> D'),
    isSupremum (supremum_m fs) fs.
  Proof with eauto with *.
    unfold supremum_m.
    intros fs f.
    split.
    - intros H0 f' H1.
      assert (claim1 : f' =< exist isMonotonicMap (supOfMonotonicMaps fs) (supOfMonotonicMaps_isMonotonic fs)).
      { intros x.
        simpl.
        apply (proj2_sig (supremum_always_exists_in_CompleteLattice (image (fun f_i : D >=> D' => proj1_sig f_i x) fs)))...
      }
      transitivity (exist isMonotonicMap (supOfMonotonicMaps fs) (supOfMonotonicMaps_isMonotonic fs))...
    - intros H x.
      simpl.
      assert (claim2 : forall x' : D', member x' (image (fun f_i : D >=> D' => proj1_sig f_i x) fs) -> x' =< proj1_sig f x).
      { intros x' H0.
        inversion H0; subst.
        rename x0 into f'.
        apply (H f' H1 x)...
      }
      apply (proj2_sig (supremum_always_exists_in_CompleteLattice (image (fun f_i : D >=> D' => proj1_sig f_i x) fs)))...
  Qed.

  Local Instance MonotonicMaps_on_CompleteLattice_constitute_CompleteLattice {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} (D_requiresCompleteLattice : @isCompleteLattice D D_isPoset) (D'_requiresCompleteLattice : @isCompleteLattice D' D'_isPoset) : @isCompleteLattice (D >=> D') (fish_isPoset D_requiresCompleteLattice D'_requiresCompleteLattice) :=
    { supremum_always_exists_in_CompleteLattice :=
      fun fs : ensemble (D >=> D') =>
      exist (fun sup_fs : D >=> D' => isSupremum sup_fs fs) (supremum_m fs) (supOfMonotonicMaps_isSupremum fs)
    }
  .

  Lemma LeastFixedPointInCompleteLattice {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D -> D,
    isMonotonicMap f ->
    exists lfp : D, isInfimum lfp (prefixed_points f) /\ isLeastFixedPoint lfp f.
  Proof with eauto with *.
    intros f H.
    destruct (infimum_always_exists_in_CompleteLattice (prefixed_points f)) as [lfp H0].
    exists lfp.
    split...
    apply LeastFixedPointOfMonotonicMaps...
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
    split.
    - assert (H1 : gfp =< f gfp).
      { apply H0.
        intros x H1.
        transitivity (f x)...
      }
      apply Poset_asym.
      + apply H1.
      + apply H0...
    - intros fix_f H1...
  Qed.

  Lemma GreatestFixedPointInCompleteLattice {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D -> D,
    isMonotonicMap f ->
    exists gfp : D, isSupremum gfp (postfixed_points f) /\ isGreatestFixedPoint gfp f.
  Proof with eauto with *.
    intros f H.
    destruct (supremum_always_exists_in_CompleteLattice (postfixed_points f)) as [gfp H0].
    exists gfp.
    split...
    apply GreatestFixedPointOfMonotonicMaps...
  Qed.

  Definition nu {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : forall f : D >=> D, {gfp : D | isGreatestFixedPoint gfp (proj1_sig f)} :=
    fun f : D >=> D =>
    match supremum_always_exists_in_CompleteLattice (postfixed_points (proj1_sig f)) with
    | exist _ gfp H => exist _ gfp (GreatestFixedPointOfMonotonicMaps (proj1_sig f) (proj2_sig f) gfp H)
    end
  .

  Lemma nu_isSupremum {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >=> D,
    isSupremum (proj1_sig (nu f)) (postfixed_points (proj1_sig f)).
  Proof with eauto with *.
    unfold nu.
    intros f.
    destruct (supremum_always_exists_in_CompleteLattice (postfixed_points (proj1_sig f))) as [gfp H]...
  Qed.

  Definition or_plus {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : D -> D -> D :=
    fun x1 : D =>
    fun x2 : D =>
    proj1_sig (supremum_always_exists_in_CompleteLattice (finite [x1; x2]))
  .

  Lemma le_or_plus {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall x1 : D,
    forall x2 : D,
    x1 =< or_plus x1 x2 /\ x2 =< or_plus x1 x2.
  Proof with eauto with *.
    intros x1 x2.
    assert (H : isSupremum (or_plus x1 x2) (finite [x1; x2])) by apply (proj2_sig (supremum_always_exists_in_CompleteLattice (finite [x1; x2]))).
    split...
  Qed.

  Lemma le_or_plus_intro1 {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall x1 : D,
    forall x2 : D,
    x1 =< or_plus x1 x2.
  Proof.
    apply le_or_plus.
  Qed.

  Global Hint Resolve le_or_plus_intro1 : my_hints.

  Lemma le_or_plus_intro2 {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall x1 : D,
    forall x2 : D,
    x2 =< or_plus x1 x2.
  Proof.
    apply le_or_plus.
  Qed.

  Global Hint Resolve le_or_plus_intro2 : my_hints.

  Lemma or_plus_le_iff {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall x1 : D,
    forall x2 : D,
    forall d : D,
    or_plus x1 x2 =< d <-> (x1 =< d /\ x2 =< d).
  Proof with eauto with *.
    intros x1 x2 d.
    assert (H : isSupremum (or_plus x1 x2) (finite [x1; x2])) by apply (proj2_sig (supremum_always_exists_in_CompleteLattice (finite [x1; x2]))).
    split.
    - intros H0.
      split...
    - intros [H0 H1].
      apply H.
      intros x H2.
      inversion H2; subst.
      destruct H3 as [H3 | [H3 | []]]; subst...
  Qed.

  Lemma PrincipleOfTarski {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >=> D,
    forall x : D,
    x =< proj1_sig f x ->
    x =< proj1_sig (nu f).
  Proof with eauto with *.
    intros f.
    assert (claim1 := nu_isSupremum f)...
  Qed.

  Lemma StrongCoinduction {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >=> D,
    forall x : D,
    x =< proj1_sig (nu f) <-> x =< proj1_sig f (or_plus x (proj1_sig (nu f))).
  Proof with eauto with *.
    intros f.
    destruct (proj2_sig (nu f)) as [H H0].
    assert (claim1 : forall x : D, proj1_sig f (proj1_sig (nu f)) =< proj1_sig f (or_plus x (proj1_sig (nu f)))).
    { intros x.
      apply (proj2_sig f)...
    }
    intros x.
    split.
    - intros H1.
      transitivity (proj1_sig (nu f))...
    - intros H1.
      enough (claim2 : or_plus x (proj1_sig (nu f)) =< proj1_sig f (or_plus x (proj1_sig (nu f)))).
      { transitivity (proj1_sig f (or_plus x (proj1_sig (nu f)))).
        - apply H1.
        - apply PrincipleOfTarski, (proj2_sig f)... 
      }
      apply or_plus_le_iff...
  Qed.

  Example G_f_aux_isMonotonic {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >=> D,
    forall x : D,
    isMonotonicMap (fun y : D => proj1_sig f (or_plus x y)).
  Proof with eauto with *.
    intros f d x1 x2 H.
    apply (proj2_sig f), or_plus_le_iff...
  Qed.

  Definition G_f {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : (D >=> D) -> (D -> D) :=
    fun f : D >=> D =>
    let G_f_aux : D -> D -> D := fun x : D => fun y : D => proj1_sig f (or_plus x y) in
    fun x : D =>
    proj1_sig (nu (exist isMonotonicMap (G_f_aux x) (G_f_aux_isMonotonic f x)))
  .

  Lemma G_f_isMonotoinc {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >=> D,
    isMonotonicMap (G_f f).
  Proof with eauto with *.
    intros f.
    set (G_f_aux := fun x : D => fun y : D => proj1_sig f (or_plus x y)).
    intros x1 x2 H.
    apply StrongCoinduction.
    assert (claim1 := nu_isSupremum f).
    simpl in *.
    assert (claim2 : G_f f x1 == proj1_sig f (or_plus x1 (G_f f x1))) by apply (proj2_sig (nu (exist _ (G_f_aux x1) (G_f_aux_isMonotonic f x1)))).
    transitivity (proj1_sig f (or_plus x1 (G_f f x1))).
    - apply Poset_refl1...
    - apply (proj2_sig f).
      transitivity (or_plus x2 (G_f f x1)); apply or_plus_le_iff...
  Qed.

  Definition ParameterizedGreatestFixedpoint {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : (D >=> D) -> (D >=> D) :=
    fun f : D >=> D =>
    exist isMonotonicMap (G_f f) (G_f_isMonotoinc f)
  .

  Lemma ParameterizedGreatestFixedpoint_isMonotonic {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    isMonotonicMap ParameterizedGreatestFixedpoint.
  Proof with eauto with *.
    intros f1 f2 H x.
    simpl.
    unfold G_f.
    assert (claim1 := nu_isSupremum (exist isMonotonicMap (fun y : D => proj1_sig f1 (or_plus x y)) (G_f_aux_isMonotonic f1 x))).
    assert (claim2 := nu_isSupremum (exist isMonotonicMap (fun y : D => proj1_sig f2 (or_plus x y)) (G_f_aux_isMonotonic f2 x))).
    apply claim1...
  Qed.

  Definition bot {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : D :=
    proj1_sig (supremum_always_exists_in_CompleteLattice (finite []))
  .

  Lemma bot_isBottom {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall x : D,
    bot =< x.
  Proof with easy.
    intros x.
    apply (proj2_sig (supremum_always_exists_in_CompleteLattice (finite []))).
    intros x' H.
    inversion H; subst...
  Qed.

  Global Hint Resolve bot_isBottom : my_hints.

  Lemma initialize_cofixpoint {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >=> D,
    proj1_sig (nu f) == proj1_sig (ParameterizedGreatestFixedpoint f) bot.
  Proof with eauto with *.
    intros f.
    symmetry.
    unfold ParameterizedGreatestFixedpoint, G_f.
    assert (H := nu_isSupremum (exist isMonotonicMap (fun y : D => proj1_sig f (or_plus bot y)) (G_f_aux_isMonotonic f bot))).
    assert (H0 := nu_isSupremum f).
    simpl in *.
    apply Poset_asym.
    - apply H.
      intros x H1.
      apply H0...
      unfold member, postfixed_points in *.
      transitivity (proj1_sig f (or_plus bot x)).
      + apply H1.
      + apply (proj2_sig f), or_plus_le_iff...
    - apply H0.
      intros x H1.
      apply H...
      unfold member, postfixed_points in *.
      transitivity (proj1_sig f x).
      + apply H1.
      + apply (proj2_sig f)...
  Qed.

  Lemma unfold_cofixpoint {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >=> D,
    forall x : D,
    proj1_sig (ParameterizedGreatestFixedpoint f) x == proj1_sig f (or_plus x (proj1_sig (ParameterizedGreatestFixedpoint f) x)).
  Proof with eauto with *.
    intros f x.
    unfold ParameterizedGreatestFixedpoint.
    simpl.
    unfold G_f.
    assert (H := nu_isSupremum (exist isMonotonicMap (fun y : D => proj1_sig f (or_plus x y)) (G_f_aux_isMonotonic f x))).
    simpl in *.
    apply (GreatestFixedPointOfMonotonicMaps (fun y : D => proj1_sig f (or_plus x y)) (G_f_aux_isMonotonic f x))...
  Qed.

  Lemma accumulate_cofixpoint {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >=> D,
    forall x : D,
    forall y : D,
    y =< proj1_sig (ParameterizedGreatestFixedpoint f) x <-> y =< proj1_sig (ParameterizedGreatestFixedpoint f) (or_plus x y).
  Proof with eauto with *.
    unfold ParameterizedGreatestFixedpoint.
    simpl.
    intros f.
    split.
    - intros H.
      transitivity (G_f f x).
      + apply H.
      + apply G_f_isMonotoinc...
    - intros H.
      assert (claim1 : proj1_sig (ParameterizedGreatestFixedpoint f) (or_plus x y) == proj1_sig f (or_plus (or_plus x y) (G_f f (or_plus x y)))) by now apply unfold_cofixpoint.
      assert (claim2 : proj1_sig f (or_plus (or_plus x y) (G_f f (or_plus x y))) =< proj1_sig f (or_plus x (G_f f (or_plus x y)))).
      { apply (proj2_sig f), or_plus_le_iff.
        split; [apply or_plus_le_iff | apply le_or_plus]...
      }
      assert (claim3 : G_f f (or_plus x y) =< G_f f x).
      { apply PrincipleOfTarski.
        simpl.
        transitivity (proj1_sig f (or_plus (or_plus x y) (G_f f (or_plus x y))))...
      }
      transitivity (G_f f (or_plus x y))...
  Qed.

  Theorem Compositionality_of_ParameterizedCoinduction {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >=> D,
    forall r : D,
    forall r1 : D,
    forall r2 : D,
    forall g1 : D,
    forall g2 : D,
    g1 =< G_f f r1 ->
    g2 =< G_f f r2 ->
    r1 =< or_plus r g2 ->
    r2 =< or_plus r g1 ->
    or_plus g1 g2 =< G_f f r.
  Proof with eauto with *.
    intros f r r1 r2 g1 g2 H H0 H1 H2.
    assert (H3 : g1 =< G_f f (or_plus r (or_plus g1 g2))).
    { transitivity (G_f f r1).
      - apply H.
      - apply G_f_isMonotoinc.
        transitivity (or_plus r g2); [apply H1 | apply or_plus_le_iff]...
    }
    assert (H4 : g2 =< G_f f (or_plus r (or_plus g1 g2))).
    { transitivity (G_f f r2).
      - apply H0.
      - apply G_f_isMonotoinc.
        transitivity (or_plus r g1); [apply H2 | apply or_plus_le_iff]...
    }
    assert (H5 : or_plus g1 g2 =< G_f f (or_plus r (or_plus g1 g2))) by now apply or_plus_le_iff.
    apply accumulate_cofixpoint...
  Qed.

  Lemma FullCharacterization_of_ParameterizedGreatestFixedPoint {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >=> D,
    forall G_f' : D >=> D,
    (forall x : D, proj1_sig G_f' x == proj1_sig f (or_plus x (proj1_sig G_f' x))) ->
    (forall x : D, forall y : D, y =< proj1_sig G_f' (or_plus x y) -> y =< proj1_sig G_f' x) ->
    (G_f' == ParameterizedGreatestFixedpoint f).
  Proof with eauto with *. (* Thanks to SoonWon *)
    intros f G_f' H H0.
    assert (claim1 : forall x : D, proj1_sig G_f' x =< proj1_sig (ParameterizedGreatestFixedpoint f) x).
    { intros x.
      apply PrincipleOfTarski.
      simpl...
    }
    assert (claim2 := unfold_cofixpoint f).
    assert (claim3 : forall x : D, proj1_sig (ParameterizedGreatestFixedpoint f) x =< proj1_sig G_f' (or_plus x (proj1_sig (ParameterizedGreatestFixedpoint f) x))).
    { intros x.
      transitivity (proj1_sig f (or_plus x (proj1_sig (ParameterizedGreatestFixedpoint f) x))).
      - apply Poset_refl1, unfold_cofixpoint.
      - assert (H1 := H (or_plus x (proj1_sig (ParameterizedGreatestFixedpoint f) x))).
        transitivity (proj1_sig f (or_plus (or_plus x (proj1_sig (ParameterizedGreatestFixedpoint f) x)) (proj1_sig G_f' (or_plus x (proj1_sig (ParameterizedGreatestFixedpoint f) x))))).
        + apply (proj2_sig f), or_plus_le_iff.
          split; transitivity (or_plus x (proj1_sig (ParameterizedGreatestFixedpoint f) x))...
        + apply Poset_refl2...
    }
    intros x...
  Qed.

  Theorem KnasterTarski {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >=> D,
    forall fps : ensemble D,
    isSubsetOf fps (fixed_points (proj1_sig f)) ->
    {fix_f : D | isSupremumIn fix_f fps (fixed_points (proj1_sig f))}.
  Proof with eauto with *. (* Referring to "https://www.cs.utexas.edu/users/misra/Notes.dir/KnasterTarski.pdf" written by Jayadev Misra *)
    unfold isSupremumIn.
    intros f W W_is_a_subset_of_the_fixed_points.
    destruct (supremum_always_exists_in_CompleteLattice W) as [q q_is_lub_of_W].
    simpl.
    set (W_hat := fun w : D => q =< w).
    assert (claim1 := make_Supremum_to_Infimum_of_upper_bounds W q q_is_lub_of_W).
    assert (claim2 : member q W_hat) by apply Poset_refl.
    assert (claim3 : forall x : D, member x W_hat -> member (proj1_sig f x) W_hat).
    { intros x H.
      apply q_is_lub_of_W.
      intros w H0.
      transitivity (proj1_sig f w).
      - apply Poset_refl1, W_is_a_subset_of_the_fixed_points...
      - apply (proj2_sig f).
        transitivity q...
    }
    assert (H : q =< proj1_sig f q) by apply (claim3 q claim2).
    destruct (infimum_always_exists_in_CompleteLattice (fun x : D => proj1_sig f x =< x /\ member x W_hat)) as [fix_f H0].
    assert (claim4 : proj1_sig f fix_f =< fix_f).
    { apply H0.
      intros x [H1 H2].
      transitivity (proj1_sig f x).
      - apply (proj2_sig f), H0...
      - apply H1.
    }
    assert (claim5 : q =< fix_f).
    { apply H0.
      intros x [H1 H2]...
    }
    assert (claim6 : fix_f == proj1_sig f fix_f).
    { apply Poset_asym.
      - apply H0...
        split; [apply (proj2_sig f) | apply claim3]...
      - apply claim4.
    }
    exists fix_f.
    split.
    - apply claim6.
    - intros x H1.
      split.
      + intros H2 x' H3.
        transitivity q...
      + intros H2.
        apply H0...
        split...
        apply q_is_lub_of_W...
  Qed.

  Lemma CoinductionPrinciple {D : Type} `{D_isCompleteLattice : isCompleteLattice D} (b : D >=> D) :
    forall x : D,
    x =< proj1_sig (nu b) <-> (exists y : D, x =< y /\ y =< proj1_sig b y).
  Proof with eauto with *.
    intros x.
    split.
    - assert (H := nu_isSupremum b).
      simpl.
      assert (H0 := GreatestFixedPointOfMonotonicMaps (proj1_sig b) (proj2_sig b) (proj1_sig (nu b)) H).
      simpl.
      intros H1.
      exists (proj1_sig (nu b)).
      split; [apply H1 | apply Poset_refl1, H0].
    - intros [gfp [H H0]].
      transitivity gfp; [apply H | apply PrincipleOfTarski]...
  Qed.

End ConstructiveCoLaTheory.

Module CAWU. (* Reference: "Coinduction All the Way Up" written by "Damien Pous" *)

  Import ListNotations MyUtilities BasicSetoidTheory MyEnsemble BasicPosetTheory ConstructiveCoLaTheory.

  Definition isCompatibleFor {D : Type} `{D_isPoset : isPoset D} : (D >=> D) -> (D >=> D) -> Prop :=
    fun f : D >=> D =>
    fun b : D >=> D =>
    forall x : D,
    proj1_sig f (proj1_sig b x) =< proj1_sig b (proj1_sig f x)
  .

  Global Hint Unfold isCompatibleFor : my_hints.

  Global Notation "f 'is-compatible-for' b" := (isCompatibleFor f b) (at level 70, no associativity) : type_scope.

  Lemma const_isCompatibleFor_iff {D : Type} `{D_isPoset : isPoset D} :
    forall b : D >=> D,
    forall d : D,
    const_m d is-compatible-for b <-> d =< proj1_sig b d.
  Proof with eauto with *.
    intros b d.
    unfold isCompatibleFor, const_m, const.
    simpl...
  Qed.

  Lemma id_isCompatibleFor {D : Type} `{D_isPoset : isPoset D} :
    forall b : D >=> D,
    id_m is-compatible-for b.
  Proof with eauto with *.
    unfold isCompatibleFor, id_m.
    simpl...
  Qed.

  Lemma compose_isCompatibleFor {D : Type} `{D_isPoset : isPoset D} :
    forall b : D >=> D,
    forall f1 : D >=> D,
    forall f2 : D >=> D,
    f1 is-compatible-for b ->
    f2 is-compatible-for b ->
    compose_m f1 f2 is-compatible-for b.
  Proof with eauto with *.
    unfold isCompatibleFor, compose_m.
    simpl.
    intros b f1 f2 H H0 x.
    assert (H1 := proj2_sig f1).
    transitivity (proj1_sig f1 (proj1_sig b (proj1_sig f2 x)))...
  Qed.

  Lemma supremum_isCompatibleFor {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall b : D >=> D,
    forall F : ensemble (D >=> D),
    (forall f : D >=> D, member f F -> f is-compatible-for b) ->
    supremum_m F is-compatible-for b.
  Proof with eauto with *.
    intros b F H.
    set (F_b := fun x : D => image (fun f_i : D >=> D => proj1_sig f_i (proj1_sig b x)) F).
    set (sup_F_b := fun x : D => proj1_sig (supremum_always_exists_in_CompleteLattice (F_b x))).
    assert (claim1 : forall x : D, proj1_sig (supremum_m F) (proj1_sig b x) =< sup_F_b x).
    { intros x.
      unfold sup_F_b, supremum_m, supOfMonotonicMaps.
      destruct (supremum_always_exists_in_CompleteLattice (F_b x)) as [sup_F_b_x H0].
      simpl.
      destruct (supremum_always_exists_in_CompleteLattice (image (fun f_i : D >=> D => proj1_sig f_i (proj1_sig b x)) F)) as [sup_f_i_b_x H1].
      simpl.
      apply H1.
      intros x' H2.
      inversion H2; subst.
      rename x0 into f_i.
      apply H0...
    }
    set (b_F := fun x : D => image (fun f_i : D >=> D => proj1_sig b (proj1_sig f_i x)) F).
    set (sup_b_F := fun x : D => proj1_sig (supremum_always_exists_in_CompleteLattice (b_F x))).
    assert (claim2 : forall x : D, sup_F_b x =< sup_b_F x).
    { intros x.
      unfold sup_F_b, sup_b_F.
      destruct (supremum_always_exists_in_CompleteLattice (F_b x)) as [sup_F_b_x H0].
      destruct (supremum_always_exists_in_CompleteLattice (b_F x)) as [sup_b_F_x H1].
      simpl.
      apply H0.
      intros x' H2.
      inversion H2; subst.
      rename x0 into f_i.
      transitivity (proj1_sig b (proj1_sig f_i x)).
      - apply H...
      - apply H1...
    }
    assert (claim3 : forall x : D, sup_b_F x =< proj1_sig b (proj1_sig (supremum_m F) x)).
    { intros x.
      unfold sup_b_F, supremum_m, supOfMonotonicMaps.
      destruct (supremum_always_exists_in_CompleteLattice (b_F x)) as [sup_b_F_x H0].
      simpl.
      destruct (supremum_always_exists_in_CompleteLattice (image (fun f_i : D >=> D => proj1_sig f_i x) F)) as [sup_f_i_x H1].
      simpl.
      apply H0.
      intros x' H2.
      inversion H2; subst.
      rename x0 into f_i.
      apply (proj2_sig b), H1...
    }
    intros x...
  Qed.

  Definition companion {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : (D >=> D) -> (D >=> D) :=
    fun b : D >=> D =>
    exist isMonotonicMap (proj1_sig (supremum_m (fun f : D >=> D => compose_m f b =< compose_m b f))) (supOfMonotonicMaps_isMonotonic (fun f : D >=> D => compose_m f b =< compose_m b f))
  .

  Section companion_properties.

  Context {D : Type} `{D_isCompleteLattice : isCompleteLattice D} (b : D >=> D).

  Lemma companion_isCompatibleFor :
    companion b is-compatible-for b.
  Proof with eauto with *.
    apply supremum_isCompatibleFor...
  Qed.

  Lemma companion_isTheGreatestCompatibleFunction :
    forall f : D >=> D,
    f is-compatible-for b ->
    f =< companion b.
  Proof with eauto with *.
    intros f H.
    unfold companion.
    set (F := fun f_i : D >=> D => compose_m f_i b =< compose_m b f_i).
    apply (supOfMonotonicMaps_isSupremum F)...
  Qed.

  Lemma b_le_t :
    b =< companion b.
  Proof with eauto with *.
    apply companion_isTheGreatestCompatibleFunction...
  Qed.

  Lemma id_le_t :
    id_m =< companion b.
  Proof with eauto with *.
    apply companion_isTheGreatestCompatibleFunction, id_isCompatibleFor.
  Qed.

  Lemma tt_le_t :
    compose_m (companion b) (companion b) =< companion b.
  Proof with eauto with *.
    apply companion_isTheGreatestCompatibleFunction, compose_isCompatibleFor; apply companion_isCompatibleFor.
  Qed.

  End companion_properties.

End CAWU.

Module PowerSetCoLa.

  Import MyUtilities BasicSetoidTheory MyEnsemble BasicPosetTheory ConstructiveCoLaTheory.

  Global Instance ensemble_isPoset {A : Type} : isPoset (ensemble A) :=
    arrow_isPoset Prop_isPoset
  .

  Lemma unions_isSupremum {A : Type} :
    forall Xs : ensemble (ensemble A),
    isSupremum (unions Xs) Xs.
  Proof with eauto with *.
    intros Xs X.
    split.
    - intros H X_i H0 x H1.
      assert (H2 : exists X : ensemble A, member x X /\ member X Xs) by firstorder.
      assert (H3 := proj2 (in_unions_iff x Xs) H2).
      apply H...
    - intros H x H0.
      destruct (proj1 (in_unions_iff x Xs) H0) as [X_i [H1 H2]].
      apply (H X_i H2)...
  Qed.

  Global Instance ensemble_isCompleteLattice {A : Type} : isCompleteLattice ensemble_isPoset :=
    { supremum_always_exists_in_CompleteLattice :=
      fun Xs : ensemble (ensemble A) =>
      exist _ (unions Xs) (unions_isSupremum Xs)
    }
  .

  Section PACO. (* Reference: "The Power of Parameterization in Coinductive Proof" *)

  Context {A : Type}.

  Let MyUnion : ensemble A -> ensemble A -> ensemble A :=
    fun X : ensemble A =>
    fun Y : ensemble A =>
    fun a : A =>
    member a X \/ member a Y
  .

  Lemma MyUnion_eq_or_plus :
    forall X : ensemble A,
    forall Y : ensemble A,
    MyUnion X Y == or_plus X Y.
  Proof with eauto with *.
    intros X Y.
    apply Poset_asym.
    - intros a [H | H]; apply in_union_iff; [left | right]...
    - intros a H.
      apply in_union_iff in H.
      destruct H as [H | H]; [left | right]...
  Qed.

  Section ParameterizedCoInduction.

  Variable F : ensemble A -> ensemble A.

  CoInductive PaCo : ensemble A -> ensemble A :=
  | mkPaCo :
    forall X : ensemble A,
    forall Y : ensemble A,
    isSubsetOf X (MyUnion (PaCo Y) Y) ->
    isSubsetOf (F X) (PaCo Y)
  .

  Lemma PaCo_fold :
    forall Y : ensemble A,
    isSubsetOf (F (or_plus (PaCo Y) Y)) (PaCo Y).
  Proof with eauto with *.
    intros Y.
    apply mkPaCo.
    intros a H0.
    apply in_union_iff in H0...
  Qed.

  Hypothesis F_mon : isMonotonicMap F.

  Lemma PaCo_unfold :
    forall Y : ensemble A,
    isSubsetOf (PaCo Y) (F (or_plus (PaCo Y) Y)).
  Proof with eauto with *.
    intros Y a H.
    inversion H; subst.
    assert (H2 : isSubsetOf (F X) (F (MyUnion (PaCo Y) Y))) by now apply (F_mon X (MyUnion (PaCo Y) Y)).
    assert (H3 : isSubsetOf (MyUnion (PaCo Y) Y) (or_plus (PaCo Y) Y)).
    { intros a' H'.
      apply in_union_iff in H'...
    }
    assert (H4 := F_mon (MyUnion (PaCo Y) Y) (or_plus (PaCo Y) Y) H3).
    apply H4, H2...
  Qed.

  Lemma PaCo_preserves_monotonicity :
    isMonotonicMap PaCo.
  Proof with eauto with *.
    intros X1 X2 H.
    assert (H0 := PaCo_unfold X1).
    cofix CIH.
    intros a H1.
    apply (mkPaCo (MyUnion (PaCo X1) X1) X2).
    - intros a' [H1' | H1']; [left; apply CIH | right; apply H]...
    - apply (F_mon (or_plus (PaCo X1) X1)).
      + apply or_plus_le_iff.
        split; intros a' H2'; [left | right]...
      + apply H0...
  Qed.

  Lemma PaCo_init :
    proj1_sig (nu (exist isMonotonicMap F F_mon)) == PaCo bot.
  Proof with eauto with *.
    assert (claim1 := PaCo_fold bot).
    assert (claim2 := PaCo_unfold bot).
    assert (claim3 : PaCo bot == F (PaCo bot)).
    { apply Poset_asym.
      - transitivity (F (or_plus (PaCo bot) bot)).
        + apply claim2.
        + apply (F_mon (or_plus (PaCo bot) bot)), or_plus_le_iff...
      - transitivity (F (or_plus (PaCo bot) bot)).
        + apply (F_mon (PaCo bot))...
        + apply claim1.
    }
    assert (claim4 : isSupremum (proj1_sig (nu (exist _ F F_mon))) (postfixed_points F)) by now apply nu_isSupremum.
    destruct (GreatestFixedPointOfMonotonicMaps F F_mon (proj1_sig (nu (exist _ F F_mon))) claim4) as [claim5 claim6].
    assert (claim7 : F (proj1_sig (nu (exist _ F F_mon))) =< PaCo bot).
    { cofix CIH.
      apply mkPaCo.
      intros a H.
      left.
      apply CIH, claim5...
    }
    enough (therefore_we_can_conclude : proj1_sig (nu (exist _ F F_mon)) =< PaCo bot)...
  Qed.

  Lemma PaCo_acc :
    forall X : ensemble A,
    forall Y : ensemble A,
    isSubsetOf Y (PaCo X) <-> isSubsetOf Y (PaCo (MyUnion X Y)).
  Proof with eauto with *.
    intros X Y.
    split.
    - intros H.
      assert (H0 : X =< MyUnion X Y) by now constructor 1.
      assert (H1 := PaCo_preserves_monotonicity X (MyUnion X Y) H0).
      intros a H2.
      apply H1, H...
    - intros H_star.
      assert (claim1 := PaCo_unfold (MyUnion X Y)).
      assert (claim2 : isSubsetOf (F (or_plus (PaCo (MyUnion X Y)) (MyUnion X Y))) (F (or_plus (PaCo (MyUnion X Y)) X))).
      { apply F_mon, or_plus_le_iff.
        split.
        - apply le_or_plus.
        - intros a [H | H]; apply in_union_iff; [right | left]...
      }
      assert (claim3 : or_plus (PaCo (MyUnion X Y)) X =< MyUnion X (PaCo (MyUnion X Y))).
      { intros a H.
        apply in_union_iff in H.
        destruct H as [H | H]; [right | left]...
      }
      assert (claim4 : member (PaCo (MyUnion X Y)) (postfixed_points (fun Z : ensemble A => F (MyUnion X Z)))).
      { intros a H.
        apply (F_mon (or_plus (PaCo (MyUnion X Y)) X) _ claim3), claim2...
      }
      assert (claim5 : isMonotonicMap (fun Z : ensemble A => F (MyUnion X Z))).
      { intros X1 X2 H.
        apply F_mon.
        intros a [H0 | H0]; [left | right; apply H]...
      }
      set (nu0 := proj1_sig (nu (exist isMonotonicMap (fun Z : ensemble A => F (MyUnion X Z)) claim5))).
      assert (claim6 : or_plus (PaCo (MyUnion X Y)) X =< MyUnion X (PaCo (MyUnion X Y))).
      { intros a H.
        apply in_union_iff in H.
        destruct H as [H | H]; [right | left]...
      }
      assert (claim7 : PaCo (MyUnion X Y) =< F (MyUnion X (PaCo (MyUnion X Y)))).
      { intros a H.
        apply (F_mon (or_plus (PaCo (MyUnion X Y)) X) _ claim6), claim2, claim1...
      }
      assert (claim8 : PaCo (MyUnion X Y) =< nu0) by now apply PrincipleOfTarski.
      assert (claim9 : isSupremum nu0 (postfixed_points (fun Z : ensemble A => F (MyUnion X Z)))).
      { unfold nu0.
        assert (H0 := nu_isSupremum (exist isMonotonicMap (fun Z : ensemble A => F (MyUnion X Z)) claim5))...
      }
      destruct (GreatestFixedPointOfMonotonicMaps (fun Z : ensemble A => F (MyUnion X Z)) claim5 nu0 claim9) as [claim10 claim11].
      assert (claim12 : nu0 =< F (MyUnion X nu0)) by now apply Poset_refl1.
      assert (claim13 : F (MyUnion X nu0) =< PaCo X).
      { cofix CIH.
        apply mkPaCo.
        intros a [H | H]; [right | left; apply CIH, claim12]...
      }
      assert (claim14 : Y =< PaCo (MyUnion X Y)) by apply H_star.
      enough (therefore_we_can_conclude : Y =< PaCo X)...
  Qed.

  Definition accPaCo : ensemble A -> ensemble A -> Prop :=
    fun X : ensemble A =>
    fun Y : ensemble A =>
    forall Z : ensemble A,
    isSubsetOf Y Z ->
    isSubsetOf X Z ->
    isSubsetOf X (PaCo Z)
  .

  Theorem accPaCo_iff :
    forall X : ensemble A,
    forall Y : ensemble A,
    accPaCo X Y <-> isSubsetOf X (PaCo Y).
  Proof with eauto with *.
    unfold accPaCo.
    intros X Y.
    split.
    - intros acc_hyp.
      apply (proj2 (PaCo_acc Y X)), acc_hyp; intros a H; [left | right]...
    - intros acc_con Z H H0.
      enough (it_is_sufficient_to_show : X =< PaCo Z) by exact it_is_sufficient_to_show.
      transitivity (PaCo (MyUnion Y X)).
      + apply (proj1 (PaCo_acc Y X) acc_con).
      + apply PaCo_preserves_monotonicity.
        intros a [H1 | H1]; [apply H | apply H0]...
  Qed.

  End ParameterizedCoInduction.

  Definition paco : (ensemble A >=> ensemble A) -> (ensemble A >=> ensemble A) :=
    fun F : ensemble A >=> ensemble A =>
    exist isMonotonicMap (PaCo (proj1_sig F)) (PaCo_preserves_monotonicity (proj1_sig F) (proj2_sig F))
  .

  Theorem paco_spec :
    forall F : ensemble A >=> ensemble A,
    paco F == ParameterizedGreatestFixedpoint F.
  Proof with eauto with *.
    intros F.
    apply FullCharacterization_of_ParameterizedGreatestFixedPoint.
    - intros X.
      apply Poset_asym.
      + transitivity (proj1_sig F (or_plus (proj1_sig (paco F) X) X)).
        * apply (PaCo_unfold (proj1_sig F) (proj2_sig F) X).
        * apply (proj2_sig F), or_plus_le_iff...
      + transitivity (proj1_sig F (or_plus (proj1_sig (paco F) X) X)).
        * apply (proj2_sig F), or_plus_le_iff...
        * apply (PaCo_fold (proj1_sig F) X).
    - intros X Y H.
      assert (claim1 : (proj1_sig (paco F) (or_plus X Y)) =< (PaCo (proj1_sig F) (MyUnion X Y))).
      { apply (PaCo_preserves_monotonicity (proj1_sig F) (proj2_sig F) (or_plus X Y) (MyUnion X Y)). 
        intros a H0.
        apply in_union_iff in H0.
        destruct H0 as [H0 | H0]; [left | right]...
      }
      enough (claim2 : Y =< PaCo (proj1_sig F) (MyUnion X Y)) by apply (proj2 (PaCo_acc (proj1_sig F) (proj2_sig F) X Y) claim2)...
  Qed.

  End PACO.

  (** "A category theoretical approach to the definition of simulation"
    * [#1]
    * ```coq
    * Section CategoryTheoreticApproach.
    * Definition ensemble (A : Type) : Type := A -> Prop.
    * Definition member {A : Type} : A -> ensemble A -> Prop := fun x : A => fun X : ensemble A => X x.
    * Notation " x '∈' X " := (member x X) (at level 70, no associativity) : type_scope.
    * Variable Eff : Type.
    * Variant mymap {A : Type} {B : Type} (f : A -> B) (X : ensemble (A * Eff)) : ensemble (B * Eff) :=
    * | in_mymap (a : A) (e : Eff) : (a, e) ∈ X -> (f a, e) ∈ mymap f X
    * .
    * End CategoryTheoreticApproach.
    * ```
    * Let $F : Type -> Type := fun A : Type => ensemble (A * Eff)$ be an endofunctor
    * with $fmap (f : A -> B) : F A -> F B := mymap f$ for $A : Type$ and $B : Type$.
    * Then every coalgebra of the endofunctor $F$ is of the form $(State : Type, State_trans : State -> ensemble (State * Eff))$.
    * Conversely, every pair $(State : Type, State_trans : State -> ensemble (State * Eff))$ is a coalgebra of $F$.
    * If a coalgebra $(State, State_trans)$ of $F$ is given, for any $e : Eff$, $st1 : State$ and $st2 : State$,
    * we will write $st1 ~~[ e ]~> st2$ if $(st1, e) ∈ State_trans st2$ holds.
    * [#2]
    * Let $(Src, Src_trans) and $(Tgt, Tgt_trans)$ be two coalgebras of $F$.
    * We say a map $sim : Src -> Tgt$ is a simulation of $Src$ in $Tgt$ if $sim$ is a coalgebra homomorphism,
    * i.e., $fmap sim ∘ Src_trans = Tgt_trans ∘ sim$ holds.
    * But every map $f : Src -> Tgt$ satisfies $fmap f ∘ Src_trans = Tgt_trans ∘ f$ if and only if:
    * (1) $map_trans f (Src_trans s_2) \subseteq Tgt_trans (f s_2)$ holds for every $s_2 : Src$ and;
    * (2) $Tgt_trans (f s_2) \subseteq map_trans f (Src_trans s_2)$ holds for every $s_2 : Src$.
    * Therefore, we can conclude a map $f : Src -> Tgt$ is a simulation of $Src$ in $Tgt$ if and only if:
    * (1') $s_1 ~~[ e ]~> s_2 \implies f(s_1) ~~[ e ]~> f(s_2)$; and
    * (2') $t ~~[ e ]~> f(s_2) \implies \exists s_1, s_1 ~~[ e ]~> s_2 \land t = f(s_1)$,
    * by exploiting the facts that (1) is equivalent to (1') and that (2) is equivalent to (2').
    *)

  Class LabelledTransition (State : Type) (Label : Type) : Type :=
    { state_trans : State -> ensemble (State * Label)
    }
  .

  Global Notation " st1 '~~[' label ']~>' st2 " := (member (st1, label) (state_trans st2)) (at level 70, no associativity) : type_scope.

  Global Reserved Notation " st1 '~~~[' labels ']~>*' st2 " (at level 70, no associativity).

  Inductive state_star {State : Type} {Label : Type} `{HasLabelledTransition : LabelledTransition State Label} (st1 : State) : list Label -> State -> Prop :=
  | star_init :
    st1 ~~~[ nil ]~>* st1
  | star_step :
    forall st2 : State,
    forall st3 : State,
    forall label : Label,
    forall labels : list Label,
    st2 ~~[ label ]~> st3 ->
    st1 ~~~[ labels ]~>* st2 ->
    st1 ~~~[ cons label labels ]~>* st3
  where " st1 '~~~[' labels ']~>*' st2 " := (state_star st1 labels st2) : type_scope.

  Local Hint Constructors state_star : core.

  Section BISIMULATION.

  Context {Src : Type} {Tgt : Type} {Eff : Type} `{SrcTrans : LabelledTransition Src Eff} `{TgtTrans : LabelledTransition Tgt Eff}.

  (** [The diagram of "bisimF"]
    * Lemma bisimF_dia1 :
    *   forall R : ensemble (Src * Tgt),
    *   forall s1 : Src,
    *   forall t1 : Tgt,
    *   member (s1, t1) (bisimF R) ->
    *   forall e : Eff,
    *   forall s2 : Src,
    *   s1 ~~[ e ]~> s2 ->
    *   exists t2 : Tgt, t1 ~~[ e ]~> t2 /\ member (s2, t2) R.
    * Lemma bisimF_dia2 :
    *   forall R : ensemble (Src * Tgt),
    *   forall s1 : Src,
    *   forall t1 : Tgt,
    *   member (s1, t1) (bisimF R) ->
    *   forall e : Eff,
    *   forall t2 : Tgt,
    *   t1 ~~[ e ]~> t2 ->
    *   exists s2 : Src, s1 ~~[ e ]~> s2 /\ member (s2, t2) R.
    *)

  Variant bisimF (R : ensemble (Src * Tgt)) : ensemble (Src * Tgt) :=
  | PreservesBisimilarity (s1 : Src) (t1 : Tgt) (bisimF_comm1 : forall e : Eff, forall s2 : Src, s1 ~~[ e ]~> s2 -> exists t2 : Tgt, t1 ~~[ e ]~> t2 /\ member (s2, t2) R) (bisimF_comm2 : forall e : Eff, forall t2 : Tgt, t1 ~~[ e ]~> t2 -> exists s2 : Src, s1 ~~[ e ]~> s2 /\ member (s2, t2) R) : member (s1, t1) (bisimF R)
  .

  Lemma bisimF_isMonotonicMap :
    isMonotonicMap bisimF.
  Proof.
    intros R1 R2 H_incl [s1 t1] H_in1.
    inversion H_in1; subst.
    constructor.
    - intros e s2 H_trans1.
      destruct (bisimF_comm1 e s2 H_trans1) as [t2 [H_trans2 H_in2]].
      exists t2.
      split.
      + exact H_trans2.
      + exact (H_incl (s2, t2) H_in2).
    - intros e t2 H_trans1.
      destruct (bisimF_comm2 e t2 H_trans1) as [s2 [H_trans2 H_in2]].
      exists s2.
      split.
      + exact H_trans2.
      + exact (H_incl (s2, t2) H_in2).
  Qed.

  Definition bisimilar : Src -> Tgt -> Prop :=
    fun s : Src =>
    fun t : Tgt =>
    exists R : ensemble (Src * Tgt), isSubsetOf R (bisimF R) /\ member (s, t) R
  .

  Local Notation " s '`isBisimilarTo`' t " := (bisimilar s t) (at level 70, no associativity) : type_scope.

  Let commutation1 : Eff -> Src -> Tgt -> Prop :=
    fun e : Eff =>
    fun s1 : Src =>
    fun t1 : Tgt =>
    s1 `isBisimilarTo` t1 ->
    forall s2 : Src,
    s1 ~~[ e ]~> s2 ->
    exists t2 : Tgt, t1 ~~[ e ]~> t2 /\ s2 `isBisimilarTo` t2
  .

  Let commutation2 : Eff -> Src -> Tgt -> Prop :=
    fun e : Eff =>
    fun s1 : Src =>
    fun t1 : Tgt =>
    s1 `isBisimilarTo` t1 ->
    forall t2 : Tgt,
    t1 ~~[ e ]~> t2 ->
    exists s2 : Src, s1 ~~[ e ]~> s2 /\ s2 `isBisimilarTo` t2
  .

  Lemma the_diagram_of_bisimilarity :
    forall e : Eff,
    forall s : Src,
    forall t : Tgt,
    commutation1 e s t /\ commutation2 e s t.
  Proof.
    intros e s2 t2.
    split.
    - intros [R [R_le_bisimF_R H_in1]] s3 s2_e_s3.
      assert (H_in2 : member (s2, t2) (bisimF R)) by exact (R_le_bisimF_R (s2, t2) H_in1).
      inversion H_in2; subst.
      destruct (bisimF_comm1 e s3 s2_e_s3) as [t3 [t2_e_t3 H_in]].
      exists t3.
      now firstorder.
    - intros [R [R_le_bisimF_R H_in1]] t3 t2_e_t3.
      assert (H_in2 : member (s2, t2) (bisimF R)) by exact (R_le_bisimF_R (s2, t2) H_in1).
      inversion H_in2; subst.
      destruct (bisimF_comm2 e t3 t2_e_t3) as [s3 [s2_e_s3 H_in]].
      exists s3.
      now firstorder. 
  Qed.

  Let bisimilar_cond1 : Src -> Tgt -> Prop :=
    fun s1 : Src =>
    fun t1 : Tgt =>
    forall es : list Eff,
    forall s2 : Src,
    s1 ~~~[ es ]~>* s2 ->
    exists t2 : Tgt, t1 ~~~[ es ]~>* t2 /\ s2 `isBisimilarTo` t2
  .

  Let bisimilar_cond2 : Src -> Tgt -> Prop :=
    fun s1 : Src =>
    fun t1 : Tgt =>
    forall es : list Eff,
    forall t2 : Tgt,
    t1 ~~~[ es ]~>* t2 ->
    exists s2 : Src, s1 ~~~[ es ]~>* s2 /\ s2 `isBisimilarTo` t2
  .

  Lemma bisimilar_iff :
    forall s : Src,
    forall t : Tgt,
    s `isBisimilarTo` t <-> (bisimilar_cond1 s t /\ bisimilar_cond2 s t).
  Proof with eauto.
    intros s1 t1.
    split.
    - intros s1_bisimilar_t1.
      split.
      { intros es s2 s1_es_s2.
        induction s1_es_s2 as [| s2 s3 e es s2_e_s3 s1_es_s2 IH].
        - exists t1...
        - destruct IH as [t2 [t1_es_t2 s2_bisimilar_t2]].
          destruct (proj1 (the_diagram_of_bisimilarity e s2 t2) s2_bisimilar_t2 s3 s2_e_s3) as [t3 [t2_e_t3 s3_bisimilar_t3]].
          exists t3...
      }
      { intros es t2 t1_es_t2.
        induction t1_es_t2 as [| t2 t3 e es t2_e_t3 t1_es_t2 IH].
        - exists s1...
        - destruct IH as [s2 [s1_es_s2 s2_bisimilar_t2]].
          destruct (proj2 (the_diagram_of_bisimilarity e s2 t2) s2_bisimilar_t2 t3 t2_e_t3) as [s3 [s2_e_s3 s3_bisimilar_t3]].
          exists s3...
      }
    - intros [H_cond1 H_cond2].
      destruct (H_cond1 nil s1 (star_init s1)) as [t [t1_es_t s1_bisimilar_t]].
      inversion t1_es_t; subst t...
  Qed.

  Definition bisim : ensemble (Src * Tgt) :=
    proj1_sig (paco (exist isMonotonicMap bisimF bisimF_isMonotonicMap)) bot
  .

  Theorem bisim_spec :
    forall s : Src,
    forall t : Tgt,
    member (s, t) bisim <-> s `isBisimilarTo` t.
  Proof with eauto with *.
    set (b := exist isMonotonicMap bisimF bisimF_isMonotonicMap).
    set (bisim' := proj1_sig (nu b)).
    assert (claim1 : bisim' == bisim) by exact (PaCo_init bisimF bisimF_isMonotonicMap).
    assert (claim2 : isGreatestFixedPoint bisim' bisimF).
    { apply (GreatestFixedPointOfMonotonicMaps bisimF bisimF_isMonotonicMap).
      exact (nu_isSupremum b).
    }
    assert (claim3 : forall R : ensemble (Src * Tgt), R =< bisimF R -> R =< bisim) by exact (proj1 (nu_isSupremum b bisim) (Poset_refl1 bisim' bisim claim1)).
    intros s t.
    split.
    - intros H_in.
      exists bisim'.
      split.
      + exact (Poset_refl1 bisim' (bisimF bisim') (proj1 claim2)).
      + exact (proj2 (claim1 (s, t)) H_in).
    - intros [R [R_le_bisimF_R H_in]].
      exact (claim3 R R_le_bisimF_R (s, t) H_in).
  Qed.

  End BISIMULATION.

End PowerSetCoLa.

Module ConstructiveCpoTheory. (* Reference: "The Lambda Calculus: Its Syntax and Semantics" of "H. P. Barendregt." *)

  Import MyUtilities BasicSetoidTheory MyEnsemble BasicPosetTheory MyEnsembleNova BasicTopology ConstructiveCoLaTheory.

  Definition isDirected {D : Type} `{D_isPoset : isPoset D} : ensemble D -> Prop :=
    fun X : ensemble D =>
    nonempty X /\ (forall x1 : D, member x1 X -> forall x2 : D, member x2 X -> exists x3 : D, member x3 X /\ x1 =< x3 /\ x2 =< x3)
  .

  Class isCompletePartialOrder {D : Type} (D_isPoset : isPoset D) : Type :=
    { bottom_exists :
      {min_D : D | forall x : D, min_D =< x}
    ; square_up_exists :
      forall X : ensemble D,
      isDirected X ->
      {sup_X : D | isSupremum sup_X X}
    }
  .

  Lemma square_up_isSupremum {D : Type} `{D_isPoset : isPoset D} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} :
    forall X : ensemble D,
    forall X_isDirected : @isDirected D D_isPoset X,
    @isSupremum D D_isPoset (proj1_sig (square_up_exists X X_isDirected)) X.
  Proof.
    intros X X_isDirected.
    exact (proj2_sig (square_up_exists X X_isDirected)).
  Qed.

  Local Instance CompleteLattice_isCompletePartialOrder {D : Type} `{D_isPoset : isPoset D} (D_requiresCompleteLattice : @isCompleteLattice D D_isPoset) : @isCompletePartialOrder D D_isPoset :=
    { bottom_exists :=
      exist _ bot bot_isBottom
    ; square_up_exists :=
      fun X : ensemble D =>
      fun _ : isDirected X =>
      supremum_always_exists_in_CompleteLattice X
    }
  .

  Section BuildScottTopology.

  Context (D : Type) (D_isPoset : isPoset D).

  Let ScottOpen_cond1 : ensemble D -> Prop :=
    fun O : ensemble D =>
    forall x : D,
    forall y : D,
    member x O ->
    x =< y ->
    member y O
  .

  Let ScottOpen_cond2 : ensemble D -> Prop :=
    fun O : ensemble D =>
    forall X : ensemble D,
    isDirected X ->
    forall sup_X : D,
    isSupremum sup_X X ->
    member sup_X O ->
    nonempty (intersection X O)
  .

  Definition isOpen_ScottTopology : ensemble D -> Prop :=
    fun O : ensemble D =>
    ScottOpen_cond1 O /\ ScottOpen_cond2 O
  .

  Local Hint Unfold isOpen_ScottTopology : core.

  Context (D_requiresCompletePartialOrder : @isCompletePartialOrder D D_isPoset).

  Lemma open_full_ScottTopology :
    isOpen_ScottTopology full.
  Proof with eauto with *.
    split.
    - now firstorder.
    - unfold full.
      intros X [[x H] H0] sup_X H1 H2...
  Qed.

  Lemma open_unions_ScottTopology :
    forall Xs : ensemble (ensemble D),
    (forall X : ensemble D, member X Xs -> isOpen_ScottTopology X) ->
    isOpen_ScottTopology (unions Xs).
  Proof with try now firstorder.
    intros Xs H.
    split.
    - intros x y.
      repeat (rewrite in_unions_iff)...
    - intros X H1 sup_X.
      rewrite in_unions_iff.
      intros H2 [X_i [H3 H4]].
      destruct (proj2 (H X_i H4) X H1 sup_X H2 H3) as [x H5].
      exists x.
      rewrite in_intersection_iff, in_unions_iff in *...
  Qed.

  Lemma open_intersection_ScottTopology :
    forall X1 : ensemble D,
    forall X2 : ensemble D,
    isOpen_ScottTopology X1 ->
    isOpen_ScottTopology X2 ->
    isOpen_ScottTopology (intersection X1 X2).
  Proof with try now firstorder.
    intros X1 X2 H H0.
    split.
    - intros x y.
      repeat (rewrite in_intersection_iff)...
    - intros X H1 sup_X.
      repeat (rewrite in_intersection_iff).
      intros H2 [H3 H4].
      destruct (proj2 H X H1 sup_X H2 H3) as [x1 H5].
      destruct (proj2 H0 X H1 sup_X H2 H4) as [x2 H6].
      revert H5 H6.
      repeat (rewrite in_intersection_iff).
      intros [H5 H6] [H7 H8].
      destruct (proj2 H1 x1 H5 x2 H7) as [x [H9 [H10 H11]]].
      unfold nonempty.
      exists x.
      repeat (rewrite in_intersection_iff)...
  Qed.

  Lemma open_ext_eq_ScottTopology :
    forall O1 : ensemble D,
    isOpen_ScottTopology O1 ->
    forall O2 : ensemble D,
    (forall x : D, member x O1 <-> member x O2) ->
    isOpen_ScottTopology O2.
  Proof with try now firstorder.
    intros O1 [H H0] O2 H1.
    enough (it_is_sufficient_to_show : forall X : ensemble D, isDirected X -> forall sup_X : D, isSupremum sup_X X -> member sup_X O2 -> nonempty (intersection X O2)) by firstorder.
    intros X H2 sup_X H3 H4.
    assert (H5 := proj2 (H1 sup_X) H4).
    destruct (H0 X H2 sup_X H3 H5) as [x0 H6].
    exists x0.
    rewrite in_intersection_iff in *...
  Qed.

  End BuildScottTopology.

  Global Instance ScottTopology {D : Type} `{D_isPoset : isPoset D} (D_requiresCompletePartialOrder : @isCompletePartialOrder D D_isPoset) : isTopologicalSpace D :=
    { isOpen := isOpen_ScottTopology D D_isPoset
    ; open_full := open_full_ScottTopology D D_isPoset D_requiresCompletePartialOrder
    ; open_unions := open_unions_ScottTopology D D_isPoset D_requiresCompletePartialOrder
    ; open_intersection := open_intersection_ScottTopology D D_isPoset D_requiresCompletePartialOrder
    ; open_ext_eq := open_ext_eq_ScottTopology D D_isPoset D_requiresCompletePartialOrder
    }
  .

  Lemma bot_of_direct_product {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall p : D * D',
    (proj1_sig bottom_exists, proj1_sig bottom_exists) =< p.
  Proof with eauto with *.
    intros [x y].
    split; apply (proj2_sig bottom_exists).
  Qed.

  Lemma directed_subset_of_direct_product {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} :
    forall X : ensemble (D * D'),
    isDirected X ->
    isDirected (image fst X) /\ isDirected (image snd X).
  Proof with eauto with *.
    intros X [[[x0 y0] H] H0].
    split; split.
    - exists x0...
    - intros p1 H1 p2 H2.
      inversion H1; subst.
      rename x into x1.
      inversion H2; subst.
      rename x into x2.
      destruct (H0 x1 H3 x2 H4) as [[x3 y3] [H5 [[H6 H7] [H8 H9]]]].
      simpl in *.
      exists x3.
      split...
    - exists y0...
    - intros p1 H1 p2 H2.
      inversion H1; subst.
      rename x into x1.
      inversion H2; subst.
      rename x into x2.
      destruct (H0 x1 H3 x2 H4) as [[x3 y3] [H5 [[H6 H7] [H8 H9]]]].
      simpl in *.
      exists y3.
      split...
  Qed.

  Lemma square_up_of_direct_product {D : Type} {D' : Type} `{D_isCompletePartialOrder : isCompletePartialOrder D} `{D'_isCompletePartialOrder : isCompletePartialOrder D'} :
    forall X : ensemble (D * D'),
    forall X_isDirected : isDirected X,
    isSupremum (proj1_sig (square_up_exists (image fst X) (proj1 (directed_subset_of_direct_product X X_isDirected))), proj1_sig (square_up_exists (image snd X) (proj2 (directed_subset_of_direct_product X X_isDirected)))) X.
  Proof with eauto with *.
    intros X X_isDirected.
    destruct (square_up_exists (image fst X) (proj1 (directed_subset_of_direct_product X X_isDirected))) as [sup_X1 H].
    destruct (square_up_exists (image snd X) (proj2 (directed_subset_of_direct_product X X_isDirected))) as [sup_X2 H0].
    simpl.
    intros [x y].
    split.
    - intros [H1 H2] [x' y'] H3.
      split; simpl in *.
      + apply H...
      + apply H0...
    - intros H1.
      split; simpl.
      + apply H.
        intros x' H2.
        inversion H2; subst.
        apply H1...
      + apply H0.
        intros y' H2.
        inversion H2; subst.
        apply H1...
  Qed.

  Global Instance direct_product_of_CompletePartialOrder_isCompletePartialOrder {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} (D_requiresCompletePartialOrder : @isCompletePartialOrder D D_isPoset) (D'_requiresCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset) : @isCompletePartialOrder (D * D') (DirectProductOfPoset D_isPoset D'_isPoset) :=
    { bottom_exists :=
      exist _ (proj1_sig bottom_exists, proj1_sig bottom_exists) bot_of_direct_product
    ; square_up_exists :=
      fun X : ensemble (D * D') =>
      fun X_isDirected : isDirected X =>
      exist _ (proj1_sig (square_up_exists (image fst X) (proj1 (directed_subset_of_direct_product X X_isDirected))), proj1_sig (square_up_exists (image snd X) (proj2 (directed_subset_of_direct_product X X_isDirected)))) (square_up_of_direct_product X X_isDirected)
    }
  .

End ConstructiveCpoTheory.
