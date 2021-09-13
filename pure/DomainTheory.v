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

  Class isCompleteLattice (D : Type) `{D_isPoset : isPoset D} : Type :=
    { supremum_always_exists_in_CompleteLattice :
      forall X : ensemble D,
      {sup_X : D | isSupremum sup_X X}
    }
  .

  Definition infimum_always_exists_in_CompleteLattice {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} : forall X : ensemble D, {inf_X : D | isInfimum inf_X X} :=
    fun X : ensemble D =>
    match supremum_always_exists_in_CompleteLattice (fun d : D => forall x : D, member x X -> d =< x) with
    | exist _ inf_X inf_X_isInfimum_X => exist _ inf_X (compute_Infimum X inf_X inf_X_isInfimum_X)
    end
  .

  Global Instance fish_isPoset {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} (D_requiresCompleteLattice : @isCompleteLattice D D_isPoset) (D'_requiresCompleteLattice : @isCompleteLattice D' D'_isPoset) : isPoset (D >=> D') :=
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

  Lemma compose_isMonotonic {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} :
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

  Definition supOfMonotonicMaps {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} `{D'_isCompleteLattice : @isCompleteLattice D' D'_isPoset} : ensemble (D >=> D') -> D -> D' :=
    fun fs : ensemble (D >=> D') =>
    fun x : D =>
    proj1_sig (supremum_always_exists_in_CompleteLattice (image (fun f_i : D >=> D' => proj1_sig f_i x) fs))
  .

  Lemma supOfMonotonicMaps_isMonotonic {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} `{D'_isCompleteLattice : @isCompleteLattice D' D'_isPoset} :
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

  Definition supremum_m {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} `{D'_isCompleteLattice : @isCompleteLattice D' D'_isPoset} : ensemble (D >=> D') -> (D >=> D') :=
    fun F : ensemble (D >=> D') =>
    exist isMonotonicMap (supOfMonotonicMaps F) (supOfMonotonicMaps_isMonotonic F)
  .

  Lemma supOfMonotonicMaps_isSupremum {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} `{D'_isCompleteLattice : @isCompleteLattice D' D'_isPoset} :
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

  Global Instance MonotonicMaps_on_CompleteLattice_constitute_CompleteLattice {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} (D_requiresCompleteLattice : @isCompleteLattice D D_isPoset) (D'_requiresCompleteLattice : @isCompleteLattice D' D'_isPoset) : @isCompleteLattice (D >=> D') (fish_isPoset D_requiresCompleteLattice D'_requiresCompleteLattice) :=
    { supremum_always_exists_in_CompleteLattice :=
      fun fs : ensemble (D >=> D') =>
      exist (fun sup_fs : D >=> D' => isSupremum sup_fs fs) (supremum_m fs) (supOfMonotonicMaps_isSupremum fs)
    }
  .

  Lemma LeastFixedPointInCompleteLattice {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
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
    assert (claim1 : gfp =< f gfp).
    { apply H0.
      intros x H1.
      transitivity (f x)...
    }
    split.
    - apply Poset_asym.
      + exact claim1.
      + apply H0...
    - intros fix_f H1...
  Qed.

  Lemma GreatestFixedPointInCompleteLattice {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
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

  Definition nu {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} : forall f : D >=> D, {gfp : D | isGreatestFixedPoint gfp (proj1_sig f)} :=
    fun f : D >=> D =>
    match supremum_always_exists_in_CompleteLattice (postfixed_points (proj1_sig f)) with
    | exist _ gfp H => exist _ gfp (GreatestFixedPointOfMonotonicMaps (proj1_sig f) (proj2_sig f) gfp H)
    end
  .

  Lemma nu_isSupremum {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
    forall f : D >=> D,
    isSupremum (proj1_sig (nu f)) (postfixed_points (proj1_sig f)).
  Proof with eauto with *.
    unfold nu.
    intros f.
    destruct (supremum_always_exists_in_CompleteLattice (postfixed_points (proj1_sig f))) as [gfp H]...
  Qed.

  Definition or_plus {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} : D -> D -> D :=
    fun x1 : D =>
    fun x2 : D =>
    proj1_sig (supremum_always_exists_in_CompleteLattice (finite [x1; x2]))
  .

  Lemma le_or_plus {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
    forall x1 : D,
    forall x2 : D,
    x1 =< or_plus x1 x2 /\ x2 =< or_plus x1 x2.
  Proof with eauto with *.
    intros x1 x2.
    assert (H : isSupremum (or_plus x1 x2) (finite [x1; x2])) by exact (proj2_sig (supremum_always_exists_in_CompleteLattice (finite [x1; x2]))).
    split...
  Qed.

  Lemma le_or_plus_intro1 {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
    forall x1 : D,
    forall x2 : D,
    x1 =< or_plus x1 x2.
  Proof.
    apply le_or_plus.
  Qed.

  Global Hint Resolve le_or_plus_intro1 : my_hints.

  Lemma le_or_plus_intro2 {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
    forall x1 : D,
    forall x2 : D,
    x2 =< or_plus x1 x2.
  Proof.
    apply le_or_plus.
  Qed.

  Global Hint Resolve le_or_plus_intro2 : my_hints.

  Lemma or_plus_le_iff {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
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

  Lemma PrincipleOfTarski {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
    forall f : D >=> D,
    forall x : D,
    x =< proj1_sig f x ->
    x =< proj1_sig (nu f).
  Proof with eauto with *.
    intros f.
    assert (claim1 := nu_isSupremum f)...
  Qed.

  Lemma StrongCoinduction {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
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

  Definition G_f_aux {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} : (D >=> D) -> D -> D -> D :=
    fun f : D >=> D =>
    fun x : D =>
    fun y : D =>
    proj1_sig f (or_plus x y)
  .

  Lemma G_f_aux_x_isMonotonic {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
    forall f : D >=> D,
    forall x : D,
    isMonotonicMap (G_f_aux f x).
  Proof with eauto with *.
    intros f x y1 y2 H.
    apply (proj2_sig f), or_plus_le_iff...
  Qed.

  Definition G_f {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} : (D >=> D) -> (D -> D) :=
    fun f : D >=> D =>
    fun x : D =>
    proj1_sig (nu (exist isMonotonicMap (G_f_aux f x) (G_f_aux_x_isMonotonic f x)))
  .

  Lemma G_f_isMonotoinc {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
    forall f : D >=> D,
    isMonotonicMap (G_f f).
  Proof with eauto with *.
    intros f.
    assert (claim1 := nu_isSupremum f).
    set (G_f_aux := fun x : D => fun y : D => proj1_sig f (or_plus x y)).
    intros x1 x2 H.
    apply StrongCoinduction.
    simpl in *.
    assert (claim2 : G_f f x1 == proj1_sig f (or_plus x1 (G_f f x1))) by apply (proj2_sig (nu (exist isMonotonicMap (G_f_aux x1) (G_f_aux_x_isMonotonic f x1)))).
    transitivity (proj1_sig f (or_plus x1 (G_f f x1))).
    - apply Poset_refl1...
    - apply (proj2_sig f).
      transitivity (or_plus x2 (G_f f x1)); apply or_plus_le_iff...
  Qed.

  Definition ParameterizedGreatestFixedpoint {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} : (D >=> D) -> (D >=> D) :=
    fun f : D >=> D =>
    exist isMonotonicMap (G_f f) (G_f_isMonotoinc f)
  .

  Lemma ParameterizedGreatestFixedpoint_isMonotonic {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
    isMonotonicMap ParameterizedGreatestFixedpoint.
  Proof with eauto with *.
    intros f1 f2 H x.
    simpl.
    unfold G_f.
    assert (claim1 := nu_isSupremum (exist isMonotonicMap (fun y : D => proj1_sig f1 (or_plus x y)) (G_f_aux_x_isMonotonic f1 x))).
    assert (claim2 := nu_isSupremum (exist isMonotonicMap (fun y : D => proj1_sig f2 (or_plus x y)) (G_f_aux_x_isMonotonic f2 x))).
    apply claim1...
  Qed.

  Definition bot {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} : D :=
    proj1_sig (supremum_always_exists_in_CompleteLattice (finite []))
  .

  Lemma bot_isBottom {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
    forall x : D,
    bot =< x.
  Proof.
    intros x.
    apply (proj2_sig (supremum_always_exists_in_CompleteLattice (finite []))).
    intros x' H.
    now inversion H; subst.
  Qed.

  Global Hint Resolve bot_isBottom : my_hints.

  Lemma initialize_cofixpoint {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
    forall f : D >=> D,
    proj1_sig (nu f) == proj1_sig (ParameterizedGreatestFixedpoint f) bot.
  Proof with eauto with *.
    intros f.
    symmetry.
    unfold ParameterizedGreatestFixedpoint, G_f.
    assert (H := nu_isSupremum (exist isMonotonicMap (fun y : D => proj1_sig f (or_plus bot y)) (G_f_aux_x_isMonotonic f bot))).
    assert (H0 := nu_isSupremum f).
    simpl in *.
    apply Poset_asym.
    - apply H.
      intros x H1.
      apply H0...
      unfold member, postfixed_points in *.
      transitivity (proj1_sig f (or_plus bot x)).
      + exact H1.
      + apply (proj2_sig f), or_plus_le_iff...
    - apply H0.
      intros x H1.
      apply H...
      unfold member, postfixed_points in *.
      transitivity (proj1_sig f x).
      + apply H1.
      + apply (proj2_sig f)...
  Qed.

  Lemma unfold_cofixpoint {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
    forall f : D >=> D,
    forall x : D,
    proj1_sig (ParameterizedGreatestFixedpoint f) x == proj1_sig f (or_plus x (proj1_sig (ParameterizedGreatestFixedpoint f) x)).
  Proof with eauto with *.
    intros f x.
    unfold ParameterizedGreatestFixedpoint.
    simpl.
    unfold G_f.
    assert (H := nu_isSupremum (exist isMonotonicMap (fun y : D => proj1_sig f (or_plus x y)) (G_f_aux_x_isMonotonic f x))).
    simpl in *.
    apply (GreatestFixedPointOfMonotonicMaps (fun y : D => proj1_sig f (or_plus x y)) (G_f_aux_x_isMonotonic f x))...
  Qed.

  Lemma accumulate_cofixpoint {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
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

  Theorem Compositionality_of_ParameterizedCoinduction {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
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
    assert (claim1 : g1 =< G_f f (or_plus r (or_plus g1 g2))).
    { transitivity (G_f f r1).
      - apply H.
      - apply G_f_isMonotoinc.
        transitivity (or_plus r g2); [apply H1 | apply or_plus_le_iff]...
    }
    assert (claim2 : g2 =< G_f f (or_plus r (or_plus g1 g2))).
    { transitivity (G_f f r2).
      - apply H0.
      - apply G_f_isMonotoinc.
        transitivity (or_plus r g1); [apply H2 | apply or_plus_le_iff]...
    }
    assert (claim3 : or_plus g1 g2 =< G_f f (or_plus r (or_plus g1 g2))) by now apply or_plus_le_iff.
    apply accumulate_cofixpoint...
  Qed.

  Lemma FullCharacterization_of_ParameterizedGreatestFixedPoint {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
    forall f : D >=> D,
    forall G_f' : D >=> D,
    (forall x : D, proj1_sig G_f' x == proj1_sig f (or_plus x (proj1_sig G_f' x))) ->
    (forall x : D, forall y : D, y =< proj1_sig G_f' (or_plus x y) -> y =< proj1_sig G_f' x) ->
    (G_f' == ParameterizedGreatestFixedpoint f).
  Proof with eauto with *. (* Thanks to SoonWon Moon *)
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

  Theorem KnasterTarski {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
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

  Lemma CoinductionPrinciple {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} (b : D >=> D) :
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

  Local Notation "f 'is-compatible-for' b" := (isCompatibleFor f b) (at level 70, no associativity) : type_scope.

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

  Lemma supremum_isCompatibleFor {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} :
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

  Definition companion {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} : (D >=> D) -> (D >=> D) :=
    fun b : D >=> D =>
    exist isMonotonicMap (proj1_sig (supremum_m (fun f : D >=> D => compose_m f b =< compose_m b f))) (supOfMonotonicMaps_isMonotonic (fun f : D >=> D => compose_m f b =< compose_m b f))
  .

  Section companion_properties.

  Context {D : Type} `{D_isPoset : isPoset D} `{D_isCompleteLattice : @isCompleteLattice D D_isPoset} (b : D >=> D).

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

  Global Instance ensemble_isCompleteLattice {A : Type} : @isCompleteLattice (ensemble A) ensemble_isPoset :=
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

  Class isLabelledGraph (Vertex : Type) (Label : Type) : Type :=
    { getEdgesIn : Vertex -> ensemble (Vertex * Label)
    }
  .

  Global Notation " v1 '~~[' label ']~>' v2 " := (member (v1, label) (getEdgesIn v2)) (at level 70, no associativity) : type_scope.

  Global Reserved Notation " v1 '~~~[' labels ']~>*' v2 " (at level 70, no associativity).

  Inductive walkLabelledGraph {Vertex : Type} {Label : Type} `{G : isLabelledGraph Vertex Label} (v0 : Vertex) : list Label -> Vertex -> Prop :=
  | walk_nil : v0 ~~~[ nil ]~>* v0
  | walk_cons (v1 : Vertex) (v2 : Vertex) (l : Label) (ls : list Label) (H_step : v1 ~~[ l ]~> v2) (H_walk : v0 ~~~[ ls ]~>* v1) : v0 ~~~[ cons l ls ]~>* v2
  where " v1 '~~~[' labels ']~>*' v2 " := (walkLabelledGraph v1 labels v2) : type_scope.

  Section IDEA_OF_SIMULATION.

  Local Hint Constructors walkLabelledGraph : core.

  Context {Src : Type} {Tgt : Type} {Eff : Type} `{src_system : isLabelledGraph Src Eff} `{tgt_system : isLabelledGraph Tgt Eff}.

  Variant simF (R : ensemble (Src * Tgt)) : ensemble (Src * Tgt) :=
  | preservesSimilarity (s1 : Src) (t1 : Tgt) (H_sim : forall e : Eff, forall t2 : Tgt, t1 ~~[ e ]~> t2 -> exists s2 : Src, s1 ~~[ e ]~> s2 /\ member (s2, t2) R) : member (s1, t1) (simF R)
  .

  Lemma simF_isMonotonicMap :
    isMonotonicMap simF.
  Proof.
    intros R1 R2 H_incl [s1 t1] H_in1.
    inversion H_in1; subst.
    constructor.
    intros e t2 t1_e_t2.
    destruct (H_sim e t2 t1_e_t2) as [s2 [s1_e_s2 H_in2]].
    now exists s2; firstorder.
  Qed.

  Lemma R_le_simF_R_iff_R_walk_diag (R : ensemble (Src * Tgt)) :
    R =< simF R <-> (forall s0 : Src, forall t0 : Tgt, member (s0, t0) R -> forall es : list Eff, forall t : Tgt, t0 ~~~[ es ]~>* t -> exists s : Src, s0 ~~~[ es ]~>* s /\ member (s, t) R).
  Proof with eauto.
    split.
    - intros R_le_simF_R s0 t0 R_s0_t0 es t t0_es_t.
      induction t0_es_t as [| t1 t2 e es t1_e_t2 t0_es_t1 IH].
      + exists s0...
      + destruct IH as [s1 [s0_es_s1 R_s1_t1]].
        assert (H_in1 : member (s1, t1) (simF R)) by exact (R_le_simF_R (s1, t1) R_s1_t1).
        inversion H_in1; subst.
        destruct (H_sim e t2 t1_e_t2) as [s2 [s1_e_s2 R_s2_t2]].
        exists s2...
    - intros H_incl [s1 t1] H_in1.
      constructor.
      intros e t2 t1_e_t2.
      destruct (H_incl s1 t1 H_in1 (cons e nil) t2 (walk_cons t1 t1 t2 e nil t1_e_t2 (walk_nil t1))) as [s2 [s1_e_s2 H_in2]].
      inversion s1_e_s2; subst.
      inversion H_walk; subst...
  Qed.

  Definition simulates : Tgt -> Src -> Prop :=
    fun t : Tgt =>
    fun s : Src =>
    member (s, t) (unions (fun R : ensemble (Src * Tgt) => isSubsetOf R (simF R)))
  .

  Lemma simulates_walk_diag :
    forall s0 : Src,
    forall t0 : Tgt,
    simulates t0 s0 <-> (forall es : list Eff, forall t : Tgt, t0 ~~~[ es ]~>* t -> exists s : Src, s0 ~~~[ es ]~>* s /\ simulates t s).
  Proof.
    assert (claim1 : forall s : Src, forall t : Tgt, simulates t s <-> exists R : ensemble (Src * Tgt), member (s, t) R /\ isSubsetOf R (simF R)) by exact (fun s : Src => fun t : Tgt => in_unions_iff (s, t) (postfixed_points simF)).
    intros s0 t0.
    split.
    - intros t0_simulates_s0 es t t0_es_t.
      destruct (proj1 (claim1 s0 t0) t0_simulates_s0) as [R [H_in0 R_le_simF_R]].
      destruct (proj1 (R_le_simF_R_iff_R_walk_diag R) R_le_simF_R s0 t0 H_in0 es t t0_es_t) as [s [s0_es_s H_in]].
      now exists s; firstorder.
    - intros H_cond.
      destruct (H_cond nil t0 (walk_nil t0)) as [s [s0_nil_s t_simulates_s]].
      now inversion s0_nil_s; subst.
  Qed.

  Definition simulation : ensemble (Src * Tgt) :=
    proj1_sig (paco (exist isMonotonicMap simF simF_isMonotonicMap)) bot
  .

  Lemma in_simulation_iff :
    forall s : Src,
    forall t : Tgt,
    member (s, t) simulation <-> simulates t s.
  Proof.
    set (nu_simF := proj1_sig (nu (exist isMonotonicMap simF simF_isMonotonicMap))).
    assert (claim1 : nu_simF == simulation) by exact (PaCo_init simF simF_isMonotonicMap).
    exact (fun s : Src => fun t : Tgt => Setoid_sym (simulates t s) (member (s, t) simulation) (claim1 (s, t))).
  Qed.

(* "Notes"
  [#1]
  The definition of homomorphism between two coalgebras for an endofunctor is given by:
  > Let $(X \in Ob(C), alpha : X -> F X)$ and $(Y \in Ob(C), beta : Y -> F Y)$ be two coalgebras for an endofunctor $F$ of a category $C$.
  > Then an arrow $f : X -> Y$ is an $F$-coalgebra homomorphism if and only if it satisfies $F(f) ∘ alpha = beta ∘ f$.
  [#2]
  Let $R : Src -> Tgt -> Prop$ be given.
  Then $R$ is a bisimulation iff the left-lower path guarantees the existence of the right-upper path on each following squares:
  % =================== % =================== %
  % Forward Simulation  % Backward Simulation %
  % =================== % =================== %
  %  t_1 ~~[ e ]~> t_2  %  s_1 ~~[ e ]~> s_2  %
  %   |             |   %   |             |   %
  %   |             |   %   |             |   %
  %  R^T           R^T  %   R             R   %
  %   |             |   %   |             |   %
  %  \|/           \|/  %  \|/           \|/  %
  %  s_1 ~~[ e ]~> s_2  %  t_1 ~~[ e ]~> t_2  %
  % =================== % =================== %
  where $R^T$ denotes $flip R$ -- that is, the equivalence $R s t <-> R^T t s$ holds for any $s : Src$ and $t : Tgt$.
  The left one asserts:
  > $R s_1 t_1$ holds and the state of $Src$ moves from $s_1$ to $s_2$ along an edge labelled $e$
  > only if the state of $Tgt$ moves from $t_1$ to $t_2$ along the edge labelled $e$ and $R s_2 t_2$ holds.
  It means that $R$ is a simulation of $Src$ in $Tgt$.
  The right one asserts:
  > $R s_1 t_1$ holds and the state of $Tgt$ moves from $t_1$ to $t_2$ along an edge labelled $e$
  > only if the state of $Src$ moves from $s_1$ to $s_2$ along the edge labelled $e$ and $R s_2 t_2$ holds.
  It means that $R^T$ is a simulation of $Tgt$ in $Src$.
  [#3]
  ```coq
  Section TMP_SECT_1.
  Definition ensemble (A : Type) : Type := A -> Prop.
  Definition member {A : Type} : A -> ensemble A -> Prop := fun x : A => fun X : ensemble A => X x.
  Variable Eff : Type.
  Inductive my_map {A : Type} {B : Type} (f : A -> B) (X : ensemble (A * Eff)) : ensemble (B * Eff) :=
  | in_my_map : forall a : A, forall e : Eff, member (a, e) X -> member (f a, e) (my_map f X)
  .
  End TMP_SECT_1.
  ```
  Define $F : Type -> Type := fun A : Type => ensemble (A * Eff)$.
  Then, noting the fact that $my_map f X$ exactly represents to the set ${ (f a, e) | (a, e) \in X }$,
  we find that $my_map$ is a covariant map thus $(F, my_map)$ is an endofunctor of the category of types.
  If a coalgebra $(State : Type, State_trans : State -> F State)$ for the endofunctor $F$ is given,
  we will write $st1 ~~[ e ]~> st2$ whenever $member (st1, e) (State_trans st2)$ holds.
  Let $(Src, Src_trans) and $(Tgt, Tgt_trans)$ be two $F$-coalgebras.
  Then every function $f : Src -> Tgt$ is an $F$-coalgebra homomorphism iff:
  (1) $my_map f (Src_trans s_2) \subseteq Tgt_trans (f s_2)$ for all $s_2 : Src$, and
  (2) $Tgt_trans (f s_2) \subseteq my_map f (Src_trans s_2)$ for all $s_2 : Src$.
  Note that (1) is equivalent to (1') and that (2) is equivalent to (2'):
  (1') $s_1 ~~[ e ]~> s_2 \implies f s_1 ~~[ e ]~> f s_2$, and
  (2') $t_1 ~~[ e ]~> f s_2 \implies \exists s_1, s_1 ~~[ e ]~> s_2 \land t_1 = f s_1$.
  Therefore the left-lower path guarantees the existence of the right-upper path and vice versa on the following square:
  % =========================== %
  % $F$-coalgebra homomorphism  %
  % =========================== %
  %      t_1 ~~[ e ]~> t_2      %
  %       |             |       %
  %       |             |       %
  %      R^T           R^T      %
  %       |             |       %
  %      \|/           \|/      %
  %      s_1 ~~[ e ]~> s_2      %
  % =========================== %
  where $R : Src -> Tgt -> Prop := fun s : Src => fun t : Tgt => f s = t$.
  [#4]
  Therefore we can conclude:
  > From any given $F$-coalgebra homomorphism,
  > we can derive a simulation,
  > which is generally not a bisimulation,
  > where $F : Type -> Type$ is the endofunctor given in [#3].
*)

  End IDEA_OF_SIMULATION.

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

  Context {D : Type} `{D_isPoset : isPoset D}.

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
    { isOpen := @isOpen_ScottTopology D D_isPoset
    ; open_full := @open_full_ScottTopology D D_isPoset D_requiresCompletePartialOrder
    ; open_unions := @open_unions_ScottTopology D D_isPoset D_requiresCompletePartialOrder
    ; open_intersection := @open_intersection_ScottTopology D D_isPoset D_requiresCompletePartialOrder
    ; open_ext_eq := @open_ext_eq_ScottTopology D D_isPoset D_requiresCompletePartialOrder
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
