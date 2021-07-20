Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import DschingisKhan.pure.MyStructures.

Module PosetTheory.

  Import BasicSetoidTheory BasicPosetTheory MyEnsemble.

  Definition isSupremum {D : Type} `{D_isPoset : isPoset D} : D -> ensemble D -> Prop :=
    fun sup_X : D =>
    fun X : ensemble D =>
    forall d : D,
    sup_X =< d <-> (forall x : D, member x X -> x =< d)
  .

  Global Hint Unfold isSupremum : my_hints.

  Lemma isSupremum_upperbound {D : Type} `{D_isPoset : isPoset D} :
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

  Global Hint Resolve isSupremum_upperbound : my_hints.

  Lemma isSupremum_isSubsetOf {D : Type} `{D_isPoset : isPoset D} :
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

  Global Hint Resolve isSupremum_isSubsetOf : my_hints.

  Lemma isSupremum_ext {D : Type} `{D_isPoset : isPoset D} :
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

  Global Hint Resolve isSupremum_ext : my_hints.

  Lemma isSupremum_unique {D : Type} `{D_isPoset : isPoset D} :
    forall X : ensemble D,
    forall sup1 : D,
    isSupremum sup1 X ->
    forall sup2 : D,
    isSupremum sup2 X <-> sup1 == sup2.
  Proof with eauto with *.
    intros X sup1 H sup2...
  Qed.

  Global Hint Resolve isSupremum_unique : my_hints.

  Definition image_sup {D : Type} `{D_isPoset : isPoset D} : ensemble (ensemble D) -> ensemble D :=
    fun Xs : ensemble (ensemble D) =>
    fun sup_X : D =>
    exists X : ensemble D, member X Xs /\ isSupremum sup_X X
  .

  Global Hint Unfold image_sup : my_hints.

  Lemma sup_in_image_sup {D : Type} `{D_isPoset : isPoset D} :
    forall X : ensemble D,
    forall sup_X : D,
    isSupremum sup_X X ->
    forall Xs : ensemble (ensemble D),
    member X Xs ->
    member sup_X (image_sup Xs).
  Proof with eauto with *.
    intros X sup_X H Xs H0...
  Qed.

  Global Hint Resolve sup_in_image_sup : my_hints.

  Lemma sup_image_sup_isGreaterThan {D : Type} `{D_isPoset : isPoset D} :
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

  Global Hint Resolve sup_image_sup_isGreaterThan : my_hints.

  Lemma isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs {D : Type} `{D_isPoset : isPoset D} :
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

  Global Hint Resolve isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs : my_hints.

  Definition isInfimum {D : Type} `{D_isPoset : isPoset D} : D -> ensemble D -> Prop :=
    fun inf_X : D =>
    fun X : ensemble D=>
    forall d : D,
    d =< inf_X <-> (forall x : D, member x X -> d =< x)
  .

  Global Hint Unfold isInfimum : my_hints.

  Lemma isInfimum_unique {D : Type} `{D_isPoset : isPoset D} :
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

  Global Hint Resolve isInfimum_unique : my_hints.

  Lemma compute_Infimum {D : Type} `{D_isPoset: isPoset D} :
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

  Global Hint Resolve compute_Infimum : my_hints.

  Lemma make_Supremum_to_Infimum_of_upper_bounds {D : Type} `{D_isPoset : isPoset D} :
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

  Definition prefixed_points {D : Type} `{D_isPoset : isPoset D} : (D -> D) -> ensemble D :=
    fun f : D -> D =>
    fun x : D =>
    f x =< x
  .

  Global Hint Unfold prefixed_points : my_hints.

  Definition fixed_points {D : Type} `{D_isSetoid : isSetoid D} : (D -> D) -> ensemble D :=
    fun f : D -> D =>
    fun x : D =>
    x == f x
  .

  Global Hint Unfold fixed_points : my_hints.

  Definition postfixed_points {D : Type} `{D_isPoset : isPoset D} : (D -> D) -> ensemble D :=
    fun f : D -> D =>
    fun x : D =>
    x =< f x
  .

  Global Hint Unfold postfixed_points : my_hints.

  Definition isLeastFixedPoint {D : Type} `{D_isPoset : isPoset D} : D -> (D -> D) -> Prop :=
    fun lfp : D =>
    fun f : D -> D =>
    member lfp (fixed_points f) /\ (forall fix_f : D, member fix_f (fixed_points f) -> lfp =< fix_f)
  .

  Global Hint Unfold isLeastFixedPoint : my_hints.

  Theorem LeastFixedPointOfMonotonicMaps {D : Type} `{D_isPoset : isPoset D} :
    forall f : D -> D,
    isMonotonicMap f ->
    forall lfp : D,
    isInfimum lfp (prefixed_points f) ->
    isLeastFixedPoint lfp f.
  Proof with eauto with *.
    intros f H lfp H0.
    split.
    - assert (H1 : f lfp =< lfp).
      { apply H0.
        intros x H1.
        assert (H2 : lfp =< x).
        { transitivity (f x).
          - apply H0...
          - apply H1.
        }
        transitivity (f x)...
      }
      apply Poset_asym.
      + apply H0...
      + apply H1.
    - intros fix_f H1.
      apply H0...
  Qed.

  Definition isGreatestFixedPoint {D : Type} `{D_isPoset : isPoset D} : D -> (D -> D) -> Prop :=
    fun gfp : D =>
    fun f : D -> D =>
    member gfp (fixed_points f) /\ (forall fix_f : D, member fix_f (fixed_points f) -> fix_f =< gfp)
  .

  Global Hint Unfold isGreatestFixedPoint : my_hints.

  Theorem GreatestFixedPointOfMonotonicMaps {D : Type} `{D_isPoset : isPoset D} :
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
    - intros fix_f H1.
      apply H0...
  Qed.

  Definition isSupremumIn {D : Type} `{D_isPoset : isPoset D} : D -> ensemble D -> ensemble D -> Prop :=
    fun sup_X : D =>
    fun X : ensemble D =>
    fun subPoset : ensemble D =>
    member sup_X subPoset /\ (forall d : D, member d subPoset -> sup_X =< d <-> (forall x : D, member x X -> x =< d))
  .

  Local Instance SubPoset0 {D : Type} {P : D -> Prop} (D_requiresPoset : isPoset D) : isPoset (@sig D P) :=
    SubPoset D_requiresPoset
  .

  Lemma isSupremumIn_iff {D : Type} `{D_isPoset : isPoset D} :
    forall P : D -> Prop,
    forall sup_X : @sig D P,
    forall X : ensemble (@sig D P),
    isSupremumIn (proj1_sig sup_X) (image (@proj1_sig D P) X) P <-> isSupremum sup_X X.
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
          rewrite in_image_iff in H2.
          destruct H2 as [x' [H2 H3]].
          rewrite H2.
          enough (H4 : x' =< d) by apply H4...
    - intros H.
      split.
      + membership.
      + intros d H0.
        set (d' := exist P d H0).
        assert (H1 : sup_X =< d' <-> (forall x' : @sig D P, member x' X -> x' =< d')) by apply H.
        split.
        * intros H2 x H3.
          rewrite in_image_iff in H3.
          destruct H3 as [x' [H3 H4]].
          rewrite H3.
          enough (H5 : x' =< d') by apply H5...
        * intros H2.
          apply H1.
          intros x' H3.
          apply H2...
  Qed.

End PosetTheory.

Module ConstructiveDomainTheory.

  Import ListNotations BasicSetoidTheory BasicPosetTheory MyEnsemble BasicTopology PosetTheory.

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
    split...
  Qed.

  Global Notation "D1 >=> D2" := (@sig (D1 -> D2) (fun f : D1 -> D2 => isMonotonicMap f)) (at level 50, no associativity) : type_scope.

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
    intros d x1 x2 H...
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
      apply (in_image f_i (fun f_i' : D >=> D' => proj1_sig f_i' x2))...
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
      assert (H2 : f' =< exist isMonotonicMap (supOfMonotonicMaps fs) (supOfMonotonicMaps_isMonotonic fs)).
      { intros x.
        simpl.
        apply (proj2_sig (supremum_always_exists_in_CompleteLattice (image (fun f_i : D >=> D' => proj1_sig f_i x) fs)))...
        apply (in_image f' (fun f_i' : D >=> D' => proj1_sig f_i' x))...
      }
      transitivity (exist isMonotonicMap (supOfMonotonicMaps fs) (supOfMonotonicMaps_isMonotonic fs))...
    - intros H x.
      simpl.
      assert (claim1 : forall x' : D', member x' (image (fun f_i : D >=> D' => proj1_sig f_i x) fs) -> x' =< proj1_sig f x).
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
    destruct (supremum_always_exists_in_CompleteLattice (fun x : D => x =< f x)) as [gfp H0].
    exists gfp.
    split...
    apply GreatestFixedPointOfMonotonicMaps...
  Qed.

  Definition nu {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : forall f : D >=> D, {gfp : D | isGreatestFixedPoint gfp (proj1_sig f)} :=
    fun f : D >=> D =>
    match supremum_always_exists_in_CompleteLattice (fun x : D => x =< proj1_sig f x) with
    | exist _ gfp H => exist _ gfp (GreatestFixedPointOfMonotonicMaps (proj1_sig f) (proj2_sig f) gfp H)
    end
  .

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
    x =< proj1_sig f x -> x =< proj1_sig (nu f).
  Proof with eauto with *.
    intros f x H.
    unfold nu.
    destruct (supremum_always_exists_in_CompleteLattice (fun x0 : D => x0 =< proj1_sig f x0)) as [gfp H0].
    apply H0...
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
    unfold nu.
    simpl.
    destruct (supremum_always_exists_in_CompleteLattice (fun y : D => y =< proj1_sig f (or_plus x2 y))) as [gfp2 H0].
    simpl in *.
    assert (claim1 : G_f f x1 == proj1_sig f (or_plus x1 (G_f f x1))) by apply (proj2_sig (nu (exist _ (G_f_aux x1) (G_f_aux_isMonotonic f x1)))).
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
    unfold G_f, nu.
    simpl.
    destruct (supremum_always_exists_in_CompleteLattice (fun y : D => y =< proj1_sig f1 (or_plus x y))) as [gfp1 H0].
    destruct (supremum_always_exists_in_CompleteLattice (fun y : D => y =< proj1_sig f2 (or_plus x y))) as [gfp2 H1].
    apply H0...
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
    unfold ParameterizedGreatestFixedpoint, G_f, nu.
    simpl.
    destruct (supremum_always_exists_in_CompleteLattice (fun y : D => y =< proj1_sig f (or_plus bot y))) as [gfp1 H].
    destruct (supremum_always_exists_in_CompleteLattice (fun y : D => y =< proj1_sig f y)) as [gfp2 H0].
    simpl.
    apply Poset_asym.
    - apply H.
      intros x H1.
      apply H0...
      unfold member in *.
      transitivity (proj1_sig f (or_plus bot x)).
      + apply H1.
      + apply (proj2_sig f), or_plus_le_iff...
    - apply H0.
      intros x H1.
      apply H...
      unfold member in *.
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
    unfold G_f, nu.
    simpl.
    destruct (supremum_always_exists_in_CompleteLattice (fun y : D => y =< proj1_sig f (or_plus x y))) as [gfp1 H].
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
        split.
        - apply or_plus_le_iff...
        - apply le_or_plus.
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
        transitivity (or_plus r g2).
        + apply H1.
        + apply or_plus_le_iff...
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
    intros x.
    apply Poset_asym...
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
    assert ( claim3 :
      forall x : D,
      member x W_hat ->
      member (proj1_sig f x) W_hat
    ).
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
      + apply (proj2_sig f), H0...
      + apply H1.
    }
    assert (claim5 : q =< fix_f).
    { apply H0.
      intros x [H1 H2]...
    }
    assert (claim6 : fix_f == proj1_sig f fix_f).
    { apply Poset_asym.
      - apply H0...
        split.
        + apply (proj2_sig f)...
        + apply claim3...
      - apply claim4.
    }
    exists fix_f.
    split.
    - apply claim6.
    - intros x H1.
      split.
      + intros H2 x' H3.
        transitivity q...
      + intros H2...
        apply H0...
        split...
        apply q_is_lub_of_W...
  Qed.

  Lemma ConinductionPrinciple {D : Type} `{D_isCompleteLattice : isCompleteLattice D} (b : D >=> D) :
    forall x : D,
    x =< proj1_sig (nu b) <-> (exists y : D, x =< y /\ y =< proj1_sig b y).
  Proof with eauto with *.
    intros x.
    split.
    - unfold nu.
      destruct (supremum_always_exists_in_CompleteLattice (fun y : D => y =< proj1_sig b y)) as [gfp H].
      simpl.
      assert (H0 := GreatestFixedPointOfMonotonicMaps (proj1_sig b) (proj2_sig b) gfp H).
      simpl.
      intros H1.
      exists gfp.
      split; [apply H1 | apply Poset_refl1, H0].
    - intros [gfp [H H0]].
      transitivity gfp.
      + apply H.
      + apply PrincipleOfTarski...
  Qed.

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
        apply (in_image f_i (fun f_i' : D >=> D => proj1_sig b (proj1_sig f_i' x)))...
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
      apply (proj2_sig b).
      apply H1...
      apply (in_image f_i (fun f_i' : D >=> D => proj1_sig f_i' x))...
    }
    intros x...
  Qed.

  Definition companion {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : (D >=> D) -> (D >=> D) :=
    fun b : D >=> D =>
    exist isMonotonicMap (proj1_sig (supremum_m (fun f : D >=> D => compose_m f b =< compose_m b f))) (supOfMonotonicMaps_isMonotonic (fun f : D >=> D => compose_m f b =< compose_m b f))
  .

  Lemma companion_isCompatibleFor {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall b : D >=> D,
    companion b is-compatible-for b.
  Proof with eauto with *.
    intros b.
    apply supremum_isCompatibleFor...
  Qed.

  Lemma companion_isTheGreatestCompatibleFunction {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall b : D >=> D,
    forall f : D >=> D,
    f is-compatible-for b ->
    f =< companion b.
  Proof with eauto with *.
    intros b f H.
    unfold companion.
    set (F := fun f_i : D >=> D => compose_m f_i b =< compose_m b f_i).
    apply (supOfMonotonicMaps_isSupremum F)...
  Qed.

  Lemma b_le_t {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall b : D >=> D,
    b =< companion b.
  Proof with eauto with *.
    intros b.
    apply companion_isTheGreatestCompatibleFunction...
  Qed.

  Lemma id_le_t {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall b : D >=> D,
    id_m =< companion b.
  Proof with eauto with *.
    intros b.
    apply companion_isTheGreatestCompatibleFunction, id_isCompatibleFor.
  Qed.

  Lemma tt_le_t {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall b : D >=> D,
    compose_m (companion b) (companion b) =< companion b.
  Proof with eauto with *.
    intros b.
    apply companion_isTheGreatestCompatibleFunction, compose_isCompatibleFor; apply companion_isCompatibleFor.
  Qed.

  Definition isDirected {D : Type} `{D_isPoset : isPoset D} : ensemble D -> Prop :=
    fun X : ensemble D =>
    nonempty X /\ (forall x1 : D, member x1 X -> forall x2 : D, member x2 X -> exists x3 : D, member x3 X /\ x1 =< x3 /\ x2 =< x3)
  .

  Class isCompletePartialOrder (D : Type) `{D_isPoset : isPoset D} : Type :=
    { bottom_exists :
      {min_D : D | forall x : D, min_D =< x}
    ; square_up_exists :
      forall X : ensemble D,
      isDirected X ->
      {sup_X : D | isSupremum sup_X X}
    }
  .

  Local Instance CompleteLattice_isCompletePartialOrder {D : Type} `{D_isPoset : isPoset D} (D_requiresCompleteLattice : @isCompleteLattice D D_isPoset) : @isCompletePartialOrder D D_isPoset :=
    { bottom_exists :=
      exist _ bot bot_isBottom
    ; square_up_exists :=
      fun X : ensemble D =>
      fun _ : isDirected X =>
      supremum_always_exists_in_CompleteLattice X
    }
  .

  Global Program Instance ScottTopology {D : Type} `{D_isPoset : isPoset D} (D_requiresCompletePartialOrder : @isCompletePartialOrder D D_isPoset) : isTopologicalSpace D :=
    { isOpen :=
      fun O : ensemble D =>
      (forall x : D, forall y : D, member x O -> x =< y -> member y O) /\ (forall X : ensemble D, isDirected X -> forall sup_X : D, isSupremum sup_X X -> member sup_X O -> nonempty (intersection X O))
    }
  . 

  Next Obligation with eauto with *.
    split.
    - firstorder.
    - intros X [[x H0] H1] sup_X H2 H3...
  Qed.

  Next Obligation with eauto with *.
    split.
    - intros x y H1 H2.
      assert (H3 := proj1 (H0 x) H1).
      apply in_unions_iff in H3.
      destruct H3 as [X [H3 H4]].
      assert (H5 := proj1 (H X H4) x y).
      apply H0, in_unions_iff...
    - intros.
      inversion H1; subst.
      assert (H6 := proj1 (H0 sup_X) H3).
      rewrite in_unions_iff in H6.
      destruct H6 as [X' [H6 H7]].
      destruct (proj2 (H X' H7) X H1 sup_X H2 H6) as [x H8].
      exists x.
      revert H8.
      repeat (rewrite in_intersection_iff).
      intros [H8 H9].
      split...
      apply H0...
  Qed.

  Next Obligation with eauto with *.
    split.
    - intros x y H4 H5.
      apply H1.
      assert (H6 := proj1 (H1 x) H4).
      revert H6.
      repeat (rewrite in_intersection_iff).
      intros [H6 H7].
      split...
    - intros.
      inversion H4; subst.
      assert (H9 := proj1 (H1 sup_X) H6).
      revert H9.
      repeat (rewrite in_intersection_iff).
      intros [H9 H10].
      destruct (H3 X H4 sup_X H5 H9) as [x1 H11].
      destruct (H2 X H4 sup_X H5 H10) as [x2 H12].
      rewrite in_intersection_iff in H11, H12.
      destruct H11 as [H11 H13].
      destruct H12 as [H12 H14].
      destruct (H8 x1 H11 x2 H12) as [x [H15 [H16 H17]]].
      assert (H18 : member x xs).
      { apply H1.
        apply in_intersection_iff.
        split...
      }
      exists x...
  Qed.

  Lemma bot_of_direct_product {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} `{D_isCompletePartialOrder : @isCompletePartialOrder D D_isPoset} `{D'_isCompletePartialOrder : @isCompletePartialOrder D' D'_isPoset} :
    forall p : D * D',
    (proj1_sig bottom_exists, proj1_sig bottom_exists) =< p.
  Proof with eauto with *.
    intros p.
    split; simpl; apply (proj2_sig bottom_exists).
  Qed.

  Lemma directed_subset_of_direct_product {D : Type} {D' : Type} `{D_isPoset : isPoset D} `{D'_isPoset : isPoset D'} :
    forall X : ensemble (D * D'),
    isDirected X ->
    isDirected (image fst X) /\ isDirected (image snd X).
  Proof with eauto with *.
    intros X [[[x0 y0] H] H0].
    split.
    - split.
      + exists x0...
        apply (in_image (x0, y0) fst)...
      + intros p1 H1 p2 H2.
        inversion H1; subst.
        rename x into x1.
        inversion H2; subst.
        rename x into x2.
        destruct (H0 x1 H3 x2 H4) as [[x3 y3] [H5 [[H6 H7] [H8 H9]]]].
        simpl in *.
        exists x3.
        split...
        apply (in_image (x3, y3) fst)...
    - split.
      + exists y0.
        apply (in_image (x0, y0) snd)...
      + intros p1 H1 p2 H2.
        inversion H1; subst.
        rename x into x1.
        inversion H2; subst.
        rename x into x2.
        destruct (H0 x1 H3 x2 H4) as [[x3 y3] [H5 [[H6 H7] [H8 H9]]]].
        simpl in *.
        exists y3.
        split...
        apply (in_image (x3, y3) snd)...
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
        apply (in_image (x', y') fst)...
      + apply H0...
        apply (in_image (x', y') snd)...
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

End ConstructiveDomainTheory.

Module PowerSetLattice.

  Import BasicSetoidTheory BasicPosetTheory MyEnsemble PosetTheory ConstructiveDomainTheory.

  Global Instance ensemble_isPoset {A : Type} : isPoset (ensemble A) :=
    arrow_isPoset Prop_isPoset
  .

  Lemma isSubsetOf_le {A : Type} :
    forall X : ensemble A,
    forall Y : ensemble A,
    (X =< Y) = (isSubsetOf X Y).
  Proof with eauto with *.
    reflexivity.
  Qed.

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

  Section PACO.

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

  CoInductive PaCo (F : ensemble A -> ensemble A) : ensemble A -> ensemble A :=
  | mkPaCo :
    forall X : ensemble A,
    forall Y : ensemble A,
    isSubsetOf X (MyUnion (PaCo F Y) Y) ->
    isSubsetOf (F X) (PaCo F Y)
  .

  Lemma PaCo_fold :
    forall F : ensemble A -> ensemble A,
    isMonotonicMap F ->
    forall Y : ensemble A,
    isSubsetOf (F (or_plus (PaCo F Y) Y)) (PaCo F Y).
  Proof with eauto with *.
    intros F H Y.
    cofix CIH.
    apply mkPaCo.
    intros a H0.
    apply in_union_iff in H0...
  Qed.

  Lemma PaCo_unfold :
    forall F : ensemble A -> ensemble A,
    isMonotonicMap F ->
    forall Y : ensemble A,
    isSubsetOf (PaCo F Y) (F (or_plus (PaCo F Y) Y)).
  Proof with eauto with *.
    intros F H Y a H0.
    inversion H0; subst.
    assert (H3 : isSubsetOf (F X) (F (MyUnion (PaCo F Y) Y))) by now apply (H X (MyUnion (PaCo F Y) Y)).
    assert (H4 : isSubsetOf (MyUnion (PaCo F Y) Y) (or_plus (PaCo F Y) Y)).
    { intros a' H'.
      apply in_union_iff in H'...
    }
    assert (H5 := H (MyUnion (PaCo F Y) Y) (or_plus (PaCo F Y) Y) H4).
    apply H5, H3...
  Qed.

  Lemma PaCo_preserves_monotonicity :
    forall F : ensemble A -> ensemble A,
    isMonotonicMap F ->
    isMonotonicMap (PaCo F).
  Proof with eauto with *.
    intros F H X1 X2 H0.
    assert (H1 := PaCo_unfold F H X1).
    cofix CIH.
    intros a H2.
    apply (mkPaCo F (MyUnion (PaCo F X1) X1) X2).
    - intros a' [H2' | H2']; [left; apply CIH | right; apply H0]...
    - apply (H (or_plus (PaCo F X1) X1)).
      + apply or_plus_le_iff.
        split; intros a' H2'; [left | right]...
      + apply H1...
  Qed.

  Lemma PaCo_init :
    forall F : ensemble A -> ensemble A,
    isMonotonicMap F ->
    forall nu0 : ensemble A,
    isSupremum nu0 (postfixed_points F) ->
    nu0 == PaCo F bot.
  Proof with eauto with *.
    intros F H nu0 H0.
    assert (H1 := PaCo_fold F H bot).
    assert (H2 := PaCo_unfold F H bot).
    assert (claim1 : PaCo F bot == F (PaCo F bot)).
    { apply Poset_asym.
      - transitivity (F (or_plus (PaCo F bot) bot)).
        + apply H2.
        + apply (H (or_plus (PaCo F bot) bot)), or_plus_le_iff...
      - transitivity (F (or_plus (PaCo F bot) bot)).
        + apply (H (PaCo F bot))...
        + apply H1.
    }
    assert (claim2 := GreatestFixedPointOfMonotonicMaps F H nu0 H0).
    assert (claim3 : F nu0 =< PaCo F bot).
    { cofix CIH.
      apply mkPaCo.
      intros a H3.
      left.
      apply CIH, H0...
    }
    assert (claim4 : nu0 =< PaCo F bot).
    { transitivity (F nu0).
      - apply H0...
      - apply claim3.
    }
    apply Poset_asym...
  Qed.

  Lemma PaCo_acc :
    forall F : ensemble A -> ensemble A,
    isMonotonicMap F ->
    forall X : ensemble A,
    forall Y : ensemble A,
    isSubsetOf Y (PaCo F X) <-> isSubsetOf Y (PaCo F (MyUnion X Y)).
  Proof with eauto with *.
    intros F F_mon X Y.
    split.
    - intros H0.
      assert (H1 : X =< MyUnion X Y) by now constructor 1.
      assert (H2 := PaCo_preserves_monotonicity F F_mon X (MyUnion X Y) H1).
      intros a H3.
      apply H2, H0...
    - intros H_star.
      assert (claim1 := PaCo_unfold F F_mon (MyUnion X Y)).
      assert (claim2 : isSubsetOf (F (or_plus (PaCo F (MyUnion X Y)) (MyUnion X Y))) (F (or_plus (PaCo F (MyUnion X Y)) X))).
      { apply F_mon.
        intros a H.
        apply in_union_iff in H.
        apply in_union_iff.
        destruct H as [H | [H | H]]; [left | right | left]...
      }
      assert (claim3 : or_plus (PaCo F (MyUnion X Y)) X =< MyUnion X (PaCo F (MyUnion X Y))).
      { intros a H.
        apply in_union_iff in H.
        destruct H as [H | H]; [right | left]...
      }
      assert (claim4 : member (PaCo F (MyUnion X Y)) (postfixed_points (fun Z : ensemble A => F (MyUnion X Z)))).
      { intros a H.
        apply (F_mon (or_plus (PaCo F (MyUnion X Y)) X) _ claim3), claim2... 
      }
      destruct (supremum_always_exists_in_CompleteLattice (postfixed_points (fun Z : ensemble A => F (MyUnion X Z)))) as [nu0 claim5].
      assert (tarski : forall Z : ensemble A, Z =< F (MyUnion X Z) -> Z =< nu0).
      { intros Z H.
        apply claim5...
      }
      assert (claim6 : or_plus (PaCo F (MyUnion X Y)) X =< MyUnion X (PaCo F (MyUnion X Y))).
      { intros a H.
        apply in_union_iff in H.
        destruct H as [H | H]; [right | left]...
      }
      assert (claim7 : PaCo F (MyUnion X Y) =< F (MyUnion X (PaCo F (MyUnion X Y)))).
      { intros a H.
        apply (F_mon (or_plus (PaCo F (MyUnion X Y)) X) _ claim6), claim2, claim1...
      }
      assert (claim8 := tarski (PaCo F (MyUnion X Y)) claim7).
      assert (claim9 : isMonotonicMap (fun Z : ensemble A => F (MyUnion X Z))).
      { intros X1 X2 H.
        apply F_mon.
        intros a [H0 | H0]; [left | right; apply H]...
      }
      destruct (GreatestFixedPointOfMonotonicMaps (fun Z : ensemble A => F (MyUnion X Z)) claim9 nu0 claim5) as [claim10 claim11].
      assert (claim12 : nu0 =< F (MyUnion X nu0)) by now apply Poset_refl1.
      assert (claim13 : nu0 =< PaCo F X).
      { transitivity (F (MyUnion X nu0)).
        - apply claim12.
        - cofix CIH.
          apply mkPaCo.
          intros a [H | H]; [right | left; apply CIH, claim12]...
      }
      assert (claim14 : Y =< PaCo F (MyUnion X Y)) by apply H_star.
      enough (therefore_we_can_conclude : Y =< PaCo F X)...
  Qed.

  Definition accPaCo : ensemble A -> (ensemble A -> ensemble A) -> ensemble A -> Prop :=
    fun X : ensemble A =>
    fun F : ensemble A -> ensemble A =>
    fun Y : ensemble A =>
    forall Z : ensemble A,
    isSubsetOf Y Z ->
    isSubsetOf X Z ->
    isSubsetOf X (PaCo F Z)
  .

  Theorem accPaCo_iff :
    forall F : ensemble A -> ensemble A,
    isMonotonicMap F ->
    forall X : ensemble A,
    forall Y : ensemble A,
    accPaCo X F Y <-> isSubsetOf X (PaCo F Y).
  Proof with eauto with *.
    unfold accPaCo.
    intros F F_mon X Y.
    split.
    - intros acc_hyp.
      apply (proj2 (PaCo_acc F F_mon Y X)), acc_hyp; intros a H; [left | right]...
    - intros acc_con.
      intros Z H H0.
      enough (it_is_sufficient_to_show : X =< (PaCo F Z)) by apply it_is_sufficient_to_show.
      transitivity (PaCo F (MyUnion Y X)).
      + apply (proj1 (PaCo_acc F F_mon Y X) acc_con).
      + apply (PaCo_preserves_monotonicity F F_mon).
        intros a [H1 | H1]; [apply H | apply H0]...
  Qed.

  Definition paco : (ensemble A >=> ensemble A) -> (ensemble A >=> ensemble A) :=
    fun F : ensemble A >=> ensemble A =>
    exist isMonotonicMap (PaCo (proj1_sig F)) (PaCo_preserves_monotonicity (proj1_sig F) (proj2_sig F))
  .

  Theorem paco_ParameterizedGreatestFixedpoint :
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
        * apply (PaCo_fold (proj1_sig F) (proj2_sig F) X).
    - intros X Y H.
      assert (claim1 : (proj1_sig (paco F) (or_plus X Y)) =< (PaCo (proj1_sig F) (MyUnion X Y))).
      { apply (PaCo_preserves_monotonicity (proj1_sig F) (proj2_sig F) (or_plus X Y) (MyUnion X Y)). 
        intros a H0.
        apply in_union_iff in H0.
        destruct H0 as [H0 | H0]; [left | right]...
      }
      apply (proj2 (PaCo_acc (proj1_sig F) (proj2_sig F) X Y)).
      enough (claim2 : Y =< PaCo (proj1_sig F) (MyUnion X Y)) by apply claim2...
  Qed.

  End PACO.

End PowerSetLattice.
