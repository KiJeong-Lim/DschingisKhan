Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import DschingisKhan.theories.Auxiliary.

Module DomainTheory.

  Import ListNotations.

  Import MyStructures.

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
    assert (claim1 := fun x : D => fun H1 : member x X1 => proj1 (H x) H1).
    assert (claim2 := fun x : D => fun H1 : member x X2 => proj2 (H x) H1).
    split...
    intros H1.
    intros x.
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
    intros Xs sup H X H0 sup_X H1.
    apply H...
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
      + intros H1 x' [X [H2 H3]].
        apply H3...
      + intros H1.
        apply H0.
        intros x' H2.
        inversion H2; subst.
        destruct (H xs H4) as [sup_xs H5].
        apply H5...
        apply H1...
    - intros H0 x.
      split.
      + intros H1 x' H2.
        inversion H2; subst.
        destruct (H xs H4) as [sup_xs H5].
        apply H5...
      + intros H1.
        apply H0.
        intros x' [X [H2 H3]].
        apply H3...
  Qed.

  Global Hint Resolve isSupremum_unions_Xs_iff_isSupremum_image_sup_Xs : my_hints.

  Class isCompleteLattice (D : Type) : Type :=
    { CompleteLattice_requiresPoset :> isPoset D
    ; supremum_always_exists_in_CompleteLattice :
      forall X : ensemble D,
      {sup_X : D | isSupremum sup_X X}
    }
  .

  Global Hint Resolve CompleteLattice_requiresPoset : my_hints.

  Lemma isInfimum_unique {A : Type} `{A_isPoset : isPoset A} :
    forall X : ensemble A,
    forall inf1 : A,
    isInfimum inf1 X ->
    forall inf2 : A,
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

  Lemma compute_Infimum_in_CompleteLattice {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall X : ensemble D,
    forall inf_X : D,
    isSupremum inf_X (fun d : D => forall x : D, member x X -> d =< x) ->
    isInfimum inf_X X.
  Proof with eauto with *.
    intros X inf_X H d.
    split.
    - intros H0 x H1.
      transitivity inf_X...
      apply H...
    - intros H0.
      apply H...
  Qed.

  Global Hint Resolve compute_Infimum_in_CompleteLattice : my_hints.

  Lemma make_Supremum_to_Infimum_of_upper_bounds {D : Type} `{D_isPoset : isPoset D} :
    forall X : ensemble D,
    forall sup_X : D,
    isSupremum sup_X X ->
    isInfimum sup_X (fun x : D => sup_X =< x).
  Proof with eauto with *.
    intros X sup_X H d.
    split.
    - intros H0 x H1.
      transitivity sup_X.
      + apply H0.
      + apply H...
    - intros H0.
      apply H0...
  Qed.

  Definition infimum_always_exists_in_CompleteLattice {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall X : ensemble D,
    {inf_X : D | isInfimum inf_X X}.
  Proof.
    intros X.
    destruct (supremum_always_exists_in_CompleteLattice (fun d : D => forall x : D, member x X -> d =< x)) as [inf_X H].
    exists inf_X.
    apply compute_Infimum_in_CompleteLattice, H.
  Defined.

  Lemma unions_isSupremum {A : Type} :
    forall Xs : ensemble (ensemble A),
    isSupremum (unions Xs) Xs.
  Proof with eauto with *.
    intros Xs X.
    split.
    - intros H xs H0.
      transitivity (unions Xs)...
      intros x H1.
      apply (in_unions xs)...
    - intros H x H0.
      inversion H0; subst.
      apply (H xs)...
  Qed.

  Global Instance ensemble_isCompleteLattice {A : Type} : isCompleteLattice (ensemble A) :=
    { CompleteLattice_requiresPoset := ensemble_isPoset
    ; supremum_always_exists_in_CompleteLattice :=
      fun Xs : ensemble (ensemble A) =>
      exist (fun unions_Xs : ensemble A => isSupremum unions_Xs Xs) (unions Xs) (unions_isSupremum Xs)
    }
  .

  Global Notation "D1 >~> D2" := ({f : D1 -> D2 | isMonotonicMap f}) (at level 25, no associativity) : type_scope.

  Definition isSupremumIn {D : Type} `{D_isPoset : isPoset D} : D -> ensemble D -> ensemble D -> Prop :=
    fun sup_X : D =>
    fun X : ensemble D =>
    fun subPoset : ensemble D =>
    member sup_X subPoset /\ (forall d : D, member d subPoset -> sup_X =< d <-> (forall x : D, member x X -> x =< d))
  .

  Global Program Instance MonotonicMap_isSetoid {D : Type} {D' : Type} (D_requiresPoset : isPoset D) (D'_requiresPoset : isPoset D') : isSetoid (D >~> D') :=
    { eqProp :=
      fun f1 : D >~> D' =>
      fun f2 : D >~> D' =>
      forall x : D,
      proj1_sig f1 x == proj1_sig f2 x
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Global Program Instance MonotonicMap_can_be_pointwise_partially_ordered {D : Type} {D' : Type} (D_requiresPoset : isPoset D) (D'_requiresPoset : isPoset D') : isPoset (D >~> D') :=
    { leProp :=
      fun f1 : D >~> D' =>
      fun f2 : D >~> D' =>
      forall x : D,
      proj1_sig f1 x =< proj1_sig f2 x
    ; Poset_requiresSetoid := MonotonicMap_isSetoid D_requiresPoset D'_requiresPoset
    }
  .

  Next Obligation with eauto with *.
    split...
  Qed.

  Next Obligation with firstorder with my_hints.
    split...
  Qed.

  Lemma id_isMonotonic {D : Type} `{D_isPoset : isPoset D} :
    isMonotonicMap (fun x : D => x).
  Proof with eauto with *.
    unfold isMonotonicMap...
  Qed.

  Definition id_m {D1 : Type} `{D1_isPoset : isPoset D1} : D1 >~> D1 :=
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

  Definition compose_m {D1 : Type} {D2 : Type} {D3 : Type} `{D1_isPoset : isPoset D1} `{D2_isPoset : isPoset D2} `{D3_isPoset : isPoset D3} : (D2 >~> D3) -> (D1 >~> D2) -> (D1 >~> D3) :=
    fun g : D2 >~> D3 =>
    fun f : D1 >~> D2 =>
    exist isMonotonicMap (fun x : D1 => proj1_sig g (proj1_sig f x)) (compose_isMonotonic (proj1_sig f) (proj2_sig f) (proj1_sig g) (proj2_sig g))
  .

  Definition supOfMonotonicMaps {D : Type} {D' : Type} `{D_isCompleteLattice : isCompleteLattice D} `{D'_isCompleteLattice : isCompleteLattice D'} : ensemble (D >~> D') -> D -> D' :=
    fun fs : ensemble (D >~> D') =>
    fun x : D =>
    proj1_sig (supremum_always_exists_in_CompleteLattice (image (fun f_i : D >~> D' => proj1_sig f_i x) fs))
  .

  Lemma supOfMonotonicMaps_isMonotonic {D : Type} {D' : Type} `{D_isCompleteLattice : isCompleteLattice D} `{D'_isCompleteLattice : isCompleteLattice D'} :
    forall fs : ensemble (D >~> D'),
    isMonotonicMap (supOfMonotonicMaps fs).
  Proof with eauto with *.
    intros fs x1 x2 H.
    unfold supOfMonotonicMaps.
    destruct (supremum_always_exists_in_CompleteLattice (image (fun f_i : D >~> D' => proj1_sig f_i x1) fs)) as [sup1 H0].
    destruct (supremum_always_exists_in_CompleteLattice (image (fun f_i : D >~> D' => proj1_sig f_i x2) fs)) as [sup2 H1].
    simpl.
    apply H0.
    intros x H2.
    inversion H2; subst.
    rename x0 into f_i.
    transitivity (proj1_sig f_i x2).
    - apply (proj2_sig f_i)...
    - apply H1...
      apply (in_image (fun f_i' : D >~> D' => proj1_sig f_i' x2))...
  Qed.

  Definition supremum_m {D : Type} {D' : Type} `{D_isCompleteLattice : isCompleteLattice D} `{D'_isCompleteLattice : isCompleteLattice D'} : ensemble (D >~> D') -> (D >~> D') :=
    fun F : ensemble (D >~> D') =>
    exist isMonotonicMap (supOfMonotonicMaps F) (supOfMonotonicMaps_isMonotonic F)
  .

  Lemma supOfMonotonicMaps_isSupremum {D : Type} {D' : Type} `{D_isCompleteLattice : isCompleteLattice D} `{D'_isCompleteLattice : isCompleteLattice D'} :
    forall fs : ensemble (D >~> D'),
    isSupremum (supremum_m fs) fs.
  Proof with eauto with *.
    unfold supremum_m.
    intros fs f.
    split.
    - intros H0 f' H1.
      transitivity (exist isMonotonicMap (supOfMonotonicMaps fs) (supOfMonotonicMaps_isMonotonic fs))...
      intros x.
      simpl.
      apply (proj2_sig (supremum_always_exists_in_CompleteLattice (image (fun f_i : D >~> D' => proj1_sig f_i x) fs)))...
      apply (in_image (fun f_i' : D >~> D' => proj1_sig f_i' x))...
    - intros H x.
      simpl.
      apply (proj2_sig (supremum_always_exists_in_CompleteLattice (image (fun f_i : D >~> D' => proj1_sig f_i x) fs)))...
      intros f' H0.
      inversion H0; subst.
      rename x0 into f'.
      apply (H f' H1 x).
  Qed.

  Global Instance MonotonicMaps_on_CompleteLattice_constitute_CompleteLattice {D : Type} {D' : Type} (D_requiresCompleteLattice : isCompleteLattice D) (D'_requiresCompleteLattice : isCompleteLattice D') : isCompleteLattice (D >~> D') :=
    { CompleteLattice_requiresPoset := MonotonicMap_can_be_pointwise_partially_ordered (@CompleteLattice_requiresPoset D D_requiresCompleteLattice) (@CompleteLattice_requiresPoset D' D'_requiresCompleteLattice)
    ; supremum_always_exists_in_CompleteLattice :=
      fun fs : ensemble (D >~> D') =>
      exist (fun sup_fs : D >~> D' => isSupremum sup_fs fs) (supremum_m fs) (supOfMonotonicMaps_isSupremum fs)
    }
  .

  Definition fixed_points {D : Type} `{D_isSetoid : isSetoid D} : (D -> D) -> ensemble D :=
    fun f : D -> D =>
    fun fix_f : D =>
    fix_f == f fix_f
  .

  Global Hint Unfold fixed_points : my_hints.

  Definition isLeastFixedPoint {D : Type} `{D_isPoset : isPoset D} : D -> (D -> D) -> Prop :=
    fun lfp : D =>
    fun f : D -> D =>
    member lfp (fixed_points f) /\ (forall fix_f : D, member fix_f (fixed_points f) -> lfp =< fix_f)
  .

  Global Hint Unfold isLeastFixedPoint : my_hints.

  Lemma LeastFixedPointOfMonotonicMaps {D : Type} `{D_isPoset : isPoset D} :
    forall f : D -> D,
    isMonotonicMap f ->
    forall lfp : D,
    isInfimum lfp (fun x : D => f x =< x) ->
    isLeastFixedPoint lfp f.
  Proof with eauto with *.
    intros f H lfp H0.
    split.
    - assert (H1 : f lfp =< lfp).
      { apply H0.
        intros x H1.
        transitivity (f x)...
        apply H...
        transitivity (f x)...
        apply H0...
      }
      apply Poset_asym.
      + apply H0...
      + apply H1.
    - intros fix_f H1.
      apply H0...
  Qed.

  Lemma LeastFixedPointInCompleteLattice {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D -> D,
    isMonotonicMap f ->
    exists lfp : D, isInfimum lfp (fun x : D => f x =< x) /\ isLeastFixedPoint lfp f.
  Proof with eauto with *.
    intros f H.
    destruct (infimum_always_exists_in_CompleteLattice (fun x : D => f x =< x)) as [lfp H0].
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
    isSupremum gfp (fun x : D => x =< f x) ->
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

  Lemma GreatestFixedPointInCompleteLattice {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D -> D,
    isMonotonicMap f ->
    exists gfp : D, isSupremum gfp (fun x : D => x =< f x) /\ isGreatestFixedPoint gfp f.
  Proof with eauto with *.
    intros f H.
    destruct (supremum_always_exists_in_CompleteLattice (fun x : D => x =< f x)) as [gfp H0].
    exists gfp.
    split...
    apply GreatestFixedPointOfMonotonicMaps...
  Qed.

  Definition nu {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : forall f : D >~> D, {gfp : D | isGreatestFixedPoint gfp (proj1_sig f)} :=
    fun f : D >~> D =>
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

  Lemma le_or_plus1 {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall x1 : D,
    forall x2 : D,
    x1 =< or_plus x1 x2.
  Proof.
    apply le_or_plus.
  Defined.

  Global Hint Resolve le_or_plus1 : my_hints.

  Lemma le_or_plus2 {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall x1 : D,
    forall x2 : D,
    x2 =< or_plus x1 x2.
  Proof.
    apply le_or_plus.
  Defined.

  Global Hint Resolve le_or_plus2 : my_hints.

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
    forall f : D >~> D,
    forall x : D,
    x =< proj1_sig f x -> x =< proj1_sig (nu f).
  Proof with eauto with *.
    intros f x H.
    unfold nu.
    destruct (supremum_always_exists_in_CompleteLattice (fun x0 : D => x0 =< proj1_sig f x0)) as [gfp H0].
    simpl.
    apply H0...
  Qed.

  Lemma StrongCoinduction {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >~> D,
    forall x : D,
    x =< proj1_sig (nu f) <-> x =< proj1_sig f (or_plus x (proj1_sig (nu f))).
  Proof with eauto with *.
    intros f.
    destruct (proj2_sig (nu f)) as [H H0].
    assert (claim1 : forall x : D, proj1_sig f (proj1_sig (nu f)) =< proj1_sig f (or_plus x (proj1_sig (nu f)))).
    { intros x.
      apply (proj2_sig f).
      apply le_or_plus.
    }
    intros x.
    split.
    - intros H1.
      transitivity (proj1_sig (nu f))...
    - intros H1.
      enough (claim2 : or_plus x (proj1_sig (nu f)) =< proj1_sig f (or_plus x (proj1_sig (nu f)))).
      { transitivity (proj1_sig f (or_plus x (proj1_sig (nu f)))).
        - apply H1.
        - apply PrincipleOfTarski.
          apply (proj2_sig f)... 
      }
      apply or_plus_le_iff...
  Qed.

  Example G_f_aux_isMonotonic {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >~> D,
    forall x : D,
    isMonotonicMap (fun y : D => proj1_sig f (or_plus x y)).
  Proof with eauto with *.
    intros f d x1 x2 H.
    apply (proj2_sig f).
    apply or_plus_le_iff.
    split.
    - apply le_or_plus.
    - transitivity x2...
  Qed.

  Definition G_f {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : (D >~> D) -> (D -> D) :=
    fun f : D >~> D =>
    let G_f_aux : D -> D -> D := fun x : D => fun y : D => proj1_sig f (or_plus x y) in
    fun x : D =>
    proj1_sig (nu (exist _ (G_f_aux x) (G_f_aux_isMonotonic f x)))
  .

  Lemma G_f_isMonotoinc {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >~> D,
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
      transitivity (or_plus x2 (G_f f x1)).
      + apply or_plus_le_iff...
      + apply or_plus_le_iff...
  Qed.

  Definition ParameterizedGreatestFixedpoint {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : (D >~> D) -> (D >~> D) :=
    fun f : D >~> D =>
    exist _ (G_f f) (G_f_isMonotoinc f)
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
    simpl.
    apply H0.
    unfold member.
    intros y H2.
    apply H1...
  Qed.

  Definition bot {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : D :=
    proj1_sig (supremum_always_exists_in_CompleteLattice empty)
  .

  Lemma bot_isBottom {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall x : D,
    bot =< x.
  Proof.
    intros x.
    apply (proj2_sig (supremum_always_exists_in_CompleteLattice empty)).
    intros x' H.
    inversion H; subst.
    contradiction H0.
  Qed.

  Global Hint Resolve bot_isBottom : my_hints.

  Lemma initialize_cofixpoint {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >~> D,
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
      + apply (proj2_sig f).
        apply or_plus_le_iff...
    - apply H0.
      intros x H1.
      apply H...
      unfold member in *.
      transitivity (proj1_sig f x).
      + apply H1.
      + apply (proj2_sig f)...
  Qed.

  Lemma unfold_cofixpoint {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >~> D,
    forall x : D,
    proj1_sig (ParameterizedGreatestFixedpoint f) x == proj1_sig f (or_plus x (proj1_sig (ParameterizedGreatestFixedpoint f) x)).
  Proof with eauto with *.
    intros f x.
    unfold ParameterizedGreatestFixedpoint.
    simpl.
    unfold G_f, nu.
    simpl.
    destruct (supremum_always_exists_in_CompleteLattice (fun y : D => y =< proj1_sig f (or_plus x y))) as [gfp1 H].
    simpl.
    assert (claim1 := GreatestFixedPointOfMonotonicMaps (fun y : D => proj1_sig f (or_plus x y)) (G_f_aux_isMonotonic f x) gfp1 H).
    apply claim1.
  Qed.

  Lemma accumulate_cofixpoint {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >~> D,
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
      { apply (proj2_sig f).
        apply or_plus_le_iff.
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
    forall f : D >~> D,
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
        transitivity (or_plus r g1).
        + apply H2.
        + apply or_plus_le_iff...
    }
    assert (H5 : or_plus g1 g2 =< G_f f (or_plus r (or_plus g1 g2))) by now apply or_plus_le_iff.
    apply accumulate_cofixpoint...
  Qed.

  Lemma FullCharacterization_of_ParameterizedGreatestFixedPoint {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >~> D,
    forall G_f' : D >~> D,
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
      - apply Poset_refl1.
        apply unfold_cofixpoint.
      - assert (H1 := H (or_plus x (proj1_sig (ParameterizedGreatestFixedpoint f) x))).
        transitivity (proj1_sig f (or_plus (or_plus x (proj1_sig (ParameterizedGreatestFixedpoint f) x)) (proj1_sig G_f' (or_plus x (proj1_sig (ParameterizedGreatestFixedpoint f) x))))).
        + apply (proj2_sig f).
          apply or_plus_le_iff.
          split.
          * transitivity (or_plus x (proj1_sig (ParameterizedGreatestFixedpoint f) x))...
          * transitivity (or_plus x (proj1_sig (ParameterizedGreatestFixedpoint f) x))...
        + apply Poset_refl2...
    }
    intros x.
    apply Poset_asym...
  Qed.

  Theorem KnasterTarski {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall f : D >~> D,
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
      + apply (proj2_sig f).
        apply H0...
      + apply H1.
    }
    assert (claim5 : q =< fix_f).
    { apply H0.
      intros x [H1 H2].
      apply H2.
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
      + intros H2.
        apply H0...
        split...
        apply q_is_lub_of_W...
  Qed.

  Lemma ConinductionPrinciple {D : Type} `{D_isCompleteLattice : isCompleteLattice D} (b : D >~> D) :
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
      split.
      + apply H1.
      + apply Poset_refl1.
        apply H0.
    - intros [gfp [H H0]].
      transitivity gfp.
      + apply H.
      + apply PrincipleOfTarski...
  Qed.

  Definition isCompatibleFor {D : Type} `{D_isPoset : isPoset D} : (D >~> D) -> (D >~> D) -> Prop :=
    fun f : D >~> D =>
    fun b : D >~> D =>
    forall x : D,
    proj1_sig f (proj1_sig b x) =< proj1_sig b (proj1_sig f x)
  .

  Global Hint Unfold isCompatibleFor : my_hints.

  Global Notation "f 'is-compatible-for' b" := (isCompatibleFor f b) (at level 70, no associativity) : type_scope.

  Lemma id_isCompatibleFor {D : Type} `{D_isPoset : isPoset D} :
    forall b : D >~> D,
    id_m is-compatible-for b.
  Proof with eauto with *.
    unfold isCompatibleFor, id_m.
    simpl...
  Qed.

  Lemma compose_isCompatibleFor {D : Type} `{D_isPoset : isPoset D} :
    forall b : D >~> D,
    forall f1 : D >~> D,
    forall f2 : D >~> D,
    f1 is-compatible-for b ->
    f2 is-compatible-for b ->
    (compose_m f1 f2) is-compatible-for b.
  Proof with eauto with *.
    unfold isCompatibleFor, compose_m.
    simpl.
    intros b f1 f2 H H0 x.
    transitivity (proj1_sig f1 (proj1_sig b (proj1_sig f2 x)))...
    apply (proj2_sig f1)...
  Qed.

  Lemma supremum_isCompatibleFor {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall b : D >~> D,
    forall F : ensemble (D >~> D),
    (forall f : D >~> D, member f F -> f is-compatible-for b) ->
    supremum_m F is-compatible-for b.
  Proof with eauto with *.
    intros b F H.
    set (F_b := fun x : D => image (fun f_i : D >~> D => proj1_sig f_i (proj1_sig b x)) F).
    set (sup_F_b := fun x : D => proj1_sig (supremum_always_exists_in_CompleteLattice (F_b x))).
    assert (claim1 : forall x : D, proj1_sig (supremum_m F) (proj1_sig b x) =< sup_F_b x).
    { intros x.
      unfold sup_F_b, supremum_m, supOfMonotonicMaps.
      destruct (supremum_always_exists_in_CompleteLattice (F_b x)) as [sup_F_b_x H0].
      simpl.
      destruct (supremum_always_exists_in_CompleteLattice (image (fun f_i : D >~> D => proj1_sig f_i (proj1_sig b x)) F)) as [sup_f_i_b_x H1].
      simpl.
      apply H1.
      intros x' H2.
      inversion H2; subst.
      rename x0 into f_i.
      apply H0...
    }
    set (b_F := fun x : D => image (fun f_i : D >~> D => proj1_sig b (proj1_sig f_i x)) F).
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
        apply (in_image (fun f_i' : D >~> D => proj1_sig b (proj1_sig f_i' x)))...
    }
    assert (claim3 : forall x : D, sup_b_F x =< proj1_sig b (proj1_sig (supremum_m F) x)).
    { intros x.
      unfold sup_b_F, supremum_m, supOfMonotonicMaps.
      destruct (supremum_always_exists_in_CompleteLattice (b_F x)) as [sup_b_F_x H0].
      simpl.
      destruct (supremum_always_exists_in_CompleteLattice (image (fun f_i : D >~> D => proj1_sig f_i x) F)) as [sup_f_i_x H1].
      simpl.
      apply H0.
      intros x' H2.
      inversion H2; subst.
      rename x0 into f_i.
      apply (proj2_sig b).
      apply H1...
      apply (in_image (fun f_i' : D >~> D => proj1_sig f_i' x) F)...
    }
    intros x.
    transitivity (sup_F_b x)...
  Qed.

  Definition companion {D : Type} `{D_isCompleteLattice : isCompleteLattice D} : (D >~> D) -> (D >~> D) :=
    fun b : D >~> D =>
    exist isMonotonicMap (proj1_sig (supremum_m (fun f : D >~> D => compose_m f b =< compose_m b f))) (supOfMonotonicMaps_isMonotonic (fun f : D >~> D => compose_m f b =< compose_m b f))
  .

  Lemma companion_isCompatibleFor {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall b : D >~> D,
    companion b is-compatible-for b.
  Proof with eauto with *.
    intros b.
    apply supremum_isCompatibleFor...
  Qed.

  Lemma companion_isTheGreatestCompatibleFunction {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall b : D >~> D,
    forall f : D >~> D,
    f is-compatible-for b ->
    f =< companion b.
  Proof with eauto with *.
    intros b f H.
    unfold companion.
    set (F := fun f_i : D >~> D => compose_m f_i b =< compose_m b f_i).
    apply (supOfMonotonicMaps_isSupremum F)...
  Qed.

  Lemma b_le_t {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall b : D >~> D,
    b =< companion b.
  Proof with eauto with *.
    intros b.
    apply companion_isTheGreatestCompatibleFunction...
  Qed.

  Lemma id_le_t {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall b : D >~> D,
    id_m =< companion b.
  Proof with eauto with *.
    intros b.
    apply companion_isTheGreatestCompatibleFunction, id_isCompatibleFor.
  Qed.

  Lemma tt_le_t {D : Type} `{D_isCompleteLattice : isCompleteLattice D} :
    forall b : D >~> D,
    compose_m (companion b) (companion b) =< companion b.
  Proof with eauto with *.
    intros b.
    apply companion_isTheGreatestCompatibleFunction.
    apply compose_isCompatibleFor.
    all: apply companion_isCompatibleFor.
  Qed.

  Definition isDirected {D : Type} `{D_isPoset : isPoset D} : ensemble D -> Prop :=
    fun X : ensemble D =>
    nonempty X /\ (forall x1 : D, member x1 X -> forall x2 : D, member x2 X -> exists x3 : D, member x3 X /\ x1 =< x3 /\ x2 =< x3)
  .

  Class isCompletePartialOrder (D : Type) : Type :=
    { CompletePartialOrder_requiresPoset :> isPoset D
    ; bottom_exists : {min_D : D | forall x : D, min_D =< x}
    ; square_up_exists :
      forall X : ensemble D,
      isDirected X ->
      {sup_X : D | isSupremum sup_X X}
    }
  .

  Global Program Instance CompleteLattice_isCompletePartialOrder {D : Type} (D_requiresCompleteLattice : isCompleteLattice D) : isCompletePartialOrder D :=
    { CompletePartialOrder_requiresPoset := CompleteLattice_requiresPoset
    }
  .

  Next Obligation.
    destruct (supremum_always_exists_in_CompleteLattice empty) as [min_D H].
    exists min_D.
    intros x.
    apply H.
    intros x' H0.
    inversion H0; subst.
    inversion H1.
  Defined.

  Next Obligation.
    apply supremum_always_exists_in_CompleteLattice.
  Defined.

  Global Program Instance ScottTopology_isTopologicalSpace {D : Type} (D_requiresCompletePartialOrder : isCompletePartialOrder D) : isTopologicalSpace D :=
    { isOpen :=
      fun O : ensemble D =>
      (forall x : D, forall y : D, member x O -> x =< y -> member y O) /\ (forall X : ensemble D, isDirected X -> forall sup_X : D, isSupremum sup_X X -> member sup_X O -> nonempty (intersection X O))
    }
  .

  Next Obligation with eauto with *.
    split...
    intros.
    destruct H as [[x H] H2]...
  Qed.

  Next Obligation with eauto with *.
    split.
    - intros.
      destruct H0.
      apply (in_unions xs)...
      apply (proj1 (H xs H2) x y)...
    - intros.
      inversion H0; subst.
      inversion H2; subst.
      destruct (proj2 (H xs H6) X H0 sup_X H1 H5) as [x H7].
      inversion H7; subst...
  Qed.

  Next Obligation with eauto with *.
    split.
    - intros.
      destruct H3...
    - intros.
      inversion H5; subst.
      destruct (H2 X H3 sup_X H4 H6) as [x1 H8].
      destruct (H1 X H3 sup_X H4 H7) as [x2 H9].
      inversion H3; subst.
      inversion H8; inversion H9; subst.
      destruct (H11 x1 H12 x2 H17) as [x [H14 [H15 H16]]].
      exists x...
  Qed.

End DomainTheory.
