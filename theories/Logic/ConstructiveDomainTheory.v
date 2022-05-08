Require Import Coq.Program.Basics.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Math.BasicPosetTheory.

Module BasicCoLaTheory.

  Import MathProps MathClasses BasicPosetTheory DomainTheoryHelper.

  Local Existing Instances pair_isPoset arrow_isPoset.

  Definition getInfimumOf_inCoLa {D : Type} {requiresPoset : isPoset D} {requiresCoLa : isCoLa D} (X : ensemble D) : {inf_X : D | isInfimumOf inf_X X} :=
    let inf_X : D := proj1_sig (getSupremumOf_inCoLa (LowerBoundsOf X)) in
    @exist D (fun inf : D => isInfimumOf inf X) inf_X (proj2 (SupremumOfLowerBounds_isInfimum inf_X X) (proj2_sig (getSupremumOf_inCoLa (LowerBoundsOf X))))
  .

  Definition MonotonicMaps (dom : Type) (cod : Type) {dom_requiresPoset : isPoset dom} {cod_requiresPoset : isPoset cod} : Type :=
    @sig (Hask.arrow dom cod) (fun f : dom -> cod => isMonotonicMap f)
  .

  Local Instance MonotonicMaps_isPoset (dom : Type) (cod : Type) {dom_requiresPoset : isPoset dom} {cod_requiresPoset : isPoset cod} : isPoset (MonotonicMaps dom cod) :=
    subPoset (Hask.arrow dom cod) (requiresPoset := arrow_isPoset cod_requiresPoset)
  .

  Local Notation " '⟬' dom '⟶' cod '⟭' " := (MonotonicMaps dom cod) : type_scope.

End BasicCoLaTheory.

Module ParameterizedCoinduction.

  Import MathProps MathClasses BasicPosetTheory BasicCoLaTheory.

  Local Existing Instances pair_isPoset arrow_isPoset MonotonicMaps_isPoset.

End ParameterizedCoinduction.
