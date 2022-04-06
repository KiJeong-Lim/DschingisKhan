Require Import DschingisKhan.Prelude.

Module Scratch.

  (** "1. CPO and CoLa" *)

  Definition isUpperBound {D : Hask.t} {requiresPoset : isPoset D} (upper_bound_of_X : D) (X : ensemble D) : Prop :=
    forall x : D, member x X -> x =< upper_bound_of_X
  .

  Definition isSupremumOf {D : Hask.t} {requiresPoset : isPoset D} (sup_X : D) (X : ensemble D) : Prop :=
    forall upper_bound_of_X : D, isUpperBound upper_bound_of_X X <-> sup_X =< upper_bound_of_X
  .

  Class isCoLa (D : Hask.t) {requiresPoset : isPoset D} : Type :=
    CoLa_isCompleteLattice (X : ensemble D)
    : {sup_X : D | isSupremumOf sup_X X}
  .

  Definition isDirectedSubset {D : Hask.t} {requiresPoset : isPoset D} (X : ensemble D) : Prop :=
    forall x1 : D, member x1 X ->
    forall x2 : D, member x2 X ->
    exists x3 : D, member x3 X /\
    <{ DIRECT : x1 =< x3 /\ x2 =< x3 }>
  .

  Class isCPO (D : Hask.t) {requiresPoset : isPoset D} : Type :=
    CPO_isCompletePartialOrder (X : ensemble D)
    (X_isDirected : isDirectedSubset X)
    : {sup_X : D | isSupremumOf sup_X X}
  .

  (** "2. Topology" *)

  Class isTopologicalSpace (A : Hask.t) : Type :=
    { isOpen (X : ensemble A) : Prop
    ; fullOpen
      : isOpen full
    ; unionsOpen
      (Xs : ensemble (ensemble A))
      (every_member_of_Xs_isOpen : forall X : ensemble A, member X Xs -> isOpen X)
      : isOpen (unions Xs)
    ; intersectionOpen
      (X1 : ensemble A)
      (X2 : ensemble A)
      (X1_isOpen : isOpen X1)
      (X2_isOpen : isOpen X2)
      : isOpen (intersection X1 X2)
    ; isOpen_eqProp_isOpen
      (X1 : ensemble A)
      (X2 : ensemble A)
      (X1_isOpen : isOpen X1)
      (X1_eq_X2 : X1 == X2)
      : isOpen X2
    }
  .

  (** "3. Semigroup, Monoid and Group" *)

  Section AXIOMS_OF_GROUP.

  Variable G : Hask.t.

  Variable requiresSetoid : isSetoid G.

  Class LawsOfSemigroup (add : G -> G -> G) : Prop :=
    { add_lifts_eqProp :> isBinaryOperationCompatibleWithSetoid add
    ; add_assoc :> isAssociativeBinaryOperation add
    }
  .

  Class LawsOfMonoid (add : G -> G -> G) (zero : G) : Prop :=
    { Monoid_requiresSemigroup :> LawsOfSemigroup add
    ; zero_id_add :> zero `isIdentityOf` add
    }
  .

  Class LawsOfGroup (add : G -> G -> G) (zero : G) (neg : G -> G) : Prop :=
    { Group_requiresMonoid :> LawsOfMonoid add zero
    ; neg_inv_add :> neg `isInverseOpFor` add
    }
  .

  End AXIOMS_OF_GROUP.

  Global Arguments LawsOfSemigroup (G) {requiresSetoid}.
  Global Arguments LawsOfMonoid (G) {requiresSetoid}.
  Global Arguments LawsOfGroup (G) {requiresSetoid}.

  Class Semigroup_sig (S : Hask.t) : Type :=
    { add : S -> S -> S
    }
  .

  Class isSemigroup (S : Hask.t) {requiresSetoid : isSetoid S} : Type :=
    { Semigroup_methods :> Semigroup_sig S
    ; obeysLawsOfSemigroup :> LawsOfSemigroup S add
    }
  .

  Class Monoid_sig (M : Hask.t) : Type :=
    { zero : M
    ; Monoid_has_Semigroup_methods :> Semigroup_sig M
    }
  .

  Class isMonoid (M : Hask.t) {requiresSetoid : isSetoid M} : Type :=
    { Monoid_methods :> Monoid_sig M
    ; obeysLawsOfMonoid :> LawsOfMonoid M add zero
    }
  .

  Class Group_sig (G : Hask.t) : Type :=
    { neg : G -> G
    ; Group_has_Monoid_methods :> Monoid_sig G
    }
  .

  Class isGroup (G : Hask.t) {requiresSetoid : isSetoid G} : Type :=
    { Group_methods :> Group_sig G
    ; obeysLawsOfGroup :> LawsOfGroup G add zero neg
    }
  .

  Class isAbelianGroup (G : Hask.t) {requiresSetoid : isSetoid G} : Type :=
    { AbelianGroup_isGroup :> isGroup G
    ; add_comm :> isCommutativeBinaryOperation add
    }
  .

  Class Rng_sig (R : Hask.t) : Type :=
    { mul : R -> R -> R
    }
  .

  Class isRng (R : Hask.t) {requiresSetoid : isSetoid R} : Type :=
    { Rng_add_isGroup :> isAbelianGroup R
    ; Rng_mul_methods :> Rng_sig R
    ; Rng_mul_isSemigroup :> LawsOfSemigroup R mul
    ; Rng_requires_mul_distr_add :> isDistributiveOver mul add
    }
  .

  Class Ring_sig (R : Hask.t) : Type :=
    { unity : R
    ; Ring_has_Rng_methods :> Rng_sig R
    }
  .

  Class isRig (R : Hask.t) {requiresSetoid : isSetoid R} : Type :=
    { Rig_add_isMonoid :> isMonoid R
    ; Rig_mul_methods :> Ring_sig R
    ; Rig_mul_isMonoid :> LawsOfMonoid R mul unity
    ; Rig_requires_mul_distr_add :> isDistributiveOver mul add
    }
  .

End Scratch.
