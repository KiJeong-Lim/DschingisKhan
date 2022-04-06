Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeUtil.

Module MathPrelude.

  Local Open Scope program_scope.

  (** "0. Utilities" *)

  Class isUnaryOperationCompatibleWithSetoid {dom : Hask.t} {cod : Hask.t} {dom_isSetoid : isSetoid dom} {cod_isSetoid : isSetoid cod} (f : dom -> cod) : Prop :=
    unary_operation_preserves_eqProp (lhs : dom) (rhs : dom)
    (H_EQ : lhs == rhs)
    : f lhs == f rhs
  .

  Class isBinaryOperationCompatibleWithSetoid {dom1 : Hask.t} {dom2 : Hask.t} {cod : Hask.t} {dom1_isSetoid : isSetoid dom1} {dom2_isSetoid : isSetoid dom2} {cod_isSetoid : isSetoid cod} (f : dom1 -> dom2 -> cod) : Prop :=
    binary_operation_preserves_eqProp (lhs1 : dom1) (rhs1 : dom1) (lhs2 : dom2) (rhs2 : dom2)
    (H_EQ1 : lhs1 == rhs1)
    (H_EQ2 : lhs2 == rhs2)
    : f lhs1 lhs2 == f rhs1 rhs2
  .

  Global Add Parametric Morphism {dom : Hask.t} {cod : Hask.t} {dom_isSetoid : isSetoid dom} {cod_isSetoid : isSetoid cod} (f : dom -> cod) {isCompatibleWith_eqProp : isUnaryOperationCompatibleWithSetoid f} :
    f with signature (eqProp ==> eqProp)
    as unary_operation_lifts_eqProp.
  Proof. intros x1 x2 H_x_eq; exact (isCompatibleWith_eqProp x1 x2 H_x_eq). Defined.

  Global Add Parametric Morphism {dom1 : Hask.t} {dom2 : Hask.t} {cod : Hask.t} {dom1_isSetoid : isSetoid dom1} {dom2_isSetoid : isSetoid dom2} {cod_isSetoid : isSetoid cod} (f : dom1 -> dom2 -> cod) {isCompatibleWith_eqProp : isBinaryOperationCompatibleWithSetoid f} :
    f with signature (eqProp ==> eqProp ==> eqProp)
    as binary_operation_lifts_eqProp.
  Proof. intros x1 x2 H_x_eq y1 y2 H_y_eq; exact (isCompatibleWith_eqProp x1 x2 y1 y2 H_x_eq H_y_eq). Defined.

  Section STATEMENTS_FOR_OPERATION_PROPERTIES.

  Context {A : Hask.t} {requiresSetoid : isSetoid A}.

  Class isAssociativeBinaryOperation (bin_op : A -> A -> A) : Prop :=
    bin_op_assoc (x : A) (y : A) (z : A)
    : bin_op x (bin_op y z) == bin_op (bin_op x y) z
  .

  Class isCommutativeBinaryOperation (bin_op : A -> A -> A) : Prop :=
    bin_op_comm (x : A) (y : A)
    : bin_op x y == bin_op y x
  .

  Class isIdempotentBinaryOperation (bin_op : A -> A -> A) : Prop :=
    idemponence (x : A) : bin_op x x == x
  .

  Class isDistributiveOver (bin_op1 : A -> A -> A) (bin_op2 : A -> A -> A) : Prop :=
    { left_distr (x : A) (y : A) (z : A)
      : bin_op1 x (bin_op2 y z) == bin_op2 (bin_op1 x y) (bin_op1 x z)
    ; right_distr (x : A) (y : A) (z : A)
      : bin_op1 (bin_op2 y z) x == bin_op2 (bin_op1 y x) (bin_op1 z x)
    }
  .

  Class isIdentity (e : A) (bin_op : A -> A -> A) : Prop :=
    { left_id (x : A)
      : bin_op e x == x
    ; right_id (x : A)
      : bin_op x e == x
    }
  .

  Class isInverseOperation (inv : A -> A) (bin_op : A -> A -> A) : Prop :=
    { left_inv (x : A)
      : bin_op (inv x) x == x
    ; right_inv (x : A)
      : bin_op x (inv x) == x
    }
  .

  Class linkedByAbsorptionLaw (bin_op1 : A -> A -> A) (bin_op2 : A -> A -> A) : Prop :=
    { abosortion_left (x : A) (y : A)
      : bin_op1 x (bin_op2 x y) == x
    ; abosortion_right (x : A) (y : A)
      : bin_op2 x (bin_op1 x y) == x
    }
  .

  End STATEMENTS_FOR_OPERATION_PROPERTIES.

  Global Infix " `distributesOver` " := isDistributiveOver (at level 70, no associativity) : type_scope.
  Global Infix " `isIdentityOf` " := isIdentity (at level 70, no associativity) : type_scope.
  Global Infix " `isInverseOpFor` " := isInverseOperation (at level 70, no associativity) : type_scope.

  Class isCountable (A : Hask.t) : Type :=
    { enum (n : nat) : A
    ; enumeratable (x : A)
      : exists n : nat, enum n = x
    }
  .

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

End MathPrelude.

Export MathPrelude.
