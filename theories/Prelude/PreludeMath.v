Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.

Module MathProps.

  Local Open Scope program_scope.

  Class Op1_preserves_eqProp {dom : Hask.t} {cod : Hask.t} {dom_isSetoid : isSetoid dom} {cod_isSetoid : isSetoid cod} (f : dom -> cod) : Prop :=
    unary_operation_lifts_eqProp (lhs1 : dom) (rhs1 : dom)
    (H_EQ1 : lhs1 == rhs1)
    : f lhs1 == f rhs1
  .

  Global Add Parametric Morphism {dom : Hask.t} {cod : Hask.t} {dom_isSetoid : isSetoid dom} {cod_isSetoid : isSetoid cod} (f : dom -> cod) {preserves_eqProp : Op1_preserves_eqProp f} :
    f with signature (eqProp ==> eqProp)
    as unary_operation_preserves_eqProp.
  Proof. intros x1 x2 H_x_eq; exact (unary_operation_lifts_eqProp x1 x2 H_x_eq). Defined.

  Class Op2_preserves_eqProp {dom1 : Hask.t} {dom2 : Hask.t} {cod : Hask.t} {dom1_isSetoid : isSetoid dom1} {dom2_isSetoid : isSetoid dom2} {cod_isSetoid : isSetoid cod} (f : dom1 -> dom2 -> cod) : Prop :=
    binary_operation_lifts_eqProp (lhs1 : dom1) (rhs1 : dom1) (lhs2 : dom2) (rhs2 : dom2)
    (H_EQ1 : lhs1 == rhs1)
    (H_EQ2 : lhs2 == rhs2)
    : f lhs1 lhs2 == f rhs1 rhs2
  .

  Global Add Parametric Morphism {dom1 : Hask.t} {dom2 : Hask.t} {cod : Hask.t} {dom1_isSetoid : isSetoid dom1} {dom2_isSetoid : isSetoid dom2} {cod_isSetoid : isSetoid cod} (f : dom1 -> dom2 -> cod) {preserves_eqProp : Op2_preserves_eqProp f} :
    f with signature (eqProp ==> eqProp ==> eqProp)
    as binary_operation_preserves_eqProp.
  Proof. intros x1 x2 H_x_eq y1 y2 H_y_eq; exact (binary_operation_lifts_eqProp x1 x2 y1 y2 H_x_eq H_y_eq). Defined.

  Class Op1_preserves_leProp {dom : Hask.t} {cod : Hask.t} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} (f : dom -> cod) : Prop :=
    unary_operation_lifts_leProp (lhs1 : dom) (rhs1 : dom)
    (H_LE1 : lhs1 =< rhs1)
    : f lhs1 =< f rhs1
  .

  Global Add Parametric Morphism {dom : Hask.t} {cod : Hask.t} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} (f : dom -> cod) {preserves_leProp : Op1_preserves_leProp f} :
    f with signature (leProp ==> leProp)
    as lifts_leProp_if_monotonic.
  Proof. intros x1 x2 H_x_le; exact (unary_operation_lifts_leProp x1 x2 H_x_le). Defined.

  Class Op2_preserves_leProp {dom1 : Hask.t} {dom2 : Hask.t} {cod : Hask.t} {dom1_isPoset : isPoset dom1} {dom2_isPoset : isPoset dom2} {cod_isSetoid : isPoset cod} (f : dom1 -> dom2 -> cod) : Prop :=
    binary_operation_lifts_leProp (lhs1 : dom1) (rhs1 : dom1) (lhs2 : dom2) (rhs2 : dom2)
    (H_LE1 : lhs1 =< rhs1)
    (H_LE2 : lhs2 =< rhs2)
    : f lhs1 lhs2 =< f rhs1 rhs2
  .

  Global Add Parametric Morphism {dom1 : Hask.t} {dom2 : Hask.t} {cod : Hask.t} {dom1_isPoset : isPoset dom1} {dom2_isPoset : isPoset dom2} {cod_isSetoid : isPoset cod} (f : dom1 -> dom2 -> cod) {preserves_leProp : Op2_preserves_leProp f} :
    f with signature (leProp ==> leProp ==> leProp)
    as lifts_leProp_if_monotonic2.
  Proof. intros x1 x2 H_x_le y1 y2 H_y_le; exact (binary_operation_lifts_leProp x1 x2 y1 y2 H_x_le H_y_le). Defined.

  Section STATEMENTS_FOR_OPERATION_PROPERTIES.

  Context {A : Hask.t} {requiresSetoid : isSetoid A}.

  Class Assoc (bin_op : A -> A -> A) : Prop :=
    associativity (x : A) (y : A) (z : A)
    : bin_op x (bin_op y z) == bin_op (bin_op x y) z
  .

  Class Comm (bin_op : A -> A -> A) : Prop :=
    commutativity (x : A) (y : A)
    : bin_op x y == bin_op y x
  .

  Class Idem (bin_op : A -> A -> A) : Prop :=
    idemponence (x : A)
    : bin_op x x == x
  .

  Class Distr (bin_op1 : A -> A -> A) (bin_op2 : A -> A -> A) : Prop :=
    { left_distr (x : A) (y : A) (z : A)
      : bin_op1 x (bin_op2 y z) == bin_op2 (bin_op1 x y) (bin_op1 x z)
    ; right_distr (x : A) (y : A) (z : A)
      : bin_op1 (bin_op2 y z) x == bin_op2 (bin_op1 y x) (bin_op1 z x)
    }
  .

  Class IdElemOf (e : A) (bin_op : A -> A -> A) : Prop :=
    { left_id (x : A)
      : bin_op e x == x
    ; right_id (x : A)
      : bin_op x e == x
    }
  .

  Class InvOpOf (inv : A -> A) (bin_op : A -> A -> A) : Prop :=
    { left_inv (x : A)
      : bin_op (inv x) x == x
    ; right_inv (x : A)
      : bin_op x (inv x) == x
    }
  .

  Class Absorption (bin_op1 : A -> A -> A) (bin_op2 : A -> A -> A) : Prop :=
    { abosortion_left (x : A) (y : A)
      : bin_op1 x (bin_op2 x y) == x
    ; abosortion_right (x : A) (y : A)
      : bin_op2 x (bin_op1 x y) == x
    }
  .

  End STATEMENTS_FOR_OPERATION_PROPERTIES.

  Global Infix " `distributesOver` " := Distr (at level 70, no associativity) : type_scope.
  Global Infix " `isIdentityOf` " := IdElemOf (at level 70, no associativity) : type_scope.
  Global Infix " `isInverseOpFor` " := InvOpOf (at level 70, no associativity) : type_scope.

  Class Countable (A : Hask.t) : Type :=
    { enum : nat -> A
    ; requiresRecursivelyEnumerable
      : forall x : A, exists n : nat, enum n = x
    }
  .

End MathProps.

Export MathProps.
