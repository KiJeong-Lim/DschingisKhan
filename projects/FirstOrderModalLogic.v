Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module FirstOrderModalLogic.

  Import ListNotations MyUtilities MyEnsemble.

  Definition ivar : Set :=
    nat
  .

  Definition ivar_eq_dec :
    forall x : ivar,
    forall y : ivar,
    {x = y} + {x <> y}.
  Proof.
    exact (fun x y => Nat.eq_dec x y).
  Defined.

  Variant logical_symbol : Set :=
  | CONTRADICTION : logical_symbol
  | NEGATION : logical_symbol
  | CONJUNCTION : logical_symbol
  | DISJUNCTION : logical_symbol
  | IMPLICATION : logical_symbol
  | BICONDITIONAL : logical_symbol 
  | FORALL : logical_symbol
  | EXISTS : logical_symbol
  | EQUAL : logical_symbol
  | BOX : logical_symbol
  | DIA : logical_symbol
  .

  Definition logical_symbol_eq_dec :
    forall s1 : logical_symbol,
    forall s2 : logical_symbol,
    {s1 = s2} + {s1 <> s2}.
  Proof.
    induction s1;
    destruct s2;
    (left; congruence) || (right; congruence).
  Defined.

  Inductive ty_expr : Set :=
  | TyI : ty_expr
  | TyO : ty_expr
  | ARR (arg_ty : ty_expr) (ret_ty : ty_expr) : ty_expr
  .

  Definition ty_expr_eq_dec :
    forall ty1 : ty_expr,
    forall ty2 : ty_expr,
    {ty1 = ty2} + {ty1 <> ty2}.
  Proof.
    induction ty1 as [ | | ty1_1 IH1 ty1_2 IH2];
    destruct ty2 as [ | | ty2_1 ty2_2];
    repeat (
      first
      [ now ((left; congruence) || (right; congruence))
      | destruct (IH1 ty2_1); destruct (IH2 ty2_2)
      ]
    ).
  Defined.

  Global Declare Custom Entry object_level_ty_expr.
  Global Notation " 'i' " := (TyI) (in custom object_level_ty_expr at level 0, no associativity).
  Global Notation " 'o' " := (TyO) (in custom object_level_ty_expr at level 0, no associativity).
  Global Notation " ty1 '->' ty2 " := (ARR ty1 ty2) (in custom object_level_ty_expr at level 1, right associativity).
  Global Notation " ty " := (ty) (in custom object_level_ty_expr, ty ident).
  Global Notation " '(' ty ')' " := (ty) (in custom object_level_ty_expr at level 0, no associativity).

  Global Declare Scope object_level_ty_expr_scope.
  Global Notation " '\ty[' ty  ']' " := (ty) (ty custom object_level_ty_expr at level 1, at level 0, no associativity) : object_level_ty_expr_scope.

  Local Open Scope object_level_ty_expr_scope.

  Definition get_type_of_logical_symbol (s : logical_symbol) : ty_expr :=
    match s with
    | CONTRADICTION => \ty[ o ]
    | NEGATION => \ty[ o -> o ]
    | CONJUNCTION => \ty[ o -> o -> o ]
    | DISJUNCTION => \ty[ o -> o -> o ]
    | IMPLICATION => \ty[ o -> o -> o ]
    | BICONDITIONAL => \ty[ o -> o -> o ]
    | FORALL => \ty[ (i -> o) -> o ]
    | EXISTS => \ty[ (i -> o) -> o ]
    | EQUAL => \ty[ i -> i -> o ]
    | BOX => \ty[ o -> o ]
    | DIA => \ty[ o -> o ]
    end
  .

  Section SYNTAX_OF_FIRST_ORDER_MODAL_LOGIC.

  Let arity : Set :=
    nat
  .

  Set Primitive Projections.

  Record language_signature : Set :=
    { func_arity_env : forall f_id : nat, option arity
    ; pred_arity_env : forall p_id : nat, option arity
    }
  .

  Unset Primitive Projections.

  Variable lsig : language_signature.

  Variant symbol : Set :=
  | PrimSym (s : logical_symbol) : symbol
  | FuncSym (fsym_id : {f_id : nat | lsig.(func_arity_env) f_id <> None}) : symbol
  | PredSym (psym_id : {p_id : nat | lsig.(pred_arity_env) p_id <> None}) : symbol
  .

  Definition get_type_of_symbol (c : symbol) : ty_expr :=
    match c with
    | PrimSym s => get_type_of_logical_symbol s
    | FuncSym fsym_id => nat_rec (fun _ => ty_expr) \ty[ i ] (fun _ ty1 => \ty[ i -> ty1 ]) (fromJust (lsig.(func_arity_env) (proj1_sig fsym_id)) (proj2_sig fsym_id))
    | PredSym psym_id => nat_rec (fun _ => ty_expr) \ty[ o ] (fun _ ty1 => \ty[ i -> ty1 ]) (fromJust (lsig.(pred_arity_env) (proj1_sig psym_id)) (proj2_sig psym_id))
    end
  .

  Inductive tm_expr : Set :=
  | VAR (x : ivar) : tm_expr
  | CON (c : symbol) : tm_expr
  | APP (t1 : tm_expr) (t2 : tm_expr) : tm_expr
  | LAM (y : ivar) (t1 : tm_expr) : tm_expr
  .

  Inductive typeOf : tm_expr -> ty_expr -> Set :=
  | TypeOfVAR (x : ivar) : typeOf (VAR x) \ty[ i ]
  | TypeOfCON (c : symbol) : typeOf (CON c) (get_type_of_symbol c)
  | TypeOfAPP (t1 : tm_expr) (t2 : tm_expr) (ty1 : ty_expr) (ty2 : ty_expr) (H1 : typeOf t1 \ty[ ty1 -> ty2 ]) (H2 : typeOf t2 \ty[ ty1 ]) : typeOf (APP t1 t2) \ty[ ty2 ]
  | TypeOfLAM (y : ivar) (t1 : tm_expr) (ty1 : ty_expr) (H1 : typeOf t1 \ty[ ty1 ]) : typeOf (LAM y t1) \ty[ i -> ty1 ]
  .

  End SYNTAX_OF_FIRST_ORDER_MODAL_LOGIC.

  Arguments PrimSym {lsig}.
  Arguments FuncSym {lsig}.
  Arguments PredSym {lsig}.

  Arguments VAR {lsig}.
  Arguments CON {lsig}.
  Arguments APP {lsig}.
  Arguments LAM {lsig}.

  Arguments typeOf {lsig}.
  Arguments TypeOfVAR {lsig}.
  Arguments TypeOfCON {lsig}.
  Arguments TypeOfAPP {lsig}.
  Arguments TypeOfLAM {lsig}.

  Section SEMANTICS_OF_FIRST_ORDER_MODAL_LOGIC.

  Variable Univ : Type.

  Fixpoint interprete0_ty (ty : ty_expr) {struct ty} : Type :=
    match ty with
    | \ty[ i ] => Univ
    | \ty[ o ] => Prop
    | \ty[ arg_ty -> ret_ty ] => interprete0_ty arg_ty -> interprete0_ty ret_ty
    end
  .

  Variable Worlds : Type.

  Let wUniv : Type :=
    Worlds -> Univ
  .

  Let wProp : Type :=
    Worlds -> Prop
  .

  Fixpoint interpreteW_ty (ty : ty_expr) {struct ty} : Type :=
    match ty with
    | \ty[ i ] => wUniv
    | \ty[ o ] => wProp
    | \ty[ arg_ty -> ret_ty ] => interpreteW_ty arg_ty -> interpreteW_ty ret_ty
    end
  .

  Definition interpreteW_func (lsig : language_signature) (fsym_id : {f_id : nat | lsig.(func_arity_env) f_id <> None}) :
    (Worlds -> interprete0_ty (get_type_of_symbol lsig (FuncSym fsym_id))) ->
    interpreteW_ty (get_type_of_symbol lsig (FuncSym fsym_id)).
  Proof.
    simpl; generalize (fromJust (lsig.(func_arity_env) (proj1_sig fsym_id)) (proj2_sig fsym_id)) as n.
    induction n as [ | n IH]; [exact (fun val_w => val_w) | exact (fun kon_w arg_w => IH (fun w => kon_w w (arg_w w)))].
  Defined.

  Definition interpreteW_pred (lsig : language_signature) (psym_id : {p_id : nat | lsig.(pred_arity_env) p_id <> None}) :
    (Worlds -> interprete0_ty (get_type_of_symbol lsig (PredSym psym_id))) ->
    interpreteW_ty (get_type_of_symbol lsig (PredSym psym_id)).
  Proof.
    simpl; generalize (fromJust (lsig.(pred_arity_env) (proj1_sig psym_id)) (proj2_sig psym_id)) as n.
    induction n as [ | n IH]; [exact (fun val_w => val_w) | exact (fun kon_w arg_w => IH (fun w => kon_w w (arg_w w)))].
  Defined.

  Variable accessibility_relation : ensemble (Worlds * Worlds).

  Local Notation " w1 '`is_accessible_to`' w2 " := (member (w1, w2) accessibility_relation) (at level 70, no associativity) : type_scope.

  Definition interpreteW_logical (s : logical_symbol) : interpreteW_ty (get_type_of_logical_symbol s) :=
    match s with
    | CONTRADICTION => fun w => False
    | NEGATION => fun wP1 w => ~ wP1 w
    | CONJUNCTION => fun wP1 wP2 w => wP1 w /\ wP2 w
    | DISJUNCTION => fun wP1 wP2 w => wP1 w \/ wP2 w
    | IMPLICATION => fun wP1 wP2 w => wP1 w -> wP2 w
    | BICONDITIONAL => fun wP1 wP2 w => wP1 w <-> wP2 w
    | FORALL => fun wP1' w => forall y_val : wUniv, wP1' y_val w
    | EXISTS => fun wP1' w => exists y_val : wUniv, wP1' y_val w
    | EQUAL => fun x_val y_val w => x_val w = y_val w
    | BOX => fun wP1 w => forall w' : Worlds, w `is_accessible_to` w' -> wP1 w'
    | DIA => fun wP1 w => exists w' : Worlds, w `is_accessible_to` w' /\ wP1 w'
    end
  .

  Variable lsig : language_signature.

  Variable func_env : forall fsym_id : {f_id : nat | lsig.(func_arity_env) f_id <> None}, Worlds -> interprete0_ty (get_type_of_symbol lsig (FuncSym fsym_id)).

  Variable pred_env : forall psym_id : {p_id : nat | lsig.(pred_arity_env) p_id <> None}, Worlds -> interprete0_ty (get_type_of_symbol lsig (PredSym psym_id)).

  Definition interpreteW_symbol (c : symbol lsig) : interpreteW_ty (get_type_of_symbol lsig c) :=
    match c with
    | PrimSym s => interpreteW_logical s
    | FuncSym fsym_id => interpreteW_func lsig fsym_id (func_env fsym_id) 
    | PredSym psym_id => interpreteW_pred lsig psym_id (pred_env psym_id)
    end
  .

  Fixpoint interpreteW_tm (ivar_env : ivar -> wUniv) (tm : tm_expr lsig) (ty : ty_expr) (H : typeOf tm ty) {struct H} : interpreteW_ty ty :=
    match H with
    | TypeOfVAR x => ivar_env x
    | TypeOfCON c => interpreteW_symbol c
    | TypeOfAPP t1 t2 ty1 ty2 H1 H2 => (interpreteW_tm ivar_env t1 \ty[ ty1 -> ty2 ] H1) (interpreteW_tm ivar_env t2 \ty[ ty1 ] H2)
    | TypeOfLAM y t1 ty1 H1 => (fun y_val => interpreteW_tm (fun z => if ivar_eq_dec y z then y_val else ivar_env z) t1 \ty[ ty1 ] H1)
    end
  .

  End SEMANTICS_OF_FIRST_ORDER_MODAL_LOGIC.

End FirstOrderModalLogic.
