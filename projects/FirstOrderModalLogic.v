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

  Variant connectives : Set :=
  | CONTRADICTION : connectives
  | NEGATION : connectives
  | CONJUNCTION : connectives
  | DISJUNCTION : connectives
  | IMPLICATION : connectives
  | BICONDITIONAL : connectives 
  | FORALL : connectives
  | EXISTS : connectives
  | EQUAL : connectives
  | BOX : connectives
  | DIA : connectives
  .

  Definition connectives_eq_dec :
    forall c1 : connectives,
    forall c2 : connectives,
    {c1 = c2} + {c1 <> c2}.
  Proof.
    induction c1; destruct c2;
    (left; congruence) || (right; congruence); trivial.
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
    induction ty1 as [ | | ty1_1 IH1 ty1_2 IH2]; destruct ty2 as [ | | ty2_1 ty2_2];
    repeat (
      first
      [ (left; congruence) || (right; congruence); trivial
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

  Definition get_type_of_connectives (c : connectives) : ty_expr :=
    match c with
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
    { fun_arity_env : forall f_id : nat, option arity
    ; rel_arity_env : forall r_id : nat, option arity
    }
  .

  Unset Primitive Projections.

  Variable lsig : language_signature.

  Variant symbol : Set :=
  | CncSym (c : connectives) : symbol
  | FunSym (fsym_id : {f_id : nat | lsig.(fun_arity_env) f_id <> None}) : symbol
  | RelSym (rsym_id : {r_id : nat | lsig.(rel_arity_env) r_id <> None}) : symbol
  .

  Definition get_type_of_symbol (s : symbol) : ty_expr :=
    match s with
    | CncSym s => get_type_of_connectives s
    | FunSym fsym_id => nat_rec (fun _ => ty_expr) \ty[ i ] (fun _ ty1 => \ty[ i -> ty1 ]) (fromJust (lsig.(fun_arity_env) (proj1_sig fsym_id)) (proj2_sig fsym_id))
    | RelSym rsym_id => nat_rec (fun _ => ty_expr) \ty[ o ] (fun _ ty1 => \ty[ i -> ty1 ]) (fromJust (lsig.(rel_arity_env) (proj1_sig rsym_id)) (proj2_sig rsym_id))
    end
  .

  Inductive tm_expr : Set :=
  | VAR (x : ivar) : tm_expr
  | CON (s : symbol) : tm_expr
  | APP (t1 : tm_expr) (t2 : tm_expr) : tm_expr
  | LAM (y : ivar) (t1 : tm_expr) : tm_expr
  .

  Inductive typeOf : tm_expr -> ty_expr -> Set :=
  | TypeOfVAR (x : ivar) : typeOf (VAR x) \ty[ i ]
  | TypeOfCON (s : symbol) : typeOf (CON s) (get_type_of_symbol s)
  | TypeOfAPP (t1 : tm_expr) (t2 : tm_expr) (ty1 : ty_expr) (ty2 : ty_expr) (H1 : typeOf t1 \ty[ ty1 -> ty2 ]) (H2 : typeOf t2 \ty[ ty1 ]) : typeOf (APP t1 t2) \ty[ ty2 ]
  | TypeOfLAM (y : ivar) (t1 : tm_expr) (ty1 : ty_expr) (H1 : typeOf t1 \ty[ ty1 ]) : typeOf (LAM y t1) \ty[ i -> ty1 ]
  .

  End SYNTAX_OF_FIRST_ORDER_MODAL_LOGIC.

  Arguments CncSym {lsig}.
  Arguments FunSym {lsig}.
  Arguments RelSym {lsig}.

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
    | \ty[ ty1 -> ty2 ] => interprete0_ty \ty[ ty1 ] -> interprete0_ty \ty[ ty2 ]
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
    | \ty[ ty1 -> ty2 ] => interpreteW_ty \ty[ ty1 ] -> interpreteW_ty \ty[ ty2 ]
    end
  .

  Definition interpreteW_func (lsig : language_signature) (fsym_id : {f_id : nat | lsig.(fun_arity_env) f_id <> None}) :
    (Worlds -> interprete0_ty (get_type_of_symbol lsig (FunSym fsym_id))) ->
    interpreteW_ty (get_type_of_symbol lsig (FunSym fsym_id)).
  Proof.
    simpl; generalize (fromJust (lsig.(fun_arity_env) (proj1_sig fsym_id)) (proj2_sig fsym_id)) as n.
    induction n as [ | n IH]; [exact (fun val_w => val_w) | exact (fun kon_w arg_w => IH (fun w => kon_w w (arg_w w)))].
  Defined.

  Definition interpreteW_pred (lsig : language_signature) (rsym_id : {r_id : nat | lsig.(rel_arity_env) r_id <> None}) :
    (Worlds -> interprete0_ty (get_type_of_symbol lsig (RelSym rsym_id))) ->
    interpreteW_ty (get_type_of_symbol lsig (RelSym rsym_id)).
  Proof.
    simpl; generalize (fromJust (lsig.(rel_arity_env) (proj1_sig rsym_id)) (proj2_sig rsym_id)) as n.
    induction n as [ | n IH]; [exact (fun val_w => val_w) | exact (fun kon_w arg_w => IH (fun w => kon_w w (arg_w w)))].
  Defined.

  Variable accessibility_relation : ensemble (Worlds * Worlds).

  Local Notation " w1 '`is_accessible_to`' w2 " := (member (w1, w2) accessibility_relation) (at level 70, no associativity) : type_scope.

  Definition interpreteW_logical (c : connectives) : interpreteW_ty (get_type_of_connectives c) :=
    match c with
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

  Variable func_env : forall fsym_id : {f_id : nat | lsig.(fun_arity_env) f_id <> None}, Worlds -> interprete0_ty (get_type_of_symbol lsig (FunSym fsym_id)).

  Variable pred_env : forall rsym_id : {r_id : nat | lsig.(rel_arity_env) r_id <> None}, Worlds -> interprete0_ty (get_type_of_symbol lsig (RelSym rsym_id)).

  Definition interpreteW_symbol (s : symbol lsig) : interpreteW_ty (get_type_of_symbol lsig s) :=
    match s with
    | CncSym c => interpreteW_logical c
    | FunSym fsym_id => interpreteW_func lsig fsym_id (func_env fsym_id) 
    | RelSym rsym_id => interpreteW_pred lsig rsym_id (pred_env rsym_id)
    end
  .

  Fixpoint interpreteW_tm (ivar_env : ivar -> wUniv) (tm : tm_expr lsig) (ty : ty_expr) (H : typeOf tm ty) {struct H} : interpreteW_ty ty :=
    match H with
    | TypeOfVAR x => ivar_env x
    | TypeOfCON s => interpreteW_symbol s
    | TypeOfAPP t1 t2 ty1 ty2 H1 H2 => (interpreteW_tm ivar_env t1 \ty[ ty1 -> ty2 ] H1) (interpreteW_tm ivar_env t2 \ty[ ty1 ] H2)
    | TypeOfLAM y t1 ty1 H1 => (fun y_val => interpreteW_tm (fun z => if ivar_eq_dec y z then y_val else ivar_env z) t1 \ty[ ty1 ] H1)
    end
  .

  End SEMANTICS_OF_FIRST_ORDER_MODAL_LOGIC.

End FirstOrderModalLogic.
