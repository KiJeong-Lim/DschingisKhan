Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module FirstOrderModalLogicSyntax.

  Import ListNotations MyUtilities MyEnsemble.

  Record first_order_modal_language : Set :=
    FOML
    { func_arity : forall f_id : nat, nat
    ; pred_arity : forall p_id : nat, nat
    }
  .

  Definition ivar : Set :=
    nat
  .

  Variant ctor : Set :=
  | CONTRADICTION : ctor
  | NEGATION : ctor
  | CONJUNCTION : ctor
  | DISJUNCTION : ctor
  | IMPLICATION : ctor
  | BICONDITIONAL : ctor 
  | FORALL : ctor
  | EXISTS : ctor
  | EQUAL : ctor
  | DIA : ctor
  | BOX : ctor
  | FuncSym : forall f_id : nat, ctor
  | PredSym : forall p_id : nat, ctor
  .

  Inductive tm : Set :=
  | VAR : forall x : ivar, tm
  | CON : forall c : ctor, tm
  | APP : forall t1 : tm, forall t2 : tm, tm
  | LAM : forall y : ivar, forall t1 : tm, tm
  .

  Inductive ty : Set :=
  | TyI : ty
  | TyO : ty
  | ARR : forall arg_ty : ty, forall ret_ty : ty, ty
  .

  Definition ty_eq_dec :
    forall ty1 : ty,
    forall ty2 : ty,
    {ty1 = ty2} + {ty1 <> ty2}.
  Proof.
    induction ty1; destruct ty2.
    - left; congruence.
    - right; congruence.
    - right; congruence.
    - right; congruence.
    - left; congruence.
    - right; congruence.
    - right; congruence.
    - right; congruence.
    - destruct (IHty1_1 ty2_1); destruct (IHty1_2 ty2_2).
      + left; congruence.
      + right; congruence.
      + right; congruence.
      + right; congruence.
  Defined.

  Global Declare Custom Entry object_level_ty.

  Global Notation " 'i' " := (TyI) (in custom object_level_ty at level 0, no associativity).

  Global Notation " 'o' " := (TyO) (in custom object_level_ty at level 0, no associativity).

  Global Notation " ty1 '->' ty2 " := (ARR ty1 ty2) (in custom object_level_ty at level 1, right associativity).

  Global Notation " ty1 " := (ty1) (in custom object_level_ty, ty1 ident).

  Global Notation " '(' ty1 ')' " := (ty1) (in custom object_level_ty at level 0, no associativity).

  Definition view_ty (ty_expr : ty) : ty :=
    ty_expr
  .

  Global Notation " 'Ty<' ty_expr '>' " := (view_ty ty_expr) (ty_expr custom object_level_ty at level 1, no associativity).

  Section WELL_FORMED.

  Variable lang : first_order_modal_language.

  Definition get_ty_of_ctor : ctor -> ty :=
    fun c : ctor =>
    match c with
    | CONTRADICTION => Ty< o >
    | NEGATION => Ty< o -> o >
    | CONJUNCTION => Ty< o -> o -> o >
    | DISJUNCTION => Ty< o -> o -> o >
    | IMPLICATION => Ty< o -> o -> o >
    | BICONDITIONAL => Ty< o -> o -> o >
    | FORALL => Ty< (i -> o) -> o >
    | EXISTS => Ty< (i -> o) -> o >
    | EQUAL => Ty< i -> i -> o >
    | DIA => Ty< o -> o >
    | BOX => Ty< o -> o >
    | FuncSym f_id => nat_rec _ (Ty< i >) (fun _ : nat => fun ty1 : ty => Ty< i -> ty1 >) (lang.(func_arity) f_id)
    | PredSym p_id => nat_rec _ (Ty< o >) (fun _ : nat => fun ty1 : ty => Ty< i -> ty1 >) (lang.(pred_arity) p_id) 
    end
  .

  Definition bindMaybe {A : Type} {B : Type} : option A -> (A -> option B) -> option B :=
    fun option_A : option A =>
    fun A_to_option_B : A -> option B =>
    match option_A with
    | None => None
    | Some a => A_to_option_B a
    end
  .

  Definition pureMaybe {A : Type} : A -> option A :=
    Some
  .

  Definition lookup (x : ivar) : list (ivar * ty) -> option ty :=
    fix lookup_fix (ty_ctx : list (ivar * ty)) : option ty :=
    match ty_ctx with
    | [] => None
    | ty_ctx_item :: ty_ctx' =>
      if Nat.eq_dec (fst ty_ctx_item) x
      then Some (snd ty_ctx_item)
      else lookup_fix ty_ctx'
    end
  .

  Definition modus_ponens : ty -> ty -> option ty :=
    fun ty1 : ty =>
    fun ty2 : ty =>
    match ty1 with
    | TyI => None
    | TyO => None
    | ARR arg_ty ret_ty =>
      if ty_eq_dec arg_ty ty2
      then Some ret_ty
      else None
    end
  .

  Fixpoint typing (ty_ctx : list (ivar * ty)) (t : tm) {struct t} : option ty :=
    match t with
    | VAR x => lookup x ty_ctx
    | CON c => pureMaybe (get_ty_of_ctor c)
    | APP t1 t2 => bindMaybe (typing ty_ctx t1) (fun ty1 : ty => bindMaybe (typing ty_ctx t2) (fun ty2 : ty => modus_ponens ty1 ty2))
    | LAM y t1 => typing ((y, Ty< i >) :: ty_ctx) t1
    end
  .

  End WELL_FORMED.

  Global Notation " ty_ctx '\vdash_{' lang  '}' tm_expr '\isof' ty_expr " := (typing lang ty_ctx tm_expr = Some ty_expr) (at level 70, no associativity) : type_scope.

End FirstOrderModalLogicSyntax.

Module FirstOrderModalLogicSemantics.

  Import MyEnsemble FirstOrderModalLogicSyntax.

  Section EVALUATION.

  Variable worlds : Type.

  Let wProp : Type :=
    worlds -> Prop
  .

  Let wIndividuals : Type :=
    worlds -> Type
  .

  Definition interprete_ty : ty -> Type :=
    fix interprete_ty_fix (ty_expr : ty) {struct ty_expr} : Type :=
    match ty_expr with
    | TyI => wIndividuals
    | TyO => wProp
    | ARR arg_ty ret_ty => interprete_ty_fix arg_ty -> interprete_ty_fix ret_ty
    end
  .

  Variable is_accessible_to : worlds -> worlds -> Prop.

  Variable lang : first_order_modal_language.

  Variable func_env : forall f_id : nat, interprete_ty (nat_rec _ (Ty< i >) (fun _ : nat => fun ty1 : ty => Ty< i -> ty1 >) (lang.(func_arity) f_id)).

  Variable pred_env : forall p_id : nat, interprete_ty (nat_rec _ (Ty< o >) (fun _ : nat => fun ty1 : ty => Ty< i -> ty1 >) (lang.(pred_arity) p_id)).

  Definition interprete_ctor (c : ctor) : interprete_ty (get_ty_of_ctor lang c) :=
    match c with
    | CONTRADICTION =>
      fun w : worlds =>
      False
    | NEGATION =>
      fun wP1 : wProp =>
      fun w : worlds =>
      ~ wP1 w
    | CONJUNCTION =>
      fun wP1 : wProp =>
      fun wP2 : wProp =>
      fun w : worlds =>
      wP1 w /\ wP2 w
    | DISJUNCTION =>
      fun wP1 : wProp =>
      fun wP2 : wProp =>
      fun w : worlds =>
      wP1 w \/ wP2 w
    | IMPLICATION =>
      fun wP1 : wProp =>
      fun wP2 : wProp =>
      fun w : worlds =>
      wP1 w -> wP2 w
    | BICONDITIONAL =>
      fun wP1 : wProp =>
      fun wP2 : wProp =>
      fun w : worlds =>
      wP1 w <-> wP2 w
    | FORALL =>
      fun wP1' : wIndividuals -> wProp =>
      fun w : worlds =>
      forall x : wIndividuals, wP1' (fun _ : worlds => x w) w
    | EXISTS =>
      fun wP1' : wIndividuals -> wProp =>
      fun w : worlds =>
      exists x : wIndividuals, wP1' (fun _ : worlds => x w) w
    | EQUAL =>
      fun x : wIndividuals =>
      fun y : wIndividuals =>
      fun w : worlds =>
      x w = y w
    | DIA =>
      fun wP1 : wProp =>
      fun w : worlds =>
      forall w' : worlds, is_accessible_to w w' -> wP1 w'
    | BOX =>
      fun wP1 : wProp =>
      fun w : worlds =>
      exists w' : worlds, is_accessible_to w w' /\ wP1 w'
    | FuncSym f_id => func_env f_id
    | PredSym p_id => pred_env p_id
    end
  .

  End EVALUATION.

End FirstOrderModalLogicSemantics.

