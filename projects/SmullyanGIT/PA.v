Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import DschingisKhan.classical.ExclusiveMiddle.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module Tarski's_Theorem_for_Arithmetic.

  Import ListNotations MyUtilities.

  Section BasicSyntaxDefn.

  Definition Vr : Set :=
    nat
  .

  Definition Vr_eq_dec : forall x : Vr, forall y : Vr, {x = y} + {x <> y} :=
    Nat.eq_dec
  .

  Inductive Tm : Set :=
  | ivarTm : forall x : Vr, Tm
  | zeroTm : Tm
  | succTm : forall t1 : Tm, Tm
  | plusTm : forall t1 : Tm, forall tm2 : Tm, Tm
  | multTm : forall t1 : Tm, forall tm2 : Tm, Tm
  | expoTm : forall t1 : Tm, forall tm2 : Tm, Tm
  .

  Lemma Tm_eq_dec :
    forall t1 : Tm,
    forall t2 : Tm,
    {t1 = t2} + {t1 <> t2}.
  Proof with try ((right; congruence) || (left; congruence)).
    induction t1; destruct t2...
    - destruct (Vr_eq_dec x x0)...
    - destruct (IHt1 t2)...
    - destruct (IHt1_1 t2_1); destruct (IHt1_2 t2_2)...
    - destruct (IHt1_1 t2_1); destruct (IHt1_2 t2_2)...
    - destruct (IHt1_1 t2_1); destruct (IHt1_2 t2_2)...
  Qed.

  Inductive Form : Set :=
  | eqnF : forall t1 : Tm, forall t2 : Tm, Form
  | leqF : forall t1 : Tm, forall t2 : Tm, Form
  | negF : forall f1 : Form, Form
  | impF : forall f1 : Form, forall f2 : Form, Form
  | allF : forall y : Vr, forall f1 : Form, Form
  .

  Lemma Form_eq_dec :
    forall f1 : Form,
    forall f2 : Form,
    {f1 = f2} + {f1 <> f2}.
  Proof with try ((right; congruence) || (left; congruence)).
    induction f1; destruct f2...
    - destruct (Tm_eq_dec t1 t0); destruct (Tm_eq_dec t2 t3)...
    - destruct (Tm_eq_dec t1 t0); destruct (Tm_eq_dec t2 t3)...
    - destruct (IHf1 f2)...
    - destruct (IHf1_1 f2_1); destruct (IHf1_2 f2_2)...
    - destruct (Vr_eq_dec y y0); destruct (IHf1 f2)...
  Qed.

  End BasicSyntaxDefn.

  Section BasicSemanticsDefn.

  Let VrValue : Set :=
    nat
  .

  Let MyType : Type :=
    Type
  .

  Definition Env : MyType :=
    Vr -> VrValue
  .

  Definition TmValue : MyType :=
    VrValue
  .

  Fixpoint evalTm (mathbfE : Env) (t : Tm) {struct t} : TmValue :=
    match t with
    | ivarTm x => mathbfE x
    | zeroTm => O
    | succTm t1 => S (evalTm mathbfE t1)
    | plusTm t1 t2 => plus (evalTm mathbfE t1) (evalTm mathbfE t2)
    | multTm t1 t2 => mult (evalTm mathbfE t1) (evalTm mathbfE t2)
    | expoTm t1 t2 => Nat.pow (evalTm mathbfE t1) (evalTm mathbfE t2)
    end
  .

  Definition FormValue : MyType :=
    Prop
  .

  Fixpoint evalForm (mathbfE : Env) (f : Form) {struct f} : FormValue :=
    match f with
    | eqnF t1 t2 => eq (evalTm mathbfE t1) (evalTm mathbfE t2)
    | leqF t1 t2 => le (evalTm mathbfE t1) (evalTm mathbfE t2)
    | negF f1 => ~ evalForm mathbfE f1
    | impF f1 f2 => evalForm mathbfE f1 -> evalForm mathbfE f2
    | allF y f1 => forall v : VrValue, evalForm (fun z : Vr => if Vr_eq_dec y z then v else mathbfE z) f1
    end
  .

  End BasicSemanticsDefn.

  Section OccurencesDefn.

  Fixpoint occursFreeInTm (z : Vr) (t : Tm) {struct t} : bool :=
    match t with
    | ivarTm x => if Vr_eq_dec x z then true else false
    | zeroTm => false
    | succTm t1 => occursFreeInTm z t1
    | plusTm t1 t2 => occursFreeInTm z t1 || occursFreeInTm z t2
    | multTm t1 t2 => occursFreeInTm z t1 || occursFreeInTm z t2
    | expoTm t1 t2 => occursFreeInTm z t1 || occursFreeInTm z t2
    end
  .

  Fixpoint occursFreeInForm (z : Vr) (f : Form) {struct f} : bool :=
    match f with
    | eqnF t1 t2 => occursFreeInTm z t1 || occursFreeInTm z t2
    | leqF t1 t2 => occursFreeInTm z t1 || occursFreeInTm z t2
    | negF f1 => occursFreeInForm z f1
    | impF f1 f2 => occursFreeInForm z f1 || occursFreeInForm z f2
    | allF y f1 => if Vr_eq_dec y z then false else occursFreeInForm z f1
    end
  .

  Fixpoint getFreeVarsTm (t : Tm) {struct t} : list Vr :=
    match t with
    | ivarTm x => [x]
    | zeroTm => []
    | succTm t1 => getFreeVarsTm t1
    | plusTm t1 t2 => getFreeVarsTm t1 ++ getFreeVarsTm t2
    | multTm t1 t2 => getFreeVarsTm t1 ++ getFreeVarsTm t2
    | expoTm t1 t2 => getFreeVarsTm t1 ++ getFreeVarsTm t2
    end
  .

  Fixpoint getFreeVarsForm (f : Form) {struct f} : list Vr :=
    match f with
    | eqnF t1 t2 => getFreeVarsTm t1 ++ getFreeVarsTm t2
    | leqF t1 t2 => getFreeVarsTm t1 ++ getFreeVarsTm t2
    | negF f1 => getFreeVarsForm f1
    | impF f1 f2 => getFreeVarsForm f1 ++ getFreeVarsForm f2
    | allF y f1 => remove Vr_eq_dec y (getFreeVarsForm f1)
    end
  .

  End OccurencesDefn.

  Section SubstitutionDefn.

  Definition substitution : Set :=
    Vr -> Tm
  .

  Definition nilSubst : substitution :=
    ivarTm
  .

  Definition consSubst (y : Vr) (t : Tm) (sigma : substitution) : substitution :=
    fun z : Vr =>
    if Vr_eq_dec y z
    then t
    else sigma z
  .

  Definition applySubst_Vr (sigma : substitution) (x : Vr) : Tm :=
    sigma x
  .

  Definition getMaxNumOfFreeVarsInTm (t : Tm) : Vr :=
    fold_right_max_0 (getFreeVarsTm t)
  .

  Definition isFreshVarIn_applySubst_Tm (sigma : substitution) (z : Vr) (t : Tm) : Prop :=
    forallb (fun x : Vr => negb (occursFreeInTm z (applySubst_Vr sigma x))) (getFreeVarsTm t) = true
  .

  Definition isFreshVarIn_applySubst_Form (sigma : substitution) (z : Vr) (f : Form) : Prop :=
    forallb (fun x : Vr => negb (occursFreeInTm z (applySubst_Vr sigma x))) (getFreeVarsForm f) = true
  .

  Definition chi (sigma : substitution) (f : Form) : Vr :=
    S (fold_right_max_0 (map (fun x : Vr => getMaxNumOfFreeVarsInTm (applySubst_Vr sigma x)) (getFreeVarsForm f)))
  .

  Fixpoint applySubst_Tm (sigma : substitution) (t : Tm) {struct t} : Tm :=
    match t with
    | ivarTm x => applySubst_Vr sigma x
    | zeroTm => zeroTm
    | succTm t1 => succTm (applySubst_Tm sigma t1)
    | plusTm t1 t2 => plusTm (applySubst_Tm sigma t1) (applySubst_Tm sigma t2)
    | multTm t1 t2 => multTm (applySubst_Tm sigma t1) (applySubst_Tm sigma t2)
    | expoTm t1 t2 => expoTm (applySubst_Tm sigma t1) (applySubst_Tm sigma t2)
    end
  .

  Fixpoint applySubst_Form (sigma : substitution) (f : Form) {struct f} : Form :=
    match f with
    | eqnF t1 t2 => eqnF (applySubst_Tm sigma t1) (applySubst_Tm sigma t2)
    | leqF t1 t2 => leqF (applySubst_Tm sigma t1) (applySubst_Tm sigma t2)
    | negF f1 => negF (applySubst_Form sigma f1)
    | impF f1 f2 => impF (applySubst_Form sigma f1) (applySubst_Form sigma f2)
    | allF y f1 =>
      let z : Vr := chi sigma f in
      allF z (applySubst_Form (consSubst y (ivarTm z) sigma) f1)
    end
  .

  End SubstitutionDefn.

  Section BasicMetaTheories.

  Lemma in_getFreeVarsForm_iff :
    forall f : Form,
    forall x : Vr,
    In x (getFreeVarsForm f) <-> occursFreeInForm x f = true.
  Proof with eauto.
  Admitted.

  Lemma getMaxNumOfFreeVarsInTm_lt_implies :
    forall t : Tm,
    forall x : Vr,
    getMaxNumOfFreeVarsInTm t < x ->
    occursFreeInTm x t = false.
  Proof with eauto.
  Admitted.

  Lemma evalTm_equiv_if_FVs_equiv :
    forall t : Tm,
    forall E1 : Env,
    forall E2 : Env,
    (forall x : Vr, occursFreeInTm x t = true -> E1 x = E2 x) ->
    evalTm E1 t = evalTm E2 t.
  Proof with eauto.
  Admitted.

  Lemma evalForm_equiv_if_FVs_equiv :
    forall f : Form,
    forall E1 : Env,
    forall E2 : Env,
    (forall x : Vr, occursFreeInForm x f = true -> E1 x = E2 x) ->
    evalForm E1 f <-> evalForm E2 f.
  Proof with eauto.
  Admitted.

  Lemma applySubst_Tm_preserves_evalTm :
    forall t : Tm,
    forall sigma : substitution,
    forall E : Env,
    evalTm (fun z : Vr => evalTm E (applySubst_Vr sigma z)) t = evalTm E (applySubst_Tm sigma t).
  Proof with eauto.
  Admitted.

  Lemma the_main_reason_for_introducing_chi :
    forall f : Form,
    forall sigma : substitution,
    isFreshVarIn_applySubst_Form sigma (chi sigma f) f.
  Proof with eauto.
  Admitted.

  Lemma applySubst_Form_preserves_evalForm :
    forall f : Form,
    forall sigma : substitution,
    forall E : Env,
    evalForm (fun z : Vr => evalTm E (applySubst_Vr sigma z)) f <-> evalForm E (applySubst_Form sigma f).
  Proof with eauto.
  Admitted.

  End BasicMetaTheories.

End Tarski's_Theorem_for_Arithmetic.

Module The_Incompleteness_of_Peano_Arithmetic_With_Exponentation.

End The_Incompleteness_of_Peano_Arithmetic_With_Exponentation.

Module Arithmetic_Without_the_Exponential.

End Arithmetic_Without_the_Exponential.
