Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.

Module SCRATCH.

  Import ListNotations.

  Definition dep_S {A : Type} {B : forall x : A, Type} {C : forall x : A, forall y : B x, Type} (f : forall x : A, forall y : B x, C x y) (g : forall x : A, B x) (x : A) : C x (g x) := f x (g x).

  Definition dep_K {A : Type} {B : forall x : A, Type} (x : A) (y : B x) : A := x.

  Definition kconcat {M : Hask.cat -----> Hask.cat} {requiresMonad : isMonad M} {X : Type} : list (kleisli M X X) -> kleisli M X X :=
    fix kconcat_fix (ks : list (kleisli M X X)) {struct ks} : kleisli M X X :=
    match ks with
    | [] => kempty
    | k :: ks => k <=< kconcat_fix ks
    end
  .

  Section SYNCHRONOUS_CIRCUIT.

  Set Primitive Projections.

  CoInductive circuit (Input : Type) (Output : Type) : Type :=
    Circuit_go { Circuit_observe : Input -> (circuit Input Output) * Output }
  .

  Global Arguments Circuit_go {Input} {Output}.
  Global Arguments Circuit_observe {Input} {Output}.

  Definition delayWithInit {I : Type} : I -> circuit I I :=
    cofix delayWithInit_cofix (x : I) : circuit I I :=
    Circuit_go (fun x' : I => (delayWithInit_cofix x', x))
  .

  Definition embedFunIntoCircuit {I : Type} {O : Type} (arr : I -> O) : circuit I O :=
    cofix embedFunIntoCircuit_cofix : circuit I O :=
    Circuit_go (fun x : I => (embedFunIntoCircuit_cofix, arr x))
  .

  Definition combineCircuit {I1 : Type} {I2 : Type} {O1 : Type} {O2 : Type}
    : circuit I1 O1 -> circuit I2 O2 -> circuit (I1 * I2) (O1 * O2).
  Proof.
    cofix combineCircuit_cofix.
    intros circuit1 circuit2. econstructor.
    intros [x y].
    destruct (Circuit_observe circuit1 x) as [x_1 x_2].
    destruct (Circuit_observe circuit2 y) as [y_1 y_2].
    exact (combineCircuit_cofix x_1 y_1, (x_2, y_2)).
  Defined.

  End SYNCHRONOUS_CIRCUIT.

End SCRATCH.
