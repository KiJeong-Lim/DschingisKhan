Require Import DschingisKhan.pure.DomainTheory.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

(* [Simulation]

  Definition Similarity : Type :=
    ensemble (Src * Tgt) -> ensemble (Src * Tgt)
  .

  Definition follows : ensemble (Src * Tgt) -> ensemble (Src * Tgt) -> Prop :=
    fun R1 : ensemble (Src * Tgt) =>
    fun R2 : ensemble (Src * Tgt) =>
    forall x1 : Src,
    forall y1 : Tgt,
    (x1, y1) \in R1 ->
    forall x2 : Src,
    forall e : Eff,
    x1 ~~[ e ]~>1 x2 ->
    exists y2 : Tgt, (x2, y2) \in R2 /\ y1 ~~[ e ]~>* y2
  .

  CoInductive IsSimulation (sim : Similarity) : ensemble (Src * Tgt) -> Prop :=
  | followsForever :
    forall R : ensemble (Src * Tgt),
    follows (sim R) R ->
    IsSimulation sim (sim R) ->
    IsSimulation sim R
  .

*)
