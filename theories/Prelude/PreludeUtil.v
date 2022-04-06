Require Export Coq.Arith.PeanoNat.
Require Import DschingisKhan.Prelude.PreludeInit.

Module EQ_FACTS.

End EQ_FACTS.

Module NAT_ARITH.

End NAT_ARITH.

Module FUN_FACTS.

  (** "1. Acc" *)

  Class isWellFounded (A : Type) : Type :=
    { wf_rel : A -> A -> Prop
    ; WELL_FOUNDED : forall a : A, Acc wf_rel a
    }
  .

  Lemma NoetherianRecursionAux {A : Type} (LT : A -> A -> Prop) (phi : A -> Type)
    (H_GOAL : forall x : A, <{ IH : forall y : A, LT y x -> phi y }> -> phi x)
    : forall a : A, Acc LT a -> phi a.
  Proof.
    exact (
      fix Noetherian_fix (x : A) (H_Acc_x : Acc LT x) {struct H_Acc_x} : phi x :=
      match H_Acc_x as _ in Acc _ _ return phi x with
      | Acc_intro _ H_LT_implies_Acc => H_GOAL x (fun y : A => fun H_LT : LT y x => Noetherian_fix y (H_LT_implies_Acc y H_LT))
      end
    ).
  Defined.

  Theorem NoetherianRecursion {A : Type} {requiresWellFounded : isWellFounded A} {phi : A -> Type}
    (H_GOAL : forall x : A, <{ IH : forall y : A, wf_rel y x -> phi y }> -> phi x)
    : forall a : A, phi a.
  Proof.
    exact (fun a : A => NoetherianRecursionAux wf_rel phi H_GOAL a (WELL_FOUNDED a)).
  Defined.

  (** "2. LawOfExclusiveMiddle" *)

End FUN_FACTS.
