Require Import DschingisKhan.Prelude.PreludeInit.

Module FUN_FACTS.

  Lemma NoetherianRecursionAux {A : Type} {phi : A -> Type} (LT : A -> A -> Prop)
    (H_GOAL : forall x : A, <{ IH : forall y : A, LT y x -> phi y }> -> phi x)
    : forall a : A, Acc LT a -> phi a.
  Proof.
    exact (
      fix NoetherianRecursionAux_fix (x : A) (H_Acc : Acc LT x) {struct H_Acc} : phi x :=
      match H_Acc as _ in Acc _ _ return phi x with
      | Acc_intro _ H_acc => H_GOAL x (fun y : A => fun H_LT : LT y x => NoetherianRecursionAux_fix y (H_acc y H_LT))
      end
    ).
  Defined.

  Theorem NoetherianRecursion {A : Type} {phi : A -> Type} (LT : A -> A -> Prop)
    (H_WELL_FOUNDED : forall a : A, Acc LT a)
    (H_GOAL : forall x : A, <{ IH : forall y : A, LT y x -> phi y }> -> phi x)
    : forall a : A, phi a.
  Proof.
    exact (fun a : A => NoetherianRecursionAux LT H_GOAL a (H_WELL_FOUNDED a)).
  Defined.

End FUN_FACTS.
