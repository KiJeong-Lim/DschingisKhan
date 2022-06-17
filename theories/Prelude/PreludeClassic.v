Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeUtil.

Module ExclusiveMiddle.

  Axiom classic : forall P : Prop, P \/ ~ P.

  Lemma NNPP (P : Prop)
    (NNP : ~ ~ P)
    : P.
  Proof. pose proof (classic P) as [? | ?]; [trivial | contradiction NNP]. Qed.

  Lemma proof_irrelevance (P : Prop)
    : pirrel_STMT P.
  Proof. eapply exclusive_middle_implies_proof_irrelevance; exact classic. Qed.

  Lemma projT2_eq (A : Type) (B : A -> Type) (x : A)
    : projT2_eq_STMT A B x.
  Proof. eapply eq_rect_eq_iff_projT2_eq, pirrel_iff_eq_rect_eq, proof_irrelevance. Qed.

End ExclusiveMiddle.
