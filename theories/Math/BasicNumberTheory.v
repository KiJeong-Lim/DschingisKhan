Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeUtil.

Module BasicNumberTheoryOfNat.

  Theorem sqrt2irrat (p : nat) (q : nat)
    : (p = 0 /\ q = 0) <-> (p * p = 2 * q * q).
  Proof. (* Thanks to Junyoung Jang *)
    split; [lia | revert p q].
    assert (lemma1 : forall n : nat, n mod 2 = 1 <-> (exists k : nat, n = 2 * k + 1)).
    { intros n. split.
      - pose proof (Nat.div_mod n 2) as H1. intros H2.
        rewrite H2 in H1. eexists. eapply H1. lia.
      - intros [k H1]. eapply div_mod_uniqueness.
        + eassumption.
        + lia.
    }
    assert (lemma2 : forall n : nat, n mod 2 = 0 <-> (exists k : nat, n = 2 * k)).
    { intros n. split.
      - pose proof (Nat.div_mod n 2) as H1. intros H2.
        rewrite H2, Nat.add_0_r in H1. eexists. eapply H1. lia.
      - intros [k H1]. eapply div_mod_uniqueness.
        + rewrite Nat.add_0_r. eassumption.
        + lia.
    }
    assert (lemma3 : forall n : nat, n mod 2 = 0 \/ n mod 2 = 1).
    { intros n. pose proof (Nat.mod_bound_pos n 2) as H1. lia. }
    assert (lemma4 : 0 <> 1) by lia.
    assert (claim1 : forall p : nat, forall q : nat, p * p = 2 * q * q -> p mod 2 = 0).
    { intros p q pp_eq_2qq.
      enough (to_show : p mod 2 <> 1) by now pose proof (lemma3 p) as H2; lia.
      intros H_contradiction. pose proof (proj1 (lemma1 p) H_contradiction) as [k H2].
      assert (pp_mod_2_eq_1 : (p * p) mod 2 = 1) by lia.
      rewrite pp_eq_2qq in pp_mod_2_eq_1.
      eapply lemma4. rewrite <- pp_mod_2_eq_1. symmetry.
      eapply lemma2. eexists. rewrite Nat.mul_assoc. reflexivity.
    }
    { intros p q pp_eq_2qq. enough (p_eq_0 : p = 0) by lia.
      revert p q pp_eq_2qq. induction p as [p IH] using @lt_strong_ind. unnw. ii.
      pose proof (proj1 (lemma2 p) (claim1 p q pp_eq_2qq)) as [p' p_eq_2p'].
      pose proof (n_le_m_or_m_lt_n_holds_for_any_n_and_any_m p 0) as [p_le_0 | p_gt_0]; try lia.
      assert (p_gt_p' : p' < p) by lia. assert (H1 : q * q = 2 * p' * p') by lia.
      pose proof (proj1 (lemma2 q) (claim1 q p' H1)) as [q' p_eq_2q'].
      assert (H2 : p' * p' = 2 * q' * q') by lia. assert (therefore : p' = 0) by exact (IH p' p_gt_p' q' H2). lia.
    }
  Qed.

End BasicNumberTheoryOfNat.
