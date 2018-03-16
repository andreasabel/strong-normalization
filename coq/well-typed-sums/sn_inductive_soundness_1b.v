(** * Different Characterisations Strong Normalisation *)
Require Import base contexts stlc reduction sn_inductive_soundness_1a sn_defs.

Lemma SN_sn :
  (forall g A (M: tm g A), SN M -> sn M)
/\ (forall g A (M: tm g A), SNe M -> sn M /\ neutral M)
/\ (forall g A (M: tm g A) M', SNRed M M' -> redsn M M') .
Proof.
  apply SN_multind; intros.
  - intuition.
  - now apply closed_lam.
  - now apply closed_inl.
  - now apply closed_inr.
  - eauto using redsn_backwards.
  - split; [|now constructor].
    + constructor. intros M H. inv H.
  - split; [|intuition].
    + apply sn_case_neutral; intuition.
  - split; [|intuition].
    + now apply sn_app_neutral.
  - subst. now constructor.
  - now constructor.
  - now constructor.
  - subst. now constructor.
  - subst. now constructor.
Qed.
