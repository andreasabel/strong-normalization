(** * Different Characterisations Strong Normalisation *)
Require Import stlc reduction sn_defs sn_inductive_soundness_1a.

Lemma SN_sn :
  (forall n (M: tm n), SN M -> sn M)
/\ (forall n (M: tm n), SNe M -> sn M /\ neutral M)
/\ (forall n (M: tm n) M', SNRed M M' -> redsn M M') .
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
