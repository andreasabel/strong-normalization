Require Import base contexts stlc reduction.

(** ** Strong normalization *)
Inductive sn {G A} (s : tm G A) : Prop :=
| snI : (forall t, step s t -> sn t) -> sn s.

Lemma sn_mstep {G A} (s t : tm G A):
  mstep s t -> sn s -> sn t.
Proof.
  induction 1; eauto. intros []%IHmstep. now apply H1.
Qed.

Inductive SN : forall g A, tm g A -> Prop :=
| SNeu g A (M: tm g A): SNe M -> SN M
| SAbs g A B (M: tm (A ::g) B) : SN M -> SN (lam M)
| SRed g A (M M': tm g A): SNRed M M' -> SN M' -> SN M
with SNe : forall g A, tm g A -> Prop :=
| SVar g A (x: at_ty g A) : SNe (var x)
| SApp g A B (R: tm g (Fun A B)) M : SNe R -> SN M -> SNe (app R M)
with SNRed : forall g A, tm g A -> tm g A -> Prop :=
| SBeta g A B (M : tm (A :: g) B) N M': SN N -> M' = inst (N .: ids) M -> SNRed (app (lam M) N) M'
| SAppl g A B (R R': tm g (Fun A B)) M : SNRed R R' -> SNRed (app R M) (app R' M).

Scheme SN_ind_2 := Minimality for SN Sort Prop
                   with SNe_ind_2  := Minimality for SNe Sort Prop
                    with redSN_ind_2 := Minimality for SNRed Sort Prop.
Combined Scheme SN_multind from SN_ind_2, SNe_ind_2, redSN_ind_2.
