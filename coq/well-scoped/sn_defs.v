Require Import stlc reduction.

(** ** Strong normalization *)
Inductive sn {n} (s : tm n) : Prop :=
| snI : (forall t, step s t -> sn t) -> sn s.

Lemma sn_mstep {n} (s t : tm n):
  mstep s t -> sn s -> sn t.
Proof.
  induction 1; eauto. intros []%IHmstep. now apply H1.
Qed.

Inductive SN : forall {n}, tm n -> Prop :=
| SNeu n (M: tm n): SNe M -> SN M
| SAbs n A (M: tm (S n)) : SN M -> SN (lam A M)
| SRed n (M M': tm n): SNRed M M' -> SN M' -> SN M
with SNe : forall {n}, tm n -> Prop :=
| SVar n (x: fin n) : SNe (ids x)
| SApp n (R: tm n) M : SNe R -> SN M -> SNe (app R M)
with SNRed : forall {n}, tm n -> tm n -> Prop :=
| SBeta n A (M : tm (S n)) N M': SN N -> M' = M[N..] -> SNRed (app (lam A M) N) M'
| SAppl n (R R': tm n) M : SNRed R R' -> SNRed (app R M) (app R' M).

Scheme SN_ind_2 := Minimality for SN Sort Prop
                   with SNe_ind_2  := Minimality for SNe Sort Prop
                    with redSN_ind_2 := Minimality for SNRed Sort Prop.
Combined Scheme SN_multind from SN_ind_2, SNe_ind_2, redSN_ind_2.
