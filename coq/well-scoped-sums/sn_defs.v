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
| SInl n (M: tm n) : SN M -> SN (inl M)
| SInr n (M: tm n) : SN M -> SN (inr M)
| SRed n (M M': tm n): SNRed M M' -> SN M' -> SN M
with SNe : forall {n}, tm n -> Prop :=
| SVar n (x: fin n) : SNe (ids x)
| SNeuOr n (M: tm n) (N1: tm (S n)) N2:
   SNe M -> SN N1 -> SN N2 -> SNe (orelim M N1 N2)
| SApp n (R: tm n) M : SNe R -> SN M -> SNe (app R M)
with SNRed : forall {n}, tm n -> tm n -> Prop :=
| SBeta n A (M : tm (S n)) N M': SN N -> M' = M[N..] -> SNRed (app (lam A M) N) M'
| SAppl n (R R': tm n) M : SNRed R R' -> SNRed (app R M) (app R' M)
| SOr n  (M M' : tm n) (N1 : tm (S n)) N2: SNRed M M' -> SNRed (orelim M N1 N2) (orelim M' N1 N2)
| SCaseL n (s: tm n) t t' (u: tm (S n)) : SN s -> SN t -> SN u -> t' = (t[s..]) -> SNRed (orelim (inl s) t u) t'
| SCaseR n (s: tm n) (t: tm (S n)) u u': SN s -> SN t -> SN u -> u' = (u[s..]) ->  SNRed (orelim (inr s) t u) u'
.

Scheme SN_ind_2 := Minimality for SN Sort Prop
                   with SNe_ind_2  := Minimality for SNe Sort Prop
                    with redSN_ind_2 := Minimality for SNRed Sort Prop.
Combined Scheme SN_multind from SN_ind_2, SNe_ind_2, redSN_ind_2.
