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
| SInl g A B (M: tm g A) : SN M -> SN (inl (B := B) M)
| SInr g A B (M: tm g B) : SN M -> SN (inr (A := A) M)
| SRed g A (M M': tm g A): SNRed M M' -> SN M' -> SN M
with SNe : forall g A, tm g A -> Prop :=
| SVar g A (x: at_ty g A) : SNe (var x)
| SNeuOr g A B C (M: tm g (Plus A B)) (N1: tm (A::g) C) N2:
   SNe M -> SN N1 -> SN N2 -> SNe (orelim M N1 N2)
| SApp g A B (R: tm g (Fun A B)) M : SNe R -> SN M -> SNe (app R M)
with SNRed : forall g A, tm g A -> tm g A -> Prop :=
| SBeta g A B (M : tm (A :: g) B) N M': SN N -> M' = inst (N .: ids) M -> SNRed (app (lam M) N) M'
| SAppl g A B (R R': tm g (Fun A B)) M : SNRed R R' -> SNRed (app R M) (app R' M)
| SOr g A B C (M M' : tm g (Plus A B)) (N1 : tm (A ::g) C) N2: SNRed M M' -> SNRed (orelim M N1 N2) (orelim M' N1 N2)
| SCaseL G A B C (s: tm G A) t t' (u: tm (B :: G) C) : SN s -> SN t -> SN u -> t' = (inst (s.:ids) t) -> SNRed (orelim (inl s) t u) t'
| SCaseR G A B C (s: tm G B) (t: tm (A :: G) C) u u': SN s -> SN t -> SN u -> u' = (inst (s.:ids) u) ->  SNRed (orelim (inr s) t u) u'
.

Scheme SN_ind_2 := Minimality for SN Sort Prop
                   with SNe_ind_2  := Minimality for SNe Sort Prop
                    with redSN_ind_2 := Minimality for SNRed Sort Prop.
Combined Scheme SN_multind from SN_ind_2, SNe_ind_2, redSN_ind_2.
