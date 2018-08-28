module StrongNorm

open FStar.List.Tot
open FStar.Math.Lemmas
open FStar.Constructive
open Prelude
open Base
open PropSN
open Sound
open PropSN2

val normR: g:ctx -> t:ty -> e:texp g t -> Tot Type0
  (decreases t)
let rec normR g t e = match t with
  | TBase -> sSN g TBase e
  | TArr ta tb -> (g':ctx -> 
		r:sub g' g {renaming r} ->
		e0:texp g' ta ->
		norm0:normR g' ta e0 ->
		Tot (normR g' tb (TyApp (subst r e) e0))
		)

// Theorem 2.23
val normR_SN: #g:ctx -> #t:ty -> #e:texp g t -> normR g t e ->
  Tot (sSN g t e) (decreases %[t;0])
val sSNe_normR: #g:ctx -> #t:ty -> #e:texp g t -> ssne:sSNe g t e ->
  Tot (normR g t e) (decreases %[t;0])
val sSN_step_normR: #g:ctx -> #t:ty -> #e1:texp g t -> #e2:texp g t
  -> sSN_head_red g t e1 e2 -> normR g t e2 -> Tot (normR g t e1)
  (decreases %[t;1])
let rec normR_SN #g #t #e norm = match t with
  | TBase -> norm
  | TArr ta tb -> let xSNe = SNeVar (ta::g) 0 in
	 let xnorm = sSNe_normR xSNe in
	 let wk = weaken_sub g ta in
	 weaken_sub_renaming g ta;
	 let norm': g':ctx -> r:sub g' g {renaming r} -> e0:texp g' ta
	    -> norm0:normR g' ta e0 -> Tot (normR g' tb (TyApp (subst r e) e0)) =
	   norm in
	 let normB = norm' (ta::g) wk (TyVar 0) xnorm in
	 let snB = normR_SN normB in
	 let sn_e' = extend_SN 0 (subst wk e) snB in
	 sSN_anti_rename e wk sn_e'
and sSNe_normR #g #t #e sne = match t with
  | TBase -> SNNeut sne
  | TArr ta tb -> let f (g':ctx) (r:sub g' g {renaming r}) (e0:texp g' ta)
    (norm0:normR g' ta e0): Tot (normR g' tb (TyApp (subst r e) e0)) = 
      let e0sn = normR_SN norm0 in
      let e' = sSNe_rename sne r in
      let eappsn = SNeApp e' e0sn in
      sSNe_normR eappsn
      in f
and sSN_step_normR #g #t #e1 #e2 sSNst norm2 = match t with
  | TBase -> let e2sn = normR_SN norm2 in
	  SNStep sSNst e2sn
  | TArr ta tb -> let f (g':ctx) (r:sub g' g {renaming r}) (e0:texp g' ta)
    (norm0:normR g' ta e0): Tot (normR g' tb (TyApp (subst r e1) e0)) =
      let norm2': g':ctx -> r:sub g' g {renaming r} -> e0:texp g' ta
      -> norm0:normR g' ta e0 -> Tot (normR g' tb (TyApp (subst r e2) e0))
      = norm2 in
      let norm2app = norm2' g' r e0 norm0 in
      let e1':texp g' (TArr ta tb) = subst r e1 in
      let e2':texp g' (TArr ta tb) = subst r e2 in
      let sSNst':sSN_head_red g' (TArr ta tb) e1' e2' 
	= sSN_head_red_rename sSNst r in
      let sSNst'app: sSN_head_red g' tb (TyApp e1' e0)
	(TyApp e2' e0) = SNHApp sSNst' e0 in
      sSN_step_normR sSNst'app norm2app
      in f

// Definition 2.2
noeq type sem_sub: g':ctx -> g:ctx -> s:sub g' g -> Type =
  | SemNil: g':ctx ->
	      sem_sub g' [] (STNil g')
  | SemCons: #g':ctx ->
	     #g:ctx ->
	     #s:sub g' g ->
	     hsem:sem_sub g' g s ->
	     #t:ty ->
	     #e:texp g' t ->
	     normR g' t e ->
	     sem_sub g' (t::g) (STCons e s)
	     
val sem_index: #g':ctx -> #g:ctx -> #s:sub g' g -> sem:sem_sub g' g s
  -> n:nat {n < length g} ->
  Tot (normR g' (index g n) (sindex s n))
let rec sem_index #g' #g #s sem n = match sem with
  | SemCons hsem norm -> if n = 0 
		 then norm 
		 else sem_index hsem (n-1)

val normR_renaming: #g':ctx -> #g:ctx -> #t:ty -> #e:texp g t
  -> norm:normR g t e -> r:sub g' g {renaming r} ->
  Tot (normR g' t (subst r e))
  (decreases t)
let rec normR_renaming #g' #g #t #e norm r = match t with
  | TBase -> sSN_rename #g #t #e norm #g' r
  | TArr ta tb -> let f (g'':ctx) (r':sub g'' g' {renaming r'})
    (e0:texp g'' ta) (norm0:normR g'' ta e0) 
    :Tot (normR g'' tb (TyApp (subst r' (subst r e)) e0))
    = let norm': g':ctx -> r:sub g' g {renaming r} -> e0:texp g' ta
      -> norm0:normR g' ta e0 -> Tot (normR g' tb (TyApp (subst r e) e0))
      = norm in
    sub_app_renaming r' r;
    subst_subst_app r' r e;
    norm' g'' (sub_app r' r) e0 norm0
   in f

val sem_sub_weaken: #g'':ctx -> #g':ctx -> #g:ctx -> #s:sub g' g
  -> sem:sem_sub g' g s -> r:sub g'' g' {renaming r} ->
  Tot (sem_sub g'' g (sub_app r s))
  (decreases sem)
let rec sem_sub_weaken #g'' #g' #g #s sem r = match sem with
  | SemNil g' -> SemNil g''
  | SemCons hsem hnorm -> let hsem' = sem_sub_weaken hsem r in
    let hnorm' = normR_renaming hnorm r in
    SemCons hsem' hnorm'

// Lemma 2.24
val fundamental: #g':ctx -> #g:ctx -> #t:ty -> e:texp g t
  -> #s:sub g' g -> hsem:sem_sub g' g s -> 
  Tot (normR g' t (subst s e))
  (decreases e)
let rec fundamental #g' #g #t e #s hsem = match e with
  | TyVar v -> sem_index hsem v
  | TyApp e1 e2 -> let norm1 = fundamental e1 hsem in
	  let norm2 = fundamental e2 hsem in
	  id_sub_renaming g';
	  id_sub_id (subst s e);
	  norm1 g' (id_sub g') (subst s e2) norm2
  | TyLam #g tlam #t' e' -> let f (g'':ctx) (r:sub g'' g' {renaming r})
    (e0:texp g'' tlam) (norm0:normR g'' tlam e0)
    : Tot (normR g'' t' (TyApp (subst r (subst s e)) e0)) = 
    let sem_rs: sem_sub g'' g (sub_app r s) = sem_sub_weaken hsem r in
    let e0rs = STCons e0 (sub_app r s) in
    let sem_rs':sem_sub g'' (tlam::g) e0rs = SemCons sem_rs norm0 in
    let e'_sub_norm: normR g'' t' (subst e0rs e') 
      = fundamental e' sem_rs' in
    let e0_SN: sSN g'' tlam e0 = normR_SN norm0 in
    let e_sub_SNst: sSN_head_red g'' t' (TyApp (TyLam tlam (subst 
      (sub_elam tlam (sub_app r s)) e')) e0)
      (subst (sub_beta e0) (subst (sub_elam tlam (sub_app r s)) e'))
      = SNHBeta (subst (sub_elam tlam (sub_app r s)) e') e0_SN in
    subst_subst_app r s e;
    sub_beta_elam2 tlam e' e0 (sub_app r s);
    sSN_step_normR e_sub_SNst e'_sub_norm
    in f

val id_sem_sub': n:nat -> g:ctx {n <= length g} -> 
  Tot (sem_sub g (drop n g) (id_sub' n g))
  (decreases ((length g) - n))
let rec id_sem_sub' n g = if n = length g then SemNil g
  else (
    let normV = sSNe_normR (SNeVar g n) in
    SemCons (id_sem_sub' (n+1) g) normV 
  )

// Corollary 2.25
val strong_norm: #g:ctx -> #t:ty -> e:texp g t ->
  Tot (sSN g t e)
let strong_norm #g #t e = 
  let norm_e = fundamental e (id_sem_sub' 0 g) in
  id_sub_id e;
  normR_SN norm_e
