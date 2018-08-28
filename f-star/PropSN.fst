module PropSN

open FStar.List.Tot
open FStar.Math.Lib
open FStar.Constructive
open Prelude
open Base

// Lemma 2.10
val sn_vars: n:nat -> g:ctx -> v:nat{v < length g} ->
  Tot (ssn (n+1) g (index g v) (TyVar v))
let sn_vars n g v = let t = index g v in
  let f = (fun (e':texp g t) (st:step g t (TyVar v) e') 
	    -> match st with) in
    Ssn n f

val sn_lam: #n:nat -> #g:ctx -> tlam:ty -> #t:ty -> #e:texp (tlam::g) t
  -> hssn:ssn n (tlam::g) t e ->
  Tot (ssn n g (TArr tlam t) (TyLam tlam e))
  (decreases n)
let rec sn_lam #n #g tlam #t #e hssn = match hssn with
  | Ssn m f -> let f': e':texp g (TArr tlam t)  
    -> st:step g (TArr tlam t) (TyLam tlam e) e'
	-> Tot (ssn m g (TArr tlam t) e') = fun e' st ->
	  (match st with
	  | SLam #g t'lam #t' #e1 #e2 hst -> 
		 sn_lam t'lam (f e2 hst)
	  ) in
	Ssn m f'

val sn_beta: #n:nat -> #g:ctx -> tlam:ty -> #t:ty -> e1:texp (tlam::g) t
  -> e2:texp g tlam -> hssn:ssn n g t (subst (sub_beta e2) e1) ->
  Tot (ssn n (tlam::g) t e1)
let rec sn_beta #n #g tlam #t e1 e2 hssn = match hssn with
  | Ssn m f -> let f': e1':texp (tlam::g) t -> hst:step (tlam::g) t e1 e1' ->
	Tot (ssn m (tlam::g) t e1') = fun e1' hst ->
	   let hst' = step_beta_sub hst e2 in
	   let ssn' = f (subst (sub_beta e2) e1') hst' in
	   sn_beta tlam e1' e2 ssn'
	in Ssn m f'

val sn_app: #n:nat -> #g:ctx -> #t1:ty -> #t2:ty -> e1:texp g (TArr t1 t2)
  -> e2:texp g t1 -> hssn:ssn n g t2 (TyApp e1 e2) ->
  Tot (ssn n g (TArr t1 t2) e1 * ssn n g t1 e2)
let rec sn_app #n #g #t1 #t2 e1 e2 hssn = match hssn with
  | Ssn m f -> let f1: e1':texp g (TArr t1 t2) 
    -> hst1:step g (TArr t1 t2) e1 e1'
    -> Tot (ssn m g (TArr t1 t2) e1') = fun e1' hst1 ->
      let hst1' = SAppL e2 hst1 in
      let hssn' = f (TyApp e1' e2) hst1' in
      let ssn'',_ = sn_app e1' e2 hssn' in
      ssn''
   in let f2: e2':texp g t1 -> hst2:step g t1 e2 e2'
     -> Tot (ssn m g t1 e2') = fun e2' hst2 ->
       let hst2' = SAppR e1 hst2 in
       let hssn' = f (TyApp e1 e2') hst2' in
       let _,ssn'' = sn_app  e1 e2' hssn' in
       ssn''
   in 
   (Ssn (n-1) f1),(Ssn (n-1) f2)

val step_sn: #g:ctx -> #t:ty -> #e1:texp g t -> #e2:texp g t ->
  hst:step g t e1 e2 -> #n:nat {n > 0} -> hssn:ssn n g t e1 ->
  Tot (ssn (n-1) g t e2)
let step_sn #g #t #e1 #e2 hst #n hssn = 
  multi_step_sn (MSingle hst (MRefl g t e2)) hssn

// Lemma 2.11
val weak_head_expand: #g:ctx -> tlam:ty -> #t:ty -> #e1:texp (tlam::g) t
  -> #e2:texp g tlam -> #n2:nat -> #ns:nat -> hssn2:ssn n2 g tlam e2 
  -> hssns:ssn ns g t (subst (sub_beta e2) e1) ->
  Tot (ssn (1 + ns + n2) g t (TyApp (TyLam tlam e1) e2))
  (decreases (ns+n2))
let rec weak_head_expand #g tlam #t #e1 #e2 #n2 #ns hssn2 hssns =
  let n' = ns + n2 in
  let f': e':texp g t -> st:step g t (TyApp (TyLam tlam e1) e2) e' ->
    Tot (ssn n' g t e') = fun e' st -> (match st with
      | SAppL #g #_ #_ #te1 #te1'  _e2 hst1 -> (match hssns with
	| Ssn m f -> (match te1' with | TyLam tlam e1' ->
	  (match hst1 with | SLam _ hst1' ->
	  let hstb: step g t (subst (sub_beta e2) e1) (subst (sub_beta e2) e1')
	    = step_beta_sub hst1' e2 in
	  let ssns':ssn (ns-1) g t (subst (sub_beta e2) e1')
	    = step_sn hstb hssns in
	  weak_head_expand tlam hssn2 ssns'
	))
      )
      | SAppR #g #_ #_ _te1 #_e2 #e2' hst2 -> (match hssn2 with
	| Ssn m f ->
	  let msts:multi_step g t (subst (sub_beta e2) e1)
	    (subst (sub_beta e2') e1) = multi_step_beta tlam e1 hst2 in
	  let msl = multi_step_len msts in
	  ssn_mst_size hssns msts;
	  let ssns':ssn (ns - msl) g t (subst (sub_beta e2') e1)
	    = multi_step_sn msts hssns in
          let _:step g tlam e2 e2' = hst2 in
	  //hssn2: ssn n2 g tlam e2
	  let ssn2':ssn (n2-1) g tlam e2' = step_sn hst2 hssn2 in
	  assert (e' == TyApp (TyLam tlam e1) e2');
	  let ssn'':ssn (1 + ns -msl + n2 -1) g t e'
	    = weak_head_expand tlam ssn2' ssns' in
	  sn_nat_weaken n' ssn''
      )
      | SBeta _tlam _e1 _e2 -> sn_nat_weaken n' hssns
      )
    in Ssn n' f'

type ne: g:ctx -> t:ty -> e:texp g t -> Type =
  | NeVar: g:ctx ->
	   v:var {v < length g} ->
	   ne g (index g v) (TyVar v)
  | NeApp: #g:ctx ->
	   #t1:ty ->
	   #t2:ty ->
	   #e1:texp g (TArr t1 t2) ->
	   hne:ne g (TArr t1 t2) e1 ->
	   e2:texp g t1 ->
	   ne g t2 (TyApp e1 e2)

// Lemma 2.12
val ne_closed_step: #g:ctx -> #t:ty -> #e:texp g t -> #e':texp g t
  -> hne:ne g t e -> hst:step g t e e' ->
  Tot (ne g t e')
  (decreases hne)
let rec ne_closed_step #g #t #e #e' hne hst = match hne with
  | NeVar g v -> hne
  | NeApp hne' e2 -> (match hst with
    | SAppL e2 hst1 -> let hne'' = ne_closed_step hne' hst1 in
      NeApp hne'' e2
    | SAppR #g #t1 #t2 e1 #e2 #e2' hst2 -> NeApp hne' e2'
    )

val ne_app_sn: #g:ctx -> #t1:ty -> #t2:ty -> #e1:texp g (TArr t1 t2)
  -> #e2:texp g t1 -> hne1:ne g (TArr t1 t2) e1 -> #n1:nat -> #n2:nat
  -> hssn1:ssn n1 g (TArr t1 t2) e1 -> hssn2:ssn n2 g t1 e2 ->
  Tot (ssn (1+n1+n2) g t2 (TyApp e1 e2))
  (decreases (n1+n2))
let rec ne_app_sn #g #t1 #t2 #e1 #e2 hne1 #n1 #n2 hssn1 hssn2 =
  let f: e':texp g t2 -> hst:step g t2 (TyApp e1 e2) e' ->
    Tot (ssn (n1+n2) g t2 e') = fun e' hst -> (match hst with
  | SAppL e2 hst1 -> let ssn1' = step_sn hst1 hssn1 in
    let hne1' = ne_closed_step hne1 hst1 in
    ne_app_sn hne1' ssn1' hssn2
  | SAppR e1 hst2 -> let ssn2' = step_sn hst2 hssn2 in
    ne_app_sn hne1 hssn1 ssn2'
  ) in
  Ssn (n1+n2) f

noeq type ssn_head_red: g:ctx -> t:ty -> e1:texp g t -> e2:texp g t -> Type =
  | SsnHBeta: #g:ctx ->
	      #tlam:ty ->
	      #t:ty ->
	      #e1:texp g tlam ->
	      e2:texp (tlam::g) t ->
	      #n:nat ->
	      hssn:ssn n g tlam e1 ->
	      ssn_head_red g t (TyApp (TyLam tlam e2) e1) 
		(subst (sub_beta e1) e2)
  | SsnHApp: #g:ctx ->
	     #t1:ty ->
	     #t2:ty ->
	     #e1:texp g (TArr t1 t2) ->
	     #e1':texp g (TArr t1 t2) ->
	     hshr:ssn_head_red g (TArr t1 t2) e1 e1' ->
	     e2:texp g t1 ->
	     ssn_head_red g t2 (TyApp e1 e2) (TyApp e1' e2)


// Lemma 2.13
val sn_confulence: #g:ctx -> #t:ty -> #e1:texp g t -> #e2:texp g t -> #e2':texp g t
  -> hshr:ssn_head_red g t e1 e2 -> hst:step g t e1 e2' ->
  Tot (cor (ceq e2 e2') 
    (q:texp g t & ssn_head_red g t e2' q * multi_step g t e2 q))
  (decreases hshr)
let rec sn_confulence #g #t #e1 #e2 #e2' hshr hst = match hshr with
  | SsnHBeta e02 hssn1 -> (match hst with
    | SBeta tlam e01 e02 -> IntroL Refl
    | SAppL e01 hst2 -> (match hst2 with
      | SLam #g tlam #t #e02 #e02' hst1' -> let q = subst (sub_beta e01) e02' in
	let hshr' = SsnHBeta e02' hssn1 in
	let stb = step_beta_sub hst1' e01 in
	let mstb = MSingle stb (MRefl g t (subst (sub_beta e01) e02')) in
	IntroR (Mkdtuple2 q (hshr', mstb))
      )
    | SAppR #_ #_ #_ el02 #e01 #e01' hst1 -> 
      let q = subst (sub_beta e01') e02 in
      let ssn1' = step_sn hst1 hssn1 in
      let hshr' = SsnHBeta e02 ssn1' in
      (match el02 with
	| TyLam tlam _ -> let mstb = multi_step_beta tlam e02 hst1 in
	  IntroR (Mkdtuple2 q (hshr', mstb))
      )
    )
  | SsnHApp #g #_ #_ #e02 #e02' hshr' e01 -> (match hst with
    | SAppL e01 hst2 -> (match sn_confulence hshr' hst2 with
      | IntroL _ -> IntroL Refl
      | IntroR (Mkdtuple2 p (snp,mstp)) -> let q = TyApp p e01 in
	let hshr'' = SsnHApp snp e01 in
	let mstq = multi_step_appl e01 mstp in
	IntroR (Mkdtuple2 q (hshr'', mstq))
      )
    | SAppR #g #t1 #t2 e02 #e01 #e01' hst1 -> let q = TyApp e02' e01' in
      let hshr'' = SsnHApp hshr' e01' in
      let mst1' = MSingle hst1 (MRefl g t1 e01') in
      let mstq = multi_step_appr e02' mst1' in
      IntroR (Mkdtuple2 q (hshr'', mstq))
    )

// Lemma 2.14
val back_closed_sn_app: #g:ctx -> #t1:ty -> #t2:ty -> #e1:texp g t1
  -> #e2:texp g (TArr t1 t2) -> #e2':texp g (TArr t1 t2) -> #n1:nat
  -> ssn1:ssn n1 g t1 e1 -> #n2:nat -> ssn2:ssn n2 g (TArr t1 t2) e2
  -> snhead2:ssn_head_red g (TArr t1 t2) e2 e2' -> #nap:nat 
  -> ssnap:ssn nap g t2 (TyApp e2' e1) ->
  Tot (ssn (1+n2+nap) g t2 (TyApp e2 e1))
  (decreases (n1+n2))
let rec back_closed_sn_app #g #t1 #t2 #e1 #e2 #e2' #n1 ssn1 #n2 ssn2
  snhead2 #nap ssnap = let f (e':texp g t2) (hst:step g t2 (TyApp e2 e1) e')
    :ssn (n2+nap) g t2 e' = match hst with
    | SAppL e1 hst2 -> (match sn_confulence snhead2 hst2 with
      | IntroL _ -> assert (e' == TyApp e2' e1); 
	   sn_nat_weaken (n2+nap) ssnap
      | IntroR (Mkdtuple2 p (snp,mstp)) -> 
	(match mstp with
	 | MRefl _ _ _ -> assert (e2' == p); 
	   let ssn2'' = step_sn hst2 ssn2 in
	   back_closed_sn_app ssn1 ssn2'' snp ssnap
	 | MSingle _ _ ->
	   let mstp':multi_step g t2 (TyApp e2' e1) (TyApp p e1) 
	       = multi_step_appl e1 mstp in
	   ssn_mst_size ssnap mstp';
	   let mstpl = multi_step_len mstp' in
	   let pe1sn:ssn (nap -mstpl) g t2 (TyApp p e1)
	     = multi_step_sn mstp' ssnap in
	   let ssn2'' = step_sn hst2 ssn2 in
	   let res = back_closed_sn_app ssn1 ssn2'' snp pe1sn in
	   multi_step_single_len mstp';
	   sn_nat_weaken (n2+nap) res
	)
      )
    | SAppR e2 hst1 -> 
      let hst' = SAppR e2' hst1 in
      let ssnap' = step_sn hst' ssnap in
      let ssn1' = step_sn hst1 ssn1 in
      let res = back_closed_sn_app ssn1' ssn2 snhead2 ssnap' in
      sn_nat_weaken (n2+nap) res
    in Ssn (n2+nap) f

val ssn_head_inner_n: #g:ctx -> #t:ty -> #e:texp g t -> #e':texp g t
  -> hshr:ssn_head_red g t e e' -> Tot nat (decreases hshr)
let rec ssn_head_inner_n #g #t #e #e' hshr = match hshr with
  | SsnHBeta #g #tlam #t #e1 e2 #n ssn1 -> n
  | SsnHApp hshr' e2 -> (*0 //*) ssn_head_inner_n hshr'

val back_closed_sn: #g:ctx -> #t:ty -> #e:texp g t -> #e':texp g t
  -> hshr:ssn_head_red g t e e' -> #n:nat -> hssn:ssn n g t e' ->
  Tot (ssn (1+n+ssn_head_inner_n hshr) g t e)
  (decreases hshr)
let rec back_closed_sn #g #t #e #e' hshr #n hssn = 
  match hshr with
  | SsnHBeta #g #tlam #t #e1 e2 #n' ssn1 -> 
    weak_head_expand #g tlam #t #e2 ssn1 hssn
  | SsnHApp #g #t1 #t2 #e1 #e1' hshr' e2 -> 
    assert (e' == TyApp e1' e2);
    assert (t2 == t);
    let ssn1',ssn2:ssn n g (TArr t1 t2) e1' * ssn n g t1 e2
      = sn_app e1' e2 hssn in
    let ssn1 = back_closed_sn hshr' ssn1' in
    let ret = back_closed_sn_app ssn2 ssn1 hshr' hssn in
    //sn_nat_weaken (1+n+ssn_head_inner_n hshr) ret
    admit ()
