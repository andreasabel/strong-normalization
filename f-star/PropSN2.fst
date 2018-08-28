module PropSN2

open FStar.List.Tot
open FStar.Math.Lemmas
open FStar.Constructive
open Prelude
open Base
open PropSN
open Sound

// Lemma 2.20
val sSN_rename: #g:ctx -> #t:ty -> #e:texp g t -> hSN:sSN g t e
  -> #g':ctx -> r:sub g' g {renaming r} ->
  Tot (sSN g' t (subst r e))
  (decreases hSN)
val sSNe_rename: #g:ctx -> #t:ty -> #e:texp g t -> hSNe:sSNe g t e
  -> #g':ctx -> r:sub g' g {renaming r} ->
  Tot (sSNe g' t (subst r e))
  (decreases hSNe)
val sSN_head_red_rename: #g:ctx -> #t:ty -> #e1:texp g t -> #e2:texp g t
  -> hSN_step:sSN_head_red g t e1 e2 -> #g':ctx -> r:sub g' g {renaming r} ->
  Tot (sSN_head_red g' t (subst r e1) (subst r e2))
  (decreases hSN_step)
let rec sSN_rename #g #t #e hSN #g' r = match hSN with
  | SNNeut hsne -> SNNeut (sSNe_rename hsne r)
  | SNLam tlam hsn' -> 
    sub_elam_renaming tlam r;
    let hsn'' = sSN_rename hsn' (sub_elam tlam r) in
    SNLam tlam hsn''
  | SNStep snstep hsn' -> let snstep' = sSN_head_red_rename snstep r in
    let hsn'' = sSN_rename hsn' r in
    SNStep snstep' hsn''
and sSNe_rename #g #t #e hSNe #g' r = match hSNe with
  | SNeVar g v -> sindex_renaming r v;
    (match sindex r v with
    | TyVar v' -> SNeVar g' v'
  )
  | SNeApp hsne' hsn' -> let hsne'' = sSNe_rename hsne' r in
    let hsn'' = sSN_rename hsn' r in
    SNeApp hsne'' hsn''
and sSN_head_red_rename #g #t #e1 #e2 hSN_step #g' r = match hSN_step with
  | SNHBeta #g #tlam #_ #e1' e2' hsn' -> let hsn'' = sSN_rename hsn' r in
    let r_weak = sub_weaken tlam r in
    let r' = sub_elam tlam r in
    let e2'' = subst r' e2' in
    assert (subst r e1 == TyApp (TyLam tlam e2'') (subst r e1'));
    sub_sub_beta r tlam e1' e2';
    SNHBeta e2'' hsn''
  | SNHApp hshr e2' -> let hshr' = sSN_head_red_rename hshr r in
    let e2'' = subst r e2' in
    SNHApp hshr' e2''

// Lemma 2.21
val sSN_anti_rename: #g':ctx -> #g:ctx -> #t:ty -> e:texp g t 
  -> r:sub g' g {renaming r} -> hSN:sSN g' t (subst r e) ->
  Tot (sSN g t e)
  (decreases hSN)
val sSNe_anti_rename: #g':ctx -> #g:ctx -> #t:ty -> e:texp g t
  -> r:sub g' g {renaming r} -> hSNe:sSNe g' t (subst r e) ->
  Tot (sSNe g t e)
  (decreases hSNe)
val sSN_head_red_anti_rename: #g':ctx -> #g:ctx -> #t:ty -> e1:texp g t
  -> #e2':texp g' t -> r:sub g' g {renaming r}
  -> hSNst:sSN_head_red g' t (subst r e1) e2' ->
  Tot (e2:texp g t & sSN_head_red g t e1 e2 * ceq e2' (subst r e2))
  (decreases hSNst)
let rec sSN_anti_rename #g' #g #t e r hSN = match hSN with
  | SNNeut hsne -> SNNeut (sSNe_anti_rename e r hsne)
  | SNLam tlam hsn' -> renaming_prop r e;
    (match e with
    | TyLam _ e' -> 
    sub_elam_renaming tlam r;
    let r' = sub_elam tlam r in
    let hsn'' = sSN_anti_rename e' r' hsn' in
    SNLam tlam hsn''
    )
  | SNStep #g #_ #e1 #e2 snstep hsn' ->
    let Mkdtuple2 e2 (hst',_) = sSN_head_red_anti_rename e r snstep in
    let ssn1 = sSN_anti_rename e2 r hsn' in
      SNStep hst' ssn1
and sSNe_anti_rename #g' #g #t e r hSNe = match hSNe with
  | SNeVar g' v -> SNeVar g (TyVar?.v e)
  | SNeApp hsne' hsn' -> renaming_prop r e;
    (match e with
    | TyApp e1 e2 -> let hsne'' = sSNe_anti_rename e1 r hsne' in
    let hsn'' = sSN_anti_rename e2 r hsn' in
    SNeApp hsne'' hsn''
    )
and sSN_head_red_anti_rename #g' #g #t e1 #e2' r hSNst = 
  renaming_prop r e1;
  match hSNst with
  | SNHBeta e12' hsn -> (match e1 with
    | TyApp el12 e11 -> 
      let hsn' = sSN_anti_rename e11 r hsn in
      renaming_prop r el12;
      (match el12 with
	| TyLam tlam e12 -> sub_sub_beta r tlam e11 e12;
	  Mkdtuple2 (subst (sub_beta e11) e12) (SNHBeta e12 hsn', Refl)
      )
    )
  | SNHApp hshr' e12' -> (match e1 with
    | TyApp e11 e12 ->
    let Mkdtuple2 e21 (hshr,_) = sSN_head_red_anti_rename e11 r hshr' in
    Mkdtuple2 (TyApp e21 e12) (SNHApp hshr e12, Refl)
    )

// Lemma 2.22
val extend_SN: #g:ctx -> #t:ty -> v:var {v < length g}
  -> e:texp g (TArr (index g v) t) -> hSN:sSN g t (TyApp e (TyVar v)) ->
  Tot (sSN g (TArr (index g v) t) e)
  (decreases hSN)
let rec extend_SN #g #t v e hSN = match hSN with
  | SNNeut hsne -> (match hsne with
    | SNeApp hsne' _ -> SNNeut hsne'
    )
  | SNStep snstep hsn -> (match snstep with
    | SNHBeta e2 hsn' -> 
      sub_beta_renaming (TyVar #g v);
      let e' = sSN_anti_rename e2 (sub_beta (TyVar v)) hsn  in
      SNLam (index g v) e'
    | SNHApp #g #_ #_ #e1 #e1' hshr e2 -> 
      let _:sSN g t (TyApp e1' (TyVar v)) = hsn in
      let _:texp g (TArr (index g v) t) = e1' in
      let sn' = extend_SN v e1' hsn in
      SNStep hshr sn'
      )
