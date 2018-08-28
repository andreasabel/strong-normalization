module Base

open FStar.List.Tot
open FStar.Math.Lib
open FStar.Constructive
open Prelude

type var = nat

type ty =
  | TBase : ty
  | TArr : ty -> ty -> ty

type ctx = list ty

type texp: ctx -> ty -> Type =
  | TyVar: #g:ctx ->
            v:var {v < length g} ->
            texp g (index g v)
  | TyLam: #g:ctx ->
            tlam:ty ->
           #t:ty ->
           $e':texp (tlam::g) t ->
           texp g (TArr tlam t)
  | TyApp: #g:ctx ->
           #t1:ty ->
           #t2:ty ->
           $e1:texp g (TArr t1 t2) ->
           $e2:texp g t1 ->
           texp g t2

type sub: g':ctx -> g:ctx -> Type =
  | STNil: g':ctx ->
           sub g' []
  | STCons: #g':ctx ->
            #t:ty ->
            #g:ctx ->
            $e:texp g' t ->
            $hst:sub g' g ->
            sub g' (t::g)

val renaming: #g':ctx -> #g:ctx -> s:sub g' g -> Tot Type0
   (decreases s)
let rec renaming #g' #g s = match s with
  | STNil _ -> True
  | STCons e s' -> TyVar? e /\ renaming s'

val id_sub':n:nat -> g:ctx {n<=length g} -> 
  Tot (sub g (drop n g))
  (decreases ((length g) - n))
let rec id_sub' n g = if n = length g then STNil g 
            else STCons (TyVar n) (id_sub' (n+1) g)

val id_sub: g:ctx -> Tot (sub g g)
let id_sub g = id_sub' 0 g

val id_sub'_renaming: n:nat -> g:ctx {n<= length g} ->
  Lemma (ensures (renaming (id_sub' n g)))
  (decreases ((length g) - n))
let rec id_sub'_renaming n g = if n = length g then ()
  else id_sub'_renaming (n+1) g

val id_sub_renaming: g:ctx -> Lemma (renaming (id_sub g))
let id_sub_renaming g = id_sub'_renaming 0 g

val sindex: #g':ctx -> #g:ctx -> s:sub g' g 
  -> n:nat {n < length g} 
  -> Tot (texp g' (index g n))
let rec sindex #g' #g s n = match s with
  | STCons e s' -> if n = 0 then e else sindex s' (n-1)

val sindex_renaming: #g':ctx -> #g:ctx -> r:sub g' g
  -> n:nat {n < length g} ->
  Lemma (requires (renaming r))
  (ensures (TyVar? (sindex r n)))
let rec sindex_renaming #g' #g s n = match s with
  | STCons e s' -> if n = 0 then () else sindex_renaming s' (n-1)

irreducible val id_sub'_index: n:nat -> g:ctx {n< length g} -> m:nat {m < length g - n} ->
  Lemma (ensures (sindex (id_sub' n g) m == TyVar (n+m)))
  (decreases m)
let rec id_sub'_index n g m = if m = 0 then ()
  else id_sub'_index (n+1) g (m-1)

val sfind_index: #g':ctx -> #g:ctx -> s:sub g' g -> #t:ty
  -> e:texp g' t -> Tot (on:option nat {(Some? on ==>
   (let n = Some?.v on in n < length g /\ index g n == t 
   /\ sindex s n == e))})
let rec sfind_index #g' #g s #t e = match s with
  | STNil _ -> None
  | STCons #g' #t' #g e' s' -> if t = t' && e = e' then Some 0
    else match sfind_index s' e with
        | Some n -> Some (n+1)
        | None -> None

// Lemma 2.1 implicid in encoding

// Lemma 2.2
val texp_exchange: #g:ctx -> n:nat {n+1 < length g} ->
  #t:ty -> e:texp g t -> Tot (texp (exchange_list n g) t)
  (decreases e)
let rec texp_exchange #g n #t e = match e with
  | TyVar x -> exchange_list_props n g;
          if x = n then TyVar (x+1)
              else if x = n + 1 then TyVar (x-1)
              else TyVar x
  | TyApp e1 e2 -> TyApp (texp_exchange n e1) (texp_exchange n e2)
  | TyLam tlam e' -> TyLam tlam (texp_exchange (n+1) e')

val texp_weaken_at: #g:ctx -> #t:ty -> n:nat {n <= length g}
  -> t':ty -> e:texp g t -> Tot (texp (insertAt g t' n) t)
  (decreases e)
let rec texp_weaken_at #g #t n t' e  = match e with
  | TyVar x -> if x >= n then (
      insert_index g t' n (x+1);
      TyVar (x+1)
      ) else (
        insert_index g t' n x;
        TyVar x 
      )
  | TyApp e1 e2 -> TyApp (texp_weaken_at n t' e1) (texp_weaken_at n t' e2)
  | TyLam tlam e' -> TyLam tlam (texp_weaken_at (n+1) t' e') 

val texp_weaken: #g:ctx -> #t:ty -> t':ty -> e:texp g t ->
  Tot (texp (t'::g) t)
let texp_weaken #g #t t' e = texp_weaken_at 0 t' e

val texp_weaken_level: #g:ctx -> #t:ty -> g2:ctx -> e:texp g t ->
  Tot (texp (g2@g) t)
  (decreases g2)
let rec texp_weaken_level #g #t g2 e = match g2 with
  | [] -> e
  | hd::tl -> let e' = texp_weaken_level tl e in
    texp_weaken hd e'

val texp_weaken_level_app: #g:ctx -> #t1:ty -> #t2:ty -> g2:ctx
  -> e1:texp g (TArr t1 t2) -> e2:texp g t1 ->
  Lemma (ensures (texp_weaken_level g2 (TyApp e1 e2) ==
    TyApp (texp_weaken_level g2 e1) (texp_weaken_level g2 e2)))
    (decreases g2)
let rec texp_weaken_level_app #g #t1 #t2 g2 e1 e2 = match g2 with
  | [] -> ()
  | hd::tl -> texp_weaken_level_app tl e1 e2

val texp_weaken_level_var: g:ctx -> v:var {v < length g} -> g2:ctx -> 
    Lemma (texp_weaken_level g2 (TyVar #g v) == TyVar (v+length g2))
let rec texp_weaken_level_var g v g2 = match g2 with
  | [] -> ()
  | hd::tl -> texp_weaken_level_var g v tl;
    assert (texp_weaken_level tl (TyVar #g v) == TyVar (v+length tl));
    assert (texp_weaken_level g2 (TyVar #g v) == texp_weaken hd
      (texp_weaken_level tl (TyVar #g v)));
    assert (texp_weaken hd (TyVar #(tl@g) (v+length tl)) ==
      TyVar (v+length tl +1))

val sub_weaken: #g':ctx -> #g:ctx -> t:ty ->
  s:sub g' g -> Tot (sub (t::g') g)
  (decreases s)
let rec sub_weaken #g' #g t s = match s with
  | STNil g' -> STNil (t::g')
  | STCons e s' -> let e' = texp_weaken t e in
    let s'' = sub_weaken t s' in
    STCons e' s''

irreducible val sub_weaken_index: #g':ctx -> #g:ctx -> t:ty ->
  s:sub g' g -> n:nat {n < length g} -> 
  Lemma (sindex (sub_weaken t s) n
    == texp_weaken t (sindex s n))
let rec sub_weaken_index #g' #g t s n = match s with
  | STCons e s' -> if n = 0 then () else sub_weaken_index t s' (n-1)

irreducible val sub_weaken_renaming: #g':ctx -> #g:ctx -> t:ty ->
  r:sub g' g {renaming r} -> Lemma (renaming (sub_weaken t r))
let rec sub_weaken_renaming #g' #g t r = match r with
  | STNil _ -> ()
  | STCons e s' -> assert (TyVar? (texp_weaken t e));
    sub_weaken_renaming t s'

val sub_elam: #g':ctx -> #g:ctx -> t:ty -> s:sub g' g ->
  Tot (sub (t::g') (t::g))
let rec sub_elam #g' #g t s = let s' = sub_weaken t s in
  STCons (TyVar 0) s'

irreducible val sub_elam_index: #g':ctx -> #g:ctx -> t:ty -> s:sub g' g ->
  n:nat {n < length g} -> Lemma (sindex (sub_elam t s) (n+1)
    == texp_weaken t (sindex s n))
let sub_elam_index #g' #g t s n = match s with
  | STCons _ s' -> if n = 0 then ()
    else sub_weaken_index t s' (n-1)

val sub_elam_level: #g':ctx -> #g:ctx -> g2:ctx -> s:sub g' g ->
  Tot (sub (g2@g') (g2@g)) (decreases g2)
let rec sub_elam_level #g' #g g2 s = match g2 with
  | [] -> s
  | hd::tl -> let s' = sub_elam_level tl s in
    sub_elam hd s'

irreducible val sub_elam_level_id: #g':ctx -> #g:ctx -> g2:ctx -> s:sub g' g 
  -> n:nat {n < length g2} ->
 Lemma (ensures (index (g2@g) n == index (g2@g') n 
   /\ sindex (sub_elam_level g2 s) n == TyVar #(g2@g') n))
 (decreases g2)
let rec sub_elam_level_id #g' #g g2 s n =
  index_append g2 g n;
  index_append g2 g' n;
  match g2 with
  | hd::tl -> if n = 0 then ()
          else (sub_elam_level_id tl s (n-1);
               index_append tl g (n-1);
               sub_elam_index hd (sub_elam_level tl s) (n-1)
            )

irreducible val sub_elam_level_sub: #g':ctx -> #g:ctx -> g2:ctx -> s:sub g' g
  -> n:nat {length g2 <= n /\ n < length g2 + length g} -> 
  Lemma (ensures (index (g2@g) n == index g (n - length g2)
    /\ sindex (sub_elam_level g2 s) n 
    == texp_weaken_level g2 (sindex s (n - length g2))))
  (decreases g2)
let rec sub_elam_level_sub #g' #g g2 s n =
  index_append g2 g n;
  assert (index (g2@g) n == index g (n-length g2));
  match g2 with
  | [] -> ()
  | hd::tl -> sub_elam_level_sub tl s (n-1);
          assert (n-1 < length tl + length g);
          assert (sindex (sub_elam_level tl s) (n-1)
            == texp_weaken_level tl (sindex s (n -1 - length tl)));
          assert (sub_elam_level g2 s == sub_elam hd
            (sub_elam_level tl s));
          sub_elam_index hd (sub_elam_level tl s) (n-1)

irreducible val sub_elam_renaming: #g':ctx -> #g:ctx -> t:ty -> r:sub g' g {renaming r} ->
  Lemma (renaming (sub_elam t r))
let sub_elam_renaming #g' #g t r = sub_weaken_renaming t r

val subst: #g':ctx -> #g:ctx -> #t:ty
  -> s:sub g' g -> e:texp g t ->
  Tot (texp g' t)
  (decreases e)
let rec subst #g' #g #t s e = match e with
  | TyApp e1 e2 -> TyApp (subst s e1) (subst s e2)
  | TyLam tlam e' -> TyLam tlam (subst (sub_elam tlam s) e')
  | TyVar x -> sindex s x

val sub_beta: #g:ctx -> #t:ty -> e:texp g t ->
  Tot (sub g (t::g))
let sub_beta #g #t e = STCons e (id_sub g)

val sub_beta_index: #g:ctx -> #t:ty -> e:texp g t ->
  i:nat {i < length (t::g)} ->
  Lemma (ensures ((i==0 ==> sindex (sub_beta e) 0 == e)
    /\ (i <> 0 ==> sindex (sub_beta e) i == TyVar #g (i-1))))
let sub_beta_index #g #t e i = if i = 0 then ()
  else id_sub'_index 0 g (i-1)

val sub_beta_level: #g1:ctx -> g2:ctx -> #t:ty -> e:texp g1 t ->
  Tot (sub (g2@g1) (g2@t::g1)) (decreases g2)
let sub_beta_level #g1 g2 #t e = sub_elam_level g2 (sub_beta e)

val sub_beta_renaming: #g:ctx -> #t:ty -> e:texp g t ->
  Lemma (requires (TyVar? e))
  (ensures (renaming (sub_beta e)))
let sub_beta_renaming #g #t e = id_sub_renaming g

val renaming_prop: #g':ctx -> #g:ctx -> r:sub g' g
  -> #t:ty -> e:texp g t
  -> Lemma (requires (renaming r))
  (ensures ((TyVar? (subst r e) ==> TyVar? e)
    /\ (TyLam? (subst r e) ==> TyLam? e)
    /\ (TyApp? (subst r e) ==> TyApp? e)))
let rec renaming_prop #g' #g r #t e = match e with
  | TyVar x -> sindex_renaming r x;
    assert (TyVar? (subst r e))
  | TyApp e1 e2 -> assert (TyApp? (subst r e))
  | TyLam tlam e' -> assert (TyLam? (subst r e))

val sub_eq_index: #g':ctx -> #g:ctx -> s1:sub g' g -> s2:sub g' g
  -> (n:nat {n < length g} -> Tot (ceq (sindex s1 n) (sindex s2 n))) ->
  Lemma (s1 == s2)
let rec sub_eq_index #g' #g s1 s2 f = match s1 with
  | STNil _ -> ()
  | STCons e1 s1' -> (match s2 with
           | STCons e2 s2' -> let _ = f 0 in
             sub_eq_index s1' s2' (fun n -> f (n+1))
           )

val id_sub_elam: g:ctx -> t:ty ->
  Lemma (sub_elam t (id_sub g) == id_sub (t::g))
let id_sub_elam g t = let s1 = sub_elam t (id_sub g) in
  let s2 = id_sub (t::g) in
  let f (n:nat {n < length (t::g)})
  : Tot (ceq (sindex s1 n) (sindex s2 n)) =
  if n > 0 then (
    sub_elam_index t (id_sub g) (n-1);
    assert (sindex s1 n == texp_weaken t (sindex (id_sub g) (n-1)));
    id_sub'_index 0 g (n-1);
    assert (sindex s1 n == texp_weaken t (TyVar (n-1)));
    assert (sindex s1 n == TyVar n)
  ) else (
    assert (sindex s1 0 == TyVar 0)
  );
  id_sub'_index 0 (t::g) n;
  Refl
  in sub_eq_index s1 s2 f

val id_sub_id: #g:ctx -> #t:ty -> e:texp g t ->
  Lemma (ensures subst (id_sub g) e == e)
  (decreases e)
let rec id_sub_id #g #t e = match e with
  | TyApp e1 e2 -> id_sub_id e1; id_sub_id e2
  | TyLam tlam e' -> id_sub_id e';
    assert (subst (id_sub g) e == TyLam tlam (subst 
      (sub_elam tlam (id_sub g)) e'));
      id_sub_elam g tlam
  | TyVar v -> id_sub'_index 0 g v

type step: g:ctx -> t:ty -> e:texp g t -> e':texp g t -> Type =
  | SAppL: #g:ctx ->
           #t1:ty ->
           #t2:ty ->
           #e1:texp g (TArr t1 t2) ->
           #e1':texp g (TArr t1 t2) ->
           $e2:texp g t1 ->
           $hst:step g (TArr t1 t2) e1 e1' ->
            step g t2 (TyApp e1 e2) (TyApp e1' e2)
  | SAppR: #g:ctx ->
           #t1:ty ->
           #t2:ty ->
           $e1:texp g (TArr t1 t2) ->
           #e2:texp g t1 ->
           #e2':texp g t1 ->
           $hst:step g t1 e2 e2' ->
             step g t2 (TyApp e1 e2) (TyApp e1 e2')
  | SLam: #g:ctx ->
           tlam:ty ->
          #t:ty ->
          #e:texp (tlam::g) t ->
          #e':texp (tlam::g) t ->
          $hst:step (tlam::g) t e e' ->
            step g (TArr tlam t) (TyLam tlam e) (TyLam tlam e') 
  | SBeta: #g:ctx ->
            tlam:ty ->
           #t:ty ->
           $e1:texp (tlam::g) t ->
           $e2:texp g tlam ->
             step g t (TyApp (TyLam tlam e1) e2)
               (subst (sub_beta e2) e1)

  (*
  // Lemma 2.4
val anti_renaming_ty: #g':ctx -> #g:ctx -> r:sub g' g {renaming r} 
  -> #t:ty -> e:texp g' t -> Tot (texp g t)
  (decreases e)
let rec anti_renaming_ty #g' #g r #t e = match e with
  | TyApp e1 e2 -> TyApp (anti_renaming_ty r e1) (anti_renaming_ty r e2)
  | TyLam tlam e' -> sub_elam_renaming tlam r;
    TyLam tlam (anti_renaming_ty (sub_elam tlam r) e')
  | TyVar x -> 
          TyVar (Some?.v (sfind_index r e))
  *)

val texp_weaken_exchange_var: g:ctx -> t1:ty -> t2:ty
  -> v:var {v < length g} -> n:nat {n <= length g} -> m:nat {m <= n} ->
  Lemma (ensures texp_weaken_at (n+1) t1 (texp_weaken_at m t2 (TyVar #g v))
    == texp_weaken_at m t2 (texp_weaken_at n t1 (TyVar #g v)))
let texp_weaken_exchange_var g t1 t2 v n m = 
  if v >= n then (
    insert_index g t1 n (v+1);
    assert (texp_weaken_at n t1 (TyVar #g v) 
      == TyVar #(insertAt g t1 n) (v+1));
    assert (v+1+1 == v+2);
    insert_index (insertAt g t1 n) t2 m (v+2);
    assert (texp_weaken_at m t2 (TyVar #(insertAt g t1 n) (v+1)) 
      == TyVar (v+2));

    insert_index g t2 m (v+1);
    assert (texp_weaken_at m t2 (TyVar #g v) 
      == TyVar #(insertAt g t2 m) (v+1));
    insert_index (insertAt g t2 m) t1 (n+1) (v+2);
    assert (texp_weaken_at (n+1) t1 (TyVar #(insertAt g t2 m) (v+1))
      == TyVar (v+2))
  ) else if v >= m then (
    assert (v < n);
    insert_index g t1 n v;
    assert (texp_weaken_at n t1 (TyVar #g v) == TyVar #(insertAt g t1 n) v);
    insert_index (insertAt g t1 n) t2 m (v+1);
    assert (texp_weaken_at m t2 (TyVar #(insertAt g t1 n) v) ==
      TyVar (v+1));

    insert_index g t2 m v;
    assert (texp_weaken_at m t2 (TyVar #g v)
      == TyVar #(insertAt g t2 m) (v+1));
    insert_index (insertAt g t2 m) t1 (n+1) (v+1);
    assert (texp_weaken_at (n+1) t1 (TyVar #(insertAt g t2 m) (v+1))
      == TyVar #(insertAt (insertAt g t2 m) t1 (n+1)) (v+1))
  ) else (
    assert (v < n);
    assert (v < m);
    insert_index g t1 n v;
    assert (texp_weaken_at n t1 (TyVar #g v) == TyVar #(insertAt g t1 n) v);
    insert_index (insertAt g t1 n) t2 m v;
    assert (texp_weaken_at m t2 (TyVar #(insertAt g t1 n) v) ==
      TyVar #(insertAt (insertAt g t1 n) t2 m) v);
    
    insert_index g t2 m v;
    assert (texp_weaken_at m t2 (TyVar #g v) == TyVar #(insertAt g t2 m) v);
    insert_index (insertAt g t2 m) t1 (n+1) v;
    assert (texp_weaken_at (n+1) t1 (TyVar #(insertAt g t2 m) v)
      == TyVar #(insertAt (insertAt g t2 m) t1 (n+1)) v)
  )

val texp_weaken_exchange: #g:ctx -> #t:ty -> t1:ty -> t2:ty -> e:texp g t
  -> n:nat {n <= length g} -> m:nat {m <= n} -> 
  Lemma (ensures texp_weaken_at (n+1) t1 (texp_weaken_at m t2 e) == 
    texp_weaken_at m t2 (texp_weaken_at n t1 e))
  (decreases e)
let rec texp_weaken_exchange #g #t t1 t2 e n m = match e with
  | TyApp e1 e2 -> texp_weaken_exchange t1 t2 e1 n m;
    texp_weaken_exchange t1 t2 e2 n m
  | TyLam tlam e' -> 
    assert (texp_weaken_at (n+1) t1 (texp_weaken_at m t2 e) ==
      TyLam tlam (texp_weaken_at (n+2) t1 (texp_weaken_at (m+1) t2 e')));
    assert (texp_weaken_at m t2 (texp_weaken_at n t1 e) ==
      TyLam tlam (texp_weaken_at (m+1) t2 (texp_weaken_at (n+1) t1 e')));
    texp_weaken_exchange t1 t2 e' (n+1) (m+1)
  | TyVar v -> texp_weaken_exchange_var g t1 t2 v n m

val texp_weaken_exchange_level: #g:ctx -> #t:ty -> e:texp g t -> t':ty
  -> ts:ctx ->
  Lemma (let l = length ts in
    texp_weaken_at l t' (texp_weaken_level ts e) ==
    texp_weaken_level ts (texp_weaken t' e))
let rec texp_weaken_exchange_level #g #t e t' ts = match ts with
  | [] -> ()
  | hd::tl -> texp_weaken_exchange_level e t' tl;
    assert (texp_weaken_at (length tl) t' (texp_weaken_level tl e) ==
      texp_weaken_level tl (texp_weaken t' e));
    assert (texp_weaken_level ts (texp_weaken t' e) ==
      texp_weaken hd (texp_weaken_level tl (texp_weaken t' e)));
    assert (texp_weaken_level ts (texp_weaken t' e) ==
      texp_weaken hd (texp_weaken_at (length tl) t' 
        (texp_weaken_level tl e)));
    texp_weaken_exchange t' hd (texp_weaken_level tl e) (length tl) 0

val level_sub_base_var: #g':ctx -> #g:ctx -> s:sub g' g -> t':ty 
  -> v:var {v < length g} -> Lemma (ensures texp_weaken t' (subst s (TyVar v))
    == subst (sub_elam t' s) (texp_weaken t' (TyVar v)))
let level_sub_base_var #g' #g s t' v = 
  assert (subst s (TyVar v) == sindex s v);
  assert (texp_weaken t' (TyVar #g v) == TyVar (v+1));
  sub_elam_index t' s v;
  assert (subst (sub_elam t' s) (TyVar (v+1)) == texp_weaken t'
    (sindex s v))

val level_sub_base'_var: #g':ctx -> #g:ctx -> g2:ctx -> s:sub g' g -> t':ty
  -> v:var {v < length g2 + length g} -> 
    Lemma (ensures texp_weaken_at (length g2) t' 
    ((subst (sub_elam_level g2 s)) (TyVar #(g2@g) v)) ==
    subst (sub_elam_level g2 (sub_elam t' s))
    (texp_weaken_at (length g2) t' (TyVar #(g2@g) v)))
let level_sub_base'_var #g' #g g2 s t' v =
  if v >= length g2 then (
    sub_elam_level_sub g2 s v;
    assert (subst (sub_elam_level g2 s) (TyVar #(g2@g) v) ==
      texp_weaken_level g2 (sindex s (v - length g2)));

    assert (texp_weaken_at (length g2) t' (TyVar #(g2@g) v) 
      == TyVar (v+1));
    sub_elam_level_sub g2 (sub_elam t' s) (v+1);
    assert (subst (sub_elam_level g2 (sub_elam t' s))
      (TyVar (v+1)) == texp_weaken_level g2 (sindex (sub_elam t' s)
	(v+1 -length g2)));
    assert (v+1 -length g2 == v -length g2 +1);
    sub_elam_index t' s (v -length g2);
    assert (sindex (sub_elam t' s) (v +1 -length g2) 
      == texp_weaken t' (sindex s (v-length g2)));
    texp_weaken_exchange_level (sindex s (v-length g2)) t' g2
  ) else (
    assert (v < length g2);
    sub_elam_level_id g2 (sub_elam t' s) v;
    sub_elam_level_id g2 s v
  )

val level_sub_base': #g':ctx -> #g:ctx -> g2:ctx -> s:sub g' g -> t':ty 
  -> #t:ty -> e:texp (g2@g) t -> Lemma (ensures texp_weaken_at (length g2) t' 
    (subst (sub_elam_level g2 s) e) == 
      subst (sub_elam_level g2 (sub_elam t' s))
      (texp_weaken_at (length g2) t' e))
  (decreases e)
let rec level_sub_base' #g' #g g2 s t' #t e = match e with
  | TyApp e1 e2 -> 
    level_sub_base' g2 s t' e1;
    level_sub_base' g2 s t' e2
  | TyLam tlam e' -> level_sub_base' (tlam::g2) s t' e'
  | TyVar x -> level_sub_base'_var g2 s t' x

irreducible val level_sub_base: #g':ctx -> #g:ctx -> s:sub g' g -> t':ty -> #t:ty
  -> e:texp g t -> Lemma (ensures subst (sub_elam t' s) (texp_weaken t' e)
    == texp_weaken t' (subst s e))
let level_sub_base #g' #g s t' #t e = 
    level_sub_base' [] s t' e

irreducible val level_sub: #g':ctx -> #g:ctx -> s:sub g' g -> g2:ctx -> #t:ty
  -> e:texp g t -> Lemma (ensures (subst (sub_elam_level g2 s) 
    (texp_weaken_level g2 e) == texp_weaken_level g2 (subst s e)))
  (decreases g2)
let rec level_sub #g' #g s g2 #t e = match g2 with
  | [] -> ()
  | hd::tl -> level_sub s tl e;
          assert (subst (sub_elam_level tl s) (texp_weaken_level tl e)
            == texp_weaken_level tl (subst s e));
          level_sub_base (sub_elam_level tl s) hd (texp_weaken_level tl e)

val sub_app: #g'':ctx -> #g':ctx -> #g:ctx -> s1:sub g'' g'
  -> s2:sub g' g -> Tot (sub g'' g)
  (decreases s2)
let rec sub_app #g'' #g' #g s1 s2 = match s2 with
  | STNil g' -> STNil g''
  | STCons e hst -> STCons (subst s1 e) (sub_app s1 hst)

val sub_app_index: #g'':ctx -> #g':ctx -> #g:ctx -> s1:sub g'' g'
  -> s2:sub g' g -> n:nat {n < length g} ->
  Lemma (sindex (sub_app s1 s2) n == subst s1 (sindex s2 n))
let rec sub_app_index #g'' #g' #g s1 s2 n = match s2 with
  | STCons e s2' -> if n = 0 then () else sub_app_index s1 s2' (n-1)

val sub_elam_app: #g'':ctx -> #g':ctx -> #g:ctx -> s1:sub g'' g'
  -> s2:sub g' g -> t:ty ->
  Lemma (sub_elam t (sub_app s1 s2) == sub_app (sub_elam t s1)
    (sub_elam t s2))
let sub_elam_app #g'' #g' #g s1 s2 t =
  let f (n:nat {n < length (t::g)})
  : Tot (ceq (sindex (sub_elam t (sub_app s1 s2)) n)
    (sindex (sub_app (sub_elam t s1) (sub_elam t s2)) n)) = 
    if n = 0 then (
      assert (sindex (sub_elam t (sub_app s1 s2)) 0 == TyVar 0);
      sub_app_index (sub_elam t s1) (sub_elam t s2) 0;
      assert (sindex (sub_elam t s2) 0 == TyVar 0);
      assert (sindex (sub_elam t s1) 0 == TyVar 0);
      Refl
    ) else (
      sub_elam_index t (sub_app s1 s2) (n-1);
      sub_app_index s1 s2 (n-1);
      assert (sindex (sub_elam t (sub_app s1 s2)) n ==
	texp_weaken t (subst s1 (sindex s2 (n-1))));
    
      sub_app_index (sub_elam t s1) (sub_elam t s2) n;
      sub_elam_index t s2 (n-1);
      level_sub s1 [t] (sindex s2 (n-1));
      Refl
    )
  in sub_eq_index (sub_elam t (sub_app s1 s2))
    (sub_app (sub_elam t s1) (sub_elam t s2)) f

val subst_subst_app: #g'':ctx -> #g':ctx -> #g:ctx
  -> s1:sub g'' g' -> s2:sub g' g -> #t:ty -> e:texp g t ->
  Lemma (ensures subst (sub_app s1 s2) e == subst s1 (subst s2 e))
  (decreases e)
let rec subst_subst_app #g'' #g' #g s1 s2 #t e = match e with
  | TyApp e1 e2 -> subst_subst_app s1 s2 e1;
    subst_subst_app s1 s2 e2
  | TyVar v -> assert (subst s2 e == sindex s2 v);
    sub_app_index s1 s2 v
  | TyLam tlam e' -> assert (subst s1 (subst s2 e) ==
    TyLam tlam (subst (sub_elam tlam s1) (subst (sub_elam tlam s2) e')));
    assert (subst (sub_app s1 s2) e == TyLam tlam (subst 
    (sub_elam tlam (sub_app s1 s2)) e'));
    sub_elam_app s1 s2 tlam;
    subst_subst_app (sub_elam tlam s1) (sub_elam tlam s2) e'

val sub_app_renaming: #g'':ctx -> #g':ctx -> #g:ctx
  -> r1:sub g'' g' -> r2:sub g' g ->
  Lemma (requires renaming r1 /\ renaming r2)
  (ensures renaming (sub_app r1 r2))
let rec sub_app_renaming #g'' #g' #g r1 r2 = match r2 with
  | STNil g' -> ()
  | STCons (TyVar v) hst -> sub_app_renaming r1 hst;
    sindex_renaming r1 v;
    assert (TyVar? (subst r1 (TyVar v)))

val sub_beta_weaken_index': #g:ctx -> #t:ty -> #tlam:ty -> g2:ctx 
  -> e1:texp (g2@g) t -> e2:texp g tlam ->
  Lemma (ensures e1 == subst (sub_beta_level g2 e2)
    (texp_weaken_at (length g2) tlam e1))
  (decreases e1)
let rec sub_beta_weaken_index' #g #t #tlam g2 e1 e2 = match e1 with
  | TyLam t'lam e1' -> sub_beta_weaken_index' (t'lam::g2) e1' e2
  | TyApp e11 e12 -> sub_beta_weaken_index' g2 e11 e2;
    sub_beta_weaken_index' g2 e12 e2
  | TyVar v -> if v < length g2 then (
          assert (texp_weaken_at (length g2) tlam e1 == TyVar v);
          sub_elam_level_id g2 (sub_beta e2) v
    ) else (
      assert (texp_weaken_at (length g2) tlam e1 
        == TyVar (v+1));
      sub_elam_level_sub g2 (sub_beta e2) (v+1);
      sub_beta_index e2 (v+1 - length g2);
      assert (index g (v - length g2) == index (g2@tlam::g) (v+1));
      assert (subst (sub_beta_level g2 e2) (TyVar (v+1)) ==
        texp_weaken_level g2 (TyVar #g (v-length g2)));
      texp_weaken_level_var g (v-length g2) g2;
      assert (texp_weaken_level g2 (TyVar #g (v-length g2))
        == TyVar (v-length g2 + length g2));
      nat_inv_elim v (length g2);
      assert (TyVar #(g2@g) (v-length g2 + length g2)
        == TyVar v)
    )

val sub_beta_weaken_index: #g:ctx -> #t:ty -> #tlam:ty -> e1:texp g t
  -> e2:texp g tlam ->
  Lemma (ensures e1 == subst (sub_beta e2) (texp_weaken tlam e1))
  (decreases e1)
let rec sub_beta_weaken_index #g #t #tlam e1 e2 =
  sub_beta_weaken_index' [] e1 e2

val sub_beta_elam2': #g':ctx -> #g:ctx -> tlam:ty
  -> e0:texp g' tlam -> s:sub g' g ->
  Lemma (sub_app (sub_beta e0) (sub_elam tlam s) == STCons e0 s)
let sub_beta_elam2' #g' #g tlam e0 s = 
  let f (n:nat {n < length (tlam::g)})
    :Tot (ceq (sindex (sub_app (sub_beta e0) (sub_elam tlam s)) n)
    (sindex (STCons e0 s) n)) = if n = 0 then (
      assert (sindex (sub_elam tlam s) 0 == TyVar 0);
      assert (sindex (sub_app (sub_beta e0) (sub_elam tlam s)) 0 
	== e0);
      assert (sindex (STCons e0 s) 0 == e0);
      Refl
    ) else (
      sub_app_index (sub_beta e0) (sub_elam tlam s) n;
      assert (sindex (sub_app (sub_beta e0) (sub_elam tlam s)) n
	== subst (sub_beta e0) (sindex (sub_elam tlam s) n));
      sub_elam_index tlam s (n-1);
      assert (sindex (sub_elam tlam s) n == texp_weaken tlam 
	(sindex s (n-1)));
      sub_beta_weaken_index (sindex s (n-1)) e0;
      assert (sindex (STCons e0 s) n == sindex s (n-1));
      Refl
    )
  in sub_eq_index (sub_app (sub_beta e0) (sub_elam tlam s))
    (STCons e0 s) f

val sub_beta_elam2: #g':ctx -> #g:ctx -> tlam:ty -> #t:ty
  -> e:texp (tlam::g) t -> e0:texp g' tlam -> s:sub g' g ->
  Lemma (subst (sub_beta e0) (subst (sub_elam tlam s) e)
    == subst (STCons e0 s) e)
let sub_beta_elam2 #g' #g tlam #t e e0 s = 
  subst_subst_app (sub_beta e0) (sub_elam tlam s) e;
  sub_beta_elam2' tlam e0 s

val sub_sub_beta_help: #g':ctx -> #g:ctx -> s:sub g' g -> #t:ty -> tlam:ty
  -> g2:ctx -> e2:texp g tlam -> e1:texp (g2@tlam::g) t -> 
  Lemma (ensures (subst (sub_elam_level g2 s) (subst (sub_beta_level g2 e2) e1))
    == subst (sub_beta_level g2 (subst s e2))
    (subst (sub_elam_level g2 (sub_elam tlam s)) e1))
  (decreases e1)
let rec sub_sub_beta_help #g' #g s #t tlam g2 e2 e1 = match e1 with
  | TyApp e1' e2' -> sub_sub_beta_help s tlam g2 e2 e1';
          sub_sub_beta_help s tlam g2 e2 e2'
  | TyLam t' e' -> sub_sub_beta_help s tlam (t'::g2) e2 e'
  | TyVar x -> if x < length g2 then (
        index_append g2 (tlam::g) x;
        index_append g2 g x;
        sub_elam_level_id g2 (sub_beta e2) x;
        sub_elam_level_id g2 s x;
        sub_elam_level_id g2 (sub_elam tlam s) x;
        sub_elam_level_id g2 (sub_beta (subst s e2)) x
    ) else if x = length g2 then (
        index_append g2 (tlam::g) x;
      sub_elam_level_sub g2 (sub_beta e2) x;
      assert (sindex (sub_beta_level g2 e2) x 
        == texp_weaken_level g2 e2);
      sub_elam_level_sub g2 (sub_elam tlam s) x;
      assert (sindex (sub_elam_level g2 (sub_elam tlam s)) x
        == texp_weaken_level g2 (TyVar 0));
      level_sub s g2 e2;
      level_sub (sub_beta (subst s e2)) g2 (TyVar 0)
    ) else (
      assert (x > length g2);
      assert (x < length g2 + length (tlam::g));
      index_append g2 (tlam::g) x;
      sub_elam_level_sub g2 (sub_elam tlam s) x;
      sub_elam_level_sub g2 (sub_beta e2) x;
      sub_beta_index e2 (x -length g2);
      sub_elam_index tlam s (x - length g2 -1);
      let eq1 = sindex (sub_elam tlam s) (x - length g2) in
      let eq1' = texp_weaken tlam (sindex s (x - length g2 -1)) in
      level_sub (sub_beta (subst s e2)) g2 eq1;
      let eq2 = TyVar #g (x - length g2 -1) in
      level_sub s g2 eq2;
      sub_beta_weaken_index (sindex s (x - length g2 -1)) (subst s e2)
    )

irreducible val sub_sub_beta: #g':ctx -> #g:ctx -> s:sub g' g -> #t:ty -> tlam:ty 
  -> e2:texp g tlam -> e1:texp (tlam::g) t -> 
  Lemma (ensures (subst s (subst (sub_beta e2) e1) 
      == subst (sub_beta (subst s e2)) (subst (sub_elam tlam s) e1)))
let sub_sub_beta #g' #g s #t tlam e2 e1 = 
  sub_sub_beta_help s tlam [] e2 e1

// Lemma 2.8
val step_sub: #g':ctx -> #g:ctx -> #t:ty -> #e1:texp g t -> #e2:texp g t ->
  s:sub g' g -> st:step g t e1 e2 -> Tot (step g' t (subst s e1) (subst s e2))
  (decreases st)
let rec step_sub #g' #g #t #e1 #e2 s st = match st with
  | SAppL e2 hst -> let hst' = step_sub s hst in
    SAppL (subst s e2) hst'
  | SAppR e1 hst -> let hst' = step_sub s hst in
    SAppR (subst s e1) hst'
  | SLam tlam hst -> let hst' = step_sub (sub_elam tlam s) hst in
    SLam tlam hst'
  | SBeta tlam e1' e2' -> let e1'' = subst (sub_elam tlam s) e1' in
    let e2'' = subst s e2' in
    sub_sub_beta s tlam e2' e1';
    SBeta tlam e1'' e2''

val weaken_sub: g:ctx -> t:ty -> Tot (sub (t::g) g)
let weaken_sub g t = sub_weaken t (id_sub g)

val weaken_sub_renaming: g:ctx -> t:ty ->
  Lemma (renaming (weaken_sub g t))
let weaken_sub_renaming g t = id_sub_renaming g;
  sub_weaken_renaming t (id_sub g)

val weaken_subst'_var: g:ctx -> g2:ctx 
  -> v:var {v < length g2 + length g} -> t':ty ->
  Lemma (ensures texp_weaken_at (length g2) t' (TyVar v) ==
  subst (sub_elam_level g2 (weaken_sub g t')) (TyVar v))
let weaken_subst'_var g g2 v t' = if v < length g2 then (
    assert (texp_weaken_at (length g2) t' (TyVar #(g2@g) v) 
      == TyVar #(insertAt (g2@g) t' (length g2)) v);
      sub_elam_level_id g2 (weaken_sub g t') v
  ) else (
    assert (texp_weaken_at (length g2) t' (TyVar #(g2@g) v)
      == TyVar #(insertAt (g2@g) t' (length g2)) (v+1));
    sub_elam_level_sub g2 (weaken_sub g t') v;
    assert (subst (sub_elam_level g2 (weaken_sub g t')) (TyVar v) 
      == texp_weaken_level g2 (sindex (weaken_sub g t') (v - length g2)));
    assert (sindex (weaken_sub g t') (v - length g2) ==
      sindex (sub_weaken t' (id_sub g)) (v - length g2));
    sub_weaken_index t' (id_sub g) (v - length g2);
    assert (sindex (sub_weaken t' (id_sub g)) (v - length g2)
      == texp_weaken t' (sindex (id_sub g) (v - length g2)));
    id_sub'_index 0 g (v - length g2);
    assert (sindex (id_sub g) (v - length g2) == TyVar #g (v - length g2));
    assert (texp_weaken t' (TyVar #g (v - length g2)) ==
      TyVar (v - length g2 +1));
    texp_weaken_level_var (t'::g) (v - length g2 +1) g2;
    assert (texp_weaken_level g2 (TyVar #(t'::g) (v - length g2 +1))
      == TyVar #(g2@t'::g) (v - length g2 +1 + length g2));

    insert_append_cons g2 g t';
    assert (g2@t'::g == insertAt (g2@g) t' (length g2));
    nat_inv_elim (v+1) (length g2);
    assert (v - length g2 +1 + length g2 == v+1)
  )

val weaken_subst': g:ctx -> #t:ty -> g2:ctx -> e:texp (g2@g) t -> t':ty ->
  Lemma (ensures texp_weaken_at (length g2) t' e == 
    subst (sub_elam_level g2 (weaken_sub g t')) e)
  (decreases e)
let rec weaken_subst' g #t g2 e t' = match e with
  | TyApp e1 e2 -> weaken_subst' g g2 e1 t';
    weaken_subst' g g2 e2 t'
  | TyLam tlam e' -> weaken_subst' g (tlam::g2) e' t'
  | TyVar v -> weaken_subst'_var g g2 v t'

val weaken_subst: #g:ctx -> #t:ty -> e:texp g t -> t':ty -> 
  Lemma (ensures (texp_weaken t' e == subst (weaken_sub g t') e))
let weaken_subst #g #t e t' = weaken_subst' g [] e  t'
 
val exchange_sub': t1:ty -> t2:ty -> g:ctx -> 
  Tot (sub (t2::t1::g) (t1::t2::g))
let exchange_sub' t1 t2 g = 
  assert (index (t2::t1::g) 0 == t2);
  assert (index (t2::t1::g) 1 == t1);
  assert (drop 2 (t2::t1::g) == g);
  STCons (TyVar 1) (STCons (TyVar 0) (id_sub' 2 (t2::t1::g)))

val exchange_sub'_index: t1:ty -> t2:ty -> g:ctx
  -> i:nat {i < length (t1::t2::g) /\ i >= 2} ->
  Lemma (sindex (exchange_sub' t1 t2 g) i
    == sindex (id_sub' 2 (t2::t1::g)) (i-2))
let exchange_sub'_index t1 t2 g i = ()

val exchange_sub: g:ctx -> n:nat {n+1 < length g} ->
  Tot (sub (exchange_list n g) g)
let exchange_sub g n = let init = take n g in
  match drop n g with
  | t1::t2::tl -> take_drop_split n g;
    exchange_list_elems init t1 t2 tl;
    sub_elam_level init (exchange_sub' t1 t2 tl)

val exchange_subst_var: g:ctx -> v:var {v < length g} 
  -> n:nat {n+1 < length g} ->
  Lemma (ensures texp_exchange n (TyVar #g v) 
    == subst (exchange_sub g n) (TyVar #g v))
let exchange_subst_var g v n = let init = take n g in
  match drop n g with
  | t1::t2::tail -> take_drop_split n g;
  exchange_list_elems init t1 t2 tail;
  exchange_list_props n g;
  assert (g == init@t1::t2::tail);
  assert (exchange_list n g == init@t2::t1::tail);
  if v = n then (
    assert (texp_exchange n (TyVar #g v) 
      == TyVar #(exchange_list n g) (v+1));

    sub_elam_level_sub init (exchange_sub' t1 t2 tail) v;
    assert (subst (exchange_sub g n) (TyVar #g v) ==
      sindex (exchange_sub g n) v);
    assert (sindex (exchange_sub g n) v ==
      texp_weaken_level init (sindex (exchange_sub' t1 t2 tail)
	(v-(length init))));
    assert (v-(length init) == 0);
    assert (sindex (exchange_sub' t1 t2 tail) 0 == TyVar #(t2::t1::tail) 1);
    texp_weaken_level_var (t2::t1::tail) 1 init;
    assert (texp_weaken_level init (TyVar #(t2::t1::tail) 1) ==
      TyVar #(init@t2::t1::tail) (v+1))
  ) else if v = n + 1 then (
    assert (texp_exchange n (TyVar #g v) 
      == TyVar #(exchange_list n g) n);
    
    sub_elam_level_sub init (exchange_sub' t1 t2 tail) v;
    assert (subst (exchange_sub g n) (TyVar #g v) ==
      texp_weaken_level init (sindex (exchange_sub' t1 t2 tail) (v-n)));
    nat_plus_side v n 1;
    assert (v-n == 1);
    assert (sindex (exchange_sub' t1 t2 tail) 1 == TyVar #(t2::t1::tail) 0);
    texp_weaken_level_var (t2::t1::tail) 0 init;
    assert (texp_weaken_level init (TyVar #(t2::t1::tail) 0) ==
      TyVar #(init@t2::t1::tail) (0+length init));
    add_zero_l (length init);
    assert (0+length init == n)
  ) else if v < n then (
    assert (length init == n);
    sub_elam_level_id init (exchange_sub' t1 t2 tail) v;
    assert (subst (sub_elam_level init (exchange_sub' t1 t2 tail)) (TyVar v)
      == TyVar #(init@t2::t1::tail) v);

    assert (texp_exchange n (TyVar #g v) == TyVar #(exchange_list n g) v);
    assert (exchange_list n g == init@t2::t1::tail)
  ) else (
    sub_elam_level_sub init (exchange_sub' t1 t2 tail) v;
    assert (subst (sub_elam_level init (exchange_sub' t1 t2 tail)) (TyVar #g v)
      == texp_weaken_level init 
	(sindex (exchange_sub' t1 t2 tail) (v - length init)));
    assert (length init == n);
    assert (v - length init >= 2);
    exchange_sub'_index t1 t2 tail (v - length init);
    assert (sindex (exchange_sub' t1 t2 tail) (v - length init) ==
      sindex (id_sub' 2 (t2::t1::tail)) (v - length init -2));
    id_sub'_index 2 (t2::t1::tail) (v-length init -2);
    assert (sindex (id_sub' 2 (t2::t1::tail)) (v - length init - 2)
      == TyVar #(t2::t1::tail) (v - length init -2 +2));
    nat_inv_elim (v-length init) 2;
    assert (v - length init -2 +2 == v - length init);
    texp_weaken_level_var (t2::t1::tail) (v - length init) init;
    assert (texp_weaken_level init (TyVar #(t2::t1::tail) (v-length init))
      == TyVar #(init@t2::t1::tail) (v-length init + length init));
    nat_inv_elim v (length init)
  )

val exchange_subst: #g:ctx -> #t:ty -> e:texp g t -> n:nat {n+1 < length g}
  -> Lemma (ensures (texp_exchange n e == subst (exchange_sub g n) e))
  (decreases e)
let rec exchange_subst #g #t e n = match e with
  | TyApp e1 e2 -> exchange_subst e1 n;
    exchange_subst e2 n
  | TyLam tlam e' -> exchange_subst e' (n+1)
  | TyVar v -> exchange_subst_var g v n

// Lemma 2.5
val step_weaken: #g:ctx -> #t:ty -> #e1:texp g t -> #e2:texp g t ->
  hst:step g t e1 e2  -> t':ty -> 
  Tot (step (t'::g) t (texp_weaken t' e1) (texp_weaken t' e2))
let step_weaken #g #t #e1 #e2 hst t' = 
  weaken_subst e1 t';
  weaken_subst e2 t';
  step_sub (weaken_sub g t') hst

val step_exchange: #g:ctx -> #t:ty -> #e1:texp g t -> #e2:texp g t ->
  hst:step g t e1 e2 -> n:nat {n+1 < length g} ->
  Tot (step (exchange_list n g) t (texp_exchange n e1) (texp_exchange n e2))
let step_exchange #g #t #e1 #e2 hst n =
  exchange_subst e1 n;
  exchange_subst e2 n;
  step_sub (exchange_sub g n) hst

val step_weaken_level: #g:ctx -> #t:ty -> #e1:texp g t -> #e2:texp g t
  -> hst:step g t e1 e2 -> g2:ctx ->
  Tot (step (g2@g) t (texp_weaken_level g2 e1) (texp_weaken_level g2 e2))
  (decreases g2)
let rec step_weaken_level #g #t #e1 #e2 hst g2 = match g2 with
  | [] -> hst
  | hd::tl -> let hst' = step_weaken_level hst tl in
    step_weaken hst' hd

val texp_height: #g:ctx -> #t:ty -> e:texp g t -> Tot nat
  (decreases e)
let rec texp_height #g #t e = match e with
  | TyVar x -> 0
  | TyApp e1 e2 -> 1+max (texp_height e1) (texp_height e2)
  | TyLam tlam e' -> 1+texp_height e'

val texp_exchange_height: #g:ctx -> n:nat {n+1 < length g} -> #t:ty
  -> e:texp g t -> 
  Lemma (ensures (texp_height e == texp_height (texp_exchange n e)))
  (decreases e)
let rec texp_exchange_height #g n #t e = match e with
  | TyApp e1 e2 -> texp_exchange_height n e1; texp_exchange_height n e2
  | TyVar x -> ()
  | TyLam tlam e' -> texp_exchange_height (n+1) e'

val step_height: #g:ctx -> #t:ty -> #e1:texp g t -> #e2:texp g t 
  -> hst:step g t e1 e2 -> Tot nat
  (decreases hst)
let rec step_height #g #t #e1 #e2 hst = match hst with
  | SAppL e2' hst' -> 1+step_height hst'
  | SAppR e1' hst' -> 1+step_height hst'
  | SLam tlam hst' -> 1+step_height hst'
  | SBeta tlam e1' e2' -> 0

val step_sub_pres_height: #g':ctx -> #g:ctx -> #t:ty -> #e1:texp g t 
  -> #e2:texp g t -> s:sub g' g -> st:step g t e1 e2 -> 
  Lemma (ensures (step_height st == step_height (step_sub s st)))
  (decreases st)
let rec step_sub_pres_height #g' #g #t #e1 #e2 s st = match st with
  | SAppL e2' hst' -> step_sub_pres_height s hst'
  | SAppR e1' hst' -> step_sub_pres_height s hst'
  | SLam tlam hst' -> step_sub_pres_height (sub_elam tlam s) hst'
  | SBeta tlam e1' e2' -> ()
  
val step_exchange_pres_height: #g:ctx -> #t:ty -> #e1:texp g t -> #e2:texp g t ->
  hst:step g t e1 e2 -> n:nat {n+1 < length g} ->
  Lemma (step_height hst == step_height (step_exchange hst n))
let step_exchange_pres_height #g #t #e1 #e2 hst n = 
  step_sub_pres_height (exchange_sub g n) hst

val step_beta_sub': #g:ctx -> g2:ctx -> #t':ty -> #t:ty 
  -> #e1:texp (g2@t'::g) t -> #e2:texp (g2@t'::g) t
  -> hst:step (g2@t'::g) t e1 e2 -> e':texp g t' ->
  Tot (step (g2@g) t (subst (sub_beta_level g2 e') e1)
    (subst (sub_beta_level g2 e') e2))
  (decreases (step_height hst))
let rec step_beta_sub' #g g2 #t' #t #e1 #e2 hst e' = match hst with
  | SAppL e2' hst1 -> let e2'' = subst (sub_beta_level g2 e') e2' in
    let hst1' = step_beta_sub' g2 hst1 e' in
    SAppL e2'' hst1'
  | SAppR e1' hst2 -> let e1'' = subst (sub_beta_level g2 e') e1' in
    let hst2' = step_beta_sub' g2 hst2 e' in
    SAppR e1'' hst2'
  | SLam tlam hst' -> let hst'' = step_beta_sub' (tlam::g2) hst' e' in
    SLam tlam hst''
  | SBeta tlam e1' e2'  -> let e2'' = subst (sub_beta_level g2 e') e2' in
    let e1'' = subst (sub_beta_level (tlam::g2) e') e1' in
    assert (subst (sub_beta_level g2 e') e1 == TyApp (TyLam tlam e1'') e2'');
    sub_sub_beta (sub_beta_level g2 e') tlam e2' e1';
    assert (subst (sub_beta_level g2 e') (subst (sub_beta e2') e1')
      == subst (sub_beta e2'') e1'');
    SBeta tlam e1'' e2''

// Lemma 2.6
val step_beta_sub: #g:ctx -> #t':ty -> #t:ty -> #e1:texp (t'::g) t
  -> #e2:texp (t'::g) t -> hst:step (t'::g) t e1 e2 -> e':texp g t'
  -> Tot (step g t (subst (sub_beta e') e1) (subst (sub_beta e') e2))
let step_beta_sub #g #t' #t #e1 #e2 hst e' = 
  step_beta_sub' [] hst e'

type multi_step: g:ctx -> t:ty -> e1:texp g t -> e2:texp g t -> Type =
  | MRefl: g:ctx ->
           t:ty ->
           e:texp g t ->
           multi_step g t e e
  | MSingle: #g:ctx ->
             #t:ty ->
             #e1:texp g t ->
             #e2:texp g t ->
             #e3:texp g t ->
             $hst:step g t e1 e2 ->
             $mst:multi_step g t e2 e3 ->
             multi_step g t e1 e3

// Lemma 2.7
val multi_step_plus: #g:ctx -> #t:ty -> #e1:texp g t -> #e2:texp g t
  -> #e3:texp g t -> mst1:multi_step g t e1 e2 -> mst2:multi_step g t e2 e3 ->
  Tot (multi_step g t e1 e3)
  (decreases mst1)
let rec multi_step_plus #g #t #e1 #e2 #e3 mst1 mst2 = match mst1 with
  | MRefl g t e -> mst2
  | MSingle hst mst1' -> let mst = multi_step_plus mst1' mst2 in
    MSingle hst mst

val multi_step_appl: #g:ctx -> #t1:ty -> #t2:ty -> #e1:texp g (TArr t1 t2)
  -> #e1':texp g (TArr t1 t2) -> e2:texp g t1 
  -> hmst:multi_step g (TArr t1 t2) e1 e1' ->
  Tot (multi_step g t2 (TyApp e1 e2) (TyApp e1' e2))
  (decreases hmst)
let rec multi_step_appl #g #t1 #t2 #e1 #e1' e2 hmst = match hmst with
  | MRefl g tap e1 -> MRefl g t2 (TyApp e1 e2)
  | MSingle hst1 mst1 -> let mst = multi_step_appl e2 mst1 in
    let hst = SAppL e2 hst1 in
    MSingle hst mst

val multi_step_appr: #g:ctx -> #t1:ty -> #t2:ty -> e1:texp g (TArr t1 t2)
  -> #e2:texp g t1 -> #e2':texp g t1 -> hmst:multi_step g t1 e2 e2' ->
  Tot (multi_step g t2 (TyApp e1 e2) (TyApp e1 e2'))
  (decreases hmst)
let rec multi_step_appr #g #t1 #t2 e1 #e2 #e2' hmst = match hmst with
  | MRefl g tap e2 -> MRefl g t2 (TyApp e1 e2)
  | MSingle hst2 mst2 -> let mst = multi_step_appr e1 mst2 in
    let hst = SAppR e1 hst2 in
    MSingle hst mst

val multi_step_app: #g:ctx -> #t1:ty -> #t2:ty -> #e1:texp g (TArr t1 t2)
  -> #e1':texp g (TArr t1 t2) -> #e2:texp g t1 -> #e2':texp g t1
  -> mst1:multi_step g (TArr t1 t2) e1 e1' -> mst2:multi_step g t1 e2 e2' ->
  Tot (multi_step g t2 (TyApp e1 e2) (TyApp e1' e2'))
  (decreases mst1)
let rec multi_step_app #g #t1 #t2 #e1 #e1' #e2 #e2' mst1 mst2 =
  match mst1 with
  | MRefl g tap e1 -> multi_step_appr e1 mst2
  | MSingle #g #tap #e1 #em1 #e1' hst1 mst1' -> 
    let mst:multi_step g t2 (TyApp em1 e2) (TyApp e1' e2')
      = multi_step_app mst1' mst2 in
    let hst = SAppL e2 hst1 in
    let hmst:multi_step g t2 (TyApp e1 e2) (TyApp em1 e2)
      = MSingle hst (MRefl g t2 (TyApp em1 e2)) in
    multi_step_plus hmst mst
  
val multi_step_lam: #g:ctx -> tlam:ty -> #t:ty -> #e:texp (tlam::g) t
  -> #e':texp (tlam::g) t -> mst:multi_step (tlam::g) t e e' ->
  Tot (multi_step g (TArr tlam t) (TyLam tlam e) (TyLam tlam e'))
  (decreases mst)
let rec multi_step_lam #g tlam #t #e #e' mst = match mst with
  | MRefl tg t e  -> MRefl g (TArr tlam t) (TyLam tlam e)
  | MSingle hst hmst -> let mst' = multi_step_lam tlam hmst in
    let hst' = SLam tlam hst in
    MSingle hst' mst'

val multi_step_beta'_var: #g:ctx -> tlam:ty -> g2:ctx
  -> v:var {v < length (g2@tlam::g)} -> #e2:texp g tlam
  -> #e2':texp g tlam -> hst:step g tlam e2 e2' ->
  Tot (multi_step (g2@g) (index (g2@tlam::g) v) 
    (subst (sub_beta_level g2 e2) (TyVar v))
    (subst (sub_beta_level g2 e2') (TyVar v)))
let multi_step_beta'_var #g tlam g2 v #e2 #e2' hst = 
  if v < length g2 then (
    sub_elam_level_id g2 (sub_beta e2) v;
    sub_elam_level_id g2 (sub_beta e2') v;
    MRefl (g2@g) (index (g2@tlam::g) v) (TyVar v)
  ) else if v = length g2 then (
    sub_elam_level_sub g2 (sub_beta e2) v;
    sub_elam_level_sub g2 (sub_beta e2') v;
    assert (subst (sub_beta_level g2 e2) (TyVar #(g2@tlam::g) v) ==
      texp_weaken_level g2 (sindex (sub_beta e2) (v - length g2)));
    assert (subst (sub_beta_level g2 e2') (TyVar #(g2@tlam::g) v) ==
      texp_weaken_level g2 (sindex (sub_beta e2') (v - length g2)));
    assert (v - length g2 == 0);
    assert (sindex (sub_beta e2) 0 == e2);
    assert (sindex (sub_beta e2') 0 == e2');
    let hst' = step_weaken_level hst g2 in
    index_append g2 (tlam::g) v;
    assert (index (g2@tlam::g) v == tlam);
    let e2'' = texp_weaken_level g2 e2' in
    MSingle hst' (MRefl (g2@g) tlam e2'')
  ) else (
    assert (v > length g2);
    sub_elam_level_sub g2 (sub_beta e2) v;
    sub_elam_level_sub g2 (sub_beta e2') v;
    assert (subst (sub_beta_level g2 e2) (TyVar #(g2@tlam::g) v) ==
      texp_weaken_level g2 (sindex (sub_beta e2) (v - length g2)));
    assert (subst (sub_beta_level g2 e2') (TyVar #(g2@tlam::g) v) ==
      texp_weaken_level g2 (sindex (sub_beta e2') (v - length g2)));
    assert (v - length g2 > 0);
    sub_beta_index e2 (v - length g2);
    sub_beta_index e2' (v - length g2);
    assert (sindex (sub_beta e2) (v-length g2) ==
      TyVar (v-length g2 -1));
    assert (sindex (sub_beta e2') (v-length g2) ==
      TyVar (v-length g2 -1));
    texp_weaken_level_var g (v-length g2-1) g2;
    assert (texp_weaken_level g2 (TyVar #g (v-length g2-1))
      == TyVar (v-length g2-1+length g2));
    nat_inv_elim (v-1) (length g2);
    assert (v-length g2-1+length g2 == v-1);
    MRefl (g2@g) (index (g2@tlam::g) v) (TyVar (v-1))
  )

val multi_step_beta': #g:ctx -> tlam:ty -> #t:ty -> g2:ctx
  -> e1:texp (g2@tlam::g) t -> #e2:texp g tlam -> #e2':texp g tlam
  -> hst:step g tlam e2 e2' ->
  Tot (multi_step (g2@g) t (subst (sub_beta_level g2 e2) e1)
    (subst (sub_beta_level g2 e2') e1))
  (decreases e1)
let rec multi_step_beta' #g tlam #t g2 e1 #e2 #e2' hst = match e1 with
  | TyApp e11 e12 -> let e11' = multi_step_beta' tlam g2 e11 hst in
    let e12' = multi_step_beta' tlam g2 e12 hst in
    multi_step_app e11' e12'
  | TyLam t'lam e' -> let e'' = multi_step_beta' tlam (t'lam::g2) e' hst in
    append_cons_l t'lam g2 g;
    multi_step_lam t'lam e''
  | TyVar v -> multi_step_beta'_var tlam g2 v hst

val multi_step_beta: #g:ctx -> tlam:ty -> #t:ty -> e1:texp (tlam::g) t
  -> #e2:texp g tlam -> #e2':texp g tlam -> hst:step g tlam e2 e2' ->
  Tot (multi_step g t (subst (sub_beta e2) e1) (subst (sub_beta e2') e1))
  (decreases (texp_height e1))
let multi_step_beta #g tlam #t e1 #e2 #e2' hst =
  multi_step_beta' tlam [] e1 hst

val multi_step_len: #g:ctx -> #t:ty -> #e:texp g t -> #e':texp g t
  -> mst:multi_step g t e e' -> Tot nat
  (decreases mst)
let rec multi_step_len #g #t #e #e' mst = match mst with
  | MRefl _ _ _ -> 0
  | MSingle _ hmst -> 1+ multi_step_len hmst

val multi_step_single_len: #g:ctx -> #t:ty -> #e:texp g t -> #e':texp g t
  -> mst:multi_step g t e e' -> Lemma (requires (MSingle? mst))
  (ensures (multi_step_len mst >= 1))
let multi_step_single_len #g #t #e #e' mst = ()

noeq type ssn: n:nat -> g:ctx -> t:ty -> e:texp g t -> Type =
  | Ssn: #g:ctx ->
         #t:ty ->
         #e:texp g t ->
         n:nat ->
         f:(e':texp g t ->
           hst:step g t e e' ->
           Tot (ssn n g t e')
           ) ->
          ssn (n+1) g t e

 // Lemma 2.9
val multi_step_sn: #g:ctx -> #t:ty -> #e:texp g t -> #e':texp g t
  -> #n:nat -> mst:multi_step g t e e' {multi_step_len mst <= n}
  -> hssn:ssn n g t e  ->
  Tot (ssn (abs (n-multi_step_len mst)) g t e') // does not work without abs
  (decreases mst)
let rec multi_step_sn #g #t #e #e' #n mst hssn =
  match mst with
  | MRefl g t e -> hssn
  | MSingle #g #t #e1 #e2 #e3 hst hmst -> (match hssn with
    | Ssn m f -> let hssn2 = f e2 hst in
      assert (e' == e3);
      assert (1+multi_step_len hmst == multi_step_len mst);
      assert (1+m == n);
      assert (m - multi_step_len hmst == n - multi_step_len mst);
      multi_step_sn hmst hssn2
    )

val sn_nat_weaken: #n:nat -> n':nat {n' >= n} -> #g:ctx -> #t:ty -> #e:texp g t
  -> hssn:ssn n g t e -> Tot (ssn n' g t e)
  (decreases n)
let rec sn_nat_weaken #n n' #g #t #e hssn = match hssn with
  | Ssn m f -> let f' = fun e' hst -> 
        sn_nat_weaken (n'-1) (f e' hst) in
    Ssn (n'-1) f'

val multi_step_sn2: #g:ctx -> #t:ty -> #e:texp g t -> #e':texp g t
  -> #n:nat -> mst:multi_step g t e e' -> hssn:ssn n g t e ->
  Tot (ssn n g t e')
  (decreases mst)
let rec multi_step_sn2 #g #t #e #e' #n mst hssn =
  match mst with
  | MRefl g t e -> hssn
  | MSingle #g #t #e1 #e2 #e3 hst hmst -> (match hssn with
    | Ssn m f -> let hssn2 = f e2 hst in
      let ssn' = multi_step_sn2 hmst hssn2 in
      sn_nat_weaken n ssn'
    )

val ssn_mst_size: #g:ctx -> #t:ty -> #e:texp g t -> #e':texp g t ->
  #n:nat -> hssn:ssn n g t e -> mst:multi_step g t e e' ->
  Lemma (ensures (multi_step_len mst <= n))
  (decreases mst)
let rec ssn_mst_size #g #t #e #e' #n hssn mst = match hssn with
  | Ssn m f -> (match mst with
    | MRefl g t e -> ()
    | MSingle #g #t #e #e0 #e' hst mst' ->
      let ssn' = f e0 hst in
      ssn_mst_size ssn' mst'
    )
