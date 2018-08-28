module Prelude

open FStar.Math.Lib
open FStar.List.Tot

val nth_index: n:nat -> l:list 'a{n < length l} ->
  Lemma (Some? (nth l n) /\ (index l n == Some?.v (nth l n)))
  [SMTPat (index l n)]
let rec nth_index n l = match l with
  | hd::tl -> if n = 0 then () else nth_index (n-1) tl

val nth_length: n:nat -> l:list 'a ->
  Lemma (requires (Some? (nth l n)))
    (ensures (length l > n))
let rec nth_length n l = match l with
  | hd::tl -> if n = 0 then () 
          else nth_length (n-1) tl

val index_mem: #a:eqtype -> l:list a -> n:nat {n < length l} -> 
  Lemma (mem (index l n) l)
let rec index_mem #a l n = match l with
  | [] -> ()
  | hd::tl -> if n = 0 then () else index_mem tl (n-1)

val index_map: f:('a -> Tot 'b) -> l:list 'a -> n:nat {n < length l} ->
  Lemma (index (map f l) n == f (index l n))
let rec index_map f l n = match l with
  | hd::tl -> if n = 0 then () else index_map f tl (n-1)

val nth_some: l1:list 'a -> l2:list 'b -> n:nat -> Lemma
    (requires (length l1 == length l2))
    (ensures (Some? (nth l1 n) <==> Some? (nth l2 n)))
let rec nth_some l1 l2 n = match l1,l2 with
  | [],[] -> ()
  | h1::t1, h2::t2 -> if n = 0 then () else nth_some t1 t2 (n-1)

val exchange_list: n:nat -> l:list 'a {n+1 < length l} ->
  Tot (list 'a)
let rec exchange_list n l = match l with
  | a1::a2::tl -> if n = 0 then a2::a1::tl 
                        else 
                        a1::(exchange_list (n-1) (a2::tl))

val exchange_list_elems: l1:list 'a -> e1:'a -> e2:'a -> l2:list 'a ->
  Lemma (length (l1@e1::e2::l2) == length l1 + 2 + length l2
    /\ exchange_list (length l1) (l1@e1::e2::l2) == l1@e2::e1::l2)
let rec exchange_list_elems l1 e1 e2 l2 = 
  assert (length (l1@e1::e2::l2) == length l1 + length (e1::e2::l2));
  assert (length (l1@e1::e2::l2) == length l1 + length l2 + 2);
  match l1 with
  | [] -> ()
  | hd::tl -> exchange_list_elems tl e1 e2 l2

val exchange_list_length: n:nat -> l:list 'a {n+1 < length l} ->
  Lemma (length (exchange_list n l) == length l)
  [SMTPat (exchange_list n l)]
let rec exchange_list_length n l = match l with
  | a1::a2::tl -> if n = 0 then ()
	       else exchange_list_length (n-1) (a2::tl)
 
val exchange_list_double: n:nat -> l:list 'a {n+1 < length l} ->
  Lemma (exchange_list n (exchange_list n l) == l)
  [SMTPat (exchange_list n (exchange_list n l))]
let rec exchange_list_double n l = match l with
  | a1::a2::tl -> if n = 0 then ()
	     else exchange_list_double (n-1) (a2::tl)

val exchange_list_props: n:nat -> l:list 'a {n+1 < length l} ->
  Lemma (let l' = exchange_list n l in 
  index l n == index l' (n+1) /\ index l (n+1) == index l' n
  /\ (forall m. (m <> n /\ m <> (n+1)) ==> index l m == index l' m))
let rec exchange_list_props n l = match l with
  | a1::a2::tl -> if n = 0 then ()
               else let l' = exchange_list (n-1) (a2::tl) in
                exchange_list_props (n-1) (a2::tl);
                assert (forall m. ((m-1) >= 0 /\ (m-1) <> (n-1) 
                          /\ (m-1) <> n /\ m-1 < length (a2::tl)) ==> 
                          index (a2::tl) (m-1) == index l' (m-1));
                assert (forall m. (m <> n /\ m <> (n+1)) ==>
                          index l m == index (a1::l') m)

val exchange_list_append: n:nat -> l1:list 'a {n+1 < length l1}
  -> l2:list 'a -> Lemma (ensures (exchange_list n (l1@l2) ==
    (exchange_list n l1)@l2))
  [SMTPat (exchange_list n (l1@l2))]
let rec exchange_list_append n l1 l2 = match l1 with
  | a1::a2::tl -> if n = 0 then ()
	       else exchange_list_append (n-1) (a2::tl) l2
                 
val exchange_list_cons: n:nat -> l:list 'a {n+1 < length l} ->
  a:'a -> Lemma (a::(exchange_list n l) == exchange_list (n+1) (a::l))
let exchange_list_cons n l a = ()

val mem_index: #a:eqtype -> e:a -> l:list a -> Tot (r:(option nat)
               {(Some? r ==> (nth l (Some?.v r) == Some e))
               /\ (None? r ==> ~(mem e l))})
let rec mem_index #a e l = match l with
  | [] -> None
  | hd::tl -> if hd = e then Some 0
                      else (match mem_index e tl with
                            | None -> None
                            | Some i -> Some (i+1)
                            )

val drop: n:nat -> l:list 'a {n <= length l} -> Tot (l':list 'a
  {length l' == (length l) - n})
let rec drop n l = if n = 0 then l 
  else match l with
  | _::tl -> drop (n-1) tl

val drop_cons: n:nat -> l:list 'a {n < length l} ->
  Lemma (drop n l == (index l n) :: (drop (n+1) l))
  [SMTPat (drop n l)]
let rec drop_cons n l = if n = 0 then ()
  else match l with
  | _::tl -> drop_cons (n-1) tl

val drop_cons2: n:nat -> l:list 'a {n < length l} -> e:'a ->
  Lemma (drop n l == drop (n+1) (e::l))
  [SMTPat (drop (n+1) (e::l))]
let rec drop_cons2 n l e = () 

val take: n:nat -> l:list 'a {n <= length l} -> Tot (l':list 'a
  {length l' == n})
let rec take n l = if n = 0 then []
  else match l with
  | hd::tl -> hd::(take (n-1) tl)

val take_drop_split: n:nat -> l:list 'a {n <= length l} ->
  Lemma (l == (take n l)@(drop n l))
let rec take_drop_split n l = if n = 0 then ()
  else match l with
  | hd::tl -> take_drop_split (n-1) tl
 
val index_append: l1:list 'a -> l2:list 'a -> n:nat {n < length l1 + length l2} ->
  Lemma (((n < length l1) ==> index (l1 @ l2) n == index l1 n) 
    /\ ((n >= length l1) ==> index (l1 @ l2) n == index l2 (n - length l1)))
  [SMTPat (index (l1 @ l2) n)]
let rec index_append l1 l2 n = match l1 with
  | hd::tl -> if n = 0 then () else index_append tl l2 (n-1)
  | [] -> ()

val drop_index1:l:list 'a -> n:nat{n < length l} ->
  Lemma (ensures (index l n == hd (drop n l)))
let rec drop_index1 l n = if n = 0 then ()
  else match l with
  | _::tl -> drop_index1 tl (n-1)

val drop_index2: l:list 'a -> n:nat{n < length l} -> m:nat {m < length l - n}
  -> e:'a -> Lemma (ensures (index (drop n l) m 
    == index (drop (n+1) (e::l)) m))
let rec drop_index2 l n m e = ()

val drop_index: l:list 'a -> n:nat{n < length l} -> m:nat {m < length l - n} ->
  Lemma (ensures (index l (n+m) == index (drop n l) m))
  (decreases n)
  [SMTPat (index (drop n l) m)]
let rec drop_index l n m = if n = 0 then ()
    else if m = 0 then drop_index1 l n
    else match l with
    | _::tl -> drop_index tl (n-1) m

val insertAt: l:list 'a -> e:'a -> n:nat {n <= length l} -> Tot (list 'a)
let rec insertAt l e n = if n = 0 then e::l
  else match l with
    | hd::tl -> hd::(insertAt tl e (n-1))

val insert_length: l:list 'a -> e:'a -> n:nat {n <= length l} ->
  Lemma (length (insertAt l e n) == 1+length l)
  [SMTPat (length (insertAt l e n))]
let rec insert_length l e n = if n = 0 then ()
  else match l with
    | hd::tl -> insert_length tl e (n-1)

val insert_index: l:list 'a -> e:'a -> n:nat {n <= length l} ->
  i:nat {i < length (insertAt l e n)} ->
  Lemma ((i < n ==> index (insertAt l e n) i == index l i)
    /\ (i = n ==> index (insertAt l e n) i == e)
    /\ (i > n ==> index (insertAt l e n) i == index l (i-1)))
let rec insert_index l e n i = if i <= n then (
    if i = 0 then ()
      else insert_index (tl l) e (n-1) (i-1)
  ) else (
    assert (i > n);
    if n = 0 then ()
    else insert_index (tl l) e (n-1) (i-1)
  )

val insert_append: l1:list 'a -> l2:list 'a -> e:'a 
  -> n:nat {n <= length l1 + length l2} ->
  Lemma (ensures (n < length l1 ==> 
    insertAt (l1@l2) e n == (insertAt l1 e n)@l2)
    /\ (n >= length l1 ==>
    insertAt (l1@l2) e n == l1@(insertAt l2 e (n - length l1))))
let rec insert_append l1 l2 e n = if n = 0 then () 
  else match l1 with
    | [] -> ()
    | hd::tl -> insert_append tl l2 e (n-1)

val insert_append_cons: l1:list 'a -> l2:list 'a -> e:'a ->
  Lemma (ensures insertAt (l1@l2) e (length l1) == (l1@e::l2))
  [SMTPat (insertAt (l1@l2) e (length l1))]
let insert_append_cons l1 l2 e = insert_append l1 l2 e (length l1)

val insert_exchange: l:list 'a -> e1:'a -> n1:nat {n1 <= length l}
  -> e2:'a -> n2:nat {n2 <= n1} ->
  Lemma (insertAt (insertAt l e1 n1) e2 n2 
    == insertAt (insertAt l e2 n2) e1 (n1+1))
  [SMTPat (insertAt (insertAt l e1 n1) e2 n2)]
let rec insert_exchange l e1 n1 e2 n2 = if n2 = 0 then ()
  else match l with
    hd::tl -> insert_exchange tl e1 (n1-1) e2 (n2-1)

val nat_inv_elim: n:nat -> v:nat {v <= n} -> Lemma (n -v +v == n)
let nat_inv_elim n v = ()
  
val nat_plus_side: a:nat -> b:nat -> c:nat ->
  Lemma (a == b + c <==> a - b = c)
let nat_plus_side a b c = ()

val add_zero_l: a:nat -> Lemma (0+a == a)
let add_zero_l a = ()
