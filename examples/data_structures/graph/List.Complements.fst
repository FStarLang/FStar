module List.Complements

open FStar.Fin
module L = FStar.List.Tot
module C = FStar.Classical

let disjoint (#a:eqtype) (n1: list a) (n2:list a) = forall x . L.mem x n1 ==> not (L.mem x  n2)

let rec noRepeats_map (#a #b:eqtype) (f:a -> b) (l:list a)
  : Lemma (requires (L.noRepeats l /\
    (forall (x y:a). L.memP x l /\ L.memP y l /\ f x == f y ==> x == y)))
    (ensures (L.noRepeats (L.map f l)))
    (decreases l)
= match l with
  | [] -> ()
  | x :: xs ->
    let x' = f x in
    let l' = L.map f xs in
    noRepeats_map f xs ;
    L.mem_memP x xs ; L.mem_memP x' l' ;
    L.memP_map_elim f x' xs ;
    L.noRepeats_cons (f x)l'


let noRepeats_tail (#a:eqtype) (l:list a{Cons? l})
 : Lemma (requires (L.noRepeats l)) (ensures (L.noRepeats (L.tail l)))
 = ()

let rec filter_no_mem (#a :eqtype) (f:a -> bool) (l:list a) (e:a)
  : Lemma (requires (L.mem e l = false))
    (ensures (L.mem e (L.filter f l) = false))
    (decreases l)
= match l with
 | [] -> ()
 | x :: xs -> filter_no_mem f xs e

let rec noRepeats_filter (#a :eqtype) (f:a -> bool) (l:list a)
  : Lemma (requires (L.noRepeats l))
    (ensures (L.noRepeats (L.filter f l)))
    (decreases l)
= match l with
  | [] -> ()
  | x :: xs -> 
   if f x then
   (
    filter_no_mem f xs x;
    noRepeats_filter f xs
   )
   else noRepeats_filter f xs

let rec noRepeats_length_lemma (#n:nat) (l:list (fin n))
: Lemma (requires (L.noRepeats l)) (ensures (L.length l <= n)) (decreases n)
=
  match l with
  | [] -> ()
  | x :: xs ->
    if n = 1 then ()
    else
      let f (k:fin n) : fin (n-1) = if k > x then k - 1 else if k < x then (k <: nat) else 0 <: fin (n-1) in
      C.forall_intro (fun (k:fin n) -> L.mem_memP k xs <: Lemma (L.mem k xs <==> L.memP k xs)) ;
      assert (forall (k:fin n). L.memP k xs ==> k <> x) ;
      assert (forall (k1 k2:fin n). k1 <> x /\ k2 <> x /\ f k1 == f k2 ==> k1 == k2) ;
      let l' = L.map f xs in
      noRepeats_map f xs ;
      noRepeats_length_lemma #(n-1) l'

