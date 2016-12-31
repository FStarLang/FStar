module MRefHeap

open Preorder

(* Heap is a tuple of a source of freshness (the no. of the next fresh
   reference to be allocated) and a mapping of allocated raw references
   (represented as natural numbers) to types, values and preorders. *)

abstract type heap = h:(nat * (nat -> Tot (option (dtuple2 Type0 (fun a -> a * r:relation a{preorder r})))))
		       {(forall (n:nat) . n < fst h ==> (exists v . snd h n == Some v)) /\
			(forall (n:nat) . n >= fst h ==> snd h n == None)}

(* References. *)

abstract type mref (a:Type) (r:relation a{preorder r}) = nat


(* Containment predicate on heaps. *)

let contains (#a:Type) (#r:relation a{preorder r}) (h:heap) (m:mref a r) =
  exists v .
    snd h m == Some v /\
    dfst v == a /\
    snd #a #(r:relation a{preorder r}) (dsnd v) == r


(* Select. *)

val sel : #a:Type ->
          #r:relation a{preorder r} ->
          h:heap ->
	  m:mref a r{contains h m} ->
          Tot a
let sel #a #b h m =
  match snd h m with
  | Some (| _ , (x , _) |) -> x


(* Generating a fresh reference for the given heap. *)

val alloc_ref : h0:heap ->
		a:Type ->
		r:relation a{preorder r} ->
	        x:a ->
		Tot (mh1:(mref a r * heap){~(contains #a #r h0 (fst mh1)) /\
		                           contains (snd mh1) (fst mh1) /\
		                           sel (snd mh1) (fst mh1) == x /\
					   (forall b r' (m:mref b r') .
			                      contains h0 m
			                      ==>
			                      contains (snd mh1) m) /\
			                   (forall b r' (m:mref b r'{contains h0 m}) y .
			                      sel #b h0 m == y
		                              ==>
			                      sel #b (snd mh1) m == y)})
let alloc_ref h a r x =
  (fst h , (fst h + 1 , (fun n -> if n = fst h then Some (| a , (x , r) |)
					       else snd h n)))


(* Update. *)

val upd : #a:Type ->
	  #r:relation a{preorder r} ->
          h0:heap ->
          m:mref a r{contains h0 m} ->
          x:a ->
          Tot (h1:heap{contains h1 m /\
	               sel h1 m == x /\
		       (forall b r' (m':mref b r') .
			  contains h0 m'
			  ==>
			  contains h1 m') /\
		       (forall b r' (m':mref b r'{contains h0 m'}) y .
		          ~(m' === m) /\
			  sel h0 m' == y
			  ==>
			  sel h1 m' == y)})
let upd #a #r h0 m x =
  (fst h0 , (fun m' -> if m = m' then Some (| a , (x , r) |)
                                 else snd h0 m'))


(* Empty. *)

val emp : heap
let emp =
  Mktuple2 #nat #(nat -> Tot (option (dtuple2 Type0 (fun a -> a * r:relation a{preorder r})))) 0 (fun (r:nat) -> None)
