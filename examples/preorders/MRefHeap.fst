module MRefHeap

open FStar.Preorder

(* Heap is a tuple of a source of freshness (the no. of the next fresh
   reference to be allocated) and a mapping of allocated raw references
   (represented as natural numbers) to types, values and preorders. *)

let preorder_t (a:Type0) = r:preorder a
let heap_cell_a (a:Type0) = a * preorder_t a
let heap_cell = (a:Type0 & heap_cell_a a)
abstract type heap = h:(nat * (nat -> Tot (option heap_cell)))
		       {(forall (n:nat) . n < fst h ==> (exists v . snd h n == Some v)) /\
			(forall (n:nat) . n >= fst h ==> snd h n == None)}

(* References. *)

abstract type mref (a:Type) (r:preorder_t a) = nat

abstract let addr_of (#a:Type) (#r:preorder_t a) (m:mref a r) : nat = m


(* Containment predicate on heaps. *)

abstract let contains (#a:Type) (#r:preorder_t a) (h:heap) (m:mref a r) : GTot Type0 =
  exists (v:heap_cell).
    snd h m == Some v /\
    dfst v == a /\
    snd #(dfst v) #(preorder_t a) (dsnd v) == r

let contains_same_addr_lemma (#a:Type) (#b:Type) (#r:preorder_t a) (#s:preorder_t b) (h:heap) (m:mref a r) (m':mref b s)
  : Lemma (contains h m /\ contains h m' /\ addr_of m = addr_of m' ==> a == b /\ r == s)
    [SMTPat (contains h m); SMTPat (contains h m'); SMTPat (addr_of m); SMTPat (addr_of m')]
  = ()

let contains_diff_addr_lemma (#a:Type) (#b:Type) (#r:preorder_t a) (#s:preorder_t b) (h:heap) (m:mref a r) (m':mref b s)
  : Lemma (contains h m /\ contains h m' /\ ~(addr_of m = addr_of m') ==> ~(m === m'))
    [SMTPat (contains h m); SMTPat (contains h m'); SMTPat (addr_of m); SMTPat (addr_of m')]
  = ()

(* Select. *)

abstract val sel : #a:Type ->
          #r:preorder a ->
          h:heap ->
	  m:mref a r{contains h m} ->
          Tot a
let sel #a #b h m =
  match snd h m with
  | Some (| _ , (x , _) |) -> x


(* Generating a fresh reference for the given heap. *)

abstract val alloc_ref : h0:heap ->
		a:Type ->
		r:preorder a ->
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

abstract val upd : #a:Type ->
	  #r:preorder a ->
          h0:heap ->
          m:mref a r{contains h0 m} ->
          x:a ->
          Tot (h1:heap{contains h1 m /\
	               sel h1 m == x /\
		       (forall b r' (m':mref b r') .
			  contains h0 m'
			  ==>
			  contains h1 m') /\
		       (forall b r' (m':mref b r'{contains h0 m'}).{:pattern (sel h0 m') \/ (sel h1 m')}
		          ((addr_of m' <> addr_of m) \/
                           ~(m === m')) ==>
			  sel h0 m' == sel h1 m')})
let upd #a #r h0 m x =
  (fst h0 , (fun m' -> if m = m' then Some (| a , (x , r) |)
                                 else snd h0 m'))


(* Empty. *)

abstract val emp : heap
let emp = 0, (fun (r:nat) -> None)
