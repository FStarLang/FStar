module NatHeap

open FStar.Preorder

(* Heap is a tuple of a source of freshness (the no. of the next 
   reference to be allocated) and a mapping of allocated raw 
   references (represented as natural numbers) to types and values. *)

(* NB: (a:Type0 & a) instead of dtuple2 is better notation *)

module F = FStar.FunctionalExtensionality

abstract type heap = h:(nat * (F.restricted_t nat (fun _ -> (option (dtuple2 Type0 (fun a -> a))))))
		       {(forall (n:nat) . n < fst h ==> (exists v . snd h n == Some v)) /\ 
			(forall (n:nat) . n >= fst h ==> snd h n == None)}


(* Consistency of heaps. aka, no strong updates *)

abstract let consistent (h0:heap) (h1:heap) : GTot Type0 =
  forall n x y . (snd h0 n == Some x /\ snd h1 n == Some y)  ==> dfst x == dfst y


(* References. *)

abstract type ref (a:Type) = nat

//type aref =
//  | Ref : a:Type -> r:ref a -> aref

(* Containment predicate on heaps. *)

abstract let contains (#a:Type) (h:heap) (r:ref a) : GTot Type0 =
  exists x . snd h r == Some (| a , x |)
//NB: Some? (snd h r), would avoid the existential, but would not capture the type equality

//NB: match snd h r with | Some (| b, _ |) -> a == b | _ -> False
//    this style would avoid the existential

//NB: Although, it appears that the existential variable actually seems to help in this case
//    would be good to understand why (at some point)

(* Select. *)

abstract val sel : #a:Type -> 
          h:heap ->
	  r:ref a{contains h r} -> 
          Tot a
let sel #a h r =
  match snd h r with
  | Some (| _ , x |) -> x


(* Generating a fresh reference for the given heap. *)

abstract val alloc_ref : h0:heap ->
                a:Type -> 
		x:a -> 
		Tot (rh1:(ref a * heap)
			 {~(contains h0 (fst rh1)) /\ 
			  contains (snd rh1) (fst rh1) /\
		          sel (snd rh1) (fst rh1) == x /\
			  (forall b (r:ref b) .{:pattern (contains h0 r)}
			     contains h0 r 
			     ==> 
			     contains (snd rh1) r) /\
			  (forall b (r:ref b{contains h0 r}) . {:pattern sel #b h0 r}
			     sel #b h0 r == sel #b (snd rh1) r)})
let alloc_ref h0 a x = 
  (fst h0 , (fst h0 + 1 , F.on_dom nat (fun r -> if r = fst h0 then Some (| a , x |)
					     else snd h0 r)))


(* Update. *)

abstract val upd : #a:Type -> 
          h0:heap -> 
          r:ref a{contains h0 r} -> 
          x:a -> 
          Tot (h1:heap{contains h1 r /\ 
	               sel h1 r == x /\
		       (forall b (r':ref b) . {:pattern (contains h0 r')}
			  contains h0 r' 
			  ==> 
			  contains h1 r') /\
		       (forall b (r':ref b{contains h0 r'}) . {:pattern sel h0 r'}
		          ~(r === r') ==>
			  sel h0 r' == sel h1 r')})
let upd #a h0 r x = 
  (fst h0 , F.on_dom nat (fun r' -> if r = r' then Some (| a , x |)
                                else snd h0 r'))


(* Empty. *)

abstract val emp : heap
let emp = Mktuple2 0 (F.on_dom nat (fun (r:nat) -> None))


(*
(* Domain. *)

open FStar.Set

private val domain_acc : h:heap -> n:nat{n <= fst h} -> Tot (set aref)
let rec domain_acc h n = 
  if n = 0 then empty
           else (match snd h (n - 1) with
	         | Some (| a , _ |) -> let r:ref a = n - 1 in 
		                       union (singleton (Ref a r)) (domain_acc h (n - 1)))  //Universe problem with (Ref a r)


val domain : heap -> Tot (set aref)
let domain h = domain_acc h (fst h)
*)


(* Concatenation. *)

val max : nat -> nat -> Tot nat
let max n m =
  if n > m then n else m
  

abstract val concat : h0:heap -> h1:heap{consistent h0 h1} -> Tot heap
let concat h0 h1 = 
  (max (fst h0) (fst h1) , F.on_dom nat (fun r -> match snd h0 r with
                                             | None -> snd h1 r
  				             | Some v -> 
  				               (match snd h1 r with
  					        | None -> Some v
  					        | Some v' -> Some v')))


(* Lemmas about the consistency of heaps. *)

val consistent_refl : h:heap ->
                      Lemma (consistent h h)
let consistent_refl h = ()


val emp_consistent : h:heap -> 
                     Lemma (consistent emp h)
let emp_consistent h = ()


val upd_consistent : h:heap ->
                     a:Type ->
		     r:ref a{contains h r} ->
		     x:a ->
                     Lemma (consistent h (upd h r x))
let upd_consistent h a r x = ()


val alloc_ref_consistent : h:heap ->
                           a:Type ->
			   x:a ->
			   Lemma (consistent h (snd (alloc_ref h a x)))
let alloc_ref_consistent h a x = ()


(* Lemmas about (contains). *)

val contains_sel : h:heap -> 
                   a:Type -> 
		   r:ref a{contains h r} -> 
		   Lemma (exists x . sel h r == x)
let contains_sel h a r = ()


val contains_upd : h:heap ->                
                   a:Type ->
		   b:Type ->
		   r:ref a{contains h r} ->
		   x:a ->
		   r':ref b ->
		   Lemma (requires (contains h r'))
		         (ensures  (contains (upd h r x) r'))
		   [SMTPat (contains (upd h r x) r')]  
let contains_upd h a b r x r' = ()           


val contains_emp : a:Type -> 
                   r:ref a -> 
		   Lemma (requires (True))
		         (ensures  (~(contains emp r)))
		   [SMTPat (~(contains emp r))]
let contains_emp a r = ()


(* Lemmas about the interaction of (sel) and (upd). *)

val sel_upd1 : h:heap ->
               a:Type -> 
	       r:ref a{contains #a h r} -> 
	       x:a -> 
	       Lemma (requires (True))
	             (ensures  (sel (upd h r x) r == x))
	       [SMTPat (sel (upd h r x) r)]
let sel_upd1 h a r x = ()


val sel_upd2 : h:heap ->
               a:Type ->
               b:Type -> 
	       r:ref a{contains #a h r} -> 
	       x:a -> 
	       r':ref b{contains #b h r'} -> 
	       Lemma (requires (~(r === r')))
	             (ensures  (sel (upd h r x) r' == sel h r'))
	       [SMTPat (sel (upd h r x) r')]
let sel_upd2 h a b r x r' = ()


val upd_sel : h:heap ->
              a:Type -> 
	      r:ref a{contains #a h r} -> 
	      Lemma (requires (True))
	            (ensures  (upd h r (sel h r) == h))
	      [SMTPat (upd h r (sel h r))]
let upd_sel h a r = 
  assert (FStar.FunctionalExtensionality.feq (snd (upd h r (sel h r))) (snd h))


(* Lemmas about (concat). *)

val contains_concat1 : h0:heap -> 
		       h1:heap{consistent h0 h1} -> 
		       a:Type ->
		       r:ref a -> 
		       Lemma (requires (contains h0 r))
                             (ensures  (contains (concat h0 h1) r))
			     [SMTPat (contains (concat h0 h1) r)]
let contains_concat1 h0 h1 a r = 
  match snd h0 r with
  | Some v -> 
      (match snd h1 r with
       | None -> ()
       | Some v' -> assert (dfst v == dfst v'))


val contains_concat2 : h0:heap -> 
		       h1:heap{consistent h0 h1} -> 
		       a:Type ->
		       r:ref a -> 
		       Lemma (requires (contains h1 r))
                             (ensures  (contains (concat h0 h1) r))
		       [SMTPat (contains (concat h0 h1) r)]
let contains_concat2 h0 h1 a r = ()


val sel_concat1 : h0:heap -> 
		  h1:heap{consistent h0 h1} -> 
		  a:Type ->
		  r:ref a{contains h0 r /\ ~(contains h1 r)} -> 
		  Lemma (requires (True))
		        (ensures  (sel (concat h0 h1) r == sel h0 r))
	          [SMTPat (sel (concat h0 h1) r)]
let sel_concat1 h0 h1 a r = 
  match snd h0 r with
  | Some v -> 
      match snd h1 r with
      | None -> ()
      | Some v' -> assert (dfst v == dfst v')


val sel_concat2 : h0:heap -> 
		  h1:heap{consistent h0 h1} -> 
		  a:Type ->
		  r:ref a{contains h1 r} -> 
		  Lemma (requires (True))
		        (ensures  (sel (concat h0 h1) r == sel h1 r))
	          [SMTPat (sel (concat h0 h1) r)]
let sel_concat2 h0 h1 a r = ()

