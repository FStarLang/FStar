module FStar.MRef.MST

open FStar.Monotonic.Heap

open FStar.Preorder

(* TODO: Use the module system to uniformly control the visibility of the actions of MSTATE and functions *)


(* Definition of the underlying state monad on heap using DM4F *)

let st (a:Type) = heap -> M (a * heap)

let return_st (a:Type) (x:a) : st a = fun h0 -> x, h0

let bind_st (a:Type) (b:Type) (f:st a) (g:a -> st b) : st b
  = fun (h0:heap) -> let (x,h) = f h0 in g x h

let get_st () : st heap = fun h0 -> h0, h0

let put_st (x:heap) : st unit = fun _ -> (), x

total new_effect {
  MSTATE : a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
     ; get_st      = get_st
     ; put_st      = put_st
}


(* Pre- and postcondition presentation of MSTATE *)

let st_pre = heap -> Type0
let st_post a = a -> heap -> Type0

effect MST (a:Type) (pre:st_pre) (post: (heap -> Tot (st_post a))) =
       MSTATE a
             (fun (h0:heap) (p:(a * heap) -> Type0) -> pre h0 
	                                               /\ (forall a h1. post h0 a h1 ==> p (a, h1)))


(* Private definition of monotonic references, used to define heap_rel *)

private abstract let mmref (a:Type) (rel:preorder a) = mref a rel

private let m_as_mref (#a:Type) (#rel:preorder a) (m:mmref a rel) :GTot (mref a rel) = m

private let m_contains (#a:Type) (#rel:preorder a) (m:mmref a rel) (h:heap) = contains h (m_as_mref m)

private let m_addr_of (#a:Type) (#rel:preorder a) (m:mmref a rel) :GTot nat = addr_of (m_as_mref m)

private let m_sel (#a:Type) (#rel:preorder a) (h:heap) (m:mmref a rel) :GTot a 
  = sel h (m_as_mref m)

private let m_upd (#a:Type) (#rel:preorder a) (h:heap) (m:mmref a rel) (x:a{upd_condition h (m_as_mref m) x}) 
  :GTot heap 
  = upd h (m_as_mref m) x


(* Generated preorder on heaps *)

let heap_rel (h0:heap) (h1:heap) 
  = (forall a rel (m:mmref a rel) . (m_contains m h0 ==> m_contains m h1) )
 /\ (forall a rel (m:mmref a rel) . (m_contains m h0 ==> rel (m_sel h0 m) (m_sel h1 m)))


(* Lifting a relation on mmref to heap_rel *)

val m_lifting_lemma_aux: (#a:Type)
	              -> (#b:Type)
                      -> (#rel:preorder a)
	              -> (#rel':preorder b)
                      -> (h:heap)
                      -> (m:mmref a rel)
	              -> (m':mmref b rel')
                      -> (x:a)
	              -> Lemma (requires (m_contains m h /\ rel (m_sel h m) x
		                          /\ m_addr_of m = m_addr_of m' /\ m_contains m' h))
	                       (ensures  (rel (m_sel h m) x
			                  /\ rel' (m_sel h m') (m_sel (m_upd h m x) m')))
		               [SMTPat (m_contains m' h); SMTPat (rel (m_sel h m) x)]
let m_lifting_lemma_aux #a #b #rel #rel' h m m' x 
  = lemma_contains_same_type h (m_as_mref m) (m_as_mref m'); 
    lemma_contains_same_rel h (m_as_mref m) (m_as_mref m')

val m_lifting_lemma: (#a:Type) 
                  -> (#rel:preorder a) 
	          -> (h:heap)
	          -> (m:mmref a rel) 
	          -> (x:a)
	          -> Lemma (requires (m_contains m h /\ rel (m_sel h m) x))
		           (ensures  (m_contains m h /\ rel (m_sel h m) x
			              /\ heap_rel h (m_upd h m x)))
			   [SMTPat (heap_rel h (m_upd h m x))]
let m_lifting_lemma #a #rel h m x = ()


(* The preorder-indexed monad interface for MSTATE *)

val mst_get: unit -> MST heap (fun _ -> True) (fun h0 h h1 -> h0 == h /\ h == h1)
let mst_get () = MSTATE?.get_st ()

val mst_put: h:heap -> MST unit (fun h0 -> heap_rel h0 h) (fun _ _ h1 -> h == h1)
let mst_put h = MSTATE?.put_st h

//this abstract type can be used when MST is defined in a separate module
//abstract type mst_witnessed (p:predicate heap) = True

assume type mst_witnessed : (p:predicate heap) -> Type0

val mst_witness: p:predicate heap{stable p heap_rel} 
              -> MST unit (fun h0 -> p h0) (fun h0 _ h1 -> h0 == h1 /\ mst_witnessed p)
let mst_witness p = admit () //intentional (justified by metatheory)

//Compared to FStar.MRef.fst, has (stable p heap_rel) refinement, so as to ensure the metatheoretical well-formedness of (mst_witnessed p)
val mst_recall: p:predicate heap{stable p heap_rel} 
             -> MST unit (fun _ -> mst_witnessed p) (fun h0 _ h1 -> h0 == h1 /\ p h1)
let mst_recall p = admit () //intentional (justified by metatheory)


(* Monotonic references and operations on them *)

abstract let mref (a:Type) (rel:preorder a) = m:mmref a rel{mst_witnessed (m_contains m)}

let as_mref (#a:Type) (#rel:preorder a) (m:mref a rel) 
  :GTot (FStar.Monotonic.Heap.mref a rel) 
  = m_as_mref m

private let as_mmref (#a:Type) (#rel:preorder a) (m:mref a rel) :GTot (mmref a rel) = m

let contains (#a:Type) (#rel:preorder a) (h:heap) (m:mref a rel) = m_contains (as_mref m) h

let addr_of (#a:Type) (#rel:preorder a) (m:mref a rel) :GTot nat = m_addr_of (as_mref m)

let sel (#a:Type) (#rel:preorder a) (h:heap) (m:mref a rel) :GTot a = m_sel h (as_mref m)

let upd (#a:Type) (#rel:preorder a) (h:heap) (m:mref a rel) (x:a{upd_condition h (as_mref m) x}) 
  :GTot heap 
  = m_upd h (as_mref m) x


(* Lifting a relation on mref to heap_rel *)

val lifting_lemma: (#a:Type) 
                -> (#rel:preorder a) 
	        -> (h:heap)
	        -> (m:mref a rel) 
	        -> (x:a)
	        -> Lemma (requires (contains h m /\ rel (sel h m) x))
		         (ensures  (contains h m /\ rel (sel h m) x /\ heap_rel h (upd h m x)))
			 [SMTPat (heap_rel h (upd h m x))]
let lifting_lemma #a #rel h m x = m_lifting_lemma h (as_mmref m) x


(* The public monotonic references interface for MSTATE *)

(* Allocation *)

type fresh(#a:Type) (#rel:preorder a) (x:a) h0 (m:mref a rel) h1 = 
  ~(contains h0 m) /\ contains h1 m /\ h1 == upd h0 m x

val alloc: #a:Type
        -> #rel:preorder a
        -> x:a
        -> MST (mref a rel)
               (requires (fun _ -> True))
               (fun h0 m h1 -> fresh x h0 m h1)
let alloc #a #rel x 
  = let h0 = mst_get () in
    let m, h1 = alloc_tot h0 x rel false in 
    mst_put h1;
    mst_witness (m_contains m);
    m

(* Read and write *)

val read: #a:Type
       -> #rel:preorder a
       -> m:mref a rel
       -> MST a
              (requires (fun h -> True))
              (ensures  (fun h0 v h1 -> h0 == h1 /\ v == sel h0 m))
let read #a #rel m
  = let h = mst_get () in
    mst_recall (m_contains m);
    FStar.Monotonic.Heap.sel_tot h m

val write: #a:Type
        -> #rel:preorder a
        -> m:mref a rel
        -> x:a
        -> MST unit
               (requires (fun h0 -> rel (sel h0 m) x))
               (ensures  (fun h0 _ h1 -> rel (sel h0 m) x /\ h1 == upd h0 m x))
let write #a #rel m x
  = let h0 = mst_get () in
    mst_recall (m_contains m);
    let h1 = FStar.Monotonic.Heap.upd_tot h0 m x in
    mst_put h1

(* Taking and recalling tokens*)

let token (#a:Type) (#rel:preorder a) (m:mref a rel) (p:predicate a) 
  = mst_witnessed (fun h -> contains h m /\ p (sel h m))


val take_token: #a:Type
             -> #rel:preorder a
             -> m:mref a rel
             -> p:predicate a
             -> MST unit
                    (requires (fun h0 -> p (sel h0 m) /\ stable p rel))
                    (ensures  (fun h0 _ h1 -> h0 == h1 /\ token m p))
let take_token #a #rel m p 
  = mst_recall (m_contains m); 
    mst_witness (fun h -> contains h m /\ p (sel h m))

val recall_token: #a:Type
               -> #rel:preorder a
               -> m:mref a rel
               -> p:predicate a
               -> MST unit
	              //Compared to FStar.MRef.fst, has (stable p rel) precondition to ensure 
		      //the metatheoretical well-formedness of the underlying (mst_witnessed p)
                      (requires (fun _ -> stable p rel /\ token m p))   
                      (ensures  (fun h0 _ h1 -> h0 == h1 /\ p (sel h1 m)))
let recall_token #a #rel m p
  = mst_recall (fun h -> contains h m /\ p (sel h m))

(* Witnessing and recalling *)

let stable_on_heap_aux (#a:Type) (#rel:preorder a) (m:mref a rel) (p:predicate heap) (h0:heap) (h1:heap) =
  p h0 /\
  (contains h0 m ==> contains h1 m /\ rel (sel h0 m) (sel h1 m))
  ==>
  p h1

let stable_on_heap (#a:Type) (#rel:preorder a) (m:mref a rel) (p:predicate heap) = 
  forall h0 h1. stable_on_heap_aux m p h0 h1

let lemma_stable_on_heap (#a:Type) (#rel:preorder a) (m:mref a rel) (p:predicate heap) 
  :Lemma (forall h0 h1 . stable_on_heap_aux m p h0 h1
			 ==>
			 (p h0 /\ heap_rel h0 h1 ==> p h1))
	 [SMTPat (stable_on_heap m p); SMTPat (stable p heap_rel)]
= ()

let witnessed (p:predicate heap) = mst_witnessed p

val witness: #a:Type
          -> #rel:preorder a
          -> m:mref a rel
          -> p:predicate heap
          -> MST unit
                 (requires (fun h0 -> p h0 /\ stable_on_heap m p))
                 (ensures  (fun h0 _ h1 -> h0 == h1 /\ witnessed p))
let witness #a #rel m p = mst_witness p

val recall: #a:Type
                        -> #rel:preorder a
                        -> m:mref a rel
                        -> p:predicate heap
                        -> MST unit
			       //Compared to FStar.MRef.fst, has (stable_on_heap m p) precondition to ensure 
		               //the metatheoretical well-formedness of the underlying (mst_witnessed p)
                               (requires (fun _ -> stable_on_heap m p /\ witnessed p))
                               (ensures  (fun h0 _ h1 -> h0 == h1 /\ p h1))
let recall #a #rel m p = mst_recall p

val witness_heap: #a:Type
               -> #rel:preorder a
               -> m:mref a rel
               -> p:predicate heap
               -> MST unit
                      (requires (fun h0 -> p h0 /\ stable p heap_rel))
                      (ensures  (fun h0 _ h1 -> h0 == h1 /\ witnessed p))
let witness_heap #a #rel m p = mst_witness p

val recall_heap: #a:Type
              -> #rel:preorder a
              -> m:mref a rel
              -> p:predicate heap
              -> MST unit
		     //Compared to FStar.MRef.fst, has (stable p heap_rel) precondition to ensure 
		     //the metatheoretical well-formedness of the underlying (mst_witnessed p)
                     (requires (fun _ -> stable p heap_rel /\ witnessed p))
                     (ensures  (fun h0 _ h1 -> h0 == h1 /\ p h1))
let recall_heap #a #rel m p = mst_recall p



(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* Below is a more strongly typed version of the above code *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

(*
module FStar.MRef.MST

open FStar.Monotonic.Heap

open FStar.Preorder

(* TODO: Use the module system to properly control the visibility of actions and functions *)


(* Definition of the underlying state monad on heap using DM4F *)

let st (a:Type) = heap -> M (a * heap)

let return_st (a:Type) (x:a) : st a = fun h0 -> x, h0

let bind_st (a:Type) (b:Type) (f:st a) (g:a -> st b) : st b
  = fun (h0:heap) -> let (x,h) = f h0 in g x h

let get_st () : st heap = fun h0 -> h0, h0

let put_st (x:heap) : st unit = fun _ -> (), x

total new_effect {
  MSTATE : a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
     ; get_st      = get_st
     ; put_st      = put_st
}


(* Pre- and postcondition presentation of MSTATE *)

let st_pre = heap -> Type0
let st_post a = a -> heap -> Type0

effect MST (a:Type) (pre:st_pre) (post: (heap -> Tot (st_post a))) =
       MSTATE a
             (fun (h0:heap) (p:(a * heap) -> Type0) -> pre h0 
	                                               /\ (forall a h1. post h0 a h1 ==> p (a, h1)))


(* Private definition of monotonic references, used to define heap_rel *)

private abstract let mmref (a:Type) (rel:preorder a) = mref a rel

private let m_as_mref (#a:Type) (#rel:preorder a) (m:mmref a rel) :GTot (mref a rel) = m

private let m_contains (#a:Type) (#rel:preorder a) (m:mmref a rel) (h:heap) = contains h (m_as_mref m)

private let m_addr_of (#a:Type) (#rel:preorder a) (m:mmref a rel) :GTot nat = addr_of (m_as_mref m)

private let m_sel (#a:Type) (#rel:preorder a) (h:heap) (m:mmref a rel) :GTot a 
  = sel h (m_as_mref m)

private let m_upd (#a:Type) (#rel:preorder a) (h:heap) (m:mmref a rel) (x:a{upd_condition h (m_as_mref m) x}) 
  :GTot heap 
  = upd h (m_as_mref m) x


(* Generated preorder on heaps *)

let heap_rel (h0:heap) (h1:heap) 
  = (forall a rel (m:mmref a rel) . (m_contains m h0 ==> m_contains m h1) )
 /\ (forall a rel (m:mmref a rel) . (m_contains m h0 ==> rel (m_sel h0 m) (m_sel h1 m)))


(* Lifting a relation on mmref to heap_rel *)

val m_lifting_lemma_aux: (#a:Type)
	              -> (#b:Type)
                      -> (#rel:preorder a)
	              -> (#rel':preorder b)
                      -> (h:heap)
                      -> (m:mmref a rel)
	              -> (m':mmref b rel')
                      -> (x:a)
	              -> Lemma (requires (m_contains m h /\ rel (m_sel h m) x
		                          /\ m_addr_of m = m_addr_of m' /\ m_contains m' h))
	                       (ensures  (rel (m_sel h m) x
			                  /\ rel' (m_sel h m') (m_sel (m_upd h m x) m')))
		               [SMTPat (m_contains m' h); SMTPat (rel (m_sel h m) x)]
let m_lifting_lemma_aux #a #b #rel #rel' h m m' x 
  = lemma_contains_same_type h (m_as_mref m) (m_as_mref m'); 
    lemma_contains_same_rel h (m_as_mref m) (m_as_mref m')

val m_lifting_lemma: (#a:Type) 
                  -> (#rel:preorder a) 
	          -> (h:heap)
	          -> (m:mmref a rel) 
	          -> (x:a)
	          -> Lemma (requires (m_contains m h /\ rel (m_sel h m) x))
		           (ensures  (m_contains m h /\ rel (m_sel h m) x
			              /\ heap_rel h (m_upd h m x)))
			   [SMTPat (heap_rel h (m_upd h m x))]
let m_lifting_lemma #a #rel h m x = ()


(* The preorder-indexed monad interface for MSTATE *)

val mst_get: unit -> MST heap (fun _ -> True) (fun h0 h h1 -> h0 == h /\ h == h1)
let mst_get () = MSTATE?.get_st ()

val mst_put: h:heap -> MST unit (fun h0 -> heap_rel h0 h) (fun _ _ h1 -> h == h1)
let mst_put h = MSTATE?.put_st h

//this abstract type can be used when MST is defined in a separate module
//abstract type mst_witnessed (p:predicate heap{stable p heap_rel}) = True

assume type mst_witnessed : (p:predicate heap{stable p heap_rel}) -> Type0

val mst_witness: p:predicate heap{stable p heap_rel} 
              -> MST unit (fun h0 -> p h0) (fun h0 _ h1 -> h0 == h1 /\ mst_witnessed p)
let mst_witness p = admit () //intentional (justified by metatheory)

val mst_recall: p:predicate heap{stable p heap_rel} 
             -> MST unit (fun _ -> mst_witnessed p) (fun h0 _ h1 -> h0 == h1 /\ p h1)
let mst_recall p = admit () //intentional (justified by metatheory)


(* Monotonic references and operations on them *)

abstract let mref (a:Type) (rel:preorder a) = m:mmref a rel{mst_witnessed (m_contains m)}

let as_mref (#a:Type) (#rel:preorder a) (m:mref a rel) 
  :GTot (FStar.Monotonic.Heap.mref a rel) 
  = m_as_mref m

let as_mmref (#a:Type) (#rel:preorder a) (m:mref a rel) :GTot (mmref a rel) = m

let contains (#a:Type) (#rel:preorder a) (h:heap) (m:mref a rel) = m_contains (as_mref m) h //contains h (as_mref m)

let addr_of (#a:Type) (#rel:preorder a) (m:mref a rel) :GTot nat = m_addr_of (as_mref m) //addr_of (as_mref m)

let sel (#a:Type) (#rel:preorder a) (h:heap) (m:mref a rel) :GTot a = m_sel h (as_mref m) //sel h (as_mref m)

let upd (#a:Type) (#rel:preorder a) (h:heap) (m:mref a rel) (x:a{upd_condition h (as_mref m) x}) 
  :GTot heap 
  = m_upd h (as_mref m) x //upd h (as_mref m) x


(* Lifting a relation on mref to heap_rel *)

val lifting_lemma: (#a:Type) 
                -> (#rel:preorder a) 
	        -> (h:heap)
	        -> (m:mref a rel) 
	        -> (x:a)
	        -> Lemma (requires (contains h m /\ rel (sel h m) x))
		         (ensures  (contains h m /\ rel (sel h m) x /\ heap_rel h (upd h m x)))
			 [SMTPat (heap_rel h (upd h m x))]
let lifting_lemma #a #rel h m x = m_lifting_lemma h (as_mmref m) x


(* The public monotonic references interface for MSTATE *)

(* Allocation *)

type fresh(#a:Type) (#rel:preorder a) (x:a) h0 (m:mref a rel) h1 = 
  ~(contains h0 m) /\ contains h1 m /\ h1 == upd h0 m x

val alloc: #a:Type
        -> #rel:preorder a
        -> x:a
        -> MST (mref a rel)
               (requires (fun _ -> True))
               (fun h0 m h1 -> fresh x h0 m h1)
let alloc #a #rel x 
  = let h0 = mst_get () in
    let m, h1 = alloc_tot h0 x rel false in 
    mst_put h1;
    mst_witness (m_contains m);
    m

(* Read and write *)

val read: #a:Type
       -> #rel:preorder a
       -> m:mref a rel
       -> MST a
              (requires (fun h -> True))
              (ensures  (fun h0 v h1 -> h0 == h1 /\ v == sel h0 m))
let read #a #rel m
  = let h = mst_get () in
    mst_recall (m_contains m);
    FStar.Monotonic.Heap.sel_tot h m

val write: #a:Type
        -> #rel:preorder a
        -> m:mref a rel
        -> x:a
        -> MST unit
               (requires (fun h0 -> rel (sel h0 m) x))
               (ensures  (fun h0 _ h1 -> rel (sel h0 m) x /\ h1 == upd h0 m x))
let write #a #rel m x
  = let h0 = mst_get () in
    mst_recall (m_contains m);
    let h1 = FStar.Monotonic.Heap.upd_tot h0 m x in
    mst_put h1

(* Taking and recalling tokens*)

let token (#a:Type) (#rel:preorder a) (m:mref a rel) (p:predicate a{stable p rel}) 
  = mst_witnessed (fun h -> contains h m /\ p (sel h m))


val take_token: #a:Type
             -> #rel:preorder a
             -> m:mref a rel
             -> p:predicate a{stable p rel}
             -> MST unit
                    (requires (fun h0 -> p (sel h0 m)))
                    (ensures  (fun h0 _ h1 -> h0 == h1 /\ token m p))
let take_token #a #rel m p 
  = mst_recall (m_contains m); 
    mst_witness (fun h -> contains h m /\ p (sel h m))

val recall_token: #a:Type
               -> #rel:preorder a
               -> m:mref a rel
               -> p:predicate a{stable p rel}
               -> MST unit
                      (requires (fun _ ->  token m p))
                      (ensures  (fun h0 _ h1 -> h0 == h1 /\ p (sel h1 m)))
let recall_token #a #rel m p
  = mst_recall (fun h -> contains h m /\ p (sel h m))

(* Witnessing and recalling *)

let stable_on_heap_aux (#a:Type) (#rel:preorder a) (m:mref a rel) (p:predicate heap) (h0:heap) (h1:heap) =
  p h0 /\
  (contains h0 m ==> contains h1 m /\ rel (sel h0 m) (sel h1 m))
  ==>
  p h1

let stable_on_heap (#a:Type) (#rel:preorder a) (m:mref a rel) (p:predicate heap) = 
  forall h0 h1. stable_on_heap_aux m p h0 h1

let lemma_stable_on_heap (#a:Type) (#rel:preorder a) (m:mref a rel) (p:predicate heap) 
  :Lemma (forall h0 h1 . stable_on_heap_aux m p h0 h1
			 ==>
			 (p h0 /\ heap_rel h0 h1 ==> p h1))
	 [SMTPat (stable_on_heap m p); SMTPat (stable p heap_rel)]
= ()

let witnessed_stable_on_heap (#a:Type) (#rel:preorder a) (m:mref a rel) (p:predicate heap{stable_on_heap m p}) = mst_witnessed p

val witness_stable_on_heap: #a:Type
                         -> #rel:preorder a
                         -> m:mref a rel
                         -> p:predicate heap{stable_on_heap m p}
                         -> MST unit
                                (requires (fun h0 -> p h0))
                                (ensures  (fun h0 _ h1 -> h0 == h1 /\ witnessed_stable_on_heap m p))
let witness_stable_on_heap #a #rel m p = mst_witness p

val recall_stable_on_heap: #a:Type
                        -> #rel:preorder a
                        -> m:mref a rel
                        -> p:predicate heap{stable_on_heap m p}
                        -> MST unit
                               (requires (fun _ ->  witnessed_stable_on_heap m p))
                               (ensures  (fun h0 _ h1 -> h0 == h1 /\ p h1))
let recall_stable_on_heap #a #rel m p = mst_recall p

let witnessed (p:predicate heap{stable p heap_rel}) = mst_witnessed p

val witness: #a:Type
          -> #rel:preorder a
          -> m:mref a rel
          -> p:predicate heap{stable p heap_rel}
          -> MST unit
                 (requires (fun h0 -> p h0))
                 (ensures  (fun h0 _ h1 -> h0 == h1 /\ witnessed p))
let witness #a #rel m p = mst_witness p

val recall: #a:Type
         -> #rel:preorder a
         -> m:mref a rel
         -> p:predicate heap{stable p heap_rel}
         -> MST unit
                (requires (fun _ ->  witnessed p))
                (ensures  (fun h0 _ h1 -> h0 == h1 /\ p h1))
let recall #a #rel m p = mst_recall p
*)
