module FStar.MRef.MST2

open FStar.Monotonic.Heap

(* TODO: Use the module system to properly control the visibility of actions and functions *)

(* Preordered relations and stable predicates *)

let relation (a:Type) = a -> a -> Type0

let predicate (a:Type) = a -> Type0

let preorder_rel (#a:Type) (rel:relation a) = 
  (forall x . rel x x) /\ (forall x y z . rel x y /\ rel y z ==> rel x z)

let preorder (a:Type) = rel:relation a{preorder_rel rel}

let stable_rel (#a:Type) (rel:relation a{preorder_rel rel}) (p:predicate a) =
  forall x y . p x /\ rel x y ==> p y


(* Defining the underlying state monad on mem using DM4F *)

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


(* Pre- and postcondition form of MSTATE *)

let st_pre = heap -> Type0
let st_post a = a -> heap -> Type0

effect MST (a:Type) (pre:st_pre) (post: (heap -> Tot (st_post a))) =
       MSTATE a
             (fun (h0:heap) (p:(a * heap) -> Type0) -> pre h0 /\ (forall a h1. post h0 a h1 ==> p (a, h1)))


(* Private definition of monotonic references, used to state heap_rel *)

private abstract let mmref (a:Type) (rel:preorder a) = mref a rel

let m_as_mref (#a:Type) (#rel:preorder a) (m:mmref a rel) :GTot (mref a rel) = m

let m_contains (#a:Type) (#rel:preorder a) (h:heap) (m:mmref a rel) = contains h (m_as_mref m)

let m_addr_of (#a:Type) (#rel:preorder a) (m:mmref a rel) :GTot nat = addr_of (m_as_mref m)

let m_sel (#a:Type) (#rel:preorder a) (h:heap) (m:mmref a rel) :GTot a 
  = sel h (m_as_mref m)

let m_upd (#a:Type) (#rel:preorder a) (h:heap) (m:mmref a rel) (x:a{upd_condition h (m_as_mref m) x}) :GTot heap 
  = upd h (m_as_mref m) x


(* Generated preorder on heaps *)

let heap_rel (h0:heap) (h1:heap) 
  = (forall a rel (m:mmref a rel) . (m_contains h0 m ==> m_contains h1 m) )
 /\ (forall a rel (m:mmref a rel) . (m_contains h0 m ==> rel (m_sel h0 m) (m_sel h1 m)))


(* Lifting a relation on reference to heap_rel *)

val m_lifting_lemma_aux: (#a:Type)
	              -> (#b:Type)
                      -> (#rel:preorder a)
	              -> (#rel':preorder b)
                      -> (h:heap)
                      -> (m:mmref a rel)
	              -> (m':mmref b rel')
                      -> (x:a)
	              -> Lemma (requires (m_contains h m /\ rel (m_sel h m) x /\ m_addr_of m = m_addr_of m' /\ m_contains h m'))
	                       (ensures  (rel (m_sel h m) x /\ rel' (m_sel h m') (m_sel (m_upd h m x) m')))
		               [SMTPat (m_contains h m'); SMTPat (rel (m_sel h m) x)]
let m_lifting_lemma_aux #a #b #rel #rel' h m m' x = lemma_contains_same_type h (m_as_mref m) (m_as_mref m'); lemma_contains_same_rel h (m_as_mref m) (m_as_mref m')

val m_lifting_lemma: (#a:Type) 
                  -> (#rel:preorder a) 
	          -> (h:heap)
	          -> (m:mmref a rel) 
	          -> (x:a)
	          -> Lemma (requires (m_contains h m /\ rel (m_sel h m) x))
		           (ensures  (m_contains h m /\ rel (m_sel h m) x /\ heap_rel h (m_upd h m x)))
			   [SMTPat (heap_rel h (m_upd h m x))]
let m_lifting_lemma #a #rel h m x = ()


(* The preorder-indexed monad interface for MSTATE *)

val mst_get: unit -> MST heap (fun _ -> True) (fun h0 h h1 -> h0 == h /\ h == h1)
let mst_get () = MSTATE?.get_st ()

val mst_put: h:heap -> MST unit (fun h0 -> heap_rel h0 h) (fun _ _ h1 -> h == h1)
let mst_put h = MSTATE?.put_st h

abstract type mst_witnessed (p:predicate heap{stable heap_rel p}) = True

val mst_witness: p:predicate heap{stable heap_rel p} -> MST unit (fun h0 -> p h0) (fun h0 _ h1 -> h0 == h1 /\ mst_witnessed p)
let mst_witness p = ()

val mst_recall: p:predicate heap{stable heap_rel p} -> MST unit (fun _ -> mst_witnessed p) (fun h0 _ h1 -> h0 == h1 /\ p h1)
let mst_recall p = admit () //intentional (justified by metatheory)


(* Monotonic references and operations on them *)

abstract let mref (a:Type) (rel:preorder a) = m:mmref a rel{mst_witnessed (fun h -> m_contains h m)}

let as_mref (#a:Type) (#rel:preorder a) (m:mref a rel) :GTot (FStar.Monotonic.Heap.mref a rel) = m_as_mref m

let as_mmref (#a:Type) (#rel:preorder a) (m:mref a rel) :GTot (mmref a rel) = m

let contains (#a:Type) (#rel:preorder a) (h:heap) (m:mref a rel) = contains h (as_mref m)

let addr_of (#a:Type) (#rel:preorder a) (m:mref a rel) :GTot nat = addr_of (as_mref m)

let sel (#a:Type) (#rel:preorder a) (h:heap) (m:mref a rel) :GTot a = sel h (as_mref m)

let upd (#a:Type) (#rel:preorder a) (h:heap) (m:mref a rel) (x:a{upd_condition h (as_mref m) x}) :GTot heap = upd h (as_mref m) x


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

val read: #a:Type
       -> #rel:preorder a
       -> m:mref a rel
       -> MST a
              (requires (fun h -> True))
              (ensures  (fun h0 v h1 -> h0 == h1 /\ v == sel h0 m))
let read #a #rel m 
  = let h = mst_get () in
    mst_recall (fun h -> contains h m);
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
    mst_recall (fun h -> contains h m);
    let h1 = FStar.Monotonic.Heap.upd_tot h0 m x in
    assert (h1 == upd h0 m x);
    mst_put h1


(*type fresh(#a:Type) (#rel:preorder a) (x:a) h0 (m:mref a rel) h1 = 
  ~ (contains h0 m) /\ contains h1 m /\ h1 == upd h0 m x

val alloc: #a:Type
        -> #rel:preorder a
        -> x:a
        -> MST (mref a rel)
              (requires (fun _ -> True))
              (fun h0 m h1 -> fresh x h0 m h1)
let alloc #a #rel x 
  = let h0 = mst_get () in
    //let mh = alloc h0 x rel false in 
    admit () //ST.alloc x*)


(*

let stable (#a:Type) (p:predicate a) (rel:preorder a) = stable_rel rel p

abstract type token (#a:Type) (#rel:preorder a) (m:mref a rel) (p:predicate a{stable p rel}) = True
abstract type witnessed (p:heap -> Type) = True

type fresh(#a:Type) (#rel:preorder a) (x:a) h0 (m:mref a rel) h1 = 
  ~ (contains h0 m) /\ contains h1 m /\ h1==upd h0 m x

val alloc: #a:Type
        -> #rel:preorder a
        -> x:a
        -> ST (mref a rel)
              (requires (fun _ -> True))
              (fun h0 m h1 -> fresh x h0 m h1)
let alloc #a #rel x = ST.alloc x

val read: #a:Type
       -> #rel:preorder a
       -> x:mref a rel
       -> ST a
            (requires (fun h -> True))
            (ensures (fun h0 v h1 -> h0==h1 /\ v==sel h0 x))
let read #a #b x = !x

val write: #a:Type
        -> #rel:preorder a
        -> x:mref a rel
        -> v:a
        -> ST unit
              (requires (fun h0 -> rel (sel h0 x) v))
              (ensures (fun h0 _ h1 -> h1==upd h0 x v))
let write #a #b x v = x := v

val take_token: #a:Type
          -> #rel:preorder a
          -> m:mref a rel
          -> p:(a -> Type)
          -> ST unit
                (requires (fun h0 -> p (sel h0 m) /\ stable p rel))
                (ensures (fun h0 _ h1 -> h0==h1 /\ token m p))
let take_token #a #rel m p = ()

assume val recall_token: #a:Type
                     -> #b:reln a
                     -> m:mref a b
                     -> p:(a -> Type)
                     -> ST unit
                       (requires (fun _ ->  token m p))
                       (ensures (fun h0 _ h1 -> h0==h1 /\ p (sel h1 m)))

let stable_on_heap (#a:Type) (#b:reln a) (r:mref a b) (p:(heap -> Type)) = 
  forall h0 h1. p h0 /\ b (sel h0 r) (sel h1 r) ==> p h1
  
assume val recall: p:(heap -> Type)
                -> ST unit
                      (requires (fun _ ->  witnessed p))
                      (ensures (fun h0 _ h1 -> p h1))

val witness: #a:Type
          -> #b:reln a
          -> m:mref a b
          -> p:(heap -> Type)
          -> ST unit
                (requires (fun h0 -> p h0 /\ stable_on_heap m p))
                (ensures (fun h0 _ h1 -> h0==h1 /\ witnessed p))
let witness #a #b m p = ()*)


