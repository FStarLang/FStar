module FStar.MRef.MST2

open FStar.Monotonic.Heap

module MH = FStar.Monotonic.Heap

(* Preordered relations and stable predicates *)

let relation (a:Type) = a -> a -> Type0

let predicate (a:Type) = a -> Type0

let preorder_rel (#a:Type) (rel:relation a) = 
  (forall x . rel x x) /\ (forall x y z . rel x y /\ rel y z ==> rel x z)

let preorder (a:Type) = rel:relation a{preorder_rel rel}

let stable (#a:Type) (rel:relation a{preorder_rel rel}) (p:predicate a) =
  forall x y . p x /\ rel x y ==> p y
  

(* Defining the underlying state monad on mem using DM4F *)

let st (a:Type) = heap -> M (a * heap)

let return_st (a:Type) (x:a) : st a = fun h0 -> x, h0

let bind_st (a:Type) (b:Type) (f:st a) (g:a -> st b) : st b
  = fun (h0:heap) -> let (x,h) = f h0 in g x h

(* Actions *)
let get_st () : st heap = fun h0 -> h0, h0

let put_st (x:heap) : st unit = fun _ -> (), x

total new_effect {
  MSTATE : a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
     ; get      = get_st
     ; put      = put_st
}

//let reln (a:Type) = a -> a -> Type

//let monotonic (a:Type) (b:reln a) =
//  (forall x. b x x)                             (* reflexive *)
//  /\ (forall x y z. b x y /\ b y z ==> b x z)   (* transitive *)

abstract let mref (a:Type) (rel:preorder a) = MH.mref a rel

val as_mref: #a:Type -> #rel:preorder a -> mref a rel -> GTot (mref a rel)
let as_mref #a #rel m = m

let contains (#a:Type) (#rel:preorder a) (h:heap) (m:mref a rel) = MH.contains h (as_mref m)

val sel: #a:Type -> #rel:preorder a -> h:heap -> mref a rel -> GTot a
let sel #a #rel h m = MH.sel h (as_mref m)

val upd: #a:Type -> #rel:preorder a -> h:heap -> (m:mref a rel) -> (x:a{rel (sel h m) x}) -> GTot heap
let upd #a #rel h m v = MH.upd h (as_mref m) v


(* Generated preorder on heaps *)

let heap_rel (h0:heap) (h1:heap) 
  = (forall a rel (m:mref a rel) . (contains h0 m ==> contains h1 m) )
 /\ (forall a rel (m:mref a rel) . (contains h0 m ==> rel (sel h0 m) (sel h1 m)))

val lemma1: (a:Type)
         -> (rel: preorder a)
         -> (h:heap)
         -> (m:mref a rel)
         -> (x:a)
	 -> Lemma (requires (contains h m /\ rel (sel h m) x))
	          (ensures  (rel (sel h m) x /\ (forall b rel' (m':mref b rel') . contains h m' ==> contains (upd h m x) m')))
let lemma1 a rel h m x = ()

val lemma2: (a:Type)
         -> (rel: preorder a)
         -> (h:heap)
         -> (m:mref a rel)
         -> (x:a)
	 -> Lemma (requires (contains h m /\ rel (sel h m) x))
	          (ensures  (rel (sel h m) x /\ (forall b rel' (m':mref b rel') . addr_of m <> addr_of m' /\ contains h m' ==> rel' (sel h m') (sel (upd h m x) m'))))
let lemma2 a rel h m x = ()

val lemma3: (a:Type)
         -> (rel: preorder a)
         -> (h:heap)
         -> (m:mref a rel)
         -> (x:a)
	 -> Lemma (requires (contains h m /\ rel (sel h m) x))
	          (ensures  (rel (sel h m) x /\ sel (upd h m x) m == x))
let lemma3 a rel h m x = ()

val lemma4: (a:Type)
         -> (rel: preorder a)
         -> (h:heap)
         -> (m:mref a rel)
         -> (x:a)
	 -> Lemma (requires (contains h m /\ rel (sel h m) x))
	          (ensures  (contains h m /\ rel (sel h m) x /\ (forall b rel' (m':mref b rel') . addr_of m = addr_of m' /\ contains h m' ==> rel' (sel h m') (sel (upd h m x) m'))))
let lemma4 a rel h m x = ()

val lifting_lemma: (a:Type) 
                -> (rel:preorder a) 
	        -> (m:mref a rel) 
	        -> (h:heap)
	        -> (x:a)
	        -> Lemma (requires (contains h m /\ rel (sel h m) x))
		         (ensures  (contains h m /\ rel (sel h m) x /\ heap_rel h (upd h m x)))
let lifting_lemma a rel m h x = ()


(* The preorder-indexed monad interface for MSTATE *)

(*val mst_get: unit -> MST heap (fun _ -> True) (fun h0 h h1 -> h0 == h /\ h == h1)
let mst_get () = MSTATE?.get ()

val mst_put: h:heap -> MST unit (fun h0 -> h_rel h0 h) (fun _ _ h1 -> h == h1)
let mst_put h = MSTATE?.put h

abstract type mst_witnessed (p:predicate heap{stable h_rel p}) = True

val mst_witness: p:predicate heap{stable h_rel p} -> MST unit (fun h0 -> p h0) (fun h0 _ h1 -> h0 == h1 /\ mst_witnessed p)
let mst_witness p = ()

val mst_recall: p:predicate heap{stable h_rel p} -> MST unit (fun _ -> mst_witnessed p) (fun h0 _ h1 -> h0 == h1 /\ p h1)
let mst_recall p = admit () //intentional (justified by metatheory)*)





(*
let stable (#a:Type) (p:predicate a) (rel:preorder a) = FStar.Preorder.stable rel p

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
