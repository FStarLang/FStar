module FStar.Monotonic.RRef.MST

open FStar

open FStar.HyperHeap
open FStar.HyperStack

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

open FStar.Preorder

(* Defining the underlying state monad on mem using DM4F *)

let st (a:Type) = mem -> M (a * mem)

let return_st (a:Type) (x:a) : st a = fun m0 -> x, m0

let bind_st (a:Type) (b:Type) (f:st a) (g:a -> st b) : st b
  = fun (m0:mem) -> let (x,m) = f m0 in g x m

(* Actions *)
let get_st () : st mem = fun m0 -> m0, m0

let put_st (x:mem) : st unit = fun _ -> (), x

total new_effect {
  MSTATE : a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
     ; get      = get_st
     ; put      = put_st
}

(* Monotonic references *)

type rid = r:HH.rid{is_eternal_region r}

abstract type m_rref (r:rid) (a:Type) (rel:preorder a) = x:HS.ref a{x.id = r}

val as_hsref: #r:rid -> #a:Type -> #rel:preorder a -> m_rref r a rel -> GTot (x:HS.ref a{x.id = r})
let as_hsref #r #a #rel x = x

let m_contains (#r:rid) (#a:Type) (#rel:preorder a) (mr:m_rref r a rel) (m:mem) = HS.contains m (as_hsref mr)

let m_fresh (#r:rid) (#a:Type) (#rel:preorder a) (mr:m_rref r a rel) (m0:mem) (m1:mem) : GTot Type0 =
  let hsref = as_hsref mr in
  HyperHeap.fresh_rref hsref.ref m0.h m1.h

val m_sel: #r:rid -> #a:Type -> #rel:preorder a -> h:mem -> m_rref r a rel -> GTot a
let m_sel #r #a #rel h m = HS.sel h (as_hsref m)

(* Preorder on memories *)

let m_rel (m0:mem) (m1:mem) 
  = forall r a rel (mr:m_rref r a rel) . 
      (contains m0 mr ==> contains m1 mr) 
   /\ (contains m0 mr ==> rel (sel m0 mr) (sel m1 mr))


(* The preorder-indexed monad interface for MSTATE *)

val get: unit -> MST mem (fun _ -> True) (fun m0 m m1 -> m0 == m /\ m == m1)
let get () = MSTATE?.get ()

val put: m:mem -> MST unit (fun m0 -> m_rel m0 m) (fun _ _ m1 -> m == m1)
let put m = MSTATE?.put m

abstract type witnessed (p:predicate mem{stable m_rel p}) = True

val witness: p:predicate mem{stable m_rel p} -> MST unit (fun m0 -> p m0) (fun m0 _ m1 -> m0 == m1 /\ witnessed p)
let witness p = ()

val recall: p:predicate mem{stable m_rel p} -> MST unit (fun _ -> witnessed p) (fun m0 _ m1 -> m0 == m1 /\ p m1)
let recall p = admit () //intentional (justified by metatheory)


