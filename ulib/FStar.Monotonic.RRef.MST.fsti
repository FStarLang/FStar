module FStar.Monotonic.RRef.MST

open FStar

open FStar.HyperHeap
open FStar.HyperStack

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

open FStar.Preorder

(* The underlying ordinary state monad of the preorder-indexed MSTATE effect *)

private let st (a:Type) = mem -> M (a * mem)

private let return_st (a:Type) (x:a) : st a = fun m0 -> x, m0

private let bind_st (a:Type) (b:Type) (f:st a) (g:a -> st b) : st b
          = fun (m0:mem) -> let (x,m) = f m0 in g x m

total new_effect {
  MSTATE : a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
     //hiding the standard get and put operations
}

(* Pre- and postcondition form of MSTATE *)

let st_pre = mem -> Type0
let st_post a = a -> mem -> Type0

effect MST (a:Type) (pre:st_pre) (post: (mem -> Tot (st_post a))) =
       MSTATE a
             (fun (m0:mem) (p:(a * mem) -> Type0) -> pre m0 /\ (forall a m1. post m0 a m1 ==> p (a, m1)))
