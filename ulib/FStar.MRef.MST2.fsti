module FStar.MRef.MST2

open FStar.Monotonic.Heap
open FStar.ST

open FStar.Preorder

module MH = FStar.Monotonic.Heap

(* The underlying ordinary state monad of the preorder-indexed MSTATE effect *)

private let st (a:Type) = heap -> M (a * heap)

private let return_st (a:Type) (x:a) : st a = fun h0 -> x, h0

private let bind_st (a:Type) (b:Type) (f:st a) (g:a -> st b) : st b
          = fun (h0:heap) -> let (x,h) = f h0 in g x h

total new_effect {
  MSTATE : a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
     //hiding the underlying get and put operations
}

(* Pre- and postcondition form of MSTATE *)

let st_pre = heap -> Type0
let st_post a = a -> heap -> Type0

effect MST (a:Type) (pre:st_pre) (post: (heap -> Tot (st_post a))) =
       MSTATE a
             (fun (h0:heap) (p:(a * heap) -> Type0) -> pre h0 /\ (forall a h1. post h0 a h1 ==> p (a, h1)))
