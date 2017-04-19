module FStar.MRef.MST2

open FStar.Monotonic.Heap
open FStar.ST

module MH = FStar.Monotonic.Heap

(* The underlying ordinary state monad of the preorder-indexed MSTATE effect *)

(*private let sti (a:Type) = heap -> M (a * heap)

private let return_sti (a:Type) (x:a) : sti a = fun h0 -> x, h0

private let bind_sti (a:Type) (b:Type) (f:sti a) (g:a -> sti b) : sti b
          = fun (h0:heap) -> let (x,h) = f h0 in g x h

total new_effect {
  MSTATE : a:Type -> Effect
  with repr     = sti
     ; bind     = bind_sti
     ; return   = return_sti
     //hiding the underlying get and put operations
}

(* Pre- and postcondition form of MSTATE *)

let st_pre = heap -> Type0
let st_post a = a -> heap -> Type0

effect MST (a:Type) (pre:st_pre) (post: (heap -> Tot (st_post a))) =
       MSTATE a
             (fun (h0:heap) (p:(a * heap) -> Type0) -> pre h0 /\ (forall a h1. post h0 a h1 ==> p (a, h1)))
*)
