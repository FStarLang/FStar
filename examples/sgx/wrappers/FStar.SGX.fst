module FStar.SGX

open FStar.HyperHeap
open FStar.HyperStack


(**
   Effect of heap-based code.
   - assumes that the stack is empty (tip = root)
   - corresponds to the HyperHeap ST effect
   - can call to Stack and ST code freely
   - respects the stack invariant: the stack has to be empty when returning
   - Only u_heap and UV_shared_buf are modified
*)
effect Wrapper (a:Type) (pre:st_pre) (post: (mem -> Tot (st_post a))) =
       STATE a
             (fun (p:st_post a) (h:mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1 /\ h.tip = HH.root /\ h1.tip = HH.root ) ==> p a h1)) (* WP *)

