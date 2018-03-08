module SL.Examples

open SepLogic.Heap
open SL.Effect

open FStar.Tactics

let lemma_read_write (phi:heap -> heap -> Type0) (r:ref int) (h:heap)
  :Lemma (requires h `contains` r /\ phi (restrict h r) (minus h r))
         (ensures (exists (h0:heap) (h1:heap). disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\
	                                  (exists (x:int). (r |> x) h0) /\ phi h0 h1))
  = assume (disjoint_heaps (restrict h r) (minus h r));
    assume (h == join_tot (restrict h r) (minus h r));
    assume (exists x. (r |> x) (restrict h r))


//#set-options "--ugly"
let write_read (r:ref int) =
  (r := 2;
   !r)
  
  <: STATE int (fun p h2 -> (r |> 1) h2 ==> (forall h3. (r |> 2) h3 ==> p 2 h3))

  by (fun () -> let t1 = forall_intro () in
             let t2 = forall_intro () in
	     let t3 = implies_intro () in
	     let _ = apply_lemma (`lemma_read_write) in
	     dump "after")
