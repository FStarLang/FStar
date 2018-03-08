module SL.Examples

open SepLogic.Heap
open SL.Effect

open FStar.Tactics

let lemma_read_write (phi:heap -> heap -> Type0) (r:ref int) (h:heap)
  :Lemma (requires (h `contains` r /\ phi (restrict h r) (minus h r)))
         (ensures (exists (h0:heap) (h1:heap). 
                    (disjoint_heaps h0 h1 /\ h == join_tot h0 h1) /\
	            ((exists (x:int). (r |> x) h0) /\ phi h0 h1)))
  = disjoint_heaps_restrict_minus r h;
    join_tot_restrict_minus r h;
    restrict_points_to r h

//#set-options "--ugly"

let write_read (r:ref int) =
  (r := 2;
   !r)
  
  <: STATE int (fun p h2 -> (exists x. (r |> x) h2) /\ 
                            (forall h3. (r |> 2) h3 ==> p 2 h3))

  by (fun () -> 
             let _ = forall_intro () in
             let _ = forall_intro () in
	     let _ = implies_intro () in
	     let _ = apply_lemma (`lemma_read_write) in
	     split ();
	     smt ();
	     //dump "Before";
	     let _ = forall_intro () in
	     let _ = implies_intro () in
	     split ();
	     smt ();
	     let _ = apply_lemma (`lemma_read_write) in
	     split ();
	     smt ();
	     let _ = forall_intro () in
             let _ = implies_intro () in
             split ();
             //let _ = apply_lemma (`disjoint_heaps_restrict_minus) in 
	     dump "After")
