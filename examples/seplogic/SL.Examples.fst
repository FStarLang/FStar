module SL.Examples

open SepLogic.Heap
open SL.Effect

open FStar.Tactics

let lemma_rw_rw (phi:heap -> heap -> int -> Type0) (r:ref int) (x:int) (h:heap)
  :Lemma (requires (phi (r |> x) h x))
         (ensures  (exists h0 h1. ((r |> x) <*> h) == (h0 <*> h1) /\ (exists x. h0 == (r |> x) /\ phi h0 h1 x)))
  = ()

let lemma_rw_bind (phi:heap -> heap -> heap -> heap -> int -> Type0) (r:ref int) (x:int) (h:heap)
  :Lemma (requires (phi ((r |> x) <*> h) emp (r |> x) h x))
         (ensures  (exists h0 h1. ((r |> x) <*> h) == (h0 <*> h1) /\
	                     (exists h3 h4. h0 == (h3 <*> h4) /\ (exists x. h3 == (r |> x) /\ phi h0 h1 h3 h4 x))))

  
  = ()

#set-options "--print_full_names"

let lemma_rewrite_sep_comm (h1 h2:heap) (phi:heap -> heap -> heap -> heap -> Type0)
  :Lemma (requires (exists h3 h4. (h1 <*> h2) == (h3 <*> h4) /\ phi h1 h2 h3 h4))
         (ensures  (exists h3 h4. (h2 <*> h1) == (h3 <*> h4) /\ phi h1 h2 h3 h4))
  = sep_comm h1 h2

let prelude () :Tac unit =
  let _ = forall_intros () in  //forall (p:post) (h:heap)
  let h = implies_intro () in  //the annotated wp
  and_elim (pack (Tv_Var h));  //break it into conjuncts
  clear h;
  ignore (repeat (fun _ -> let h = implies_intro () in
                        or_else (fun _ -> rewrite h) idtac))  //introduce the conjuncts into the context, but rewrite in the goal before doing that, specifically we want the initial heap expression to be inlined in the goal
  
let write_read (r:ref int) (s:ref int) (n:int) (m:int) =
  (r := 2;
   !s)
  
  <: STATE int (fun p h -> h == ((r |> n) <*> (s |> m)) /\ p m ((r |> 2) <*> (s |> m)))

  by (fun () -> prelude ();
	     apply_lemma (`lemma_rw_rw);
	     apply_lemma (`lemma_rewrite_sep_comm);
	     apply_lemma (`lemma_rw_rw))

let swap (r1 r2:ref int) (m n:int) =
  (let x = !r1 in
   let y = !r2 in
   r1 := y;
   r2 := x)

  <: STATE unit (fun post h -> h == ((r1 |> m) <*> (r2 |> n)) /\ post () ((r1 |> n) <*> (r2 |> m)))

  by (fun () -> prelude ();
             apply_lemma (`lemma_rw_rw);
	     apply_lemma (`lemma_rewrite_sep_comm);
	     apply_lemma (`lemma_rw_bind);
	     apply_lemma (`lemma_rewrite_sep_comm);
	     apply_lemma (`lemma_rw_bind);
	     apply_lemma (`lemma_rewrite_sep_comm);
	     apply_lemma (`lemma_rw_rw))
