module SL.Examples

open SL.Effect

open FStar.Tactics

let lemma_rw_rw (phi:memory -> memory -> int -> Type0) (r:ref int) (x:int) (h:memory)
  :Lemma (requires (defined ((r |> x) <*> h) /\ phi (r |> x) h x))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ ((r |> x) <*> h) == (h0 <*> h1) /\ (exists x. h0 == (r |> x) /\ phi h0 h1 x)))
  = ()

let lemma_rw_bind (phi:memory -> memory -> memory -> memory -> int -> Type0) (r:ref int) (x:int) (h:memory)
  :Lemma (requires (defined (((r |> x) <*> h) <*> emp) /\ phi ((r |> x) <*> h) emp (r |> x) h x))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ ((r |> x) <*> h) == (h0 <*> h1) /\
	                              (exists (h3 h4:memory). defined (h3 <*> h4) /\ h0 == (h3 <*> h4) /\ (exists x. h3 == (r |> x) /\ phi h0 h1 h3 h4 x))))  
  = ()

let lemma_pure (h h':memory) (phi:memory -> memory -> memory -> memory -> Type0)
  :Lemma (requires (defined (h <*> h') /\ phi h h' emp (h <*> h')))
         (ensures  (exists h0 h1. defined (h0 <*> h1) /\ (h <*> h') == (h0 <*> h1) /\ phi h h' h0 h1))
  = ()

let lemma_procedure_rw (phi:memory -> memory -> memory -> memory -> Type0)
		       (h h':memory)
  :Lemma (requires (defined (h <*> h') /\ phi h h' h h'))
         (ensures  (exists h0 h1. defined (h0 <*> h1) /\ (h <*> h') == (h0 <*> h1) /\
	                     (h0 == h /\ phi h h' h0 h1)))
  = ()

let lemma_procedure_bind (phi:memory -> memory -> memory -> memory -> memory -> memory -> Type0)
                         (h h':memory)
  :Lemma (requires (defined (h <*> h') /\ phi h h' (h <*> h') emp h h'))
         (ensures  (exists h0 h1. defined (h0 <*> h1) /\ (h <*> h') == (h0 <*> h1) /\
	                     (exists h3 h4. defined (h3 <*> h4) /\ h0 == (h3 <*> h4) /\ (h3 == h /\ phi h h' h0 h1 h3 h4))))
  = ()

let lemma_rewrite_sep_comm (h1 h2:memory) (phi:memory -> memory -> memory -> memory -> Type0)
  :Lemma (requires (exists h3 h4. defined (h3 <*> h4) /\ (h1 <*> h2) == (h3 <*> h4) /\ phi h1 h2 h3 h4))
         (ensures  (exists h3 h4. defined (h3 <*> h4) /\ (h2 <*> h1) == (h3 <*> h4) /\ phi h1 h2 h3 h4))
  = lemma_join_is_commutative h1 h2

let lemma_rewrite_sep_assoc1 (h1 h2 h3:memory) (phi:memory -> memory -> memory -> memory -> memory -> Type0)
  :Lemma (requires (exists h4 h5. defined (h4 <*> h5) /\ (h2 <*> (h1 <*> h3)) == (h4 <*> h5) /\
	                     phi h1 h2 h3 h4 h5))
         (ensures  (exists h4 h5. defined (h4 <*> h5) /\ (h1 <*> (h2 <*> h3)) == (h4 <*> h5) /\
	                     phi h1 h2 h3 h4 h5))
  = ()

let lemma_rewrite_sep_assoc2 (h1 h2 h3:memory) (phi:memory -> memory -> memory -> memory -> memory -> Type0)
  :Lemma (requires (exists h4 h5. defined (h4 <*> h5) /\ (h3 <*> (h1 <*> h2)) == (h4 <*> h5) /\
	                     phi h1 h2 h3 h4 h5))
         (ensures  (exists h4 h5. defined (h4 <*> h5) /\ (h1 <*> (h2 <*> h3)) == (h4 <*> h5) /\
	                     phi h1 h2 h3 h4 h5))
  = ()

let lemma_rewrite_sep_assoc3 (h1 h2 h3:memory) (phi:memory -> memory -> memory -> memory -> memory -> Type0)
  :Lemma (requires (exists h4 h5. defined (h4 <*> h5) /\ ((h1 <*> h2) <*> h3) == (h4 <*> h5) /\
	                     phi h1 h2 h3 h4 h5))
         (ensures  (exists h4 h5. defined (h4 <*> h5) /\ (h1 <*> (h2 <*> h3)) == (h4 <*> h5) /\
	                     phi h1 h2 h3 h4 h5))
  = ()

let lemma_rewrite_sep_assoc4 (h1 h2 h3:memory) (phi:memory -> memory -> memory -> memory -> memory -> Type0)
  :Lemma (requires (exists h4 h5. defined (h4 <*> h5) /\ (h1 <*> (h2 <*> h3)) == (h4 <*> h5) /\
	                     phi h1 h2 h3 h4 h5))
         (ensures  (exists h4 h5. defined (h4 <*> h5) /\ ((h1 <*> h2) <*> h3) == (h4 <*> h5) /\
	                     phi h1 h2 h3 h4 h5))
  = ()

(*
 * (a /\ b) ==> c --> a ==> b ==> c, with proper handling of nested conjuncts
 *)
let implies_intro_with_and_elim () :Tac unit =
  let aux () =
    let h = implies_intro () in
    and_elim (pack (Tv_Var (fst (inspect_binder h))));
    clear h
  in
  ignore (repeat aux)

let prelude () :Tac unit =
  let _ = forall_intros () in  //forall (p:post) (h:heap)
  implies_intro_with_and_elim ();
  ignore (repeat (fun _ -> let h = implies_intro () in
                        or_else (fun _ -> rewrite h) idtac))  //introduce the conjuncts into the context, but rewrite in the goal before doing that, specifically we want the initial heap expression to be inlined in the goal

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0 --use_two_phase_tc false"

let write_read (r:ref int) (s:ref int) (n:int) (m:int) =
  (r := 2;
   !s)
  
  <: STATE int (fun p h -> h == ((r |> n) <*> (s |> m)) /\ (addr_of r <> addr_of s /\ p m ((r |> 2) <*> (s |> m))))

  by (fun () ->
      prelude ();
      apply_lemma (`lemma_rw_rw);
      split (); smt (); split (); smt ();  //farm the definedness goals to smt
      apply_lemma (`lemma_rewrite_sep_comm);
      apply_lemma (`lemma_rw_rw))

let swap (r1 r2:ref int) (m n:int)
  = (let x = !r1 in
     let y = !r2 in
     r1 := y;
     r2 := x)

     <: STATE unit (fun post h -> h == ((r1 |> m) <*> (r2 |> n)) /\ (addr_of r1 <> addr_of r2 /\ post () ((r1 |> n) <*> (r2 |> m))))

     by (fun () -> prelude ();
                apply_lemma (`lemma_rw_rw);
	        split (); smt (); split (); smt ();
	        apply_lemma (`lemma_rewrite_sep_comm);
	        apply_lemma (`lemma_rw_bind);
	        split (); smt (); split (); smt ();
	        apply_lemma (`lemma_rewrite_sep_comm);
	        apply_lemma (`lemma_rw_bind);
	        split (); smt (); split (); smt ();
	        apply_lemma (`lemma_rewrite_sep_comm);
                apply_lemma (`lemma_rw_rw))

unfold let distinct_refs3 (#a:Type) (#b:Type) (#c:Type) (r1:ref a) (r2:ref b) (r3:ref c)
  = addr_of r1 <> addr_of r2 /\ addr_of r2 <> addr_of r3 /\ addr_of r3 <> addr_of r1

let rotate (r1 r2 r3:ref int) (l m n:int) =
  (swap r2 r3 m n;
   swap r1 r2 l n;
   let x = !r1 in
   x)
   
  <: STATE int (fun post h -> h == ((r1 |> l) <*> ((r2 |> m) <*> (r3 |> n))) /\
                         (distinct_refs3 r1 r2 r3 /\ post n ((r1 |> n) <*> ((r2 |> l) <*> (r3 |> m)))))

  by (fun () -> prelude ();
             apply_lemma (`lemma_rewrite_sep_comm);
	     apply_lemma (`lemma_procedure_rw);
	     split (); smt ();
	     split (); smt ();
	     split (); smt ();
	     apply_lemma (`lemma_rewrite_sep_comm);
	     apply_lemma (`lemma_rewrite_sep_assoc3);
	     apply_lemma (`lemma_procedure_bind);
	     split (); smt ();
	     split (); smt ();
	     split (); smt ();
	     apply_lemma (`lemma_rewrite_sep_assoc4);
	     apply_lemma (`lemma_rw_bind);
	     split (); smt ();
	     split (); smt ();
	     apply_lemma (`lemma_pure))
