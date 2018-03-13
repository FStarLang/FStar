module SL.Examples

//open SepLogic.Heap
open SL.Effect

open FStar.Tactics

(*** command specific lemmas ***)

(*
 * these lemmas match on the VCs
 *)

(*
 * a read/write command followed by a read/write command with singleton heap
 *)
let lemma_singleton_heap_rw_rw (#a:Type0) (phi:memory -> memory -> a -> Type0) (r:ref a) (x:a)
  :Lemma (requires (phi (r |> x) emp x))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\
	                              (r |> x) == (h0 <*> h1) /\ (exists x. h0 == (r |> x) /\ phi h0 h1 x)))
  = ()

(*
 * a read/write command followed by a read/write command
 *)
let lemma_rw_rw (#a:Type0) (phi:memory -> memory -> a -> Type0) (r:ref a) (x:a) (h:memory)
  :Lemma (requires (defined ((r |> x) <*> h) /\ phi (r |> x) h x))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\
	                              ((r |> x) <*> h) == (h0 <*> h1) /\ (exists x. h0 == (r |> x) /\ phi h0 h1 x)))
  = ()

(*
 * a read/write command followed by a bind with singleton heap
 *)
let lemma_singleton_heap_rw_bind (#a:Type0) (phi:memory -> memory -> memory -> memory -> a -> Type0) (r:ref a) (x:a)
  :Lemma (requires (phi (r |> x) emp (r |> x) emp x))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ (r |> x) == (h0 <*> h1) /\
	                              (exists (h3 h4:memory). defined (h3 <*> h4) /\ h0 == (h3 <*> h4) /\ (exists x. h3 == (r |> x) /\ phi h0 h1 h3 h4 x))))  
  = ()

(*
 * a read/write command followed by a bind
 *)
let lemma_rw_bind (#a:Type0) (phi:memory -> memory -> memory -> memory -> a -> Type0) (r:ref a) (x:a) (h:memory)
  :Lemma (requires (defined (((r |> x) <*> h) <*> emp) /\ phi ((r |> x) <*> h) emp (r |> x) h x))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ ((r |> x) <*> h) == (h0 <*> h1) /\
	                              (exists (h3 h4:memory). defined (h3 <*> h4) /\ h0 == (h3 <*> h4) /\ (exists x. h3 == (r |> x) /\ phi h0 h1 h3 h4 x))))  
  = ()

(*
 * pure expression at the end
 *)
let lemma_pure_right (h h':memory) (phi:memory -> memory -> memory -> Type0)
  :Lemma (requires (defined (h <*> h') /\ phi h h' (h <*> h')))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ (h <*> h') == (h0 <*> h1) /\ phi h h' h1))
  = lemma_join_is_commutative (h <*> h') emp

(*
 * procedure call followed by a read/write command with singleton heap
 *)
let lemma_singleton_heap_procedure_rw (#a:Type0) (phi:memory -> memory -> a -> Type0)
		                 (r:ref a) (x:a)
  :Lemma (requires (phi (r |> x) emp x))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ (r |> x) == (h0 <*> h1) /\
	                     (h0 == (r |> x) /\ phi h0 h1 x)))
  = ()

(*
 * procedure call followed by a read/write command
 *)
let lemma_procedure_rw (phi:memory -> memory -> memory -> memory -> Type0)
		       (h h':memory)
  :Lemma (requires (defined (h <*> h') /\ phi h h' h h'))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ (h <*> h') == (h0 <*> h1) /\
	                     (h0 == h /\ phi h h' h0 h1)))
  = ()

(*
 * procedure call followed by a bind with singleton heap
 *)
let lemma_singleton_heap_procedure_bind
  (#a:Type0) (phi:memory -> memory -> memory -> memory -> a -> Type0)
  (r:ref a) (x:a)
  :Lemma (requires (phi (r |> x) emp (r |> x) emp x))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ (r |> x) == (h0 <*> h1) /\
	                     (exists (h3 h4:memory). defined (h3 <*> h4) /\ h0 == (h3 <*> h4) /\ (h3 == (r |> x) /\ phi h0 h1 h3 h4 x))))
  = ()

(*
 * procedure call followed by a bind
 *)
let lemma_procedure_bind (phi:memory -> memory -> memory -> memory -> memory -> memory -> Type0)
                         (h h':memory)
  :Lemma (requires (defined (h <*> h') /\ phi h h' (h <*> h') emp h h'))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ (h <*> h') == (h0 <*> h1) /\
	                     (exists (h3 h4:memory). defined (h3 <*> h4) /\ h0 == (h3 <*> h4) /\ (h3 == h /\ phi h h' h0 h1 h3 h4))))
  = ()

let lemma_procedure (phi:memory -> memory -> memory -> memory -> Type0) (h h':memory)
  :Lemma (requires (defined (h <*> h') /\ phi h h' h h'))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ (h <*> h') == (h0 <*> h1) /\ (h0 == h /\ phi h h' h0 h1)))
  = ()

(*** command specific lemmas end ***)

(*** following are heap algebra lemmas, should be replaced with canonizer? ***)

let lemma_rewrite_sep_comm (h1 h2:memory) (phi:memory -> memory -> memory -> memory -> Type0)
  :Lemma (requires (exists (h3 h4:memory). defined (h3 <*> h4) /\ (h1 <*> h2) == (h3 <*> h4) /\ phi h1 h2 h3 h4))
         (ensures  (exists (h3 h4:memory). defined (h3 <*> h4) /\ (h2 <*> h1) == (h3 <*> h4) /\ phi h1 h2 h3 h4))
  = lemma_join_is_commutative h1 h2

let lemma_rewrite_sep_assoc1 (h1 h2 h3:memory) (phi:memory -> memory -> memory -> memory -> memory -> Type0)
  :Lemma (requires (exists (h4 h5:memory). defined (h4 <*> h5) /\ (h2 <*> (h1 <*> h3)) == (h4 <*> h5) /\
	                     phi h1 h2 h3 h4 h5))
         (ensures  (exists (h4 h5:memory). defined (h4 <*> h5) /\ (h1 <*> (h2 <*> h3)) == (h4 <*> h5) /\
	                     phi h1 h2 h3 h4 h5))
  = lemma_join_is_commutative h1 h2

let lemma_rewrite_sep_assoc2 (h1 h2 h3:memory) (phi:memory -> memory -> memory -> memory -> memory -> Type0)
  :Lemma (requires (exists (h4 h5:memory). defined (h4 <*> h5) /\ (h3 <*> (h1 <*> h2)) == (h4 <*> h5) /\
	                     phi h1 h2 h3 h4 h5))
         (ensures  (exists (h4 h5:memory). defined (h4 <*> h5) /\ (h1 <*> (h2 <*> h3)) == (h4 <*> h5) /\
	                     phi h1 h2 h3 h4 h5))
  = lemma_join_is_commutative h3 h1;
    lemma_join_is_commutative h3 h2

let lemma_rewrite_sep_assoc3 (h1 h2 h3:memory) (phi:memory -> memory -> memory -> memory -> memory -> Type0)
  :Lemma (requires (exists (h4 h5:memory). defined (h4 <*> h5) /\ ((h1 <*> h2) <*> h3) == (h4 <*> h5) /\
	                     phi h1 h2 h3 h4 h5))
         (ensures  (exists (h4 h5:memory). defined (h4 <*> h5) /\ (h1 <*> (h2 <*> h3)) == (h4 <*> h5) /\
	                     phi h1 h2 h3 h4 h5))
  = ()

let lemma_rewrite_sep_assoc4 (h1 h2 h3:memory) (phi:memory -> memory -> memory -> memory -> memory -> Type0)
  :Lemma (requires (exists (h4 h5:memory). defined (h4 <*> h5) /\ (h1 <*> (h2 <*> h3)) == (h4 <*> h5) /\
	                     phi h1 h2 h3 h4 h5))
         (ensures  (exists (h4 h5:memory). defined (h4 <*> h5) /\ ((h1 <*> h2) <*> h3) == (h4 <*> h5) /\
	                     phi h1 h2 h3 h4 h5))
  = ()

(*** heap algebra lemmas end ***)


(*** examples begin ***)

(*
 * preprocess the VC by moving foralls and implies into the context
 * when we move implies, we break the conjuncts, and inline initial heap in the VC
 *)
let prelude () :Tac unit =
  let _ = forall_intros () in  //forall (p:post) (h:heap)
  let aux () =
    let h = implies_intro () in
    and_elim (pack (Tv_Var (fst (inspect_binder h))));
    clear h
  in
  ignore (repeat aux);  //(a /\ b) ==> c --> a ==> b ==> c, repeat to account for nested conjuncts
  ignore (repeat (fun _ -> let h = implies_intro () in
                        or_else (fun _ -> rewrite h) idtac))  //introduce the conjuncts into the context, but rewrite in the goal before doing that, specifically we want the initial heap expression to be inlined in the goal

private let rec apply_lemmas (l:list term) :Tac unit
  = match l with
    | []    -> fail "no command lemma matched the goal"
    | hd::tl -> or_else (fun () -> apply_lemma hd) (fun () -> apply_lemmas tl)

private let process_command () :Tac unit
  = apply_lemmas [`lemma_singleton_heap_rw_rw;
                  `lemma_rw_rw;
		  `lemma_singleton_heap_rw_bind;
		  `lemma_rw_bind;
		  `lemma_singleton_heap_procedure_rw;
		  `lemma_procedure_rw;
		  `lemma_singleton_heap_procedure_bind;
		  `lemma_procedure_bind;
		  `lemma_procedure;
		  `lemma_pure_right]

(*
 * TODO: use it from Derived
 *)
private val split_lem : (#a:Type) -> (#b:Type) ->
                        squash a -> squash b -> Lemma (a /\ b)
let split_lem #a #b sa sb = ()

private let get_to_the_next_frame () :Tac unit =
  ignore (repeat (fun () -> apply_lemma (`split_lem); smt ()))

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0 --use_two_phase_tc false --print_full_names"


(*
 * main idea for the examples:
 *   call process_command for each command, currently the ordering of the heap is manual
 *)

(*
 * two commands
   *)
 let write_read (r:ref int) (s:ref int) (n:int) (m:int) =
  (r := 2;
   !s)
  
  <: STATE int (fun p h -> h == ((r |> n) <*> (s |> m)) /\ (defined h /\ p m ((r |> 2) <*> (s |> m))))

  by (fun () ->
      prelude ();
      process_command ();
      get_to_the_next_frame ();
      apply_lemma (`lemma_rewrite_sep_comm);
      process_command ())

(*
 * four commands
 *)
let swap (r1 r2:ref int)
  = (let x = !r1 in
     let y = !r2 in
     r1 := y;
     r2 := x)

     <: STATE unit (fun post h -> h == ((r1 |> m) <*> (r2 |> n)) /\ (defined h /\ post () ((r1 |> n) <*> (r2 |> m))))

     by (fun () -> prelude ();
                process_command ();
	        get_to_the_next_frame ();
	        apply_lemma (`lemma_rewrite_sep_comm);
	        process_command ();
	        get_to_the_next_frame ();
	        apply_lemma (`lemma_rewrite_sep_comm);
	        process_command ();
	        get_to_the_next_frame ();
	        apply_lemma (`lemma_rewrite_sep_comm);
                process_command ())

(*
 * three commands, the inline pure expressions don't count
 *)
let incr (r:ref int) (n:int)
  = (let y = !r in
     let z = y + 1 in
     r := z;
     !r)

     <: STATE int (fun post h -> h == (r |> n) /\ (defined h /\ post (n + 1) (r |> n + 1)))

     by (fun () -> prelude ();
                process_command ();
		get_to_the_next_frame ();
		process_command ();
		get_to_the_next_frame ();
		process_command ())

(*
 * checking procedure calls below
 * for the procedures, we assume their heap footprints as part of their spec,
 *   e.g. in incr and swap above (and it should be the first thing in the spec)
 *)
(*
 * 2 commands + one at the end
 *)
let incr2 (r:ref int) (n:int)
  = (let n = incr r n in
     incr r n)

    <: STATE int (fun post h -> h == (r |> n) /\ (defined h /\ post (n + 2) (r |> n + 2)))

    by (fun () -> prelude ();
               process_command ();
	       get_to_the_next_frame ();
	       process_command ())

(*
 * 3 commands + one at the end
 *)
#set-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0 --initial_fuel 0 --initial_ifuel 0"
let rotate (r1 r2 r3:ref int) (l m n:int) =
  (swap r2 r3 m n;
   swap r1 r2 l n;
   let x = !r1 in
   x)
   
  <: STATE int (fun post h -> h == ((r1 |> l) <*> ((r2 |> m) <*> (r3 |> n))) /\
                         (defined h /\ post n ((r1 |> n) <*> ((r2 |> l) <*> (r3 |> m)))))

  by (fun () -> prelude ();
             apply_lemma (`lemma_rewrite_sep_comm);
	     process_command ();
	     get_to_the_next_frame ();
	     apply_lemma (`lemma_rewrite_sep_comm);
	     apply_lemma (`lemma_rewrite_sep_assoc3);
	     process_command ();
	     get_to_the_next_frame ();
	     apply_lemma (`lemma_rewrite_sep_assoc4);
	     process_command ();
	     get_to_the_next_frame ();
	     process_command ())
