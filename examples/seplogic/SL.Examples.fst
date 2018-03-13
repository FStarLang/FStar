module SL.Examples

//open SepLogic.Heap
open SL.Effect

open FStar.Tactics

(*** command specific lemmas ***)

(*
 * these lemmas match on the VCs
 *)


let lemma_singleton_heap_rw (#a:Type0) (phi:memory -> memory -> a -> Type0) (r:ref a) (x:a)
  :Lemma (requires (phi (r |> x) emp x))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\
	                              (r |> x) == (h0 <*> h1) /\ (exists x. h0 == (r |> x) /\ phi h0 h1 x)))
  = ()

let lemma_rw (#a:Type0) (phi:memory -> memory -> a -> Type0) (r:ref a) (x:a) (h:memory)
  :Lemma (requires (defined ((r |> x) <*> h) /\ phi (r |> x) h x))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\
	                              ((r |> x) <*> h) == (h0 <*> h1) /\ (exists x. h0 == (r |> x) /\ phi h0 h1 x)))
  = ()

let lemma_bind (phi:memory -> memory -> memory -> memory -> Type0) (h h':memory)
  :Lemma (requires (exists h3 h4. defined (h3 <*> h4) /\ (h <*> h') == (h3 <*> h4) /\ phi (h <*> h') emp h3 h4))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ (h <*> h') == (h0 <*> h1) /\
	                              (exists (h3 h4:memory). defined (h3 <*> h4) /\ h0 == (h3 <*> h4) /\ phi h0 h1 h3 h4)))
  = ()

let lemma_singleton_heap_procedure (#a:Type0) (phi:memory -> memory -> a -> Type0)
		                   (r:ref a) (x:a)
  :Lemma (requires (phi (r |> x) emp x))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ (r |> x) == (h0 <*> h1) /\
	                              (h0 == (r |> x) /\ phi h0 h1 x)))
  = ()

let lemma_procedure (phi:memory -> memory -> memory -> memory -> Type0)
		    (h h':memory)
  :Lemma (requires (defined (h <*> h') /\ phi h h' h h'))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ (h <*> h') == (h0 <*> h1) /\
	                              (h0 == h /\ phi h h' h0 h1)))
  = ()

let lemma_pure_right (h h':memory) (phi:memory -> memory -> memory -> Type0)
  :Lemma (requires (defined (h <*> h') /\ phi h h' (h <*> h')))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ (h <*> h') == (h0 <*> h1) /\ phi h h' h1))
  = lemma_join_is_commutative (h <*> h') emp

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

private let rec apply_lemmas (l:list term) :Tac unit
  = match l with
    | []    -> fail "no command lemma matched the goal"
    | hd::tl -> or_else (fun () -> apply_lemma hd) (fun () -> apply_lemmas tl)

private let process_command () :Tac unit
  = apply_lemmas [`lemma_singleton_heap_rw;
                  `lemma_rw;
		  `lemma_bind;
		  `lemma_singleton_heap_procedure;
		  `lemma_procedure;
		  `lemma_pure_right]

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

private val split_lem : (#a:Type) -> (#b:Type) ->
                        squash a -> squash b -> Lemma (a /\ b)
let split_lem #a #b sa sb = ()

private let get_to_the_next_frame () :Tac unit =
  ignore (repeat (fun () -> apply_lemma (`split_lem); smt ()))

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0 --use_two_phase_tc false --print_full_names"

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
let swap (r1 r2:ref int) (m n:int)
  = (let x = !r1 in
     let y = !r2 in
     r1 := y;
     r2 := x)

     <: STATE unit (fun post h -> h == ((r1 |> m) <*> (r2 |> n)) /\ (defined h /\ post () ((r1 |> n) <*> (r2 |> m))))

     by (fun () -> prelude ();
                process_command ();
		get_to_the_next_frame ();
		process_command ();
	        apply_lemma (`lemma_rewrite_sep_comm);
		process_command ();
	        get_to_the_next_frame ();
		process_command ();
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
		process_command ();
		get_to_the_next_frame ();
		process_command ())

(*
 * 2 commands
 *)
let incr2 (r:ref int) (n:int)
  = (let n = incr r n in
     incr r n)

    <: STATE int (fun post h -> h == (r |> n) /\ (defined h /\ post (n + 2) (r |> n + 2)))

    by (fun () -> prelude ();
               process_command ();
	       get_to_the_next_frame ();
	       process_command ())

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
	     process_command ();
	     apply_lemma (`lemma_rewrite_sep_comm);
	     apply_lemma (`lemma_rewrite_sep_assoc3);
	     process_command ();
	     get_to_the_next_frame ();
	     apply_lemma (`lemma_rewrite_sep_assoc4);
	     process_command ();
	     process_command ();
	     get_to_the_next_frame ();
	     process_command ())

let lemma_pattern_inline (psi1 psi2:Type) (h h':memory) (phi1 phi2: memory -> memory -> Type)
  :Lemma (requires ((psi1 ==> (exists (h0 h1:memory). defined (h0 <*> h1) /\ (h <*> h') == (h0 <*> h1) /\ phi1 h0 h1)) /\
                    (psi2 ==> (exists (h0 h1:memory). defined (h0 <*> h1) /\ (h <*> h') == (h0 <*> h1) /\ phi2 h0 h1))))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ (h <*> h') == (h0 <*> h1) /\
	                              ((psi1 ==> phi1 h0 h1) /\
				       (psi2 ==> phi2 h0 h1))))
  = admit ()

let cond (r1 r2:ref int) (n:int) (b:bool)
  = (let x = !r1 in
     if b then
       r1 := x + 1
     else
       r2 := x + 2)

    <: STATE unit (fun p h -> h == ((r1 |> n) <*> (r2 |> n)) /\ (defined h /\ (b ==> p () ((r1 |> n + 1) <*> (r2 |> n)))))

    by (fun () -> prelude ();
               apply_lemma (`lemma_rw);
	       get_to_the_next_frame ();
               dump "A")


// #set-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0 --initial_fuel 0 --initial_ifuel 0"

// #reset-options "--print_full_names"

// noeq type listptr' =
//   | Null :listptr'
//   | Cell :head:int -> tail:listptr -> listptr'

// and listptr = ref listptr'

// assume Ref_points_to_axiom: forall (a:Type) (r:ref a) (x:a) (m:memory). m == (r |> x) ==> x << r

// let rec valid (p:listptr) (repr:list int) (h:memory) :Type0 =
//   match repr with
//   | []    -> h == (p |> Null)
//   | hd::tl -> exists (tail:listptr) (h1:memory). defined ((p |> Cell hd tail) <*> h1) /\ h == ((p |> Cell hd tail) <*> h1) /\ valid tail tl h1

// private let __exists_elim_as_forall
//   (#a:Type) (#b:Type) (#p: a -> b -> Type) (#phi:Type)
//   (_:(exists x y. p x y)) (_:(squash (forall (x:a) (y:b). p x y ==> phi)))
//   :Lemma phi
//   = ()

// private let __elim_and (h:binder) :Tac unit
//   = and_elim (pack (Tv_Var (bv_of_binder h)));
//     clear h

// private let __elim_exists (h:binder) :Tac unit
//   = let t = `__exists_elim_as_forall in
//     apply_lemma (mk_e_app t [pack (Tv_Var (bv_of_binder h))]);
//     clear h;
//     ignore (forall_intros ())

// private let __implies_intros_with_processing_exists_and_and () :Tac unit
//   = or_else (fun _ -> let h = implies_intro () in
//                     or_else (fun _ -> __elim_and h)
// 		            (fun _ -> or_else (fun _ -> __elim_exists h)
// 			                   (fun _ -> or_else (fun _ -> rewrite h) idtac)))
//             (fun _ -> fail "done")

// let test0 (l:listptr)
//   = (let Cell hd _ = !l in
//      hd)

//     <: STATE int (fun p h -> valid l [2; 3] h /\ (defined h /\ p 2 h))

//     by (fun () ->
//         let _ = forall_intros () in
// 	norm [delta_only ["SL.Examples.valid"]];
// 	ignore (repeat __implies_intros_with_processing_exists_and_and);
// 	process_command ();
// 	get_to_the_next_frame ();
// 	process_command ();
// 	dump "A")

// let lemma_pattern_match_rw (#a:Type) (#b:Type) (#c:Type)
//                            (phi:memory -> memory -> a -> b -> c -> Type)
// 			   (psi:b -> c -> Type)
// 			   (r:ref a) (x:a) (h:memory)
//   :Lemma (requires (defined ((r |> x) <*> h) /\ (forall (y:b) (z:c). psi y z ==> phi (r |> x) h x y z)))
//          (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\
// 	                              ((r |> x) <*> h) == (h0 <*> h1) /\ 
// 				       (forall (y:b) (z:c).
// 				          psi y z ==> 
// 				          (exists x. h0 == (r |> x) /\ phi h0 h1 x y z))))
//   = ()

// let lemma_pattern_match_bind_rw (#a:Type) (#b:Type) (#c:Type)
//                            (phi:memory -> memory -> a -> b -> c -> Type)
// 			   (psi:b -> c -> Type)
// 			   (r:ref a) (x:a) (h:memory)
//   :Lemma (requires (defined ((r |> x) <*> h) /\ (forall (y:b) (z:c). psi y z ==> phi (r |> x) h x y z)))
//          (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\
// 	                              ((r |> x) <*> h) == (h0 <*> h1) /\ 
// 				       (forall (y:b) (z:c).
// 				          psi y z ==> 
// 				          (exists x. h0 == (r |> x) /\ phi h0 h1 x y z))))

// let test1 (l:listptr)
//   = (let lv = !l in
//      match lv with
//      | Cell hd tail ->
//        let _ = !tail in
//        let hd = hd + 1 in
//        let c = Cell hd tail in
//        l := c
//      | _ -> ())

//     <: STATE unit (fun p h -> valid l [2; 3] h /\ (defined h /\ (forall h1. valid l [3; 3] h1 ==> p () h1)))

//     by (fun () ->
//         let _ = forall_intros () in
// 	norm [delta_only ["SL.Examples.valid"]];
// 	ignore (repeat __implies_intros_with_processing_exists_and_and);
// 	apply_lemma (`lemma_rw_rw);
// 	get_to_the_next_frame ();
// 	norm [delta_only ["SL.Examples.uu___is_Cell";
// 	                  "SL.Examples.uu___is_Null";
// 			  "SL.Examples.__proj__Cell__item__head";
// 			  "SL.Examples.__proj__Cell__item__head"]];
// 	norm [Prims.simplify];
// 	dump "A")



// 	// let h = implies_intro () in
// 	// __elim_and h;
// 	// let h = implies_intro () in
// 	// __elim_exists h;
// 	// let h = implies_intro () in
// 	// __elim_and h;
// 	// let h = implies_intro () in
// 	// __elim_and h;
// 	// let _ = (let h = implies_intro () in or_else (fun _ -> rewrite h) idtac) in
// 	// let _ = (let h = implies_intro () in or_else (fun _ -> rewrite h) idtac) in
// 	// let h = implies_intro () in
// 	// __elim_exists h;
// 	// let h = implies_intro () in
// 	// __elim_and h;
// 	// let h = implies_intro () in
// 	// __elim_and h;
// 	// let _ = (let h = implies_intro () in or_else (fun _ -> rewrite h) idtac) in
// 	// let _ = (let h = implies_intro () in or_else (fun _ -> rewrite h) idtac) in
// 	// let _ = (let h = implies_intro () in or_else (fun _ -> rewrite h) idtac) in
// 	// let h = implies_intro () in
// 	// __elim_and h;
// 	// let _ = (let h = implies_intro () in or_else (fun _ -> rewrite h) idtac) in
// 	// let _ = (let h = implies_intro () in or_else (fun _ -> rewrite h) idtac) in

// // let foo (p:int -> int -> Type) (q:int -> int -> int -> int -> Type) (r:Type)
// //   = assert_by_tactic ((exists x1 x2. (p x1 x2 /\ (exists x3 x4. q x1 x2 x3 x4))) ==> r)
// //     (fun () -> 
// //      let h  = implies_intro () in
// //      let ae = `__exists_elim_as_forall in
// //      apply_lemma (mk_e_app ae [pack (Tv_Var (bv_of_binder h))]);
// //      clear h;
// //      let _ = forall_intros () in
// //      let h = implies_intro () in
// //      and_elim (pack (Tv_Var (bv_of_binder h)));
// //      clear h;
// //      let _ = implies_intro () in
// //      let h  = implies_intro () in
// //      let ae = `__exists_elim_as_forall in
// //      apply_lemma (mk_e_app ae [pack (Tv_Var (bv_of_binder h))]);
// //      clear h;
// //      let _ = forall_intros () in
// //      let h = implies_intro () in
// //      dump "A")
