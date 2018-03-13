module SL.Examples

open SepLogic.Heap
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
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\
	                              (r |> x) == (m0 <*> m1) /\ (exists x. m0 == (r |> x) /\ phi m0 m1 x)))
  = ()

(*
 * a read/write command followed by a read/write command
 *)
let lemma_rw_rw (#a:Type0) (phi:memory -> memory -> a -> Type0) (r:ref a) (x:a) (m:memory)
  :Lemma (requires (defined ((r |> x) <*> m) /\ phi (r |> x) m x))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\
	                              ((r |> x) <*> m) == (m0 <*> m1) /\ (exists x. m0 == (r |> x) /\ phi m0 m1 x)))
  = ()

(*
 * a read/write command followed by a bind with singleton heap
 *)
let lemma_singleton_heap_rw_bind (#a:Type0) (phi:memory -> memory -> memory -> memory -> a -> Type0) (r:ref a) (x:a)
  :Lemma (requires (phi (r |> x) emp (r |> x) emp x))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\ (r |> x) == (m0 <*> m1) /\
	                              (exists (m3 m4:memory). defined (m3 <*> m4) /\ m0 == (m3 <*> m4) /\ (exists x. m3 == (r |> x) /\ phi m0 m1 m3 m4 x))))  
  = ()

(*
 * a read/write command followed by a bind
 *)
let lemma_rw_bind (#a:Type0) (phi:memory -> memory -> memory -> memory -> a -> Type0) (r:ref a) (x:a) (m:memory)
  :Lemma (requires (defined (((r |> x) <*> m) <*> emp) /\ phi ((r |> x) <*> m) emp (r |> x) m x))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\ ((r |> x) <*> m) == (m0 <*> m1) /\
	                              (exists (m3 m4:memory). defined (m3 <*> m4) /\ m0 == (m3 <*> m4) /\ (exists x. m3 == (r |> x) /\ phi m0 m1 m3 m4 x))))  
  = ()

(*
 * pure expression at the end
 *)
let lemma_pure_right (m m':memory) (phi:memory -> memory -> memory -> Type0)
  :Lemma (requires (defined (m <*> m') /\ phi m m' (m <*> m')))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\ (m <*> m') == (m0 <*> m1) /\ phi m m' m1))
  = lemma_sep_comm (m <*> m') emp

(*
 * procedure call followed by a read/write command with singleton heap
 *)
let lemma_singleton_heap_procedure_rw (#a:Type0) (phi:memory -> memory -> a -> Type0)
		                 (r:ref a) (x:a)
  :Lemma (requires (phi (r |> x) emp x))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\ (r |> x) == (m0 <*> m1) /\
	                     (m0 == (r |> x) /\ phi m0 m1 x)))
  = ()

(*
 * procedure call followed by a read/write command
 *)
let lemma_procedure_rw (phi:memory -> memory -> memory -> memory -> Type0)
		       (m m':memory)
  :Lemma (requires (defined (m <*> m') /\ phi m m' m m'))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\ (m <*> m') == (m0 <*> m1) /\
	                     (m0 == m /\ phi m m' m0 m1)))
  = ()

(*
 * procedure call followed by a bind with singleton heap
 *)
let lemma_singleton_heap_procedure_bind
  (#a:Type0) (phi:memory -> memory -> memory -> memory -> a -> Type0)
  (r:ref a) (x:a)
  :Lemma (requires (phi (r |> x) emp (r |> x) emp x))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\ (r |> x) == (m0 <*> m1) /\
	                     (exists (m3 m4:memory). defined (m3 <*> m4) /\ m0 == (m3 <*> m4) /\ (m3 == (r |> x) /\ phi m0 m1 m3 m4 x))))
  = ()

(*
 * procedure call followed by a bind
 *)
let lemma_procedure_bind (phi:memory -> memory -> memory -> memory -> memory -> memory -> Type0)
                         (m m':memory)
  :Lemma (requires (defined (m <*> m') /\ phi m m' (m <*> m') emp m m'))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\ (m <*> m') == (m0 <*> m1) /\
	                     (exists (m3 m4:memory). defined (m3 <*> m4) /\ m0 == (m3 <*> m4) /\ (m3 == m /\ phi m m' m0 m1 m3 m4))))
  = ()

let lemma_procedure (phi:memory -> memory -> memory -> memory -> Type0) (m m':memory)
  :Lemma (requires (defined (m <*> m') /\ phi m m' m m'))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\ (m <*> m') == (m0 <*> m1) /\ (m0 == m /\ phi m m' m0 m1)))
  = ()

(*** command specific lemmas end ***)

(*** following are heap algebra lemmas, should be replaced with canonizer? ***)

let lemma_rewrite_sep_comm (m1 m2:memory) (phi:memory -> memory -> memory -> memory -> Type0)
  :Lemma (requires (exists (m3 m4:memory). defined (m3 <*> m4) /\ (m1 <*> m2) == (m3 <*> m4) /\ phi m1 m2 m3 m4))
         (ensures  (exists (m3 m4:memory). defined (m3 <*> m4) /\ (m2 <*> m1) == (m3 <*> m4) /\ phi m1 m2 m3 m4))
  = lemma_sep_comm m1 m2

let lemma_rewrite_sep_assoc1 (m1 m2 m3:memory) (phi:memory -> memory -> memory -> memory -> memory -> Type0)
  :Lemma (requires (exists (m4 m5:memory). defined (m4 <*> m5) /\ (m2 <*> (m1 <*> m3)) == (m4 <*> m5) /\
	                     phi m1 m2 m3 m4 m5))
         (ensures  (exists (m4 m5:memory). defined (m4 <*> m5) /\ (m1 <*> (m2 <*> m3)) == (m4 <*> m5) /\
	                     phi m1 m2 m3 m4 m5))
  = lemma_sep_comm m1 m2

let lemma_rewrite_sep_assoc2 (m1 m2 m3:memory) (phi:memory -> memory -> memory -> memory -> memory -> Type0)
  :Lemma (requires (exists (m4 m5:memory). defined (m4 <*> m5) /\ (m3 <*> (m1 <*> m2)) == (m4 <*> m5) /\
	                     phi m1 m2 m3 m4 m5))
         (ensures  (exists (m4 m5:memory). defined (m4 <*> m5) /\ (m1 <*> (m2 <*> m3)) == (m4 <*> m5) /\
	                     phi m1 m2 m3 m4 m5))
  = lemma_sep_comm m3 m1;
    lemma_sep_comm m3 m2

let lemma_rewrite_sep_assoc3 (m1 m2 m3:memory) (phi:memory -> memory -> memory -> memory -> memory -> Type0)
  :Lemma (requires (exists (m4 m5:memory). defined (m4 <*> m5) /\ ((m1 <*> m2) <*> m3) == (m4 <*> m5) /\
	                     phi m1 m2 m3 m4 m5))
         (ensures  (exists (m4 m5:memory). defined (m4 <*> m5) /\ (m1 <*> (m2 <*> m3)) == (m4 <*> m5) /\
	                     phi m1 m2 m3 m4 m5))
  = ()

let lemma_rewrite_sep_assoc4 (m1 m2 m3:memory) (phi:memory -> memory -> memory -> memory -> memory -> Type0)
  :Lemma (requires (exists (m4 m5:memory). defined (m4 <*> m5) /\ (m1 <*> (m2 <*> m3)) == (m4 <*> m5) /\
	                     phi m1 m2 m3 m4 m5))
         (ensures  (exists (m4 m5:memory). defined (m4 <*> m5) /\ ((m1 <*> m2) <*> m3) == (m4 <*> m5) /\
	                     phi m1 m2 m3 m4 m5))
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

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0 --use_two_phase_tc false --print_full_names --__temp_fast_implicits"


(*
 * main idea for the examples:
 *   call process_command for each command, currently the ordering of the heap is manual
 *)

(*
 * two commands
 *)
let write_read (r1 r2:ref int) (x y:int) =
  (r1 := 2;
   !r2)
  
  <: STATE int (fun p m -> m == ((r1 |> x) <*> (r2 |> y)) /\ (defined m /\ p y ((r1 |> 2) <*> (r2 |> y))))

  by (fun () ->
      prelude ();
      process_command ();
      get_to_the_next_frame ();
      apply_lemma (`lemma_rewrite_sep_comm);
      process_command ())

(*
 * four commands
 *)
let swap (r1 r2:ref int) (x y:int)
  = (let x = !r1 in
     let y = !r2 in
     r1 := y;
     r2 := x)

     <: STATE unit (fun post m -> m == ((r1 |> x) <*> (r2 |> y)) /\ (defined m /\ post () ((r1 |> y) <*> (r2 |> x))))

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
let incr (r:ref int) (x:int)
  = (let y = !r in
     let z = y + 1 in
     r := z;
     !r)

     <: STATE int (fun post m -> m == (r |> x) /\ (defined m /\ post (x + 1) (r |> x + 1)))

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
let incr2 (r:ref int) (x:int)
  = (let y = incr r x in
     incr r y)

    <: STATE int (fun post m -> m == (r |> x) /\ (defined m /\ post (x + 2) (r |> x + 2)))

    by (fun () -> prelude ();
               process_command ();
	       get_to_the_next_frame ();
	       process_command ())

(*
 * 3 commands + one at the end
 *)
#set-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0 --initial_fuel 0 --initial_ifuel 0"
let rotate (r1 r2 r3:ref int) (x y z:int) =
  (swap r2 r3 y z;
   swap r1 r2 x z;
   let w = !r1 in
   w)

  <: STATE int (fun post m -> m == ((r1 |> x) <*> ((r2 |> y) <*> (r3 |> z))) /\
                         (defined m /\ post z ((r1 |> z) <*> ((r2 |> x) <*> (r3 |> y)))))

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

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --print_full_names --__no_positivity"

noeq type listptr' =
  | Null :listptr'
  | Cell :head:int -> tail:listptr -> listptr'

and listptr = ref listptr'

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --print_full_names"

assume Ref_points_to_axiom: forall (a:Type) (r:ref a) (x:a) (m:memory). m == (r |> x) ==> x << r

let rec valid (p:listptr) (repr:list int) (m:memory) :Type0 =
  match repr with
  | []    -> m == (p |> Null)
  | hd::tl -> exists (tail:listptr) (m1:memory). defined ((p |> Cell hd tail) <*> m1) /\ m == ((p |> Cell hd tail) <*> m1) /\ valid tail tl m1


// private let __exists_elim_as_forall
//   (#a:Type) (#b:Type) (#p: a -> b -> Type) (#phi:Type)
//   (_:(exists x y. p x y)) (_:(squash (forall (x:a) (y:b). p x y ==> phi)))
//   :Lemma phi
//   = ()

// let foo (p:int -> int -> Type) (q:int -> int -> int -> int -> Type) (r:Type)
//   = assert_by_tactic ((exists x1 x2. (p x1 x2 /\ (exists x3 x4. q x1 x2 x3 x4))) ==> r)
//     (fun () -> 
//      let h  = implies_intro () in
//      let ae = `__exists_elim_as_forall in
//      apply_lemma (mk_e_app ae [pack (Tv_Var (bv_of_binder h))]);
//      clear h;
//      let _ = forall_intros () in
//      let h = implies_intro () in
//      and_elim (pack (Tv_Var (bv_of_binder h)));
//      clear h;
//      let _ = implies_intro () in
//      let h  = implies_intro () in
//      let ae = `__exists_elim_as_forall in
//      apply_lemma (mk_e_app ae [pack (Tv_Var (bv_of_binder h))]);
//      clear h;
//      let _ = forall_intros () in
//      let h = implies_intro () in
//      dump "A")

// let test (l:listptr)
//   = (let Cell hd _ = !l in
//      hd)

//     <: STATE int (fun p h -> valid l [2; 3] h /\ (defined h /\ p 2 h))

//     by (fun () ->
//         let _ = forall_intros () in
// 	norm [delta_only ["SL.Examples.valid"]];
// 	let h = implies_intro () in
// 	and_elim (pack (Tv_Var (bv_of_binder h)));
// 	clear h;
// 	let _ = implies_intro () in
// 	dump "A")
