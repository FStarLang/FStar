module SL.Examples

open SepLogic.Heap
open SL.Effect

open FStar.Tactics

(*** command specific lemmas ***)

(*
 * these lemmas match on the VCs
 *)
let lemma_singleton_heap_rw (#a:Type0) (phi:memory -> memory -> a -> Type0) (r:ref a) (x:a)
  :Lemma (requires (phi (r |> x) emp x))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\
	                              (r |> x) == (m0 <*> m1) /\ (exists x. m0 == (r |> x) /\ phi m0 m1 x)))
  = ()

let lemma_rw (#a:Type0) (phi:memory -> memory -> a -> Type0) (r:ref a) (x:a) (m:memory)
  :Lemma (requires (defined ((r |> x) <*> m) /\ phi (r |> x) m x))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\
	                              ((r |> x) <*> m) == (m0 <*> m1) /\ (exists x. m0 == (r |> x) /\ phi m0 m1 x)))
  = ()

let lemma_bind (phi:memory -> memory -> memory -> memory -> Type0) (m m':memory)
  :Lemma (requires (exists m3 m4. defined (m3 <*> m4) /\ (m <*> m') == (m3 <*> m4) /\ phi (m <*> m') emp m3 m4))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\ (m <*> m') == (m0 <*> m1) /\
	                              (exists (m3 m4:memory). defined (m3 <*> m4) /\ m0 == (m3 <*> m4) /\ phi m0 m1 m3 m4)))
  = ()

let lemma_singleton_heap_procedure (#a:Type0) (phi:memory -> memory -> a -> Type0)
		                   (r:ref a) (x:a)
  :Lemma (requires (phi (r |> x) emp x))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\ (r |> x) == (m0 <*> m1) /\
	                              (m0 == (r |> x) /\ phi m0 m1 x)))
  = ()

let lemma_procedure (phi:memory -> memory -> memory -> memory -> Type0)
		    (m m':memory)
  :Lemma (requires (defined (m <*> m') /\ phi m m' m m'))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\ (m <*> m') == (m0 <*> m1) /\
	                              (m0 == m /\ phi m m' m0 m1)))
  = ()

let lemma_pure_right (m m':memory) (phi:memory -> memory -> memory -> Type0)
  :Lemma (requires (defined (m <*> m') /\ phi m m' (m <*> m')))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\ (m <*> m') == (m0 <*> m1) /\ phi m m' m1))
  = lemma_sep_comm (m <*> m') emp

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

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0 --use_two_phase_tc false --print_full_names --__temp_fast_implicits"

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
		process_command ();
		get_to_the_next_frame ();
		process_command ())

(*
 * 2 commands
 *)
let incr2 (r:ref int) (x:int)
  = (let y = incr r x in
     incr r y)

    <: STATE int (fun post m -> m == (r |> x) /\ (defined m /\ post (x + 2) (r |> x + 2)))

    by (fun () -> prelude ();
               process_command ();
	       get_to_the_next_frame ();
	       process_command ())

let rotate (r1 r2 r3:ref int) (x y z:int) =
  (swap r2 r3 y z;
   swap r1 r2 x z;
   let x = !r1 in
   x)
   
  <: STATE int (fun post m -> m == ((r1 |> x) <*> ((r2 |> y) <*> (r3 |> z))) /\
                         (defined m /\ post z ((r1 |> z) <*> ((r2 |> x) <*> (r3 |> y)))))

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

let lemma_inline_in_patterns_two (psi1 psi2:Type) (m m':memory) (phi1 phi2: memory -> memory -> Type)
  :Lemma (requires (defined (m <*> m') /\ ((psi1 ==> phi1 (m <*> m') emp) /\ (psi2 ==> phi2 (m <*> m') emp))))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\ (m <*> m') == (m0 <*> m1) /\
	                              ((psi1 ==> phi1 m0 m1) /\
				       (psi2 ==> phi2 m0 m1))))
  = ()

let lemma_frame_out_empty_right (phi:memory -> memory -> memory -> Type) (m:memory)
  :Lemma (requires (defined m /\ phi m m emp))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\ m == (m0 <*> m1) /\ phi m m0 m1))
  = ()

let lemma_frame_out_empty_left (phi:memory -> memory -> memory -> Type) (m:memory)
  :Lemma (requires (defined m /\ phi m emp m))
         (ensures  (exists (m0 m1:memory). defined (m0 <*> m1) /\ m == (m0 <*> m1) /\ phi m m0 m1))
  = lemma_sep_comm m emp

let cond_test (r1 r2:ref int) (x:int) (b:bool)
  = (let y = !r1 in
     match b with
     | true  -> r1 := y + 1
     | false -> r2 := y + 2)

    <: STATE unit (fun p m -> m == ((r1 |> x) <*> (r2 |> x)) /\ (defined m /\ (b ==> p () ((r1 |> x + 1) <*> (r2 |> x))) /\
                                                                       (~ b ==> p () ((r1 |> x) <*> (r2 |> x + 2)))))

    by (fun () -> prelude ();
               apply_lemma (`lemma_rw);
	       get_to_the_next_frame ();
	       apply_lemma (`lemma_inline_in_patterns_two);
	       split (); smt ();
	       split ();
	       //goal 1
	       ignore (implies_intro ());
	       apply_lemma (`lemma_rw);
	       split (); smt (); split (); smt ();
	       apply_lemma (`lemma_pure_right);
	       smt ();
	       //goal 2
	       ignore (implies_intro ());
	       apply_lemma (`lemma_frame_out_empty_right);
	       split (); smt ();
	       split ();
	       //goal 2.1
	       ignore (implies_intro ());
	       apply_lemma (`lemma_rewrite_sep_comm);
	       apply_lemma (`lemma_rw);
	       split (); smt ();
	       split (); smt ();
	       apply_lemma (`lemma_frame_out_empty_left);
	       split (); smt (); split (); smt (); split (); smt ();
	       apply_lemma (`lemma_frame_out_empty_left);
	       smt ();
	       //goal 2.2
	       smt ())

#reset-options "--print_full_names --__no_positivity"

noeq type listcell =
  | Cell :head:int -> tail:listptr -> listcell

and listptr = option (ref listcell)

#reset-options "--print_full_names --__temp_fast_implicits"

let rec valid (p:listptr) (repr:list int) (m:memory) :Tot Type0 (decreases repr) =
  defined m /\
  (match repr with
   | []    -> None? p /\ m == emp
   | hd::tl -> Some? p /\
             (exists (tail:listptr) (m1:memory). m == (((Some?.v p) |> Cell hd tail) <*> m1) /\ valid tail tl m1))
                                                      
private let __exists_elim_as_forall2
  (#a:Type) (#b:Type) (#p: a -> b -> Type) (#phi:Type)
  (_:(exists x y. p x y)) (_:(squash (forall (x:a) (y:b). p x y ==> phi)))
  :Lemma phi
  = ()

private let __exists_elim_as_forall1
  (#a:Type) (#p:a -> Type) (#phi:Type)
  (_:(exists x. p x)) (_:(squash (forall (x:a). p x ==> phi)))
  :Lemma phi
  = ()

private let __elim_and (h:binder) :Tac unit
  = and_elim (pack (Tv_Var (bv_of_binder h)));
    clear h

private let __elim_exists1 (h:binder) :Tac unit
  = let t = `__exists_elim_as_forall1 in
    apply_lemma (mk_e_app t [pack (Tv_Var (bv_of_binder h))]);
    clear h;
    ignore (forall_intros ())

private let __elim_exists2 (h:binder) :Tac unit
  = let t = `__exists_elim_as_forall2 in
    apply_lemma (mk_e_app t [pack (Tv_Var (bv_of_binder h))]);
    clear h;
    ignore (forall_intros ())

private let __implies_intros_with_processing_exists_and_and () :Tac unit
  = or_else (fun _ -> let h = implies_intro () in
                    or_else (fun _ -> __elim_and h)
		            (fun _ -> or_else (fun _ -> __elim_exists2 h)
			                   (fun _ -> or_else (fun _ -> rewrite h) idtac)))
            (fun _ -> fail "done")

(*
 * AR: these two lemmas are useless because of no match-ing in the unifier
 *)
// #set-options "--z3rlimit 30"
// private let __elim_list_match0 (#a:Type) (l:list a) (phi:Type) (psi:a -> list a -> Type) (rest:list a -> Type)
//   :Lemma (requires (((l == [] /\ phi) ==> rest []) /\
//                     (forall hd tl. (l == Cons hd tl /\ psi hd tl) ==> rest (Cons hd tl))))
//          (ensures  ((match l with
// 	             | []         -> phi
// 		     | Cons hd tl -> psi hd tl) ==> rest l))
//   = ()

// private let __list_match_elim_as_cases (#l:list int) (#phi:list int -> Type0) (#psi:list int -> int -> list int -> Type0) (#rest:list int -> Type0)
//   (_:(match l with
//       | []         -> phi l
//       | Cons hd tl -> psi l hd tl))
//   (_:squash (((l == [] /\ phi []) ==> rest []) /\
//              ((forall hd tl. (l == Cons hd tl /\ psi (Cons hd tl) hd tl) ==> rest (Cons hd tl)))))
//   :Lemma (rest l)
//   = ()

// private let __elim_list_match (h:binder) :Tac unit
//   = let t = `__list_match_elim_as_cases in
//     apply_lemma (mk_e_app t [pack (Tv_Var (bv_of_binder h))])
//     //clear h

//i tried a style where i pass the proof of valid p repr m as a squashed term
//but even then unification fails
//currently all the arguments have to be provided explicitly
let __elim_valid_without_match
  (#p:listptr) (#repr:list int) (#m:memory) (#goal:listptr -> list int -> memory -> Type0)
  :Lemma (requires (((repr == [] /\ p == None /\ m == emp) ==> goal None [] emp) /\
                    (forall hd tl. (repr == hd::tl /\
	                       Some? p       /\
			       (exists tail m1. m == (((Some?.v p) |> Cell hd tail) <*> m1) /\ valid tail tl m1))
		              ==> goal p (Cons hd tl) m)))
         (ensures  (goal p repr m))
  = admit ()

let lemma_frame_exact (phi:memory -> memory -> memory -> memory -> Type0) (h h':memory)
  :Lemma (requires (defined (h <*> h') /\ phi h h' h h'))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ (h <*> h') == (h0 <*> h1) /\ phi h h' h0 h1))
  = ()

let rec length (l:listptr)
  = (match l with
     | None   -> (0 <: STATE int (fun p h -> p 0 emp))
     | Some r ->
       let Cell hd tl = !r in
       1 + length tl)

    <: STATE int (fun p m -> exists (fl:list int). valid l fl m /\ p (List.Tot.length fl) m)

    by (fun _ -> ignore (forall_intros ());
              let h = implies_intro () in __elim_exists1 h;
	      let h = implies_intro () in __elim_and h;
	      ignore (implies_intro ());
	      apply_lemma (`__elim_valid_without_match);  //this is fragile
	      assumption (); assumption (); assumption ();
	      split ();
	      let h = implies_intro () in __elim_and h;
	      let h = implies_intro () in __elim_and h;
	      let h = implies_intro () in rewrite h; let h = implies_intro () in rewrite h;
              let h = implies_intro () in rewrite h;
	      ignore (implies_intro ());
	      split ();
	      ignore (implies_intro ());
	      apply_lemma (`lemma_frame_out_empty_left);
	      split (); smt ();
	      ignore (implies_intro ());
	      split (); smt (); split (); smt ();
	      apply_lemma (`lemma_frame_out_empty_left);
	      smt (); smt ();

              //inductive case
	      let hd_binder = forall_intro () in
	      let tl_binder = forall_intro () in
	      let h = implies_intro () in __elim_and h;
	      let h = implies_intro () in __elim_and h;
	      let h = implies_intro () in rewrite h;
	      ignore (implies_intro ());
	      let h = implies_intro () in __elim_exists2 h;
	      let h = implies_intro () in __elim_and h;
	      let h = implies_intro () in rewrite h;
	      ignore (implies_intros ());
	      split (); smt ();

              ignore (implies_intro ());
	      apply_lemma (`lemma_inline_in_patterns_two);
	      split (); smt ();
	      split ();
	      ignore (implies_intro ());
	      apply_lemma (`lemma_frame_out_empty_right);
	      split (); smt ();
	      ignore (forall_intro ());
	      let h = implies_intro () in rewrite h;
	      norm [delta_only ["FStar.Pervasives.Native.__proj__Some__item__v"]];
	      apply_lemma (`lemma_rw);
	      split (); smt ();
	      split (); smt ();
	      apply_lemma (`lemma_frame_out_empty_right);
	      split (); smt ();
	      apply_lemma (`lemma_frame_out_empty_right);
	      split (); smt ();
	      ignore (forall_intros ()); ignore (implies_intro ());
	      apply_lemma (`lemma_rewrite_sep_comm);
	      apply_lemma (`lemma_frame_exact);
	      split (); smt ();
	      let w = let bv, _ = inspect_binder tl_binder in pack (Tv_Var bv) in
	      witness w;
	      split (); smt (); split (); smt ();
	      apply_lemma (`lemma_frame_out_empty_left);
	      split (); smt ();
	      ignore (forall_intro ());
	      ignore (implies_intro ());
	      split (); smt (); split (); smt ();
	      apply_lemma (`lemma_frame_out_empty_left);
	      split (); smt (); split (); smt ();
	      split (); smt (); split (); smt ();
	      apply_lemma (`lemma_frame_out_empty_left);
	      split (); smt (); split (); smt (); split (); smt ();
	      apply_lemma (`lemma_frame_out_empty_left);
	      smt ();
	      smt ())
