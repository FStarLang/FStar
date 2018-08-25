module SL.Examples

(* cf. #1323, #1465 *)
module SLHeap = SL.Heap
open SL.Heap

(*** Effect definition ***)

let pre = memory -> Type0
let post (a:Type) = a -> memory -> Type0
let st_wp (a:Type) = post a -> pre

unfold let return_wp (a:Type) (x:a) :st_wp a = 
  fun post m0 -> m0 == emp /\ post x m0

unfold let frame_wp (#a:Type) (wp:st_wp a) (post:memory -> post a) (m:memory) =
  exists (m0 m1:memory). defined (m0 <*> m1) /\ m == (m0 <*> m1) /\ wp (post m1) m0

unfold let frame_post (#a:Type) (p:post a) (m0:memory) :post a =
  fun x m1 -> defined (m1 <*> m0) /\ p x (m1 <*> m0)  //m1 is the frame

unfold let bind_wp (r:range) (a:Type) (b:Type) (wp1:st_wp a) (wp2:a -> st_wp b)
  :st_wp b
  = fun post m0 ->
    frame_wp wp1 (frame_post (fun x m1 -> frame_wp (wp2 x) (frame_post post) m1)) m0

unfold let id_wp (a:Type) (x:a) (p:post a) (m:memory) = p x emp

unfold  let st_if_then_else (a:Type) (p:Type) (wp_then:st_wp a) (wp_else:st_wp a) (post:post a) (m0:memory) =
  // l_ITE p (wp_then post m0) (wp_else post m0)
  l_ITE p ((bind_wp range_0 a a wp_then (id_wp a)) post m0)
          ((bind_wp range_0 a a wp_else (id_wp a)) post m0)

unfold  let st_ite_wp (a:Type) (wp:st_wp a) (p:post a) (m0:memory) = wp p m0

unfold  let st_stronger (a:Type) (wp1:st_wp a) (wp2:st_wp a) =
  forall (p:post a) (m:memory). wp1 p m ==> wp2 p m

unfold let st_close_wp (a:Type) (b:Type) (wp:(b -> GTot (st_wp a))) (p:post a) (m:memory) =
  forall (b:b). wp b p m

unfold  let st_assert_p (a:Type) (p:Type) (wp:st_wp a) (q:post a) (m:memory) =
  p /\ wp q m

unfold  let st_assume_p (a:Type) (p:Type) (wp:st_wp a) (q:post a) (m:memory) =
  p ==> wp q m

unfold  let st_null_wp (a:Type) (p:post a) (m:memory) =
  forall (x:a) (m:memory). p x m

unfold let st_trivial (a:Type) (wp:st_wp a) =
  forall m0. wp (fun _ _ -> True) m0
      
new_effect {
  STATE : result:Type -> wp:st_wp result -> Effect
  with return_wp    = return_wp
     ; bind_wp      = bind_wp
     ; if_then_else = st_if_then_else
     ; ite_wp       = st_ite_wp
     ; stronger     = st_stronger
     ; close_wp     = st_close_wp
     ; assert_p     = st_assert_p
     ; assume_p     = st_assume_p
     ; null_wp      = st_null_wp
     ; trivial      = st_trivial
}

unfold let lift_div_st (a:Type) (wp:pure_wp a) (p:post a) (m:memory) = wp (fun a -> p a emp)
sub_effect DIV ~> STATE = lift_div_st

assume
val ( ! ) (#a:Type) (r:ref a)
  :STATE a (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post x m0)

assume
val ( := ) (#a:Type) (r:ref a) (v:a)
  :STATE unit (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post () (r |> v))

assume
val alloc (#a:Type) (v:a)
  :STATE (ref a) (fun post m0 -> m0 == emp /\ (forall r m1 . m1 == (r |> v) ==> post r m1))


(*** End effect definition ***)


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

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0 --print_full_names --__temp_fast_implicits"

(*
 * two commands
 *)
let write_read (r1 r2:ref int) (x y:int) =
  (r1 := 2;
   !r2)
  
  <: STATE int (fun p m -> m == ((r1 |> x) <*> (r2 |> y)) /\ (defined m /\ p y ((r1 |> 2) <*> (r2 |> y))))

  by (prelude ();
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

     by (prelude ();
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

     by (prelude ();
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

    by (prelude ();
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

  by (prelude ();
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

    by (prelude ();
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

let null :listptr = None

#reset-options "--print_full_names --__temp_fast_implicits"

let rec valid (p:listptr) (repr:list int) (m:memory) :Tot Type0 (decreases repr) =
  defined m /\
  (match repr with
   | []    -> None? p /\ m == emp
   | hd::tl -> Some? p /\
             (exists (tail:listptr) (m1:memory).{:pattern (has_type tail listptr); (has_type m1 memory)}
                 m == (((Some?.v p) |> Cell hd tail) <*> m1) /\ valid tail tl m1))
                                                      
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

private let __elim_exists_return_binders1 (h:binder) :Tac (list binder)
  = let t = `__exists_elim_as_forall1 in
    apply_lemma (mk_e_app t [pack (Tv_Var (bv_of_binder h))]);
    clear h;
    forall_intros ()

private let __elim_exists1 (h:binder) :Tac unit
  = ignore (__elim_exists_return_binders1 h)

private let __elim_exists_return_binders2 (h:binder) :Tac (list binder)
  = let t = `__exists_elim_as_forall2 in
    apply_lemma (mk_e_app t [pack (Tv_Var (bv_of_binder h))]);
    clear h;
    forall_intros ()

private let __elim_exists2 (h:binder) :Tac unit = ignore (__elim_exists_return_binders2 h)

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
  :Lemma (requires ((valid p repr m) /\
                    (((repr == [] /\ p == None /\ m == emp) ==> goal None [] emp) /\
                     (forall hd tl. (repr == hd::tl /\
	                        Some? p       /\
			        (exists tail m1. m == (((Some?.v p) |> Cell hd tail) <*> m1) /\ valid tail tl m1))
		               ==> goal p (Cons hd tl) m))))
         (ensures  (goal p repr m))
  = match repr with
    | []    -> ()
    | hd::tl -> assume (exists (tail:listptr) (m1:memory). m == (((Some?.v p) |> Cell hd tail) <*> m1) /\ valid tail tl m1)  //this assume is exactly the hd::tl case of the valid predicate, but the smt encoding of valid is deep embedding, and so, it cannot prove the shallow encoding of the same predicate, there are other ways to do this, but adding an assume for now

let lemma_frame_exact (phi:memory -> memory -> memory -> memory -> Type0) (h h':memory)
  :Lemma (requires (defined (h <*> h') /\ phi h h' h h'))
         (ensures  (exists (h0 h1:memory). defined (h0 <*> h1) /\ (h <*> h') == (h0 <*> h1) /\ phi h h' h0 h1))
  = ()

let rec process_trivial_tail () :Tac unit
  = ignore (repeat (fun () -> split (); smt ()));
    or_else (fun () -> apply_lemma (`lemma_frame_out_empty_left); process_trivial_tail ())
            (fun () -> idtac ())

let split_and_smt () :Tac unit = split (); smt ()

let implies_and_elim () :Tac unit =
  let h = implies_intro () in
  first [(fun () -> __elim_and h);
         (fun () -> rewrite h);
	 (fun () -> __elim_exists2 h);
	 (fun () -> __elim_exists1 h);
	 idtac]

let rec length (l:listptr)
  = (match l with
     | None   -> (0 <: STATE int (fun p h -> p 0 emp))
     | Some r ->
       let Cell hd tl = !r in
       1 + length tl)

    <: STATE int (fun p m -> exists (fl:list int). valid l fl m /\ p (List.Tot.length fl) m)

    by (ignore (forall_intros ());
              ignore (repeatn 2 implies_and_elim);
	      ignore (implies_intro ());
	      apply_lemma (`__elim_valid_without_match);  //this is fragile
	      ignore (repeatn 3 assumption);
	      split_and_smt ();
	      split ();
	      ignore (repeatn 5 implies_and_elim);
	      ignore (implies_intro ());
	      split ();
	      ignore (implies_intro ());
	      apply_lemma (`lemma_frame_out_empty_left);
	      split_and_smt ();
	      ignore (implies_intro ());
	      ignore (repeatn 2 split_and_smt);
	      apply_lemma (`lemma_frame_out_empty_left);
	      smt (); smt ();

              //inductive case
	      let hd_binder = forall_intro () in
	      let tl_binder = forall_intro () in
	      ignore (repeatn 7 implies_and_elim);
	      ignore (implies_intros ());
	      split_and_smt ();

              ignore (implies_intro ());
	      apply_lemma (`lemma_inline_in_patterns_two);
	      split_and_smt ();
	      split ();
	      ignore (implies_intro ());
	      apply_lemma (`lemma_frame_out_empty_right);
	      split_and_smt ();
	      ignore (forall_intro ());
	      let h = implies_intro () in rewrite h;
	      norm [delta_only ["FStar.Pervasives.Native.__proj__Some__item__v"]];
	      apply_lemma (`lemma_rw);
	      ignore (repeatn 2 split_and_smt);
	      ignore (repeatn 2 (fun () -> apply_lemma (`lemma_frame_out_empty_right); split_and_smt ()));
	      ignore (forall_intros ()); ignore (implies_intro ());
	      apply_lemma (`lemma_rewrite_sep_comm);
	      apply_lemma (`lemma_frame_exact);
	      split_and_smt ();
	      let w = let bv, _ = inspect_binder tl_binder in pack (Tv_Var bv) in
	      witness w;
	      ignore (repeatn 2 split_and_smt);
	      apply_lemma (`lemma_frame_out_empty_left);
	      split_and_smt ();
	      ignore (forall_intro ());
	      ignore (implies_intro ());
	      process_trivial_tail ())

let binder_to_term b = let bv, _ = inspect_binder b in pack (Tv_Var bv)

unfold let dom (m:memory) = addrs_in m

let rec append (l1 l2:listptr)
  = (match l1 with
     | None   -> l2
     | Some r ->
       let Cell hd tl = !r in
       match tl with
       | Some tl_r ->
         let rest = append tl l2 in
	 l1
       | None ->
         r := Cell hd l2;
	 l1)

     <: STATE listptr (fun p m -> exists (fl1 fl2:list int) (m1 m2:memory).
                                 defined (m1 <*> m2) /\
				 m == (m1 <*> m2)    /\
				 valid l1 fl1 m1     /\
				 valid l2 fl2 m2     /\
				 (forall mf l. ((Set.equal (dom mf) (Set.union (dom m1) (dom m2))) /\
				           (Some? l1 ==> l1 == l)                                             /\
				           (valid l (List.Tot.append fl1 fl2) mf)) ==> p l mf))

     by (assume_safe (fun () -> // assume_safe due to all the List.Tot.hd calls
         split (); smt ();
                ignore (forall_intros ());
                let h = implies_intro () in
		let l = __elim_exists_return_binders2 h in
		let fl1_binder = List.Tot.hd l in
		let fl2_binder = List.Tot.hd (List.Tot.tl l) in
                let h = implies_intro () in
		let l = __elim_exists_return_binders2 h in
		let m1_binder = List.Tot.hd l in
		let m2_binder = List.Tot.hd (List.Tot.tl l) in
		ignore (repeatn 4 implies_and_elim);
		ignore (implies_intro ());
		let h = implies_intro () in rewrite h;
		ignore (implies_intro ());

                //induction on fl1
		apply_lemma (`__elim_valid_without_match);
		exact (quote l1);
		exact (binder_to_term fl1_binder);
		exact (binder_to_term m1_binder);
		split (); smt ();  //this is the extra valid goal from __elim_valid_without_match

                split ();

                //empty fl1 case
		ignore (repeatn 5 implies_and_elim);

                ignore (implies_intro ()); //the valid assumption for l2
		ignore (implies_intro ()); //this is the foall mf f. assumption, keep an eye on it

                split ();

                ignore (implies_intro ());
		apply_lemma (`lemma_frame_out_empty_left);
		split_and_smt ();
		ignore (implies_intro ()); ignore (forall_intro ()); ignore (implies_intro ()); ignore (forall_intro ()); ignore (implies_intro ());
		split_and_smt ();
		apply_lemma (`lemma_frame_out_empty_left);
		smt ();

                //inconsistent ()
		ignore (implies_intro ());
		smt ();

                //inductive case fl1 is Cons

                let fl1_head = forall_intro () in
		let fl1_tail = forall_intro () in
		ignore (repeatn 3 implies_and_elim);
		ignore (implies_intro ());
		let h = implies_intro () in let l1 = __elim_exists_return_binders2 h in
		let l1_tail = List.Tot.hd l1 in
		let l1_tail_memory = List.Tot.hd (List.Tot.tl l1) in
		ignore (repeatn 2 implies_and_elim);
		ignore (implies_intro ());
		ignore (implies_intro ());

                ignore (implies_intro ()); //this is the forall mf f. assumption, keep an eye on it

                split ();

                //inconsistent
                ignore (implies_intro ());
		smt ();

                ignore (implies_intro ());
		apply_lemma (`lemma_inline_in_patterns_two);
		split_and_smt ();

                split ();

                ignore (implies_intro ());
		apply_lemma (`lemma_frame_out_empty_right);
		split_and_smt ();

                ignore (forall_intro ());
		let h = implies_intro () in rewrite h;
	        norm [delta_only ["FStar.Pervasives.Native.__proj__Some__item__v"]];
		apply_lemma (`lemma_rewrite_sep_assoc4);
		apply_lemma (`lemma_rw);
		ignore (repeatn 2 split_and_smt);
		ignore (repeatn 2 (fun () -> apply_lemma (`lemma_frame_out_empty_right); split_and_smt ()));
                ignore (forall_intros ()); ignore (implies_intro ());

                split ();

                //case where Some tl_r
		ignore (implies_intro ());
		apply_lemma (`lemma_frame_out_empty_right);
		split_and_smt ();

                ignore (forall_intro ());  //tl_r binder, not needed
		ignore (implies_intro ());

                //important, this is where we are sending memory to the recursive call
		apply_lemma (`lemma_rewrite_sep_comm);
		apply_lemma (`lemma_frame_exact);

                split_and_smt ();
		//provide wp existentials for recursive call
		witness (binder_to_term fl1_tail);
		witness (binder_to_term fl2_binder);
		witness (binder_to_term l1_tail_memory);
		witness (binder_to_term m2_binder);

                //prove definedness/validity
		split_and_smt (); //boom! hail smt!

                //prove the postcondition part
		ignore (forall_intros ());
		ignore (repeatn 2 implies_and_elim);
		ignore (implies_intros ());
		split_and_smt ();

                //check this guy, both right and left seemed ok
		apply_lemma (`lemma_frame_out_empty_left);
		split_and_smt ();
		ignore (forall_intro ());
		let h = implies_intro () in rewrite h;
		ignore (repeatn 2 split_and_smt);
		apply_lemma (`lemma_frame_out_empty_left);
		ignore (repeatn 3 split_and_smt);
		apply_lemma (`lemma_frame_out_empty_left);
		ignore (repeatn 4 split_and_smt);
		apply_lemma (`lemma_frame_out_empty_left);
		ignore (repeatn 3 split_and_smt);
		apply_lemma (`lemma_frame_out_empty_left);
		smt ();

                //woot! done with the inductive case

                //now in the case when tl is None
		ignore (implies_intro ());
		apply_lemma (`lemma_inline_in_patterns_two);
		split_and_smt ();
		split ();
		ignore (implies_intro ());
		apply_lemma (`lemma_frame_out_empty_right);
		split_and_smt ();
		ignore (implies_intro ());
		apply_lemma (`lemma_rw);
		ignore (repeatn 2 split_and_smt);
		apply_lemma (`lemma_frame_out_empty_left);
		split_and_smt ();
		ignore (forall_intro ());
		let h = implies_intro () in rewrite h;
		process_trivial_tail ()))

let lemma_apply_rewrite_assoc_mem1 (m1 m2 m3 m4:memory)
  :Lemma (requires ((m2 <*> (m1 <*> m3)) == m4))
         (ensures  ((m1 <*> (m2 <*> m3)) == m4))
  = ()

let rec rev_append (l1:listptr) (l2:listptr)
  = (match l1 with
     | None   -> l2
     | Some r ->
       let Cell hd tl = !r in
       r := Cell hd l2;
       rev_append tl l1)

    <: STATE listptr (fun p m -> exists (fl1 fl2:list int) (m1 m2:memory).
                                defined (m1 <*> m2) /\
				m == (m1 <*> m2)    /\
				valid l1 fl1 m1     /\
				valid l2 fl2 m2     /\
				(forall mf l. ((Set.equal (dom mf) (Set.union (dom m1) (dom m2))) /\
				          (valid l (List.Tot.rev_acc fl1 fl2) mf)) ==> p l mf))

    by (assume_safe (fun () -> split (); smt ();
               ignore (forall_intros ());
               let h = implies_intro () in let l = __elim_exists_return_binders2 h in
	       let fl1 = List.Tot.hd l in let fl2 = List.Tot.hd (List.Tot.tl l) in
               let h = implies_intro () in let l = __elim_exists_return_binders2 h in
	       let m1 = List.Tot.hd l in let m2 = List.Tot.hd (List.Tot.tl l) in
	       ignore (repeatn 4 implies_and_elim);
	       ignore (implies_intro ());
	       let h = implies_intro () in rewrite h;
	       ignore (implies_intro ());

               //induction on fl1
	       apply_lemma (`__elim_valid_without_match);
	       exact (quote l1); exact (binder_to_term fl1); exact (binder_to_term m1);
	       split_and_smt (); //send the valid on l1 goal to smt

               split (); //split into base case and the inductive case

               //base case, fl1 = []
	       ignore (repeatn 5 implies_and_elim);
	       ignore (implies_intro ()); //valid assumption for l2
	       ignore (implies_intro ()); //this is the forall mf f. keep an eye on it

               split ();

               ignore (implies_intro ());
	       apply_lemma (`lemma_frame_out_empty_left);
	       split_and_smt ();
	       ignore (implies_intro ()); ignore (forall_intro ()); ignore (implies_intro ()); ignore (forall_intro ()); ignore (implies_intro ());
	       split_and_smt ();
	       apply_lemma (`lemma_frame_out_empty_left);
	       smt ();

               //inconsistent
	       ignore (implies_intro ()); smt ();
              
               //inductive case fl1 is cons

               let fl1_hd = forall_intro () in
	       let fl1_tl = forall_intro () in
	       ignore (repeatn 3 implies_and_elim);
	       ignore (implies_intro ());
	       let h = implies_intro () in let l = __elim_exists_return_binders2 h in
	       let l1_tl = List.Tot.hd l in let l1_tail_m = List.Tot.hd (List.Tot.tl l) in
	       ignore (repeatn 2 implies_and_elim);
	       ignore (implies_intros ());
	       
               split ();

               //inconsistent
	       ignore (implies_intro ());
	       smt ();

               ignore (implies_intro ());
	       apply_lemma (`lemma_inline_in_patterns_two);
	       split_and_smt ();

               split ();

               ignore (implies_intro ());
	       apply_lemma (`lemma_frame_out_empty_right);
	       split_and_smt ();

               ignore (forall_intro ());
	       let h = implies_intro () in rewrite h;
	       norm [delta_only ["FStar.Pervasives.Native.__proj__Some__item__v"]];
	       apply_lemma (`lemma_rewrite_sep_assoc4);
	       apply_lemma (`lemma_rw); //!r in the Some branch
	       ignore (repeatn 2 split_and_smt);
	       ignore (repeatn 2 (fun () -> apply_lemma (`lemma_frame_out_empty_right); split_and_smt ()));
	       ignore (forall_intros ()); ignore (implies_intro ());
               apply_lemma (`lemma_rw); //r:= in the Some branch
               ignore (repeatn 2 split_and_smt);

               //give memory to the recursive call
	       apply_lemma (`lemma_frame_out_empty_right);
	       split_and_smt ();

               //partition the recursive call's memory and provide witnesses for existentials
	       witness (binder_to_term fl1_tl);
               //here i want: fl1_hd::fl2
	       //mk_app `Cons (binder_to_term fl1_hd) (binder_to_term fl2)
	       witness (mk_e_app (`Prims.Cons) [binder_to_term fl1_hd; binder_to_term fl2]);
	       witness (binder_to_term l1_tail_m);
	       let uv = uvar_env (cur_env ()) (Some (`SLHeap.memory)) in
	       witness uv;
	       split (); split (); split (); split ();
	       flip ();
               apply_lemma (`lemma_apply_rewrite_assoc_mem1);
	       trefl ();
	       ignore (repeatn 3 smt);

	       ignore (forall_intros ()); ignore (implies_intros ());
	       process_trivial_tail ()))

unfold let equal_dom (m0 m1:memory) =
  Set.equal (dom m0) (dom m1)

let rev (l:listptr)
  = (rev_append l null)

    <: STATE listptr (fun p m -> exists fl. valid l fl m /\
                                    (forall mf l. ((equal_dom m mf) /\
				              (valid l (List.Tot.rev fl) mf)) ==> p l mf))

    by (assume_safe (fun () -> ignore (forall_intro ());
               let m = forall_intro () in
	       let h = implies_intro () in let l = __elim_exists_return_binders1 h in
	       let fl = List.Tot.hd l in
	       let h = implies_intro () in __elim_and h;
	       ignore (implies_intros ());

               //provide existentials for the procedure call
	       witness (binder_to_term fl);
	       witness (`(Prims.Nil #int));
	       witness (binder_to_term m);
	       witness (`SLHeap.emp)))
