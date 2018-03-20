module SL.ExamplesAuto

open SepLogic.Heap
open SL.Effect
open FStar.Algebra.CommMonoid
open FStar.Tactics
open FStar.Tactics.PatternMatching
open CanonCommMonoid
open FStar.Reflection
open FStar.List

// --using_facts_from '* -FStar.Tactics -FStar.Reflection'
#reset-options "--use_two_phase_tc false --__temp_fast_implicits"

let memory_cm : cm memory =
  CM emp (<*>) (fun x -> admit()) (fun x y z -> ()) (fun x y -> ())

// Fails when called
// (Error) user tactic failed: norm_term: Cannot type fun _ -> idtac () <: FStar.Tactics.Effect.TAC unit in context ((r1:SepLogic.Heap.ref Prims.int), (r2:SepLogic.Heap.ref Prims.int), (x:Prims.int), (y:Prims.int), (x:SL.Effect.post Prims.int), (x:SepLogic.Heap.memory), (uu___326511:SepLogic.Heap.defined (r1 |> x <*> r2 |> y) /\ x y (r1 |> 2 <*> r2 |> y))). Error = (Variable "a#327038" not found)
let solve_frame_wp_fails (_:unit) : Tac unit =
  gpm #unit (fun (a:Type) (wp:st_wp a) (post:memory->post a) (m:memory)
            (_ : goal(squash (frame_wp wp post m))) -> idtac()) ()

let frame_wp_qn = ["SL" ; "Effect" ; "frame_wp"]
let write_wp_qn = ["SL" ; "Effect" ; "write_wp"]
let read_wp_qn = ["SL" ; "Effect" ; "read_wp"]
let bind_wp_qn = ["SL" ; "Effect" ; "bind_wp"]
let framepost_qn = ["SL" ; "Effect" ; "frame_post"]
let pointsto_qn = ["SepLogic"; "Heap"; "op_Bar_Greater"]
let ref_qn = ["SepLogic"; "Heap"; "ref"]

let footprint_of (t:term) : Tac (list term) =
  let hd, tl = collect_app t in
  match inspect hd, tl with
  // | Tv_FVar fv, [(ta, Q_Implicit); (tr, Q_Explicit); (tv, Q_Explicit)] ->
  //   if inspect_fv fv = write_wp_qn then [tr]
  //   else fail "not a write_wp"
  // | Tv_FVar fv, [(ta, Q_Implicit); (tr, Q_Explicit)] ->
  //   if inspect_fv fv = read_wp_qn then [tr]
  //   else fail "not a read_wp"
  // -- generalizing the above to arbitrary "footprint expressions"
  | Tv_FVar fv, xs ->
      let footprint_aux (a : argv) : Tac (option term) =
      match inspect (fst (collect_app (tc (fst a)))) with
      | Tv_FVar fv -> if inspect_fv fv = ref_qn then Some (fst a) else None
      | _ -> None
      in FStar.Tactics.Util.filter_map footprint_aux xs
  | _ -> fail "not an applied free variable"

let pack_fv' (n:name) : Tac term = pack (Tv_FVar (pack_fv n))
let eexists (a:Type) (t:unit -> Tac a) : Tac a =
  apply_lemma (`FStar.Classical.exists_intro); later(); norm[];
  fst (divide (ngoals()-1) t dismiss)

let frame_wp_lemma (#a:Type) (#wp:st_wp a) (#f_post:memory -> post a) (m m0 m1:memory)
    (_ : (squash ((m0 <*> m1) == m)))
    (_ : (squash (defined m /\ wp (f_post m1) m0))) :
         (squash (frame_wp wp f_post m)) = ()

let pointsto_to_string (fp_refs:list term) (t:term) : Tac string =
  let hd, tl = collect_app t in
  // dump (term_to_string hd);
  match inspect hd, tl with
  | Tv_FVar fv, [(ta, Q_Implicit); (tr, Q_Explicit); (tv, Q_Explicit)] ->
    if inspect_fv fv = pointsto_qn then
       (if tr `term_mem` fp_refs then "0" else "1") ^ term_to_string tr
    else "2"
  | _, _ -> "2" // have to accept at least Tv_Uvar _ here

let sort_sl (a:Type) (vm:vmap a string) (xs:list var) : Tot (list var) =
  List.Tot.sortWith #var
    (fun x y -> FStar.String.compare (select_extra y vm)
                                     (select_extra x vm)) xs

let canon_monoid_sl (fp:list term) : Tac unit =
  canon_monoid_with string (pointsto_to_string fp) ""
                            sort_sl (fun #a m vm xs -> admit()) memory_cm

let binder_to_term (b : binder) : Tac term =
  let bv, _ = inspect_binder b in pack (Tv_Var bv)

noeq
type cmd =
  | Frame : ta:term -> twp:term -> tpost:term -> tm:term -> cmd
  | Read      : cmd
  | Write     : cmd
  | Bind      : cmd
  | FramePost : cmd
  | Unknown   : option fv ->cmd

let peek_cmd () : Tac cmd =
  let g = cur_goal () in
  let hd, tl = collect_app g in
  match inspect hd, tl with
  | Tv_FVar fv, [(t1, Q_Explicit)] ->
    if inspect_fv fv = squash_qn then
      (* is the goal fram_wp *)
      let hd, tl = collect_app t1 in
      (match inspect hd with
      | Tv_FVar fv  ->
       if inspect_fv fv = frame_wp_qn
       then match tl with
            | [(ta, Q_Implicit);
               (twp, Q_Explicit);
               (tpost, Q_Explicit);
               (tm, Q_Explicit)] -> Frame ta twp tpost tm
            | _ -> fail "Unexpected arity of frame"
       else if inspect_fv fv = read_wp_qn
       then Read
       else if inspect_fv fv = write_wp_qn
       then Write
       else if inspect_fv fv = bind_wp_qn
       then Bind
       else if inspect_fv fv = framepost_qn
       then FramePost
       else Unknown (Some fv)
      | _ -> Unknown None)
   else fail "Unrecognized command: not a squash"
 | _ -> fail "Unrecognized command: not an fv app"

let unfold_first_occurrence (name:string) : Tac unit =
  let should_rewrite (hd:term) : Tac (bool * int) =
    match inspect hd with
    | Tv_FVar fv ->
      if flatten_name (inspect_fv fv) = name
      then true, 2
      else false, 0
    | _ -> false, 0
  in
  let rewrite () : Tac unit =
    norm [delta_only [name]];
    trefl()
  in
  topdown_rewrite should_rewrite rewrite

let __tcut (#b:Type) (a:Type) (_:squash (a ==> b)) (_:squash a)
  :Lemma b
  = ()

let rec sl (i:int) : Tac unit =
  dump ("SL :" ^ string_of_int i);
  match peek_cmd () with
  | Unknown None -> smt()
  | Unknown (Some fv) ->
    // eventually this will use attributes,
    // but we can't currently get at them
    unfold_first_occurrence (fv_to_string fv);
    ignore (repeat (fun () -> FStar.Tactics.split(); smt())); //definedness
    norm[];
    sl (i + 1)

  | Bind ->
    unfold_first_occurrence (%`bind_wp);
    norm[];
    sl (i + 1)

  | Read ->
    unfold_first_occurrence (%`read_wp);
    norm[];
    eexists unit (fun () -> FStar.Tactics.split(); trefl());
    sl (i + 1)

  | Write ->
    unfold_first_occurrence (%`write_wp);
    norm[];
    eexists unit (fun () -> FStar.Tactics.split(); trefl());
    sl (i + 1)

  | FramePost ->
    unfold_first_occurrence (%`frame_post);
    norm[];
    FStar.Tactics.split(); smt(); //definedness
    sl (i + 1)

  | Frame ta twp tpost tm ->
        let fp_refs = footprint_of twp in
        dump ("fp_refs="^ FStar.String.concat ","
           (List.Tot.map term_to_string fp_refs));
        let fp = FStar.Tactics.Util.fold_left
                   (fun a t -> if term_eq a (`emp) then t
                               else mk_e_app (`( <*> )) [a;t])
                   (`emp)
                   (FStar.Tactics.Util.map
                     (fun t -> let u = fresh_uvar (Some (`int)) in
                               mk_e_app (`( |> )) [t; u]) fp_refs) in
         dump ("m0=" ^ term_to_string fp);
        let env = cur_env () in
        let frame = uvar_env env None in
        let tp : term = mk_app (`eq2)
              [((`memory),                     Q_Implicit);
               (mk_e_app (`(<*>)) [fp;frame],  Q_Explicit);
               (tm,                            Q_Explicit)] in
        let new_goal = tp in //mk_e_app (pack_fv' squash_qn) [tp] in
	apply_lemma (mk_e_app (`__tcut) [new_goal]);
        //let heq = tcut new_goal in
         dump "with new goal:";
        flip();
        dump ("before canon_monoid");
        canon_monoid_sl fp_refs;
         dump ("after canon_monoid");
        trefl();
        //norm_binder_type [] heq;
         dump ("after trefl");
	 ignore (implies_intro ());
	 apply_lemma (mk_e_app (`frame_wp_lemma) [tm; fp; frame]);
         //apply_lemma (mk_e_app (`frame_wp_lemma)
        //                [tm; fp; frame; ta; twp; tpost; binder_to_term heq]);
         dump ("after frame lemma - 1");
	 smt ();
        FStar.Tactics.split(); smt(); //definedness
         dump ("after frame lemma - 2");
        sl(i + 1)

let __elim_exists_as_forall
  (#a:Type) (#p:a -> Type) (#phi:Type) (_:(exists x. p x)) (_:squash (forall (x:a). p x ==> phi))
  :Lemma phi
  = ()

let __elim_exists (h:binder) :Tac unit
  = let t = `__elim_exists_as_forall in
    apply_lemma (mk_e_app t [pack (Tv_Var (bv_of_binder h))]);
    clear h

let rec intro_annotated_wp () :Tac binder
  = let h = implies_intro () in
    or_else (fun () -> __elim_exists h; intro_annotated_wp ())
            (fun () -> h)
  
let prelude' () : Tac unit =
   dump "start";
   norm [delta_only [%`st_stronger; "Prims.auto_squash"]];
   mapply (`FStar.Squash.return_squash);
   let post = forall_intro_as "post" in
   let m = forall_intro_as "m" in
   unfold_first_occurrence (%`frame_wp);
   unfold_first_occurrence (%`frame_post);
   norm [];
   let h = implies_intro () in
   __elim_exists h;
   let m0 = forall_intro_as "m0" in
   let h = implies_intro () in
   __elim_exists h;
   let m1 = forall_intro_as "m1" in
   //ignore (implies_intro ());
   
   let wp_annot = intro_annotated_wp () in
   and_elim (pack (Tv_Var (fst (inspect_binder wp_annot))));
   clear wp_annot;
   let hm0 = implies_intro() in
   and_elim (binder_to_term hm0);
   clear hm0;
   ignore (implies_intro ());
   let hm0 = implies_intro () in
   dump "before rewrite";
   rewrite hm0; clear hm0;
   dump "after rewrite";
   let user_annot = implies_intro() in
   norm_binder_type [primops; iota; delta; zeta] user_annot;
   and_elim (binder_to_term user_annot);
   clear user_annot;
   let h = implies_intro () in rewrite h; clear h;
   ignore (implies_intro ())

let sl_auto () : Tac unit =
   prelude'();
   dump "after prelude";
   sl(0)

[@"unfold_for_sl"]
let swap_wp (r1 r2:ref int) (x y:int) =
  fun p m -> m == ((r1 |> x) <*> (r2 |> y)) /\ (defined m /\ p () ((r1 |> y) <*> (r2 |> x)))

let swap0 (r1 r2:ref int) (x y:int)
     : STATE unit (fun post m -> frame_wp (swap_wp r1 r2 x y) (frame_post post) m) by sl_auto
  =
     (let x = !r1 in
     let y = !r2 in
     r1 := y;
     r2 := x)

let rotate_wp (r1 r2 r3:ref int) (x y z:int) =
  fun p m -> m == ((r1 |> x) <*> ((r2 |> y) <*> (r3 |> z))) /\ (defined m /\ p () ((r1 |> z) <*> ((r2 |> x) <*> (r3 |> y))))

let rotate (r1 r2 r3:ref int) (x y z:int)
  : STATE unit (fun post m -> frame_wp (rotate_wp r1 r2 r3 x y z) (frame_post post) m) by sl_auto
  = swap0 r2 r3 y z;
    swap0 r1 r2 x z


// let test (r1 r2:ref int) =
//   (!r1)

//   <: STATE int (fun p m -> exists x y. m == ((r1 |> x) <*> (r2 |> y)) /\ (defined m /\ p x m))

//   by sl_auto

// (*
// //  * two commands
// //  *)
// let write_read (r1 r2:ref int) =
//   (r1 := 2;
//    !r2)
//   <: STATE int (fun p m -> exists x y. m == ((r1 |> x) <*> (r2 |> y)) /\ (defined m /\ p y ((r1 |> 2) <*> (r2 |> y))))
//   by sl_auto

// let read_write (r1 r2:ref int) =
//   (let x = !r1 in
//    r2 := x)
//   <: STATE unit (fun p m -> exists x y. m == ((r1 |> x) <*> (r2 |> y)) /\ (defined m /\ p () ((r1 |> x) <*> (r2 |> x))))
//   by sl_auto

// (*
// //  * four commands
// //  *)
// let swap (r1 r2:ref int)
//      : STATE unit (fun post m -> exists x y. m == ((r1 |> x) <*> (r2 |> y)) /\ (defined m /\ post () ((r1 |> y) <*> (r2 |> x)))) by sl_auto
//   = (let x = !r1 in
//      let y = !r2 in
//      r1 := y;
//      r2 := x)

// let call (#wp:...) (f:unit -> STATE 'a (fun :STATE unit (fun p m -> frame_wp (

