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
  CM emp (<*>) (fun x -> ()) (fun x -> admit()) (fun x y z -> ()) (fun x y -> ())

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

let footprint_of (t:term) : Tac (list term) =
  let hd, tl = collect_app t in
  match inspect hd, tl with
  | Tv_FVar fv, [(ta, Q_Implicit); (tr, Q_Explicit); (tv, Q_Explicit)] ->
    if inspect_fv fv = write_wp_qn then [tr]
    else fail "not a write_wp"
  | Tv_FVar fv, [(ta, Q_Implicit); (tr, Q_Explicit)] ->
    if inspect_fv fv = read_wp_qn then [tr]
    else fail "not a read_wp"
  | _ -> fail "not an applied free variable"

let pack_fv' (n:name) : Tac term = pack (Tv_FVar (pack_fv n))
let eexists (a:Type) (t:unit -> Tac a) : Tac a =
  apply_lemma (`FStar.Classical.exists_intro); later(); norm[];
  fst (divide (ngoals()-1) t dismiss)

let frame_wp_lemma (m0 m1:memory) (a:Type) (wp:st_wp a)
    (f_post:memory -> post a) : Lemma
  (requires (defined (m0 <*> m1) /\ wp (f_post m1) m0))
  (ensures (frame_wp wp f_post (m0 <*> m1))) = ()

let frame_wp_lemma_with_squashes (m m0 m1:memory) (a:Type) (wp:st_wp a)
    (f_post:memory -> post a)
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

let sort_sl (a:Type) (vm:vmap a string) (xs:list var) =
  List.Tot.sortWith #var
    (fun x y -> FStar.String.compare (select_extra x vm)
                                     (select_extra y vm)) xs

let canon_monoid_sl fp =
  canon_monoid_with string (pointsto_to_string fp) ""
                           sort_sl (fun #a m vm xs -> admit())

let binder_to_term (b : binder) : Tac term =
  let bv, _ = inspect_binder b in pack (Tv_Var bv)

noeq
type cmd =
  | Frame : ta:term -> twp:term -> tpost:term -> tm:term -> cmd
  | Read      : cmd
  | Write     : cmd
  | Bind      : cmd
  | FramePost : cmd
  | Unknown   : cmd

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
       else Unknown
      | _ -> Unknown)
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

let rec sl (i:int) : Tac unit =
  dump ("SL :" ^ string_of_int i);
//  admit();
  match peek_cmd () with
  | Unknown -> smt ()

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
        // dump ("fp_refs="^ FStar.String.concat ","
        //   (List.Tot.map term_to_string fp_refs));
        let fp = FStar.Tactics.Util.fold_left
                   (fun a t -> if term_eq a (`emp) then t
                               else mk_e_app (`( <*> )) [a;t])
                   (`emp)
                   (FStar.Tactics.Util.map
                     (fun t -> let u = fresh_uvar (Some (`int)) in
                               mk_e_app (`( |> )) [t; u]) fp_refs) in
        // dump ("m0=" ^ term_to_string fp);
        let env = cur_env () in
        let frame = uvar_env env (Some (`memory)) in
        let tp : term = mk_app (`eq2)
              [((`memory),                     Q_Implicit);
               (mk_e_app (`(<*>)) [fp;frame],  Q_Explicit);
               (tm,                            Q_Explicit)] in
        let new_goal = mk_e_app (pack_fv' squash_qn) [tp] in
        let heq = tcut new_goal in
        // dump "with new goal:";
        flip();
        // dump ("before canon_monoid");
        canon_monoid_sl fp_refs memory_cm;
        // dump ("after canon_monoid");
        trefl();
        // dump ("after trefl");
        // let fp : term = norm_term [] fp in
        // let frame : term = norm_term [] frame in
        // dump ("m0/fp=" ^ term_to_string fp ^ "\n" ^
        //       "m1/frame=" ^ term_to_string frame ^ "\n" ^
        //       "a/ta=" ^ term_to_string ta ^ "\n" ^
        //       "wp/twp=" ^ term_to_string twp ^ "\n" ^
        //       "f_post/tpost=" ^ term_to_string tpost);
        apply_lemma (mk_e_app (`frame_wp_lemma_with_squashes)
                       [tm; fp; frame; ta; twp; tpost; binder_to_term heq]);
        FStar.Tactics.split(); smt(); //definedness
        // dump ("after frame lemma");
        sl(i + 1)

let prelude' () : Tac unit =
   dump "start";
   norm [delta_only [%`st_stronger; "Prims.auto_squash"]];
   mapply (`FStar.Squash.return_squash);
   let post = forall_intro () in
   let m0 = forall_intro () in
   let wp_annot = implies_intro() in
   and_elim (pack (Tv_Var (fst (inspect_binder wp_annot))));
   clear wp_annot;
   let hm0 = implies_intro() in
   rewrite hm0; clear hm0;
   ignore (implies_intro() )

let sl' () : Tac unit =
   prelude'();
   dump "after prelude";
   sl(0)

(*
 * two commands
 *)
let write_read (r1 r2:ref int) (x y:int) =
  (r1 := 2;
   !r2)
  <: STATE int (fun p m -> m == ((r1 |> x) <*> (r2 |> y)) /\ (defined m /\ p y ((r1 |> 2) <*> (r2 |> y))))
  by sl'

let read_write (r1 r2:ref int) (x y:int) =
  (let x = !r1 in
   r2 := x)
  <: STATE unit (fun p m -> m == ((r1 |> x) <*> (r2 |> y)) /\ (defined m /\ p () ((r1 |> x) <*> (r2 |> x))))
  by sl'

(*
 * four commands
 *)
let swap (r1 r2:ref int) (x y:int)
  = (let x = !r1 in
     let y = !r2 in
     r1 := y;
     r2 := x)

     <: STATE unit (fun post m -> m == ((r1 |> x) <*> (r2 |> y)) /\ (defined m /\ post () ((r1 |> y) <*> (r2 |> x))))

     by sl'
