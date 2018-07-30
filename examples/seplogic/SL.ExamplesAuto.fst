module SL.ExamplesAuto

(* cf. #1323, #1465 *)
module SLHeap = SL.Heap

open SL.Heap
open SL.Effect
open FStar.Algebra.CommMonoid
open FStar.Tactics
open FStar.Tactics.PatternMatching
open CanonCommMonoid
open FStar.Reflection
open FStar.List

// --using_facts_from '* -FStar.Tactics -FStar.Reflection'
#reset-options "--__temp_fast_implicits"

let memory_cm : cm memory =
  CM emp (<*>) (fun x -> lemma_sep_unit' x) (fun x y z -> ()) (fun x y -> ())

// Fails when called
// (Error) user tactic failed: norm_term: Cannot type fun _ -> idtac () <: FStar.Tactics.Effect.TAC unit in context ((r1:SepLogic.Heap.ref Prims.int), (r2:SepLogic.Heap.ref Prims.int), (x:Prims.int), (y:Prims.int), (x:SL.Effect.post Prims.int), (x:SepLogic.Heap.memory), (uu___326511:SepLogic.Heap.defined (r1 |> x <*> r2 |> y) /\ x y (r1 |> 2 <*> r2 |> y))). Error = (Variable "a#327038" not found)
let solve_frame_wp_fails (_:unit) : Tac unit =
  gpm #unit (fun (a:Type) (wp:st_wp a) (post:memory->post a) (m:memory)
            (_ : pm_goal(squash (frame_wp wp post m))) -> idtac()) ()

let frame_wp_qn = ["SL" ; "Effect" ; "frame_wp"]
let write_wp_qn = ["SL" ; "Effect" ; "write_wp"]
let read_wp_qn = ["SL" ; "Effect" ; "read_wp"]
let bind_wp_qn = ["SL" ; "Effect" ; "bind_wp"]
let framepost_qn = ["SL" ; "Effect" ; "frame_post"]
let pointsto_qn = ["SL"; "Heap"; "op_Bar_Greater"]
let ref_qn = ["SL"; "Heap"; "ref"]
let ite_wp_qn = ["SL"; "Effect"; "st_ite_wp"]
let if_then_else_wp_qn = ["SL"; "Effect"; "st_if_then_else"]
let close_wp_qn = ["SL"; "Effect"; "st_close_wp"]
let assume_p_qn = ["SL"; "Effect"; "st_assume_p"]

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

let ite_wp_lemma (#a:Type) (#wp:st_wp a) (#post:post a) (#m:memory)
  (_:squash (wp post m))
  :Lemma (st_ite_wp a wp post m)
  = ()

let if_then_else_wp_lemma (#a:Type) (#b:Type) (#then_wp:st_wp a) (#else_wp:st_wp a) (#post:post a) (#m:memory)
  (_:squash (b   ==> then_wp post m))
  (_:squash (~ b ==> else_wp post m))
  :Lemma (st_if_then_else a b then_wp else_wp post m)
  = ()

let close_wp_lemma (#a:Type) (#b:Type) (#wp:(b -> GTot (st_wp a))) (#post:post a) (#m:memory)
  (_:squash (forall b. wp b post m))
  :Lemma (st_close_wp a b wp post m)
  = ()

let assume_p_lemma (#a:Type) (#p:Type) (#wp:st_wp a) (#post:post a) (#m:memory)
  (_:squash (p ==> wp post m))
  :Lemma (st_assume_p a p wp post m)
  = ()

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

let sort_sl (a:Type) (vm:vmap a string) (xs:list var) : Tot (list var) =
  List.Tot.sortWith #var
    (fun x y -> FStar.String.compare (select_extra y vm)
                                     (select_extra x vm)) xs

let sort_sl_correct : permute_correct sort_sl =
  fun #a m vm xs -> sortWith_correct (fun x y -> FStar.String.compare (select_extra y vm) (select_extra x vm)) #a m vm xs

let canon_monoid_sl (fp:list term) : Tac unit =
  canon_monoid_with string (pointsto_to_string fp) ""
                            sort_sl (fun #a -> sort_sl_correct #a) memory_cm

let binder_to_term (b : binder) : Tac term =
  let bv, _ = inspect_binder b in pack (Tv_Var bv)

noeq
type cmd =
  | Frame : ta:term -> twp:term -> tpost:term -> tm:term -> cmd
  | Read      : cmd
  | Write     : cmd
  | Bind      : cmd
  | Ite       : cmd
  | IfThenElse: cmd
  | Close     : cmd
  | Assume    : cmd
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
       else if inspect_fv fv = ite_wp_qn
       then Ite
       else if inspect_fv fv = if_then_else_wp_qn
       then IfThenElse
       else if inspect_fv fv = close_wp_qn
       then Close
       else if inspect_fv fv = assume_p_qn
       then Assume
       else if inspect_fv fv = framepost_qn
       then FramePost
       else if inspect_fv fv = exists_qn  //if it is exists x. then we can't unfold, so return None
       then Unknown None
       else if inspect_fv fv = false_qn  //AR: TODO: this is quite hacky, we need a better way
       then Unknown None
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

//in procedure calls, the callee wp might involve some exists x y. sort of stuff, if so solve them by trefl
//initial call set use_trefl to false
//return t_refl if we did some something, so that the caller can make progress on rest of the VC
let rec solve_procedure_ref_value_existentials (use_trefl:bool) :Tac bool =
  let g = cur_goal () in
  match term_as_formula g with
  | Exists x t ->
    let w = uvar_env (cur_env ()) (Some (inspect_bv x).bv_sort) in
    witness w;
    solve_procedure_ref_value_existentials true
  | _ ->
   if use_trefl then begin FStar.Tactics.split (); trefl (); true end
   else false

let rec sl (i:int) : Tac unit =
  //dump ("SL :" ^ string_of_int i);

  //post procedure call, we sometimes have a m == m kind of expression in the wp
  //this will solve it in the tactic itself rather than farming it out to smt
  norm [simplify];
  match peek_cmd () with
  | Unknown None ->
    //either we are done
    //or we are stuck at some existential in procedure calls
    let cont = solve_procedure_ref_value_existentials false in
    if cont then sl (i + 1)
    else smt ()
  | Unknown (Some fv) ->
    //so here we are unfolding something like swap_wp below

    // eventually this will use attributes,
    // but we can't currently get at them
    unfold_first_occurrence (fv_to_string fv);
    ignore (repeat (fun () -> FStar.Tactics.split(); smt())); //definedness
    norm [];
    sl (i + 1)

  | Bind ->
    unfold_first_occurrence (`%bind_wp);
    norm[];
    sl (i + 1)

  | Ite ->
    apply_lemma (`ite_wp_lemma);
    sl (i + 1)

  | IfThenElse ->
    apply_lemma (`if_then_else_wp_lemma);
    //we now have 2 goals

    let f () :Tac unit =
      ignore (implies_intro ());
      sl (i + 1)
    in

    ignore (divide 1 f f)

  | Close ->
    apply_lemma (`close_wp_lemma);
    ignore (forall_intros ());
    sl (i + 1)

  | Assume ->
    apply_lemma (`assume_p_lemma);
    ignore (implies_intro ());
    sl (i + 1)

  | Read ->
    unfold_first_occurrence (`%read_wp);
    norm[];
    eexists unit (fun () -> FStar.Tactics.split(); trefl());
    sl (i + 1)

  | Write ->
    unfold_first_occurrence (`%write_wp);
    norm[];
    eexists unit (fun () -> FStar.Tactics.split(); trefl());
    sl (i + 1)

  | FramePost ->
    unfold_first_occurrence (`%frame_post);
    norm[];
    FStar.Tactics.split(); smt(); //definedness
    sl (i + 1)

  | Frame ta twp tpost tm ->
    //we are at frame_wp, real work starts

    //compute the footprint from the arg (e.g. read_wp r1, swap_wp r1 r2, etc.)
    let fp_refs = footprint_of twp in
    //dump ("fp_refs="^ FStar.String.concat "," (List.Tot.map term_to_string fp_refs));

    //build the footprint memory expression, uvars for ref values, and join then
    let fp = FStar.Tactics.Util.fold_left
               (fun a t -> if term_eq a (`emp) then t
                        else mk_e_app (`( <*> )) [a;t])
               (`emp)
               (FStar.Tactics.Util.map
                 (fun t -> let u = fresh_uvar (Some (`int)) in
                        mk_e_app (`( |> )) [t; u]) fp_refs)
    in
    //dump ("m0=" ^ term_to_string fp);

    //introduce another uvar for the _frame_
    let env = cur_env () in
    let frame = uvar_env env (Some (`SLHeap.memory)) in

    //make the term equating the fp join frame with the current memory
    let tp :term = mk_app (`eq2)
                   [((`memory),                     Q_Implicit);
                    (mk_e_app (`(<*>)) [fp;frame],  Q_Explicit);
                    (tm,                            Q_Explicit)] in

    //cut
    apply_lemma (mk_e_app (`__tcut) [tp]);
    //dump "with new goal:";

    //flip so that the current goal is the equality of memory expressions
    flip();
    
    //dump ("before canon_monoid");
    canon_monoid_sl fp_refs;
    //dump ("after canon_monoid");
    trefl();
    //dump ("after trefl");

    //this is the a ==> b thing when we did cut above
    let cut_hyp = implies_intro () in

    //sort of beta step
    let fp = norm_term [] fp in  //if we don't do these norms, fast implicits don't kick in because of lambdas
    let frame = norm_term [] frame in
    apply_lemma (mk_e_app (`frame_wp_lemma) [tm; fp; frame]);
    //dump ("after frame lemma - 1");

    //equality goal from frame_wp_lemma
    mapply (binder_to_term cut_hyp);

    FStar.Tactics.split(); smt(); //definedness
    //dump ("after frame lemma - 2");
    sl(i + 1)

let __elim_exists_as_forall
  (#a:Type) (#p:a -> Type) (#phi:Type) (_:(exists x. p x)) (_:squash (forall (x:a). p x ==> phi))
  :Lemma phi
  = ()

let __elim_exists (h:binder) :Tac unit
  = let t = `__elim_exists_as_forall in
    apply_lemma (mk_e_app t [pack (Tv_Var (bv_of_binder h))]);
    clear h

let prelude' () : Tac unit =
  //take care of some auto_squash stuff
  //dump "start";
  norm [delta_only [`%st_stronger; "Prims.auto_squash"]];
  mapply (`FStar.Squash.return_squash);

  //forall post m. 
  let post = forall_intro_as "post" in
  let m = forall_intro_as "m" in

  //wps are written in the style frame_wp (<small footprint wp> (frame_post post) ...
  //unfold frame_wp and frame_post in the annotated wp
  unfold_first_occurrence (`%frame_wp);
  unfold_first_occurrence (`%frame_post);
  norm [];

  //unfolding frame_wp introduces two existentials m0 and m1 for frames
  //introduce them in the context
  let h = implies_intro () in
  __elim_exists h;
  let m0 = forall_intro_as "m0" in
  let h = implies_intro () in
  __elim_exists h;
  let m1 = forall_intro_as "m1" in

  //the goal might start with exists x y. to quantify over the ref values

  //now the goal looks something like (defined m0 * m1 /\ (m == m0 * m1 /\ (...)))
  //do couple of implies_intro and and_elim to get these conjections
  let h = implies_intro () in and_elim (binder_to_term h); clear h;
  let h = implies_intro() in and_elim (binder_to_term h); clear h;

  //defined m0 * m1
  ignore (implies_intro ());

  //this is the m = ..., introduced by the frame_wp
  let m0 = implies_intro () in
  //dump "before rewrite";
  rewrite m0; clear m0;
  //dump "after rewrite";

  //dump "Before elim ref values";
  ignore (repeat (fun () -> let h = implies_intro () in
                           __elim_exists h;
			   ignore (forall_intro ())));
  //dump "After elim ref values";

  //now we are at the small footprint style wp
  //we should full norm it, so that we can get our hands on the m0 == ..., i.e. the footprint of the command
  let user_annot = implies_intro() in
  norm_binder_type [primops; iota; delta; zeta] user_annot;
  and_elim (binder_to_term user_annot);
  clear user_annot;

  //the first conjunct there is the m0 = ..., so inline it
  let h = implies_intro () in rewrite h; clear h;

  //push rest of the lhs implicatio in the context
  ignore (implies_intro ())

let sl_auto () : Tac unit =
   prelude'();
   //dump "after prelude";
   sl(0)

effect ST (a:Type) (wp:st_wp a) = STATE a (fun post m -> frame_wp wp (frame_post post) m)


let swap_wp (r1 r2:ref int) = fun p m -> exists x y. m == (r1 |> x <*> r2 |> y) /\ p () (r1 |> y <*> r2 |> x)

let swap (r1 r2:ref int) :ST unit (swap_wp r1 r2) by (sl_auto ())
  = let x = !r1 in
    let y = !r2 in
    r1 := y;
    r2 := x

let rotate_wp (r1 r2 r3:ref int)
  = fun p m -> exists x y z. m == (r1 |> x <*> r2 |> y <*> r3 |> z) /\ p () (r1 |> z <*> r2 |> x <*> r3 |> y)

let rotate (r1 r2 r3:ref int) :ST unit (rotate_wp r1 r2 r3) by (sl_auto ())
  = swap r2 r3;
    swap r1 r2

let test (r1 r2:ref int) :ST int (fun p m -> exists x y. m == (r1 |> x <*> r2 |> y) /\ p x m) by (sl_auto ())
  = !r1

(*
 * two commands
 *)
let write_read (r1 r2:ref int) :ST int (fun p m -> exists x y. m == (r1 |> x <*> r2 |> y) /\ p y (r1 |> 2 <*> r2 |> y)) by (sl_auto ())
  = r1 := 2;
    !r2

let read_write (r1 r2:ref int) :ST unit (fun p m -> exists x y. m == (r1 |> x <*> r2 |> y) /\ p () (r1 |> x <*> r2 |> x)) by (sl_auto ())
  = let x = !r1 in
    r2 := x


let cond_test (r:ref int) (b:bool) :ST unit (fun p m -> exists x. m == r |> x /\ ((b   ==> p () (r |> 1)) /\
                                                                      (~ b ==> p () (r |> 2))))
  by (prelude' (); sl 0)

  = if b then r := 1 else r := 2

let rotate_left_or_right (r1 r2 r3:ref int) (b:bool)
  :ST unit (fun p m -> exists x y z. m == (r1 |> x <*> r2 |> y <*> r3 |> z) /\
                             ((b   ==> p () (r1 |> z <*> r2 |> x <*> r3 |> y)) /\
			      (~ b ==> p () (r1 |> y <*> r2 |> z <*> r3 |> x))))
  by (sl_auto ())

  = if b then rotate r1 r2 r3 else rotate r3 r2 r1
