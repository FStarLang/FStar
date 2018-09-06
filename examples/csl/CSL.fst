module CSL

(* This is mostly a copy of SL.ExamplesAuto, until we make it more extensible. *)

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

let with_footprint (fp : list (ref int)) (x:'a) : 'a = x

let par_comp #a #b (wpa : st_wp a) (wpb : st_wp b) post m1 m2 =
   defined (m1 <*> m2) ==> 
   wpa (fun a m1' -> wpb (fun b m2' -> defined (m1' <*> m2') /\ post (a, b) (m1' <*> m2')) m2) m1
	
let par_wp' #a #b (wpa : st_wp a) (wpb : st_wp b) post m =
    exists m1 m2.
           defined (m1 <*> m2)
        /\ m == (m1 <*> m2)
        /\ par_comp wpa wpb post m1 m2

(* Silly lemma, but allows to handle goals properly *)
let par_wp'_lemma
  #a #b
  (#wpa : st_wp a)
  (#wpb : st_wp b)
  (m m1 m2 : memory)
  (post : post (a * b))
  (_ : squash (defined (m1 <*> m2)))
  (_ : squash (m == (m1 <*> m2)))
  (_ : squash (par_comp wpa wpb post m1 m2))
  //(_ : squash (wpa (fun a m1' -> forall b. post (a, b) m1') m1))
  //(_ : squash (wpb (fun b m2' -> forall a. post (a, b) m2') m2))
     : Lemma (defined (m1 <*> m2)
               /\ m == (m1 <*> m2)
               /\ (par_comp wpa wpb post m1 m2)) = ()

let frame_wp_lemma (#a:Type) (#wp:st_wp a) (#f_post:memory -> post a) (m m0 m1:memory)
    (_ : squash ((m0 <*> m1) == m))
    (_ : squash (defined m))
    (_ : squash (wp (f_post m1) m0)) :
         (squash (frame_wp wp f_post m)) = ()

let par_wp #a #b (wpa : st_wp a) (wpb : st_wp b) : st_wp (a * b) =
  fun post m0 -> frame_wp (par_wp' wpa wpb) (frame_post post) m0

assume val par : (#a:Type) -> (#b:Type) ->
                 (#wpa : st_wp a) ->  (#wpb : st_wp b) ->
                 ($f : (unit -> STATE a wpa)) ->
                 ($g : (unit -> STATE b wpb)) ->
                 STATE (a * b) (par_wp wpa wpb)



(* Locks and operations *)
// Locks are over a particular reference r.
// Can we use a list or a set? Non-trivial to make it work. Even a set of addresses causes many blowups.
// Can we use a heap predicate? Can we automate frame inference then?
assume new type lock : #a:Type -> ref a -> Type0

let mklock_wp #a (r:ref a) post m = exists v. m == r |> v /\ (forall (l:lock r). post l emp)
let frame_mklock_wp r post m0 = frame_wp (mklock_wp r) (frame_post post) m0
assume val mklock : #a:Type -> (r: ref a) ->
		    STATE (lock r) (frame_mklock_wp r)

  //let l = mklock r in
  //acquire l;
  //par (fun () -> acquire l; r := 2; release l)
  //    (fun () -> r := !r + 1; release l)


let acquire_wp r l post m = m == emp /\ (forall v. post () (r |> v))
let frame_acquire_wp r l post m0 = frame_wp (acquire_wp r l) (frame_post post) m0
assume val acquire : #a:Type -> (#r: ref a) -> (l : lock r) ->
		     STATE unit (frame_acquire_wp r l)


let release_wp r l post m = (exists v. m == r |> v) /\ post () emp
let frame_release_wp r l post m0 = frame_wp (release_wp r l) (frame_post post) m0
assume val release : #a:Type -> (#r: ref a) -> (l : lock r) ->
		     STATE unit (frame_release_wp r l)


// let locking_wp r l wp post m =
//     wp (fun x m' -> forall v m1. m' == (r |> v <*> m1) ==> post x m1) m
// 
// assume val locking : #a:Type -> #b:Type -> #r:(ref a) -> (l : lock r) ->
//                      (#wp : st_wp b) -> (f : unit -> STATE b wp) ->
// 		     STATE b (frame_locking_wp r l wp)


(* A version with explicit heaps *)
unfold let par_wp'_exp #a #b (wpa : st_wp a) (wpb : st_wp b) (m1 m2 : memory)
                       (post : post (a * b)) (m : memory) : Type0 =
         defined (m1 <*> m2)
        /\ m == (m1 <*> m2)
        /\ wpa (fun a m1' -> wpb (fun b m2' -> post (a, b) (m1' <*> m2')) m2) m1

let par_wp_exp #a #b (wpa : st_wp a) (wpb : st_wp b) (m1 m2 : memory) : st_wp (a * b) =
  fun post m0 -> frame_wp (par_wp'_exp wpa wpb m1 m2) (frame_post post) m0

assume val par_exp : (#a:Type) -> (#b:Type) ->
                 (#wpa : st_wp a) ->  (#wpb : st_wp b) ->
                 (m1 : memory) -> (m2 : memory) ->
                 ($f : (unit -> STATE a wpa)) ->
                 ($g : (unit -> STATE b wpb)) ->
                 STATE (a * b) (par_wp_exp #a #b wpa wpb m1 m2)

(* Unframed, explicit variant. Not very user-friendly. *)
assume val par_exp' : (#a:Type) -> (#b:Type) ->
                 (#wpa : st_wp a) ->  (#wpb : st_wp b) ->
                 (m1 : memory) -> (m2 : memory) ->
                 ($f : (unit -> STATE a wpa)) ->
                 ($g : (unit -> STATE b wpb)) ->
                 STATE (a * b) (par_wp'_exp #a #b wpa wpb m1 m2)

let memory_cm : cm memory =
  CM emp (<*>) (fun x -> lemma_sep_unit' x) (fun x y z -> ()) (fun x y -> ())

let frame_wp_qn = ["SL" ; "Effect" ; "frame_wp"]
let write_wp_qn = ["SL" ; "Effect" ; "write_wp"]
let read_wp_qn = ["SL" ; "Effect" ; "read_wp"]
let bind_wp_qn = ["SL" ; "Effect" ; "bind_wp"]
let par_wp_qn = `%par_wp' // small-footprint-style
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
      //if String.concat "." (inspect_fv fv) = `%mklock_wp then [] else
      //if String.concat "." (inspect_fv fv) = `%release_wp then [] else
      if String.concat "." (inspect_fv fv) = `%acquire_wp then [] else
      let footprint_aux (a : argv) : Tac (option term) =
      match inspect (fst (collect_app (tc (fst a)))) with
      | Tv_FVar fv -> if inspect_fv fv = ref_qn then Some (fst a) else None
      | _ -> None
      in FStar.Tactics.Util.filter_map footprint_aux xs
  | _ -> fail "not an applied free variable"
  
let footprint_R (t:term) : Tac (list term) =
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
      if String.concat "." (inspect_fv fv) = `%acquire_wp then [] else
      let footprint_aux (a : argv) : Tac (option term) =
      match inspect (fst (collect_app (tc (fst a)))) with
      | Tv_FVar fv -> if inspect_fv fv = ref_qn then Some (fst a) else None
      | _ -> None
      in FStar.Tactics.Util.filter_map footprint_aux xs
  | _ -> fail "not an applied free variable"
  
let footprint_W (t:term) : Tac (list term) =
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
      if String.concat "." (inspect_fv fv) = `%release_wp then [] else
      let footprint_aux (a : argv) : Tac (option term) =
      match inspect (fst (collect_app (tc (fst a)))) with
      | Tv_FVar fv -> if inspect_fv fv = ref_qn then Some (fst a) else None
      | _ -> None
      in FStar.Tactics.Util.filter_map footprint_aux xs
  | _ -> fail "not an applied free variable"

let pack_fv' (n:name) : Tac term = pack (Tv_FVar (pack_fv n))

(* `t` receives the existential witness *)
let eexists (#a:Type) (t:term -> Tac a) : Tac a =
  apply_lemma (`FStar.Classical.exists_intro);
  let w = cur_witness () in
  dismiss ();
  norm [];
  t w

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
  | Cont      : string -> cmd
  | Read      : cmd
  | Write     : cmd
  | Bind      : cmd
  | Par       : ta:term -> tb:term -> wpa:term -> wpb:term -> post:term -> m:term -> cmd
  | Ite       : cmd
  | IfThenElse: cmd
  | Forall    : cmd
  | Eq2       : t:term -> l:term -> r:term -> cmd
  | Implies   : cmd
  | Squash    : cmd
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
       else if String.concat "." (inspect_fv fv) = par_wp_qn
       then match tl with
	    | [(ta, Q_Implicit);
	       (tb, Q_Implicit);
	       (wpa, Q_Explicit);
	       (wpb, Q_Explicit);
	       (post, Q_Explicit);
	       (m, Q_Explicit)] -> Par ta tb wpa wpb post m
	    | _ -> fail "unexpected arity of par_wp'"
       else if String.concat "." (inspect_fv fv) = `%acquire_wp
       then Cont (`%acquire_wp)
       else if String.concat "." (inspect_fv fv) = `%release_wp
       then Cont (`%release_wp)
       else if inspect_fv fv = bind_wp_qn
       then Bind
       else if inspect_fv fv = squash_qn
       then Squash
       else if inspect_fv fv = ite_wp_qn
       then Ite
       else if inspect_fv fv = if_then_else_wp_qn
       then IfThenElse
       else if inspect_fv fv = close_wp_qn
       then Close
       else if inspect_fv fv = imp_qn
       then Implies
       else if inspect_fv fv = forall_qn
       then Forall
       else if inspect_fv fv = eq2_qn
       then match tl with
            | [(t, Q_Implicit);
               (l, Q_Explicit);
               (r, Q_Explicit)] -> Eq2 t l r
            | _ -> fail "Unexpected arity of eq2"
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
//return true if we did some something, so that the caller can make progress on rest of the VC
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
  dump ("SL:" ^ string_of_int i);

  //post procedure call, we sometimes have a m == m kind of expression in the wp
  //this will solve it in the tactic itself rather than farming it out to smt
  norm [simplify];
  let r = peek_cmd () in
  dump ("r = " ^ term_to_string (quote r));
  match r with
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
    ignore (repeat (fun () -> FStar.Tactics.split(); trefl `or_else` smt));
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

  | Forall ->
    ignore (forall_intros ());
    sl (i + 1)

  | Eq2 _ _ _ ->
    trefl `or_else` smt;
    sl (i + 1)

  | Implies ->
    ignore (implies_intros ());
    sl (i + 1)

  | Squash ->
    // eliminate double squashes
    apply_lemma (`FStar.Squash.return_squash);
    sl (i + 1)

  | Assume ->
    apply_lemma (`assume_p_lemma);
    ignore (implies_intro ());
    sl (i + 1)

  | Cont lid ->
    unfold_first_occurrence lid;
    norm[];
    sl (i + 1)

  | Read ->
    unfold_first_occurrence (`%read_wp);
    norm[];
    eexists (fun _ -> FStar.Tactics.split(); trefl());
    sl (i + 1)
    
  | Write ->
    unfold_first_occurrence (`%write_wp);
    norm[];
    eexists (fun _ -> FStar.Tactics.split(); trefl());
    sl (i + 1)
    
  | Par ta tb wpa wpb post m ->
    dump "GG par 0";

    let wpa = norm_term [delta] wpa in
    dump ("norm(wpa) = " ^ term_to_string wpa);
    let wpb = norm_term [delta] wpb in
    dump ("norm(wpb) = " ^ term_to_string wpb);
    
    //let fp_refs_a = footprint_of wpa in
    //dump ("fp_refs_a ="^ FStar.String.concat "," (List.Tot.map term_to_string fp_refs_a));
    //
    //let fp_refs_b = footprint_of wpb in
    //dump ("fp_refs_b ="^ FStar.String.concat "," (List.Tot.map term_to_string fp_refs_b));

    dump "GG par";
    //witness (`emp);
    //witness (`emp);

    eexists (fun _ha ->
    eexists (fun _hb ->
        dump "GG 1";
	apply_lemma (`par_wp'_lemma);
	smt ();
	later ();
	dump "GG 5";
        unfold_first_occurrence (`%par_comp);
	dump "GG 6";
        unfold_first_occurrence (`%bind_wp);
	dump "GG 6.1";
	let _ = implies_intro_force () in
	// dump "GG 7";
	// FStar.Tactics.split (); trefl ();
	// dump "GG 8";
	// FStar.Tactics.split (); trefl ();
	dump "GG 9";
	iseq [  (fun () -> sl (i + 1));
	      //; (fun () -> sl (i + 1))
	      ]))
    //));
    //sl (i + 1)
    
    //		dump "GG 4";
    //		repeatseq (fun () -> ignore (FStar.Tactics.split ()));
    //		dump "GG 5";
    //		smt (); // defined
    //		dump "GG 6";
    //		smt (); // separating conjunction
    //		dump "GG 7";
    //		trefl ();
    //		dump "GG 8";
    //		trefl ()
    //            ))
    //);
    //sl (i + 1)

  | FramePost ->
    unfold_first_occurrence (`%frame_post);
    norm[];
    FStar.Tactics.split(); smt(); //definedness
    sl (i + 1)

  | Frame ta twp tpost tm ->
    //we are at frame_wp, real work starts

    //compute the footprint from the arg (e.g. read_wp r1, swap_wp r1 r2, etc.)
    dump ("twp = " ^ term_to_string twp);
    let twp' = norm_term [delta] twp in
    dump ("norm(twp) = " ^ term_to_string twp');
    //let fp_refs_w = footprint_W twp in
    //dump ("fp_refs_w ="^ FStar.String.concat "," (List.Tot.map term_to_string fp_refs_w));
    
    let fp_refs_r = footprint_of twp in
    dump ("fp_refs_r ="^ FStar.String.concat "," (List.Tot.map term_to_string fp_refs_r));

    //build the footprint memory expression, uvars for ref values, and join then
    let fp_r = FStar.Tactics.Util.fold_left
                 (fun a t -> if term_eq a (`emp) then t
                          else mk_e_app (`( <*> )) [a;t])
                 (`emp)
                 (FStar.Tactics.Util.map
                   (fun t -> let u = fresh_uvar (Some (`int)) in
                          mk_e_app (`( |> )) [t; u]) fp_refs_r)
    in
    //let fp_w = FStar.Tactics.Util.fold_left
    //             (fun a t -> if term_eq a (`emp) then t
    //                      else mk_e_app (`( <*> )) [a;t])
    //             (`emp)
    //             (FStar.Tactics.Util.map
    //               (fun t -> let u = fresh_uvar (Some (`int)) in
    //                      mk_e_app (`( |> )) [t; u]) fp_refs_w)
    //in
    dump ("m0 =" ^ term_to_string fp_r);
    //dump ("m1 =" ^ term_to_string fp_w);

    //introduce another uvar for the _frame_
    let env = cur_env () in
    let frame = uvar_env env (Some (`SLHeap.memory)) in

    //make the term equating the fp join frame with the current memory
    let tp :term = mk_app (`eq2)
                   [((`memory),                     Q_Implicit);
                    (mk_e_app (`(<*>)) [fp_r;frame],  Q_Explicit);
                    (tm,                            Q_Explicit)] in

    //cut
    apply_lemma (mk_e_app (`__tcut) [tp]);
    dump "with new goal:";

    //flip so that the current goal is the equality of memory expressions
    flip();
    
    dump ("before canon_monoid");
    canon_monoid_sl fp_refs_r;
    dump ("after canon_monoid");
    trefl();
    dump ("after trefl");

    //this is the a ==> b thing when we did cut above
    let cut_hyp = implies_intro () in

    //sort of beta step
    let fp_r = norm_term [] fp_r in  //if we don't do these norms, fast implicits don't kick in because of lambdas
    let frame = norm_term [] frame in
    dump ("frame = " ^ term_to_string frame);
    
    let lem = mk_e_app (`frame_wp_lemma) [tm; fp_r; frame] in

    dump ("before frame lemma, lem = " ^ term_to_string lem);
    apply_lemma lem;
    dump ("after frame lemma - 1");

    //equality goal from frame_wp_lemma
    mapply (binder_to_term cut_hyp);

    //definedness
    smt();
    
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

  dump "Before elim ref values";
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

let join_all_smt_goals () =
  let gs, sgs = goals (), smt_goals () in
  set_smt_goals [];
  set_goals sgs;
  repeat' join;
  let sgs' = goals () in // should be a single one
  set_goals gs;
  set_smt_goals sgs'
  
let sl_auto () : Tac unit =
   dump "STARTING SL_AUTO";
   prelude'();
   //dump "after prelude";
   sl(0);
   dump "Joining";
   //join_all_smt_goals ();
   dump "After joining";
   ()

effect ST (a:Type) (wp:st_wp a) = STATE a (fun post m -> frame_wp wp (frame_post post) m)

// Lift from PURE to STATE, needed since we use $ for some args, which is annoying...
let l (x:'a) : STATE 'a (fun p m -> m == emp /\ p x m) = x


(* A trivial test without mentioning heaps *)
//let test03 (r:ref int) : ST int (fun p m -> exists v. m == r |> v /\ p 3 (r |> v)) by (sl_auto ())
//=
//  let (x, y) = par (fun () -> l 1) (fun () -> l 2) in
//  x + y


(* Actually changing a reference *)
//let test04 (r:ref int) : ST int (fun p m -> exists v. m == r |> v /\ p 3 (r |> v)) by (sl_auto ())
//=
//  let (x, y) = par // #_ #_ #(bind_wp (range_of ()) _ _ (frame_write_wp r 2) (fun _ -> return_wp _ 1)) #_
//	           (fun () -> r := 2; 1) (fun () -> l 2) in
//  x + y

let noaddrs = Set.empty #nat

  //#set-options "--print_full_names"


// let addrs_emp (m m':memory) : Lemma (requires (defined m /\ addrs_in m == Set.empty))
// 				    (ensures (defined (m <*> m') /\ m <*> m' == m'))
// 				    [SMTPat (m <*> m')] // TODO: very likely a bad pattern
//      = admit () // provable from inside SL.Heap

let test05' (r:ref int) (l:lock r) : ST int (fun p m -> m == emp /\ (forall v. p 3 (r |> v))) by (sl_auto ())
			    
  =
  acquire l;
  3
  
let test05 (r:ref int) (l:lock r) : ST int (fun p m -> m == emp /\ p 3 emp) by (sl_auto ())
			    
  =
  acquire l;
  //let v = !r in
  release l

let test06 (r:ref int) : ST int (fun p m -> exists v. m == r |> v /\ p 3 (r |> v)) by (sl_auto ()) =
  let l = mklock (fun p -> True) in
  let _ = par (fun () -> acquire l; release l; 1) (fun () -> acquire l; release l; 2) in
  3









unfold let return_wp (a:Type) (x:a) :st_wp a = 
  fun post m0 -> m0 == emp /\ post x m0

open FStar.Tactics

// `compute` is needed for these two, but they work without the tactic since they are
// explicit about their heaps already. We also use STATE instead of the framed ST.
let test01 () : STATE int (fun p m -> forall r. m == emp /\ p r m) by (compute ())
=
  let (x, y) = par_exp' emp emp (fun () -> l 1) (fun () -> l 2) in
  x + y

let test02 () : STATE int (fun p m -> m == emp /\ p 3 m) by (compute ())
=
  let (x, y) = par_exp' emp emp (fun () -> l 1) (fun () -> l 2) in
  x + y

(* Sanity check that other programs still work.. since we modified the tactic *)
let swap_wp (r1 r2:ref int) = fun p m -> exists x y. m == (r1 |> x <*> r2 |> y) /\ p () (r1 |> y <*> r2 |> x)
let swap (r1 r2:ref int) :ST unit (swap_wp r1 r2) by (sl_auto ())
  = let x = !r1 in
    let y = !r2 in
    r1 := y;
    r2 := x

#set-options "--print_full_names --prn --print_implicits"

(* This is explicit about the frames of the parallel composition, but still requires
 * non-trivial frame reasoning *)
let test03' (r:ref int) : ST int (fun p m -> exists v. m == r |> v /\ p 3 (r |> v)) by (sl_auto ())
=
  let (x, y) = par_exp emp emp (fun () -> l 1) (fun () -> l 2) in
  x + y
