module SL.AutoTactic

open FStar.Algebra.CommMonoid
open FStar.Tactics
module T = FStar.Tactics

open FStar.Tactics.PatternMatching
open CanonCommMonoid
open FStar.Reflection
open FStar.List

open SL.Base

(* cf. #1323, #1465 *)
module SLHeap = SL.Heap

// --using_facts_from '* -FStar.Tactics -FStar.Reflection'

let ddump m = if T.debugging () then T.dump m


let memory_cm : cm memory =
  CM emp (<*>) (fun x -> lemma_sep_unit' x) (fun x y z -> ()) (fun x y -> ())

// Fails when called
// (Error) user tactic failed: norm_term: Cannot type fun _ -> idtac () <: FStar.Tactics.Effect.TAC unit in context ((r1:SepLogic.Heap.ref Prims.int), (r2:SepLogic.Heap.ref Prims.int), (x:Prims.int), (y:Prims.int), (x:SL.Effect.post Prims.int), (x:SepLogic.Heap.memory), (uu___326511:SepLogic.Heap.defined (r1 |> x <*> r2 |> y) /\ x y (r1 |> 2 <*> r2 |> y))). Error = (Variable "a#327038" not found)
let solve_frame_wp_fails (_:unit) : Tac unit =
  gpm #unit (fun (a:Type) (wp:st_wp a) (post:post a) (m:memory)
            (_ : pm_goal(squash (frame_wp wp post m))) -> idtac()) ()

let fv_is (fv:fv) (name:string) = implode_qn (inspect_fv fv) = name

let rec explode_list (t:term) : Tac (list term) =
    let hd, args = collect_app t in
    match inspect hd with
    | Tv_FVar fv ->
        if fv_is fv (`%Cons)
        then match args with
             | [(_t, Q_Implicit); (hd, Q_Explicit); (tl, Q_Explicit)] -> hd :: explode_list tl
             | _ -> fail "bad Cons"
        else if fv_is fv (`%Nil)
        then []
        else fail "not a list"
    | _ ->
        fail "not a list (not an fv)"

let from_sref (t:term) : Tac term =
    let hd, args = collect_app t in
    match inspect hd, args with
    | Tv_FVar _, [(_t, Q_Implicit); (r, Q_Explicit)] -> r
    | _ -> fail ("from_sref: " ^ term_to_string t)

let rec footprint_of (t:term) : Tac (list term) =
  let hd, tl = collect_app t in
  match inspect hd, tl with
  // | Tv_FVar fv, [(ta, Q_Implicit); (tr, Q_Explicit); (tv, Q_Explicit)] ->
  //   if fv_is fv (`%write_wp) then [tr]
  //   else fail "not a write_wp"
  // | Tv_FVar fv, [(ta, Q_Implicit); (tr, Q_Explicit)] ->
  //   if fv_is fv (`%read_wp) then [tr]
  //   else fail "not a read_wp"
  // -- generalizing the above to arbitrary "footprint expressions"
  | Tv_Abs b t, [] -> footprint_of t
  | Tv_FVar fv, args ->
      if fv_is fv (`%with_fp)
      then match args with
           | (_t, Q_Implicit)::(fp, Q_Explicit)::_ ->
               let fp = explode_list fp in
               Tactics.Util.map from_sref fp
           | _ -> fail ("unexpected arity for with_fp: " ^ term_to_string t)
      else if fv_is fv (`%frame_wp)
      then match args with
           | (_ta, Q_Implicit)::(wpa, Q_Explicit)::_ ->
                footprint_of wpa
           | _ -> fail ("unexpected arity for frame_wp: " ^ term_to_string t)
      else if fv_is fv (`%par_wp')
      then match args with
           | (_ta, Q_Implicit)::(_tb, Q_Implicit)::(wpa, Q_Explicit)::(wpb, Q_Explicit)::_ ->
                footprint_of wpa @ footprint_of wpb
           | _ -> fail ("unexpected arity for par_wp': " ^ term_to_string t)
      else fail ("do not know how to get footprint of: " ^ term_to_string t)
  | _ -> fail ("not an applied free variable: " ^ term_to_string t)

let pack_fv' (n:name) : Tac term = pack (Tv_FVar (pack_fv n))
let eexists (a:Type) (t:unit -> Tac a) : Tac a =
  apply_lemma (`FStar.Classical.exists_intro); later(); norm[];
  fst (divide (ngoals()-1) t dismiss)

let frame_wp_lemma (#a:Type) (#wp:st_wp a) (#f_post:post a) (m m0 m1:memory)
    (_ : (squash ((m0 <*> m1) == m)))
    (_ : (squash (defined (m0 <*> m1))))
    (_ : (squash (m == (m0 <*> m1) ==> defined (m0 <*> m1) ==> wp (frame_post f_post m1) m0))) :
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

type bdata = int * term

let pointsto_to_bdata (fp_refs:list term) (t:term) : Tac bdata =
  let hd, tl = collect_app t in
  match inspect hd, tl with
  | Tv_FVar fv, [(ta, Q_Implicit); (tr, Q_Explicit); (tv, Q_Explicit)] ->
    if fv_is fv (`%(op_Bar_Greater)) then
       if tr `term_mem` fp_refs
       then (0, tr)
       else (1, tr)
    else (2, t)
  | _, _ -> (2, t) // have to accept at least Tv_Uvar _ here

let pointsto_to_bdata' t = pointsto_to_bdata [] t

let compare_b (n1, t1) (n2, t2) : int =
  (* lex order *)
  if n2 - n1 <> 0
  then n2 - n1
  else FStar.Order.int_of_order (compare_term t1 t2)

let compare_v #a (vm : vmap a bdata) (v1 v2 : var) =
    compare_b (select_extra v1 vm) (select_extra v2 vm)

let sort_sl (a:Type) (vm:vmap a bdata) (xs:list var) : Tot (list var) =
  List.Tot.sortWith #var (compare_v vm) xs

let sort_sl_correct : permute_correct sort_sl =
  fun #a m vm xs -> sortWith_correct (compare_v vm) #a m vm xs

let canon_monoid_sl (fp:list term) : Tac unit =
  canon_monoid_with bdata (pointsto_to_bdata fp) (0, `())
                          sort_sl (fun #a -> sort_sl_correct #a) memory_cm

let canon_monoid_sl' () : Tac unit =
  canon_monoid_with bdata pointsto_to_bdata' (0, `())
                          sort_sl (fun #a -> sort_sl_correct #a) memory_cm

let binder_to_term (b : binder) : Tac term =
  let bv, _ = inspect_binder b in pack (Tv_Var bv)

noeq
type cmd =
  | Frame     : ta:term -> twp:term -> tpost:term -> tm:term -> cmd
  | Read      : cmd
  | Write     : cmd
  | Bind      : cmd
  | Ite       : cmd
  | IfThenElse: cmd
  | Close     : cmd
  | WithFP    : cmd
  | ParWP     : twpa:term -> twpb:term -> th0:term -> cmd
  | Assume    : cmd
  | Squash    : cmd
  | Implies   : cmd
  | Forall    : cmd
  | Exists    : cmd
  | And       : cmd
  | Eq        : cmd
  | FramePost : cmd
  | Acquire   : cmd
  | Release   : cmd
  | Unknown   : option fv -> cmd
  | BySMT     : cmd
  | MemEq     : cmd

let peek_in (t:term) : Tac cmd =
    let hd, tl = collect_app t in
    match inspect hd with
    | Tv_FVar fv  ->
     if fv_is fv (`%frame_wp)
     then match tl with
          | [(ta,      Q_Implicit);
             (twp,     Q_Explicit);
             (tpost,   Q_Explicit);
             (tm,      Q_Explicit)] -> Frame ta twp tpost tm
          | _ -> fail "Unexpected arity of frame"
     else if fv_is fv (`%par_wp')
     then match tl with
          | [(ta,      Q_Implicit);
             (tb,      Q_Implicit);
             (twpa,    Q_Explicit);
             (twpb,    Q_Explicit);
             (tpost,   Q_Explicit);
             (th0,     Q_Explicit)] -> ParWP twpa twpb th0
          | _ -> fail "Unexpected arity of parwp'"
     else if fv_is fv (`%read_wp)               then Read
     else if fv_is fv (`%write_wp)              then Write
     else if fv_is fv (`%with_fp)               then WithFP
     else if fv_is fv (`%bind_wp)               then Bind
     else if fv_is fv (`%st_ite_wp)             then Ite
     else if fv_is fv (`%st_if_then_else)       then IfThenElse
     else if fv_is fv (`%st_close_wp)           then Close
     else if fv_is fv (`%st_assume_p)           then Assume
     else if fv_is fv (`%squash)                then Squash
     else if fv_is fv (`%l_imp)                 then Implies
     else if fv_is fv (`%l_Forall)              then Forall
     else if fv_is fv (`%l_Exists)              then Exists
     else if fv_is fv (`%l_and)                 then And
     else if fv_is fv (`%eq2)                   then Eq
     else if fv_is fv (`%frame_post)            then FramePost
     else if fv_is fv (`%by_smt)                then BySMT
     else if fv_is fv (`%mem_eq)                then MemEq
     else if fv_is fv (`%l_False)               then Unknown None //AR: TODO: this is quite hacky, we need a better way then Unknown None
     else Unknown (Some fv)
    | _ -> Unknown None
 
let peek_cmd () : Tac cmd =
  let g = cur_goal () in
  let hd, tl = collect_app g in
  match inspect hd, tl with
  | Tv_FVar fv, [(t1, Q_Explicit)] ->
    if fv_is fv (`%squash) then peek_in t1
    else fail "Unrecognized command: not a squash"
 | _ -> fail "Unrecognized command: not an fv app"

private let __lem_eq_sides t (a b c d : t) (_ : squash (a == c)) (_ : squash (b == d)) :
                         Lemma ((a == b) == (c == d)) = ()

private let __and_elim #p #q #r (_ : (p /\ q)) (_ : squash (p ==> (q ==> r))) : Lemma r = ()

let destruct_and (b:binder) : Tac (binder * binder) =
  apply_lemma (`(__and_elim (`#(binder_to_term b))));
  if ngoals () <> 1 then fail "no";
  clear b;
  let b1 = implies_intro () in
  let b2 = implies_intro () in
  (b1, b2)

let canon_binder_mem_eq (b:binder) : Tac unit =
    ddump "canon_binder_mem_eq before";
    norm_binder_type [delta_only [`%mem_eq]] b;
    binder_retype b;
    focus (fun () ->
        apply_lemma (`__lem_eq_sides);
        guard (List.length (goals()) = 2);
        canon_monoid_sl' (); trefl ();
        canon_monoid_sl' (); trefl ();
    ()
    );
    ddump "canon_binder_mem_eq after";
    ()

let rec proc_intro (b:binder) : Tac binders =
  ddump ("proc_intro of " ^ binder_to_string b);
  let t = norm_term [weak;hnf;delta] (type_of_binder b) in
  ddump ("proc_intro, t = " ^ term_to_string t);
  match peek_in t with
  | Exists ->
    let (_, b) = sk_binder b in
    proc_intro b

  | And ->
    let (b1, b2) = destruct_and b in
    proc_intro b1 @ proc_intro b2

  | MemEq ->
    canon_binder_mem_eq b;
    [b]

  | _ -> [b]

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

let __elim_fp fp phi (_ : squash phi) : Lemma (with_fp fp phi) = ()
let elim_fp () : Tac unit = apply_lemma (`__elim_fp)

//in procedure calls, the callee wp might involve some exists x y. sort of stuff, if so solve them by trefl
//initial call set use_trefl to false
//return t_refl if we did some something, so that the caller can make progress on rest of the VC
let rec solve_procedure_ref_value_existentials (use_trefl:bool) :Tac bool =
  let g = cur_goal () in
  ddump "solve_procedure_ref_value_existentials";
  match term_as_formula g with
  | Reflection.Formula.Exists x t ->
    let w = uvar_env (cur_env ()) (Some (inspect_bv x).bv_sort) in
    witness w;
    solve_procedure_ref_value_existentials true
  | _ ->
   if use_trefl then begin
     //let _ = T.repeat T.split in
     //trefl ();
     true
   end
   else false

let ref_terms_to_heap_term (refs : list term) : Tac term =
    T.fold_left
      (fun a t ->
        let u = fresh_uvar (Some (`int)) in // TODO: int is hardcoded
        let t = (`(`#t |> `#u)) in
        if term_eq a (`emp)
        then t
        else (`(`#a <*> `#t))) (`emp) refs

private
let __unif_helper h1 h2 : Lemma (requires (h1 == h2))
                                (ensures (h1 <*> emp == h2)) = ()

(* refs is a list of the references in `small`, used for commuting the heaps appropriately for unification *)
(* returns: the frame and a proof of equality of the heaps, which is a new binder introduced *)
let find_frame (refs : list term) (small : term) (big : term) : Tac (term * binder) =
    // Introduce a uvar for frame
    let env = cur_env () in
    let frame = uvar_env env (Some (`SLHeap.memory)) in

    // Make the term equating the small footprint + frame with the current memory
    let eq = `((`#small <*> `#frame) == `#big) in

    //cut
    apply_lemma (mk_e_app (`__tcut) [eq]);

    //flip so that the current goal is the equality of memory expressions
    flip ();
    
    ddump ("before canon_monoid");
    canon_monoid_sl refs;
    ddump ("after canon_monoid");
    begin match trytac trefl with
    | Some _ -> ()
    | None ->
        (* trefl didn't succeed, this can happen in the frame is empty
         * since (r |> ?u1 <*> ?u2) does not unify with (r |> ?u1);
         * so, try to set an empty frame and try again. *)
        let b = unify frame (`emp) in
        if b
        then (apply_lemma (`__unif_helper); trefl ())
        else fail "impossible? setting the frame uvar to emp failed"
    end;
    ddump ("after trefl");

    //this is the a ==> b thing when we did cut above
    let heap_eq = implies_intro () in
    (frame, heap_eq)

let rec sl (i:int) : Tac unit =
  ddump ("SL :" ^ string_of_int i);

  unfold_def (`(<|));

  //post procedure call, we sometimes have a m == m kind of expression in the wp
  //this will solve it in the tactic itself rather than farming it out to smt
  //norm [simplify];
  // GM: Hard to predict behaviour if so
  
  let c = peek_cmd () in
  ddump ("c = " ^ term_to_string (quote c));
  match c with
  | Exists
  | Unknown None ->
    //either we are done
    //or we are stuck at some existential in procedure calls
    let cont = solve_procedure_ref_value_existentials false in
    if cont then sl (i + 1)
    else (tlabel "Unknown None,"; smt ())

  | Unknown (Some fv) ->
    //so here we are unfolding something like swap_wp below

    // eventually this will use attributes,
    // but we can't currently get at them
    trivial `or_else` (fun () ->
    unfold_first_occurrence (fv_to_string fv);
    tlabel ("Unknown (Some " ^ fv_to_string fv ^ "),");
    norm [];
    sl (i + 1))

  | BySMT ->
    tlabel "explicit by_smt,";
    smt ()

  | MemEq ->
    tlabel "mem_eq";
    unfold_first_occurrence (`%mem_eq);
    norm [delta_only [`%dfst; `%dsnd]];
    canon_monoid_sl' ();
    trefl ();
    ()

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
      ignore (proc_intro (implies_intro ()));
      sl (i + 1)
    in

    ignore (divide 1 f f)

  | Close ->
    apply_lemma (`close_wp_lemma);
    ignore (Tactics.Util.map proc_intro (forall_intros ()));
    sl (i + 1)

  | Assume ->
    apply_lemma (`assume_p_lemma);
    ignore (proc_intro (implies_intro ()));
    sl (i + 1)

  | Read ->
    unfold_first_occurrence (`%read_wp);
    norm[];
    eexists unit (fun () -> T.split(); trefl());
    sl (i + 1)

  | Write ->
    unfold_first_occurrence (`%write_wp);
    norm[];
    eexists unit (fun () -> T.split(); trefl());
    sl (i + 1)

  | Squash ->
    squash_intro ();
    sl (i + 1)

  | Implies ->
    ignore (proc_intro (implies_intro ()));
    sl (i + 1)

  | Forall ->
    ignore (proc_intro (forall_intro ()));
    sl (i + 1)

  | And ->
    T.split ();
    let k s () =
      tlabel s;
      sl (i + 1)
    in
    iseq [k "left,"; k "right,"]

  | Eq ->
    trefl `or_else` smt

  | WithFP ->
    unfold_first_occurrence (`%with_fp);
    norm[];
    sl (i + 1)
    
  | FramePost ->
    unfold_first_occurrence (`%frame_post);
    norm[];
    ignore (implies_intro ()); //definedness
    sl (i + 1)

  | Frame ta twp tpost tm ->
    //we are at frame_wp, real work starts

    //compute the footprint from the arg (e.g. read_wp r1, swap_wp r1 r2, etc.)
    let fp_refs = footprint_of twp in
    ddump ("fp_refs="^ FStar.String.concat "," (List.Tot.map term_to_string fp_refs));

    //build the footprint memory expression, uvars for ref values, and join then
    let fp = ref_terms_to_heap_term fp_refs in
    ddump ("m0=" ^ term_to_string fp);

    let (frame, heap_eq) = find_frame fp_refs fp tm in

    //sort of beta step
    let fp = norm_term [] fp in  //if we don't do these norms, fast implicits don't kick in because of lambdas
    let frame = norm_term [] frame in
    apply_lemma (mk_e_app (`frame_wp_lemma) [tm; fp; frame]);
    ddump ("after frame lemma - 1");

    //equality goal from frame_wp_lemma
    mapply (binder_to_term heap_eq);

    canon_binder_mem_eq heap_eq;
    
    smt(); //definedness
    ddump ("after frame lemma - 2");
    sl(i + 1)

  | ParWP wpa wpb th0 ->
    (* Another interesting case. We find the footprints for each process
     * and split the input heap accordingly. All of the extra parts of the heap,
     * unneded by both processes, go arbitrarilly to the left one. *)
    let fp_a = footprint_of wpa in
    let fp_b = footprint_of wpb in
    let fp = fp_a @ fp_b in

    let h_a = ref_terms_to_heap_term fp_a in
    let h_b = ref_terms_to_heap_term fp_b in
    let h = ref_terms_to_heap_term fp in

    let (frame, eq_hyp) = find_frame fp h th0 in


    witness (`(`#h_a <*> `#frame));
    witness h_b;

    apply_lemma (`(par_wp'_lemma));

    canon_monoid_sl fp;
    trefl ();

    sl (i + 1)

  | _ -> fail "impossible.. coverage"

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
  ddump "start";
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
  let h = Tactics.Logic.implies_intro () in
  __elim_exists h;
  let m0 = forall_intro_as "m0" in
  let h = Tactics.Logic.implies_intro () in
  __elim_exists h;
  let m1 = forall_intro_as "m1" in

  //the goal might start with exists x y. to quantify over the ref values

  //now the goal looks something like (defined m0 * m1 /\ (m == m0 * m1 /\ (...)))
  //do couple of implies_intro and and_elim to get these conjections
  let h = implies_intro () in and_elim (binder_to_term h); clear h;
  let h = implies_intro() in and_elim (binder_to_term h); clear h;

  unfold_first_occurrence (`%with_fp);
  
  //defined m0 * m1
  ignore (implies_intro ());

  //this is the m = ..., introduced by the frame_wp
  let m0 = implies_intro () in
  ddump "before rewrite";
  rewrite m0; //clear m0;
  ddump "after rewrite";

  ddump "Before elim ref values";
  ignore (repeat (fun () -> let h = implies_intro () in
                           __elim_exists h;
               ignore (forall_intro ())));
  ddump "After elim ref values";
  
  //now we are at the small footprint style wp
  //we should full norm it, so that we can get our hands on the m0 == ..., i.e. the footprint of the command
  let user_annot = implies_intro() in
  norm_binder_type [primops; iota; delta; zeta] user_annot;
  and_elim (binder_to_term user_annot);
  clear user_annot;

  //the first conjunct there is the m0 = ..., so inline it
  let h = implies_intro () in rewrite h; //clear h;

  //push rest of the lhs implicatio in the context
  ignore (implies_intro ())

let sl_auto () : Tac unit =
   prelude' ();
   ddump "after prelude";
   sl 0;
   ddump "after sl";
   ()
