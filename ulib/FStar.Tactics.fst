// This should be moved to the standard libary, e.g., FStar/ulib
module FStar.Tactics
assume type binder //FStar.Syntax.Syntax.binder
assume type term
assume type env
type typ     = term
type binders = list binder
type goal    = env * term
type goals   = list goal
type state   = goals  //active goals 
             * goals  //goals that have to be dispatched to SMT: maybe change this part of the state to be opaque to a user program

(* This is meant to be all named representation
     -- while providing some conveniences for 
        handling the logical structure of a term 
   NB: rename this to term_view? or something like that
*)
noeq type formula = 
  //the logical skeleton of a term
  | True_  : formula
  | False_ : formula  
  | Eq     : typ -> term -> term -> formula
  | And    : term -> term -> formula  //Prims.l_and
  | Or     : term -> term -> formula
  | Not    : term -> formula
  | Implies: term -> term -> formula
  | Iff    : term -> term -> formula  
  | Forall : binders -> term -> formula
  | Exists : binders -> term -> formula
  | App    : term -> term -> formula
  | Name   : binder -> formula
   (* TODO more cases *) 
  | IntLit : int -> formula
  //Abs   : binders -> term -> formula //Named repr
  //Match : ....

noeq type _result (a:Type) =
  | Success: a -> state -> _result a
  | Failed: string -> state -> _result a

(* If it starts with an underline don't use it from the outside! *)

let _tac (a:Type) = state -> M (_result a)

(* monadic return *)
val _ret : a:Type -> x:a -> _tac a
let _ret a x = fun (s:state) -> Success x s

(* monadic bind *)
let _bind (a:Type) (b:Type) 
         (t1:_tac a)
         (t2:a -> _tac b)
    : _tac b
    = fun p ->
        let r = t1 p in
        match r with
        | Success a q  -> t2 a q
        | Failed msg q -> Failed msg q

(* Actions *)
let _get () : _tac state = fun s0 -> Success s0 s0 

let tac_wp a = state -> (_result a -> Tot Type0) -> Tot Type0

unfold let g_bind (r:range) (a:Type) (b:Type) (wp:tac_wp a) (f:a -> tac_wp b) = fun ps post ->
    wp ps (fun m' -> match m' with
                     | Success a q -> f a q post
                     | Failed msg q -> post (Failed msg q))

unfold let g_compact (a:Type) (wp:tac_wp a) : tac_wp a =
    fun ps post -> wp ps (fun _ -> True) /\ (forall (r:_result a). post r \/ wp ps (fun r' -> ~(r == r')))

unfold let __TAC_eff_override_bind_wp (r:range) (a:Type) (b:Type) (wp:tac_wp a) (f:a -> tac_wp b) =
    g_compact b (g_bind r a b wp f)

(* total  *) //disable the termination check, although it remains reifiable
reifiable reflectable new_effect {
  TAC : a:Type -> Effect
  with repr     = _tac
     ; bind     = _bind
     ; return   = _ret
     ; _get     = _get
}
effect Tac (a:Type) = TAC a (fun i post -> forall j. post j)
let tactic (a:Type) = unit -> Tac a

(* working around #885 *)
let _fail (a:Type) (msg:string) : _tac a = fun s0 -> Failed #a msg s0
let fail (#a:Type) (msg:string) : tactic a = fun () -> TAC?.reflect (_fail a msg)

let or_else (#a:Type) (t1:tactic a) (t2:tactic a)
        : tactic a
        = fun () ->
          TAC?.reflect (fun p -> 
            match reify (t1 ()) p with
            | Failed _ _ -> reify (t2 ()) p
            | q -> q)

// TODO: forgot the underscore in result and F* blew up,
// didn't mention a undefined "result". bug?
abstract 
let by_tactic (t:state -> _result unit) (a:Type) : Type = a

// TODO: generalize to any type
let reify_tactic (t:tactic unit) : _tac unit =
  fun s -> reify (t ()) s

let assert_by_tactic (t:tactic unit) (p:Type)
  : Pure unit 
         (requires (by_tactic (reify_tactic t) p))
         (ensures (fun _ -> p))
  = ()

  // TODO: naming convention.. underscore before or after?

assume private val binders_of_env_ : env -> binders
let binders_of_env (e:env) : tactic binders = fun () -> binders_of_env_ e

assume private val type_of_binder_: binder -> term 
let type_of_binder (b:binder) : tactic term = fun () -> type_of_binder_ b

assume private val term_eq_ : term -> term -> bool
let term_eq t1 t2 : tactic bool = fun () ->  term_eq_ t1 t2

assume private val embed  : #a:Type -> a -> term
let quote #a (x:a) : tactic term = fun () -> embed x

//This primitive provides a way to destruct a term as a formula
//TODO: We should add a formula_as_term also
assume private val term_as_formula_ : term -> option formula
let term_as_formula t : tactic (option formula) = fun () -> term_as_formula_ t

(* Many of these could be derived from apply_lemma, 
   rather than being assumed as primitives. 
   E.g., forall_intros could be an application of 
         FStar.Classical.forall_intro
 *)         
assume private val forall_intros_: _tac binders
let forall_intros : tactic binders = fun () -> TAC?.reflect forall_intros_

assume private val implies_intro_: _tac binder
let implies_intro : tactic binder = fun () -> TAC?.reflect implies_intro_

assume private val trivial_  : _tac unit
let trivial : tactic unit = fun () -> TAC?.reflect trivial_

assume private val revert_  : _tac unit
let revert : tactic unit = fun () -> TAC?.reflect revert_

assume private val clear_   : _tac unit
let clear : tactic unit = fun () -> TAC?.reflect clear_

assume private val split_   : _tac unit
let split : tactic unit = fun () -> TAC?.reflect split_

assume private val merge_   : _tac unit
let merge : tactic unit = fun () -> TAC?.reflect merge_

assume private val rewrite_ : binder -> _tac unit
let rewrite (b:binder) : tactic unit = fun () -> TAC?.reflect (rewrite_ b)

assume private val smt_     : _tac unit
let smt : tactic unit = fun () -> TAC?.reflect smt_

assume private val visit_   : _tac unit -> _tac unit
let visit (f:tactic unit) : tactic unit = fun () -> TAC?.reflect (visit_ (reify_tactic f))

assume private val focus_: _tac unit -> _tac unit
let focus (f:tactic unit) : tactic unit = fun () -> TAC?.reflect (focus_ (reify_tactic f))

(* could be implemented using focus_ *)
assume private val seq_ : _tac unit -> _tac unit -> _tac unit
let seq (f:tactic unit) (g:tactic unit) : tactic unit = fun () -> 
  TAC?.reflect (seq_ (reify_tactic f) (reify_tactic g))

assume private val exact_ : term -> _tac unit
let exact (t:tactic term) : tactic unit = fun () -> let tt = t () in TAC?.reflect (exact_ tt)

assume private val apply_lemma_ : term -> _tac unit
let apply_lemma (t:tactic term) : tactic unit = fun () -> let tt = t () in TAC?.reflect (apply_lemma_ tt)

assume val print_ : string -> _tac unit
let print (msg:string) : tactic unit = fun () -> TAC?.reflect (print_ msg)

assume val grewrite_ : term -> term -> _tac unit
let grewrite (e1:tactic term) (e2:tactic term) : tactic unit =
    fun () -> let t1 = e1 () in
              let t2 = e2 () in
              TAC?.reflect (grewrite_ t1 t2)

let tret (#a:Type) (x:a) : tactic a =
    fun () -> x

let tbind (#a:Type) (#b:Type) (t : tactic a) (f : a -> tactic b) : tactic b =
    fun () -> let r = t () in f r ()

let tbind' (#a:Type) (#b:Type) (t : tactic a) (f : tactic b) : tactic b =
    fun () -> let r = t () in f ()

// For some reason, a direct definition fails.
let revert_all (bs:binders) : tactic unit =
    let rec _revert_all (bs:binders) : Tac unit =
      match bs with
      | [] -> ()
      | _::tl -> let _ = revert () in _revert_all tl
    in fun () -> _revert_all bs

let get : tactic state = fun () -> TAC?._get ()

let cur_goal : tactic goal = fun () ->
  let goals, _ = get () in
  match goals with
  | [] -> fail "No more goals" ()
  | hd::_ -> hd

let destruct_equality_implication (t:term) : tactic (option (formula * term)) = fun () ->
  match term_as_formula t () with
  | Some (Implies lhs rhs) ->
    let lhs = term_as_formula lhs () in
    (match lhs with
     | Some (Eq _ _ _) -> Some (Some?.v lhs, rhs)
     | _ -> None)
  | _ -> None

// TODO: Needs to be unit -> Tac unit since it's a let rec.
let rec simplify_eq_implication : unit -> Tac unit
  = fun () ->
    let context, goal_t = cur_goal () in  // G |- x=e ==> P
    match destruct_equality_implication goal_t () with
    | None -> fail "Not an equality implication" ()
    | Some (_, rhs) ->
      let eq_h = implies_intro () in  // G, eq_h:x=e |- P
      rewrite eq_h (); // G, eq_h:x=e |- P[e/x]
      clear ();     // G |- P[e/x]
      visit simplify_eq_implication ()

// TODO: aux isn't used. wtf?
// in this one, if the return type is "tactic unit", it complains
// about not being able to show a decreasing order. again wtf?
let rec user_visit (callback:tactic unit) : unit -> Tac unit
    = fun () ->
         let aux : tactic unit = fun () ->
           let context, goal_t = cur_goal () in
           match term_as_formula goal_t () with
           | None -> smt ()
           | Some (Exists _ _) -> //not yet handled
             ()

           | Some (Forall xs body) ->
             let binders = forall_intros () in
             let _ = user_visit callback () in
             revert_all binders ()

           | Some (And t1 t2) ->
             let _ = seq split (user_visit callback) () in
             merge ()

           | Some (Implies t1 t2) ->
             let h = implies_intro () in
             let _ = user_visit callback () in
             revert ()

           | _ ->
             or_else trivial smt ()
         in
         or_else callback (user_visit callback) ()

let rec try_rewrite_equality (x:term)
                             (bs:binders)
  : tactic unit
  = fun () ->
    match bs with
    | [] -> ()
    | x_t::bs -> begin
      match term_as_formula (type_of_binder x_t ()) () with
      | Some (Eq _ y _) ->
        if term_eq x y ()
        then rewrite x_t ()
        else try_rewrite_equality x bs ()
      | _ -> try_rewrite_equality x bs ()
      end

let rec rewrite_all_context_equalities (bs:binders)
  : tactic unit
  = fun () ->
    match bs with
    | [] -> ()
    | x_t::bs -> begin
      match term_as_formula (type_of_binder x_t ()) () with
      | Some (Eq _ _ _) ->
        rewrite x_t ();
        rewrite_all_context_equalities bs ()
      | _ ->
        rewrite_all_context_equalities bs ()
      end

// TODO: has to be arrow
let rec rewrite_eqs_from_context : unit -> Tac unit
  = fun () ->
       let context, _ = cur_goal () in
       rewrite_all_context_equalities (binders_of_env context ()) ()

let rewrite_equality (x:tactic term) : tactic unit
  = fun () ->
     let context, _ = cur_goal () in
     try_rewrite_equality (x ()) (binders_of_env context ()) ()

let solved : tactic unit = fun () ->
  let _, goal = cur_goal () in
  match term_as_formula goal () with
  | Some True_ -> ()
  | _ -> fail "Not solved" ()

let rec just_do_intros : unit -> Tac unit =
    focus (fun () ->
       let _ = forall_intros () in
       let _ = implies_intro () in
       smt ();
       revert ();
       revert ())

// TODO: again has to be an arrow
let rec rewrite_all_equalities : unit -> Tac unit = fun () ->
  visit simplify_eq_implication ()


assume val lemma_mul_comm : x:nat -> y:nat -> Lemma (op_Multiply x y == op_Multiply y x)
let mul_commute_ascription : tactic unit
  = fun () ->
    let _, goal_t = cur_goal () in  // G |- x=e ==> P
    match term_as_formula goal_t () with
    | Some (Eq _ _ _) ->
      apply_lemma (quote lemma_mul_comm) ()
    | _ -> fail "Not an equality" ()

// TODO: unfold tactic or complains about termination
let rec unfold_definition_and_simplify_eq' (tm:term)
  : unit -> Tac unit
  = fun () ->
      let _, goal_t = cur_goal () in  // G |- x=e ==> P
      match term_as_formula goal_t () with
      | Some (App hd arg) ->
        if term_eq hd tm () then trivial ()
      | _ -> begin
        match destruct_equality_implication goal_t () with
        | None -> fail "Not an equality implication" ()
        | Some (_, rhs) ->
          let eq_h = implies_intro () in  // G, eq_h:x=e |- P
          rewrite eq_h (); // G, eq_h:x=e |- P[e/x]
          clear ();     // G |- P[e/x]
          visit (unfold_definition_and_simplify_eq' tm) ()
       end

let unfold_definition_and_simplify_eq (tm:tactic term) 
  : tactic unit 
  = fun () -> unfold_definition_and_simplify_eq' (tm ()) ()
