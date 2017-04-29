module FStar.Tactics

assume type binder //FStar.Syntax.Syntax.binder
assume type term
assume type env
assume type fv

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

#reset-options "--no_tactics"

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

noeq
type const =
  | C_Unit : const
  | C_Int : int -> const // Not exposing the details, I presume
  (* TODO: complete *)

noeq
type term_view =
  | Tv_Var    : binder -> term_view
  | Tv_FVar   : fv -> term_view
  | Tv_App    : term -> term -> term_view
  | Tv_Abs    : binder -> term -> term_view
  | Tv_Arrow  : binder -> term -> term_view
  | Tv_Type   : unit -> term_view
  | Tv_Refine : binder -> term -> term_view
  | Tv_Const  : const -> term_view
  (* TODO: complete *)


noeq type __result (a:Type) =
  | Success: a -> state -> __result a
  | Failed: string -> state -> __result a

(* If it starts with an underline don't use it from the outside! *)

let __tac (a:Type) = state -> M (__result a)

(* monadic return *)
val __ret : a:Type -> x:a -> __tac a
let __ret a x = fun (s:state) -> Success x s

(* monadic bind *)
let __bind (a:Type) (b:Type) (t1:__tac a) (t2:a -> __tac b) : __tac b =
    fun p -> let r = t1 p in
             match r with
             | Success a q  -> t2 a q
             | Failed msg q -> Failed msg q

(* Actions *)
let __get () : __tac state = fun s0 -> Success s0 s0 

let tac_wp a = state -> (__result a -> Tot Type0) -> Tot Type0

(*
 * The DMFF-generated `bind_wp` doesn't the contain the "don't duplicate the post-condition"
 * optimization, which causes VCs (for well-formedness of tactics) to blow up.
 *
 * Work around that by overriding `bind_wp` for the effect with an efficient one.
 *)
unfold let g_bind (a:Type) (b:Type) (wp:tac_wp a) (f:a -> tac_wp b) = fun ps post ->
    wp ps (fun m' -> match m' with
                     | Success a q -> f a q post
                     | Failed msg q -> post (Failed msg q))

unfold let g_compact (a:Type) (wp:tac_wp a) : tac_wp a =
    fun ps post -> wp ps (fun _ -> True) /\ (forall (r:__result a). post r \/ wp ps (fun r' -> ~(r == r')))

unfold let __TAC_eff_override_bind_wp (r:range) (a:Type) (b:Type) (wp:tac_wp a) (f:a -> tac_wp b) =
    g_compact b (g_bind a b wp f)

(* total  *) //disable the termination check, although it remains reifiable
reifiable reflectable new_effect {
  TAC : a:Type -> Effect
  with repr     = __tac
     ; bind     = __bind
     ; return   = __ret
     ; __get    = __get
}
effect Tac (a:Type) = TAC a (fun i post -> forall j. post j)
let tactic (a:Type) = unit -> Tac a

(* working around #885 *)
let __fail (a:Type) (msg:string) : __tac a = fun s0 -> Failed #a msg s0
let fail (#a:Type) (msg:string) : tactic a = fun () -> TAC?.reflect (__fail a msg)

let reify_tactic (t:tactic 'a) : __tac 'a =
  fun s -> reify (t ()) s

// TODO: SERIOUS: if I use `reify (t1 ()) p` down here, the combination
// never backtracks. Must be related to the normalization of `reify`, but it's
// weird anyway that going via reify_tactic "fixes" it
let or_else (#a:Type) (t1:tactic a) (t2:tactic a) : tactic a = fun () ->
    TAC?.reflect (fun p -> match reify_tactic t1 p with
                           | Failed _ _ -> reify_tactic t2 p
                           | q -> q)

// TODO: forgot the underscore in result and F* blew up,
// didn't mention a undefined "result". bug?
abstract 
let by_tactic (t:state -> __result unit) (a:Type) : Type = a

// Must run with tactics off, as it will otherwise try to run `by_tactic
// (reify_tactic t)`, which fails as `t` is not a concrete tactic
#reset-options "--no_tactics"
let assert_by_tactic (t:tactic unit) (p:Type)
  : Pure unit 
         (requires (by_tactic (reify_tactic t) p))
         (ensures (fun _ -> p))
  = ()
#reset-options ""

// TODO: naming convention.. underscore before or after?

assume private val __binders_of_env : env -> binders
let binders_of_env (e:env) : tactic binders = fun () -> __binders_of_env e

assume private val __type_of_binder: binder -> term 
let type_of_binder (b:binder) : tactic term = fun () -> __type_of_binder b

assume private val __term_eq : term -> term -> bool
let term_eq t1 t2 : tactic bool = fun () ->  __term_eq t1 t2

assume private val __embed  : #a:Type -> a -> term
let quote #a (x:a) : tactic term = fun () -> __embed x

//This primitive provides a way to destruct a term as a formula
//TODO: We should add a formula_as_term also
assume private val __term_as_formula : term -> option formula
let term_as_formula t : tactic (option formula) = fun () -> __term_as_formula t

assume val __inspect : term -> option term_view
let inspect t : tactic term_view = fun () -> match __inspect t with
                                             | Some x -> x
                                             | None -> fail "inspect failed, possibly unknown syntax" ()

(* Many of these could be derived from apply_lemma, 
   rather than being assumed as primitives. 
   E.g., forall_intros could be an application of 
         FStar.Classical.forall_intro
 *)         
assume private val __forall_intros: __tac binders
let forall_intros : tactic binders = fun () -> TAC?.reflect __forall_intros

assume private val __implies_intro: __tac binder
let implies_intro : tactic binder = fun () -> TAC?.reflect __implies_intro

assume private val __trivial  : __tac unit
let trivial : tactic unit = fun () -> TAC?.reflect __trivial

assume private val __revert  : __tac unit
let revert : tactic unit = fun () -> TAC?.reflect __revert

assume private val __clear   : __tac unit
let clear : tactic unit = fun () -> TAC?.reflect __clear

assume private val __split   : __tac unit
let split : tactic unit = fun () -> TAC?.reflect __split

assume private val __merge   : __tac unit
let merge : tactic unit = fun () -> TAC?.reflect __merge

// TODO: isn't this is unsound if b is not the environment? I think so but couldn't quickly come up with a contradiction
assume private val __rewrite : binder -> __tac unit
let rewrite (b:binder) : tactic unit = fun () -> TAC?.reflect (__rewrite b)

assume private val __smt     : __tac unit
let smt : tactic unit = fun () -> TAC?.reflect __smt

assume private val __visit   : __tac unit -> __tac unit
let visit (f:tactic unit) : tactic unit = fun () -> TAC?.reflect (__visit (reify_tactic f))

assume private val __focus: __tac unit -> __tac unit
let focus (f:tactic unit) : tactic unit = fun () -> TAC?.reflect (__focus (reify_tactic f))

(* could be implemented using __focus *)
assume private val __seq : __tac unit -> __tac unit -> __tac unit
let seq (f:tactic unit) (g:tactic unit) : tactic unit = fun () -> 
  TAC?.reflect (__seq (reify_tactic f) (reify_tactic g))

assume private val __exact : term -> __tac unit
let exact (t:tactic term) : tactic unit = fun () -> let tt = t () in TAC?.reflect (__exact tt)

assume private val __apply_lemma : term -> __tac unit
let apply_lemma (t:tactic term) : tactic unit = fun () -> let tt = t () in TAC?.reflect (__apply_lemma tt)

assume val __print : string -> __tac unit
let print (msg:string) : tactic unit = fun () -> TAC?.reflect (__print msg)

assume val __grewrite : term -> term -> __tac unit
let grewrite (e1:tactic term) (e2:tactic term) : tactic unit =
    fun () -> let t1 = e1 () in
              let t2 = e2 () in
              TAC?.reflect (__grewrite t1 t2)

let tret (#a:Type) (x:a) : tactic a =
    fun () -> x

let tbind (#a:Type) (#b:Type) (t : tactic a) (f : a -> tactic b) : tactic b =
    fun () -> let r = t () in f r ()

let tbind' (#a:Type) (#b:Type) (t : tactic a) (f : tactic b) : tactic b =
    fun () -> let r = t () in f ()

// For some reason, a direct definition fails.
let revert_all (bs:binders) : tactic unit =
    let rec __revert_all (bs:binders) : Tac unit =
      match bs with
      | [] -> ()
      | _::tl -> let _ = revert () in __revert_all tl
    in fun () -> __revert_all bs

let get : tactic state = fun () -> TAC?.__get ()

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

// TODO: aux isn't used. wtf?
// in this one, if the return type is "tactic unit", it complains
// about not being able to show a decreasing order. again wtf?
let rec user_visit (callback:tactic unit) : unit -> Tac unit
    = fun () ->
         or_else callback (user_visit callback) ()

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
      user_visit simplify_eq_implication ()

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
