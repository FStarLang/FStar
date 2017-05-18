module FStar.Tactics

open FStar.Order
include FStar.Reflection

type goal    = env * term
type goals   = list goal
type state   = goals  //active goals
             * goals  //goals that have to be dispatched to SMT: maybe change this part of the state to be opaque to a user program

noeq type __result (a:Type) =
  | Success: a -> state -> __result a
  | Failed: string -> state -> __result a

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

let __tac_wp a = state -> (__result a -> Tot Type0) -> Tot Type0

(*
 * The DMFF-generated `bind_wp` doesn't the contain the "don't duplicate the post-condition"
 * optimization, which causes VCs (for well-formedness of tactics) to blow up.
 *
 * Work around that by overriding `bind_wp` for the effect with an efficient one.
 *)
unfold let g_bind (a:Type) (b:Type) (wp:__tac_wp a) (f:a -> __tac_wp b) = fun ps post ->
    wp ps (fun m' -> match m' with
                     | Success a q -> f a q post
                     | Failed msg q -> post (Failed msg q))

unfold let g_compact (a:Type) (wp:__tac_wp a) : __tac_wp a =
    fun ps post -> forall post'. (forall (r:__result a). post r <==> post' r) ==> wp ps post'

unfold let __TAC_eff_override_bind_wp (r:range) (a:Type) (b:Type) (wp:__tac_wp a) (f:a -> __tac_wp b) =
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

let return (#a:Type) (x:a) : tactic a =
    fun () -> x

let bind (#a:Type) (#b:Type) (t : tactic a) (f : a -> tactic b) : tactic b =
    fun () -> let r = t () in f r ()

let idtac : tactic unit =
    return ()

(* Fix combinator, so we need not expose the TAC effect (c.f. 1017) *)
val fix : #a:Type -> (tactic a -> tactic a) -> unit -> Tac a
let rec fix #a ff (u:unit) = ff (fix #a ff) ()

val fix1 : #a:Type -> #b:Type -> ((b -> tactic a) -> (b -> tactic a)) -> b -> unit -> Tac a
let rec fix1 #a #b ff x (u:unit) = ff (fix1 #a #b ff) x ()

(* working around #885 *)
let __fail (a:Type) (msg:string) : __tac a = fun s0 -> Failed #a msg s0
let fail (#a:Type) (msg:string) : tactic a = fun () -> TAC?.reflect (__fail a msg)

let reify_tactic (t:tactic 'a) : __tac 'a =
  fun s -> reify (t ()) s

// Never fails
let trytac (#a:Type) (t : tactic a) : tactic (option a) = fun () ->
    TAC?.reflect (fun ps -> match reify_tactic t ps with
                            | Success a ps' -> Success (Some a) ps'
                            | Failed _ _ -> Success None ps)

let or_else (#a:Type) (t1 : tactic a) (t2 : tactic a) : tactic a =
    r <-- trytac t1;
    (match r with
    | Some x -> return x
    | None -> t2)

(*
 * This is the way we inspect goals and any other term. We can quote them
 * to turn them into a representation of them. Having a total function
 * that does this is completely unsound (1 + 1 == 2, but not syntactically,
 * contradiction).
 *
 * So, we encapsulate the syntax inspection effect as a tactic (in the TAC effect)
 * so it cannot taint user code (pure or impure!). The cleanest way would be to directly
 * assume __embed as a `a -> tactic term` computation (TODO?)
 *)
assume private val __embed  : #a:Type -> a -> term
unfold let quote #a (x:a) : tactic term = fun () -> __embed x


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

assume private val __simpl  : __tac unit
let simpl : tactic unit = fun () -> TAC?.reflect __simpl

assume private val __revert  : __tac unit
let revert : tactic unit = fun () -> TAC?.reflect __revert

assume private val __clear   : __tac unit
let clear : tactic unit = fun () -> TAC?.reflect __clear

assume private val __split   : __tac unit
let split : tactic unit = fun () -> TAC?.reflect __split

assume private val __merge   : __tac unit
let merge : tactic unit = fun () -> TAC?.reflect __merge

// TODO: isn't this is unsound if b is not the environment?
// I think so but couldn't quickly come up with a contradiction
assume private val __rewrite : binder -> __tac unit
let rewrite (b:binder) : tactic unit = fun () -> TAC?.reflect (__rewrite b)

assume private val __smt     : __tac unit
let smt () : tactic unit = fun () -> TAC?.reflect __smt

assume private val __focus: __tac unit -> __tac unit
let focus (f:tactic unit) : tactic unit = fun () -> TAC?.reflect (__focus (reify_tactic f))

(* could be implemented using __focus *)
assume private val __seq : __tac unit -> __tac unit -> __tac unit
let seq (f:tactic unit) (g:tactic unit) : tactic unit = fun () ->
  TAC?.reflect (__seq (reify_tactic f) (reify_tactic g))

assume private val __exact : term -> __tac unit
let exact (t:term) : tactic unit = fun () -> TAC?.reflect (__exact t)

assume private val __apply_lemma : term -> __tac unit
let apply_lemma (t:tactic term) : tactic unit = fun () -> let tt = t () in TAC?.reflect (__apply_lemma tt)

assume val __print : string -> __tac unit
let print (msg:string) : tactic unit = fun () -> TAC?.reflect (__print msg)

assume val __dump : string -> __tac unit
let dump (msg:string) : tactic unit = fun () -> TAC?.reflect (__dump msg)

assume val __grewrite : term -> term -> __tac unit
let grewrite (t1:term) (t2:term) : tactic unit =
    fun () -> TAC?.reflect (__grewrite t1 t2)

let rec revert_all (bs:binders) : tactic unit =
    match bs with
    | [] -> return ()
    | _::tl -> revert;;
               revert_all tl

(* Cannot eta reduce this... *)
let get : tactic state = fun () -> TAC?.__get ()

let cur_goal : tactic goal =
  ps <-- get;
  let goals, _ = ps in
  match goals with
  | [] -> fail "No more goals"
  | hd::_ -> return hd

let destruct_equality_implication (t:term) : tactic (option (formula * term)) =
    match term_as_formula t with
    | Implies lhs rhs ->
        let lhs = term_as_formula lhs in
        begin match lhs with
        | Comp Eq _ _ _ -> return (Some (lhs, rhs))
        | _ -> return None
        end
    | _ -> return None

let rec visit (callback:tactic unit) () : Tac unit =
    focus (or_else callback
                   (eg <-- cur_goal;
                    let e, g = eg in
                    match term_as_formula g with
                    | Forall b phi ->
                        binders <-- forall_intros;
                        seq (visit callback) (
                            revert_all binders
                        )
                    | And p q ->
                        seq split (
                            visit callback;;
                            trytac merge;;
                            return ()
                        )
                    | Implies p q ->
                        implies_intro;;
                        seq (visit callback)
                            revert
                    | _ ->
                        or_else trivial (smt ())
                   )
          ) ()

// Need to thunk it like to this for proper handling of non-termination.
// (not doing it would still work, because of issue #1017, but should not)
let rec simplify_eq_implication (u:unit) : Tac unit = (
    g <-- cur_goal;
    let context, goal_t = g in // G |- x=e ==> P
    r <-- destruct_equality_implication goal_t;
    match r with
    | None ->
        fail "Not an equality implication"
    | Some (_, rhs) ->
        eq_h <-- implies_intro; // G, eq_h:x=e |- P
        rewrite eq_h;; // G, eq_h:x=e |- P[e/x]
        clear;; // G |- P[e/x]
        visit simplify_eq_implication) ()

let rec try_rewrite_equality (x:term) (bs:binders) : tactic unit =
    match bs with
    | [] -> return ()
    | x_t::bs ->
        begin match term_as_formula (type_of_binder x_t) with
        | Comp Eq _ y _ ->
            if term_eq x y
            then rewrite x_t
            else try_rewrite_equality x bs
        | _ ->
            try_rewrite_equality x bs
        end

let rec rewrite_all_context_equalities (bs:binders) : tactic unit =
    match bs with
    | [] ->
        return ()
    | x_t::bs -> begin
        match term_as_formula (type_of_binder x_t) with
        | Comp Eq _ _ _ ->
            rewrite x_t;;
            rewrite_all_context_equalities bs
        | _ ->
            rewrite_all_context_equalities bs
        end

let rewrite_eqs_from_context : tactic unit =
    g <-- cur_goal;
    let context, _ = g in
    rewrite_all_context_equalities (binders_of_env context)

let rewrite_equality (x:tactic term) : tactic unit =
    g <-- cur_goal;
    let context, _ = g in
    t <-- x;
    try_rewrite_equality t (binders_of_env context)

let rewrite_all_equalities : tactic unit =
    visit (simplify_eq_implication)

// See comment on `simplify_eq_implication`
let rec unfold_definition_and_simplify_eq' (tm:term) (u:unit) : Tac unit = (
    g <-- cur_goal;
    let (_, goal_t) = g in
    match term_as_formula goal_t with
    | App hd arg ->
        if term_eq hd tm
        then trivial
        else return ()
    | _ -> begin
        r <-- destruct_equality_implication goal_t;
        match r with
        | None -> fail "Not an equality implication"
        | Some (_, rhs) ->
            eq_h <-- implies_intro;
            rewrite eq_h;;
            clear;;
            visit (unfold_definition_and_simplify_eq' tm)
        end) ()

// Proof namespace management
assume val __prune : string -> __tac unit
let prune ns : tactic unit = fun () -> TAC?.reflect (__prune ns)

assume val __addns : string -> __tac unit
let addns ns : tactic unit = fun () -> TAC?.reflect (__addns ns)

let unfold_definition_and_simplify_eq (tm:tactic term) : tactic unit =
    tm' <-- tm;
    unfold_definition_and_simplify_eq' tm'

abstract
let by_tactic (t:__tac unit) (a:Type) : Type = a

// Must run with tactics off, as it will otherwise try to run `by_tactic
// (reify_tactic t)`, which fails as `t` is not a concrete tactic
#reset-options "--no_tactics"
let assert_by_tactic (t:tactic unit) (p:Type)
  : Pure unit
         (requires (by_tactic (reify_tactic t) p))
         (ensures (fun _ -> p))
  = ()
#reset-options


(* Monadic helpers, could be made generic for do notation? *)

val liftM1' : ('a -> tactic 'b) -> (tactic 'a -> tactic 'b)
let liftM1' f ma = a <-- ma;
                   f a

val liftM1 : ('a -> 'b) -> (tactic 'a -> tactic 'b)
let liftM1 f = liftM1' (fun x -> return (f x))

val liftM2' : ('a -> 'b -> tactic 'c) -> (tactic 'a -> tactic 'b -> tactic 'c)
let liftM2' f ma mb = a <-- ma;
                      b <-- mb;
                      f a b

val liftM2 : ('a -> 'b -> 'c) -> (tactic 'a -> tactic 'b -> tactic 'c)
let liftM2 f = liftM2' (fun x y -> return (f x y))
