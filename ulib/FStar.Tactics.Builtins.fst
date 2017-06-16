module FStar.Tactics.Builtins

open FStar.Tactics.Effect
open FStar.Order
open FStar.Reflection

(* Inspecting proofstate, needs to go via this since it is an assumed type *)
assume private val __cur_env     : __tac env
let cur_env = fun () -> TAC?.reflect __cur_env

assume private val __cur_goal    : __tac term
let cur_goal = fun () -> TAC?.reflect __cur_goal

assume private val __cur_witness : __tac term
let cur_witness = fun () -> TAC?.reflect __cur_witness

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

assume private val __trytac : #a:Type -> __tac a -> __tac (option a)
let trytac (t : tactic 'a) = fun () -> TAC?.reflect (__trytac (reify_tactic t))

assume private val __trivial  : __tac unit
let trivial : tactic unit = fun () -> TAC?.reflect __trivial

assume private val __norm  : list norm_step -> __tac unit
let norm steps : tactic unit = fun () -> TAC?.reflect (__norm steps)

assume private val __intro  : __tac binder
let intro : tactic binder = fun () -> TAC?.reflect __intro

assume private val __revert  : __tac unit
let revert : tactic unit = fun () -> TAC?.reflect __revert

assume private val __clear   : __tac unit
let clear : tactic unit = fun () -> TAC?.reflect __clear

assume private val __rewrite : binder -> __tac unit
let rewrite (b:binder) : tactic unit = fun () -> TAC?.reflect (__rewrite b)

assume private val __smt     : __tac unit
let smt () : tactic unit = fun () -> TAC?.reflect __smt

assume private val __divide: int -> __tac 'a -> __tac 'b -> __tac ('a * 'b)
let divide (n:int) (f:tactic 'a) (g:tactic 'b): tactic ('a * 'b) = fun () -> TAC?.reflect (__divide n (reify_tactic f) (reify_tactic g))

(* could be implemented using __focus *)
assume private val __seq : __tac unit -> __tac unit -> __tac unit
let seq (f:tactic unit) (g:tactic unit) : tactic unit = fun () ->
  TAC?.reflect (__seq (reify_tactic f) (reify_tactic g))

assume private val __exact : term -> __tac unit
let exact (t:tactic term) : tactic unit = fun () -> let tt = t () in TAC?.reflect (__exact tt)

assume private val __exact_lemma : term -> __tac unit
let exact_lemma (t:tactic term) : tactic unit = fun () -> let tt = t () in TAC?.reflect (__exact_lemma tt)

assume private val __apply : term -> __tac unit
let apply (t:tactic term) : tactic unit = fun () -> let tt = t () in TAC?.reflect (__apply tt)

assume private val __apply_lemma : term -> __tac unit
let apply_lemma (t:tactic term) : tactic unit = fun () -> let tt = t () in TAC?.reflect (__apply_lemma tt)

assume private val __print : string -> __tac unit
let print (msg:string) : tactic unit = fun () -> TAC?.reflect (__print msg)

assume private val __dump : string -> __tac unit
let dump (msg:string) : tactic unit = fun () -> TAC?.reflect (__dump msg)

assume private val __dump1 : string -> __tac unit
let dump1 (msg:string) : tactic unit = fun () -> TAC?.reflect (__dump1 msg)

assume private val __trefl : __tac unit
let trefl : tactic unit = fun () -> TAC?.reflect __trefl

assume private val __pointwise : __tac unit -> __tac unit
let pointwise (tau : tactic unit) : tactic unit = fun () -> TAC?.reflect (__pointwise (reify_tactic tau))

assume private val __later : __tac unit
let later : tactic unit = fun () -> TAC?.reflect __later

assume private val __flip : __tac unit
let flip : tactic unit = fun () -> TAC?.reflect __flip

assume private val __qed : __tac unit
let qed : tactic unit = fun () -> TAC?.reflect __qed

// Proof namespace management
assume private val __prune : string -> __tac unit
let prune ns : tactic unit = fun () -> TAC?.reflect (__prune ns)

assume private val __addns : string -> __tac unit
let addns ns : tactic unit = fun () -> TAC?.reflect (__addns ns)

assume private val __cases : term -> __tac (term * term)
let cases t : tactic (term * term) = fun () -> TAC?.reflect (__cases t)

assume private val __set_options : string -> __tac unit
let set_options s : tactic unit = fun () -> TAC?.reflect (__set_options s)
