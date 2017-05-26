module FStar.Tactics.Builtins

open FStar.Tactics.Effect
open FStar.Order
open FStar.Reflection

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

assume private val __norm  : list norm_step -> __tac unit
let norm steps : tactic unit = fun () -> TAC?.reflect (__norm steps)

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
let exact (t:tactic term) : tactic unit = fun () -> let tt = t () in TAC?.reflect (__exact tt)

assume private val __apply_lemma : term -> __tac unit
let apply_lemma (t:tactic term) : tactic unit = fun () -> let tt = t () in TAC?.reflect (__apply_lemma tt)

assume private val __print : string -> __tac unit
let print (msg:string) : tactic unit = fun () -> TAC?.reflect (__print msg)

assume private val __dump : string -> __tac unit
let dump (msg:string) : tactic unit = fun () -> TAC?.reflect (__dump msg)

assume private val __grewrite : term -> term -> __tac unit
let grewrite (t1:term) (t2:term) : tactic unit =
    fun () -> TAC?.reflect (__grewrite t1 t2)

assume private val __trefl : __tac unit
let trefl : tactic unit = fun () -> TAC?.reflect __trefl

assume private val __pointwise : __tac unit -> __tac unit
let pointwise (tau : tactic unit) : tactic unit = fun () -> TAC?.reflect (__pointwise (reify_tactic tau))

assume private val __later : __tac unit
let later : tactic unit = fun () -> TAC?.reflect __later

assume private val __qed : __tac unit
let qed : tactic unit = fun () -> TAC?.reflect __qed

// Proof namespace management
assume private val __prune : string -> __tac unit
let prune ns : tactic unit = fun () -> TAC?.reflect (__prune ns)

assume private val __addns : string -> __tac unit
let addns ns : tactic unit = fun () -> TAC?.reflect (__addns ns)

assume private val __cases : term -> __tac (term * term)
let cases t : tactic (term * term) = fun () -> TAC?.reflect (__cases t)
