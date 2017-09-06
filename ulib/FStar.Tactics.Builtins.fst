(**
Every tactic primitive, i.e., those built into the compiler
@summary Tactic primitives
*)
module FStar.Tactics.Builtins

open FStar.Tactics.Effect
open FStar.Order
open FStar.Reflection
open FStar.Reflection.Types

assume private val __cur_env     : __tac env
(** [cur_env] returns the current goal's environment *)
let cur_env = fun () -> TAC?.reflect __cur_env

assume private val __cur_goal    : __tac term
(** [cur_goal] returns the current goal's type *)
let cur_goal = fun () -> TAC?.reflect __cur_goal

assume private val __cur_witness : __tac term
(** [cur_witness] returns the current goal's witness *)
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

assume private val __unquote : #a:Type -> term -> __tac a
let unquote (#a:Type) (t:term) : tactic a = fun () -> TAC?.reflect (__unquote #a t)

assume private val __trytac : #a:Type -> __tac a -> __tac (option a)
(** [trytac t] will attempt to run [t] and allow to recover from a failure.
If [t] succeeds with return value [a], [trytac t] returns [Some a].
On failure, it returns [None]. See also [or_else].
*)
let trytac (t : tactic 'a) = fun () -> TAC?.reflect (__trytac (reify_tactic t))

assume private val __trivial  : __tac unit
(** [trivial] will discharge the goal if it's exactly [True] after
doing normalization and simplification of it. *)
let trivial : tactic unit = fun () -> TAC?.reflect __trivial

assume private val __norm  : list norm_step -> __tac unit
(** [norm steps] will call the normalizer on the current goal's
type and witness, with its reduction behaviour parameterized
by the flags in [steps].
Currently, the flags (defined in FStar.Reflection.Syntax) are
[Simpl] (do logical simplifications)
[WHNF] (only reduce until weak head-normal-form)
[Primops] (performing primitive reductions, such as arithmetic and
string operations)
[Delta] (unfold names)
[UnfoldOnly] (restricts unfolding to those names)
*)
let norm steps : tactic unit = fun () -> TAC?.reflect (__norm steps)

assume private val __intro  : __tac binder
(** [intro] pushes the first argument of an arrow goal into the
environment, turning [Gamma |- ?u : x:a -> b] into [Gamma, x:a |- ?u' : b].
Note that this does not work for logical implications/forall. See
FStar.Tactics.Logic for that.
*)
let intro : tactic binder = fun () -> TAC?.reflect __intro

assume private val __intro_rec  : __tac (binder * binder)
(** Similar to intros, but allows to build a recursive function.
Currently broken (c.f. issue #1103)
*)
let intro_rec : tactic (binder * binder) = fun () -> TAC?.reflect __intro_rec

assume private val __revert  : __tac unit

(** [revert] pushes out a binder from the environment into the goal type,
so a behaviour opposite to [intros].
*)
let revert : tactic unit = fun () -> TAC?.reflect __revert

assume private val __clear   : __tac unit
(** [clear] will drop the outermost binder from the environment.
Can only be used if the goal does not at all depend on it.
*)
let clear : tactic unit = fun () -> TAC?.reflect __clear

assume private val __rewrite : binder -> __tac unit
(** If [b] is a binder of type [v == r], [rewrite b] will rewrite
the variable [v] for [r] everywhere in the current goal type and witness/
*)
let rewrite (b:binder) : tactic unit = fun () -> TAC?.reflect (__rewrite b)

assume private val __smt     : __tac unit
(** [smt] will mark the current goal for being solved through the SMT.
This does not immediately run the SMT:  it is a marker.
This tactic never fails, and a goal marked for SMT cannot be brought back. *)
let smt : tactic unit = fun () -> TAC?.reflect __smt

assume private val __divide: int -> __tac 'a -> __tac 'b -> __tac ('a * 'b)
(** [divide n t1 t2] will split the current set of goals into the [n]
first ones, and the rest. It then runs [t1] on the first set, and [t2]
on the second, returning both results (and concatenating remaining goals). *)
let divide (n:int) (f:tactic 'a) (g:tactic 'b): tactic ('a * 'b) = fun () -> TAC?.reflect (__divide n (reify_tactic f) (reify_tactic g))

(* could be implemented using divide *)
assume private val __seq : __tac unit -> __tac unit -> __tac unit
(** Runs tactic [t1] on the current goal, and then tactic [t2] on *each*
subgoal produced by [t1]. Each invocation of [t2] runs on a proofstate
with a single goal (they're "focused"). *)
let seq (f:tactic unit) (g:tactic unit) : tactic unit = fun () ->
  TAC?.reflect (__seq (reify_tactic f) (reify_tactic g))

assume private val __exact : term -> __tac unit
(** [exact e] will solve a goal [Gamma |- w : t] if [e] has type exactly
[t] in [Gamma]. Also, [e] needs to unift with [w], but this will almost
always be the case since [w] is usually a uvar. *)
let exact (t:tactic term) : tactic unit = fun () -> let tt = t () in TAC?.reflect (__exact tt)

assume private val __apply : term -> __tac unit
(** [apply f] will attempt to produce a solution to the goal by an application
of [f] to any amount of arguments (which need to be solved as further goals).
The amount of arguments introduced is the least such that [f a_i] unifies
with the goal's type. *)
let apply (t:tactic term) : tactic unit = fun () -> let tt = t () in TAC?.reflect (__apply tt)

assume private val __apply_lemma : term -> __tac unit
(** [apply_lemma l] will solve a goal of type [squash phi] when [l] is a Lemma
ensuring [phi]. The arguments to [l] and its requires clause are introduced as new goals.
As a small optimization, [unit] arguments are discharged by the engine. *)
// TODO: do the unit thing too for [apply].
let apply_lemma (t:tactic term) : tactic unit = fun () -> let tt = t () in TAC?.reflect (__apply_lemma tt)

assume private val __print : string -> __tac unit
(** [print str] has no effect on the proofstate, but will have the side effect
of printing [str] on the compiler's standard output. *)
let print (msg:string) : tactic unit = fun () -> TAC?.reflect (__print msg)

assume private val __dump : string -> __tac unit
(** Similar to [print], but will dump a text representation of the proofstate
along with the message. *)
let dump (msg:string) : tactic unit = fun () -> TAC?.reflect (__dump msg)

assume private val __dump1 : string -> __tac unit
(** Similar to [dump], but only dumping the current goal. *)
let dump1 (msg:string) : tactic unit = fun () -> TAC?.reflect (__dump1 msg)

assume private val __trefl : __tac unit
(** Solves a goal [Gamma |= squash (l == r)] by attempting to unify
[l] with [r]. This currently only exists because of some universe problems
when trying to [apply] a reflexivity lemma. *)
let trefl : tactic unit = fun () -> TAC?.reflect __trefl

assume private val __pointwise : __tac unit -> __tac unit
(** (TODO: explain bettter) When running [pointwise tau] For every
subterm [t'] of the goal's type [t], the engine will build a goal [Gamma
|= t' == ?u] and run [tau] on it. When the tactic proves the goal,
the engine will rewrite [t'] for [?u] in the original goal type. This
is done for every subterm, bottom-up. This allows to recurse over an
unknown goal type. By inspecting the goal, the [tau] can then decide
what to do (to not do anything, use [trefl]). *)
let pointwise (tau : tactic unit) : tactic unit = fun () -> TAC?.reflect (__pointwise (reify_tactic tau))

assume private val __later : __tac unit
(** Push the current goal to the back. *)
let later : tactic unit = fun () -> TAC?.reflect __later

assume private val __dup : __tac unit
(** Given the current goal [Gamma |- w : t],
[dup] will turn this goal into
[Gamma |- ?u : t] and
[Gamma |= ?u == w]. It can thus be used to change
a goal's witness in any way needed, by choosing
some [?u] (possibly with exact) and then solving the other goal.
*)
let dup : tactic unit = fun () -> TAC?.reflect __dup

assume private val __flip : __tac unit
(** Flip the first two goals. *)
let flip : tactic unit = fun () -> TAC?.reflect __flip

assume private val __qed : __tac unit
(** Succeed if there are no more goals left, and fail otherwise. *)
let qed : tactic unit = fun () -> TAC?.reflect __qed

// Proof namespace management
assume private val __prune : string -> __tac unit
(** [prune "A.B.C"] will mark all top-level definitions in module
[A.B.C] (and submodules of it) to not be encoded to the SMT, for the current goal.
The string is a namespace prefix. [prune ""] will prune everything, but note
that [prune "FStar.S"] will not prune ["FStar.Set"]. *)
let prune ns : tactic unit = fun () -> TAC?.reflect (__prune ns)

assume private val __addns : string -> __tac unit
(** The opposite operation of [prune]. The latest one takes precedence. *)
let addns ns : tactic unit = fun () -> TAC?.reflect (__addns ns)

assume private val __cases : term -> __tac (term * term)
(** Given a disjunction [e], destruct it and generate two goals
for each case. Return value is terms representing proofs for each case.
The first one is only valid in the first goal, and likewise for
the second (TODO: change this awful behaviour).
*)
let cases t : tactic (term * term) = fun () -> TAC?.reflect (__cases t)

assume private val __set_options : string -> __tac unit
(** Set command line options for the current goal. Mostly useful to
change SMT encoding options such as [set_options "--z3rlimit 20"]. *)
let set_options s : tactic unit = fun () -> TAC?.reflect (__set_options s)

assume private val __uvar_env : env -> option typ -> __tac term
let uvar_env (e : env) (o : option typ) : tactic term = fun () -> TAC?.reflect (__uvar_env e o)

assume private val __unify : term -> term -> __tac bool
let unify (t1 t2 : term) : tactic bool = fun () -> TAC?.reflect(__unify t1 t2)
