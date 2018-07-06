(**
Every tactic primitive, i.e., those built into the compiler
@summary Tactic primitives
*)
module FStar.Tactics.Builtins

open FStar.Tactics.Effect
open FStar.Reflection.Types
open FStar.Reflection.Data
open FStar.Tactics.Types
open FStar.Tactics.Result

(** Simply fail. The specs ensures that it fails *without changing the
proofstate*, but hides the message. *)
assume val fail : #a:Type -> m:string -> TacH a (requires (fun _ -> True)) (ensures (fun ps r -> Failed? r /\ Failed?.ps r == ps))

// NOTE: The only reason `fail` is assumed as a primitive is to enable
// the TacFail debugging flag. We could instead define it like this,
// obtaining the exact same spec and runtime behaviour (minus the
// debugging flag).
(* let fail = fail_act *)

(** [top_env] returns the environment where the tactic started running.
 * This works even if no goals are present. *)
assume val top_env : unit -> Tac env

(** [push_binder] extends the environment with a single binder.
    This is useful as one traverses the syntax of a term,
    pushing binders as one traverses a binder in a lambda,
    match, etc. Note, the environment here is disconnected to
    (though perhaps derived from) the environment in the proofstate *)
(* TODO: move to FStar.Reflection.Basic? *)
assume val push_binder : env -> binder -> env

(** [fresh ()] returns a fresh integer. It does not get reset when
catching a failure. *)
assume val fresh : unit -> Tac int

(** [is_guard] returns whether the current goal arised from a typechecking guard *)
assume val is_guard : unit -> Tac bool

(** [refine_intro] will turn a goal of shape [w : x:t{phi}]
into [w : t] and [phi{w/x}] *)
assume val refine_intro : unit -> Tac unit

(** [tc] returns the type of a term in the current environment,
or fails if it is untypeable. *)
assume val tc : term -> Tac term

(** [unshelve] creates a goal from a term for its given type.
It can be used when the system decided not to present a goal, but
you want one anyway. For example, if you request a uvar through
[uvar_env] or [fresh_uvar], you might want to instantiate it
explicitly. *)
assume val unshelve : term -> Tac unit

(** [unquote t] with turn a quoted term [t] into an actual value, of
any type. This will fail at tactic runtime if the quoted term does not
typecheck to type [a]. *)
assume val unquote : #a:Type -> term -> Tac a

assume private val __catch : #a:Type -> __tac a -> __tac (either string a)
(** [catch t] will attempt to run [t] and allow to recover from a failure.
If [t] succeeds with return value [a], [catch t] returns [Inr a].
On failure, it returns [Inl msg], where [msg] is the error [t]
raised. See also [or_else].
*)
let catch (t : unit -> Tac 'a) = TAC?.reflect (__catch (reify (t ())))

(** [trivial] will discharge the goal if it's exactly [True] after
doing normalization and simplification of it. *)
assume val trivial  : unit -> Tac unit

(** [norm steps] will call the normalizer on the current goal's
type and witness, with its reduction behaviour parameterized
by the flags in [steps].
Currently, the flags (provided in Prims) are
[simpl] (do logical simplifications)
[whnf] (only reduce until weak head-normal-form)
[primops] (performing primitive reductions, such as arithmetic and
string operations)
[delta] (unfold names)
[zeta] (inline let bindings)
[iota] (reduce match statements over constructors)
[delta_only] (restrict delta to only unfold this list of fully-qualfied identifiers)
*)
assume val norm  : list norm_step -> Tac unit

(** [norm_term_env e steps t] will call the normalizer on the term [t]
using the list of steps [steps], over environment [e]. The list has the same meaning as for [norm]. *)
assume val norm_term_env  : env -> list norm_step -> term -> Tac term

(** [norm_binder_type steps b] will call the normalizer on the type of the [b]
binder for the current goal. Notably, this cannot be done via binder_retype and norm,
because of uvars being resolved to lambda-abstractions. *)
assume val norm_binder_type  : list norm_step -> binder -> Tac unit

(** [intro] pushes the first argument of an arrow goal into the
environment, turning [Gamma |- ?u : x:a -> b] into [Gamma, x:a |- ?u' : b].
Note that this does not work for logical implications/forall. See
FStar.Tactics.Logic for that.
*)
assume val intro : unit -> Tac binder

(** Similar to intros, but allows to build a recursive function.
Currently broken (c.f. issue #1103)
*)
assume val intro_rec  : unit -> Tac (binder * binder)

(** [rename_to b nm] will rename the binder [b] to [nm] in
the environment, goal, and witness in a safe manner. The only use of this
is to make goals and terms more user readable. *)
assume val rename_to  : binder -> string -> Tac unit

(** [revert] pushes out a binder from the environment into the goal type,
so a behaviour opposite to [intros].
*)
assume val revert  : unit -> Tac unit

(** [binder_retype] changes the type of a binder in the context. After calling it
with a binder of type `t`, the user is presented with a goal of the form `t == ?u`
to be filled. The original goal (following that one) has the type of `b` in the
context replaced by `?u`.
*)
assume val binder_retype  : binder -> Tac unit

(** [clear_top] will drop the outermost binder from the environment.
Can only be used if the goal does not at all depend on it.
*)
assume val clear_top : unit -> Tac unit

(** [clear] will drop the given binder from the context, is
nothing depends on it.
*)
assume val clear : binder -> Tac unit

(** If [b] is a binder of type [v == r], [rewrite b] will rewrite
the variable [v] for [r] everywhere in the current goal type and witness/
*)
assume val rewrite : binder -> Tac unit

(** [smt] will mark the current goal for being solved through the SMT.
This does not immediately run the SMT:  it is a marker.
This tactic never fails, and a goal marked for SMT cannot be brought back. *)
assume val smt     : unit -> Tac unit

assume val __divide : int -> __tac 'a -> __tac 'b -> __tac ('a * 'b)
(** [divide n t1 t2] will split the current set of goals into the [n]
first ones, and the rest. It then runs [t1] on the first set, and [t2]
on the second, returning both results (and concatenating remaining goals). *)
let divide (n:int) (f:unit -> Tac 'a) (g:unit -> Tac 'b): Tac ('a * 'b) =
    TAC?.reflect (__divide n (reify (f ())) (reify (g ())))

(* could be implemented using divide *)
assume val __seq : __tac unit -> __tac unit -> __tac unit
(** Runs tactic [t1] on the current goal, and then tactic [t2] on *each*
subgoal produced by [t1]. Each invocation of [t2] runs on a proofstate
with a single goal (they're "focused"). *)
let seq (f:unit -> Tac unit) (g:unit -> Tac unit) : Tac unit =
  TAC?.reflect (__seq (reify (f ())) (reify (g ())))

(** First boolean is whether to attempt to intrpoduce a refinement
before solving. In that case, a goal for the refinement formula will be
added. Second boolean is whether to set the expected type internally.
Just use `exact` from FStar.Tactics.Derived if you don't know what's up
with all this. *)
assume val t_exact : bool -> bool -> term -> Tac unit

(** Inner primitive for [apply], takes a boolean specifying whether
to not ask for implicits that appear free in posterior goals. Example:
when the boolean is true, applying transitivity to
[|- a = c] will give two goals, [|- a = ?u] and [|- ?u = c] without
asking to instantiate [?u] since it will most likely be constrained
later by solving these goals. In any case, we track [?u] and will fail
if it's not solved later.

You probably want [apply] from FStar.Tactics.Derived.
*)
assume val t_apply : bool -> term -> Tac unit

(** [apply_lemma l] will solve a goal of type [squash phi] when [l] is a Lemma
ensuring [phi]. The arguments to [l] and its requires clause are introduced as new goals.
As a small optimization, [unit] arguments are discharged by the engine. *)
// TODO: do the unit thing too for [apply].
assume val apply_lemma : term -> Tac unit

(** [print str] has no effect on the proofstate, but will have the side effect
of printing [str] on the compiler's standard output. *)
assume val print : string -> Tac unit

(** [debug str] is similar to [print str], but will only print the message
if the [--debug] option was given for the current module. *)
assume val debug : string -> Tac unit

(** Similar to [print], but will dump a text representation of the proofstate
along with the message. *)
assume val dump : string -> Tac unit

(** Similar to [dump], but only dumping the current goal. *)
assume val dump1 : string -> Tac unit

(** Solves a goal [Gamma |= squash (l == r)] by attempting to unify
[l] with [r]. This currently only exists because of some universe problems
when trying to [apply] a reflexivity lemma. *)
assume val trefl : unit -> Tac unit

assume val __pointwise : direction -> __tac unit -> __tac unit
(** (TODO: explain bettter) When running [pointwise tau] For every
subterm [t'] of the goal's type [t], the engine will build a goal [Gamma
|= t' == ?u] and run [tau] on it. When the tactic proves the goal,
the engine will rewrite [t'] for [?u] in the original goal type. This
is done for every subterm, bottom-up. This allows to recurse over an
unknown goal type. By inspecting the goal, the [tau] can then decide
what to do (to not do anything, use [trefl]). *)
(* TODO: move these away *)
let pointwise  (tau : unit -> Tac unit) : Tac unit = TAC?.reflect (__pointwise BottomUp (reify (tau ())))
let pointwise' (tau : unit -> Tac unit) : Tac unit = TAC?.reflect (__pointwise TopDown  (reify (tau ())))

assume val __topdown_rewrite : (term -> __tac (bool * int)) -> __tac unit -> __tac unit

(** [topdown_rewrite ctrl rw] is used to rewrite those sub-terms [t]
    of the goal on which [fst (ctrl t)] returns true.

    On each such sub-term, [rw] is presented with an equality of goal
    of the form [Gamma |= t == ?u]. When [rw] proves the goal,
    the engine will rewrite [t] for [?u] in the original goal
    type.

    The goal formula is traversed top-down and the traversal can be
    controlled by [snd (ctrl t)]:

    When [snd (ctrl t) = 0], the traversal continues down through the
    position in the goal term.

    When [snd (ctrl t) = 1], the traversal continues to the next
    sub-tree of the goal.

    When [snd (ctrl t) = 2], no more rewrites are performed in the
    goal.
*)
let topdown_rewrite
       (ctrl : term -> Tac (bool * int))
       (rw:unit -> Tac unit)
    : Tac unit
    = TAC?.reflect (__topdown_rewrite (fun x -> reify (ctrl x)) (reify (rw ())))

(** Push the current goal to the back. *)
assume val later : unit -> Tac unit

(** Given the current goal [Gamma |- w : t],
[dup] will turn this goal into
[Gamma |- ?u : t] and
[Gamma |= ?u == w]. It can thus be used to change
a goal's witness in any way needed, by choosing
some [?u] (possibly with exact) and then solving the other goal.
*)
assume val dup : unit -> Tac unit

(** Flip the order of the first two goals. *)
assume val flip : unit -> Tac unit
assume val join : unit -> Tac unit

(** Succeed if there are no more goals left, and fail otherwise. *)
assume val qed : unit -> Tac unit

// Proof namespace management
(** [prune "A.B.C"] will mark all top-level definitions in module
[A.B.C] (and submodules of it) to not be encoded to the SMT, for the current goal.
The string is a namespace prefix. [prune ""] will prune everything, but note
that [prune "FStar.S"] will not prune ["FStar.Set"]. *)
assume val prune : string -> Tac unit

(** The opposite operation of [prune]. The latest one takes precedence. *)
assume val addns : string -> Tac unit

(** Given a disjunction [e], destruct it and generate two goals
for each case. Return value is terms representing proofs for each case.
The first one is only valid in the first goal, and likewise for
the second (TODO: change this awful behaviour).
*)
assume val cases : term -> Tac (term * term)

(** Destruct a value of an inductive type by matching on it. The generated
match has one branch for each constructor and is therefore trivially
exhaustive, no VC is generated for that purpose. It returns a list
with the fvars of each constructor and their arities, in the order
they appear as goals. *)
assume val t_destruct : term -> Tac (list (fv * nat))

(** Set command line options for the current goal. Mostly useful to
change SMT encoding options such as [set_options "--z3rlimit 20"]. *)
assume val set_options : string -> Tac unit

(** Creates a new, unconstrained unification variable in environment
[env]. The type of the uvar can optionally be provided in [o]. If not
provided, a second uvar is created for the type. *)
assume val uvar_env : env -> option typ -> Tac term

(** Call the unifier on two terms. The returned boolean specifies
whether unification was possible. When the tactic returns true, the
terms have been unified, instantiating uvars as needed. When false,
unification was not possible and no change to uvars occurs. *)
assume val unify_env : env -> term -> term -> Tac bool

(** Launches an external process [prog] with arguments [args] and input
[input] and returns the output. For security reasons, this can only be
performed when the `--unsafe_tactic_exec` options was provided for the
current F* invocation. The tactic will fail if this is not so. *)
assume val launch_process : string -> string -> string -> Tac string

(** Get a fresh bv of some name and type. The name is only useful
for pretty-printing, since there is a fresh unaccessible integer within
the bv too. *)
assume val fresh_bv_named : string -> typ -> Tac bv

(** Change the goal to another type, given that it is convertible
to the current type. *)
assume val change : typ -> Tac unit

(** Get the current guard policy. The guard policy specifies what should
be done when a VC arises internally from the tactic engine. Options
are SMT (mark it as an SMT goal), Goal (add it as an extra goal)
and Force (only allow trivial guards, that need no SMT. *)
assume val get_guard_policy : unit -> Tac guard_policy

(** Set the current guard policy. See [get_guard_policy} for an explanation *)
assume val set_guard_policy : guard_policy -> Tac unit

(** [lax_on] returns true iff the current environment has the
`--lax` option set, and thus drops all verification conditions. *)
assume val lax_on : unit -> Tac bool

(** Ignore the current goal. If left unproven, this will fail after
the tactic finishes. *)
assume val dismiss : unit -> Tac unit

(** Admit the current goal. Raises a warning. *)
assume val tadmit : unit -> Tac unit

(** View a term in a fully-named representation *)
assume val inspect : term -> Tac term_view

(** Pack a term view on a fully-named representation back into a term *)
assume val pack    : term_view -> Tac term

(* Guido: TODO: restore *)
(* assume val lget     : #a:Type -> string -> Tac a *)
(* assume val lset     : #a:Type -> string -> a -> Tac unit *)
