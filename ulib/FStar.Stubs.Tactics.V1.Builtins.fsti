(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
(**
Every tactic primitive, i.e., those built into the compiler
@summary Tactic primitives
*)
module FStar.Stubs.Tactics.V1.Builtins

open FStar.Stubs.VConfig
open FStar.Stubs.Reflection.V1.Builtins
open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V1.Data
open FStar.Reflection.Const
open FStar.Tactics.Effect
open FStar.Stubs.Tactics.Types
include FStar.Stubs.Tactics.Unseal

(** [top_env] returns the environment where the tactic started running.
 * This works even if no goals are present. *)
val top_env : unit -> Tac env

(** [fresh ()] returns a fresh integer. It does not get reset when
catching a failure. *)
val fresh : unit -> Tac int

(** [refine_intro] will turn a goal of shape [w : x:t{phi}]
into [w : t] and [phi{w/x}] *)
val refine_intro : unit -> Tac unit

(** [tc] returns the type of a term in [env],
or fails if it is untypeable. *)
val tc : env -> term -> Tac term

(** [tcc] like [tc], but returns the full computation type
with the effect label and its arguments (WPs, etc) as well *)
val tcc : env -> term -> Tac comp

(** [unshelve] creates a goal from a term for its given type.
It can be used when the system decided not to present a goal, but
you want one anyway. For example, if you request a uvar through
[uvar_env] or [fresh_uvar], you might want to instantiate it
explicitly. *)
val unshelve : term -> Tac unit

(** [unquote t] with turn a quoted term [t] into an actual value, of
any type. This will fail at tactic runtime if the quoted term does not
typecheck to type [a]. *)
val unquote : #a:Type -> term -> Tac a

(** [catch t] will attempt to run [t] and allow to recover from a
failure. If [t] succeeds with return value [a], [catch t] returns [Inr
a]. On failure, it returns [Inl msg], where [msg] is the error [t]
raised, and all unionfind effects are reverted. See also [recover] and
[or_else]. *)
val catch : #a:Type -> (unit -> Tac a) -> TacS (either exn a)

(** Like [catch t], but will not discard unionfind effects on failure. *)
val recover : #a:Type -> (unit -> Tac a) -> TacS (either exn a)

(** [norm steps] will call the normalizer on the current goal's
type and witness, with its reduction behaviour parameterized
by the flags in [steps].
Currently, the flags (provided in FStar.Pervasives) are
[simpl] (do logical simplifications)
[whnf] (only reduce until weak head-normal-form)
[primops] (performing primitive reductions, such as arithmetic and
string operations)
[delta] (unfold names)
[zeta] (unroll let rec bindings, but with heuristics to avoid loops)
[zeta_full] (unroll let rec bindings fully)
[iota] (reduce match statements over constructors)
[delta_only] (restrict delta to only unfold this list of fully-qualified identifiers)
*)
val norm  : list norm_step -> Tac unit

(** [norm_term_env e steps t] will call the normalizer on the term [t]
using the list of steps [steps], over environment [e]. The list has the same meaning as for [norm]. *)
val norm_term_env  : env -> list norm_step -> term -> Tac term

(** [norm_binder_type steps b] will call the normalizer on the type of the [b]
binder for the current goal. Notably, this cannot be done via binder_retype and norm,
because of uvars being resolved to lambda-abstractions. *)
val norm_binder_type  : list norm_step -> binder -> Tac unit

(** [intro] pushes the first argument of an arrow goal into the
environment, turning [Gamma |- ?u : x:a -> b] into [Gamma, x:a |- ?u' : b].
Note that this does not work for logical implications/forall. See
FStar.Tactics.Logic for that.
*)
val intro : unit -> Tac binder

(** Similar to intros, but allows to build a recursive function.
Currently broken (c.f. issue #1103)
*)
val intro_rec  : unit -> Tac (binder & binder)

(** [rename_to b nm] will rename the binder [b] to [nm] in
the environment, goal, and witness in a safe manner. The only use of this
is to make goals and terms more user readable. The primitive returns
the new binder, since the old one disappears from the context. *)
val rename_to  : binder -> string -> Tac binder

(** [revert] pushes out a binder from the environment into the goal type,
so a behaviour opposite to [intros].
*)
val revert  : unit -> Tac unit

(** [binder_retype] changes the type of a binder in the context. After calling it
with a binder of type `t`, the user is presented with a goal of the form `t == ?u`
to be filled. The original goal (following that one) has the type of `b` in the
context replaced by `?u`.
*)
val binder_retype  : binder -> Tac unit

(** [clear_top] will drop the outermost binder from the environment.
Can only be used if the goal does not at all depend on it.
*)
val clear_top : unit -> Tac unit

(** [clear] will drop the given binder from the context, is
nothing depends on it.
*)
val clear : binder -> Tac unit

(** If [b] is a binder of type [v == r], [rewrite b] will rewrite
the variable [v] for [r] everywhere in the current goal type and witness/
*)
val rewrite : binder -> Tac unit

(** First boolean is whether to attempt to introduce a refinement
before solving. In that case, a goal for the refinement formula will be
added. Second boolean is whether to set the expected type internally.
Just use `exact` from FStar.Tactics.Derived if you don't know what's up
with all this. *)
val t_exact : maybe_refine:bool -> set_expected_typ:bool -> term -> Tac unit

(** Inner primitive for [apply], takes a boolean specifying whether
to not ask for implicits that appear free in posterior goals, a
boolean specifying whether it's forbidden to instantiate uvars in the
goal, and a boolean specifying whether uvars resolved during unification
of the goal to the term should be typechecked as part of t_apply

If the third boolean is false, those uvars will be typechecked at the
end by the tactics engine.

Example: when [uopt] is true, applying transitivity to [|- a = c]
will give two goals, [|- a = ?u] and [|- ?u = c] without asking to
instantiate [?u] since it will most likely be constrained later by
solving these goals. In any case, we track [?u] and will fail if it's
not solved later.

Example: when [noinst] is true, applying a function returning
[1 = 2] will fail on a goal of the shape [1 = ?u] since it must
instantiate [?u]. We use this in typeclass resolution.

You may want [apply] from FStar.Tactics.Derived, or one of
the other user facing variants.
*)
val t_apply : uopt:bool -> noinst:bool -> tc_resolved_uvars:bool -> term -> Tac unit

(** [t_apply_lemma ni nilhs l] will solve a goal of type [squash phi]
when [l] is a Lemma ensuring [phi]. The arguments to [l] and its
requires clause are introduced as new goals. As a small optimization,
[unit] arguments are discharged by the engine. For the meaning of
the [noinst] boolean arg see [t_apply], briefly, it does not allow to
instantiate uvars in the goal. The [noinst_lhs] flag is similar, it
forbids instantiating uvars *but only on the LHS of the goal*, provided
the goal is an equality. It is meant to be useful for rewrite-goals, of
the shape [X = ?u]. Setting [noinst] means [noinst_lhs] is ignored. *)
val t_apply_lemma : noinst:bool -> noinst_lhs:bool -> term -> Tac unit
// TODO: do the unit thing too for [apply].

(** [print str] has no effect on the proofstate, but will have the side effect
of printing [str] on the compiler's standard output. *)
val print : string -> Tac unit

(** [debugging ()] returns true if the current module has the debug flag
on, i.e. when [--debug Tac] was passed in. *)
val debugging : unit -> Tac bool

(** Similar to [print], but will dump a text representation of the proofstate
along with the message. *)
val dump : string -> Tac unit

(** Similar to [dump], but will print *every* unsolved implicit
in the proofstate, not only the visible/focused goals. When the
[print_resolved] boolean is true, it will also print every solved goal.
Warning, these can be a *lot*. *)
val dump_all : print_resolved:bool -> string -> Tac unit

(** Will print a goal for every unresolved implicit in the provided goal. *)
val dump_uvars_of : goal -> string -> Tac unit

(** Solves a goal [Gamma |= squash (l == r)] by attempting to unify
[l] with [r]. This currently only exists because of some universe
problems when trying to [apply] a reflexivity lemma. When [allow_guards]
is [true], it is allowed that (some) guards are raised during the
unification process and added as a single goal to be discharged later.
Currently, the only guards allowed here are for equating refinement
types (e.g. [x:int{x>0}] and [x:int{0<x}]. *)
val t_trefl : allow_guards:bool -> Tac unit

(** Provides a proof for the equality
[(match e with ... | pi -> ei ...) a1 .. an
 == (match e with ... | pi -> e1 a1 .. an)].
This is particularly useful to rewrite the expression on the left to the
one on the right when the RHS is actually a unification variable. *)
val t_commute_applied_match : unit -> Tac unit

(** In case there are goals that are already solved which have
    non-trivial typing guards, make those guards as explicit proof
    obligations in the tactic state, solving any trivial ones by simplification.
    See tests/bug-reports/Bug2635.fst for some examples

    Update 11/14/2022: with the introduction of the core typechecker,
    this primitive should no longer be necessary. Try using the compat pre core
    flags, or `with_compat_pre_core` primitive if your code breaks without
    this.*)
[@@deprecated "This will soon be removed, please use compat pre core settings if needed"]
val gather_or_solve_explicit_guards_for_resolved_goals : unit -> Tac unit

(** [ctrl_rewrite] will traverse the current goal, and call [ctrl]
 * repeatedly on subterms. When [ctrl t] returns [(true, _)], the
 * tactic will call [rw] with a goal of type [t = ?u], which once
 * solved will rewrite [t] to the solution of [?u]. No goal is
 * made if [ctrl t] returns [(false, _)].
 *
 * The second component of the return value of [ctrl] specifies
 * whether for continue descending in the goal or not. It can
 * either be:
 *   - Continue: keep on with further subterms
 *   - Skip: stop descending in this tree
 *   - Abort: stop everything
 *
 * The first argument is the direction, [TopDown] or [BottomUp]. It
 * specifies how the AST of the goal is traversed (preorder or postorder).
 *
 * Note: for [BottomUp] a [Skip] means to stop trying to rewrite everything
 * from the current node up to the root, but still consider siblings. This
 * means that [ctrl_rewrite BottomUp (fun _ -> (true, Skip)) t] will call [t]
 * for every leaf node in the AST.
 *
 * See [pointwise] and [topdown_rewrite] for more friendly versions.
 *)
val ctrl_rewrite :
    direction ->
    (ctrl : term -> Tac (bool & ctrl_flag)) ->
    (rw:unit -> Tac unit) ->
    Tac unit

(** Given the current goal [Gamma |- w : t],
[dup] will turn this goal into
[Gamma |- ?u : t] and
[Gamma |= ?u == w]. It can thus be used to change
a goal's witness in any way needed, by choosing
some [?u] (possibly with exact) and then solving the other goal.
*)
val dup : unit -> Tac unit

// Proof namespace management
(** [prune "A.B.C"] will mark all top-level definitions in module
[A.B.C] (and submodules of it) to not be encoded to the SMT, for the current goal.
The string is a namespace prefix. [prune ""] will prune everything, but note
that [prune "FStar.S"] will not prune ["FStar.Set"]. *)
val prune : string -> Tac unit

(** The opposite operation of [prune]. The latest one takes precedence. *)
val addns : string -> Tac unit

(** Destruct a value of an inductive type by matching on it. The generated
match has one branch for each constructor and is therefore trivially
exhaustive, no VC is generated for that purpose. It returns a list
with the fvars of each constructor and their arities, in the order
they appear as goals. *)
val t_destruct : term -> Tac (list (fv & nat))

(** Set command line options for the current goal. Mostly useful to
change SMT encoding options such as [set_options "--z3rlimit 20"]. *)
val set_options : string -> Tac unit

(** Creates a new, unconstrained unification variable in environment
[env]. The type of the uvar can optionally be provided in [o]. If not
provided, a second uvar is created for the type. *)
val uvar_env : env -> option typ -> Tac term

(** Creates a new, unconstrained unification variable in environment
[env]. The type of the uvar must be provided and the uvar can be solved
to a Ghost term of that type *)
val ghost_uvar_env : env -> typ -> Tac term

(** Creates a new, unconstrained universe unification variable.
The returned term is Type (U_Unif ?u). *)
val fresh_universe_uvar : unit -> Tac term

(** Call the unifier on two terms. The returned boolean specifies
whether unification was possible. When the tactic returns true, the
terms have been unified, instantiating uvars as needed. When false,
unification was not possible and no change to uvars occurs. *)
val unify_env : env -> t1:term -> t2:term -> Tac bool

(** Similar to [unify_env], but allows for some guards to be raised
during unification (see [t_trefl] for an explanation). Will add a new
goal with the guard. *)
val unify_guard_env : env -> t1:term -> t2:term -> Tac bool

(** Check if [t1] matches [t2], i.e., whether [t2] can have its uvars
instantiated into unifying with [t1]. When the tactic returns true, the
terms have been unified, instantiating uvars as needed. When false,
matching was not possible and no change to uvars occurs. *)
val match_env : env -> t1:term -> t2:term -> Tac bool

(** Launches an external process [prog] with arguments [args] and input
[input] and returns the output. For security reasons, this can only be
performed when the `--unsafe_tactic_exec` options was provided for the
current F* invocation. The tactic will fail if this is not so. *)
val launch_process : string -> list string -> string -> Tac string

(** Get a fresh bv of some name and type. The name is only useful
for pretty-printing, since there is a fresh inaccessible integer within
the bv too. *)
val fresh_bv_named : string -> Tac bv

(** Change the goal to another type, given that it is convertible
to the current type. *)
val change : typ -> Tac unit

(** Get the current guard policy. The guard policy specifies what should
be done when a VC arises internally from the tactic engine. Options
are SMT (mark it as an SMT goal), Goal (add it as an extra goal)
and Force (only allow trivial guards, that need no SMT. *)
val get_guard_policy : unit -> Tac guard_policy

(** Set the current guard policy. See [get_guard_policy} for an explanation *)
val set_guard_policy : guard_policy -> Tac unit

(** [lax_on] returns true iff the current environment has the
`--admit_smt_queries true` option set, and thus drops all verification conditions. *)
val lax_on : unit -> Tac bool

(** Admit the current goal and set the witness to the given term.
Absolutely unsafe. Raises a warning. *)
val tadmit_t : term -> Tac unit

(** View a term in a fully-named representation *)
[@@coercion]
val inspect : term -> Tac term_view

(** Pack a term view on a fully-named representation back into a term.
Note: calling this with Tv_Unsupp will raise an exception. *)
[@@coercion]
val pack    : term_view -> Tac term

(** Similar to [pack] above, but does not flatten arrows, it leaves
    then in a curried form instead *)
val pack_curried : term_view -> Tac term

(** Join the first two goals, which must be irrelevant, in a single
one by finding a maximal prefix of their environment and reverting
appropriately. Useful to minimize SMT queries that share internal
obligations. *)
val join : unit -> Tac unit

(* Local metastate via a string-keyed map. [lget] fails if the
found element is not typeable at the requested type. *)
val lget     : #a:Type -> string -> Tac a
val lset     : #a:Type -> string -> a -> Tac unit

(** Set the current set of active goals at will. Obligations remain
in the implicits. *)
val set_goals     : list goal -> Tac unit

(** Set the current set of SMT goals at will. Obligations remain in the
implicits. TODO: This is a really bad name, there's no special "SMT"
about these goals. *)
val set_smt_goals : list goal -> Tac unit

(** [curms ()] returns the current (wall) time in milliseconds *)
val curms : unit -> Tac int

(** [set_urgency u] sets the urgency of error messages. Usually set just
before raising an exception (see e.g. [fail_silently]). *)
val set_urgency : int -> TacS unit

(** [string_to_term e s] runs the F* parser on the string [s] in the
environment [e], and produces a term. *)
val string_to_term : env -> string -> Tac term

(** [push_bv_dsenv e id] pushes a identifier [id] into the parsing
environment of [e] an environment. It returns a new environment that
has the identifier [id] along with its corresponding bounded
variable. *)
val push_bv_dsenv : env -> string -> Tac (env & bv)

(** Print a term via the pretty printer. This is considered effectful
since 1) setting options can change the behavior of this function, and
hence is not really pure; and 2) this function could expose details of
the term representation that do not show up in the view, invalidating
the pack_inspect_inv/inspeck_pack_inv lemmas. *)
val term_to_string : term -> Tac string

(** Print a computation type via the pretty printer. See comment
on [term_to_string]. *)
val comp_to_string : comp -> Tac string

(** Print a source range as a string *)
val range_to_string : range -> Tac string

(** A variant of Reflection.term_eq that may inspect more underlying
details of terms. This function could distinguish two _otherwise equal
terms_, but that distinction cannot leave the Tac effect.

This is only exposed as a migration path. Please use
[Reflection.term_eq] instead. *)
[@@deprecated "Use Reflection.term_eq instead"]
val term_eq_old : term -> term -> Tac bool

(** Runs the input tactic `f` with compat pre core setting `n`.
It is an escape hatch for maintaining backward compatibility
for code that breaks with the core typechecker. *)
val with_compat_pre_core : #a:Type -> n:int -> f:(unit -> Tac a) -> Tac a

(** Get the [vconfig], including fuel, ifuel, rlimit, etc,
associated with the current goal. *)
val get_vconfig : unit -> Tac vconfig

(** Set the [vconfig], including fuel, ifuel, rlimit, etc, associated
with the current goal. This vconfig will be used if the goal is
attempted by SMT at the end of a tactic run. *)
val set_vconfig : vconfig -> Tac unit

(** Attempt to solve the current goal with SMT immediately, and fail
if it cannot be solved. The vconfig specifies fuels, limits, etc. The
current goal's vconfig is ignored in favor of this one. *)
val t_smt_sync : vconfig -> Tac unit

(** This returns the free uvars that appear in a term. This is not
a reflection primitive as it depends on the state of the UF graph. *)
val free_uvars : term -> Tac (list int)
