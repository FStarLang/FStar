#light "off"
module FStar.Tactics.Basic

open FStar.TypeChecker.Env
open FStar.Tactics.Types
open FStar.Tactics.Result
open FStar.Syntax.Syntax

open FStar.Reflection.Data
module Range = FStar.Range
module EMB = FStar.Syntax.Embeddings
module Z = FStar.BigInt
module BU = FStar.Util

type tac<'a>

val run      : tac<'a> -> proofstate -> __result<'a>
val run_safe : tac<'a> -> proofstate -> __result<'a> (* Won't raise any exception, just fail within the monad *)
val ret : 'a -> tac<'a>
val set : proofstate -> tac<unit>
val get : tac<proofstate>
val bind : tac<'a> -> ('a -> tac<'b>) -> tac<'b>
val traise : exn -> tac<'a>
val fail : string -> tac<'a>

val set_goals     : list<goal> -> tac<unit>
val set_smt_goals : list<goal> -> tac<unit>

val get_guard_policy : unit -> tac<guard_policy>
val set_guard_policy : guard_policy -> tac<unit>
val lax_on : unit -> tac<bool>

val fresh      : unit -> tac<Z.t>

val join    : unit -> tac<unit>

val inspect : term -> tac<term_view>
val pack    : term_view -> tac<term>

// Not very uniform....
val log : proofstate -> (unit -> unit) -> unit
val tacprint  : string -> unit
val tacprint1 : string -> string -> unit
val tacprint2 : string -> string -> string -> unit
val tacprint3 : string -> string -> string -> string -> unit
val print     : string -> tac<unit>
val dump_proofstate : proofstate -> string -> unit
val print_proof_state  : string -> tac<unit>
val debugging : unit -> tac<bool>

val trivial : unit -> tac<unit>
val divide : Z.t -> tac<'a> -> tac<'b> -> tac<('a * 'b)>
val seq : tac<unit> -> tac<unit> -> tac<unit>
val focus : tac<'a> -> tac<'a>
val catch : tac<'a> -> tac<BU.either<exn,'a>>
val recover : tac<'a> -> tac<BU.either<exn,'a>>
val intro : unit -> tac<binder>
val intro_rec : unit -> tac<(binder * binder)>
val norm : list<EMB.norm_step> -> tac<unit>
val norm_term_env : env -> list<EMB.norm_step> -> term -> tac<term>
val refine_intro : unit -> tac<unit>
val t_exact : bool -> bool -> term -> tac<unit>
val t_apply : bool -> term -> tac<unit>
val apply_lemma : term -> tac<unit>
val rewrite : binder -> tac<unit>
val rename_to : binder -> string -> tac<unit>
val binder_retype : binder -> tac<unit>
val norm_binder_type : list<EMB.norm_step> -> binder -> tac<unit>
val revert : unit -> tac<unit>
val clear : binder -> tac<unit>
val clear_top : unit -> tac<unit>
val tc : term -> tac<typ>

val is_irrelevant : goal -> bool

val prune : string -> tac<unit>
val addns : string -> tac<unit>
val set_options : string -> tac<unit>
val launch_process : string -> list<string> -> string -> tac<string>

val fresh_bv_named : string -> typ -> tac<bv>

val pointwise : direction -> tac<unit> -> tac<unit>
val topdown_rewrite: (term -> tac<(bool * FStar.BigInt.t)>) -> tac<unit> -> tac<unit>
val trefl : unit -> tac<unit>

val dup      : unit -> tac<unit>
val tadmit_t : term -> tac<unit>

val t_destruct : term -> tac<list<(fv * Z.t)>>

val top_env : unit -> tac<env>

val unquote : typ -> term -> tac<term>
val uvar_env : env -> option<typ> -> tac<term>
val unshelve : term -> tac<unit>

val unify_env : env -> term -> term -> tac<bool>
val change : typ -> tac<unit>

val lget : typ -> string -> tac<term>
val lset : typ -> string -> term -> tac<unit>

val goal_of_goal_ty : env -> typ -> goal * guard_t
(* Returns proofstate and uvar for main witness *)
val proofstate_of_goal_ty : Range.range -> env -> typ -> proofstate * term
