#light "off"
module FStar.Tactics.Basic

open FStar.Tactics.Types
open FStar.Tactics.Result
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env

module EMB = FStar.Syntax.Embeddings
module Z = FStar.BigInt

type goal = FStar.Tactics.Types.goal

type tac<'a>

val run : tac<'a> -> proofstate -> __result<'a>
val ret : 'a -> tac<'a>
val set : proofstate -> tac<unit>
val get : tac<proofstate>
val bind : tac<'a> -> ('a -> tac<'b>) -> tac<'b>

val get_guard_policy : tac<guard_policy>
val set_guard_policy : guard_policy -> tac<unit>

// Not very uniform....
val log : proofstate -> (unit -> unit) -> unit
val tacprint  : string -> unit
val tacprint1 : string -> string -> unit
val tacprint2 : string -> string -> string -> unit
val tacprint3 : string -> string -> string -> string -> unit
val dump_proofstate : proofstate -> string -> unit
val print_proof_state1 : string -> tac<unit>
val print_proof_state  : string -> tac<unit>
val goal_to_string : goal -> string

val fail : string -> tac<'a>
val trivial : tac<unit>
val smt : tac<unit>
val divide : Z.t -> tac<'a> -> tac<'b> -> tac<('a * 'b)>
val focus : tac<'a> -> tac<'a>
val trytac : tac<'a> -> tac<option<'a>>
val seq : tac<unit> -> tac<unit> -> tac<unit>
val intro : tac<binder>
val intro_rec : tac<(binder * binder)>
val norm : list<EMB.norm_step> -> tac<unit>
val norm_term_env : env -> list<EMB.norm_step> -> term -> tac<term>
val refine_intro : tac<unit>
val t_exact : bool -> term -> tac<unit>
val apply : bool -> term -> tac<unit>
val apply_lemma : term -> tac<unit>
val rewrite : binder -> tac<unit>
val rename_to : binder -> string -> tac<unit>
val binder_retype : binder -> tac<unit>
val norm_binder_type : list<EMB.norm_step> -> binder -> tac<unit>
val revert : tac<unit>
val clear : binder -> tac<unit>
val clear_top : tac<unit>
val tc : term -> tac<typ>
val is_guard : tac<bool>

val is_irrelevant : goal -> bool

val prune : string -> tac<unit>
val addns : string -> tac<unit>
val set_options : string -> tac<unit>
val launch_process : string -> string -> string -> tac<string>

val fresh_bv_named : string -> typ -> tac<bv>

val pointwise : direction -> tac<unit> -> tac<unit>
val topdown_rewrite: (term -> tac<(bool * FStar.BigInt.t)>) -> tac<unit> -> tac<unit>
val trefl : tac<unit>

val dup     : tac<unit>
val flip    : tac<unit>
val later   : tac<unit>
val dismiss : tac<unit>
val qed     : tac<unit>

val cases : term -> tac<(term * term)>

val top_env : tac<env>
val cur_env : tac<env>
val cur_goal' : tac<term>
val cur_witness : tac<term>

val unquote : typ -> term -> tac<term>
val uvar_env : env -> option<typ> -> tac<term>
val unshelve : term -> tac<unit>

val unify : term -> term -> tac<bool>
val change : typ -> tac<unit>

val goal_of_goal_ty : env -> typ -> goal * guard_t
val proofstate_of_goal_ty : env -> typ -> proofstate * term (* Returns proofstate and uvar for main witness *)
