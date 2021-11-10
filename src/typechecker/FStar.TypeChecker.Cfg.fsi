#light "off"
module FStar.TypeChecker.Cfg
open FStar.Compiler.Effect
open FStar.Compiler.Effect
open FStar open FStar.Compiler
open FStar.Compiler.Util
open FStar.String
open FStar.Const
open FStar.Char
open FStar.Errors
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.TypeChecker
open FStar.TypeChecker.Env

module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module BU = FStar.Compiler.Util
module FC = FStar.Const
module PC = FStar.Parser.Const
module U  = FStar.Syntax.Util
module I  = FStar.Ident
module EMB = FStar.Syntax.Embeddings
module Z = FStar.BigInt
module NBE = FStar.TypeChecker.NBETerm

type fsteps = {
     beta : bool;
     iota : bool;
     zeta : bool;
     zeta_full : bool;
     weak : bool;
     hnf  : bool;
     primops : bool;
     do_not_unfold_pure_lets : bool;
     unfold_until : option<S.delta_depth>;
     unfold_only  : option<list<I.lid>>;
     unfold_fully : option<list<I.lid>>;
     unfold_attr  : option<list<I.lid>>;
     unfold_qual  : option<list<string>>;
     unfold_tac : bool;
     pure_subterms_within_computations : bool;
     simplify : bool;
     erase_universes : bool;
     allow_unbound_universes : bool;
     reify_ : bool; // fun fact: calling it 'reify' won't bootstrap :)
     compress_uvars : bool;
     no_full_norm : bool;
     check_no_uvars : bool;
     unmeta : bool;
     unascribe : bool;
     in_full_norm_request: bool;
     weakly_reduce_scrutinee:bool;
     nbe_step:bool;
     for_extraction:bool;
}

val default_steps : fsteps
val fstep_add_one : step -> fsteps -> fsteps
val to_fsteps : list<step> -> fsteps

type psc = {
     psc_range:FStar.Compiler.Range.range;
     psc_subst: unit -> subst_t // potentially expensive, so thunked
}

val null_psc : psc
val psc_range : psc -> FStar.Compiler.Range.range
val psc_subst : psc -> subst_t

type primitive_step = {
    name:FStar.Ident.lid;
    arity:int;
    univ_arity:int; // universe arity
    auto_reflect:option<int>;
    strong_reduction_ok:bool;
    requires_binder_substitution:bool;
    interpretation:(psc -> FStar.Syntax.Embeddings.norm_cb -> args -> option<term>);
    interpretation_nbe:(NBE.nbe_cbs -> NBE.args -> option<NBE.t>)
}

type debug_switches = {
    gen              : bool;
    top              : bool;
    cfg              : bool;
    primop           : bool;
    unfolding        : bool;
    b380             : bool;
    wpe              : bool;
    norm_delayed     : bool;
    print_normalized : bool;
    debug_nbe        : bool;
    erase_erasable_args: bool;
}

type cfg = {
     steps: fsteps;
     tcenv: Env.env;
     debug: debug_switches;
     delta_level: list<Env.delta_level>;  // Controls how much unfolding of definitions should be performed
     primitive_steps:BU.psmap<primitive_step>;
     strong : bool;                       // under a binder
     memoize_lazy : bool;
     normalize_pure_lets: bool;
     reifying : bool;
}

(* Profiling primitive operators *)
val primop_time_reset : unit -> unit
val primop_time_count : string -> int -> unit
val primop_time_report : unit -> string

val cfg_env: cfg -> Env.env

val cfg_to_string : cfg -> string

val log : cfg -> (unit -> unit) -> unit
val log_top : cfg -> (unit -> unit) -> unit
val log_cfg : cfg -> (unit -> unit) -> unit
val log_primops : cfg -> (unit -> unit) -> unit
val log_unfolding : cfg -> (unit -> unit) -> unit
val log_nbe : cfg -> (unit -> unit) -> unit

val is_prim_step: cfg -> fv -> bool
val find_prim_step: cfg -> fv -> option<primitive_step>

val embed_simple: EMB.embedding<'a> -> Range.range -> 'a -> term
val try_unembed_simple: EMB.embedding<'a> -> term -> option<'a>
val built_in_primitive_steps : BU.psmap<primitive_step>
val equality_ops : BU.psmap<primitive_step>

val register_plugin: primitive_step -> unit
val register_extra_step: primitive_step -> unit

val config': list<primitive_step> -> list<step> -> Env.env -> cfg
val config: list<step> -> Env.env -> cfg

val should_reduce_local_let : cfg -> letbinding -> bool

val translate_norm_steps: list<EMB.norm_step> -> list<Env.step>
