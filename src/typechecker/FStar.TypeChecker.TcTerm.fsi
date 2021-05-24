#light "off"
module FStar.TypeChecker.TcTerm
open FStar.Pervasives
open FStar.ST
open FStar.All
open FStar
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Util
open FStar.Ident
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.Const
open FStar.TypeChecker.Rel
open FStar.TypeChecker.Common

val level_of_type: env -> term -> typ -> universe //the term argument is for error reporting only
val tc_constant: env -> FStar.Range.range -> sconst -> typ
val tc_binders: env -> binders -> binders * env * guard_t * universes
val tc_term: env -> term -> term * lcomp * guard_t
val tc_maybe_toplevel_term: env -> term -> term * lcomp * guard_t
val tc_comp: env -> comp -> comp * universe * guard_t
val tc_pat : Env.env -> typ -> pat -> pat * list<bv> * list<term> * Env.env * term * term * guard_t * bool
val typeof_tot_or_gtot_term: env -> term -> must_tot:bool -> term * typ * guard_t
val universe_of: env -> term -> universe
val typeof_tot_or_gtot_term_fastpath: env -> term -> Env.must_tot -> option<typ>

val tc_tot_or_gtot_term: env -> term -> term * lcomp * guard_t
//the last string argument is the reason to be printed in the error message
//pass "" if NA
val tc_check_tot_or_gtot_term: env -> term -> typ -> string -> term * lcomp * guard_t
val tc_tactic : typ -> typ -> env -> term -> term * lcomp * guard_t
val tc_trivial_guard: env -> term -> term * lcomp
val tc_check_trivial_guard: env -> term -> term -> term

val value_check_expected_typ: env -> term -> either<typ,lcomp> -> guard_t -> term * lcomp * guard_t
val check_expected_effect: env -> option<comp> -> (term * comp) -> term * comp * guard_t
val comp_check_expected_typ: env -> term -> lcomp -> term * lcomp * guard_t

val tc_tparams: env_t -> binders -> (binders * Env.env * universes)
