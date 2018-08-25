#light "off"
module FStar.TypeChecker.TcTerm
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

val tc_constant: env -> FStar.Range.range -> sconst -> typ
val tc_binders: env -> binders -> binders * env * guard_t * universes
val tc_term: env -> term -> term * lcomp * guard_t
val tc_maybe_toplevel_term: env -> term -> term * lcomp * guard_t
val tc_comp: env -> comp -> comp * universe * guard_t
val tc_pat : Env.env -> typ -> pat -> pat * list<bv> * Env.env * term * term * guard_t
val type_of_tot_term: env -> term -> term * typ * guard_t
val universe_of: env -> term -> universe

val check_type_of_well_typed_term: bool -> env -> term -> typ -> guard_t  // guarded by --__temp_fast_implicits
val check_type_of_well_typed_term': bool -> env -> term -> typ -> guard_t // always fast

val tc_tot_or_gtot_term: env -> term -> term * lcomp * guard_t
val tc_check_tot_or_gtot_term: env -> term -> typ -> term * lcomp * guard_t
val tc_tactic : env -> term -> term * lcomp * guard_t
val tc_trivial_guard: env -> term -> term * lcomp

val value_check_expected_typ: env -> term -> either<typ,lcomp> -> guard_t -> term * lcomp * guard_t
val check_expected_effect: env -> option<comp> -> (term * comp) -> term * comp * guard_t
val comp_check_expected_typ: env -> term -> lcomp -> term * lcomp * guard_t

val tc_tparams: env_t -> binders -> (binders * Env.env * universes)
