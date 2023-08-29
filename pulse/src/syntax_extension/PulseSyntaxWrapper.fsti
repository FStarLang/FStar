module PulseSyntaxWrapper
open FStar.Ident
let range = FStar.Compiler.Range.range
let var = nat
let index = nat

val universe: Type0
val u_zero : universe
val u_succ (u:universe) : universe
val u_var (s:string) : universe
val u_max (u0 u1:universe) : universe
val u_unknown : universe

new val bv : Type0
val mk_bv (i:index) (name:string) (r:range) : bv

new val nm : Type0
val mk_nm (i:index) (name:string) (r:range) : nm

new val fv : Type0
val mk_fv (nm:lident) (r:range) : fv

new val qualifier : Type0
val as_qual (imp:bool) : option qualifier
new val term : Type0
new val binder : Type0
new val comp : Type0
let vprop = term
val mk_binder (x:ident) (t:term) : binder

val tm_bvar (bv:bv) : term
val tm_var (x:nm) : term
val tm_fvar (x:fv) : term
val tm_uinst (l:fv) (us:list universe) : term
val tm_emp (_:range) : term
val tm_pure (p:term) (_:range) : term
val tm_star (p0 p1:term) (_:range) : term
val tm_exists (b:binder) (body:vprop) (_:range)  : term
val tm_arrow (b:binder) (q:FStar.Syntax.Syntax.aqual) (body:comp) (_:range)  : term
val tm_expr (t:FStar.Syntax.Syntax.term) (_:range) : term
val tm_unknown (_:range)  : term
val tm_emp_inames : term 
val mk_tot (t:term) : comp
val mk_comp (pre:term) (ret:binder) (post:term) : comp
val ghost_comp (inames:term) (pre:term) (ret:binder) (post:term) : comp
val atomic_comp (inames:term) (pre:term) (ret:binder) (post:term) : comp

new val constant : Type0
val inspect_const : FStar.Const.sconst -> constant

new val pattern : Type0
val pat_var (ppname:string) (_:range) : pattern
val pat_constant (c:constant) (_:range) : pattern
val pat_cons (head:fv) (ps:list pattern) (_:range) : pattern

new val st_term : Type0
type branch = pattern & st_term
val tm_return (t:term) (_:range) : st_term
val tm_ghost_return (t:term) (_:range) : st_term
val tm_abs (b:binder) (q:option qualifier) (_:comp) (body:st_term) (_:range) : st_term
val tm_st_app (head:term) (q:FStar.Syntax.Syntax.aqual) (arg:term) (_:range) : st_term
val tm_bind (x:binder) (e1:st_term) (e2:st_term) (_:range) : st_term
val tm_totbind (x:binder) (e1:term) (e2:st_term) (_:range) : st_term
val tm_let_mut (x:binder) (v:term) (k:st_term) (_:range) : st_term
val tm_while (head:st_term) (invariant: (ident & vprop)) (body:st_term) (_:range) : st_term 
val tm_if (head:term) (returns_annot:option vprop) (then_ else_:st_term) (_:range) : st_term
val tm_match (head:term) (returns_:option vprop) (brs:list branch) (_:range) : st_term
val tm_intro_exists (vp:vprop) (witnesses:list term) (_:range) : st_term
val is_tm_intro_exists (x:st_term) : bool
val tm_protect (s:st_term) : st_term
val tm_par (p1:term) (p2:term) (q1:term) (q2:term) (b1:st_term) (b2:st_term) (_:range) : st_term
val tm_rewrite (p1:term) (p2:term) (_:range) : st_term
val tm_rename (pairs:list (term & term)) (_:range) : st_term
val tm_admit (_:range) : st_term
val tm_proof_hint_with_binders (_:PulseSugar.hint_type) (_:list binder) (t:term) (body:st_term) (_:range) : st_term
val close_binders (bs:list binder) (xs:list var) : list binder
val close_term (t:term) (v:var) : term
val close_st_term (t:st_term) (v:var) : st_term
val close_st_term_n (t:st_term) (vs:list var) : st_term
val close_comp (t:comp) (v:var) : comp
val comp_pre (c:comp) : term
val comp_res (c:comp) : term
val comp_post (c:comp) : term

val print_exn (e:exn) : string
val binder_to_string (env:FStar.TypeChecker.Env.env) (b:binder) : string
val term_to_string (env:FStar.TypeChecker.Env.env) (_:term) : string
val st_term_to_string (env:FStar.TypeChecker.Env.env) (_:st_term) : string
val comp_to_string (env:FStar.TypeChecker.Env.env) (_:comp) : string

val subst : Type0
val bvs_as_subst (l:list var) : subst
val subst_term (s:subst) (t:term) : term
val subst_st_term (s:subst) (t:st_term) : st_term
