
let new_kvar = (fun ( r ) ( binders ) -> (let wf = (fun ( k ) ( _33_39 ) -> (match (()) with
| () -> begin
true
end))
in (let u = (Support.Microsoft.FStar.Unionfind.fresh Microsoft_FStar_Absyn_Syntax.Uvar)
in (let _68_12883 = (let _68_12882 = (let _68_12881 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (u, _68_12881))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar _68_12882 r))
in (_68_12883, u)))))

let new_tvar = (fun ( r ) ( binders ) ( k ) -> (let wf = (fun ( t ) ( tk ) -> true)
in (let binders = (Support.Prims.pipe_right binders (Support.List.filter (fun ( x ) -> (let _68_12895 = (Microsoft_FStar_Absyn_Syntax.is_null_binder x)
in (Support.Prims.pipe_right _68_12895 Support.Prims.op_Negation)))))
in (let uv = (Support.Microsoft.FStar.Unionfind.fresh Microsoft_FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (Microsoft_FStar_Absyn_Syntax.mk_Typ_uvar' (uv, k) None r)
in (uv, uv))
end
| _ -> begin
(let args = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (let k' = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (binders, k) r)
in (let uv = (Microsoft_FStar_Absyn_Syntax.mk_Typ_uvar' (uv, k') None r)
in (let _68_12896 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (uv, args) None r)
in (_68_12896, uv)))))
end)))))

let new_evar = (fun ( r ) ( binders ) ( t ) -> (let wf = (fun ( e ) ( t ) -> true)
in (let binders = (Support.Prims.pipe_right binders (Support.List.filter (fun ( x ) -> (let _68_12908 = (Microsoft_FStar_Absyn_Syntax.is_null_binder x)
in (Support.Prims.pipe_right _68_12908 Support.Prims.op_Negation)))))
in (let uv = (Support.Microsoft.FStar.Unionfind.fresh Microsoft_FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (Microsoft_FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t) None r)
in (uv, uv))
end
| _ -> begin
(let args = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (let t' = (let _68_12910 = (let _68_12909 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (binders, _68_12909))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _68_12910 None r))
in (let uv = (Microsoft_FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t') None r)
in (match (args) with
| [] -> begin
(uv, uv)
end
| _ -> begin
(let _68_12911 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (uv, args) None r)
in (_68_12911, uv))
end))))
end)))))

type rel =
| EQ
| SUB
| SUBINV

let is_EQ = (fun ( _discr_ ) -> (match (_discr_) with
| EQ -> begin
true
end
| _ -> begin
false
end))

let is_SUB = (fun ( _discr_ ) -> (match (_discr_) with
| SUB -> begin
true
end
| _ -> begin
false
end))

let is_SUBINV = (fun ( _discr_ ) -> (match (_discr_) with
| SUBINV -> begin
true
end
| _ -> begin
false
end))

type variance =
| COVARIANT
| CONTRAVARIANT
| INVARIANT

let is_COVARIANT = (fun ( _discr_ ) -> (match (_discr_) with
| COVARIANT -> begin
true
end
| _ -> begin
false
end))

let is_CONTRAVARIANT = (fun ( _discr_ ) -> (match (_discr_) with
| CONTRAVARIANT -> begin
true
end
| _ -> begin
false
end))

let is_INVARIANT = (fun ( _discr_ ) -> (match (_discr_) with
| INVARIANT -> begin
true
end
| _ -> begin
false
end))

type ('a, 'b) problem =
{lhs : 'a; relation : rel; rhs : 'a; element : 'b option; logical_guard : (Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.typ); scope : Microsoft_FStar_Absyn_Syntax.binders; reason : string list; loc : Support.Microsoft.FStar.Range.range; rank : int option}

let is_Mkproblem = (fun ( _ ) -> (failwith ("Not yet implemented:is_Mkproblem")))

type ('a, 'b) problem_t =
('a, 'b) problem

type prob =
| KProb of (Microsoft_FStar_Absyn_Syntax.knd, unit) problem
| TProb of (Microsoft_FStar_Absyn_Syntax.typ, Microsoft_FStar_Absyn_Syntax.exp) problem
| EProb of (Microsoft_FStar_Absyn_Syntax.exp, unit) problem
| CProb of (Microsoft_FStar_Absyn_Syntax.comp, unit) problem

let is_KProb = (fun ( _discr_ ) -> (match (_discr_) with
| KProb (_) -> begin
true
end
| _ -> begin
false
end))

let is_TProb = (fun ( _discr_ ) -> (match (_discr_) with
| TProb (_) -> begin
true
end
| _ -> begin
false
end))

let is_EProb = (fun ( _discr_ ) -> (match (_discr_) with
| EProb (_) -> begin
true
end
| _ -> begin
false
end))

let is_CProb = (fun ( _discr_ ) -> (match (_discr_) with
| CProb (_) -> begin
true
end
| _ -> begin
false
end))

type probs =
prob list

type uvi =
| UK of (Microsoft_FStar_Absyn_Syntax.uvar_k * Microsoft_FStar_Absyn_Syntax.knd)
| UT of ((Microsoft_FStar_Absyn_Syntax.uvar_t * Microsoft_FStar_Absyn_Syntax.knd) * Microsoft_FStar_Absyn_Syntax.typ)
| UE of ((Microsoft_FStar_Absyn_Syntax.uvar_e * Microsoft_FStar_Absyn_Syntax.typ) * Microsoft_FStar_Absyn_Syntax.exp)

let is_UK = (fun ( _discr_ ) -> (match (_discr_) with
| UK (_) -> begin
true
end
| _ -> begin
false
end))

let is_UT = (fun ( _discr_ ) -> (match (_discr_) with
| UT (_) -> begin
true
end
| _ -> begin
false
end))

let is_UE = (fun ( _discr_ ) -> (match (_discr_) with
| UE (_) -> begin
true
end
| _ -> begin
false
end))

type worklist =
{attempting : probs; deferred : (int * string * prob) list; subst : uvi list; ctr : int; slack_vars : (bool * Microsoft_FStar_Absyn_Syntax.typ) list; defer_ok : bool; smt_ok : bool; tcenv : Microsoft_FStar_Tc_Env.env}

let is_Mkworklist = (fun ( _ ) -> (failwith ("Not yet implemented:is_Mkworklist")))

type deferred =
{carry : (string * prob) list; slack : (bool * Microsoft_FStar_Absyn_Syntax.typ) list}

let is_Mkdeferred = (fun ( _ ) -> (failwith ("Not yet implemented:is_Mkdeferred")))

let no_deferred = {carry = []; slack = []}

type solution =
| Success of (uvi list * deferred)
| Failed of (prob * string)

let is_Success = (fun ( _discr_ ) -> (match (_discr_) with
| Success (_) -> begin
true
end
| _ -> begin
false
end))

let is_Failed = (fun ( _discr_ ) -> (match (_discr_) with
| Failed (_) -> begin
true
end
| _ -> begin
false
end))

let rel_to_string = (fun ( _33_1 ) -> (match (_33_1) with
| EQ -> begin
"="
end
| SUB -> begin
"<:"
end
| SUBINV -> begin
":>"
end))

let prob_to_string = (fun ( env ) ( _33_2 ) -> (match (_33_2) with
| KProb (p) -> begin
(let _68_13050 = (Microsoft_FStar_Absyn_Print.kind_to_string p.lhs)
in (let _68_13049 = (Microsoft_FStar_Absyn_Print.kind_to_string p.rhs)
in (Support.Microsoft.FStar.Util.format3 "\t%s\n\t\t%s\n\t%s" _68_13050 (rel_to_string p.relation) _68_13049)))
end
| TProb (p) -> begin
(let _68_13063 = (let _68_13062 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env p.lhs)
in (let _68_13061 = (let _68_13060 = (Microsoft_FStar_Absyn_Print.tag_of_typ p.lhs)
in (let _68_13059 = (let _68_13058 = (let _68_13057 = (Support.Prims.pipe_right p.reason Support.List.hd)
in (let _68_13056 = (let _68_13055 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env p.rhs)
in (let _68_13054 = (let _68_13053 = (Microsoft_FStar_Absyn_Print.tag_of_typ p.rhs)
in (let _68_13052 = (let _68_13051 = (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env (Support.Prims.fst p.logical_guard))
in (_68_13051)::[])
in (_68_13053)::_68_13052))
in (_68_13055)::_68_13054))
in (_68_13057)::_68_13056))
in ((rel_to_string p.relation))::_68_13058)
in (_68_13060)::_68_13059))
in (_68_13062)::_68_13061))
in (Support.Microsoft.FStar.Util.format "\t%s (%s) \n\t\t%s(%s)\n\t%s (%s) (guard %s)" _68_13063))
end
| EProb (p) -> begin
(let _68_13065 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env p.lhs)
in (let _68_13064 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env p.rhs)
in (Support.Microsoft.FStar.Util.format3 "\t%s \n\t\t%s\n\t%s" _68_13065 (rel_to_string p.relation) _68_13064)))
end
| CProb (p) -> begin
(let _68_13067 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env p.lhs)
in (let _68_13066 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env p.rhs)
in (Support.Microsoft.FStar.Util.format3 "\t%s \n\t\t%s\n\t%s" _68_13067 (rel_to_string p.relation) _68_13066)))
end))

let uvi_to_string = (fun ( env ) ( uvi ) -> (let str = (fun ( u ) -> (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _68_13073 = (Support.Microsoft.FStar.Unionfind.uvar_id u)
in (Support.Prims.pipe_right _68_13073 Support.Microsoft.FStar.Util.string_of_int))
end))
in (match (uvi) with
| UK ((u, _)) -> begin
(let _68_13074 = (str u)
in (Support.Prims.pipe_right _68_13074 (Support.Microsoft.FStar.Util.format1 "UK %s")))
end
| UT (((u, _), t)) -> begin
(let _68_13077 = (str u)
in (Support.Prims.pipe_right _68_13077 (fun ( x ) -> (let _68_13076 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.format2 "UT %s %s" x _68_13076)))))
end
| UE (((u, _), _)) -> begin
(let _68_13078 = (str u)
in (Support.Prims.pipe_right _68_13078 (Support.Microsoft.FStar.Util.format1 "UE %s")))
end)))

let invert_rel = (fun ( _33_3 ) -> (match (_33_3) with
| EQ -> begin
EQ
end
| SUB -> begin
SUBINV
end
| SUBINV -> begin
SUB
end))

let invert = (fun ( p ) -> (let _33_165 = p
in {lhs = p.rhs; relation = (invert_rel p.relation); rhs = p.lhs; element = _33_165.element; logical_guard = _33_165.logical_guard; scope = _33_165.scope; reason = _33_165.reason; loc = _33_165.loc; rank = _33_165.rank}))

let maybe_invert = (fun ( p ) -> (match ((p.relation = SUBINV)) with
| true -> begin
(invert p)
end
| false -> begin
p
end))

let maybe_invert_p = (fun ( _33_4 ) -> (match (_33_4) with
| KProb (p) -> begin
(Support.Prims.pipe_right (maybe_invert p) (fun ( _68_13085 ) -> KProb (_68_13085)))
end
| TProb (p) -> begin
(Support.Prims.pipe_right (maybe_invert p) (fun ( _68_13086 ) -> TProb (_68_13086)))
end
| EProb (p) -> begin
(Support.Prims.pipe_right (maybe_invert p) (fun ( _68_13087 ) -> EProb (_68_13087)))
end
| CProb (p) -> begin
(Support.Prims.pipe_right (maybe_invert p) (fun ( _68_13088 ) -> CProb (_68_13088)))
end))

let vary_rel = (fun ( rel ) ( _33_5 ) -> (match (_33_5) with
| INVARIANT -> begin
EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))

let p_rel = (fun ( _33_6 ) -> (match (_33_6) with
| KProb (p) -> begin
p.relation
end
| TProb (p) -> begin
p.relation
end
| EProb (p) -> begin
p.relation
end
| CProb (p) -> begin
p.relation
end))

let p_reason = (fun ( _33_7 ) -> (match (_33_7) with
| KProb (p) -> begin
p.reason
end
| TProb (p) -> begin
p.reason
end
| EProb (p) -> begin
p.reason
end
| CProb (p) -> begin
p.reason
end))

let p_loc = (fun ( _33_8 ) -> (match (_33_8) with
| KProb (p) -> begin
p.loc
end
| TProb (p) -> begin
p.loc
end
| EProb (p) -> begin
p.loc
end
| CProb (p) -> begin
p.loc
end))

let p_context = (fun ( _33_9 ) -> (match (_33_9) with
| KProb (p) -> begin
p.scope
end
| TProb (p) -> begin
p.scope
end
| EProb (p) -> begin
p.scope
end
| CProb (p) -> begin
p.scope
end))

let p_guard = (fun ( _33_10 ) -> (match (_33_10) with
| KProb (p) -> begin
p.logical_guard
end
| TProb (p) -> begin
p.logical_guard
end
| EProb (p) -> begin
p.logical_guard
end
| CProb (p) -> begin
p.logical_guard
end))

let p_scope = (fun ( _33_11 ) -> (match (_33_11) with
| KProb (p) -> begin
p.scope
end
| TProb (p) -> begin
p.scope
end
| EProb (p) -> begin
p.scope
end
| CProb (p) -> begin
p.scope
end))

let p_invert = (fun ( _33_12 ) -> (match (_33_12) with
| KProb (p) -> begin
(Support.Prims.pipe_left (fun ( _68_13107 ) -> KProb (_68_13107)) (invert p))
end
| TProb (p) -> begin
(Support.Prims.pipe_left (fun ( _68_13108 ) -> TProb (_68_13108)) (invert p))
end
| EProb (p) -> begin
(Support.Prims.pipe_left (fun ( _68_13109 ) -> EProb (_68_13109)) (invert p))
end
| CProb (p) -> begin
(Support.Prims.pipe_left (fun ( _68_13110 ) -> CProb (_68_13110)) (invert p))
end))

let is_top_level_prob = (fun ( p ) -> ((Support.Prims.pipe_right (p_reason p) Support.List.length) = 1))

let mk_problem = (fun ( scope ) ( orig ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( reason ) -> (let _68_13120 = (new_tvar (p_loc orig) scope Microsoft_FStar_Absyn_Syntax.ktype)
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _68_13120; scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None}))

let new_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) ( reason ) -> (let _68_13130 = (let _68_13129 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_13128 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _68_13129 _68_13128 Microsoft_FStar_Absyn_Syntax.ktype)))
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _68_13130; scope = []; reason = (reason)::[]; loc = loc; rank = None}))

let problem_using_guard = (fun ( orig ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( reason ) -> {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = (p_guard orig); scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None})

let guard_on_element = (fun ( problem ) ( x ) ( phi ) -> (match (problem.element) with
| None -> begin
(let _68_13141 = (let _68_13140 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_68_13140)::[])
in (Microsoft_FStar_Absyn_Util.close_forall _68_13141 phi))
end
| Some (e) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ ((Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, e)))::[]) phi)
end))

let solve_prob' = (fun ( resolve_ok ) ( prob ) ( logical_guard ) ( uvis ) ( wl ) -> (let phi = (match (logical_guard) with
| None -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| Some (phi) -> begin
phi
end)
in (let _33_284 = (p_guard prob)
in (match (_33_284) with
| (_, uv) -> begin
(let _33_292 = (match ((let _68_13152 = (Microsoft_FStar_Absyn_Util.compress_typ uv)
in _68_13152.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uvar, k)) -> begin
(let phi = (Microsoft_FStar_Absyn_Util.close_for_kind phi k)
in (Microsoft_FStar_Absyn_Util.unchecked_unify uvar phi))
end
| _ -> begin
(match ((not (resolve_ok))) with
| true -> begin
(failwith ("Impossible: this instance has already been assigned a solution"))
end
| false -> begin
()
end)
end)
in (match (uvis) with
| [] -> begin
wl
end
| _ -> begin
(let _33_297 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug wl.tcenv) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_13154 = (let _68_13153 = (Support.List.map (uvi_to_string wl.tcenv) uvis)
in (Support.Prims.pipe_right _68_13153 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.fprint1 "Extending solution: %s\n" _68_13154))
end
| false -> begin
()
end)
in (let _33_299 = wl
in {attempting = _33_299.attempting; deferred = _33_299.deferred; subst = (Support.List.append uvis wl.subst); ctr = (wl.ctr + 1); slack_vars = _33_299.slack_vars; defer_ok = _33_299.defer_ok; smt_ok = _33_299.smt_ok; tcenv = _33_299.tcenv}))
end))
end))))

let extend_solution = (fun ( sol ) ( wl ) -> (let _33_303 = wl
in {attempting = _33_303.attempting; deferred = _33_303.deferred; subst = (sol)::wl.subst; ctr = (wl.ctr + 1); slack_vars = _33_303.slack_vars; defer_ok = _33_303.defer_ok; smt_ok = _33_303.smt_ok; tcenv = _33_303.tcenv}))

let solve_prob = (fun ( prob ) ( logical_guard ) ( uvis ) ( wl ) -> (solve_prob' false prob logical_guard uvis wl))

let explain = (fun ( env ) ( d ) ( s ) -> (let _68_13175 = (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range (p_loc d))
in (let _68_13174 = (prob_to_string env d)
in (let _68_13173 = (Support.Prims.pipe_right (p_reason d) (Support.String.concat "\n\t>"))
in (Support.Microsoft.FStar.Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _68_13175 _68_13174 _68_13173 s)))))

let empty_worklist = (fun ( env ) -> {attempting = []; deferred = []; subst = []; ctr = 0; slack_vars = []; defer_ok = true; smt_ok = true; tcenv = env})

let singleton = (fun ( env ) ( prob ) -> (let _33_315 = (empty_worklist env)
in {attempting = (prob)::[]; deferred = _33_315.deferred; subst = _33_315.subst; ctr = _33_315.ctr; slack_vars = _33_315.slack_vars; defer_ok = _33_315.defer_ok; smt_ok = _33_315.smt_ok; tcenv = _33_315.tcenv}))

let wl_of_guard = (fun ( env ) ( g ) -> (let _33_319 = (empty_worklist env)
in (let _68_13186 = (Support.List.map Support.Prims.snd g.carry)
in {attempting = _68_13186; deferred = _33_319.deferred; subst = _33_319.subst; ctr = _33_319.ctr; slack_vars = g.slack; defer_ok = false; smt_ok = _33_319.smt_ok; tcenv = _33_319.tcenv})))

let defer = (fun ( reason ) ( prob ) ( wl ) -> (let _33_324 = wl
in {attempting = _33_324.attempting; deferred = ((wl.ctr, reason, prob))::wl.deferred; subst = _33_324.subst; ctr = _33_324.ctr; slack_vars = _33_324.slack_vars; defer_ok = _33_324.defer_ok; smt_ok = _33_324.smt_ok; tcenv = _33_324.tcenv}))

let attempt = (fun ( probs ) ( wl ) -> (let _33_328 = wl
in {attempting = (Support.List.append probs wl.attempting); deferred = _33_328.deferred; subst = _33_328.subst; ctr = _33_328.ctr; slack_vars = _33_328.slack_vars; defer_ok = _33_328.defer_ok; smt_ok = _33_328.smt_ok; tcenv = _33_328.tcenv}))

let add_slack_mul = (fun ( slack ) ( wl ) -> (let _33_332 = wl
in {attempting = _33_332.attempting; deferred = _33_332.deferred; subst = _33_332.subst; ctr = _33_332.ctr; slack_vars = ((true, slack))::wl.slack_vars; defer_ok = _33_332.defer_ok; smt_ok = _33_332.smt_ok; tcenv = _33_332.tcenv}))

let add_slack_add = (fun ( slack ) ( wl ) -> (let _33_336 = wl
in {attempting = _33_336.attempting; deferred = _33_336.deferred; subst = _33_336.subst; ctr = _33_336.ctr; slack_vars = ((false, slack))::wl.slack_vars; defer_ok = _33_336.defer_ok; smt_ok = _33_336.smt_ok; tcenv = _33_336.tcenv}))

let giveup = (fun ( env ) ( reason ) ( prob ) -> (let _33_341 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_13211 = (prob_to_string env prob)
in (Support.Microsoft.FStar.Util.fprint2 "Failed %s:\n%s\n" reason _68_13211))
end
| false -> begin
()
end)
in Failed ((prob, reason))))

let commit = (fun ( env ) ( uvis ) -> (Support.Prims.pipe_right uvis (Support.List.iter (fun ( _33_13 ) -> (match (_33_13) with
| UK ((u, k)) -> begin
(Microsoft_FStar_Absyn_Util.unchecked_unify u k)
end
| UT (((u, k), t)) -> begin
(Microsoft_FStar_Absyn_Util.unchecked_unify u t)
end
| UE (((u, _), e)) -> begin
(Microsoft_FStar_Absyn_Util.unchecked_unify u e)
end)))))

let find_uvar_k = (fun ( uv ) ( s ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _33_14 ) -> (match (_33_14) with
| UK ((u, t)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.equivalent uv u)) with
| true -> begin
Some (t)
end
| false -> begin
None
end)
end
| _ -> begin
None
end))))

let find_uvar_t = (fun ( uv ) ( s ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _33_15 ) -> (match (_33_15) with
| UT (((u, _), t)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.equivalent uv u)) with
| true -> begin
Some (t)
end
| false -> begin
None
end)
end
| _ -> begin
None
end))))

let find_uvar_e = (fun ( uv ) ( s ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _33_16 ) -> (match (_33_16) with
| UE (((u, _), t)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.equivalent uv u)) with
| true -> begin
Some (t)
end
| false -> begin
None
end)
end
| _ -> begin
None
end))))

let simplify_formula = (fun ( env ) ( f ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env f))

let norm_targ = (fun ( env ) ( t ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env t))

let norm_arg = (fun ( env ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _68_13242 = (let _68_13241 = (norm_targ env t)
in (Support.Prims.pipe_left (fun ( _68_13240 ) -> Support.Microsoft.FStar.Util.Inl (_68_13240)) _68_13241))
in (_68_13242, (Support.Prims.snd a)))
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
(let _68_13245 = (let _68_13244 = (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env v)
in (Support.Prims.pipe_left (fun ( _68_13243 ) -> Support.Microsoft.FStar.Util.Inr (_68_13243)) _68_13244))
in (_68_13245, (Support.Prims.snd a)))
end))

let whnf = (fun ( env ) ( t ) -> (let _68_13250 = (Microsoft_FStar_Tc_Normalize.whnf env t)
in (Support.Prims.pipe_right _68_13250 Microsoft_FStar_Absyn_Util.compress_typ)))

let sn = (fun ( env ) ( t ) -> (let _68_13255 = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::[]) env t)
in (Support.Prims.pipe_right _68_13255 Microsoft_FStar_Absyn_Util.compress_typ)))

let sn_binders = (fun ( env ) ( binders ) -> (Support.Prims.pipe_right binders (Support.List.map (fun ( _33_17 ) -> (match (_33_17) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _68_13261 = (let _68_13260 = (let _33_417 = a
in (let _68_13259 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env a.Microsoft_FStar_Absyn_Syntax.sort)
in {Microsoft_FStar_Absyn_Syntax.v = _33_417.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _68_13259; Microsoft_FStar_Absyn_Syntax.p = _33_417.Microsoft_FStar_Absyn_Syntax.p}))
in Support.Microsoft.FStar.Util.Inl (_68_13260))
in (_68_13261, imp))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _68_13264 = (let _68_13263 = (let _33_423 = x
in (let _68_13262 = (norm_targ env x.Microsoft_FStar_Absyn_Syntax.sort)
in {Microsoft_FStar_Absyn_Syntax.v = _33_423.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _68_13262; Microsoft_FStar_Absyn_Syntax.p = _33_423.Microsoft_FStar_Absyn_Syntax.p}))
in Support.Microsoft.FStar.Util.Inr (_68_13263))
in (_68_13264, imp))
end)))))

let whnf_k = (fun ( env ) ( k ) -> (let _68_13269 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.WHNF)::[]) env k)
in (Support.Prims.pipe_right _68_13269 Microsoft_FStar_Absyn_Util.compress_kind)))

let whnf_e = (fun ( env ) ( e ) -> (let _68_13274 = (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.WHNF)::[]) env e)
in (Support.Prims.pipe_right _68_13274 Microsoft_FStar_Absyn_Util.compress_exp)))

let rec compress_k = (fun ( env ) ( wl ) ( k ) -> (let k = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, actuals)) -> begin
(match ((find_uvar_k uv wl.subst)) with
| None -> begin
k
end
| Some (k') -> begin
(match (k'.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam ((formals, body)) -> begin
(let k = (let _68_13281 = (Microsoft_FStar_Absyn_Util.subst_of_list formals actuals)
in (Microsoft_FStar_Absyn_Util.subst_kind _68_13281 body))
in (compress_k env wl k))
end
| _ -> begin
(match (((Support.List.length actuals) = 0)) with
| true -> begin
(compress_k env wl k')
end
| false -> begin
(failwith ("Wrong arity for kind unifier"))
end)
end)
end)
end
| _ -> begin
k
end)))

let rec compress = (fun ( env ) ( wl ) ( t ) -> (let t = (let _68_13288 = (Microsoft_FStar_Absyn_Util.unmeta_typ t)
in (whnf env _68_13288))
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _)) -> begin
(match ((find_uvar_t uv wl.subst)) with
| None -> begin
t
end
| Some (t) -> begin
(compress env wl t)
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) -> begin
(match ((find_uvar_t uv wl.subst)) with
| Some (t') -> begin
(let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t', args) None t.Microsoft_FStar_Absyn_Syntax.pos)
in (compress env wl t))
end
| _ -> begin
t
end)
end
| _ -> begin
t
end)))

let rec compress_e = (fun ( env ) ( wl ) ( e ) -> (let e = (Microsoft_FStar_Absyn_Util.unmeta_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, t)) -> begin
(match ((find_uvar_e uv wl.subst)) with
| None -> begin
e
end
| Some (e') -> begin
(compress_e env wl e')
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) -> begin
(match ((find_uvar_e uv wl.subst)) with
| None -> begin
e
end
| Some (e') -> begin
(let e' = (compress_e env wl e')
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e', args) None e.Microsoft_FStar_Absyn_Syntax.pos))
end)
end
| _ -> begin
e
end)))

let normalize_refinement = (fun ( env ) ( wl ) ( t0 ) -> (let _68_13301 = (compress env wl t0)
in (Microsoft_FStar_Tc_Normalize.normalize_refinement env _68_13301)))

let base_and_refinement = (fun ( env ) ( wl ) ( t1 ) -> (let rec aux = (fun ( norm ) ( t1 ) -> (match (t1.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi)) -> begin
(match (norm) with
| true -> begin
(x.Microsoft_FStar_Absyn_Syntax.sort, Some ((x, phi)))
end
| false -> begin
(match ((normalize_refinement env wl t1)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
(x.Microsoft_FStar_Absyn_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _68_13314 = (let _68_13313 = (Microsoft_FStar_Absyn_Print.typ_to_string tt)
in (let _68_13312 = (Microsoft_FStar_Absyn_Print.tag_of_typ tt)
in (Support.Microsoft.FStar.Util.format2 "impossible: Got %s ... %s\n" _68_13313 _68_13312)))
in (failwith (_68_13314)))
end)
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (_)) -> begin
(match (norm) with
| true -> begin
(t1, None)
end
| false -> begin
(let _33_554 = (let _68_13315 = (normalize_refinement env wl t1)
in (aux true _68_13315))
in (match (_33_554) with
| (t2', refinement) -> begin
(match (refinement) with
| None -> begin
(t1, None)
end
| _ -> begin
(t2', refinement)
end)
end))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
(t1, None)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _68_13318 = (let _68_13317 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _68_13316 = (Microsoft_FStar_Absyn_Print.tag_of_typ t1)
in (Support.Microsoft.FStar.Util.format2 "impossible (outer): Got %s ... %s\n" _68_13317 _68_13316)))
in (failwith (_68_13318)))
end))
in (let _68_13319 = (compress env wl t1)
in (aux false _68_13319))))

let unrefine = (fun ( env ) ( t ) -> (let _68_13324 = (base_and_refinement env (empty_worklist env) t)
in (Support.Prims.pipe_right _68_13324 Support.Prims.fst)))

let trivial_refinement = (fun ( t ) -> (let _68_13326 = (Microsoft_FStar_Absyn_Util.gen_bvar_p t.Microsoft_FStar_Absyn_Syntax.pos t)
in (_68_13326, Microsoft_FStar_Absyn_Util.t_true)))

let as_refinement = (fun ( env ) ( wl ) ( t ) -> (let _33_588 = (base_and_refinement env wl t)
in (match (_33_588) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some ((x, phi)) -> begin
(x, phi)
end)
end)))

let force_refinement = (fun ( _33_596 ) -> (match (_33_596) with
| (t_base, refopt) -> begin
(let _33_604 = (match (refopt) with
| Some ((y, phi)) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_33_604) with
| (y, phi) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (y, phi) None t_base.Microsoft_FStar_Absyn_Syntax.pos)
end))
end))

let rec occurs = (fun ( env ) ( wl ) ( uk ) ( t ) -> (let uvs = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (let _68_13346 = (Support.Prims.pipe_right uvs.Microsoft_FStar_Absyn_Syntax.uvars_t Support.Microsoft.FStar.Util.set_elements)
in (Support.Prims.pipe_right _68_13346 (Support.Microsoft.FStar.Util.for_some (fun ( _33_615 ) -> (match (_33_615) with
| (uvt, _) -> begin
(match ((find_uvar_t uvt wl.subst)) with
| None -> begin
(Support.Microsoft.FStar.Unionfind.equivalent uvt (Support.Prims.fst uk))
end
| Some (t) -> begin
(let t = (match ((Microsoft_FStar_Absyn_Util.compress_typ t)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((_, t)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
t
end
| t -> begin
t
end)
in (occurs env wl uk t))
end)
end)))))))

let occurs_check = (fun ( env ) ( wl ) ( uk ) ( t ) -> (let occurs_ok = (not ((occurs env wl uk t)))
in (let msg = (match (occurs_ok) with
| true -> begin
None
end
| false -> begin
(let _68_13359 = (let _68_13358 = (Microsoft_FStar_Absyn_Print.uvar_t_to_string uk)
in (let _68_13357 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (let _68_13356 = (let _68_13355 = (Support.Prims.pipe_right wl.subst (Support.List.map (uvi_to_string env)))
in (Support.Prims.pipe_right _68_13355 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format3 "occurs-check failed (%s occurs in %s) (with substitution %s)" _68_13358 _68_13357 _68_13356))))
in Some (_68_13359))
end)
in (occurs_ok, msg))))

let occurs_and_freevars_check = (fun ( env ) ( wl ) ( uk ) ( fvs ) ( t ) -> (let fvs_t = (Microsoft_FStar_Absyn_Util.freevars_typ t)
in (let _33_649 = (occurs_check env wl uk t)
in (match (_33_649) with
| (occurs_ok, msg) -> begin
(let _68_13370 = (Microsoft_FStar_Absyn_Util.fvs_included fvs_t fvs)
in (occurs_ok, _68_13370, (msg, fvs, fvs_t)))
end))))

let occurs_check_e = (fun ( env ) ( ut ) ( e ) -> (let uvs = (Microsoft_FStar_Absyn_Util.uvars_in_exp e)
in (let occurs_ok = (not ((Support.Microsoft.FStar.Util.set_mem ut uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)))
in (let msg = (match (occurs_ok) with
| true -> begin
None
end
| false -> begin
(let _68_13382 = (let _68_13381 = (Microsoft_FStar_Absyn_Print.uvar_e_to_string ut)
in (let _68_13380 = (let _68_13378 = (let _68_13377 = (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (Support.Prims.pipe_right _68_13377 (Support.List.map Microsoft_FStar_Absyn_Print.uvar_e_to_string)))
in (Support.Prims.pipe_right _68_13378 (Support.String.concat ", ")))
in (let _68_13379 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env e)
in (Support.Microsoft.FStar.Util.format3 "occurs-check failed (%s occurs in {%s} uvars of %s)" _68_13381 _68_13380 _68_13379))))
in Some (_68_13382))
end)
in (occurs_ok, msg)))))

let intersect_vars = (fun ( v1 ) ( v2 ) -> (let fvs1 = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders v1)
in (let fvs2 = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders v2)
in (let _68_13389 = (let _68_13388 = (Support.Microsoft.FStar.Util.set_intersect fvs1.Microsoft_FStar_Absyn_Syntax.ftvs fvs2.Microsoft_FStar_Absyn_Syntax.ftvs)
in (let _68_13387 = (Support.Microsoft.FStar.Util.set_intersect fvs1.Microsoft_FStar_Absyn_Syntax.fxvs fvs2.Microsoft_FStar_Absyn_Syntax.fxvs)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _68_13388; Microsoft_FStar_Absyn_Syntax.fxvs = _68_13387}))
in (Microsoft_FStar_Absyn_Syntax.binders_of_freevars _68_13389)))))

let binders_eq = (fun ( v1 ) ( v2 ) -> (((Support.List.length v1) = (Support.List.length v2)) && (Support.List.forall2 (fun ( ax1 ) ( ax2 ) -> (match (((Support.Prims.fst ax1), (Support.Prims.fst ax2))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(Microsoft_FStar_Absyn_Util.bvar_eq a b)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Microsoft_FStar_Absyn_Util.bvar_eq x y)
end
| _ -> begin
false
end)) v1 v2)))

let pat_var_opt = (fun ( env ) ( seen ) ( arg ) -> (let hd = (norm_arg env arg)
in (match ((Support.Prims.pipe_left Support.Prims.fst hd)) with
| Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (a); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) -> begin
(match ((Support.Prims.pipe_right seen (Support.Microsoft.FStar.Util.for_some (fun ( _33_18 ) -> (match (_33_18) with
| (Support.Microsoft.FStar.Util.Inl (b), _) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq a.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
Some ((Support.Microsoft.FStar.Util.Inl (a), (Support.Prims.snd hd)))
end)
end
| Support.Microsoft.FStar.Util.Inr ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_bvar (x); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) -> begin
(match ((Support.Prims.pipe_right seen (Support.Microsoft.FStar.Util.for_some (fun ( _33_19 ) -> (match (_33_19) with
| (Support.Microsoft.FStar.Util.Inr (y), _) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
Some ((Support.Microsoft.FStar.Util.Inr (x), (Support.Prims.snd hd)))
end)
end
| _ -> begin
None
end)))

let rec pat_vars = (fun ( env ) ( seen ) ( args ) -> (match (args) with
| [] -> begin
Some ((Support.List.rev seen))
end
| hd::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(let _33_730 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_13405 = (Microsoft_FStar_Absyn_Print.arg_to_string hd)
in (Support.Microsoft.FStar.Util.fprint1 "Not a pattern: %s\n" _68_13405))
end
| false -> begin
()
end)
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))

let destruct_flex_t = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(t, uv, k, [])
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) -> begin
(t, uv, k, args)
end
| _ -> begin
(failwith ("Not a flex-uvar"))
end))

let destruct_flex_e = (fun ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, k)) -> begin
(e, uv, k, [])
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, k)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) -> begin
(e, uv, k, args)
end
| _ -> begin
(failwith ("Not a flex-uvar"))
end))

let destruct_flex_pattern = (fun ( env ) ( t ) -> (let _33_786 = (destruct_flex_t t)
in (match (_33_786) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _ -> begin
((t, uv, k, args), None)
end)
end)))

type match_result =
| MisMatch
| HeadMatch
| FullMatch

let is_MisMatch = (fun ( _discr_ ) -> (match (_discr_) with
| MisMatch -> begin
true
end
| _ -> begin
false
end))

let is_HeadMatch = (fun ( _discr_ ) -> (match (_discr_) with
| HeadMatch -> begin
true
end
| _ -> begin
false
end))

let is_FullMatch = (fun ( _discr_ ) -> (match (_discr_) with
| FullMatch -> begin
true
end
| _ -> begin
false
end))

let head_match = (fun ( _33_20 ) -> (match (_33_20) with
| MisMatch -> begin
MisMatch
end
| _ -> begin
HeadMatch
end))

let rec head_matches = (fun ( t1 ) ( t2 ) -> (match ((let _68_13422 = (let _68_13419 = (Microsoft_FStar_Absyn_Util.unmeta_typ t1)
in _68_13419.Microsoft_FStar_Absyn_Syntax.n)
in (let _68_13421 = (let _68_13420 = (Microsoft_FStar_Absyn_Util.unmeta_typ t2)
in _68_13420.Microsoft_FStar_Absyn_Syntax.n)
in (_68_13422, _68_13421)))) with
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (x), Microsoft_FStar_Absyn_Syntax.Typ_btvar (y)) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvar_eq x y)) with
| true -> begin
FullMatch
end
| false -> begin
MisMatch
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_const (f), Microsoft_FStar_Absyn_Syntax.Typ_const (g)) -> begin
(match ((Microsoft_FStar_Absyn_Util.fvar_eq f g)) with
| true -> begin
FullMatch
end
| false -> begin
MisMatch
end)
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_btvar (_), Microsoft_FStar_Absyn_Syntax.Typ_const (_))) | ((Microsoft_FStar_Absyn_Syntax.Typ_const (_), Microsoft_FStar_Absyn_Syntax.Typ_btvar (_))) -> begin
MisMatch
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _)), Microsoft_FStar_Absyn_Syntax.Typ_refine ((y, _))) -> begin
(let _68_13423 = (head_matches x.Microsoft_FStar_Absyn_Syntax.sort y.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Prims.pipe_right _68_13423 head_match))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _)), _) -> begin
(let _68_13424 = (head_matches x.Microsoft_FStar_Absyn_Syntax.sort t2)
in (Support.Prims.pipe_right _68_13424 head_match))
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _))) -> begin
(let _68_13425 = (head_matches t1 x.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Prims.pipe_right _68_13425 head_match))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_), Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) -> begin
HeadMatch
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app ((head, _)), Microsoft_FStar_Absyn_Syntax.Typ_app ((head', _))) -> begin
(head_matches head head')
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app ((head, _)), _) -> begin
(head_matches head t2)
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_app ((head, _))) -> begin
(head_matches t1 head)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _)), Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv', _))) -> begin
(match ((Support.Microsoft.FStar.Unionfind.equivalent uv uv')) with
| true -> begin
FullMatch
end
| false -> begin
MisMatch
end)
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) -> begin
HeadMatch
end
| _ -> begin
MisMatch
end))

let head_matches_delta = (fun ( env ) ( wl ) ( t1 ) ( t2 ) -> (let success = (fun ( d ) ( r ) ( t1 ) ( t2 ) -> (r, (match (d) with
| true -> begin
Some ((t1, t2))
end
| false -> begin
None
end)))
in (let fail = (fun ( _33_911 ) -> (match (()) with
| () -> begin
(MisMatch, None)
end))
in (let rec aux = (fun ( d ) ( t1 ) ( t2 ) -> (match ((head_matches t1 t2)) with
| MisMatch -> begin
(match (d) with
| true -> begin
(fail ())
end
| false -> begin
(let t1 = (normalize_refinement env wl t1)
in (let t2 = (normalize_refinement env wl t2)
in (aux true t1 t2)))
end)
end
| r -> begin
(success d r t1 t2)
end))
in (aux false t1 t2)))))

let decompose_binder = (fun ( bs ) ( v_ktec ) ( rebuild_base ) -> (let fail = (fun ( _33_925 ) -> (match (()) with
| () -> begin
(failwith ("Bad reconstruction"))
end))
in (let rebuild = (fun ( ktecs ) -> (let rec aux = (fun ( new_bs ) ( bs ) ( ktecs ) -> (match ((bs, ktecs)) with
| ([], ktec::[]) -> begin
(rebuild_base (Support.List.rev new_bs) ktec)
end
| ((Support.Microsoft.FStar.Util.Inl (a), imp)::rest, Microsoft_FStar_Absyn_Syntax.K (k)::rest') -> begin
(aux (((Support.Microsoft.FStar.Util.Inl ((let _33_947 = a
in {Microsoft_FStar_Absyn_Syntax.v = _33_947.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _33_947.Microsoft_FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| ((Support.Microsoft.FStar.Util.Inr (x), imp)::rest, Microsoft_FStar_Absyn_Syntax.T ((t, _))::rest') -> begin
(aux (((Support.Microsoft.FStar.Util.Inr ((let _33_963 = x
in {Microsoft_FStar_Absyn_Syntax.v = _33_963.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _33_963.Microsoft_FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| _ -> begin
(fail ())
end))
in (aux [] bs ktecs)))
in (let rec mk_b_ktecs = (fun ( _33_970 ) ( _33_21 ) -> (match (_33_970) with
| (binders, b_ktecs) -> begin
(match (_33_21) with
| [] -> begin
(Support.List.rev (((None, COVARIANT, v_ktec))::b_ktecs))
end
| hd::rest -> begin
(let bopt = (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder hd)) with
| true -> begin
None
end
| false -> begin
Some (hd)
end)
in (let b_ktec = (match ((Support.Prims.fst hd)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(bopt, CONTRAVARIANT, Microsoft_FStar_Absyn_Syntax.K (a.Microsoft_FStar_Absyn_Syntax.sort))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(bopt, CONTRAVARIANT, Microsoft_FStar_Absyn_Syntax.T ((x.Microsoft_FStar_Absyn_Syntax.sort, Some (Microsoft_FStar_Absyn_Syntax.ktype))))
end)
in (let binders' = (match (bopt) with
| None -> begin
binders
end
| Some (hd) -> begin
(Support.List.append binders ((hd)::[]))
end)
in (mk_b_ktecs (binders', (b_ktec)::b_ktecs) rest))))
end)
end))
in (let _68_13479 = (mk_b_ktecs ([], []) bs)
in (rebuild, _68_13479))))))

let rec decompose_kind = (fun ( env ) ( k ) -> (let fail = (fun ( _33_989 ) -> (match (()) with
| () -> begin
(failwith ("Bad reconstruction"))
end))
in (let k0 = k
in (let k = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) -> begin
(let rebuild = (fun ( _33_22 ) -> (match (_33_22) with
| [] -> begin
k
end
| _ -> begin
(fail ())
end))
in (rebuild, []))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(decompose_binder bs (Microsoft_FStar_Absyn_Syntax.K (k)) (fun ( bs ) ( _33_23 ) -> (match (_33_23) with
| Microsoft_FStar_Absyn_Syntax.K (k) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) k0.Microsoft_FStar_Absyn_Syntax.pos)
end
| _ -> begin
(fail ())
end)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(decompose_kind env k)
end
| _ -> begin
(failwith ("Impossible"))
end)))))

let rec decompose_typ = (fun ( env ) ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.unmeta_typ t)
in (let matches = (fun ( t' ) -> ((head_matches t t') <> MisMatch))
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((hd, args)) -> begin
(let rebuild = (fun ( args' ) -> (let args = (Support.List.map2 (fun ( x ) ( y ) -> (match ((x, y)) with
| ((Support.Microsoft.FStar.Util.Inl (_), imp), Microsoft_FStar_Absyn_Syntax.T ((t, _))) -> begin
(Support.Microsoft.FStar.Util.Inl (t), imp)
end
| ((Support.Microsoft.FStar.Util.Inr (_), imp), Microsoft_FStar_Absyn_Syntax.E (e)) -> begin
(Support.Microsoft.FStar.Util.Inr (e), imp)
end
| _ -> begin
(failwith ("Bad reconstruction"))
end)) args args')
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (hd, args) None t.Microsoft_FStar_Absyn_Syntax.pos)))
in (let b_ktecs = (Support.Prims.pipe_right args (Support.List.map (fun ( _33_24 ) -> (match (_33_24) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(None, INVARIANT, Microsoft_FStar_Absyn_Syntax.T ((t, None)))
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(None, INVARIANT, Microsoft_FStar_Absyn_Syntax.E (e))
end))))
in (rebuild, matches, b_ktecs)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let _33_1075 = (decompose_binder bs (Microsoft_FStar_Absyn_Syntax.C (c)) (fun ( bs ) ( _33_25 ) -> (match (_33_25) with
| Microsoft_FStar_Absyn_Syntax.C (c) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.Microsoft_FStar_Absyn_Syntax.pos)
end
| _ -> begin
(failwith ("Bad reconstruction"))
end)))
in (match (_33_1075) with
| (rebuild, b_ktecs) -> begin
(rebuild, matches, b_ktecs)
end))
end
| _ -> begin
(let rebuild = (fun ( _33_26 ) -> (match (_33_26) with
| [] -> begin
t
end
| _ -> begin
(failwith ("Bad reconstruction"))
end))
in (rebuild, (fun ( t ) -> true), []))
end))))

let un_T = (fun ( _33_27 ) -> (match (_33_27) with
| Microsoft_FStar_Absyn_Syntax.T ((x, _)) -> begin
x
end
| _ -> begin
(failwith ("impossible"))
end))

let arg_of_ktec = (fun ( _33_28 ) -> (match (_33_28) with
| Microsoft_FStar_Absyn_Syntax.T ((t, _)) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| Microsoft_FStar_Absyn_Syntax.E (e) -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end
| _ -> begin
(failwith ("Impossible"))
end))

let imitation_sub_probs = (fun ( orig ) ( env ) ( scope ) ( ps ) ( qs ) -> (let r = (p_loc orig)
in (let rel = (p_rel orig)
in (let sub_prob = (fun ( scope ) ( args ) ( q ) -> (match (q) with
| (_, variance, Microsoft_FStar_Absyn_Syntax.K (ki)) -> begin
(let _33_1121 = (new_kvar r scope)
in (match (_33_1121) with
| (gi_xs, gi) -> begin
(let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (gi, args) r)
in (let _68_13562 = (let _68_13561 = (mk_problem scope orig gi_ps (vary_rel rel variance) ki None "kind subterm")
in (Support.Prims.pipe_left (fun ( _68_13560 ) -> KProb (_68_13560)) _68_13561))
in (Microsoft_FStar_Absyn_Syntax.K (gi_xs), _68_13562)))
end))
end
| (_, variance, Microsoft_FStar_Absyn_Syntax.T ((ti, kopt))) -> begin
(let k = (match (kopt) with
| Some (k) -> begin
k
end
| None -> begin
(Microsoft_FStar_Tc_Recheck.recompute_kind ti)
end)
in (let _33_1137 = (new_tvar r scope k)
in (match (_33_1137) with
| (gi_xs, gi) -> begin
(let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (gi, args) None r)
in (let _68_13565 = (let _68_13564 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (Support.Prims.pipe_left (fun ( _68_13563 ) -> TProb (_68_13563)) _68_13564))
in (Microsoft_FStar_Absyn_Syntax.T ((gi_xs, Some (k))), _68_13565)))
end)))
end
| (_, variance, Microsoft_FStar_Absyn_Syntax.E (ei)) -> begin
(let t = (Microsoft_FStar_Tc_Recheck.recompute_typ ei)
in (let _33_1148 = (new_evar r scope t)
in (match (_33_1148) with
| (gi_xs, gi) -> begin
(let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (gi, args) (Some (t)) r)
in (let _68_13568 = (let _68_13567 = (mk_problem scope orig gi_ps (vary_rel rel variance) ei None "expression subterm")
in (Support.Prims.pipe_left (fun ( _68_13566 ) -> EProb (_68_13566)) _68_13567))
in (Microsoft_FStar_Absyn_Syntax.E (gi_xs), _68_13568)))
end)))
end
| (_, _, Microsoft_FStar_Absyn_Syntax.C (_)) -> begin
(failwith ("impos"))
end))
in (let rec aux = (fun ( scope ) ( args ) ( qs ) -> (match (qs) with
| [] -> begin
([], [], Microsoft_FStar_Absyn_Util.t_true)
end
| q::qs -> begin
(let _33_1231 = (match (q) with
| (bopt, variance, Microsoft_FStar_Absyn_Syntax.C ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Total (ti); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(match ((sub_prob scope args (bopt, variance, Microsoft_FStar_Absyn_Syntax.T ((ti, Some (Microsoft_FStar_Absyn_Syntax.ktype)))))) with
| (Microsoft_FStar_Absyn_Syntax.T ((gi_xs, _)), prob) -> begin
(let _68_13577 = (let _68_13576 = (Microsoft_FStar_Absyn_Syntax.mk_Total gi_xs)
in (Support.Prims.pipe_left (fun ( _68_13575 ) -> Microsoft_FStar_Absyn_Syntax.C (_68_13575)) _68_13576))
in (_68_13577, (prob)::[]))
end
| _ -> begin
(failwith ("impossible"))
end)
end
| (_, _, Microsoft_FStar_Absyn_Syntax.C ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp (c); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(let components = (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.effect_args (Support.List.map (fun ( _33_29 ) -> (match (_33_29) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(None, INVARIANT, Microsoft_FStar_Absyn_Syntax.T ((t, None)))
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(None, INVARIANT, Microsoft_FStar_Absyn_Syntax.E (e))
end))))
in (let components = ((None, COVARIANT, Microsoft_FStar_Absyn_Syntax.T ((c.Microsoft_FStar_Absyn_Syntax.result_typ, Some (Microsoft_FStar_Absyn_Syntax.ktype)))))::components
in (let _33_1222 = (let _68_13579 = (Support.List.map (sub_prob scope args) components)
in (Support.Prims.pipe_right _68_13579 Support.List.unzip))
in (match (_33_1222) with
| (ktecs, sub_probs) -> begin
(let gi_xs = (let _68_13584 = (let _68_13583 = (let _68_13580 = (Support.List.hd ktecs)
in (Support.Prims.pipe_right _68_13580 un_T))
in (let _68_13582 = (let _68_13581 = (Support.List.tl ktecs)
in (Support.Prims.pipe_right _68_13581 (Support.List.map arg_of_ktec)))
in {Microsoft_FStar_Absyn_Syntax.effect_name = c.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _68_13583; Microsoft_FStar_Absyn_Syntax.effect_args = _68_13582; Microsoft_FStar_Absyn_Syntax.flags = c.Microsoft_FStar_Absyn_Syntax.flags}))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp _68_13584))
in (Microsoft_FStar_Absyn_Syntax.C (gi_xs), sub_probs))
end))))
end
| _ -> begin
(let _33_1228 = (sub_prob scope args q)
in (match (_33_1228) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_33_1231) with
| (ktec, probs) -> begin
(let _33_1244 = (match (q) with
| (Some (b), _, _) -> begin
(let _68_13586 = (let _68_13585 = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder b)
in (_68_13585)::args)
in (Some (b), (b)::scope, _68_13586))
end
| _ -> begin
(None, scope, args)
end)
in (match (_33_1244) with
| (bopt, scope, args) -> begin
(let _33_1248 = (aux scope args qs)
in (match (_33_1248) with
| (sub_probs, ktecs, f) -> begin
(let f = (match (bopt) with
| None -> begin
(let _68_13589 = (let _68_13588 = (Support.Prims.pipe_right probs (Support.List.map (fun ( prob ) -> (Support.Prims.pipe_right (p_guard prob) Support.Prims.fst))))
in (f)::_68_13588)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _68_13589))
end
| Some (b) -> begin
(let _68_13593 = (let _68_13592 = (Microsoft_FStar_Absyn_Util.close_forall ((b)::[]) f)
in (let _68_13591 = (Support.Prims.pipe_right probs (Support.List.map (fun ( prob ) -> (Support.Prims.pipe_right (p_guard prob) Support.Prims.fst))))
in (_68_13592)::_68_13591))
in (Microsoft_FStar_Absyn_Util.mk_conj_l _68_13593))
end)
in ((Support.List.append probs sub_probs), (ktec)::ktecs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

type slack =
{lower : (Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.typ); upper : (Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.typ); flag : bool ref}

let is_Mkslack = (fun ( _ ) -> (failwith ("Not yet implemented:is_Mkslack")))

let fix_slack_uv = (fun ( _33_1261 ) ( mul ) -> (match (_33_1261) with
| (uv, k) -> begin
(let inst = (match (mul) with
| true -> begin
(Microsoft_FStar_Absyn_Util.close_for_kind Microsoft_FStar_Absyn_Util.t_true k)
end
| false -> begin
(Microsoft_FStar_Absyn_Util.close_for_kind Microsoft_FStar_Absyn_Util.t_false k)
end)
in (Microsoft_FStar_Absyn_Util.unchecked_unify uv inst))
end))

let fix_slack_vars = (fun ( slack ) -> (Support.Prims.pipe_right slack (Support.List.iter (fun ( _33_1267 ) -> (match (_33_1267) with
| (mul, s) -> begin
(match ((let _68_13611 = (Microsoft_FStar_Absyn_Util.compress_typ s)
in _68_13611.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(fix_slack_uv (uv, k) mul)
end
| _ -> begin
()
end)
end)))))

let fix_slack = (fun ( slack ) -> (let _33_1281 = (Support.Prims.pipe_left destruct_flex_t (Support.Prims.snd slack.lower))
in (match (_33_1281) with
| (_, ul, kl, _) -> begin
(let _33_1288 = (Support.Prims.pipe_left destruct_flex_t (Support.Prims.snd slack.upper))
in (match (_33_1288) with
| (_, uh, kh, _) -> begin
(let _33_1289 = (fix_slack_uv (ul, kl) false)
in (let _33_1291 = (fix_slack_uv (uh, kh) true)
in (let _33_1293 = (Support.ST.op_Colon_Equals slack.flag true)
in (Microsoft_FStar_Absyn_Util.mk_conj (Support.Prims.fst slack.lower) (Support.Prims.fst slack.upper)))))
end))
end)))

let new_slack_var = (fun ( env ) ( slack ) -> (let xs = (let _68_13619 = (let _68_13618 = (destruct_flex_pattern env (Support.Prims.snd slack.lower))
in (Support.Prims.pipe_right _68_13618 Support.Prims.snd))
in (Support.Prims.pipe_right _68_13619 Support.Microsoft.FStar.Util.must))
in (let _68_13620 = (new_tvar (Support.Prims.fst slack.lower).Microsoft_FStar_Absyn_Syntax.pos xs Microsoft_FStar_Absyn_Syntax.ktype)
in (_68_13620, xs))))

let new_slack_formula = (fun ( p ) ( env ) ( wl ) ( xs ) ( low ) ( high ) -> (let _33_1306 = (new_tvar p xs Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_33_1306) with
| (low_var, uv1) -> begin
(let wl = (add_slack_add uv1 wl)
in (let _33_1310 = (new_tvar p xs Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_33_1310) with
| (high_var, uv2) -> begin
(let wl = (add_slack_mul uv2 wl)
in (let low = (match (low) with
| None -> begin
(Microsoft_FStar_Absyn_Util.mk_disj Microsoft_FStar_Absyn_Util.t_false low_var)
end
| Some (f) -> begin
(Microsoft_FStar_Absyn_Util.mk_disj f low_var)
end)
in (let high = (match (high) with
| None -> begin
(Microsoft_FStar_Absyn_Util.mk_conj Microsoft_FStar_Absyn_Util.t_true high_var)
end
| Some (f) -> begin
(Microsoft_FStar_Absyn_Util.mk_conj f high_var)
end)
in (let _68_13630 = (let _68_13629 = (let _68_13628 = (let _68_13627 = (Support.Microsoft.FStar.Util.mk_ref false)
in (low, high, _68_13627))
in Microsoft_FStar_Absyn_Syntax.Meta_slack_formula (_68_13628))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _68_13629))
in (_68_13630, wl)))))
end)))
end)))

let destruct_slack = (fun ( env ) ( wl ) ( phi ) -> (let rec destruct = (fun ( conn_lid ) ( mk_conn ) ( phi ) -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, (Support.Microsoft.FStar.Util.Inl (lhs), _)::(Support.Microsoft.FStar.Util.Inl (rhs), _)::[])) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v conn_lid) -> begin
(let rhs = (compress env wl rhs)
in (match (rhs.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
Some ((lhs, rhs))
end
| _ -> begin
(match ((destruct conn_lid mk_conn rhs)) with
| None -> begin
None
end
| Some ((rest, uvar)) -> begin
(let _68_13654 = (let _68_13653 = (mk_conn lhs rest)
in (_68_13653, uvar))
in Some (_68_13654))
end)
end))
end
| _ -> begin
None
end))
in (let phi = (Microsoft_FStar_Absyn_Util.compress_typ phi)
in (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((phi1, phi2, flag))) -> begin
(match ((Support.ST.read flag)) with
| true -> begin
(let _68_13655 = (Microsoft_FStar_Absyn_Util.unmeta_typ phi)
in Support.Microsoft.FStar.Util.Inl (_68_13655))
end
| false -> begin
(let low = (let _68_13656 = (compress env wl phi1)
in (Support.Prims.pipe_left (destruct Microsoft_FStar_Absyn_Const.or_lid Microsoft_FStar_Absyn_Util.mk_disj) _68_13656))
in (let hi = (let _68_13657 = (compress env wl phi2)
in (Support.Prims.pipe_left (destruct Microsoft_FStar_Absyn_Const.and_lid Microsoft_FStar_Absyn_Util.mk_disj) _68_13657))
in (match ((low, hi)) with
| (None, None) -> begin
(let _33_1392 = (Support.ST.op_Colon_Equals flag true)
in (let _68_13658 = (Microsoft_FStar_Absyn_Util.unmeta_typ phi)
in Support.Microsoft.FStar.Util.Inl (_68_13658)))
end
| ((Some (_), None)) | ((None, Some (_))) -> begin
(failwith ("Impossible"))
end
| (Some (l), Some (u)) -> begin
Support.Microsoft.FStar.Util.Inr ({lower = l; upper = u; flag = flag})
end)))
end)
end
| _ -> begin
Support.Microsoft.FStar.Util.Inl (phi)
end))))

let rec eq_typ = (fun ( t1 ) ( t2 ) -> (let t1 = (Microsoft_FStar_Absyn_Util.compress_typ t1)
in (let t2 = (Microsoft_FStar_Absyn_Util.compress_typ t2)
in (match ((t1.Microsoft_FStar_Absyn_Syntax.n, t2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(Microsoft_FStar_Absyn_Util.bvar_eq a b)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_const (f), Microsoft_FStar_Absyn_Syntax.Typ_const (g)) -> begin
(Microsoft_FStar_Absyn_Util.fvar_eq f g)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar ((u1, _)), Microsoft_FStar_Absyn_Syntax.Typ_uvar ((u2, _))) -> begin
(Support.Microsoft.FStar.Unionfind.equivalent u1 u2)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app ((h1, args1)), Microsoft_FStar_Absyn_Syntax.Typ_app ((h2, args2))) -> begin
((eq_typ h1 h2) && (eq_args args1 args2))
end
| _ -> begin
false
end))))
and eq_exp = (fun ( e1 ) ( e2 ) -> (let e1 = (Microsoft_FStar_Absyn_Util.compress_exp e1)
in (let e2 = (Microsoft_FStar_Absyn_Util.compress_exp e2)
in (match ((e1.Microsoft_FStar_Absyn_Syntax.n, e2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (a), Microsoft_FStar_Absyn_Syntax.Exp_bvar (b)) -> begin
(Microsoft_FStar_Absyn_Util.bvar_eq a b)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _)), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((g, _))) -> begin
(Microsoft_FStar_Absyn_Util.fvar_eq f g)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_constant (c), Microsoft_FStar_Absyn_Syntax.Exp_constant (d)) -> begin
(c = d)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((h1, args1)), Microsoft_FStar_Absyn_Syntax.Exp_app ((h2, args2))) -> begin
((eq_exp h1 h2) && (eq_args args1 args2))
end
| _ -> begin
false
end))))
and eq_args = (fun ( a1 ) ( a2 ) -> (match (((Support.List.length a1) = (Support.List.length a2))) with
| true -> begin
(Support.List.forall2 (fun ( a1 ) ( a2 ) -> (match ((a1, a2)) with
| ((Support.Microsoft.FStar.Util.Inl (t), _), (Support.Microsoft.FStar.Util.Inl (s), _)) -> begin
(eq_typ t s)
end
| ((Support.Microsoft.FStar.Util.Inr (e), _), (Support.Microsoft.FStar.Util.Inr (f), _)) -> begin
(eq_exp e f)
end
| _ -> begin
false
end)) a1 a2)
end
| false -> begin
false
end))

type flex_t =
(Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.uvar_t * Microsoft_FStar_Absyn_Syntax.knd * Microsoft_FStar_Absyn_Syntax.args)

type im_or_proj_t =
((Microsoft_FStar_Absyn_Syntax.uvar_t * Microsoft_FStar_Absyn_Syntax.knd) * Microsoft_FStar_Absyn_Syntax.arg list * Microsoft_FStar_Absyn_Syntax.binders * ((Microsoft_FStar_Absyn_Syntax.ktec list  ->  Microsoft_FStar_Absyn_Syntax.typ) * (Microsoft_FStar_Absyn_Syntax.typ  ->  bool) * (Microsoft_FStar_Absyn_Syntax.binder option * variance * Microsoft_FStar_Absyn_Syntax.ktec) list))

let rigid_rigid = 0

let flex_rigid_eq = 1

let flex_refine_inner = 2

let flex_refine = 3

let flex_rigid = 4

let rigid_flex = 5

let refine_flex = 6

let flex_flex = 7

let compress_prob = (fun ( wl ) ( p ) -> (match (p) with
| KProb (p) -> begin
(let _68_13688 = (let _33_1515 = p
in (let _68_13686 = (compress_k wl.tcenv wl p.lhs)
in (let _68_13685 = (compress_k wl.tcenv wl p.rhs)
in {lhs = _68_13686; relation = _33_1515.relation; rhs = _68_13685; element = _33_1515.element; logical_guard = _33_1515.logical_guard; scope = _33_1515.scope; reason = _33_1515.reason; loc = _33_1515.loc; rank = _33_1515.rank})))
in (Support.Prims.pipe_right _68_13688 (fun ( _68_13687 ) -> KProb (_68_13687))))
end
| TProb (p) -> begin
(let _68_13692 = (let _33_1519 = p
in (let _68_13690 = (compress wl.tcenv wl p.lhs)
in (let _68_13689 = (compress wl.tcenv wl p.rhs)
in {lhs = _68_13690; relation = _33_1519.relation; rhs = _68_13689; element = _33_1519.element; logical_guard = _33_1519.logical_guard; scope = _33_1519.scope; reason = _33_1519.reason; loc = _33_1519.loc; rank = _33_1519.rank})))
in (Support.Prims.pipe_right _68_13692 (fun ( _68_13691 ) -> TProb (_68_13691))))
end
| EProb (p) -> begin
(let _68_13696 = (let _33_1523 = p
in (let _68_13694 = (compress_e wl.tcenv wl p.lhs)
in (let _68_13693 = (compress_e wl.tcenv wl p.rhs)
in {lhs = _68_13694; relation = _33_1523.relation; rhs = _68_13693; element = _33_1523.element; logical_guard = _33_1523.logical_guard; scope = _33_1523.scope; reason = _33_1523.reason; loc = _33_1523.loc; rank = _33_1523.rank})))
in (Support.Prims.pipe_right _68_13696 (fun ( _68_13695 ) -> EProb (_68_13695))))
end
| CProb (_) -> begin
p
end))

let rank = (fun ( wl ) ( prob ) -> (let prob = (let _68_13701 = (compress_prob wl prob)
in (Support.Prims.pipe_right _68_13701 maybe_invert_p))
in (match (prob) with
| KProb (kp) -> begin
(let rank = (match ((kp.lhs.Microsoft_FStar_Absyn_Syntax.n, kp.rhs.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_), Microsoft_FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
flex_flex
end
| (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_), _) -> begin
(match ((kp.relation = EQ)) with
| true -> begin
flex_rigid_eq
end
| false -> begin
flex_rigid
end)
end
| (_, Microsoft_FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
(match ((kp.relation = EQ)) with
| true -> begin
flex_rigid_eq
end
| false -> begin
rigid_flex
end)
end
| (_, _) -> begin
rigid_rigid
end)
in (let _68_13703 = (Support.Prims.pipe_right (let _33_1558 = kp
in {lhs = _33_1558.lhs; relation = _33_1558.relation; rhs = _33_1558.rhs; element = _33_1558.element; logical_guard = _33_1558.logical_guard; scope = _33_1558.scope; reason = _33_1558.reason; loc = _33_1558.loc; rank = Some (rank)}) (fun ( _68_13702 ) -> KProb (_68_13702)))
in (rank, _68_13703)))
end
| TProb (tp) -> begin
(let _33_1565 = (Microsoft_FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_33_1565) with
| (lh, _) -> begin
(let _33_1569 = (Microsoft_FStar_Absyn_Util.head_and_args tp.rhs)
in (match (_33_1569) with
| (rh, _) -> begin
(let _33_1625 = (match ((lh.Microsoft_FStar_Absyn_Syntax.n, rh.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
(flex_flex, tp)
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_uvar (_))) when (tp.relation = EQ) -> begin
(flex_rigid_eq, tp)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), _) -> begin
(let _33_1597 = (base_and_refinement wl.tcenv wl tp.rhs)
in (match (_33_1597) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _ -> begin
(let rank = (match ((is_top_level_prob prob)) with
| true -> begin
flex_refine
end
| false -> begin
flex_refine_inner
end)
in (let _68_13705 = (let _33_1602 = tp
in (let _68_13704 = (force_refinement (b, ref_opt))
in {lhs = _33_1602.lhs; relation = _33_1602.relation; rhs = _68_13704; element = _33_1602.element; logical_guard = _33_1602.logical_guard; scope = _33_1602.scope; reason = _33_1602.reason; loc = _33_1602.loc; rank = _33_1602.rank}))
in (rank, _68_13705)))
end)
end))
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
(let _33_1612 = (base_and_refinement wl.tcenv wl tp.lhs)
in (match (_33_1612) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _ -> begin
(let _68_13707 = (let _33_1616 = tp
in (let _68_13706 = (force_refinement (b, ref_opt))
in {lhs = _68_13706; relation = _33_1616.relation; rhs = _33_1616.rhs; element = _33_1616.element; logical_guard = _33_1616.logical_guard; scope = _33_1616.scope; reason = _33_1616.reason; loc = _33_1616.loc; rank = _33_1616.rank}))
in (refine_flex, _68_13707))
end)
end))
end
| (_, _) -> begin
(rigid_rigid, tp)
end)
in (match (_33_1625) with
| (rank, tp) -> begin
(let _68_13709 = (Support.Prims.pipe_right (let _33_1626 = tp
in {lhs = _33_1626.lhs; relation = _33_1626.relation; rhs = _33_1626.rhs; element = _33_1626.element; logical_guard = _33_1626.logical_guard; scope = _33_1626.scope; reason = _33_1626.reason; loc = _33_1626.loc; rank = Some (rank)}) (fun ( _68_13708 ) -> TProb (_68_13708)))
in (rank, _68_13709))
end))
end))
end))
end
| EProb (ep) -> begin
(let _33_1633 = (Microsoft_FStar_Absyn_Util.head_and_args_e ep.lhs)
in (match (_33_1633) with
| (lh, _) -> begin
(let _33_1637 = (Microsoft_FStar_Absyn_Util.head_and_args_e ep.rhs)
in (match (_33_1637) with
| (rh, _) -> begin
(let rank = (match ((lh.Microsoft_FStar_Absyn_Syntax.n, rh.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
flex_flex
end
| ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) -> begin
flex_rigid_eq
end
| (_, _) -> begin
rigid_rigid
end)
in (let _68_13711 = (Support.Prims.pipe_right (let _33_1663 = ep
in {lhs = _33_1663.lhs; relation = _33_1663.relation; rhs = _33_1663.rhs; element = _33_1663.element; logical_guard = _33_1663.logical_guard; scope = _33_1663.scope; reason = _33_1663.reason; loc = _33_1663.loc; rank = Some (rank)}) (fun ( _68_13710 ) -> EProb (_68_13710)))
in (rank, _68_13711)))
end))
end))
end
| CProb (cp) -> begin
(let _68_13713 = (Support.Prims.pipe_right (let _33_1667 = cp
in {lhs = _33_1667.lhs; relation = _33_1667.relation; rhs = _33_1667.rhs; element = _33_1667.element; logical_guard = _33_1667.logical_guard; scope = _33_1667.scope; reason = _33_1667.reason; loc = _33_1667.loc; rank = Some (rigid_rigid)}) (fun ( _68_13712 ) -> CProb (_68_13712)))
in (rigid_rigid, _68_13713))
end)))

let next_prob = (fun ( wl ) -> (let rec aux = (fun ( _33_1674 ) ( probs ) -> (match (_33_1674) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(let _33_1682 = (rank wl hd)
in (match (_33_1682) with
| (rank, hd) -> begin
(match ((rank <= flex_rigid_eq)) with
| true -> begin
(match (min) with
| None -> begin
(Some (hd), (Support.List.append out tl), rank)
end
| Some (m) -> begin
(Some (hd), (Support.List.append out ((m)::tl)), rank)
end)
end
| false -> begin
(match ((rank < min_rank)) with
| true -> begin
(match (min) with
| None -> begin
(aux (rank, Some (hd), out) tl)
end
| Some (m) -> begin
(aux (rank, Some (hd), (m)::out) tl)
end)
end
| false -> begin
(aux (min_rank, min, (hd)::out) tl)
end)
end)
end))
end)
end))
in (aux ((flex_flex + 1), None, []) wl.attempting)))

let is_flex_rigid = (fun ( rank ) -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))

let rec solve_flex_rigid_join = (fun ( env ) ( tp ) ( wl ) -> (let _33_1693 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_13763 = (prob_to_string env (TProb (tp)))
in (Support.Microsoft.FStar.Util.fprint1 "Trying to solve by joining refinements:%s\n" _68_13763))
end
| false -> begin
()
end)
in (let _33_1697 = (Microsoft_FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_33_1697) with
| (u, args) -> begin
(let _33_1703 = (0, 1, 2, 3, 4)
in (match (_33_1703) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(let max = (fun ( i ) ( j ) -> (match ((i < j)) with
| true -> begin
j
end
| false -> begin
i
end))
in (let base_types_match = (fun ( t1 ) ( t2 ) -> (let _33_1712 = (Microsoft_FStar_Absyn_Util.head_and_args t1)
in (match (_33_1712) with
| (h1, args1) -> begin
(let _33_1716 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (match (_33_1716) with
| (h2, _) -> begin
(match ((h1.Microsoft_FStar_Absyn_Syntax.n, h2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_const (tc1), Microsoft_FStar_Absyn_Syntax.Typ_const (tc2)) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals tc1.Microsoft_FStar_Absyn_Syntax.v tc2.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(match (((Support.List.length args1) = 0)) with
| true -> begin
Some ([])
end
| false -> begin
(let _68_13775 = (let _68_13774 = (let _68_13773 = (new_problem env t1 EQ t2 None t1.Microsoft_FStar_Absyn_Syntax.pos "joining refinements")
in (Support.Prims.pipe_left (fun ( _68_13772 ) -> TProb (_68_13772)) _68_13773))
in (_68_13774)::[])
in Some (_68_13775))
end)
end
| false -> begin
None
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvar_eq a b)) with
| true -> begin
Some ([])
end
| false -> begin
None
end)
end
| _ -> begin
None
end)
end))
end)))
in (let conjoin = (fun ( t1 ) ( t2 ) -> (match ((t1.Microsoft_FStar_Absyn_Syntax.n, t2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi1)), Microsoft_FStar_Absyn_Syntax.Typ_refine ((y, phi2))) -> begin
(let m = (base_types_match x.Microsoft_FStar_Absyn_Syntax.sort y.Microsoft_FStar_Absyn_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(let phi2 = (let _68_13782 = (let _68_13781 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (let _68_13780 = (Microsoft_FStar_Absyn_Syntax.v_binder y)
in (Microsoft_FStar_Absyn_Util.mk_subst_one_binder _68_13781 _68_13780)))
in (Microsoft_FStar_Absyn_Util.subst_typ _68_13782 phi2))
in (let _68_13786 = (let _68_13785 = (let _68_13784 = (let _68_13783 = (Microsoft_FStar_Absyn_Util.mk_conj phi1 phi2)
in (x, _68_13783))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _68_13784 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) t1.Microsoft_FStar_Absyn_Syntax.pos))
in (_68_13785, m))
in Some (_68_13786)))
end))
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_refine ((y, _))) -> begin
(let m = (base_types_match t1 y.Microsoft_FStar_Absyn_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _)), _) -> begin
(let m = (base_types_match x.Microsoft_FStar_Absyn_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _ -> begin
(let m = (base_types_match t1 t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end))
in (let tt = u
in (match (tt.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _)) -> begin
(let _33_1804 = (Support.Prims.pipe_right wl.attempting (Support.List.partition (fun ( _33_30 ) -> (match (_33_30) with
| TProb (tp) -> begin
(match (tp.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(let _33_1790 = (Microsoft_FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_33_1790) with
| (u', _) -> begin
(match ((let _68_13788 = (compress env wl u')
in _68_13788.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv', _)) -> begin
(Support.Microsoft.FStar.Unionfind.equivalent uv uv')
end
| _ -> begin
false
end)
end))
end
| _ -> begin
false
end)
end
| _ -> begin
false
end))))
in (match (_33_1804) with
| (upper_bounds, rest) -> begin
(let rec make_upper_bound = (fun ( _33_1808 ) ( tps ) -> (match (_33_1808) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| TProb (hd)::tl -> begin
(match ((let _68_13793 = (compress env wl hd.rhs)
in (conjoin bound _68_13793))) with
| Some ((bound, sub)) -> begin
(make_upper_bound (bound, (Support.List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _ -> begin
None
end)
end))
in (match ((let _68_13795 = (let _68_13794 = (compress env wl tp.rhs)
in (_68_13794, []))
in (make_upper_bound _68_13795 upper_bounds))) with
| None -> begin
(let _33_1823 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(Support.Microsoft.FStar.Util.print_string "No upper bounds\n")
end
| false -> begin
()
end)
in None)
end
| Some ((rhs_bound, sub_probs)) -> begin
(let eq_prob = (new_problem env tp.lhs EQ rhs_bound None tp.loc "joining refinements")
in (match ((solve_t env eq_prob (let _33_1830 = wl
in {attempting = sub_probs; deferred = _33_1830.deferred; subst = _33_1830.subst; ctr = _33_1830.ctr; slack_vars = _33_1830.slack_vars; defer_ok = _33_1830.defer_ok; smt_ok = _33_1830.smt_ok; tcenv = _33_1830.tcenv}))) with
| Success ((subst, _)) -> begin
(let wl = (let _33_1837 = wl
in {attempting = rest; deferred = _33_1837.deferred; subst = []; ctr = _33_1837.ctr; slack_vars = _33_1837.slack_vars; defer_ok = _33_1837.defer_ok; smt_ok = _33_1837.smt_ok; tcenv = _33_1837.tcenv})
in (let wl = (solve_prob (TProb (tp)) None subst wl)
in (let _33_1843 = (Support.List.fold_left (fun ( wl ) ( p ) -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _ -> begin
None
end))
end))
end))
end
| _ -> begin
(failwith ("Impossible: Not a flex-rigid"))
end)))))
end))
end))))
and solve = (fun ( env ) ( probs ) -> (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(let probs = (let _33_1856 = probs
in {attempting = tl; deferred = _33_1856.deferred; subst = _33_1856.subst; ctr = _33_1856.ctr; slack_vars = _33_1856.slack_vars; defer_ok = _33_1856.defer_ok; smt_ok = _33_1856.smt_ok; tcenv = _33_1856.tcenv})
in (match (hd) with
| KProb (kp) -> begin
(solve_k' env (maybe_invert kp) probs)
end
| TProb (tp) -> begin
(match (((((not (probs.defer_ok)) && (flex_refine_inner <= rank)) && (rank <= flex_rigid)) && (not ((Support.ST.read Microsoft_FStar_Options.no_slack))))) with
| true -> begin
(match ((solve_flex_rigid_join env tp probs)) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end)
end
| false -> begin
(solve_t' env (maybe_invert tp) probs)
end)
end
| EProb (ep) -> begin
(solve_e' env (maybe_invert ep) probs)
end
| CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs)
end))
end
| (None, _, _) -> begin
(match (probs.deferred) with
| [] -> begin
Success ((probs.subst, {carry = []; slack = probs.slack_vars}))
end
| _ -> begin
(let _33_1887 = (Support.Prims.pipe_right probs.deferred (Support.List.partition (fun ( _33_1884 ) -> (match (_33_1884) with
| (c, _, _) -> begin
(c < probs.ctr)
end))))
in (match (_33_1887) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _68_13804 = (let _68_13803 = (let _68_13802 = (Support.List.map (fun ( _33_1893 ) -> (match (_33_1893) with
| (_, x, y) -> begin
(x, y)
end)) probs.deferred)
in {carry = _68_13802; slack = probs.slack_vars})
in (probs.subst, _68_13803))
in Success (_68_13804))
end
| _ -> begin
(let _68_13807 = (let _33_1896 = probs
in (let _68_13806 = (Support.Prims.pipe_right attempt (Support.List.map (fun ( _33_1903 ) -> (match (_33_1903) with
| (_, _, y) -> begin
y
end))))
in {attempting = _68_13806; deferred = rest; subst = _33_1896.subst; ctr = _33_1896.ctr; slack_vars = _33_1896.slack_vars; defer_ok = _33_1896.defer_ok; smt_ok = _33_1896.smt_ok; tcenv = _33_1896.tcenv}))
in (solve env _68_13807))
end)
end))
end)
end))
and solve_binders = (fun ( env ) ( bs1 ) ( bs2 ) ( orig ) ( wl ) ( rhs ) -> (let rec aux = (fun ( scope ) ( env ) ( subst ) ( xs ) ( ys ) -> (match ((xs, ys)) with
| ([], []) -> begin
(let rhs_prob = (rhs scope env subst)
in (let formula = (Support.Prims.pipe_right (p_guard rhs_prob) Support.Prims.fst)
in Support.Microsoft.FStar.Util.Inl (((rhs_prob)::[], formula))))
end
| (((Support.Microsoft.FStar.Util.Inl (_), _)::_, (Support.Microsoft.FStar.Util.Inr (_), _)::_)) | (((Support.Microsoft.FStar.Util.Inr (_), _)::_, (Support.Microsoft.FStar.Util.Inl (_), _)::_)) -> begin
Support.Microsoft.FStar.Util.Inr ("sort mismatch")
end
| (hd1::xs, hd2::ys) -> begin
(let subst = (let _68_13833 = (Microsoft_FStar_Absyn_Util.mk_subst_one_binder hd2 hd1)
in (Support.List.append _68_13833 subst))
in (let env = (let _68_13834 = (Microsoft_FStar_Tc_Env.binding_of_binder hd2)
in (Microsoft_FStar_Tc_Env.push_local_binding env _68_13834))
in (let prob = (match (((Support.Prims.fst hd1), (Support.Prims.fst hd2))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(let _68_13838 = (let _68_13837 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _68_13836 = (Support.Prims.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _68_13837 _68_13836 b.Microsoft_FStar_Absyn_Syntax.sort None "Formal type parameter")))
in (Support.Prims.pipe_left (fun ( _68_13835 ) -> KProb (_68_13835)) _68_13838))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(let _68_13842 = (let _68_13841 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _68_13840 = (Support.Prims.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _68_13841 _68_13840 y.Microsoft_FStar_Absyn_Syntax.sort None "Formal value parameter")))
in (Support.Prims.pipe_left (fun ( _68_13839 ) -> TProb (_68_13839)) _68_13842))
end
| _ -> begin
(failwith ("impos"))
end)
in (match ((aux ((hd2)::scope) env subst xs ys)) with
| Support.Microsoft.FStar.Util.Inr (msg) -> begin
Support.Microsoft.FStar.Util.Inr (msg)
end
| Support.Microsoft.FStar.Util.Inl ((sub_probs, phi)) -> begin
(let phi = (let _68_13844 = (Support.Prims.pipe_right (p_guard prob) Support.Prims.fst)
in (let _68_13843 = (Microsoft_FStar_Absyn_Util.close_forall ((hd2)::[]) phi)
in (Microsoft_FStar_Absyn_Util.mk_conj _68_13844 _68_13843)))
in Support.Microsoft.FStar.Util.Inl (((prob)::sub_probs, phi)))
end))))
end
| _ -> begin
Support.Microsoft.FStar.Util.Inr ("arity mismatch")
end))
in (let scope = (Microsoft_FStar_Tc_Env.binders env)
in (match ((aux scope env [] bs1 bs2)) with
| Support.Microsoft.FStar.Util.Inr (msg) -> begin
(giveup env msg orig)
end
| Support.Microsoft.FStar.Util.Inl ((sub_probs, phi)) -> begin
(let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_k = (fun ( env ) ( problem ) ( wl ) -> (match ((compress_prob wl (KProb (problem)))) with
| KProb (p) -> begin
(solve_k' env p wl)
end
| _ -> begin
(failwith ("impossible"))
end))
and solve_k' = (fun ( env ) ( problem ) ( wl ) -> (let orig = KProb (problem)
in (match ((Support.Microsoft.FStar.Util.physical_equality problem.lhs problem.rhs)) with
| true -> begin
(let _68_13851 = (solve_prob orig None [] wl)
in (solve env _68_13851))
end
| false -> begin
(let k1 = problem.lhs
in (let k2 = problem.rhs
in (match ((Support.Microsoft.FStar.Util.physical_equality k1 k2)) with
| true -> begin
(let _68_13852 = (solve_prob orig None [] wl)
in (solve env _68_13852))
end
| false -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let imitate_k = (fun ( _33_2020 ) -> (match (_33_2020) with
| (rel, u, ps, xs, (h, qs)) -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let _33_2025 = (imitation_sub_probs orig env xs ps qs)
in (match (_33_2025) with
| (sub_probs, gs_xs, f) -> begin
(let im = (let _68_13868 = (let _68_13867 = (h gs_xs)
in (xs, _68_13867))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam _68_13868 r))
in (let wl = (solve_prob orig (Some (f)) ((UK ((u, im)))::[]) wl)
in (solve env (attempt sub_probs wl))))
end)))
end))
in (let flex_rigid = (fun ( rel ) ( u ) ( args ) ( k ) -> (let maybe_vars1 = (pat_vars env [] args)
in (match (maybe_vars1) with
| Some (xs) -> begin
(let fvs1 = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders xs)
in (let fvs2 = (Microsoft_FStar_Absyn_Util.freevars_kind k2)
in (let uvs2 = (Microsoft_FStar_Absyn_Util.uvars_in_kind k2)
in (match ((((Support.Microsoft.FStar.Util.set_is_subset_of fvs2.Microsoft_FStar_Absyn_Syntax.ftvs fvs1.Microsoft_FStar_Absyn_Syntax.ftvs) && (Support.Microsoft.FStar.Util.set_is_subset_of fvs2.Microsoft_FStar_Absyn_Syntax.fxvs fvs1.Microsoft_FStar_Absyn_Syntax.fxvs)) && (not ((Support.Microsoft.FStar.Util.set_mem u uvs2.Microsoft_FStar_Absyn_Syntax.uvars_k))))) with
| true -> begin
(let k1 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam (xs, k2) r)
in (let _68_13877 = (solve_prob orig None ((UK ((u, k1)))::[]) wl)
in (solve env _68_13877)))
end
| false -> begin
(let _68_13882 = (let _68_13881 = (Support.Prims.pipe_right xs Microsoft_FStar_Absyn_Util.args_of_non_null_binders)
in (let _68_13880 = (decompose_kind env k)
in (rel, u, _68_13881, xs, _68_13880)))
in (imitate_k _68_13882))
end))))
end
| None -> begin
(giveup env "flex-rigid: not a pattern" (KProb (problem)))
end)))
in (match ((k1.Microsoft_FStar_Absyn_Syntax.n, k2.Microsoft_FStar_Absyn_Syntax.n)) with
| ((Microsoft_FStar_Absyn_Syntax.Kind_type, Microsoft_FStar_Absyn_Syntax.Kind_type)) | ((Microsoft_FStar_Absyn_Syntax.Kind_effect, Microsoft_FStar_Absyn_Syntax.Kind_effect)) -> begin
(let _68_13883 = (solve_prob orig None [] wl)
in (Support.Prims.pipe_left (solve env) _68_13883))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k1)), _) -> begin
(solve_k env (let _33_2055 = problem
in {lhs = k1; relation = _33_2055.relation; rhs = _33_2055.rhs; element = _33_2055.element; logical_guard = _33_2055.logical_guard; scope = _33_2055.scope; reason = _33_2055.reason; loc = _33_2055.loc; rank = _33_2055.rank}) wl)
end
| (_, Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k2))) -> begin
(solve_k env (let _33_2065 = problem
in {lhs = _33_2065.lhs; relation = _33_2065.relation; rhs = k2; element = _33_2065.element; logical_guard = _33_2065.logical_guard; scope = _33_2065.scope; reason = _33_2065.reason; loc = _33_2065.loc; rank = _33_2065.rank}) wl)
end
| (Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs1, k1')), Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs2, k2'))) -> begin
(let sub_prob = (fun ( scope ) ( env ) ( subst ) -> (let _68_13892 = (let _68_13891 = (Microsoft_FStar_Absyn_Util.subst_kind subst k1')
in (mk_problem scope orig _68_13891 problem.relation k2' None "Arrow-kind result"))
in (Support.Prims.pipe_left (fun ( _68_13890 ) -> KProb (_68_13890)) _68_13892)))
in (solve_binders env bs1 bs2 orig wl sub_prob))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_uvar ((u1, args1)), Microsoft_FStar_Absyn_Syntax.Kind_uvar ((u2, args2))) -> begin
(let maybe_vars1 = (pat_vars env [] args1)
in (let maybe_vars2 = (pat_vars env [] args2)
in (match ((maybe_vars1, maybe_vars2)) with
| ((None, _)) | ((_, None)) -> begin
(giveup env "flex-flex: non patterns" (KProb (problem)))
end
| (Some (xs), Some (ys)) -> begin
(match (((Support.Microsoft.FStar.Unionfind.equivalent u1 u2) && (binders_eq xs ys))) with
| true -> begin
(solve env wl)
end
| false -> begin
(let zs = (intersect_vars xs ys)
in (let _33_2108 = (new_kvar r zs)
in (match (_33_2108) with
| (u, _) -> begin
(let k1 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam (xs, u) r)
in (let k2 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam (ys, u) r)
in (let wl = (solve_prob orig None ((UK ((u1, k1)))::(UK ((u2, k2)))::[]) wl)
in (solve env wl))))
end)))
end)
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_uvar ((u, args)), _) -> begin
(flex_rigid problem.relation u args k2)
end
| (_, Microsoft_FStar_Absyn_Syntax.Kind_uvar ((u, args))) -> begin
(flex_rigid (invert_rel problem.relation) u args k1)
end
| ((Microsoft_FStar_Absyn_Syntax.Kind_delayed (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Kind_unknown, _)) | ((_, Microsoft_FStar_Absyn_Syntax.Kind_delayed (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Kind_unknown)) -> begin
(failwith ("Impossible"))
end
| _ -> begin
(giveup env "head mismatch (k-1)" (KProb (problem)))
end))))
end)))
end)))
and solve_t = (fun ( env ) ( problem ) ( wl ) -> (let p = (compress_prob wl (TProb (problem)))
in (match (p) with
| TProb (p) -> begin
(solve_t' env p wl)
end
| _ -> begin
(failwith ("Impossible"))
end)))
and solve_t' = (fun ( env ) ( problem ) ( wl ) -> (let giveup_or_defer = (fun ( orig ) ( msg ) -> (match (wl.defer_ok) with
| true -> begin
(let _33_2162 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_13903 = (prob_to_string env orig)
in (Support.Microsoft.FStar.Util.fprint2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _68_13903 msg))
end
| false -> begin
()
end)
in (solve env (defer msg orig wl)))
end
| false -> begin
(giveup env msg orig)
end))
in (let imitate_t = (fun ( orig ) ( env ) ( wl ) ( p ) -> (let _33_2179 = p
in (match (_33_2179) with
| ((u, k), ps, xs, (h, _, qs)) -> begin
(let xs = (sn_binders env xs)
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let _33_2185 = (imitation_sub_probs orig env xs ps qs)
in (match (_33_2185) with
| (sub_probs, gs_xs, formula) -> begin
(let im = (let _68_13914 = (let _68_13913 = (h gs_xs)
in (xs, _68_13913))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' _68_13914 None r))
in (let _33_2187 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_13919 = (Microsoft_FStar_Absyn_Print.typ_to_string im)
in (let _68_13918 = (Microsoft_FStar_Absyn_Print.tag_of_typ im)
in (let _68_13917 = (let _68_13915 = (Support.List.map (prob_to_string env) sub_probs)
in (Support.Prims.pipe_right _68_13915 (Support.String.concat ", ")))
in (let _68_13916 = (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env formula)
in (Support.Microsoft.FStar.Util.fprint4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _68_13919 _68_13918 _68_13917 _68_13916)))))
end
| false -> begin
()
end)
in (let wl = (solve_prob orig (Some (formula)) ((UT (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (let project_t = (fun ( orig ) ( env ) ( wl ) ( i ) ( p ) -> (let _33_2203 = p
in (match (_33_2203) with
| (u, ps, xs, (h, matches, qs)) -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let pi = (Support.List.nth ps i)
in (let rec gs = (fun ( k ) -> (let _33_2210 = (Microsoft_FStar_Absyn_Util.kind_formals k)
in (match (_33_2210) with
| (bs, k) -> begin
(let rec aux = (fun ( subst ) ( bs ) -> (match (bs) with
| [] -> begin
([], [])
end
| hd::tl -> begin
(let _33_2239 = (match ((Support.Prims.fst hd)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let k_a = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _33_2223 = (new_tvar r xs k_a)
in (match (_33_2223) with
| (gi_xs, gi) -> begin
(let gi_xs = (Microsoft_FStar_Tc_Normalize.eta_expand env gi_xs)
in (let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (gi, ps) (Some (k_a)) r)
in (let subst = (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder hd)) with
| true -> begin
subst
end
| false -> begin
(Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, gi_xs)))::subst
end)
in (let _68_13939 = (Microsoft_FStar_Absyn_Syntax.targ gi_xs)
in (let _68_13938 = (Microsoft_FStar_Absyn_Syntax.targ gi_ps)
in (_68_13939, _68_13938, subst))))))
end)))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let t_x = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _33_2232 = (new_evar r xs t_x)
in (match (_33_2232) with
| (gi_xs, gi) -> begin
(let gi_xs = (Microsoft_FStar_Tc_Normalize.eta_expand_exp env gi_xs)
in (let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (gi, ps) (Some (t_x)) r)
in (let subst = (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder hd)) with
| true -> begin
subst
end
| false -> begin
(Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, gi_xs)))::subst
end)
in (let _68_13941 = (Microsoft_FStar_Absyn_Syntax.varg gi_xs)
in (let _68_13940 = (Microsoft_FStar_Absyn_Syntax.varg gi_ps)
in (_68_13941, _68_13940, subst))))))
end)))
end)
in (match (_33_2239) with
| (gi_xs, gi_ps, subst) -> begin
(let _33_2242 = (aux subst tl)
in (match (_33_2242) with
| (gi_xs', gi_ps') -> begin
((gi_xs)::gi_xs', (gi_ps)::gi_ps')
end))
end))
end))
in (aux [] bs))
end)))
in (match ((let _68_13943 = (let _68_13942 = (Support.List.nth xs i)
in (Support.Prims.pipe_left Support.Prims.fst _68_13942))
in ((Support.Prims.fst pi), _68_13943))) with
| (Support.Microsoft.FStar.Util.Inl (pi), Support.Microsoft.FStar.Util.Inl (xi)) -> begin
(match ((let _68_13944 = (matches pi)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_13944))) with
| true -> begin
None
end
| false -> begin
(let _33_2251 = (gs xi.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_33_2251) with
| (g_xs, _) -> begin
(let xi = (Microsoft_FStar_Absyn_Util.btvar_to_typ xi)
in (let proj = (let _68_13946 = (let _68_13945 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (xi, g_xs) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)
in (xs, _68_13945))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_13946 None r))
in (let sub = (let _68_13952 = (let _68_13951 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (proj, ps) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)
in (let _68_13950 = (let _68_13949 = (Support.List.map (fun ( _33_2259 ) -> (match (_33_2259) with
| (_, _, y) -> begin
y
end)) qs)
in (Support.Prims.pipe_left h _68_13949))
in (mk_problem (p_scope orig) orig _68_13951 (p_rel orig) _68_13950 None "projection")))
in (Support.Prims.pipe_left (fun ( _68_13947 ) -> TProb (_68_13947)) _68_13952))
in (let _33_2261 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_13954 = (Microsoft_FStar_Absyn_Print.typ_to_string proj)
in (let _68_13953 = (prob_to_string env sub)
in (Support.Microsoft.FStar.Util.fprint2 "Projecting %s\n\tsubprob=%s\n" _68_13954 _68_13953)))
end
| false -> begin
()
end)
in (let wl = (let _68_13956 = (let _68_13955 = (Support.Prims.pipe_left Support.Prims.fst (p_guard sub))
in Some (_68_13955))
in (solve_prob orig _68_13956 ((UT ((u, proj)))::[]) wl))
in (let _68_13958 = (solve env (attempt ((sub)::[]) wl))
in (Support.Prims.pipe_left (fun ( _68_13957 ) -> Some (_68_13957)) _68_13958)))))))
end))
end)
end
| _ -> begin
None
end))))
end)))
in (let solve_t_flex_rigid = (fun ( orig ) ( lhs ) ( t2 ) ( wl ) -> (let _33_2277 = lhs
in (match (_33_2277) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(let subterms = (fun ( ps ) -> (let xs = (let _68_13985 = (Microsoft_FStar_Absyn_Util.kind_formals k)
in (Support.Prims.pipe_right _68_13985 Support.Prims.fst))
in (let xs = (Microsoft_FStar_Absyn_Util.name_binders xs)
in (let _68_13990 = (decompose_typ env t2)
in ((uv, k), ps, xs, _68_13990)))))
in (let rec imitate_or_project = (fun ( n ) ( st ) ( i ) -> (match ((i >= n)) with
| true -> begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end
| false -> begin
(match ((i = (- (1)))) with
| true -> begin
(match ((imitate_t orig env wl st)) with
| Failed (_) -> begin
(imitate_or_project n st (i + 1))
end
| sol -> begin
sol
end)
end
| false -> begin
(match ((project_t orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(imitate_or_project n st (i + 1))
end
| Some (sol) -> begin
sol
end)
end)
end))
in (let check_head = (fun ( fvs1 ) ( t2 ) -> (let _33_2303 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (match (_33_2303) with
| (hd, _) -> begin
(match (hd.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| _ -> begin
(let fvs_hd = (Microsoft_FStar_Absyn_Util.freevars_typ hd)
in (match ((Microsoft_FStar_Absyn_Util.fvs_included fvs_hd fvs1)) with
| true -> begin
true
end
| false -> begin
(let _33_2316 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14001 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs_hd)
in (Support.Microsoft.FStar.Util.fprint1 "Free variables are %s" _68_14001))
end
| false -> begin
()
end)
in false)
end))
end)
end)))
in (let imitate_ok = (fun ( t2 ) -> (let fvs_hd = (let _68_14005 = (let _68_14004 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (Support.Prims.pipe_right _68_14004 Support.Prims.fst))
in (Support.Prims.pipe_right _68_14005 Microsoft_FStar_Absyn_Util.freevars_typ))
in (match ((Support.Microsoft.FStar.Util.set_is_empty fvs_hd.Microsoft_FStar_Absyn_Syntax.ftvs)) with
| true -> begin
(- (1))
end
| false -> begin
0
end)))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(let t1 = (sn env t1)
in (let t2 = (sn env t2)
in (let fvs1 = (Microsoft_FStar_Absyn_Util.freevars_typ t1)
in (let fvs2 = (Microsoft_FStar_Absyn_Util.freevars_typ t2)
in (let _33_2329 = (occurs_check env wl (uv, k) t2)
in (match (_33_2329) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(let _68_14007 = (let _68_14006 = (Support.Option.get msg)
in (Support.String.strcat "occurs-check failed: " _68_14006))
in (giveup_or_defer orig _68_14007))
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Util.fvs_included fvs2 fvs1)) with
| true -> begin
(match (((Microsoft_FStar_Absyn_Util.is_function_typ t2) && ((p_rel orig) <> EQ))) with
| true -> begin
(let _68_14008 = (subterms args_lhs)
in (imitate_t orig env wl _68_14008))
end
| false -> begin
(let _33_2330 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14011 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _68_14010 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs1)
in (let _68_14009 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs2)
in (Support.Microsoft.FStar.Util.fprint3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _68_14011 _68_14010 _68_14009))))
end
| false -> begin
()
end)
in (let sol = (match (vars) with
| [] -> begin
t2
end
| _ -> begin
(let _68_14013 = (let _68_14012 = (sn_binders env vars)
in (_68_14012, t2))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_14013 None t1.Microsoft_FStar_Absyn_Syntax.pos))
end)
in (let wl = (solve_prob orig None ((UT (((uv, k), sol)))::[]) wl)
in (solve env wl))))
end)
end
| false -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end
| false -> begin
(match ((check_head fvs1 t2)) with
| true -> begin
(let _33_2337 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14016 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _68_14015 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs1)
in (let _68_14014 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs2)
in (Support.Microsoft.FStar.Util.fprint3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _68_14016 _68_14015 _68_14014))))
end
| false -> begin
()
end)
in (let _68_14017 = (subterms args_lhs)
in (imitate_or_project (Support.List.length args_lhs) _68_14017 (- (1)))))
end
| false -> begin
(giveup env "free-variable check failed on a non-redex" orig)
end)
end)
end)
end)
end))))))
end
| None -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "not a pattern" orig wl))
end
| false -> begin
(match ((let _68_14018 = (Microsoft_FStar_Absyn_Util.freevars_typ t1)
in (check_head _68_14018 t2))) with
| true -> begin
(let im_ok = (imitate_ok t2)
in (let _33_2341 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14019 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Support.Microsoft.FStar.Util.fprint2 "Not a pattern (%s) ... %s\n" _68_14019 (match ((im_ok < 0)) with
| true -> begin
"imitating"
end
| false -> begin
"projecting"
end)))
end
| false -> begin
()
end)
in (let _68_14020 = (subterms args_lhs)
in (imitate_or_project (Support.List.length args_lhs) _68_14020 im_ok))))
end
| false -> begin
(giveup env "head-symbol is free" orig)
end)
end)
end)))))
end)))
in (let flex_flex = (fun ( orig ) ( lhs ) ( rhs ) -> (match ((wl.defer_ok && ((p_rel orig) <> EQ))) with
| true -> begin
(solve env (defer "flex-flex deferred" orig wl))
end
| false -> begin
(let force_quasi_pattern = (fun ( xs_opt ) ( _33_2353 ) -> (match (_33_2353) with
| (t, u, k, args) -> begin
(let rec aux = (fun ( binders ) ( ys ) ( args ) -> (match (args) with
| [] -> begin
(let ys = (Support.List.rev ys)
in (let binders = (Support.List.rev binders)
in (let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (let _33_2365 = (new_tvar t.Microsoft_FStar_Absyn_Syntax.pos ys kk)
in (match (_33_2365) with
| (t', _) -> begin
(let _33_2371 = (destruct_flex_t t')
in (match (_33_2371) with
| (u1_ys, u1, k1, _) -> begin
(let sol = (let _68_14038 = (let _68_14037 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, u1_ys) (Some (k)) t.Microsoft_FStar_Absyn_Syntax.pos)
in ((u, k), _68_14037))
in UT (_68_14038))
in (sol, (t', u, k1, ys)))
end))
end)))))
end
| hd::tl -> begin
(let new_binder = (fun ( hd ) -> (match ((Support.Prims.fst hd)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _68_14042 = (let _68_14041 = (Microsoft_FStar_Tc_Recheck.recompute_kind a)
in (Support.Prims.pipe_right _68_14041 (Microsoft_FStar_Absyn_Util.gen_bvar_p a.Microsoft_FStar_Absyn_Syntax.pos)))
in (Support.Prims.pipe_right _68_14042 Microsoft_FStar_Absyn_Syntax.t_binder))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _68_14044 = (let _68_14043 = (Microsoft_FStar_Tc_Recheck.recompute_typ x)
in (Support.Prims.pipe_right _68_14043 (Microsoft_FStar_Absyn_Util.gen_bvar_p x.Microsoft_FStar_Absyn_Syntax.pos)))
in (Support.Prims.pipe_right _68_14044 Microsoft_FStar_Absyn_Syntax.v_binder))
end))
in (let _33_2390 = (match ((pat_var_opt env ys hd)) with
| None -> begin
(let _68_14045 = (new_binder hd)
in (_68_14045, ys))
end
| Some (y) -> begin
(match (xs_opt) with
| None -> begin
(y, (y)::ys)
end
| Some (xs) -> begin
(match ((Support.Prims.pipe_right xs (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Util.eq_binder y)))) with
| true -> begin
(y, (y)::ys)
end
| false -> begin
(let _68_14046 = (new_binder hd)
in (_68_14046, ys))
end)
end)
end)
in (match (_33_2390) with
| (binder, ys) -> begin
(aux ((binder)::binders) ys tl)
end)))
end))
in (aux [] [] args))
end))
in (let solve_both_pats = (fun ( wl ) ( _33_2396 ) ( _33_2400 ) ( k ) ( r ) -> (match ((_33_2396, _33_2400)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
(match (((Support.Microsoft.FStar.Unionfind.equivalent u1 u2) && (binders_eq xs ys))) with
| true -> begin
(let _68_14057 = (solve_prob orig None [] wl)
in (solve env _68_14057))
end
| false -> begin
(let xs = (sn_binders env xs)
in (let ys = (sn_binders env ys)
in (let zs = (intersect_vars xs ys)
in (let _33_2409 = (new_tvar r zs k)
in (match (_33_2409) with
| (u_zs, _) -> begin
(let sub1 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' (xs, u_zs) (Some (k1)) r)
in (let _33_2413 = (occurs_check env wl (u1, k1) sub1)
in (match (_33_2413) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end
| false -> begin
(let sol1 = UT (((u1, k1), sub1))
in (match ((Support.Microsoft.FStar.Unionfind.equivalent u1 u2)) with
| true -> begin
(let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end
| false -> begin
(let sub2 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' (ys, u_zs) (Some (k2)) r)
in (let _33_2419 = (occurs_check env wl (u2, k2) sub2)
in (match (_33_2419) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end
| false -> begin
(let sol2 = UT (((u2, k2), sub2))
in (let wl = (solve_prob orig None ((sol1)::(sol2)::[]) wl)
in (solve env wl)))
end)
end)))
end))
end)
end)))
end)))))
end)
end))
in (let solve_one_pat = (fun ( _33_2427 ) ( _33_2432 ) -> (match ((_33_2427, _33_2432)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(let _33_2433 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14063 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _68_14062 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (Support.Microsoft.FStar.Util.fprint2 "Trying flex-flex one pattern (%s) with %s\n" _68_14063 _68_14062)))
end
| false -> begin
()
end)
in (match ((Support.Microsoft.FStar.Unionfind.equivalent u1 u2)) with
| true -> begin
(let sub_probs = (Support.List.map2 (fun ( a ) ( b ) -> (let a = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder a)
in (match (((Support.Prims.fst a), (Support.Prims.fst b))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
(let _68_14067 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (Support.Prims.pipe_right _68_14067 (fun ( _68_14066 ) -> TProb (_68_14066))))
end
| (Support.Microsoft.FStar.Util.Inr (t1), Support.Microsoft.FStar.Util.Inr (t2)) -> begin
(let _68_14069 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (Support.Prims.pipe_right _68_14069 (fun ( _68_14068 ) -> EProb (_68_14068))))
end
| _ -> begin
(failwith ("Impossible"))
end))) xs args2)
in (let guard = (let _68_14071 = (Support.List.map (fun ( p ) -> (Support.Prims.pipe_right (p_guard p) Support.Prims.fst)) sub_probs)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _68_14071))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end
| false -> begin
(let t2 = (sn env t2)
in (let rhs_vars = (Microsoft_FStar_Absyn_Util.freevars_typ t2)
in (let _33_2459 = (occurs_check env wl (u1, k1) t2)
in (match (_33_2459) with
| (occurs_ok, _) -> begin
(let lhs_vars = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders xs)
in (match ((occurs_ok && (Microsoft_FStar_Absyn_Util.fvs_included rhs_vars lhs_vars))) with
| true -> begin
(let sol = (let _68_14073 = (let _68_14072 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' (xs, t2) (Some (k1)) t1.Microsoft_FStar_Absyn_Syntax.pos)
in ((u1, k1), _68_14072))
in UT (_68_14073))
in (let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end
| false -> begin
(match ((occurs_ok && (Support.Prims.pipe_left Support.Prims.op_Negation wl.defer_ok))) with
| true -> begin
(let _33_2470 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_33_2470) with
| (sol, (_, u2, k2, ys)) -> begin
(let wl = (extend_solution sol wl)
in (let _33_2472 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("QuasiPattern")))) with
| true -> begin
(let _68_14074 = (uvi_to_string env sol)
in (Support.Microsoft.FStar.Util.fprint1 "flex-flex quasi pattern (2): %s\n" _68_14074))
end
| false -> begin
()
end)
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _ -> begin
(giveup env "impossible" orig)
end)))
end))
end
| false -> begin
(giveup_or_defer orig "flex-flex constraint")
end)
end))
end))))
end))
end))
in (let _33_2482 = lhs
in (match (_33_2482) with
| (t1, u1, k1, args1) -> begin
(let _33_2487 = rhs
in (match (_33_2487) with
| (t2, u2, k2, args2) -> begin
(let maybe_pat_vars1 = (pat_vars env [] args1)
in (let maybe_pat_vars2 = (pat_vars env [] args2)
in (let r = t2.Microsoft_FStar_Absyn_Syntax.pos
in (match ((maybe_pat_vars1, maybe_pat_vars2)) with
| (Some (xs), Some (ys)) -> begin
(let _68_14075 = (Microsoft_FStar_Tc_Recheck.recompute_kind t2)
in (solve_both_pats wl (u1, k1, xs) (u2, k2, ys) _68_14075 t2.Microsoft_FStar_Absyn_Syntax.pos))
end
| (Some (xs), None) -> begin
(solve_one_pat (t1, u1, k1, xs) rhs)
end
| (None, Some (ys)) -> begin
(solve_one_pat (t2, u2, k2, ys) lhs)
end
| _ -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end
| false -> begin
(let _33_2509 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_33_2509) with
| (sol, _) -> begin
(let wl = (extend_solution sol wl)
in (let _33_2511 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("QuasiPattern")))) with
| true -> begin
(let _68_14076 = (uvi_to_string env sol)
in (Support.Microsoft.FStar.Util.fprint1 "flex-flex quasi pattern (1): %s\n" _68_14076))
end
| false -> begin
()
end)
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _ -> begin
(giveup env "impossible" orig)
end)))
end))
end)
end))))
end))
end)))))
end))
in (let orig = TProb (problem)
in (match ((Support.Microsoft.FStar.Util.physical_equality problem.lhs problem.rhs)) with
| true -> begin
(let _68_14077 = (solve_prob orig None [] wl)
in (solve env _68_14077))
end
| false -> begin
(let t1 = problem.lhs
in (let t2 = problem.rhs
in (match ((Support.Microsoft.FStar.Util.physical_equality t1 t2)) with
| true -> begin
(let _68_14078 = (solve_prob orig None [] wl)
in (solve env _68_14078))
end
| false -> begin
(let _33_2520 = (match ((Microsoft_FStar_Tc_Env.debug env (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14081 = (prob_to_string env orig)
in (let _68_14080 = (let _68_14079 = (Support.List.map (uvi_to_string wl.tcenv) wl.subst)
in (Support.Prims.pipe_right _68_14079 (Support.String.concat "; ")))
in (Support.Microsoft.FStar.Util.fprint2 "Attempting %s\n\tSubst is %s\n" _68_14081 _68_14080)))
end
| false -> begin
()
end)
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let match_num_binders = (fun ( _33_2525 ) ( _33_2528 ) -> (match ((_33_2525, _33_2528)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(let curry = (fun ( n ) ( bs ) ( mk_cod ) -> (let _33_2535 = (Support.Microsoft.FStar.Util.first_N n bs)
in (match (_33_2535) with
| (bs, rest) -> begin
(let _68_14111 = (mk_cod rest)
in (bs, _68_14111))
end)))
in (let l1 = (Support.List.length bs1)
in (let l2 = (Support.List.length bs2)
in (match ((l1 = l2)) with
| true -> begin
(let _68_14115 = (let _68_14112 = (mk_cod1 [])
in (bs1, _68_14112))
in (let _68_14114 = (let _68_14113 = (mk_cod2 [])
in (bs2, _68_14113))
in (_68_14115, _68_14114)))
end
| false -> begin
(match ((l1 > l2)) with
| true -> begin
(let _68_14118 = (curry l2 bs1 mk_cod1)
in (let _68_14117 = (let _68_14116 = (mk_cod2 [])
in (bs2, _68_14116))
in (_68_14118, _68_14117)))
end
| false -> begin
(let _68_14121 = (let _68_14119 = (mk_cod1 [])
in (bs1, _68_14119))
in (let _68_14120 = (curry l1 bs2 mk_cod2)
in (_68_14121, _68_14120)))
end)
end))))
end))
in (match ((t1.Microsoft_FStar_Absyn_Syntax.n, t2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvd_eq a.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(let _68_14122 = (solve_prob orig None [] wl)
in (solve env _68_14122))
end
| false -> begin
(let _68_14126 = (let _68_14125 = (let _68_14124 = (Microsoft_FStar_Absyn_Util.mk_eq_typ t1 t2)
in (Support.Prims.pipe_left (fun ( _68_14123 ) -> Some (_68_14123)) _68_14124))
in (solve_prob orig _68_14125 [] wl))
in (solve env _68_14126))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs1, c1)), Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs2, c2))) -> begin
(let mk_c = (fun ( c ) ( _33_31 ) -> (match (_33_31) with
| [] -> begin
c
end
| bs -> begin
(let _68_14131 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None c.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Total _68_14131))
end))
in (let _33_2566 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_33_2566) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun ( scope ) ( env ) ( subst ) -> (let c1 = (Microsoft_FStar_Absyn_Util.subst_comp subst c1)
in (let rel = (match ((Support.ST.read Microsoft_FStar_Options.use_eq_at_higher_order)) with
| true -> begin
EQ
end
| false -> begin
problem.relation
end)
in (let _33_2572 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("EQ")))) with
| true -> begin
(let _68_14138 = (let _68_14137 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.Prims.pipe_right _68_14137 Support.Microsoft.FStar.Range.string_of_range))
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Using relation %s at higher order\n" _68_14138 (rel_to_string rel)))
end
| false -> begin
()
end)
in (let _68_14140 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (Support.Prims.pipe_left (fun ( _68_14139 ) -> CProb (_68_14139)) _68_14140)))))))
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs1, t1')), Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs2, t2'))) -> begin
(let mk_t = (fun ( t ) ( _33_32 ) -> (match (_33_32) with
| [] -> begin
t
end
| bs -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (let _33_2594 = (match_num_binders (bs1, (mk_t t1')) (bs2, (mk_t t2')))
in (match (_33_2594) with
| ((bs1, t1'), (bs2, t2')) -> begin
(solve_binders env bs1 bs2 orig wl (fun ( scope ) ( env ) ( subst ) -> (let t1' = (Microsoft_FStar_Absyn_Util.subst_typ subst t1')
in (let _68_14151 = (mk_problem scope orig t1' problem.relation t2' None "lambda co-domain")
in (Support.Prims.pipe_left (fun ( _68_14150 ) -> TProb (_68_14150)) _68_14151)))))
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine (_), Microsoft_FStar_Absyn_Syntax.Typ_refine (_)) -> begin
(let _33_2608 = (as_refinement env wl t1)
in (match (_33_2608) with
| (x1, phi1) -> begin
(let _33_2611 = (as_refinement env wl t2)
in (match (_33_2611) with
| (x2, phi2) -> begin
(let base_prob = (let _68_14153 = (mk_problem (p_scope orig) orig x1.Microsoft_FStar_Absyn_Syntax.sort problem.relation x2.Microsoft_FStar_Absyn_Syntax.sort problem.element "refinement base type")
in (Support.Prims.pipe_left (fun ( _68_14152 ) -> TProb (_68_14152)) _68_14153))
in (let x1_for_x2 = (let _68_14155 = (Microsoft_FStar_Absyn_Syntax.v_binder x1)
in (let _68_14154 = (Microsoft_FStar_Absyn_Syntax.v_binder x2)
in (Microsoft_FStar_Absyn_Util.mk_subst_one_binder _68_14155 _68_14154)))
in (let phi2 = (Microsoft_FStar_Absyn_Util.subst_typ x1_for_x2 phi2)
in (let mk_imp = (fun ( imp ) ( phi1 ) ( phi2 ) -> (let _68_14172 = (imp phi1 phi2)
in (Support.Prims.pipe_right _68_14172 (guard_on_element problem x1))))
in (let fallback = (fun ( _33_2620 ) -> (match (()) with
| () -> begin
(let impl = (match ((problem.relation = EQ)) with
| true -> begin
(mk_imp Microsoft_FStar_Absyn_Util.mk_iff phi1 phi2)
end
| false -> begin
(mk_imp Microsoft_FStar_Absyn_Util.mk_imp phi1 phi2)
end)
in (let guard = (let _68_14175 = (Support.Prims.pipe_right (p_guard base_prob) Support.Prims.fst)
in (Microsoft_FStar_Absyn_Util.mk_conj _68_14175 impl))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in (match ((problem.relation = EQ)) with
| true -> begin
(let ref_prob = (let _68_14177 = (mk_problem (p_scope orig) orig phi1 EQ phi2 None "refinement formula")
in (Support.Prims.pipe_left (fun ( _68_14176 ) -> TProb (_68_14176)) _68_14177))
in (match ((solve env (let _33_2625 = wl
in {attempting = (ref_prob)::[]; deferred = []; subst = _33_2625.subst; ctr = _33_2625.ctr; slack_vars = _33_2625.slack_vars; defer_ok = false; smt_ok = _33_2625.smt_ok; tcenv = _33_2625.tcenv}))) with
| Failed (_) -> begin
(fallback ())
end
| Success ((subst, _)) -> begin
(let guard = (let _68_14180 = (Support.Prims.pipe_right (p_guard base_prob) Support.Prims.fst)
in (let _68_14179 = (let _68_14178 = (Support.Prims.pipe_right (p_guard ref_prob) Support.Prims.fst)
in (Support.Prims.pipe_right _68_14178 (guard_on_element problem x1)))
in (Microsoft_FStar_Absyn_Util.mk_conj _68_14180 _68_14179)))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl))))
end))
end
| false -> begin
(fallback ())
end))))))
end))
end))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), Microsoft_FStar_Absyn_Syntax.Typ_uvar (_))) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), Microsoft_FStar_Absyn_Syntax.Typ_uvar (_))) | ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) -> begin
(let _68_14182 = (destruct_flex_t t1)
in (let _68_14181 = (destruct_flex_t t2)
in (flex_flex orig _68_14182 _68_14181)))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _)) when (problem.relation = EQ) -> begin
(let _68_14183 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _68_14183 t2 wl))
end
| ((_, Microsoft_FStar_Absyn_Syntax.Typ_uvar (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) when (problem.relation = EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| false -> begin
(let new_rel = (match ((Support.ST.read Microsoft_FStar_Options.no_slack)) with
| true -> begin
EQ
end
| false -> begin
problem.relation
end)
in (match ((let _68_14184 = (is_top_level_prob orig)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_14184))) with
| true -> begin
(let _68_14187 = (Support.Prims.pipe_left (fun ( _68_14185 ) -> TProb (_68_14185)) (let _33_2793 = problem
in {lhs = _33_2793.lhs; relation = new_rel; rhs = _33_2793.rhs; element = _33_2793.element; logical_guard = _33_2793.logical_guard; scope = _33_2793.scope; reason = _33_2793.reason; loc = _33_2793.loc; rank = _33_2793.rank}))
in (let _68_14186 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _68_14187 _68_14186 t2 wl)))
end
| false -> begin
(let _33_2797 = (base_and_refinement env wl t2)
in (match (_33_2797) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _68_14190 = (Support.Prims.pipe_left (fun ( _68_14188 ) -> TProb (_68_14188)) (let _33_2799 = problem
in {lhs = _33_2799.lhs; relation = new_rel; rhs = _33_2799.rhs; element = _33_2799.element; logical_guard = _33_2799.logical_guard; scope = _33_2799.scope; reason = _33_2799.reason; loc = _33_2799.loc; rank = _33_2799.rank}))
in (let _68_14189 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _68_14190 _68_14189 t_base wl)))
end
| Some ((y, phi)) -> begin
(let y' = (let _33_2805 = y
in {Microsoft_FStar_Absyn_Syntax.v = _33_2805.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t1; Microsoft_FStar_Absyn_Syntax.p = _33_2805.Microsoft_FStar_Absyn_Syntax.p})
in (let impl = (guard_on_element problem y' phi)
in (let base_prob = (let _68_14192 = (mk_problem problem.scope orig t1 new_rel y.Microsoft_FStar_Absyn_Syntax.sort problem.element "flex-rigid: base type")
in (Support.Prims.pipe_left (fun ( _68_14191 ) -> TProb (_68_14191)) _68_14192))
in (let guard = (let _68_14193 = (Support.Prims.pipe_right (p_guard base_prob) Support.Prims.fst)
in (Microsoft_FStar_Absyn_Util.mk_conj _68_14193 impl))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))))
end)
end))
end))
end)
end
| ((_, Microsoft_FStar_Absyn_Syntax.Typ_uvar (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| false -> begin
(let _33_2840 = (base_and_refinement env wl t1)
in (match (_33_2840) with
| (t_base, _) -> begin
(solve_t env (let _33_2841 = problem
in {lhs = t_base; relation = EQ; rhs = _33_2841.rhs; element = _33_2841.element; logical_guard = _33_2841.logical_guard; scope = _33_2841.scope; reason = _33_2841.reason; loc = _33_2841.loc; rank = _33_2841.rank}) wl)
end))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine (_), _) -> begin
(let t2 = (let _68_14194 = (base_and_refinement env wl t2)
in (Support.Prims.pipe_left force_refinement _68_14194))
in (solve_t env (let _33_2850 = problem
in {lhs = _33_2850.lhs; relation = _33_2850.relation; rhs = t2; element = _33_2850.element; logical_guard = _33_2850.logical_guard; scope = _33_2850.scope; reason = _33_2850.reason; loc = _33_2850.loc; rank = _33_2850.rank}) wl))
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_refine (_)) -> begin
(let t1 = (let _68_14195 = (base_and_refinement env wl t1)
in (Support.Prims.pipe_left force_refinement _68_14195))
in (solve_t env (let _33_2859 = problem
in {lhs = t1; relation = _33_2859.relation; rhs = _33_2859.rhs; element = _33_2859.element; logical_guard = _33_2859.logical_guard; scope = _33_2859.scope; reason = _33_2859.reason; loc = _33_2859.loc; rank = _33_2859.rank}) wl))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_const (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_btvar (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_const (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_app (_))) -> begin
(let _33_2899 = (head_matches_delta env wl t1 t2)
in (match (_33_2899) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch, _) -> begin
(let head1 = (let _68_14196 = (Microsoft_FStar_Absyn_Util.head_and_args t1)
in (Support.Prims.pipe_right _68_14196 Support.Prims.fst))
in (let head2 = (let _68_14197 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (Support.Prims.pipe_right _68_14197 Support.Prims.fst))
in (let may_equate = (fun ( head ) -> (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (_) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) -> begin
(Microsoft_FStar_Tc_Env.is_projector env tc.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
false
end))
in (match ((((may_equate head1) || (may_equate head2)) && wl.smt_ok)) with
| true -> begin
(let _68_14203 = (let _68_14202 = (let _68_14201 = (Microsoft_FStar_Absyn_Util.mk_eq_typ t1 t2)
in (Support.Prims.pipe_left (fun ( _68_14200 ) -> Some (_68_14200)) _68_14201))
in (solve_prob orig _68_14202 [] wl))
in (solve env _68_14203))
end
| false -> begin
(giveup env "head mismatch" orig)
end))))
end
| (_, Some ((t1, t2))) -> begin
(solve_t env (let _33_2922 = problem
in {lhs = t1; relation = _33_2922.relation; rhs = t2; element = _33_2922.element; logical_guard = _33_2922.logical_guard; scope = _33_2922.scope; reason = _33_2922.reason; loc = _33_2922.loc; rank = _33_2922.rank}) wl)
end
| (_, None) -> begin
(let _33_2928 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14205 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _68_14204 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (Support.Microsoft.FStar.Util.fprint2 "Head matches: %s and %s\n" _68_14205 _68_14204)))
end
| false -> begin
()
end)
in (let _33_2932 = (Microsoft_FStar_Absyn_Util.head_and_args t1)
in (match (_33_2932) with
| (head, args) -> begin
(let _33_2935 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (match (_33_2935) with
| (head', args') -> begin
(let nargs = (Support.List.length args)
in (match ((nargs <> (Support.List.length args'))) with
| true -> begin
(let _68_14210 = (let _68_14209 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (let _68_14208 = (Microsoft_FStar_Absyn_Print.args_to_string args)
in (let _68_14207 = (Microsoft_FStar_Absyn_Print.typ_to_string head')
in (let _68_14206 = (Microsoft_FStar_Absyn_Print.args_to_string args')
in (Support.Microsoft.FStar.Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _68_14209 _68_14208 _68_14207 _68_14206)))))
in (giveup env _68_14210 orig))
end
| false -> begin
(match (((nargs = 0) || (eq_args args args'))) with
| true -> begin
(let _68_14211 = (solve_prob orig None [] wl)
in (solve env _68_14211))
end
| false -> begin
(let _33_2939 = (base_and_refinement env wl t1)
in (match (_33_2939) with
| (base1, refinement1) -> begin
(let _33_2942 = (base_and_refinement env wl t2)
in (match (_33_2942) with
| (base2, refinement2) -> begin
(match ((refinement1, refinement2)) with
| (None, None) -> begin
(let _33_2946 = (match (((head_matches head head) <> FullMatch)) with
| true -> begin
(let _68_14214 = (let _68_14213 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (let _68_14212 = (Microsoft_FStar_Absyn_Print.typ_to_string head')
in (Support.Microsoft.FStar.Util.format2 "Assertion failed: expected full match of %s and %s\n" _68_14213 _68_14212)))
in (failwith (_68_14214)))
end
| false -> begin
()
end)
in (let subprobs = (Support.List.map2 (fun ( a ) ( a' ) -> (match (((Support.Prims.fst a), (Support.Prims.fst a'))) with
| (Support.Microsoft.FStar.Util.Inl (t), Support.Microsoft.FStar.Util.Inl (t')) -> begin
(let _68_14218 = (mk_problem (p_scope orig) orig t EQ t' None "type index")
in (Support.Prims.pipe_left (fun ( _68_14217 ) -> TProb (_68_14217)) _68_14218))
end
| (Support.Microsoft.FStar.Util.Inr (v), Support.Microsoft.FStar.Util.Inr (v')) -> begin
(let _68_14220 = (mk_problem (p_scope orig) orig v EQ v' None "term index")
in (Support.Prims.pipe_left (fun ( _68_14219 ) -> EProb (_68_14219)) _68_14220))
end
| _ -> begin
(failwith ("Impossible"))
end)) args args')
in (let formula = (let _68_14222 = (Support.List.map (fun ( p ) -> (Support.Prims.fst (p_guard p))) subprobs)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _68_14222))
in (let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl))))))
end
| _ -> begin
(let lhs = (force_refinement (base1, refinement1))
in (let rhs = (force_refinement (base2, refinement2))
in (solve_t env (let _33_2970 = problem
in {lhs = lhs; relation = _33_2970.relation; rhs = rhs; element = _33_2970.element; logical_guard = _33_2970.logical_guard; scope = _33_2970.scope; reason = _33_2970.reason; loc = _33_2970.loc; rank = _33_2970.rank}) wl)))
end)
end))
end))
end)
end))
end))
end)))
end)
end))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_meta (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_delayed (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_meta (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_delayed (_))) -> begin
(failwith ("Impossible"))
end
| _ -> begin
(giveup env "head mismatch" orig)
end))))
end)))
end))))))))
and solve_c = (fun ( env ) ( problem ) ( wl ) -> (let c1 = problem.lhs
in (let c2 = problem.rhs
in (let orig = CProb (problem)
in (let sub_prob = (fun ( t1 ) ( rel ) ( t2 ) ( reason ) -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (let solve_eq = (fun ( c1_comp ) ( c2_comp ) -> (let _33_3026 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("EQ")))) with
| true -> begin
(Support.Microsoft.FStar.Util.print_string "solve_c is using an equality constraint\n")
end
| false -> begin
()
end)
in (let sub_probs = (Support.List.map2 (fun ( arg1 ) ( arg2 ) -> (match (((Support.Prims.fst arg1), (Support.Prims.fst arg2))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
(let _68_14237 = (sub_prob t1 EQ t2 "effect arg")
in (Support.Prims.pipe_left (fun ( _68_14236 ) -> TProb (_68_14236)) _68_14237))
end
| (Support.Microsoft.FStar.Util.Inr (e1), Support.Microsoft.FStar.Util.Inr (e2)) -> begin
(let _68_14239 = (sub_prob e1 EQ e2 "effect arg")
in (Support.Prims.pipe_left (fun ( _68_14238 ) -> EProb (_68_14238)) _68_14239))
end
| _ -> begin
(failwith ("impossible"))
end)) c1_comp.Microsoft_FStar_Absyn_Syntax.effect_args c2_comp.Microsoft_FStar_Absyn_Syntax.effect_args)
in (let guard = (let _68_14241 = (Support.List.map (fun ( p ) -> (Support.Prims.pipe_right (p_guard p) Support.Prims.fst)) sub_probs)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _68_14241))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in (match ((Support.Microsoft.FStar.Util.physical_equality c1 c2)) with
| true -> begin
(let _68_14242 = (solve_prob orig None [] wl)
in (solve env _68_14242))
end
| false -> begin
(let _33_3046 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14244 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _68_14243 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (Support.Microsoft.FStar.Util.fprint3 "solve_c %s %s %s\n" _68_14244 (rel_to_string problem.relation) _68_14243)))
end
| false -> begin
()
end)
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let _33_3051 = (c1, c2)
in (match (_33_3051) with
| (c1_0, c2_0) -> begin
(match ((c1.Microsoft_FStar_Absyn_Syntax.n, c2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Total (t1), Microsoft_FStar_Absyn_Syntax.Total (t2)) -> begin
(solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl)
end
| (Microsoft_FStar_Absyn_Syntax.Total (_), Microsoft_FStar_Absyn_Syntax.Comp (_)) -> begin
(let _68_14246 = (let _33_3064 = problem
in (let _68_14245 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c1))
in {lhs = _68_14245; relation = _33_3064.relation; rhs = _33_3064.rhs; element = _33_3064.element; logical_guard = _33_3064.logical_guard; scope = _33_3064.scope; reason = _33_3064.reason; loc = _33_3064.loc; rank = _33_3064.rank}))
in (solve_c env _68_14246 wl))
end
| (Microsoft_FStar_Absyn_Syntax.Comp (_), Microsoft_FStar_Absyn_Syntax.Total (_)) -> begin
(let _68_14248 = (let _33_3073 = problem
in (let _68_14247 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c2))
in {lhs = _33_3073.lhs; relation = _33_3073.relation; rhs = _68_14247; element = _33_3073.element; logical_guard = _33_3073.logical_guard; scope = _33_3073.scope; reason = _33_3073.reason; loc = _33_3073.loc; rank = _33_3073.rank}))
in (solve_c env _68_14248 wl))
end
| (Microsoft_FStar_Absyn_Syntax.Comp (_), Microsoft_FStar_Absyn_Syntax.Comp (_)) -> begin
(match ((((Microsoft_FStar_Absyn_Util.is_ml_comp c1) && (Microsoft_FStar_Absyn_Util.is_ml_comp c2)) || ((Microsoft_FStar_Absyn_Util.is_total_comp c1) && ((Microsoft_FStar_Absyn_Util.is_total_comp c2) || (Microsoft_FStar_Absyn_Util.is_ml_comp c2))))) with
| true -> begin
(solve_t env (problem_using_guard orig (Microsoft_FStar_Absyn_Util.comp_result c1) problem.relation (Microsoft_FStar_Absyn_Util.comp_result c2) None "result type") wl)
end
| false -> begin
(let c1_comp = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c1)
in (let c2_comp = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c2)
in (match (((problem.relation = EQ) && (Microsoft_FStar_Absyn_Syntax.lid_equals c1_comp.Microsoft_FStar_Absyn_Syntax.effect_name c2_comp.Microsoft_FStar_Absyn_Syntax.effect_name))) with
| true -> begin
(solve_eq c1_comp c2_comp)
end
| false -> begin
(let c1 = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c1)
in (let c2 = (Microsoft_FStar_Tc_Normalize.weak_norm_comp env c2)
in (let _33_3086 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(Support.Microsoft.FStar.Util.fprint2 "solve_c for %s and %s\n" c1.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str c2.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str)
end
| false -> begin
()
end)
in (match ((Microsoft_FStar_Tc_Env.monad_leq env c1.Microsoft_FStar_Absyn_Syntax.effect_name c2.Microsoft_FStar_Absyn_Syntax.effect_name)) with
| None -> begin
(let _68_14251 = (let _68_14250 = (Microsoft_FStar_Absyn_Print.sli c1.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _68_14249 = (Microsoft_FStar_Absyn_Print.sli c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (Support.Microsoft.FStar.Util.format2 "incompatible monad ordering: %s </: %s" _68_14250 _68_14249)))
in (giveup env _68_14251 orig))
end
| Some (edge) -> begin
(match ((problem.relation = EQ)) with
| true -> begin
(let _33_3106 = (match (c1.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp1), _)::(Support.Microsoft.FStar.Util.Inl (wlp1), _)::[] -> begin
(wp1, wlp1)
end
| _ -> begin
(let _68_14254 = (let _68_14253 = (let _68_14252 = (Microsoft_FStar_Absyn_Syntax.range_of_lid c1.Microsoft_FStar_Absyn_Syntax.effect_name)
in (Support.Microsoft.FStar.Range.string_of_range _68_14252))
in (Support.Microsoft.FStar.Util.format1 "Unexpected number of indices on a normalized effect (%s)" _68_14253))
in (failwith (_68_14254)))
end)
in (match (_33_3106) with
| (wp, wlp) -> begin
(let c1 = (let _68_14260 = (let _68_14259 = (let _68_14255 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wp)
in (Microsoft_FStar_Absyn_Syntax.targ _68_14255))
in (let _68_14258 = (let _68_14257 = (let _68_14256 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wlp)
in (Microsoft_FStar_Absyn_Syntax.targ _68_14256))
in (_68_14257)::[])
in (_68_14259)::_68_14258))
in {Microsoft_FStar_Absyn_Syntax.effect_name = c2.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = c1.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _68_14260; Microsoft_FStar_Absyn_Syntax.flags = c1.Microsoft_FStar_Absyn_Syntax.flags})
in (solve_eq c1 c2))
end))
end
| false -> begin
(let is_null_wp_2 = (Support.Prims.pipe_right c2.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _33_33 ) -> (match (_33_33) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.MLEFFECT) | (Microsoft_FStar_Absyn_Syntax.SOMETRIVIAL) -> begin
true
end
| _ -> begin
false
end))))
in (let _33_3136 = (match ((c1.Microsoft_FStar_Absyn_Syntax.effect_args, c2.Microsoft_FStar_Absyn_Syntax.effect_args)) with
| ((Support.Microsoft.FStar.Util.Inl (wp1), _)::_, (Support.Microsoft.FStar.Util.Inl (wp2), _)::_) -> begin
(wp1, wp2)
end
| _ -> begin
(let _68_14264 = (let _68_14263 = (Microsoft_FStar_Absyn_Print.sli c1.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _68_14262 = (Microsoft_FStar_Absyn_Print.sli c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (Support.Microsoft.FStar.Util.format2 "Got effects %s and %s, expected normalized effects" _68_14263 _68_14262)))
in (failwith (_68_14264)))
end)
in (match (_33_3136) with
| (wpc1, wpc2) -> begin
(match ((Support.Microsoft.FStar.Util.physical_equality wpc1 wpc2)) with
| true -> begin
(solve_t env (problem_using_guard orig c1.Microsoft_FStar_Absyn_Syntax.result_typ problem.relation c2.Microsoft_FStar_Absyn_Syntax.result_typ None "result type") wl)
end
| false -> begin
(let c2_decl = (Microsoft_FStar_Tc_Env.get_effect_decl env c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let g = (match (is_null_wp_2) with
| true -> begin
(let _33_3138 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(Support.Microsoft.FStar.Util.print_string "Using trivial wp ... \n")
end
| false -> begin
()
end)
in (let _68_14270 = (let _68_14269 = (let _68_14268 = (Microsoft_FStar_Absyn_Syntax.targ c1.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _68_14267 = (let _68_14266 = (let _68_14265 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wpc1)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_14265))
in (_68_14266)::[])
in (_68_14268)::_68_14267))
in (c2_decl.Microsoft_FStar_Absyn_Syntax.trivial, _68_14269))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_14270 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)))
end
| false -> begin
(let wp2_imp_wp1 = (let _68_14282 = (let _68_14281 = (let _68_14280 = (Microsoft_FStar_Absyn_Syntax.targ c2.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _68_14279 = (let _68_14278 = (Microsoft_FStar_Absyn_Syntax.targ wpc2)
in (let _68_14277 = (let _68_14276 = (let _68_14272 = (let _68_14271 = (Microsoft_FStar_Absyn_Const.kbin Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.imp_lid _68_14271))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_14272))
in (let _68_14275 = (let _68_14274 = (let _68_14273 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wpc1)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_14273))
in (_68_14274)::[])
in (_68_14276)::_68_14275))
in (_68_14278)::_68_14277))
in (_68_14280)::_68_14279))
in (c2_decl.Microsoft_FStar_Absyn_Syntax.wp_binop, _68_14281))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_14282 None r))
in (let _68_14287 = (let _68_14286 = (let _68_14285 = (Microsoft_FStar_Absyn_Syntax.targ c2.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _68_14284 = (let _68_14283 = (Microsoft_FStar_Absyn_Syntax.targ wp2_imp_wp1)
in (_68_14283)::[])
in (_68_14285)::_68_14284))
in (c2_decl.Microsoft_FStar_Absyn_Syntax.wp_as_type, _68_14286))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_14287 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)))
end)
in (let base_prob = (let _68_14289 = (sub_prob c1.Microsoft_FStar_Absyn_Syntax.result_typ problem.relation c2.Microsoft_FStar_Absyn_Syntax.result_typ "result type")
in (Support.Prims.pipe_left (fun ( _68_14288 ) -> TProb (_68_14288)) _68_14289))
in (let wl = (let _68_14293 = (let _68_14292 = (let _68_14291 = (Support.Prims.pipe_right (p_guard base_prob) Support.Prims.fst)
in (Microsoft_FStar_Absyn_Util.mk_conj _68_14291 g))
in (Support.Prims.pipe_left (fun ( _68_14290 ) -> Some (_68_14290)) _68_14292))
in (solve_prob orig _68_14293 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end)
end)))
end)
end))))
end)))
end)
end)
end))))
end)))))))
and solve_e = (fun ( env ) ( problem ) ( wl ) -> (match ((compress_prob wl (EProb (problem)))) with
| EProb (p) -> begin
(solve_e' env p wl)
end
| _ -> begin
(failwith ("Impossible"))
end))
and solve_e' = (fun ( env ) ( problem ) ( wl ) -> (let problem = (let _33_3154 = problem
in {lhs = _33_3154.lhs; relation = EQ; rhs = _33_3154.rhs; element = _33_3154.element; logical_guard = _33_3154.logical_guard; scope = _33_3154.scope; reason = _33_3154.reason; loc = _33_3154.loc; rank = _33_3154.rank})
in (let e1 = problem.lhs
in (let e2 = problem.rhs
in (let orig = EProb (problem)
in (let sub_prob = (fun ( lhs ) ( rhs ) ( reason ) -> (mk_problem (p_scope orig) orig lhs EQ rhs None reason))
in (let _33_3166 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14303 = (prob_to_string env orig)
in (Support.Microsoft.FStar.Util.fprint1 "Attempting:\n%s\n" _68_14303))
end
| false -> begin
()
end)
in (let flex_rigid = (fun ( _33_3173 ) ( e2 ) -> (match (_33_3173) with
| (e1, u1, t1, args1) -> begin
(let maybe_vars1 = (pat_vars env [] args1)
in (let sub_problems = (fun ( xs ) ( args2 ) -> (let _33_3200 = (let _68_14319 = (Support.Prims.pipe_right args2 (Support.List.map (fun ( _33_34 ) -> (match (_33_34) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (let _33_3187 = (new_tvar t.Microsoft_FStar_Absyn_Syntax.pos xs kk)
in (match (_33_3187) with
| (gi_xi, gi) -> begin
(let gi_pi = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (gi, args1) (Some (kk)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_14315 = (let _68_14314 = (sub_prob gi_pi t "type index")
in (Support.Prims.pipe_left (fun ( _68_14313 ) -> TProb (_68_14313)) _68_14314))
in ((Support.Microsoft.FStar.Util.Inl (gi_xi), imp), _68_14315)))
end)))
end
| (Support.Microsoft.FStar.Util.Inr (v), imp) -> begin
(let tt = (Microsoft_FStar_Tc_Recheck.recompute_typ v)
in (let _33_3196 = (new_evar v.Microsoft_FStar_Absyn_Syntax.pos xs tt)
in (match (_33_3196) with
| (gi_xi, gi) -> begin
(let gi_pi = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (gi, args1) (Some (tt)) v.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_14318 = (let _68_14317 = (sub_prob gi_pi v "expression index")
in (Support.Prims.pipe_left (fun ( _68_14316 ) -> EProb (_68_14316)) _68_14317))
in ((Support.Microsoft.FStar.Util.Inr (gi_xi), imp), _68_14318)))
end)))
end))))
in (Support.Prims.pipe_right _68_14319 Support.List.unzip))
in (match (_33_3200) with
| (gi_xi, gi_pi) -> begin
(let formula = (let _68_14321 = (Support.List.map (fun ( p ) -> (Support.Prims.pipe_right (p_guard p) Support.Prims.fst)) gi_pi)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _68_14321))
in (gi_xi, gi_pi, formula))
end)))
in (let project_e = (fun ( head2 ) ( args2 ) -> (let giveup = (fun ( reason ) -> (let _68_14328 = (Support.Microsoft.FStar.Util.format1 "flex-rigid: refusing to project expressions (%s)" reason)
in (giveup env _68_14328 orig)))
in (match ((let _68_14329 = (Microsoft_FStar_Absyn_Util.compress_exp head2)
in _68_14329.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (y) -> begin
(let _33_3217 = (match ((Microsoft_FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some ((xs, c)) -> begin
(xs, (Microsoft_FStar_Absyn_Util.comp_result c))
end)
in (match (_33_3217) with
| (all_xs, tres) -> begin
(match (((Support.List.length all_xs) <> (Support.List.length args1))) with
| true -> begin
(let _68_14332 = (let _68_14331 = (Microsoft_FStar_Absyn_Print.binders_to_string ", " all_xs)
in (let _68_14330 = (Microsoft_FStar_Absyn_Print.args_to_string args2)
in (Support.Microsoft.FStar.Util.format2 "unequal arity:\n\texpetced binders %s\n\tgot args {%s}" _68_14331 _68_14330)))
in (giveup _68_14332))
end
| false -> begin
(let rec aux = (fun ( xs ) ( args ) -> (match ((xs, args)) with
| ([], []) -> begin
(giveup "variable to project not found")
end
| (([], _)) | ((_, [])) -> begin
(failwith ("impossible"))
end
| ((Support.Microsoft.FStar.Util.Inl (_), _)::xs, (Support.Microsoft.FStar.Util.Inl (_), _)::args) -> begin
(aux xs args)
end
| ((Support.Microsoft.FStar.Util.Inr (xi), _)::xs, (Support.Microsoft.FStar.Util.Inr (arg), _)::args) -> begin
(match ((let _68_14337 = (Microsoft_FStar_Absyn_Util.compress_exp arg)
in _68_14337.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (z) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvar_eq y z)) with
| true -> begin
(let _33_3269 = (sub_problems all_xs args2)
in (match (_33_3269) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (let _68_14341 = (let _68_14340 = (let _68_14339 = (let _68_14338 = (Microsoft_FStar_Absyn_Util.bvar_to_exp xi)
in (_68_14338, gi_xi))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _68_14339 None e1.Microsoft_FStar_Absyn_Syntax.pos))
in (all_xs, _68_14340))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _68_14341 None e1.Microsoft_FStar_Absyn_Syntax.pos))
in (let _33_3271 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14345 = (Microsoft_FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _68_14344 = (Microsoft_FStar_Absyn_Print.exp_to_string sol)
in (let _68_14343 = (let _68_14342 = (Support.Prims.pipe_right gi_pi (Support.List.map (prob_to_string env)))
in (Support.Prims.pipe_right _68_14342 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.fprint3 "Projected: %s -> %s\nSubprobs=\n%s\n" _68_14345 _68_14344 _68_14343))))
end
| false -> begin
()
end)
in (let _68_14347 = (let _68_14346 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _68_14346))
in (solve env _68_14347))))
end))
end
| false -> begin
(aux xs args)
end)
end
| _ -> begin
(aux xs args)
end)
end
| (x::xs, arg::args) -> begin
(let _68_14350 = (let _68_14349 = (Microsoft_FStar_Absyn_Print.binder_to_string x)
in (let _68_14348 = (Microsoft_FStar_Absyn_Print.arg_to_string arg)
in (Support.Microsoft.FStar.Util.format2 "type incorrect term---impossible: expected %s; got %s\n" _68_14349 _68_14348)))
in (giveup _68_14350))
end))
in (aux (Support.List.rev all_xs) (Support.List.rev args1)))
end)
end))
end
| _ -> begin
(giveup "rigid head term is not a variable")
end)))
in (let imitate_or_project_e = (fun ( _33_3285 ) -> (match (()) with
| () -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid: not a pattern" orig wl))
end
| false -> begin
(let _33_3286 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14354 = (Microsoft_FStar_Absyn_Print.exp_to_string e1)
in (let _68_14353 = (Microsoft_FStar_Absyn_Print.exp_to_string e2)
in (Support.Microsoft.FStar.Util.fprint2 "Imitating expressions: %s =?= %s\n" _68_14354 _68_14353)))
end
| false -> begin
()
end)
in (let _33_3290 = (Microsoft_FStar_Absyn_Util.head_and_args_e e2)
in (match (_33_3290) with
| (head2, args2) -> begin
(let fvhead = (Microsoft_FStar_Absyn_Util.freevars_exp head2)
in (let _33_3295 = (occurs_check_e env (u1, t1) head2)
in (match (_33_3295) with
| (occurs_ok, _) -> begin
(match (((Microsoft_FStar_Absyn_Util.fvs_included fvhead Microsoft_FStar_Absyn_Syntax.no_fvs) && occurs_ok)) with
| true -> begin
(let _33_3303 = (match ((Microsoft_FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some ((xs, c)) -> begin
(xs, (Microsoft_FStar_Absyn_Util.comp_result c))
end)
in (match (_33_3303) with
| (xs, tres) -> begin
(let _33_3307 = (sub_problems xs args2)
in (match (_33_3307) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (let body = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.Microsoft_FStar_Absyn_Syntax.pos)
in (match (xs) with
| [] -> begin
body
end
| _ -> begin
(let _68_14356 = (let _68_14355 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.Microsoft_FStar_Absyn_Syntax.pos)
in (xs, _68_14355))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _68_14356 None e1.Microsoft_FStar_Absyn_Syntax.pos))
end))
in (let _33_3313 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14360 = (Microsoft_FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _68_14359 = (Microsoft_FStar_Absyn_Print.exp_to_string sol)
in (let _68_14358 = (let _68_14357 = (Support.Prims.pipe_right gi_pi (Support.List.map (prob_to_string env)))
in (Support.Prims.pipe_right _68_14357 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.fprint3 "Imitated: %s -> %s\nSubprobs=\n%s\n" _68_14360 _68_14359 _68_14358))))
end
| false -> begin
()
end)
in (let _68_14362 = (let _68_14361 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _68_14361))
in (solve env _68_14362))))
end))
end))
end
| false -> begin
(match (occurs_ok) with
| true -> begin
(project_e head2 args2)
end
| false -> begin
(giveup env "flex-rigid: occurs check failed" orig)
end)
end)
end)))
end)))
end)
end))
in (match (maybe_vars1) with
| (None) | (Some ([])) -> begin
(imitate_or_project_e ())
end
| Some (xs) -> begin
(let fvs1 = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders xs)
in (let fvs2 = (Microsoft_FStar_Absyn_Util.freevars_exp e2)
in (let _33_3325 = (occurs_check_e env (u1, t1) e2)
in (match (_33_3325) with
| (occurs_ok, _) -> begin
(match ((((Support.Microsoft.FStar.Util.set_is_subset_of fvs2.Microsoft_FStar_Absyn_Syntax.ftvs fvs1.Microsoft_FStar_Absyn_Syntax.ftvs) && (Support.Microsoft.FStar.Util.set_is_subset_of fvs2.Microsoft_FStar_Absyn_Syntax.fxvs fvs1.Microsoft_FStar_Absyn_Syntax.fxvs)) && occurs_ok)) with
| true -> begin
(let sol = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs' (xs, e2) None e1.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_14363 = (solve_prob orig None ((UE (((u1, t1), sol)))::[]) wl)
in (solve env _68_14363)))
end
| false -> begin
(imitate_or_project_e ())
end)
end))))
end)))))
end))
in (let flex_flex = (fun ( _33_3332 ) ( _33_3337 ) -> (match ((_33_3332, _33_3337)) with
| ((e1, u1, t1, args1), (e2, u2, t2, args2)) -> begin
(let maybe_vars1 = (pat_vars env [] args1)
in (let maybe_vars2 = (pat_vars env [] args2)
in (match ((maybe_vars1, maybe_vars2)) with
| ((None, _)) | ((_, None)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-flex: not a pattern" orig wl))
end
| false -> begin
(giveup env "flex-flex expressions not patterns" orig)
end)
end
| (Some (xs), Some (ys)) -> begin
(match (((Support.Microsoft.FStar.Unionfind.equivalent u1 u2) && (binders_eq xs ys))) with
| true -> begin
(solve env wl)
end
| false -> begin
(let zs = (intersect_vars xs ys)
in (let tt = (Microsoft_FStar_Tc_Recheck.recompute_typ e2)
in (let _33_3358 = (let _68_14368 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_evar _68_14368 zs tt))
in (match (_33_3358) with
| (u, _) -> begin
(let sub1 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (xs, u) (Some (t1)) e1.Microsoft_FStar_Absyn_Syntax.pos)
in (let sub2 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (ys, u) (Some (t2)) e1.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_14369 = (solve_prob orig None ((UE (((u1, t1), sub1)))::(UE (((u2, t2), sub2)))::[]) wl)
in (solve env _68_14369))))
end))))
end)
end)))
end))
in (let smt_fallback = (fun ( e1 ) ( e2 ) -> (match (wl.smt_ok) with
| true -> begin
(let _33_3364 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14374 = (prob_to_string env orig)
in (Support.Microsoft.FStar.Util.fprint1 "Using SMT to solve:\n%s\n" _68_14374))
end
| false -> begin
()
end)
in (let _33_3369 = (let _68_14376 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14375 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _68_14376 _68_14375 Microsoft_FStar_Absyn_Syntax.ktype)))
in (match (_33_3369) with
| (t, _) -> begin
(let _68_14380 = (let _68_14379 = (let _68_14378 = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (Support.Prims.pipe_left (fun ( _68_14377 ) -> Some (_68_14377)) _68_14378))
in (solve_prob orig _68_14379 [] wl))
in (solve env _68_14380))
end)))
end
| false -> begin
(giveup env "no SMT solution permitted" orig)
end))
in (match ((e1.Microsoft_FStar_Absyn_Syntax.n, e2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e1, _, _)), _) -> begin
(solve_e env (let _33_3380 = problem
in {lhs = e1; relation = _33_3380.relation; rhs = _33_3380.rhs; element = _33_3380.element; logical_guard = _33_3380.logical_guard; scope = _33_3380.scope; reason = _33_3380.reason; loc = _33_3380.loc; rank = _33_3380.rank}) wl)
end
| (_, Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e2, _, _))) -> begin
(solve_e env (let _33_3392 = problem
in {lhs = _33_3392.lhs; relation = _33_3392.relation; rhs = e2; element = _33_3392.element; logical_guard = _33_3392.logical_guard; scope = _33_3392.scope; reason = _33_3392.reason; loc = _33_3392.loc; rank = _33_3392.rank}) wl)
end
| ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) | ((Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) | ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) | ((Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) -> begin
(let _68_14382 = (destruct_flex_e e1)
in (let _68_14381 = (destruct_flex_e e2)
in (flex_flex _68_14382 _68_14381)))
end
| ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _)) -> begin
(let _68_14383 = (destruct_flex_e e1)
in (flex_rigid _68_14383 e2))
end
| ((_, Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) -> begin
(let _68_14384 = (destruct_flex_e e2)
in (flex_rigid _68_14384 e1))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (x1), Microsoft_FStar_Absyn_Syntax.Exp_bvar (x1')) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvd_eq x1.Microsoft_FStar_Absyn_Syntax.v x1'.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(let _68_14385 = (solve_prob orig None [] wl)
in (solve env _68_14385))
end
| false -> begin
(let _68_14391 = (let _68_14390 = (let _68_14389 = (let _68_14388 = (Microsoft_FStar_Tc_Recheck.recompute_typ e1)
in (let _68_14387 = (Microsoft_FStar_Tc_Recheck.recompute_typ e2)
in (Microsoft_FStar_Absyn_Util.mk_eq _68_14388 _68_14387 e1 e2)))
in (Support.Prims.pipe_left (fun ( _68_14386 ) -> Some (_68_14386)) _68_14389))
in (solve_prob orig _68_14390 [] wl))
in (solve env _68_14391))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv1, _)), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv1', _))) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv1.Microsoft_FStar_Absyn_Syntax.v fv1'.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(let _68_14392 = (solve_prob orig None [] wl)
in (solve env _68_14392))
end
| false -> begin
(giveup env "free-variables unequal" orig)
end)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_constant (s1), Microsoft_FStar_Absyn_Syntax.Exp_constant (s1')) -> begin
(let const_eq = (fun ( s1 ) ( s2 ) -> (match ((s1, s2)) with
| (Microsoft_FStar_Absyn_Syntax.Const_bytearray ((b1, _)), Microsoft_FStar_Absyn_Syntax.Const_bytearray ((b2, _))) -> begin
(b1 = b2)
end
| (Microsoft_FStar_Absyn_Syntax.Const_string ((b1, _)), Microsoft_FStar_Absyn_Syntax.Const_string ((b2, _))) -> begin
(b1 = b2)
end
| _ -> begin
(s1 = s2)
end))
in (match ((const_eq s1 s1')) with
| true -> begin
(let _68_14397 = (solve_prob orig None [] wl)
in (solve env _68_14397))
end
| false -> begin
(giveup env "constants unequal" orig)
end))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _) -> begin
(let _68_14399 = (let _33_3591 = problem
in (let _68_14398 = (whnf_e env e1)
in {lhs = _68_14398; relation = _33_3591.relation; rhs = _33_3591.rhs; element = _33_3591.element; logical_guard = _33_3591.logical_guard; scope = _33_3591.scope; reason = _33_3591.reason; loc = _33_3591.loc; rank = _33_3591.rank}))
in (solve_e env _68_14399 wl))
end
| (_, Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _68_14401 = (let _33_3612 = problem
in (let _68_14400 = (whnf_e env e2)
in {lhs = _33_3612.lhs; relation = _33_3612.relation; rhs = _68_14400; element = _33_3612.element; logical_guard = _33_3612.logical_guard; scope = _33_3612.scope; reason = _33_3612.reason; loc = _33_3612.loc; rank = _33_3612.rank}))
in (solve_e env _68_14401 wl))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((head1, args1)), Microsoft_FStar_Absyn_Syntax.Exp_app ((head2, args2))) -> begin
(let orig_wl = wl
in (let rec solve_args = (fun ( sub_probs ) ( wl ) ( args1 ) ( args2 ) -> (match ((args1, args2)) with
| ([], []) -> begin
(let guard = (let _68_14411 = (let _68_14410 = (Support.List.map p_guard sub_probs)
in (Support.Prims.pipe_right _68_14410 (Support.List.map Support.Prims.fst)))
in (Microsoft_FStar_Absyn_Util.mk_conj_l _68_14411))
in (let g = (simplify_formula env guard)
in (let g = (Microsoft_FStar_Absyn_Util.compress_typ g)
in (match (g.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
(let _68_14412 = (solve_prob orig None wl.subst (let _33_3637 = orig_wl
in {attempting = _33_3637.attempting; deferred = _33_3637.deferred; subst = []; ctr = _33_3637.ctr; slack_vars = _33_3637.slack_vars; defer_ok = _33_3637.defer_ok; smt_ok = _33_3637.smt_ok; tcenv = _33_3637.tcenv}))
in (solve env _68_14412))
end
| _ -> begin
(let _33_3644 = (let _68_14414 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14413 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _68_14414 _68_14413 Microsoft_FStar_Absyn_Syntax.ktype)))
in (match (_33_3644) with
| (t, _) -> begin
(let guard = (let _68_14415 = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (Microsoft_FStar_Absyn_Util.mk_disj g _68_14415))
in (let _68_14416 = (solve_prob orig (Some (guard)) wl.subst (let _33_3646 = orig_wl
in {attempting = _33_3646.attempting; deferred = _33_3646.deferred; subst = []; ctr = _33_3646.ctr; slack_vars = _33_3646.slack_vars; defer_ok = _33_3646.defer_ok; smt_ok = _33_3646.smt_ok; tcenv = _33_3646.tcenv}))
in (solve env _68_14416)))
end))
end))))
end
| (arg1::rest1, arg2::rest2) -> begin
(let prob = (match (((Support.Prims.fst arg1), (Support.Prims.fst arg2))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
(let _68_14418 = (mk_problem (p_scope orig) orig t1 EQ t2 None "expression type arg")
in (Support.Prims.pipe_left (fun ( _68_14417 ) -> TProb (_68_14417)) _68_14418))
end
| (Support.Microsoft.FStar.Util.Inr (e1), Support.Microsoft.FStar.Util.Inr (e2)) -> begin
(let _68_14420 = (mk_problem (p_scope orig) orig e1 EQ e2 None "expression arg")
in (Support.Prims.pipe_left (fun ( _68_14419 ) -> EProb (_68_14419)) _68_14420))
end
| _ -> begin
(failwith ("Impossible: ill-typed expression"))
end)
in (match ((solve env (let _33_3668 = wl
in {attempting = (prob)::[]; deferred = []; subst = _33_3668.subst; ctr = _33_3668.ctr; slack_vars = _33_3668.slack_vars; defer_ok = false; smt_ok = false; tcenv = _33_3668.tcenv}))) with
| Failed (_) -> begin
(smt_fallback e1 e2)
end
| Success ((subst, _)) -> begin
(solve_args ((prob)::sub_probs) (let _33_3678 = wl
in {attempting = _33_3678.attempting; deferred = _33_3678.deferred; subst = subst; ctr = _33_3678.ctr; slack_vars = _33_3678.slack_vars; defer_ok = _33_3678.defer_ok; smt_ok = _33_3678.smt_ok; tcenv = _33_3678.tcenv}) rest1 rest2)
end))
end
| _ -> begin
(failwith ("Impossible: lengths defer"))
end))
in (let rec match_head_and_args = (fun ( head1 ) ( head2 ) -> (match ((let _68_14428 = (let _68_14425 = (Microsoft_FStar_Absyn_Util.compress_exp head1)
in _68_14425.Microsoft_FStar_Absyn_Syntax.n)
in (let _68_14427 = (let _68_14426 = (Microsoft_FStar_Absyn_Util.compress_exp head2)
in _68_14426.Microsoft_FStar_Absyn_Syntax.n)
in (_68_14428, _68_14427)))) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (x), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) when ((Microsoft_FStar_Absyn_Util.bvar_eq x y) && ((Support.List.length args1) = (Support.List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _)), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((g, _))) when (((Microsoft_FStar_Absyn_Util.fvar_eq f g) && (not ((Microsoft_FStar_Absyn_Util.is_interpreted f.Microsoft_FStar_Absyn_Syntax.v)))) && ((Support.List.length args1) = (Support.List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _, _)), _) -> begin
(match_head_and_args e head2)
end
| (_, Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _, _))) -> begin
(match_head_and_args head1 e)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_abs (_), _) -> begin
(let _68_14430 = (let _33_3727 = problem
in (let _68_14429 = (whnf_e env e1)
in {lhs = _68_14429; relation = _33_3727.relation; rhs = _33_3727.rhs; element = _33_3727.element; logical_guard = _33_3727.logical_guard; scope = _33_3727.scope; reason = _33_3727.reason; loc = _33_3727.loc; rank = _33_3727.rank}))
in (solve_e env _68_14430 wl))
end
| (_, Microsoft_FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(let _68_14432 = (let _33_3735 = problem
in (let _68_14431 = (whnf_e env e2)
in {lhs = _33_3735.lhs; relation = _33_3735.relation; rhs = _68_14431; element = _33_3735.element; logical_guard = _33_3735.logical_guard; scope = _33_3735.scope; reason = _33_3735.reason; loc = _33_3735.loc; rank = _33_3735.rank}))
in (solve_e env _68_14432 wl))
end
| _ -> begin
(smt_fallback e1 e2)
end))
in (match_head_and_args head1 head2))))
end
| _ -> begin
(let _33_3744 = (let _68_14434 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14433 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _68_14434 _68_14433 Microsoft_FStar_Absyn_Syntax.ktype)))
in (match (_33_3744) with
| (t, _) -> begin
(let guard = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (let _33_3746 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14435 = (Microsoft_FStar_Absyn_Print.typ_to_string guard)
in (Support.Microsoft.FStar.Util.fprint1 "Emitting guard %s\n" _68_14435))
end
| false -> begin
()
end)
in (let _68_14439 = (let _68_14438 = (let _68_14437 = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (Support.Prims.pipe_left (fun ( _68_14436 ) -> Some (_68_14436)) _68_14437))
in (solve_prob orig _68_14438 [] wl))
in (solve env _68_14439))))
end))
end)))))))))))

type guard_formula =
| Trivial
| NonTrivial of Microsoft_FStar_Absyn_Syntax.formula

let is_Trivial = (fun ( _discr_ ) -> (match (_discr_) with
| Trivial -> begin
true
end
| _ -> begin
false
end))

let is_NonTrivial = (fun ( _discr_ ) -> (match (_discr_) with
| NonTrivial (_) -> begin
true
end
| _ -> begin
false
end))

type implicits =
((Microsoft_FStar_Absyn_Syntax.uvar_t * Support.Microsoft.FStar.Range.range), (Microsoft_FStar_Absyn_Syntax.uvar_e * Support.Microsoft.FStar.Range.range)) Support.Microsoft.FStar.Util.either list

type guard_t =
{guard_f : guard_formula; deferred : deferred; implicits : implicits}

let is_Mkguard_t = (fun ( _ ) -> (failwith ("Not yet implemented:is_Mkguard_t")))

let guard_to_string = (fun ( env ) ( g ) -> (let form = (match (g.guard_f) with
| Trivial -> begin
"trivial"
end
| NonTrivial (f) -> begin
(match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(Microsoft_FStar_Tc_Normalize.formula_norm_to_string env f)
end
| false -> begin
"non-trivial"
end)
end)
in (let carry = (let _68_14463 = (Support.List.map (fun ( _33_3763 ) -> (match (_33_3763) with
| (_, x) -> begin
(prob_to_string env x)
end)) g.deferred.carry)
in (Support.Prims.pipe_right _68_14463 (Support.String.concat ",\n")))
in (Support.Microsoft.FStar.Util.format2 "\n\t{guard_f=%s;\n\t deferred={\n%s};}\n" form carry))))

let guard_of_guard_formula = (fun ( g ) -> {guard_f = g; deferred = {carry = []; slack = []}; implicits = []})

let guard_f = (fun ( g ) -> g.guard_f)

let is_trivial = (fun ( g ) -> (match (g) with
| {guard_f = Trivial; deferred = {carry = []; slack = []}; implicits = _} -> begin
true
end
| _ -> begin
false
end))

let trivial_guard = {guard_f = Trivial; deferred = {carry = []; slack = []}; implicits = []}

let abstract_guard = (fun ( x ) ( g ) -> (match (g) with
| (None) | (Some ({guard_f = Trivial; deferred = _; implicits = _})) -> begin
g
end
| Some (g) -> begin
(let f = (match (g.guard_f) with
| NonTrivial (f) -> begin
f
end
| _ -> begin
(failwith ("impossible"))
end)
in (let _68_14480 = (let _33_3794 = g
in (let _68_14479 = (let _68_14478 = (let _68_14477 = (let _68_14476 = (let _68_14475 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_68_14475)::[])
in (_68_14476, f))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_14477 None f.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.Prims.pipe_left (fun ( _68_14474 ) -> NonTrivial (_68_14474)) _68_14478))
in {guard_f = _68_14479; deferred = _33_3794.deferred; implicits = _33_3794.implicits}))
in Some (_68_14480)))
end))

let apply_guard = (fun ( g ) ( e ) -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _33_3801 = g
in (let _68_14492 = (let _68_14491 = (let _68_14490 = (let _68_14489 = (let _68_14488 = (let _68_14487 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_68_14487)::[])
in (f, _68_14488))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_14489))
in (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn f.Microsoft_FStar_Absyn_Syntax.pos (Some (Microsoft_FStar_Absyn_Syntax.ktype))) _68_14490))
in NonTrivial (_68_14491))
in {guard_f = _68_14492; deferred = _33_3801.deferred; implicits = _33_3801.implicits}))
end))

let trivial = (fun ( t ) -> (match (t) with
| Trivial -> begin
()
end
| NonTrivial (_) -> begin
(failwith ("impossible"))
end))

let conj_guard_f = (fun ( g1 ) ( g2 ) -> (match ((g1, g2)) with
| ((Trivial, g)) | ((g, Trivial)) -> begin
g
end
| (NonTrivial (f1), NonTrivial (f2)) -> begin
(let _68_14499 = (Microsoft_FStar_Absyn_Util.mk_conj f1 f2)
in NonTrivial (_68_14499))
end))

let check_trivial = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _ -> begin
NonTrivial (t)
end))

let imp_guard_f = (fun ( g1 ) ( g2 ) -> (match ((g1, g2)) with
| (Trivial, g) -> begin
g
end
| (g, Trivial) -> begin
Trivial
end
| (NonTrivial (f1), NonTrivial (f2)) -> begin
(let imp = (Microsoft_FStar_Absyn_Util.mk_imp f1 f2)
in (check_trivial imp))
end))

let binop_guard = (fun ( f ) ( g1 ) ( g2 ) -> (let _68_14522 = (f g1.guard_f g2.guard_f)
in {guard_f = _68_14522; deferred = {carry = (Support.List.append g1.deferred.carry g2.deferred.carry); slack = (Support.List.append g1.deferred.slack g2.deferred.slack)}; implicits = (Support.List.append g1.implicits g2.implicits)}))

let conj_guard = (fun ( g1 ) ( g2 ) -> (binop_guard conj_guard_f g1 g2))

let imp_guard = (fun ( g1 ) ( g2 ) -> (binop_guard imp_guard_f g1 g2))

let close_guard = (fun ( binders ) ( g ) -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _33_3851 = g
in (let _68_14537 = (let _68_14536 = (Microsoft_FStar_Absyn_Util.close_forall binders f)
in (Support.Prims.pipe_right _68_14536 (fun ( _68_14535 ) -> NonTrivial (_68_14535))))
in {guard_f = _68_14537; deferred = _33_3851.deferred; implicits = _33_3851.implicits}))
end))

let mk_guard = (fun ( g ) ( ps ) ( slack ) ( locs ) -> {guard_f = g; deferred = {carry = ps; slack = slack}; implicits = []})

let new_t_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) -> (let reason = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _68_14549 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env lhs)
in (let _68_14548 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env rhs)
in (Support.Microsoft.FStar.Util.format3 "Top-level:\n%s\n\t%s\n%s" _68_14549 (rel_to_string rel) _68_14548)))
end
| false -> begin
"TOP"
end)
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

let new_t_prob = (fun ( env ) ( t1 ) ( rel ) ( t2 ) -> (let x = (let _68_14558 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p _68_14558 t1))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))))
in (let p = (let _68_14562 = (let _68_14560 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.Prims.pipe_left (fun ( _68_14559 ) -> Some (_68_14559)) _68_14560))
in (let _68_14561 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_t_problem env t1 rel t2 _68_14562 _68_14561)))
in (TProb (p), x)))))

let new_k_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) -> (let reason = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _68_14570 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env lhs)
in (let _68_14569 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env rhs)
in (Support.Microsoft.FStar.Util.format3 "Top-level:\n%s\n\t%s\n%s" _68_14570 (rel_to_string rel) _68_14569)))
end
| false -> begin
"TOP"
end)
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

let simplify_guard = (fun ( env ) ( g ) -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _33_3885 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _68_14575 = (Microsoft_FStar_Absyn_Print.typ_to_string f)
in (Support.Microsoft.FStar.Util.fprint1 "Simplifying guard %s\n" _68_14575))
end
| false -> begin
()
end)
in (let f = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env f)
in (let f = (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _ -> begin
NonTrivial (f)
end)
in (let _33_3893 = g
in {guard_f = f; deferred = _33_3893.deferred; implicits = _33_3893.implicits}))))
end))

let solve_and_commit = (fun ( env ) ( probs ) ( err ) -> (let probs = (match ((Support.ST.read Microsoft_FStar_Options.eager_inference)) with
| true -> begin
(let _33_3898 = probs
in {attempting = _33_3898.attempting; deferred = _33_3898.deferred; subst = _33_3898.subst; ctr = _33_3898.ctr; slack_vars = _33_3898.slack_vars; defer_ok = false; smt_ok = _33_3898.smt_ok; tcenv = _33_3898.tcenv})
end
| false -> begin
probs
end)
in (let sol = (solve env probs)
in (match (sol) with
| Success ((s, deferred)) -> begin
(let _33_3906 = (commit env s)
in Some (deferred))
end
| Failed ((d, s)) -> begin
(let _33_3912 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _68_14587 = (explain env d s)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.print_string _68_14587))
end
| false -> begin
()
end)
in (err (d, s)))
end))))

let with_guard = (fun ( env ) ( prob ) ( dopt ) -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _68_14599 = (let _68_14598 = (let _68_14597 = (let _68_14596 = (Support.Prims.pipe_right (p_guard prob) Support.Prims.fst)
in (Support.Prims.pipe_right _68_14596 (fun ( _68_14595 ) -> NonTrivial (_68_14595))))
in {guard_f = _68_14597; deferred = d; implicits = []})
in (simplify_guard env _68_14598))
in (Support.Prims.pipe_left (fun ( _68_14594 ) -> Some (_68_14594)) _68_14599))
end))

let try_keq = (fun ( env ) ( k1 ) ( k2 ) -> (let _33_3923 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14607 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (let _68_14606 = (Microsoft_FStar_Absyn_Print.kind_to_string k2)
in (Support.Microsoft.FStar.Util.fprint2 "try_keq of %s and %s\n" _68_14607 _68_14606)))
end
| false -> begin
()
end)
in (let prob = (let _68_14612 = (let _68_14611 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env k1)
in (let _68_14610 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env k2)
in (let _68_14609 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_k_problem env _68_14611 EQ _68_14610 None _68_14609))))
in (Support.Prims.pipe_left (fun ( _68_14608 ) -> KProb (_68_14608)) _68_14612))
in (let _68_14614 = (solve_and_commit env (singleton env prob) (fun ( _33_3926 ) -> None))
in (Support.Prims.pipe_left (with_guard env prob) _68_14614)))))

let keq = (fun ( env ) ( t ) ( k1 ) ( k2 ) -> (match ((try_keq env k1 k2)) with
| None -> begin
(let r = (match (t) with
| None -> begin
(Microsoft_FStar_Tc_Env.get_range env)
end
| Some (t) -> begin
t.Microsoft_FStar_Absyn_Syntax.pos
end)
in (match (t) with
| None -> begin
(let _68_14625 = (let _68_14624 = (let _68_14623 = (Microsoft_FStar_Tc_Errors.incompatible_kinds env k2 k1)
in (_68_14623, r))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14624))
in (raise (_68_14625)))
end
| Some (t) -> begin
(let _68_14628 = (let _68_14627 = (let _68_14626 = (Microsoft_FStar_Tc_Errors.expected_typ_of_kind env k2 t k1)
in (_68_14626, r))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14627))
in (raise (_68_14628)))
end))
end
| Some (g) -> begin
g
end))

let subkind = (fun ( env ) ( k1 ) ( k2 ) -> (let _33_3945 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14638 = (let _68_14635 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _68_14635))
in (let _68_14637 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (let _68_14636 = (Microsoft_FStar_Absyn_Print.kind_to_string k2)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) subkind of %s and %s\n" _68_14638 _68_14637 _68_14636))))
end
| false -> begin
()
end)
in (let prob = (let _68_14643 = (let _68_14642 = (whnf_k env k1)
in (let _68_14641 = (whnf_k env k2)
in (let _68_14640 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_k_problem env _68_14642 SUB _68_14641 None _68_14640))))
in (Support.Prims.pipe_left (fun ( _68_14639 ) -> KProb (_68_14639)) _68_14643))
in (let res = (let _68_14650 = (let _68_14649 = (solve_and_commit env (singleton env prob) (fun ( _33_3948 ) -> (let _68_14648 = (let _68_14647 = (let _68_14646 = (Microsoft_FStar_Tc_Errors.incompatible_kinds env k1 k2)
in (let _68_14645 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_14646, _68_14645)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14647))
in (raise (_68_14648)))))
in (Support.Prims.pipe_left (with_guard env prob) _68_14649))
in (Support.Microsoft.FStar.Util.must _68_14650))
in res))))

let try_teq = (fun ( env ) ( t1 ) ( t2 ) -> (let _33_3954 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14658 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _68_14657 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (Support.Microsoft.FStar.Util.fprint2 "try_teq of %s and %s\n" _68_14658 _68_14657)))
end
| false -> begin
()
end)
in (let prob = (let _68_14661 = (let _68_14660 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_t_problem env t1 EQ t2 None _68_14660))
in (Support.Prims.pipe_left (fun ( _68_14659 ) -> TProb (_68_14659)) _68_14661))
in (let g = (let _68_14663 = (solve_and_commit env (singleton env prob) (fun ( _33_3957 ) -> None))
in (Support.Prims.pipe_left (with_guard env prob) _68_14663))
in g))))

let teq = (fun ( env ) ( t1 ) ( t2 ) -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _68_14673 = (let _68_14672 = (let _68_14671 = (Microsoft_FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _68_14670 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_14671, _68_14670)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14672))
in (raise (_68_14673)))
end
| Some (g) -> begin
(let _33_3966 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14676 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _68_14675 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (let _68_14674 = (guard_to_string env g)
in (Support.Microsoft.FStar.Util.fprint3 "teq of %s and %s succeeded with guard %s\n" _68_14676 _68_14675 _68_14674))))
end
| false -> begin
()
end)
in g)
end))

let try_subtype = (fun ( env ) ( t1 ) ( t2 ) -> (let _33_3971 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14684 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _68_14683 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.fprint2 "try_subtype of %s and %s\n" _68_14684 _68_14683)))
end
| false -> begin
()
end)
in (let _33_3975 = (new_t_prob env t1 SUB t2)
in (match (_33_3975) with
| (prob, x) -> begin
(let g = (let _68_14686 = (solve_and_commit env (singleton env prob) (fun ( _33_3976 ) -> None))
in (Support.Prims.pipe_left (with_guard env prob) _68_14686))
in (let _33_3979 = (match (((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) && (Support.Microsoft.FStar.Util.is_some g))) with
| true -> begin
(let _68_14690 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _68_14689 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _68_14688 = (let _68_14687 = (Support.Microsoft.FStar.Util.must g)
in (guard_to_string env _68_14687))
in (Support.Microsoft.FStar.Util.fprint3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _68_14690 _68_14689 _68_14688))))
end
| false -> begin
()
end)
in (abstract_guard x g)))
end))))

let subtype_fail = (fun ( env ) ( t1 ) ( t2 ) -> (let _68_14697 = (let _68_14696 = (let _68_14695 = (Microsoft_FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _68_14694 = (Microsoft_FStar_Tc_Env.get_range env)
in (_68_14695, _68_14694)))
in Microsoft_FStar_Absyn_Syntax.Error (_68_14696))
in (raise (_68_14697))))

let subtype = (fun ( env ) ( t1 ) ( t2 ) -> (match ((try_subtype env t1 t2)) with
| Some (f) -> begin
f
end
| None -> begin
(subtype_fail env t1 t2)
end))

let sub_comp = (fun ( env ) ( c1 ) ( c2 ) -> (let _33_3993 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14711 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _68_14710 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (Support.Microsoft.FStar.Util.fprint2 "sub_comp of %s and %s\n" _68_14711 _68_14710)))
end
| false -> begin
()
end)
in (let rel = (match (env.Microsoft_FStar_Tc_Env.use_eq) with
| true -> begin
EQ
end
| false -> begin
SUB
end)
in (let prob = (let _68_14714 = (let _68_14713 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_problem env c1 rel c2 None _68_14713 "sub_comp"))
in (Support.Prims.pipe_left (fun ( _68_14712 ) -> CProb (_68_14712)) _68_14714))
in (let _68_14716 = (solve_and_commit env (singleton env prob) (fun ( _33_3997 ) -> None))
in (Support.Prims.pipe_left (with_guard env prob) _68_14716))))))

let solve_deferred_constraints = (fun ( env ) ( g ) -> (let fail = (fun ( _33_4004 ) -> (match (_33_4004) with
| (d, s) -> begin
(let msg = (explain env d s)
in (raise (Microsoft_FStar_Absyn_Syntax.Error ((msg, (p_loc d))))))
end))
in (let _33_4009 = (match (((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) && ((Support.List.length g.deferred.carry) <> 0))) with
| true -> begin
(let _68_14729 = (let _68_14728 = (Support.Prims.pipe_right g.deferred.carry (Support.List.map (fun ( _33_4008 ) -> (match (_33_4008) with
| (msg, x) -> begin
(let _68_14727 = (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range (p_loc x))
in (let _68_14726 = (prob_to_string env x)
in (let _68_14725 = (let _68_14724 = (Support.Prims.pipe_right (p_guard x) Support.Prims.fst)
in (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env _68_14724))
in (Support.Microsoft.FStar.Util.format4 "(At %s) %s\n%s\nguard is %s\n" _68_14727 msg _68_14726 _68_14725))))
end))))
in (Support.Prims.pipe_right _68_14728 (Support.String.concat "\n")))
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.fprint1 "Trying to solve carried problems: begin\n%s\nend\n") _68_14729))
end
| false -> begin
()
end)
in (let gopt = (let _68_14730 = (wl_of_guard env g.deferred)
in (solve_and_commit env _68_14730 fail))
in (match (gopt) with
| Some ({carry = _; slack = slack}) -> begin
(let _33_4017 = (fix_slack_vars slack)
in (let _33_4019 = g
in {guard_f = _33_4019.guard_f; deferred = no_deferred; implicits = _33_4019.implicits}))
end
| _ -> begin
(failwith ("impossible"))
end)))))

let try_discharge_guard = (fun ( env ) ( g ) -> (let g = (solve_deferred_constraints env g)
in (match ((not ((Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)))) with
| true -> begin
()
end
| false -> begin
(match (g.guard_f) with
| Trivial -> begin
()
end
| NonTrivial (vc) -> begin
(let vc = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.DeltaHard)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| Trivial -> begin
()
end
| NonTrivial (vc) -> begin
(let _33_4033 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _68_14737 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _68_14736 = (let _68_14735 = (Microsoft_FStar_Absyn_Print.formula_to_string vc)
in (Support.Microsoft.FStar.Util.format1 "Checking VC=\n%s\n" _68_14735))
in (Microsoft_FStar_Tc_Errors.diag _68_14737 _68_14736)))
end
| false -> begin
()
end)
in (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.solve env vc))
end))
end)
end)))




