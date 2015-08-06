
let new_kvar = (fun ( r ) ( binders ) -> (let wf = (fun ( k ) ( _35_39 ) -> (match (()) with
| () -> begin
true
end))
in (let u = (Support.Microsoft.FStar.Unionfind.fresh Microsoft_FStar_Absyn_Syntax.Uvar)
in (let _70_13032 = (let _70_13031 = (let _70_13030 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (u, _70_13030))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar _70_13031 r))
in (_70_13032, u)))))

let new_tvar = (fun ( r ) ( binders ) ( k ) -> (let wf = (fun ( t ) ( tk ) -> true)
in (let binders = (Support.All.pipe_right binders (Support.List.filter (fun ( x ) -> (let _70_13044 = (Microsoft_FStar_Absyn_Syntax.is_null_binder x)
in (Support.All.pipe_right _70_13044 Support.Prims.op_Negation)))))
in (let uv = (Support.Microsoft.FStar.Unionfind.fresh Microsoft_FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (Microsoft_FStar_Absyn_Syntax.mk_Typ_uvar' (uv, k) None r)
in (uv, uv))
end
| _35_53 -> begin
(let args = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (let k' = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (binders, k) r)
in (let uv = (Microsoft_FStar_Absyn_Syntax.mk_Typ_uvar' (uv, k') None r)
in (let _70_13045 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (uv, args) None r)
in (_70_13045, uv)))))
end)))))

let new_evar = (fun ( r ) ( binders ) ( t ) -> (let wf = (fun ( e ) ( t ) -> true)
in (let binders = (Support.All.pipe_right binders (Support.List.filter (fun ( x ) -> (let _70_13057 = (Microsoft_FStar_Absyn_Syntax.is_null_binder x)
in (Support.All.pipe_right _70_13057 Support.Prims.op_Negation)))))
in (let uv = (Support.Microsoft.FStar.Unionfind.fresh Microsoft_FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (Microsoft_FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t) None r)
in (uv, uv))
end
| _35_69 -> begin
(let args = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (let t' = (let _70_13059 = (let _70_13058 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (binders, _70_13058))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _70_13059 None r))
in (let uv = (Microsoft_FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t') None r)
in (match (args) with
| [] -> begin
(uv, uv)
end
| _35_75 -> begin
(let _70_13060 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (uv, args) None r)
in (_70_13060, uv))
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

let is_Mkproblem = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkproblem"))

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

let is_Mkworklist = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkworklist"))

type deferred =
{carry : (string * prob) list; slack : (bool * Microsoft_FStar_Absyn_Syntax.typ) list}

let is_Mkdeferred = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkdeferred"))

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

let rel_to_string = (fun ( _35_1 ) -> (match (_35_1) with
| EQ -> begin
"="
end
| SUB -> begin
"<:"
end
| SUBINV -> begin
":>"
end))

let prob_to_string = (fun ( env ) ( _35_2 ) -> (match (_35_2) with
| KProb (p) -> begin
(let _70_13199 = (Microsoft_FStar_Absyn_Print.kind_to_string p.lhs)
in (let _70_13198 = (Microsoft_FStar_Absyn_Print.kind_to_string p.rhs)
in (Support.Microsoft.FStar.Util.format3 "\t%s\n\t\t%s\n\t%s" _70_13199 (rel_to_string p.relation) _70_13198)))
end
| TProb (p) -> begin
(let _70_13212 = (let _70_13211 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env p.lhs)
in (let _70_13210 = (let _70_13209 = (Microsoft_FStar_Absyn_Print.tag_of_typ p.lhs)
in (let _70_13208 = (let _70_13207 = (let _70_13206 = (Support.All.pipe_right p.reason Support.List.hd)
in (let _70_13205 = (let _70_13204 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env p.rhs)
in (let _70_13203 = (let _70_13202 = (Microsoft_FStar_Absyn_Print.tag_of_typ p.rhs)
in (let _70_13201 = (let _70_13200 = (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env (Support.Prims.fst p.logical_guard))
in (_70_13200)::[])
in (_70_13202)::_70_13201))
in (_70_13204)::_70_13203))
in (_70_13206)::_70_13205))
in ((rel_to_string p.relation))::_70_13207)
in (_70_13209)::_70_13208))
in (_70_13211)::_70_13210))
in (Support.Microsoft.FStar.Util.format "\t%s (%s) \n\t\t%s(%s)\n\t%s (%s) (guard %s)" _70_13212))
end
| EProb (p) -> begin
(let _70_13214 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env p.lhs)
in (let _70_13213 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env p.rhs)
in (Support.Microsoft.FStar.Util.format3 "\t%s \n\t\t%s\n\t%s" _70_13214 (rel_to_string p.relation) _70_13213)))
end
| CProb (p) -> begin
(let _70_13216 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env p.lhs)
in (let _70_13215 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env p.rhs)
in (Support.Microsoft.FStar.Util.format3 "\t%s \n\t\t%s\n\t%s" _70_13216 (rel_to_string p.relation) _70_13215)))
end))

let uvi_to_string = (fun ( env ) ( uvi ) -> (let str = (fun ( u ) -> (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _70_13222 = (Support.Microsoft.FStar.Unionfind.uvar_id u)
in (Support.All.pipe_right _70_13222 Support.Microsoft.FStar.Util.string_of_int))
end))
in (match (uvi) with
| UK ((u, _35_141)) -> begin
(let _70_13223 = (str u)
in (Support.All.pipe_right _70_13223 (Support.Microsoft.FStar.Util.format1 "UK %s")))
end
| UT (((u, _35_146), t)) -> begin
(let _70_13226 = (str u)
in (Support.All.pipe_right _70_13226 (fun ( x ) -> (let _70_13225 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.format2 "UT %s %s" x _70_13225)))))
end
| UE (((u, _35_154), _35_157)) -> begin
(let _70_13227 = (str u)
in (Support.All.pipe_right _70_13227 (Support.Microsoft.FStar.Util.format1 "UE %s")))
end)))

let invert_rel = (fun ( _35_3 ) -> (match (_35_3) with
| EQ -> begin
EQ
end
| SUB -> begin
SUBINV
end
| SUBINV -> begin
SUB
end))

let invert = (fun ( p ) -> (let _35_165 = p
in {lhs = p.rhs; relation = (invert_rel p.relation); rhs = p.lhs; element = _35_165.element; logical_guard = _35_165.logical_guard; scope = _35_165.scope; reason = _35_165.reason; loc = _35_165.loc; rank = _35_165.rank}))

let maybe_invert = (fun ( p ) -> (match ((p.relation = SUBINV)) with
| true -> begin
(invert p)
end
| false -> begin
p
end))

let maybe_invert_p = (fun ( _35_4 ) -> (match (_35_4) with
| KProb (p) -> begin
(Support.All.pipe_right (maybe_invert p) (fun ( _70_13234 ) -> KProb (_70_13234)))
end
| TProb (p) -> begin
(Support.All.pipe_right (maybe_invert p) (fun ( _70_13235 ) -> TProb (_70_13235)))
end
| EProb (p) -> begin
(Support.All.pipe_right (maybe_invert p) (fun ( _70_13236 ) -> EProb (_70_13236)))
end
| CProb (p) -> begin
(Support.All.pipe_right (maybe_invert p) (fun ( _70_13237 ) -> CProb (_70_13237)))
end))

let vary_rel = (fun ( rel ) ( _35_5 ) -> (match (_35_5) with
| INVARIANT -> begin
EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))

let p_rel = (fun ( _35_6 ) -> (match (_35_6) with
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

let p_reason = (fun ( _35_7 ) -> (match (_35_7) with
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

let p_loc = (fun ( _35_8 ) -> (match (_35_8) with
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

let p_context = (fun ( _35_9 ) -> (match (_35_9) with
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

let p_guard = (fun ( _35_10 ) -> (match (_35_10) with
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

let p_scope = (fun ( _35_11 ) -> (match (_35_11) with
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

let p_invert = (fun ( _35_12 ) -> (match (_35_12) with
| KProb (p) -> begin
(Support.All.pipe_left (fun ( _70_13256 ) -> KProb (_70_13256)) (invert p))
end
| TProb (p) -> begin
(Support.All.pipe_left (fun ( _70_13257 ) -> TProb (_70_13257)) (invert p))
end
| EProb (p) -> begin
(Support.All.pipe_left (fun ( _70_13258 ) -> EProb (_70_13258)) (invert p))
end
| CProb (p) -> begin
(Support.All.pipe_left (fun ( _70_13259 ) -> CProb (_70_13259)) (invert p))
end))

let is_top_level_prob = (fun ( p ) -> ((Support.All.pipe_right (p_reason p) Support.List.length) = 1))

let mk_problem = (fun ( scope ) ( orig ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( reason ) -> (let _70_13269 = (new_tvar (p_loc orig) scope Microsoft_FStar_Absyn_Syntax.ktype)
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _70_13269; scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None}))

let new_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) ( reason ) -> (let _70_13279 = (let _70_13278 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_13277 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _70_13278 _70_13277 Microsoft_FStar_Absyn_Syntax.ktype)))
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _70_13279; scope = []; reason = (reason)::[]; loc = loc; rank = None}))

let problem_using_guard = (fun ( orig ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( reason ) -> {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = (p_guard orig); scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None})

let guard_on_element = (fun ( problem ) ( x ) ( phi ) -> (match (problem.element) with
| None -> begin
(let _70_13290 = (let _70_13289 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_70_13289)::[])
in (Microsoft_FStar_Absyn_Util.close_forall _70_13290 phi))
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
in (let _35_284 = (p_guard prob)
in (match (_35_284) with
| (_35_282, uv) -> begin
(let _35_292 = (match ((let _70_13301 = (Microsoft_FStar_Absyn_Util.compress_typ uv)
in _70_13301.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uvar, k)) -> begin
(let phi = (Microsoft_FStar_Absyn_Util.close_for_kind phi k)
in (Microsoft_FStar_Absyn_Util.unchecked_unify uvar phi))
end
| _35_291 -> begin
(match ((not (resolve_ok))) with
| true -> begin
(Support.All.failwith "Impossible: this instance has already been assigned a solution")
end
| false -> begin
()
end)
end)
in (match (uvis) with
| [] -> begin
wl
end
| _35_296 -> begin
(let _35_297 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug wl.tcenv) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_13303 = (let _70_13302 = (Support.List.map (uvi_to_string wl.tcenv) uvis)
in (Support.All.pipe_right _70_13302 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.fprint1 "Extending solution: %s\n" _70_13303))
end
| false -> begin
()
end)
in (let _35_299 = wl
in {attempting = _35_299.attempting; deferred = _35_299.deferred; subst = (Support.List.append uvis wl.subst); ctr = (wl.ctr + 1); slack_vars = _35_299.slack_vars; defer_ok = _35_299.defer_ok; smt_ok = _35_299.smt_ok; tcenv = _35_299.tcenv}))
end))
end))))

let extend_solution = (fun ( sol ) ( wl ) -> (let _35_303 = wl
in {attempting = _35_303.attempting; deferred = _35_303.deferred; subst = (sol)::wl.subst; ctr = (wl.ctr + 1); slack_vars = _35_303.slack_vars; defer_ok = _35_303.defer_ok; smt_ok = _35_303.smt_ok; tcenv = _35_303.tcenv}))

let solve_prob = (fun ( prob ) ( logical_guard ) ( uvis ) ( wl ) -> (solve_prob' false prob logical_guard uvis wl))

let explain = (fun ( env ) ( d ) ( s ) -> (let _70_13324 = (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range (p_loc d))
in (let _70_13323 = (prob_to_string env d)
in (let _70_13322 = (Support.All.pipe_right (p_reason d) (Support.String.concat "\n\t>"))
in (Support.Microsoft.FStar.Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _70_13324 _70_13323 _70_13322 s)))))

let empty_worklist = (fun ( env ) -> {attempting = []; deferred = []; subst = []; ctr = 0; slack_vars = []; defer_ok = true; smt_ok = true; tcenv = env})

let singleton = (fun ( env ) ( prob ) -> (let _35_315 = (empty_worklist env)
in {attempting = (prob)::[]; deferred = _35_315.deferred; subst = _35_315.subst; ctr = _35_315.ctr; slack_vars = _35_315.slack_vars; defer_ok = _35_315.defer_ok; smt_ok = _35_315.smt_ok; tcenv = _35_315.tcenv}))

let wl_of_guard = (fun ( env ) ( g ) -> (let _35_319 = (empty_worklist env)
in (let _70_13335 = (Support.List.map Support.Prims.snd g.carry)
in {attempting = _70_13335; deferred = _35_319.deferred; subst = _35_319.subst; ctr = _35_319.ctr; slack_vars = g.slack; defer_ok = false; smt_ok = _35_319.smt_ok; tcenv = _35_319.tcenv})))

let defer = (fun ( reason ) ( prob ) ( wl ) -> (let _35_324 = wl
in {attempting = _35_324.attempting; deferred = ((wl.ctr, reason, prob))::wl.deferred; subst = _35_324.subst; ctr = _35_324.ctr; slack_vars = _35_324.slack_vars; defer_ok = _35_324.defer_ok; smt_ok = _35_324.smt_ok; tcenv = _35_324.tcenv}))

let attempt = (fun ( probs ) ( wl ) -> (let _35_328 = wl
in {attempting = (Support.List.append probs wl.attempting); deferred = _35_328.deferred; subst = _35_328.subst; ctr = _35_328.ctr; slack_vars = _35_328.slack_vars; defer_ok = _35_328.defer_ok; smt_ok = _35_328.smt_ok; tcenv = _35_328.tcenv}))

let add_slack_mul = (fun ( slack ) ( wl ) -> (let _35_332 = wl
in {attempting = _35_332.attempting; deferred = _35_332.deferred; subst = _35_332.subst; ctr = _35_332.ctr; slack_vars = ((true, slack))::wl.slack_vars; defer_ok = _35_332.defer_ok; smt_ok = _35_332.smt_ok; tcenv = _35_332.tcenv}))

let add_slack_add = (fun ( slack ) ( wl ) -> (let _35_336 = wl
in {attempting = _35_336.attempting; deferred = _35_336.deferred; subst = _35_336.subst; ctr = _35_336.ctr; slack_vars = ((false, slack))::wl.slack_vars; defer_ok = _35_336.defer_ok; smt_ok = _35_336.smt_ok; tcenv = _35_336.tcenv}))

let giveup = (fun ( env ) ( reason ) ( prob ) -> (let _35_341 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_13360 = (prob_to_string env prob)
in (Support.Microsoft.FStar.Util.fprint2 "Failed %s:\n%s\n" reason _70_13360))
end
| false -> begin
()
end)
in Failed ((prob, reason))))

let commit = (fun ( env ) ( uvis ) -> (Support.All.pipe_right uvis (Support.List.iter (fun ( _35_13 ) -> (match (_35_13) with
| UK ((u, k)) -> begin
(Microsoft_FStar_Absyn_Util.unchecked_unify u k)
end
| UT (((u, k), t)) -> begin
(Microsoft_FStar_Absyn_Util.unchecked_unify u t)
end
| UE (((u, _35_358), e)) -> begin
(Microsoft_FStar_Absyn_Util.unchecked_unify u e)
end)))))

let find_uvar_k = (fun ( uv ) ( s ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _35_14 ) -> (match (_35_14) with
| UK ((u, t)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.equivalent uv u)) with
| true -> begin
Some (t)
end
| false -> begin
None
end)
end
| _35_371 -> begin
None
end))))

let find_uvar_t = (fun ( uv ) ( s ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _35_15 ) -> (match (_35_15) with
| UT (((u, _35_377), t)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.equivalent uv u)) with
| true -> begin
Some (t)
end
| false -> begin
None
end)
end
| _35_383 -> begin
None
end))))

let find_uvar_e = (fun ( uv ) ( s ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _35_16 ) -> (match (_35_16) with
| UE (((u, _35_389), t)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.equivalent uv u)) with
| true -> begin
Some (t)
end
| false -> begin
None
end)
end
| _35_395 -> begin
None
end))))

let simplify_formula = (fun ( env ) ( f ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env f))

let norm_targ = (fun ( env ) ( t ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env t))

let norm_arg = (fun ( env ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _70_13391 = (let _70_13390 = (norm_targ env t)
in (Support.All.pipe_left (fun ( _70_13389 ) -> Support.Microsoft.FStar.Util.Inl (_70_13389)) _70_13390))
in (_70_13391, (Support.Prims.snd a)))
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
(let _70_13394 = (let _70_13393 = (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env v)
in (Support.All.pipe_left (fun ( _70_13392 ) -> Support.Microsoft.FStar.Util.Inr (_70_13392)) _70_13393))
in (_70_13394, (Support.Prims.snd a)))
end))

let whnf = (fun ( env ) ( t ) -> (let _70_13399 = (Microsoft_FStar_Tc_Normalize.whnf env t)
in (Support.All.pipe_right _70_13399 Microsoft_FStar_Absyn_Util.compress_typ)))

let sn = (fun ( env ) ( t ) -> (let _70_13404 = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::[]) env t)
in (Support.All.pipe_right _70_13404 Microsoft_FStar_Absyn_Util.compress_typ)))

let sn_binders = (fun ( env ) ( binders ) -> (Support.All.pipe_right binders (Support.List.map (fun ( _35_17 ) -> (match (_35_17) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _70_13410 = (let _70_13409 = (let _35_417 = a
in (let _70_13408 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env a.Microsoft_FStar_Absyn_Syntax.sort)
in {Microsoft_FStar_Absyn_Syntax.v = _35_417.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _70_13408; Microsoft_FStar_Absyn_Syntax.p = _35_417.Microsoft_FStar_Absyn_Syntax.p}))
in Support.Microsoft.FStar.Util.Inl (_70_13409))
in (_70_13410, imp))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _70_13413 = (let _70_13412 = (let _35_423 = x
in (let _70_13411 = (norm_targ env x.Microsoft_FStar_Absyn_Syntax.sort)
in {Microsoft_FStar_Absyn_Syntax.v = _35_423.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _70_13411; Microsoft_FStar_Absyn_Syntax.p = _35_423.Microsoft_FStar_Absyn_Syntax.p}))
in Support.Microsoft.FStar.Util.Inr (_70_13412))
in (_70_13413, imp))
end)))))

let whnf_k = (fun ( env ) ( k ) -> (let _70_13418 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.WHNF)::[]) env k)
in (Support.All.pipe_right _70_13418 Microsoft_FStar_Absyn_Util.compress_kind)))

let whnf_e = (fun ( env ) ( e ) -> (let _70_13423 = (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.WHNF)::[]) env e)
in (Support.All.pipe_right _70_13423 Microsoft_FStar_Absyn_Util.compress_exp)))

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
(let k = (let _70_13430 = (Microsoft_FStar_Absyn_Util.subst_of_list formals actuals)
in (Microsoft_FStar_Absyn_Util.subst_kind _70_13430 body))
in (compress_k env wl k))
end
| _35_446 -> begin
(match (((Support.List.length actuals) = 0)) with
| true -> begin
(compress_k env wl k')
end
| false -> begin
(Support.All.failwith "Wrong arity for kind unifier")
end)
end)
end)
end
| _35_448 -> begin
k
end)))

let rec compress = (fun ( env ) ( wl ) ( t ) -> (let t = (let _70_13437 = (Microsoft_FStar_Absyn_Util.unmeta_typ t)
in (whnf env _70_13437))
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _35_455)) -> begin
(match ((find_uvar_t uv wl.subst)) with
| None -> begin
t
end
| Some (t) -> begin
(compress env wl t)
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _35_471)); Microsoft_FStar_Absyn_Syntax.tk = _35_468; Microsoft_FStar_Absyn_Syntax.pos = _35_466; Microsoft_FStar_Absyn_Syntax.fvs = _35_464; Microsoft_FStar_Absyn_Syntax.uvs = _35_462}, args)) -> begin
(match ((find_uvar_t uv wl.subst)) with
| Some (t') -> begin
(let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t', args) None t.Microsoft_FStar_Absyn_Syntax.pos)
in (compress env wl t))
end
| _35_482 -> begin
t
end)
end
| _35_484 -> begin
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
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _35_506)); Microsoft_FStar_Absyn_Syntax.tk = _35_503; Microsoft_FStar_Absyn_Syntax.pos = _35_501; Microsoft_FStar_Absyn_Syntax.fvs = _35_499; Microsoft_FStar_Absyn_Syntax.uvs = _35_497}, args)) -> begin
(match ((find_uvar_e uv wl.subst)) with
| None -> begin
e
end
| Some (e') -> begin
(let e' = (compress_e env wl e')
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e', args) None e.Microsoft_FStar_Absyn_Syntax.pos))
end)
end
| _35_518 -> begin
e
end)))

let normalize_refinement = (fun ( env ) ( wl ) ( t0 ) -> (let _70_13450 = (compress env wl t0)
in (Microsoft_FStar_Tc_Normalize.normalize_refinement env _70_13450)))

let base_and_refinement = (fun ( env ) ( wl ) ( t1 ) -> (let rec aux = (fun ( norm ) ( t1 ) -> (match (t1.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi)) -> begin
(match (norm) with
| true -> begin
(x.Microsoft_FStar_Absyn_Syntax.sort, Some ((x, phi)))
end
| false -> begin
(match ((normalize_refinement env wl t1)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi)); Microsoft_FStar_Absyn_Syntax.tk = _35_539; Microsoft_FStar_Absyn_Syntax.pos = _35_537; Microsoft_FStar_Absyn_Syntax.fvs = _35_535; Microsoft_FStar_Absyn_Syntax.uvs = _35_533} -> begin
(x.Microsoft_FStar_Absyn_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _70_13463 = (let _70_13462 = (Microsoft_FStar_Absyn_Print.typ_to_string tt)
in (let _70_13461 = (Microsoft_FStar_Absyn_Print.tag_of_typ tt)
in (Support.Microsoft.FStar.Util.format2 "impossible: Got %s ... %s\n" _70_13462 _70_13461)))
in (Support.All.failwith _70_13463))
end)
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (_)) -> begin
(match (norm) with
| true -> begin
(t1, None)
end
| false -> begin
(let _35_554 = (let _70_13464 = (normalize_refinement env wl t1)
in (aux true _70_13464))
in (match (_35_554) with
| (t2', refinement) -> begin
(match (refinement) with
| None -> begin
(t1, None)
end
| _35_557 -> begin
(t2', refinement)
end)
end))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
(t1, None)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _70_13467 = (let _70_13466 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _70_13465 = (Microsoft_FStar_Absyn_Print.tag_of_typ t1)
in (Support.Microsoft.FStar.Util.format2 "impossible (outer): Got %s ... %s\n" _70_13466 _70_13465)))
in (Support.All.failwith _70_13467))
end))
in (let _70_13468 = (compress env wl t1)
in (aux false _70_13468))))

let unrefine = (fun ( env ) ( t ) -> (let _70_13473 = (base_and_refinement env (empty_worklist env) t)
in (Support.All.pipe_right _70_13473 Support.Prims.fst)))

let trivial_refinement = (fun ( t ) -> (let _70_13475 = (Microsoft_FStar_Absyn_Util.gen_bvar_p t.Microsoft_FStar_Absyn_Syntax.pos t)
in (_70_13475, Microsoft_FStar_Absyn_Util.t_true)))

let as_refinement = (fun ( env ) ( wl ) ( t ) -> (let _35_588 = (base_and_refinement env wl t)
in (match (_35_588) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some ((x, phi)) -> begin
(x, phi)
end)
end)))

let force_refinement = (fun ( _35_596 ) -> (match (_35_596) with
| (t_base, refopt) -> begin
(let _35_604 = (match (refopt) with
| Some ((y, phi)) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_35_604) with
| (y, phi) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (y, phi) None t_base.Microsoft_FStar_Absyn_Syntax.pos)
end))
end))

let rec occurs = (fun ( env ) ( wl ) ( uk ) ( t ) -> (let uvs = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (let _70_13495 = (Support.All.pipe_right uvs.Microsoft_FStar_Absyn_Syntax.uvars_t Support.Microsoft.FStar.Util.set_elements)
in (Support.All.pipe_right _70_13495 (Support.Microsoft.FStar.Util.for_some (fun ( _35_615 ) -> (match (_35_615) with
| (uvt, _35_614) -> begin
(match ((find_uvar_t uvt wl.subst)) with
| None -> begin
(Support.Microsoft.FStar.Unionfind.equivalent uvt (Support.Prims.fst uk))
end
| Some (t) -> begin
(let t = (match ((Microsoft_FStar_Absyn_Util.compress_typ t)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((_35_628, t)); Microsoft_FStar_Absyn_Syntax.tk = _35_626; Microsoft_FStar_Absyn_Syntax.pos = _35_624; Microsoft_FStar_Absyn_Syntax.fvs = _35_622; Microsoft_FStar_Absyn_Syntax.uvs = _35_620} -> begin
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
(let _70_13508 = (let _70_13507 = (Microsoft_FStar_Absyn_Print.uvar_t_to_string uk)
in (let _70_13506 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (let _70_13505 = (let _70_13504 = (Support.All.pipe_right wl.subst (Support.List.map (uvi_to_string env)))
in (Support.All.pipe_right _70_13504 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format3 "occurs-check failed (%s occurs in %s) (with substitution %s)" _70_13507 _70_13506 _70_13505))))
in Some (_70_13508))
end)
in (occurs_ok, msg))))

let occurs_and_freevars_check = (fun ( env ) ( wl ) ( uk ) ( fvs ) ( t ) -> (let fvs_t = (Microsoft_FStar_Absyn_Util.freevars_typ t)
in (let _35_649 = (occurs_check env wl uk t)
in (match (_35_649) with
| (occurs_ok, msg) -> begin
(let _70_13519 = (Microsoft_FStar_Absyn_Util.fvs_included fvs_t fvs)
in (occurs_ok, _70_13519, (msg, fvs, fvs_t)))
end))))

let occurs_check_e = (fun ( env ) ( ut ) ( e ) -> (let uvs = (Microsoft_FStar_Absyn_Util.uvars_in_exp e)
in (let occurs_ok = (not ((Support.Microsoft.FStar.Util.set_mem ut uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)))
in (let msg = (match (occurs_ok) with
| true -> begin
None
end
| false -> begin
(let _70_13531 = (let _70_13530 = (Microsoft_FStar_Absyn_Print.uvar_e_to_string ut)
in (let _70_13529 = (let _70_13527 = (let _70_13526 = (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (Support.All.pipe_right _70_13526 (Support.List.map Microsoft_FStar_Absyn_Print.uvar_e_to_string)))
in (Support.All.pipe_right _70_13527 (Support.String.concat ", ")))
in (let _70_13528 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env e)
in (Support.Microsoft.FStar.Util.format3 "occurs-check failed (%s occurs in {%s} uvars of %s)" _70_13530 _70_13529 _70_13528))))
in Some (_70_13531))
end)
in (occurs_ok, msg)))))

let intersect_vars = (fun ( v1 ) ( v2 ) -> (let fvs1 = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders v1)
in (let fvs2 = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders v2)
in (let _70_13538 = (let _70_13537 = (Support.Microsoft.FStar.Util.set_intersect fvs1.Microsoft_FStar_Absyn_Syntax.ftvs fvs2.Microsoft_FStar_Absyn_Syntax.ftvs)
in (let _70_13536 = (Support.Microsoft.FStar.Util.set_intersect fvs1.Microsoft_FStar_Absyn_Syntax.fxvs fvs2.Microsoft_FStar_Absyn_Syntax.fxvs)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _70_13537; Microsoft_FStar_Absyn_Syntax.fxvs = _70_13536}))
in (Microsoft_FStar_Absyn_Syntax.binders_of_freevars _70_13538)))))

let binders_eq = (fun ( v1 ) ( v2 ) -> (((Support.List.length v1) = (Support.List.length v2)) && (Support.List.forall2 (fun ( ax1 ) ( ax2 ) -> (match (((Support.Prims.fst ax1), (Support.Prims.fst ax2))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(Microsoft_FStar_Absyn_Util.bvar_eq a b)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Microsoft_FStar_Absyn_Util.bvar_eq x y)
end
| _35_675 -> begin
false
end)) v1 v2)))

let pat_var_opt = (fun ( env ) ( seen ) ( arg ) -> (let hd = (norm_arg env arg)
in (match ((Support.All.pipe_left Support.Prims.fst hd)) with
| Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (a); Microsoft_FStar_Absyn_Syntax.tk = _35_687; Microsoft_FStar_Absyn_Syntax.pos = _35_685; Microsoft_FStar_Absyn_Syntax.fvs = _35_683; Microsoft_FStar_Absyn_Syntax.uvs = _35_681}) -> begin
(match ((Support.All.pipe_right seen (Support.Microsoft.FStar.Util.for_some (fun ( _35_18 ) -> (match (_35_18) with
| (Support.Microsoft.FStar.Util.Inl (b), _35_696) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq a.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v)
end
| _35_699 -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
Some ((Support.Microsoft.FStar.Util.Inl (a), (Support.Prims.snd hd)))
end)
end
| Support.Microsoft.FStar.Util.Inr ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_bvar (x); Microsoft_FStar_Absyn_Syntax.tk = _35_707; Microsoft_FStar_Absyn_Syntax.pos = _35_705; Microsoft_FStar_Absyn_Syntax.fvs = _35_703; Microsoft_FStar_Absyn_Syntax.uvs = _35_701}) -> begin
(match ((Support.All.pipe_right seen (Support.Microsoft.FStar.Util.for_some (fun ( _35_19 ) -> (match (_35_19) with
| (Support.Microsoft.FStar.Util.Inr (y), _35_716) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| _35_719 -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
Some ((Support.Microsoft.FStar.Util.Inr (x), (Support.Prims.snd hd)))
end)
end
| _35_721 -> begin
None
end)))

let rec pat_vars = (fun ( env ) ( seen ) ( args ) -> (match (args) with
| [] -> begin
Some ((Support.List.rev seen))
end
| hd::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(let _35_730 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_13554 = (Microsoft_FStar_Absyn_Print.arg_to_string hd)
in (Support.Microsoft.FStar.Util.fprint1 "Not a pattern: %s\n" _70_13554))
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
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)); Microsoft_FStar_Absyn_Syntax.tk = _35_746; Microsoft_FStar_Absyn_Syntax.pos = _35_744; Microsoft_FStar_Absyn_Syntax.fvs = _35_742; Microsoft_FStar_Absyn_Syntax.uvs = _35_740}, args)) -> begin
(t, uv, k, args)
end
| _35_756 -> begin
(Support.All.failwith "Not a flex-uvar")
end))

let destruct_flex_e = (fun ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, k)) -> begin
(e, uv, k, [])
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, k)); Microsoft_FStar_Absyn_Syntax.tk = _35_769; Microsoft_FStar_Absyn_Syntax.pos = _35_767; Microsoft_FStar_Absyn_Syntax.fvs = _35_765; Microsoft_FStar_Absyn_Syntax.uvs = _35_763}, args)) -> begin
(e, uv, k, args)
end
| _35_779 -> begin
(Support.All.failwith "Not a flex-uvar")
end))

let destruct_flex_pattern = (fun ( env ) ( t ) -> (let _35_786 = (destruct_flex_t t)
in (match (_35_786) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _35_790 -> begin
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

let head_match = (fun ( _35_20 ) -> (match (_35_20) with
| MisMatch -> begin
MisMatch
end
| _35_794 -> begin
HeadMatch
end))

let rec head_matches = (fun ( t1 ) ( t2 ) -> (match ((let _70_13571 = (let _70_13568 = (Microsoft_FStar_Absyn_Util.unmeta_typ t1)
in _70_13568.Microsoft_FStar_Absyn_Syntax.n)
in (let _70_13570 = (let _70_13569 = (Microsoft_FStar_Absyn_Util.unmeta_typ t2)
in _70_13569.Microsoft_FStar_Absyn_Syntax.n)
in (_70_13571, _70_13570)))) with
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
| (Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _35_823)), Microsoft_FStar_Absyn_Syntax.Typ_refine ((y, _35_828))) -> begin
(let _70_13572 = (head_matches x.Microsoft_FStar_Absyn_Syntax.sort y.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.All.pipe_right _70_13572 head_match))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _35_834)), _35_838) -> begin
(let _70_13573 = (head_matches x.Microsoft_FStar_Absyn_Syntax.sort t2)
in (Support.All.pipe_right _70_13573 head_match))
end
| (_35_841, Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _35_844))) -> begin
(let _70_13574 = (head_matches t1 x.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.All.pipe_right _70_13574 head_match))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_35_849), Microsoft_FStar_Absyn_Syntax.Typ_fun (_35_852)) -> begin
HeadMatch
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app ((head, _35_857)), Microsoft_FStar_Absyn_Syntax.Typ_app ((head', _35_862))) -> begin
(head_matches head head')
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app ((head, _35_868)), _35_872) -> begin
(head_matches head t2)
end
| (_35_875, Microsoft_FStar_Absyn_Syntax.Typ_app ((head, _35_878))) -> begin
(head_matches t1 head)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _35_884)), Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv', _35_889))) -> begin
(match ((Support.Microsoft.FStar.Unionfind.equivalent uv uv')) with
| true -> begin
FullMatch
end
| false -> begin
MisMatch
end)
end
| (_35_894, Microsoft_FStar_Absyn_Syntax.Typ_lam (_35_896)) -> begin
HeadMatch
end
| _35_900 -> begin
MisMatch
end))

let head_matches_delta = (fun ( env ) ( wl ) ( t1 ) ( t2 ) -> (let success = (fun ( d ) ( r ) ( t1 ) ( t2 ) -> (r, (match (d) with
| true -> begin
Some ((t1, t2))
end
| false -> begin
None
end)))
in (let fail = (fun ( _35_911 ) -> (match (()) with
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

let decompose_binder = (fun ( bs ) ( v_ktec ) ( rebuild_base ) -> (let fail = (fun ( _35_925 ) -> (match (()) with
| () -> begin
(Support.All.failwith "Bad reconstruction")
end))
in (let rebuild = (fun ( ktecs ) -> (let rec aux = (fun ( new_bs ) ( bs ) ( ktecs ) -> (match ((bs, ktecs)) with
| ([], ktec::[]) -> begin
(rebuild_base (Support.List.rev new_bs) ktec)
end
| ((Support.Microsoft.FStar.Util.Inl (a), imp)::rest, Microsoft_FStar_Absyn_Syntax.K (k)::rest') -> begin
(aux (((Support.Microsoft.FStar.Util.Inl ((let _35_947 = a
in {Microsoft_FStar_Absyn_Syntax.v = _35_947.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _35_947.Microsoft_FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| ((Support.Microsoft.FStar.Util.Inr (x), imp)::rest, Microsoft_FStar_Absyn_Syntax.T ((t, _35_958))::rest') -> begin
(aux (((Support.Microsoft.FStar.Util.Inr ((let _35_963 = x
in {Microsoft_FStar_Absyn_Syntax.v = _35_963.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _35_963.Microsoft_FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| _35_966 -> begin
(fail ())
end))
in (aux [] bs ktecs)))
in (let rec mk_b_ktecs = (fun ( _35_970 ) ( _35_21 ) -> (match (_35_970) with
| (binders, b_ktecs) -> begin
(match (_35_21) with
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
in (let _70_13628 = (mk_b_ktecs ([], []) bs)
in (rebuild, _70_13628))))))

let rec decompose_kind = (fun ( env ) ( k ) -> (let fail = (fun ( _35_989 ) -> (match (()) with
| () -> begin
(Support.All.failwith "Bad reconstruction")
end))
in (let k0 = k
in (let k = (Microsoft_FStar_Absyn_Util.compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) -> begin
(let rebuild = (fun ( _35_22 ) -> (match (_35_22) with
| [] -> begin
k
end
| _35_997 -> begin
(fail ())
end))
in (rebuild, []))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(decompose_binder bs (Microsoft_FStar_Absyn_Syntax.K (k)) (fun ( bs ) ( _35_23 ) -> (match (_35_23) with
| Microsoft_FStar_Absyn_Syntax.K (k) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) k0.Microsoft_FStar_Absyn_Syntax.pos)
end
| _35_1008 -> begin
(fail ())
end)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_35_1010, k)) -> begin
(decompose_kind env k)
end
| _35_1015 -> begin
(Support.All.failwith "Impossible")
end)))))

let rec decompose_typ = (fun ( env ) ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.unmeta_typ t)
in (let matches = (fun ( t' ) -> ((head_matches t t') <> MisMatch))
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((hd, args)) -> begin
(let rebuild = (fun ( args' ) -> (let args = (Support.List.map2 (fun ( x ) ( y ) -> (match ((x, y)) with
| ((Support.Microsoft.FStar.Util.Inl (_35_1030), imp), Microsoft_FStar_Absyn_Syntax.T ((t, _35_1036))) -> begin
(Support.Microsoft.FStar.Util.Inl (t), imp)
end
| ((Support.Microsoft.FStar.Util.Inr (_35_1041), imp), Microsoft_FStar_Absyn_Syntax.E (e)) -> begin
(Support.Microsoft.FStar.Util.Inr (e), imp)
end
| _35_1049 -> begin
(Support.All.failwith "Bad reconstruction")
end)) args args')
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (hd, args) None t.Microsoft_FStar_Absyn_Syntax.pos)))
in (let b_ktecs = (Support.All.pipe_right args (Support.List.map (fun ( _35_24 ) -> (match (_35_24) with
| (Support.Microsoft.FStar.Util.Inl (t), _35_1055) -> begin
(None, INVARIANT, Microsoft_FStar_Absyn_Syntax.T ((t, None)))
end
| (Support.Microsoft.FStar.Util.Inr (e), _35_1060) -> begin
(None, INVARIANT, Microsoft_FStar_Absyn_Syntax.E (e))
end))))
in (rebuild, matches, b_ktecs)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let _35_1075 = (decompose_binder bs (Microsoft_FStar_Absyn_Syntax.C (c)) (fun ( bs ) ( _35_25 ) -> (match (_35_25) with
| Microsoft_FStar_Absyn_Syntax.C (c) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.Microsoft_FStar_Absyn_Syntax.pos)
end
| _35_1072 -> begin
(Support.All.failwith "Bad reconstruction")
end)))
in (match (_35_1075) with
| (rebuild, b_ktecs) -> begin
(rebuild, matches, b_ktecs)
end))
end
| _35_1077 -> begin
(let rebuild = (fun ( _35_26 ) -> (match (_35_26) with
| [] -> begin
t
end
| _35_1081 -> begin
(Support.All.failwith "Bad reconstruction")
end))
in (rebuild, (fun ( t ) -> true), []))
end))))

let un_T = (fun ( _35_27 ) -> (match (_35_27) with
| Microsoft_FStar_Absyn_Syntax.T ((x, _35_1087)) -> begin
x
end
| _35_1091 -> begin
(Support.All.failwith "impossible")
end))

let arg_of_ktec = (fun ( _35_28 ) -> (match (_35_28) with
| Microsoft_FStar_Absyn_Syntax.T ((t, _35_1095)) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| Microsoft_FStar_Absyn_Syntax.E (e) -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end
| _35_1101 -> begin
(Support.All.failwith "Impossible")
end))

let imitation_sub_probs = (fun ( orig ) ( env ) ( scope ) ( ps ) ( qs ) -> (let r = (p_loc orig)
in (let rel = (p_rel orig)
in (let sub_prob = (fun ( scope ) ( args ) ( q ) -> (match (q) with
| (_35_1114, variance, Microsoft_FStar_Absyn_Syntax.K (ki)) -> begin
(let _35_1121 = (new_kvar r scope)
in (match (_35_1121) with
| (gi_xs, gi) -> begin
(let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (gi, args) r)
in (let _70_13711 = (let _70_13710 = (mk_problem scope orig gi_ps (vary_rel rel variance) ki None "kind subterm")
in (Support.All.pipe_left (fun ( _70_13709 ) -> KProb (_70_13709)) _70_13710))
in (Microsoft_FStar_Absyn_Syntax.K (gi_xs), _70_13711)))
end))
end
| (_35_1124, variance, Microsoft_FStar_Absyn_Syntax.T ((ti, kopt))) -> begin
(let k = (match (kopt) with
| Some (k) -> begin
k
end
| None -> begin
(Microsoft_FStar_Tc_Recheck.recompute_kind ti)
end)
in (let _35_1137 = (new_tvar r scope k)
in (match (_35_1137) with
| (gi_xs, gi) -> begin
(let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (gi, args) None r)
in (let _70_13714 = (let _70_13713 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (Support.All.pipe_left (fun ( _70_13712 ) -> TProb (_70_13712)) _70_13713))
in (Microsoft_FStar_Absyn_Syntax.T ((gi_xs, Some (k))), _70_13714)))
end)))
end
| (_35_1140, variance, Microsoft_FStar_Absyn_Syntax.E (ei)) -> begin
(let t = (Microsoft_FStar_Tc_Recheck.recompute_typ ei)
in (let _35_1148 = (new_evar r scope t)
in (match (_35_1148) with
| (gi_xs, gi) -> begin
(let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (gi, args) (Some (t)) r)
in (let _70_13717 = (let _70_13716 = (mk_problem scope orig gi_ps (vary_rel rel variance) ei None "expression subterm")
in (Support.All.pipe_left (fun ( _70_13715 ) -> EProb (_70_13715)) _70_13716))
in (Microsoft_FStar_Absyn_Syntax.E (gi_xs), _70_13717)))
end)))
end
| (_35_1151, _35_1153, Microsoft_FStar_Absyn_Syntax.C (_35_1155)) -> begin
(Support.All.failwith "impos")
end))
in (let rec aux = (fun ( scope ) ( args ) ( qs ) -> (match (qs) with
| [] -> begin
([], [], Microsoft_FStar_Absyn_Util.t_true)
end
| q::qs -> begin
(let _35_1231 = (match (q) with
| (bopt, variance, Microsoft_FStar_Absyn_Syntax.C ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Total (ti); Microsoft_FStar_Absyn_Syntax.tk = _35_1175; Microsoft_FStar_Absyn_Syntax.pos = _35_1173; Microsoft_FStar_Absyn_Syntax.fvs = _35_1171; Microsoft_FStar_Absyn_Syntax.uvs = _35_1169})) -> begin
(match ((sub_prob scope args (bopt, variance, Microsoft_FStar_Absyn_Syntax.T ((ti, Some (Microsoft_FStar_Absyn_Syntax.ktype)))))) with
| (Microsoft_FStar_Absyn_Syntax.T ((gi_xs, _35_1183)), prob) -> begin
(let _70_13726 = (let _70_13725 = (Microsoft_FStar_Absyn_Syntax.mk_Total gi_xs)
in (Support.All.pipe_left (fun ( _70_13724 ) -> Microsoft_FStar_Absyn_Syntax.C (_70_13724)) _70_13725))
in (_70_13726, (prob)::[]))
end
| _35_1189 -> begin
(Support.All.failwith "impossible")
end)
end
| (_35_1191, _35_1193, Microsoft_FStar_Absyn_Syntax.C ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp (c); Microsoft_FStar_Absyn_Syntax.tk = _35_1201; Microsoft_FStar_Absyn_Syntax.pos = _35_1199; Microsoft_FStar_Absyn_Syntax.fvs = _35_1197; Microsoft_FStar_Absyn_Syntax.uvs = _35_1195})) -> begin
(let components = (Support.All.pipe_right c.Microsoft_FStar_Absyn_Syntax.effect_args (Support.List.map (fun ( _35_29 ) -> (match (_35_29) with
| (Support.Microsoft.FStar.Util.Inl (t), _35_1211) -> begin
(None, INVARIANT, Microsoft_FStar_Absyn_Syntax.T ((t, None)))
end
| (Support.Microsoft.FStar.Util.Inr (e), _35_1216) -> begin
(None, INVARIANT, Microsoft_FStar_Absyn_Syntax.E (e))
end))))
in (let components = ((None, COVARIANT, Microsoft_FStar_Absyn_Syntax.T ((c.Microsoft_FStar_Absyn_Syntax.result_typ, Some (Microsoft_FStar_Absyn_Syntax.ktype)))))::components
in (let _35_1222 = (let _70_13728 = (Support.List.map (sub_prob scope args) components)
in (Support.All.pipe_right _70_13728 Support.List.unzip))
in (match (_35_1222) with
| (ktecs, sub_probs) -> begin
(let gi_xs = (let _70_13733 = (let _70_13732 = (let _70_13729 = (Support.List.hd ktecs)
in (Support.All.pipe_right _70_13729 un_T))
in (let _70_13731 = (let _70_13730 = (Support.List.tl ktecs)
in (Support.All.pipe_right _70_13730 (Support.List.map arg_of_ktec)))
in {Microsoft_FStar_Absyn_Syntax.effect_name = c.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _70_13732; Microsoft_FStar_Absyn_Syntax.effect_args = _70_13731; Microsoft_FStar_Absyn_Syntax.flags = c.Microsoft_FStar_Absyn_Syntax.flags}))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp _70_13733))
in (Microsoft_FStar_Absyn_Syntax.C (gi_xs), sub_probs))
end))))
end
| _35_1225 -> begin
(let _35_1228 = (sub_prob scope args q)
in (match (_35_1228) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_35_1231) with
| (ktec, probs) -> begin
(let _35_1244 = (match (q) with
| (Some (b), _35_1235, _35_1237) -> begin
(let _70_13735 = (let _70_13734 = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder b)
in (_70_13734)::args)
in (Some (b), (b)::scope, _70_13735))
end
| _35_1240 -> begin
(None, scope, args)
end)
in (match (_35_1244) with
| (bopt, scope, args) -> begin
(let _35_1248 = (aux scope args qs)
in (match (_35_1248) with
| (sub_probs, ktecs, f) -> begin
(let f = (match (bopt) with
| None -> begin
(let _70_13738 = (let _70_13737 = (Support.All.pipe_right probs (Support.List.map (fun ( prob ) -> (Support.All.pipe_right (p_guard prob) Support.Prims.fst))))
in (f)::_70_13737)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _70_13738))
end
| Some (b) -> begin
(let _70_13742 = (let _70_13741 = (Microsoft_FStar_Absyn_Util.close_forall ((b)::[]) f)
in (let _70_13740 = (Support.All.pipe_right probs (Support.List.map (fun ( prob ) -> (Support.All.pipe_right (p_guard prob) Support.Prims.fst))))
in (_70_13741)::_70_13740))
in (Microsoft_FStar_Absyn_Util.mk_conj_l _70_13742))
end)
in ((Support.List.append probs sub_probs), (ktec)::ktecs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

type slack =
{lower : (Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.typ); upper : (Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.typ); flag : bool Support.ST.ref}

let is_Mkslack = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkslack"))

let fix_slack_uv = (fun ( _35_1261 ) ( mul ) -> (match (_35_1261) with
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

let fix_slack_vars = (fun ( slack ) -> (Support.All.pipe_right slack (Support.List.iter (fun ( _35_1267 ) -> (match (_35_1267) with
| (mul, s) -> begin
(match ((let _70_13760 = (Microsoft_FStar_Absyn_Util.compress_typ s)
in _70_13760.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(fix_slack_uv (uv, k) mul)
end
| _35_1273 -> begin
()
end)
end)))))

let fix_slack = (fun ( slack ) -> (let _35_1281 = (Support.All.pipe_left destruct_flex_t (Support.Prims.snd slack.lower))
in (match (_35_1281) with
| (_35_1276, ul, kl, _35_1280) -> begin
(let _35_1288 = (Support.All.pipe_left destruct_flex_t (Support.Prims.snd slack.upper))
in (match (_35_1288) with
| (_35_1283, uh, kh, _35_1287) -> begin
(let _35_1289 = (fix_slack_uv (ul, kl) false)
in (let _35_1291 = (fix_slack_uv (uh, kh) true)
in (let _35_1293 = (Support.ST.op_Colon_Equals slack.flag true)
in (Microsoft_FStar_Absyn_Util.mk_conj (Support.Prims.fst slack.lower) (Support.Prims.fst slack.upper)))))
end))
end)))

let new_slack_var = (fun ( env ) ( slack ) -> (let xs = (let _70_13768 = (let _70_13767 = (destruct_flex_pattern env (Support.Prims.snd slack.lower))
in (Support.All.pipe_right _70_13767 Support.Prims.snd))
in (Support.All.pipe_right _70_13768 Support.Microsoft.FStar.Util.must))
in (let _70_13769 = (new_tvar (Support.Prims.fst slack.lower).Microsoft_FStar_Absyn_Syntax.pos xs Microsoft_FStar_Absyn_Syntax.ktype)
in (_70_13769, xs))))

let new_slack_formula = (fun ( p ) ( env ) ( wl ) ( xs ) ( low ) ( high ) -> (let _35_1306 = (new_tvar p xs Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_35_1306) with
| (low_var, uv1) -> begin
(let wl = (add_slack_add uv1 wl)
in (let _35_1310 = (new_tvar p xs Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_35_1310) with
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
in (let _70_13779 = (let _70_13778 = (let _70_13777 = (let _70_13776 = (Support.Microsoft.FStar.Util.mk_ref false)
in (low, high, _70_13776))
in Microsoft_FStar_Absyn_Syntax.Meta_slack_formula (_70_13777))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _70_13778))
in (_70_13779, wl)))))
end)))
end)))

let destruct_slack = (fun ( env ) ( wl ) ( phi ) -> (let rec destruct = (fun ( conn_lid ) ( mk_conn ) ( phi ) -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _35_1334; Microsoft_FStar_Absyn_Syntax.pos = _35_1332; Microsoft_FStar_Absyn_Syntax.fvs = _35_1330; Microsoft_FStar_Absyn_Syntax.uvs = _35_1328}, (Support.Microsoft.FStar.Util.Inl (lhs), _35_1346)::(Support.Microsoft.FStar.Util.Inl (rhs), _35_1341)::[])) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v conn_lid) -> begin
(let rhs = (compress env wl rhs)
in (match (rhs.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
Some ((lhs, rhs))
end
| _35_1372 -> begin
(match ((destruct conn_lid mk_conn rhs)) with
| None -> begin
None
end
| Some ((rest, uvar)) -> begin
(let _70_13803 = (let _70_13802 = (mk_conn lhs rest)
in (_70_13802, uvar))
in Some (_70_13803))
end)
end))
end
| _35_1379 -> begin
None
end))
in (let phi = (Microsoft_FStar_Absyn_Util.compress_typ phi)
in (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((phi1, phi2, flag))) -> begin
(match ((Support.ST.read flag)) with
| true -> begin
(let _70_13804 = (Microsoft_FStar_Absyn_Util.unmeta_typ phi)
in Support.Microsoft.FStar.Util.Inl (_70_13804))
end
| false -> begin
(let low = (let _70_13805 = (compress env wl phi1)
in (Support.All.pipe_left (destruct Microsoft_FStar_Absyn_Const.or_lid Microsoft_FStar_Absyn_Util.mk_disj) _70_13805))
in (let hi = (let _70_13806 = (compress env wl phi2)
in (Support.All.pipe_left (destruct Microsoft_FStar_Absyn_Const.and_lid Microsoft_FStar_Absyn_Util.mk_disj) _70_13806))
in (match ((low, hi)) with
| (None, None) -> begin
(let _35_1392 = (Support.ST.op_Colon_Equals flag true)
in (let _70_13807 = (Microsoft_FStar_Absyn_Util.unmeta_typ phi)
in Support.Microsoft.FStar.Util.Inl (_70_13807)))
end
| ((Some (_), None)) | ((None, Some (_))) -> begin
(Support.All.failwith "Impossible")
end
| (Some (l), Some (u)) -> begin
Support.Microsoft.FStar.Util.Inr ({lower = l; upper = u; flag = flag})
end)))
end)
end
| _35_1410 -> begin
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
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar ((u1, _35_1427)), Microsoft_FStar_Absyn_Syntax.Typ_uvar ((u2, _35_1432))) -> begin
(Support.Microsoft.FStar.Unionfind.equivalent u1 u2)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app ((h1, args1)), Microsoft_FStar_Absyn_Syntax.Typ_app ((h2, args2))) -> begin
((eq_typ h1 h2) && (eq_args args1 args2))
end
| _35_1446 -> begin
false
end))))
and eq_exp = (fun ( e1 ) ( e2 ) -> (let e1 = (Microsoft_FStar_Absyn_Util.compress_exp e1)
in (let e2 = (Microsoft_FStar_Absyn_Util.compress_exp e2)
in (match ((e1.Microsoft_FStar_Absyn_Syntax.n, e2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (a), Microsoft_FStar_Absyn_Syntax.Exp_bvar (b)) -> begin
(Microsoft_FStar_Absyn_Util.bvar_eq a b)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _35_1458)), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((g, _35_1463))) -> begin
(Microsoft_FStar_Absyn_Util.fvar_eq f g)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_constant (c), Microsoft_FStar_Absyn_Syntax.Exp_constant (d)) -> begin
(c = d)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((h1, args1)), Microsoft_FStar_Absyn_Syntax.Exp_app ((h2, args2))) -> begin
((eq_exp h1 h2) && (eq_args args1 args2))
end
| _35_1482 -> begin
false
end))))
and eq_args = (fun ( a1 ) ( a2 ) -> (match (((Support.List.length a1) = (Support.List.length a2))) with
| true -> begin
(Support.List.forall2 (fun ( a1 ) ( a2 ) -> (match ((a1, a2)) with
| ((Support.Microsoft.FStar.Util.Inl (t), _35_1490), (Support.Microsoft.FStar.Util.Inl (s), _35_1495)) -> begin
(eq_typ t s)
end
| ((Support.Microsoft.FStar.Util.Inr (e), _35_1501), (Support.Microsoft.FStar.Util.Inr (f), _35_1506)) -> begin
(eq_exp e f)
end
| _35_1510 -> begin
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
(let _70_13837 = (let _35_1515 = p
in (let _70_13835 = (compress_k wl.tcenv wl p.lhs)
in (let _70_13834 = (compress_k wl.tcenv wl p.rhs)
in {lhs = _70_13835; relation = _35_1515.relation; rhs = _70_13834; element = _35_1515.element; logical_guard = _35_1515.logical_guard; scope = _35_1515.scope; reason = _35_1515.reason; loc = _35_1515.loc; rank = _35_1515.rank})))
in (Support.All.pipe_right _70_13837 (fun ( _70_13836 ) -> KProb (_70_13836))))
end
| TProb (p) -> begin
(let _70_13841 = (let _35_1519 = p
in (let _70_13839 = (compress wl.tcenv wl p.lhs)
in (let _70_13838 = (compress wl.tcenv wl p.rhs)
in {lhs = _70_13839; relation = _35_1519.relation; rhs = _70_13838; element = _35_1519.element; logical_guard = _35_1519.logical_guard; scope = _35_1519.scope; reason = _35_1519.reason; loc = _35_1519.loc; rank = _35_1519.rank})))
in (Support.All.pipe_right _70_13841 (fun ( _70_13840 ) -> TProb (_70_13840))))
end
| EProb (p) -> begin
(let _70_13845 = (let _35_1523 = p
in (let _70_13843 = (compress_e wl.tcenv wl p.lhs)
in (let _70_13842 = (compress_e wl.tcenv wl p.rhs)
in {lhs = _70_13843; relation = _35_1523.relation; rhs = _70_13842; element = _35_1523.element; logical_guard = _35_1523.logical_guard; scope = _35_1523.scope; reason = _35_1523.reason; loc = _35_1523.loc; rank = _35_1523.rank})))
in (Support.All.pipe_right _70_13845 (fun ( _70_13844 ) -> EProb (_70_13844))))
end
| CProb (_35_1526) -> begin
p
end))

let rank = (fun ( wl ) ( prob ) -> (let prob = (let _70_13850 = (compress_prob wl prob)
in (Support.All.pipe_right _70_13850 maybe_invert_p))
in (match (prob) with
| KProb (kp) -> begin
(let rank = (match ((kp.lhs.Microsoft_FStar_Absyn_Syntax.n, kp.rhs.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_35_1534), Microsoft_FStar_Absyn_Syntax.Kind_uvar (_35_1537)) -> begin
flex_flex
end
| (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_35_1541), _35_1544) -> begin
(match ((kp.relation = EQ)) with
| true -> begin
flex_rigid_eq
end
| false -> begin
flex_rigid
end)
end
| (_35_1547, Microsoft_FStar_Absyn_Syntax.Kind_uvar (_35_1549)) -> begin
(match ((kp.relation = EQ)) with
| true -> begin
flex_rigid_eq
end
| false -> begin
rigid_flex
end)
end
| (_35_1553, _35_1555) -> begin
rigid_rigid
end)
in (let _70_13852 = (Support.All.pipe_right (let _35_1558 = kp
in {lhs = _35_1558.lhs; relation = _35_1558.relation; rhs = _35_1558.rhs; element = _35_1558.element; logical_guard = _35_1558.logical_guard; scope = _35_1558.scope; reason = _35_1558.reason; loc = _35_1558.loc; rank = Some (rank)}) (fun ( _70_13851 ) -> KProb (_70_13851)))
in (rank, _70_13852)))
end
| TProb (tp) -> begin
(let _35_1565 = (Microsoft_FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_35_1565) with
| (lh, _35_1564) -> begin
(let _35_1569 = (Microsoft_FStar_Absyn_Util.head_and_args tp.rhs)
in (match (_35_1569) with
| (rh, _35_1568) -> begin
(let _35_1625 = (match ((lh.Microsoft_FStar_Absyn_Syntax.n, rh.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_35_1571), Microsoft_FStar_Absyn_Syntax.Typ_uvar (_35_1574)) -> begin
(flex_flex, tp)
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_uvar (_))) when (tp.relation = EQ) -> begin
(flex_rigid_eq, tp)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_35_1590), _35_1593) -> begin
(let _35_1597 = (base_and_refinement wl.tcenv wl tp.rhs)
in (match (_35_1597) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _35_1600 -> begin
(let rank = (match ((is_top_level_prob prob)) with
| true -> begin
flex_refine
end
| false -> begin
flex_refine_inner
end)
in (let _70_13854 = (let _35_1602 = tp
in (let _70_13853 = (force_refinement (b, ref_opt))
in {lhs = _35_1602.lhs; relation = _35_1602.relation; rhs = _70_13853; element = _35_1602.element; logical_guard = _35_1602.logical_guard; scope = _35_1602.scope; reason = _35_1602.reason; loc = _35_1602.loc; rank = _35_1602.rank}))
in (rank, _70_13854)))
end)
end))
end
| (_35_1605, Microsoft_FStar_Absyn_Syntax.Typ_uvar (_35_1607)) -> begin
(let _35_1612 = (base_and_refinement wl.tcenv wl tp.lhs)
in (match (_35_1612) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _35_1615 -> begin
(let _70_13856 = (let _35_1616 = tp
in (let _70_13855 = (force_refinement (b, ref_opt))
in {lhs = _70_13855; relation = _35_1616.relation; rhs = _35_1616.rhs; element = _35_1616.element; logical_guard = _35_1616.logical_guard; scope = _35_1616.scope; reason = _35_1616.reason; loc = _35_1616.loc; rank = _35_1616.rank}))
in (refine_flex, _70_13856))
end)
end))
end
| (_35_1619, _35_1621) -> begin
(rigid_rigid, tp)
end)
in (match (_35_1625) with
| (rank, tp) -> begin
(let _70_13858 = (Support.All.pipe_right (let _35_1626 = tp
in {lhs = _35_1626.lhs; relation = _35_1626.relation; rhs = _35_1626.rhs; element = _35_1626.element; logical_guard = _35_1626.logical_guard; scope = _35_1626.scope; reason = _35_1626.reason; loc = _35_1626.loc; rank = Some (rank)}) (fun ( _70_13857 ) -> TProb (_70_13857)))
in (rank, _70_13858))
end))
end))
end))
end
| EProb (ep) -> begin
(let _35_1633 = (Microsoft_FStar_Absyn_Util.head_and_args_e ep.lhs)
in (match (_35_1633) with
| (lh, _35_1632) -> begin
(let _35_1637 = (Microsoft_FStar_Absyn_Util.head_and_args_e ep.rhs)
in (match (_35_1637) with
| (rh, _35_1636) -> begin
(let rank = (match ((lh.Microsoft_FStar_Absyn_Syntax.n, rh.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_35_1639), Microsoft_FStar_Absyn_Syntax.Exp_uvar (_35_1642)) -> begin
flex_flex
end
| ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) -> begin
flex_rigid_eq
end
| (_35_1658, _35_1660) -> begin
rigid_rigid
end)
in (let _70_13860 = (Support.All.pipe_right (let _35_1663 = ep
in {lhs = _35_1663.lhs; relation = _35_1663.relation; rhs = _35_1663.rhs; element = _35_1663.element; logical_guard = _35_1663.logical_guard; scope = _35_1663.scope; reason = _35_1663.reason; loc = _35_1663.loc; rank = Some (rank)}) (fun ( _70_13859 ) -> EProb (_70_13859)))
in (rank, _70_13860)))
end))
end))
end
| CProb (cp) -> begin
(let _70_13862 = (Support.All.pipe_right (let _35_1667 = cp
in {lhs = _35_1667.lhs; relation = _35_1667.relation; rhs = _35_1667.rhs; element = _35_1667.element; logical_guard = _35_1667.logical_guard; scope = _35_1667.scope; reason = _35_1667.reason; loc = _35_1667.loc; rank = Some (rigid_rigid)}) (fun ( _70_13861 ) -> CProb (_70_13861)))
in (rigid_rigid, _70_13862))
end)))

let next_prob = (fun ( wl ) -> (let rec aux = (fun ( _35_1674 ) ( probs ) -> (match (_35_1674) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(let _35_1682 = (rank wl hd)
in (match (_35_1682) with
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

let rec solve_flex_rigid_join = (fun ( env ) ( tp ) ( wl ) -> (let _35_1693 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_13912 = (prob_to_string env (TProb (tp)))
in (Support.Microsoft.FStar.Util.fprint1 "Trying to solve by joining refinements:%s\n" _70_13912))
end
| false -> begin
()
end)
in (let _35_1697 = (Microsoft_FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_35_1697) with
| (u, args) -> begin
(let _35_1703 = (0, 1, 2, 3, 4)
in (match (_35_1703) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(let max = (fun ( i ) ( j ) -> (match ((i < j)) with
| true -> begin
j
end
| false -> begin
i
end))
in (let base_types_match = (fun ( t1 ) ( t2 ) -> (let _35_1712 = (Microsoft_FStar_Absyn_Util.head_and_args t1)
in (match (_35_1712) with
| (h1, args1) -> begin
(let _35_1716 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (match (_35_1716) with
| (h2, _35_1715) -> begin
(match ((h1.Microsoft_FStar_Absyn_Syntax.n, h2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_const (tc1), Microsoft_FStar_Absyn_Syntax.Typ_const (tc2)) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals tc1.Microsoft_FStar_Absyn_Syntax.v tc2.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(match (((Support.List.length args1) = 0)) with
| true -> begin
Some ([])
end
| false -> begin
(let _70_13924 = (let _70_13923 = (let _70_13922 = (new_problem env t1 EQ t2 None t1.Microsoft_FStar_Absyn_Syntax.pos "joining refinements")
in (Support.All.pipe_left (fun ( _70_13921 ) -> TProb (_70_13921)) _70_13922))
in (_70_13923)::[])
in Some (_70_13924))
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
| _35_1728 -> begin
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
(let phi2 = (let _70_13931 = (let _70_13930 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (let _70_13929 = (Microsoft_FStar_Absyn_Syntax.v_binder y)
in (Microsoft_FStar_Absyn_Util.mk_subst_one_binder _70_13930 _70_13929)))
in (Microsoft_FStar_Absyn_Util.subst_typ _70_13931 phi2))
in (let _70_13935 = (let _70_13934 = (let _70_13933 = (let _70_13932 = (Microsoft_FStar_Absyn_Util.mk_conj phi1 phi2)
in (x, _70_13932))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _70_13933 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) t1.Microsoft_FStar_Absyn_Syntax.pos))
in (_70_13934, m))
in Some (_70_13935)))
end))
end
| (_35_1747, Microsoft_FStar_Absyn_Syntax.Typ_refine ((y, _35_1750))) -> begin
(let m = (base_types_match t1 y.Microsoft_FStar_Absyn_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _35_1760)), _35_1764) -> begin
(let m = (base_types_match x.Microsoft_FStar_Absyn_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _35_1771 -> begin
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
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _35_1779)) -> begin
(let _35_1804 = (Support.All.pipe_right wl.attempting (Support.List.partition (fun ( _35_30 ) -> (match (_35_30) with
| TProb (tp) -> begin
(match (tp.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(let _35_1790 = (Microsoft_FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_35_1790) with
| (u', _35_1789) -> begin
(match ((let _70_13937 = (compress env wl u')
in _70_13937.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv', _35_1793)) -> begin
(Support.Microsoft.FStar.Unionfind.equivalent uv uv')
end
| _35_1797 -> begin
false
end)
end))
end
| _35_1799 -> begin
false
end)
end
| _35_1801 -> begin
false
end))))
in (match (_35_1804) with
| (upper_bounds, rest) -> begin
(let rec make_upper_bound = (fun ( _35_1808 ) ( tps ) -> (match (_35_1808) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| TProb (hd)::tl -> begin
(match ((let _70_13942 = (compress env wl hd.rhs)
in (conjoin bound _70_13942))) with
| Some ((bound, sub)) -> begin
(make_upper_bound (bound, (Support.List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _35_1821 -> begin
None
end)
end))
in (match ((let _70_13944 = (let _70_13943 = (compress env wl tp.rhs)
in (_70_13943, []))
in (make_upper_bound _70_13944 upper_bounds))) with
| None -> begin
(let _35_1823 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
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
in (match ((solve_t env eq_prob (let _35_1830 = wl
in {attempting = sub_probs; deferred = _35_1830.deferred; subst = _35_1830.subst; ctr = _35_1830.ctr; slack_vars = _35_1830.slack_vars; defer_ok = _35_1830.defer_ok; smt_ok = _35_1830.smt_ok; tcenv = _35_1830.tcenv}))) with
| Success ((subst, _35_1834)) -> begin
(let wl = (let _35_1837 = wl
in {attempting = rest; deferred = _35_1837.deferred; subst = []; ctr = _35_1837.ctr; slack_vars = _35_1837.slack_vars; defer_ok = _35_1837.defer_ok; smt_ok = _35_1837.smt_ok; tcenv = _35_1837.tcenv})
in (let wl = (solve_prob (TProb (tp)) None subst wl)
in (let _35_1843 = (Support.List.fold_left (fun ( wl ) ( p ) -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _35_1846 -> begin
None
end))
end))
end))
end
| _35_1848 -> begin
(Support.All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve = (fun ( env ) ( probs ) -> (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(let probs = (let _35_1856 = probs
in {attempting = tl; deferred = _35_1856.deferred; subst = _35_1856.subst; ctr = _35_1856.ctr; slack_vars = _35_1856.slack_vars; defer_ok = _35_1856.defer_ok; smt_ok = _35_1856.smt_ok; tcenv = _35_1856.tcenv})
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
| (None, _35_1872, _35_1874) -> begin
(match (probs.deferred) with
| [] -> begin
Success ((probs.subst, {carry = []; slack = probs.slack_vars}))
end
| _35_1878 -> begin
(let _35_1887 = (Support.All.pipe_right probs.deferred (Support.List.partition (fun ( _35_1884 ) -> (match (_35_1884) with
| (c, _35_1881, _35_1883) -> begin
(c < probs.ctr)
end))))
in (match (_35_1887) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _70_13953 = (let _70_13952 = (let _70_13951 = (Support.List.map (fun ( _35_1893 ) -> (match (_35_1893) with
| (_35_1890, x, y) -> begin
(x, y)
end)) probs.deferred)
in {carry = _70_13951; slack = probs.slack_vars})
in (probs.subst, _70_13952))
in Success (_70_13953))
end
| _35_1895 -> begin
(let _70_13956 = (let _35_1896 = probs
in (let _70_13955 = (Support.All.pipe_right attempt (Support.List.map (fun ( _35_1903 ) -> (match (_35_1903) with
| (_35_1899, _35_1901, y) -> begin
y
end))))
in {attempting = _70_13955; deferred = rest; subst = _35_1896.subst; ctr = _35_1896.ctr; slack_vars = _35_1896.slack_vars; defer_ok = _35_1896.defer_ok; smt_ok = _35_1896.smt_ok; tcenv = _35_1896.tcenv}))
in (solve env _70_13956))
end)
end))
end)
end))
and solve_binders = (fun ( env ) ( bs1 ) ( bs2 ) ( orig ) ( wl ) ( rhs ) -> (let rec aux = (fun ( scope ) ( env ) ( subst ) ( xs ) ( ys ) -> (match ((xs, ys)) with
| ([], []) -> begin
(let rhs_prob = (rhs scope env subst)
in (let formula = (Support.All.pipe_right (p_guard rhs_prob) Support.Prims.fst)
in Support.Microsoft.FStar.Util.Inl (((rhs_prob)::[], formula))))
end
| (((Support.Microsoft.FStar.Util.Inl (_), _)::_, (Support.Microsoft.FStar.Util.Inr (_), _)::_)) | (((Support.Microsoft.FStar.Util.Inr (_), _)::_, (Support.Microsoft.FStar.Util.Inl (_), _)::_)) -> begin
Support.Microsoft.FStar.Util.Inr ("sort mismatch")
end
| (hd1::xs, hd2::ys) -> begin
(let subst = (let _70_13982 = (Microsoft_FStar_Absyn_Util.mk_subst_one_binder hd2 hd1)
in (Support.List.append _70_13982 subst))
in (let env = (let _70_13983 = (Microsoft_FStar_Tc_Env.binding_of_binder hd2)
in (Microsoft_FStar_Tc_Env.push_local_binding env _70_13983))
in (let prob = (match (((Support.Prims.fst hd1), (Support.Prims.fst hd2))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(let _70_13987 = (let _70_13986 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _70_13985 = (Support.All.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _70_13986 _70_13985 b.Microsoft_FStar_Absyn_Syntax.sort None "Formal type parameter")))
in (Support.All.pipe_left (fun ( _70_13984 ) -> KProb (_70_13984)) _70_13987))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(let _70_13991 = (let _70_13990 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _70_13989 = (Support.All.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _70_13990 _70_13989 y.Microsoft_FStar_Absyn_Syntax.sort None "Formal value parameter")))
in (Support.All.pipe_left (fun ( _70_13988 ) -> TProb (_70_13988)) _70_13991))
end
| _35_1979 -> begin
(Support.All.failwith "impos")
end)
in (match ((aux ((hd2)::scope) env subst xs ys)) with
| Support.Microsoft.FStar.Util.Inr (msg) -> begin
Support.Microsoft.FStar.Util.Inr (msg)
end
| Support.Microsoft.FStar.Util.Inl ((sub_probs, phi)) -> begin
(let phi = (let _70_13993 = (Support.All.pipe_right (p_guard prob) Support.Prims.fst)
in (let _70_13992 = (Microsoft_FStar_Absyn_Util.close_forall ((hd2)::[]) phi)
in (Microsoft_FStar_Absyn_Util.mk_conj _70_13993 _70_13992)))
in Support.Microsoft.FStar.Util.Inl (((prob)::sub_probs, phi)))
end))))
end
| _35_1989 -> begin
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
| _35_2004 -> begin
(Support.All.failwith "impossible")
end))
and solve_k' = (fun ( env ) ( problem ) ( wl ) -> (let orig = KProb (problem)
in (match ((Support.Microsoft.FStar.Util.physical_equality problem.lhs problem.rhs)) with
| true -> begin
(let _70_14000 = (solve_prob orig None [] wl)
in (solve env _70_14000))
end
| false -> begin
(let k1 = problem.lhs
in (let k2 = problem.rhs
in (match ((Support.Microsoft.FStar.Util.physical_equality k1 k2)) with
| true -> begin
(let _70_14001 = (solve_prob orig None [] wl)
in (solve env _70_14001))
end
| false -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let imitate_k = (fun ( _35_2020 ) -> (match (_35_2020) with
| (rel, u, ps, xs, (h, qs)) -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let _35_2025 = (imitation_sub_probs orig env xs ps qs)
in (match (_35_2025) with
| (sub_probs, gs_xs, f) -> begin
(let im = (let _70_14017 = (let _70_14016 = (h gs_xs)
in (xs, _70_14016))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam _70_14017 r))
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
in (let _70_14026 = (solve_prob orig None ((UK ((u, k1)))::[]) wl)
in (solve env _70_14026)))
end
| false -> begin
(let _70_14031 = (let _70_14030 = (Support.All.pipe_right xs Microsoft_FStar_Absyn_Util.args_of_non_null_binders)
in (let _70_14029 = (decompose_kind env k)
in (rel, u, _70_14030, xs, _70_14029)))
in (imitate_k _70_14031))
end))))
end
| None -> begin
(giveup env "flex-rigid: not a pattern" (KProb (problem)))
end)))
in (match ((k1.Microsoft_FStar_Absyn_Syntax.n, k2.Microsoft_FStar_Absyn_Syntax.n)) with
| ((Microsoft_FStar_Absyn_Syntax.Kind_type, Microsoft_FStar_Absyn_Syntax.Kind_type)) | ((Microsoft_FStar_Absyn_Syntax.Kind_effect, Microsoft_FStar_Absyn_Syntax.Kind_effect)) -> begin
(let _70_14032 = (solve_prob orig None [] wl)
in (Support.All.pipe_left (solve env) _70_14032))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_35_2048, k1)), _35_2053) -> begin
(solve_k env (let _35_2055 = problem
in {lhs = k1; relation = _35_2055.relation; rhs = _35_2055.rhs; element = _35_2055.element; logical_guard = _35_2055.logical_guard; scope = _35_2055.scope; reason = _35_2055.reason; loc = _35_2055.loc; rank = _35_2055.rank}) wl)
end
| (_35_2058, Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_35_2060, k2))) -> begin
(solve_k env (let _35_2065 = problem
in {lhs = _35_2065.lhs; relation = _35_2065.relation; rhs = k2; element = _35_2065.element; logical_guard = _35_2065.logical_guard; scope = _35_2065.scope; reason = _35_2065.reason; loc = _35_2065.loc; rank = _35_2065.rank}) wl)
end
| (Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs1, k1')), Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs2, k2'))) -> begin
(let sub_prob = (fun ( scope ) ( env ) ( subst ) -> (let _70_14041 = (let _70_14040 = (Microsoft_FStar_Absyn_Util.subst_kind subst k1')
in (mk_problem scope orig _70_14040 problem.relation k2' None "Arrow-kind result"))
in (Support.All.pipe_left (fun ( _70_14039 ) -> KProb (_70_14039)) _70_14041)))
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
in (let _35_2108 = (new_kvar r zs)
in (match (_35_2108) with
| (u, _35_2107) -> begin
(let k1 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam (xs, u) r)
in (let k2 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam (ys, u) r)
in (let wl = (solve_prob orig None ((UK ((u1, k1)))::(UK ((u2, k2)))::[]) wl)
in (solve env wl))))
end)))
end)
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_uvar ((u, args)), _35_2117) -> begin
(flex_rigid problem.relation u args k2)
end
| (_35_2120, Microsoft_FStar_Absyn_Syntax.Kind_uvar ((u, args))) -> begin
(flex_rigid (invert_rel problem.relation) u args k1)
end
| ((Microsoft_FStar_Absyn_Syntax.Kind_delayed (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Kind_unknown, _)) | ((_, Microsoft_FStar_Absyn_Syntax.Kind_delayed (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Kind_unknown)) -> begin
(Support.All.failwith "Impossible")
end
| _35_2147 -> begin
(giveup env "head mismatch (k-1)" (KProb (problem)))
end))))
end)))
end)))
and solve_t = (fun ( env ) ( problem ) ( wl ) -> (let p = (compress_prob wl (TProb (problem)))
in (match (p) with
| TProb (p) -> begin
(solve_t' env p wl)
end
| _35_2155 -> begin
(Support.All.failwith "Impossible")
end)))
and solve_t' = (fun ( env ) ( problem ) ( wl ) -> (let giveup_or_defer = (fun ( orig ) ( msg ) -> (match (wl.defer_ok) with
| true -> begin
(let _35_2162 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14052 = (prob_to_string env orig)
in (Support.Microsoft.FStar.Util.fprint2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _70_14052 msg))
end
| false -> begin
()
end)
in (solve env (defer msg orig wl)))
end
| false -> begin
(giveup env msg orig)
end))
in (let imitate_t = (fun ( orig ) ( env ) ( wl ) ( p ) -> (let _35_2179 = p
in (match (_35_2179) with
| ((u, k), ps, xs, (h, _35_2176, qs)) -> begin
(let xs = (sn_binders env xs)
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let _35_2185 = (imitation_sub_probs orig env xs ps qs)
in (match (_35_2185) with
| (sub_probs, gs_xs, formula) -> begin
(let im = (let _70_14064 = (let _70_14063 = (h gs_xs)
in (xs, _70_14063))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' _70_14064 None r))
in (let _35_2187 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14069 = (Microsoft_FStar_Absyn_Print.typ_to_string im)
in (let _70_14068 = (Microsoft_FStar_Absyn_Print.tag_of_typ im)
in (let _70_14067 = (let _70_14065 = (Support.List.map (prob_to_string env) sub_probs)
in (Support.All.pipe_right _70_14065 (Support.String.concat ", ")))
in (let _70_14066 = (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env formula)
in (Support.Microsoft.FStar.Util.fprint4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _70_14069 _70_14068 _70_14067 _70_14066)))))
end
| false -> begin
()
end)
in (let wl = (solve_prob orig (Some (formula)) ((UT (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (let project_t = (fun ( orig ) ( env ) ( wl ) ( i ) ( p ) -> (let _35_2203 = p
in (match (_35_2203) with
| (u, ps, xs, (h, matches, qs)) -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let pi = (Support.List.nth ps i)
in (let rec gs = (fun ( k ) -> (let _35_2210 = (Microsoft_FStar_Absyn_Util.kind_formals k)
in (match (_35_2210) with
| (bs, k) -> begin
(let rec aux = (fun ( subst ) ( bs ) -> (match (bs) with
| [] -> begin
([], [])
end
| hd::tl -> begin
(let _35_2239 = (match ((Support.Prims.fst hd)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let k_a = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _35_2223 = (new_tvar r xs k_a)
in (match (_35_2223) with
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
in (let _70_14089 = (Microsoft_FStar_Absyn_Syntax.targ gi_xs)
in (let _70_14088 = (Microsoft_FStar_Absyn_Syntax.targ gi_ps)
in (_70_14089, _70_14088, subst))))))
end)))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let t_x = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _35_2232 = (new_evar r xs t_x)
in (match (_35_2232) with
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
in (let _70_14091 = (Microsoft_FStar_Absyn_Syntax.varg gi_xs)
in (let _70_14090 = (Microsoft_FStar_Absyn_Syntax.varg gi_ps)
in (_70_14091, _70_14090, subst))))))
end)))
end)
in (match (_35_2239) with
| (gi_xs, gi_ps, subst) -> begin
(let _35_2242 = (aux subst tl)
in (match (_35_2242) with
| (gi_xs', gi_ps') -> begin
((gi_xs)::gi_xs', (gi_ps)::gi_ps')
end))
end))
end))
in (aux [] bs))
end)))
in (match ((let _70_14093 = (let _70_14092 = (Support.List.nth xs i)
in (Support.All.pipe_left Support.Prims.fst _70_14092))
in ((Support.Prims.fst pi), _70_14093))) with
| (Support.Microsoft.FStar.Util.Inl (pi), Support.Microsoft.FStar.Util.Inl (xi)) -> begin
(match ((let _70_14094 = (matches pi)
in (Support.All.pipe_left Support.Prims.op_Negation _70_14094))) with
| true -> begin
None
end
| false -> begin
(let _35_2251 = (gs xi.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_35_2251) with
| (g_xs, _35_2250) -> begin
(let xi = (Microsoft_FStar_Absyn_Util.btvar_to_typ xi)
in (let proj = (let _70_14096 = (let _70_14095 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (xi, g_xs) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)
in (xs, _70_14095))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_14096 None r))
in (let sub = (let _70_14102 = (let _70_14101 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (proj, ps) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)
in (let _70_14100 = (let _70_14099 = (Support.List.map (fun ( _35_2259 ) -> (match (_35_2259) with
| (_35_2255, _35_2257, y) -> begin
y
end)) qs)
in (Support.All.pipe_left h _70_14099))
in (mk_problem (p_scope orig) orig _70_14101 (p_rel orig) _70_14100 None "projection")))
in (Support.All.pipe_left (fun ( _70_14097 ) -> TProb (_70_14097)) _70_14102))
in (let _35_2261 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14104 = (Microsoft_FStar_Absyn_Print.typ_to_string proj)
in (let _70_14103 = (prob_to_string env sub)
in (Support.Microsoft.FStar.Util.fprint2 "Projecting %s\n\tsubprob=%s\n" _70_14104 _70_14103)))
end
| false -> begin
()
end)
in (let wl = (let _70_14106 = (let _70_14105 = (Support.All.pipe_left Support.Prims.fst (p_guard sub))
in Some (_70_14105))
in (solve_prob orig _70_14106 ((UT ((u, proj)))::[]) wl))
in (let _70_14108 = (solve env (attempt ((sub)::[]) wl))
in (Support.All.pipe_left (fun ( _70_14107 ) -> Some (_70_14107)) _70_14108)))))))
end))
end)
end
| _35_2265 -> begin
None
end))))
end)))
in (let solve_t_flex_rigid = (fun ( orig ) ( lhs ) ( t2 ) ( wl ) -> (let _35_2277 = lhs
in (match (_35_2277) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(let subterms = (fun ( ps ) -> (let xs = (let _70_14135 = (Microsoft_FStar_Absyn_Util.kind_formals k)
in (Support.All.pipe_right _70_14135 Support.Prims.fst))
in (let xs = (Microsoft_FStar_Absyn_Util.name_binders xs)
in (let _70_14140 = (decompose_typ env t2)
in ((uv, k), ps, xs, _70_14140)))))
in (let rec imitate_or_project = (fun ( n ) ( st ) ( i ) -> (match ((i >= n)) with
| true -> begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end
| false -> begin
(match ((i = (- (1)))) with
| true -> begin
(match ((imitate_t orig env wl st)) with
| Failed (_35_2287) -> begin
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
in (let check_head = (fun ( fvs1 ) ( t2 ) -> (let _35_2303 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (match (_35_2303) with
| (hd, _35_2302) -> begin
(match (hd.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| _35_2314 -> begin
(let fvs_hd = (Microsoft_FStar_Absyn_Util.freevars_typ hd)
in (match ((Microsoft_FStar_Absyn_Util.fvs_included fvs_hd fvs1)) with
| true -> begin
true
end
| false -> begin
(let _35_2316 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14151 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs_hd)
in (Support.Microsoft.FStar.Util.fprint1 "Free variables are %s" _70_14151))
end
| false -> begin
()
end)
in false)
end))
end)
end)))
in (let imitate_ok = (fun ( t2 ) -> (let fvs_hd = (let _70_14155 = (let _70_14154 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (Support.All.pipe_right _70_14154 Support.Prims.fst))
in (Support.All.pipe_right _70_14155 Microsoft_FStar_Absyn_Util.freevars_typ))
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
in (let _35_2329 = (occurs_check env wl (uv, k) t2)
in (match (_35_2329) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(let _70_14157 = (let _70_14156 = (Support.Option.get msg)
in (Support.String.strcat "occurs-check failed: " _70_14156))
in (giveup_or_defer orig _70_14157))
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Util.fvs_included fvs2 fvs1)) with
| true -> begin
(match (((Microsoft_FStar_Absyn_Util.is_function_typ t2) && ((p_rel orig) <> EQ))) with
| true -> begin
(let _70_14158 = (subterms args_lhs)
in (imitate_t orig env wl _70_14158))
end
| false -> begin
(let _35_2330 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14161 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _70_14160 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs1)
in (let _70_14159 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs2)
in (Support.Microsoft.FStar.Util.fprint3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _70_14161 _70_14160 _70_14159))))
end
| false -> begin
()
end)
in (let sol = (match (vars) with
| [] -> begin
t2
end
| _35_2334 -> begin
(let _70_14163 = (let _70_14162 = (sn_binders env vars)
in (_70_14162, t2))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_14163 None t1.Microsoft_FStar_Absyn_Syntax.pos))
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
(let _35_2337 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14166 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _70_14165 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs1)
in (let _70_14164 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs2)
in (Support.Microsoft.FStar.Util.fprint3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _70_14166 _70_14165 _70_14164))))
end
| false -> begin
()
end)
in (let _70_14167 = (subterms args_lhs)
in (imitate_or_project (Support.List.length args_lhs) _70_14167 (- (1)))))
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
(match ((let _70_14168 = (Microsoft_FStar_Absyn_Util.freevars_typ t1)
in (check_head _70_14168 t2))) with
| true -> begin
(let im_ok = (imitate_ok t2)
in (let _35_2341 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14169 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Support.Microsoft.FStar.Util.fprint2 "Not a pattern (%s) ... %s\n" _70_14169 (match ((im_ok < 0)) with
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
in (let _70_14170 = (subterms args_lhs)
in (imitate_or_project (Support.List.length args_lhs) _70_14170 im_ok))))
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
(let force_quasi_pattern = (fun ( xs_opt ) ( _35_2353 ) -> (match (_35_2353) with
| (t, u, k, args) -> begin
(let rec aux = (fun ( binders ) ( ys ) ( args ) -> (match (args) with
| [] -> begin
(let ys = (Support.List.rev ys)
in (let binders = (Support.List.rev binders)
in (let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (let _35_2365 = (new_tvar t.Microsoft_FStar_Absyn_Syntax.pos ys kk)
in (match (_35_2365) with
| (t', _35_2364) -> begin
(let _35_2371 = (destruct_flex_t t')
in (match (_35_2371) with
| (u1_ys, u1, k1, _35_2370) -> begin
(let sol = (let _70_14188 = (let _70_14187 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, u1_ys) (Some (k)) t.Microsoft_FStar_Absyn_Syntax.pos)
in ((u, k), _70_14187))
in UT (_70_14188))
in (sol, (t', u, k1, ys)))
end))
end)))))
end
| hd::tl -> begin
(let new_binder = (fun ( hd ) -> (match ((Support.Prims.fst hd)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _70_14192 = (let _70_14191 = (Microsoft_FStar_Tc_Recheck.recompute_kind a)
in (Support.All.pipe_right _70_14191 (Microsoft_FStar_Absyn_Util.gen_bvar_p a.Microsoft_FStar_Absyn_Syntax.pos)))
in (Support.All.pipe_right _70_14192 Microsoft_FStar_Absyn_Syntax.t_binder))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _70_14194 = (let _70_14193 = (Microsoft_FStar_Tc_Recheck.recompute_typ x)
in (Support.All.pipe_right _70_14193 (Microsoft_FStar_Absyn_Util.gen_bvar_p x.Microsoft_FStar_Absyn_Syntax.pos)))
in (Support.All.pipe_right _70_14194 Microsoft_FStar_Absyn_Syntax.v_binder))
end))
in (let _35_2390 = (match ((pat_var_opt env ys hd)) with
| None -> begin
(let _70_14195 = (new_binder hd)
in (_70_14195, ys))
end
| Some (y) -> begin
(match (xs_opt) with
| None -> begin
(y, (y)::ys)
end
| Some (xs) -> begin
(match ((Support.All.pipe_right xs (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Util.eq_binder y)))) with
| true -> begin
(y, (y)::ys)
end
| false -> begin
(let _70_14196 = (new_binder hd)
in (_70_14196, ys))
end)
end)
end)
in (match (_35_2390) with
| (binder, ys) -> begin
(aux ((binder)::binders) ys tl)
end)))
end))
in (aux [] [] args))
end))
in (let solve_both_pats = (fun ( wl ) ( _35_2396 ) ( _35_2400 ) ( k ) ( r ) -> (match ((_35_2396, _35_2400)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
(match (((Support.Microsoft.FStar.Unionfind.equivalent u1 u2) && (binders_eq xs ys))) with
| true -> begin
(let _70_14207 = (solve_prob orig None [] wl)
in (solve env _70_14207))
end
| false -> begin
(let xs = (sn_binders env xs)
in (let ys = (sn_binders env ys)
in (let zs = (intersect_vars xs ys)
in (let _35_2409 = (new_tvar r zs k)
in (match (_35_2409) with
| (u_zs, _35_2408) -> begin
(let sub1 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' (xs, u_zs) (Some (k1)) r)
in (let _35_2413 = (occurs_check env wl (u1, k1) sub1)
in (match (_35_2413) with
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
in (let _35_2419 = (occurs_check env wl (u2, k2) sub2)
in (match (_35_2419) with
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
in (let solve_one_pat = (fun ( _35_2427 ) ( _35_2432 ) -> (match ((_35_2427, _35_2432)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(let _35_2433 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14213 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _70_14212 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (Support.Microsoft.FStar.Util.fprint2 "Trying flex-flex one pattern (%s) with %s\n" _70_14213 _70_14212)))
end
| false -> begin
()
end)
in (match ((Support.Microsoft.FStar.Unionfind.equivalent u1 u2)) with
| true -> begin
(let sub_probs = (Support.List.map2 (fun ( a ) ( b ) -> (let a = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder a)
in (match (((Support.Prims.fst a), (Support.Prims.fst b))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
(let _70_14217 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (Support.All.pipe_right _70_14217 (fun ( _70_14216 ) -> TProb (_70_14216))))
end
| (Support.Microsoft.FStar.Util.Inr (t1), Support.Microsoft.FStar.Util.Inr (t2)) -> begin
(let _70_14219 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (Support.All.pipe_right _70_14219 (fun ( _70_14218 ) -> EProb (_70_14218))))
end
| _35_2449 -> begin
(Support.All.failwith "Impossible")
end))) xs args2)
in (let guard = (let _70_14221 = (Support.List.map (fun ( p ) -> (Support.All.pipe_right (p_guard p) Support.Prims.fst)) sub_probs)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _70_14221))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end
| false -> begin
(let t2 = (sn env t2)
in (let rhs_vars = (Microsoft_FStar_Absyn_Util.freevars_typ t2)
in (let _35_2459 = (occurs_check env wl (u1, k1) t2)
in (match (_35_2459) with
| (occurs_ok, _35_2458) -> begin
(let lhs_vars = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders xs)
in (match ((occurs_ok && (Microsoft_FStar_Absyn_Util.fvs_included rhs_vars lhs_vars))) with
| true -> begin
(let sol = (let _70_14223 = (let _70_14222 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' (xs, t2) (Some (k1)) t1.Microsoft_FStar_Absyn_Syntax.pos)
in ((u1, k1), _70_14222))
in UT (_70_14223))
in (let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end
| false -> begin
(match ((occurs_ok && (Support.All.pipe_left Support.Prims.op_Negation wl.defer_ok))) with
| true -> begin
(let _35_2470 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_35_2470) with
| (sol, (_35_2465, u2, k2, ys)) -> begin
(let wl = (extend_solution sol wl)
in (let _35_2472 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("QuasiPattern")))) with
| true -> begin
(let _70_14224 = (uvi_to_string env sol)
in (Support.Microsoft.FStar.Util.fprint1 "flex-flex quasi pattern (2): %s\n" _70_14224))
end
| false -> begin
()
end)
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _35_2477 -> begin
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
in (let _35_2482 = lhs
in (match (_35_2482) with
| (t1, u1, k1, args1) -> begin
(let _35_2487 = rhs
in (match (_35_2487) with
| (t2, u2, k2, args2) -> begin
(let maybe_pat_vars1 = (pat_vars env [] args1)
in (let maybe_pat_vars2 = (pat_vars env [] args2)
in (let r = t2.Microsoft_FStar_Absyn_Syntax.pos
in (match ((maybe_pat_vars1, maybe_pat_vars2)) with
| (Some (xs), Some (ys)) -> begin
(let _70_14225 = (Microsoft_FStar_Tc_Recheck.recompute_kind t2)
in (solve_both_pats wl (u1, k1, xs) (u2, k2, ys) _70_14225 t2.Microsoft_FStar_Absyn_Syntax.pos))
end
| (Some (xs), None) -> begin
(solve_one_pat (t1, u1, k1, xs) rhs)
end
| (None, Some (ys)) -> begin
(solve_one_pat (t2, u2, k2, ys) lhs)
end
| _35_2505 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end
| false -> begin
(let _35_2509 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_35_2509) with
| (sol, _35_2508) -> begin
(let wl = (extend_solution sol wl)
in (let _35_2511 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("QuasiPattern")))) with
| true -> begin
(let _70_14226 = (uvi_to_string env sol)
in (Support.Microsoft.FStar.Util.fprint1 "flex-flex quasi pattern (1): %s\n" _70_14226))
end
| false -> begin
()
end)
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _35_2516 -> begin
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
(let _70_14227 = (solve_prob orig None [] wl)
in (solve env _70_14227))
end
| false -> begin
(let t1 = problem.lhs
in (let t2 = problem.rhs
in (match ((Support.Microsoft.FStar.Util.physical_equality t1 t2)) with
| true -> begin
(let _70_14228 = (solve_prob orig None [] wl)
in (solve env _70_14228))
end
| false -> begin
(let _35_2520 = (match ((Microsoft_FStar_Tc_Env.debug env (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14231 = (prob_to_string env orig)
in (let _70_14230 = (let _70_14229 = (Support.List.map (uvi_to_string wl.tcenv) wl.subst)
in (Support.All.pipe_right _70_14229 (Support.String.concat "; ")))
in (Support.Microsoft.FStar.Util.fprint2 "Attempting %s\n\tSubst is %s\n" _70_14231 _70_14230)))
end
| false -> begin
()
end)
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let match_num_binders = (fun ( _35_2525 ) ( _35_2528 ) -> (match ((_35_2525, _35_2528)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(let curry = (fun ( n ) ( bs ) ( mk_cod ) -> (let _35_2535 = (Support.Microsoft.FStar.Util.first_N n bs)
in (match (_35_2535) with
| (bs, rest) -> begin
(let _70_14261 = (mk_cod rest)
in (bs, _70_14261))
end)))
in (let l1 = (Support.List.length bs1)
in (let l2 = (Support.List.length bs2)
in (match ((l1 = l2)) with
| true -> begin
(let _70_14265 = (let _70_14262 = (mk_cod1 [])
in (bs1, _70_14262))
in (let _70_14264 = (let _70_14263 = (mk_cod2 [])
in (bs2, _70_14263))
in (_70_14265, _70_14264)))
end
| false -> begin
(match ((l1 > l2)) with
| true -> begin
(let _70_14268 = (curry l2 bs1 mk_cod1)
in (let _70_14267 = (let _70_14266 = (mk_cod2 [])
in (bs2, _70_14266))
in (_70_14268, _70_14267)))
end
| false -> begin
(let _70_14271 = (let _70_14269 = (mk_cod1 [])
in (bs1, _70_14269))
in (let _70_14270 = (curry l1 bs2 mk_cod2)
in (_70_14271, _70_14270)))
end)
end))))
end))
in (match ((t1.Microsoft_FStar_Absyn_Syntax.n, t2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvd_eq a.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(let _70_14272 = (solve_prob orig None [] wl)
in (solve env _70_14272))
end
| false -> begin
(let _70_14276 = (let _70_14275 = (let _70_14274 = (Microsoft_FStar_Absyn_Util.mk_eq_typ t1 t2)
in (Support.All.pipe_left (fun ( _70_14273 ) -> Some (_70_14273)) _70_14274))
in (solve_prob orig _70_14275 [] wl))
in (solve env _70_14276))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs1, c1)), Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs2, c2))) -> begin
(let mk_c = (fun ( c ) ( _35_31 ) -> (match (_35_31) with
| [] -> begin
c
end
| bs -> begin
(let _70_14281 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None c.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Total _70_14281))
end))
in (let _35_2566 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_35_2566) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun ( scope ) ( env ) ( subst ) -> (let c1 = (Microsoft_FStar_Absyn_Util.subst_comp subst c1)
in (let rel = (match ((Support.ST.read Microsoft_FStar_Options.use_eq_at_higher_order)) with
| true -> begin
EQ
end
| false -> begin
problem.relation
end)
in (let _35_2572 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("EQ")))) with
| true -> begin
(let _70_14288 = (let _70_14287 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.All.pipe_right _70_14287 Support.Microsoft.FStar.Range.string_of_range))
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Using relation %s at higher order\n" _70_14288 (rel_to_string rel)))
end
| false -> begin
()
end)
in (let _70_14290 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (Support.All.pipe_left (fun ( _70_14289 ) -> CProb (_70_14289)) _70_14290)))))))
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs1, t1')), Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs2, t2'))) -> begin
(let mk_t = (fun ( t ) ( _35_32 ) -> (match (_35_32) with
| [] -> begin
t
end
| bs -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (let _35_2594 = (match_num_binders (bs1, (mk_t t1')) (bs2, (mk_t t2')))
in (match (_35_2594) with
| ((bs1, t1'), (bs2, t2')) -> begin
(solve_binders env bs1 bs2 orig wl (fun ( scope ) ( env ) ( subst ) -> (let t1' = (Microsoft_FStar_Absyn_Util.subst_typ subst t1')
in (let _70_14301 = (mk_problem scope orig t1' problem.relation t2' None "lambda co-domain")
in (Support.All.pipe_left (fun ( _70_14300 ) -> TProb (_70_14300)) _70_14301)))))
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine (_35_2600), Microsoft_FStar_Absyn_Syntax.Typ_refine (_35_2603)) -> begin
(let _35_2608 = (as_refinement env wl t1)
in (match (_35_2608) with
| (x1, phi1) -> begin
(let _35_2611 = (as_refinement env wl t2)
in (match (_35_2611) with
| (x2, phi2) -> begin
(let base_prob = (let _70_14303 = (mk_problem (p_scope orig) orig x1.Microsoft_FStar_Absyn_Syntax.sort problem.relation x2.Microsoft_FStar_Absyn_Syntax.sort problem.element "refinement base type")
in (Support.All.pipe_left (fun ( _70_14302 ) -> TProb (_70_14302)) _70_14303))
in (let x1_for_x2 = (let _70_14305 = (Microsoft_FStar_Absyn_Syntax.v_binder x1)
in (let _70_14304 = (Microsoft_FStar_Absyn_Syntax.v_binder x2)
in (Microsoft_FStar_Absyn_Util.mk_subst_one_binder _70_14305 _70_14304)))
in (let phi2 = (Microsoft_FStar_Absyn_Util.subst_typ x1_for_x2 phi2)
in (let mk_imp = (fun ( imp ) ( phi1 ) ( phi2 ) -> (let _70_14322 = (imp phi1 phi2)
in (Support.All.pipe_right _70_14322 (guard_on_element problem x1))))
in (let fallback = (fun ( _35_2620 ) -> (match (()) with
| () -> begin
(let impl = (match ((problem.relation = EQ)) with
| true -> begin
(mk_imp Microsoft_FStar_Absyn_Util.mk_iff phi1 phi2)
end
| false -> begin
(mk_imp Microsoft_FStar_Absyn_Util.mk_imp phi1 phi2)
end)
in (let guard = (let _70_14325 = (Support.All.pipe_right (p_guard base_prob) Support.Prims.fst)
in (Microsoft_FStar_Absyn_Util.mk_conj _70_14325 impl))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in (match ((problem.relation = EQ)) with
| true -> begin
(let ref_prob = (let _70_14327 = (mk_problem (p_scope orig) orig phi1 EQ phi2 None "refinement formula")
in (Support.All.pipe_left (fun ( _70_14326 ) -> TProb (_70_14326)) _70_14327))
in (match ((solve env (let _35_2625 = wl
in {attempting = (ref_prob)::[]; deferred = []; subst = _35_2625.subst; ctr = _35_2625.ctr; slack_vars = _35_2625.slack_vars; defer_ok = false; smt_ok = _35_2625.smt_ok; tcenv = _35_2625.tcenv}))) with
| Failed (_35_2628) -> begin
(fallback ())
end
| Success ((subst, _35_2632)) -> begin
(let guard = (let _70_14330 = (Support.All.pipe_right (p_guard base_prob) Support.Prims.fst)
in (let _70_14329 = (let _70_14328 = (Support.All.pipe_right (p_guard ref_prob) Support.Prims.fst)
in (Support.All.pipe_right _70_14328 (guard_on_element problem x1)))
in (Microsoft_FStar_Absyn_Util.mk_conj _70_14330 _70_14329)))
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
(let _70_14332 = (destruct_flex_t t1)
in (let _70_14331 = (destruct_flex_t t2)
in (flex_flex orig _70_14332 _70_14331)))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _)) when (problem.relation = EQ) -> begin
(let _70_14333 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _70_14333 t2 wl))
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
in (match ((let _70_14334 = (is_top_level_prob orig)
in (Support.All.pipe_left Support.Prims.op_Negation _70_14334))) with
| true -> begin
(let _70_14337 = (Support.All.pipe_left (fun ( _70_14335 ) -> TProb (_70_14335)) (let _35_2793 = problem
in {lhs = _35_2793.lhs; relation = new_rel; rhs = _35_2793.rhs; element = _35_2793.element; logical_guard = _35_2793.logical_guard; scope = _35_2793.scope; reason = _35_2793.reason; loc = _35_2793.loc; rank = _35_2793.rank}))
in (let _70_14336 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _70_14337 _70_14336 t2 wl)))
end
| false -> begin
(let _35_2797 = (base_and_refinement env wl t2)
in (match (_35_2797) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _70_14340 = (Support.All.pipe_left (fun ( _70_14338 ) -> TProb (_70_14338)) (let _35_2799 = problem
in {lhs = _35_2799.lhs; relation = new_rel; rhs = _35_2799.rhs; element = _35_2799.element; logical_guard = _35_2799.logical_guard; scope = _35_2799.scope; reason = _35_2799.reason; loc = _35_2799.loc; rank = _35_2799.rank}))
in (let _70_14339 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _70_14340 _70_14339 t_base wl)))
end
| Some ((y, phi)) -> begin
(let y' = (let _35_2805 = y
in {Microsoft_FStar_Absyn_Syntax.v = _35_2805.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t1; Microsoft_FStar_Absyn_Syntax.p = _35_2805.Microsoft_FStar_Absyn_Syntax.p})
in (let impl = (guard_on_element problem y' phi)
in (let base_prob = (let _70_14342 = (mk_problem problem.scope orig t1 new_rel y.Microsoft_FStar_Absyn_Syntax.sort problem.element "flex-rigid: base type")
in (Support.All.pipe_left (fun ( _70_14341 ) -> TProb (_70_14341)) _70_14342))
in (let guard = (let _70_14343 = (Support.All.pipe_right (p_guard base_prob) Support.Prims.fst)
in (Microsoft_FStar_Absyn_Util.mk_conj _70_14343 impl))
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
(let _35_2840 = (base_and_refinement env wl t1)
in (match (_35_2840) with
| (t_base, _35_2839) -> begin
(solve_t env (let _35_2841 = problem
in {lhs = t_base; relation = EQ; rhs = _35_2841.rhs; element = _35_2841.element; logical_guard = _35_2841.logical_guard; scope = _35_2841.scope; reason = _35_2841.reason; loc = _35_2841.loc; rank = _35_2841.rank}) wl)
end))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine (_35_2844), _35_2847) -> begin
(let t2 = (let _70_14344 = (base_and_refinement env wl t2)
in (Support.All.pipe_left force_refinement _70_14344))
in (solve_t env (let _35_2850 = problem
in {lhs = _35_2850.lhs; relation = _35_2850.relation; rhs = t2; element = _35_2850.element; logical_guard = _35_2850.logical_guard; scope = _35_2850.scope; reason = _35_2850.reason; loc = _35_2850.loc; rank = _35_2850.rank}) wl))
end
| (_35_2853, Microsoft_FStar_Absyn_Syntax.Typ_refine (_35_2855)) -> begin
(let t1 = (let _70_14345 = (base_and_refinement env wl t1)
in (Support.All.pipe_left force_refinement _70_14345))
in (solve_t env (let _35_2859 = problem
in {lhs = t1; relation = _35_2859.relation; rhs = _35_2859.rhs; element = _35_2859.element; logical_guard = _35_2859.logical_guard; scope = _35_2859.scope; reason = _35_2859.reason; loc = _35_2859.loc; rank = _35_2859.rank}) wl))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_const (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_btvar (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_const (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_app (_))) -> begin
(let _35_2899 = (head_matches_delta env wl t1 t2)
in (match (_35_2899) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch, _35_2902) -> begin
(let head1 = (let _70_14346 = (Microsoft_FStar_Absyn_Util.head_and_args t1)
in (Support.All.pipe_right _70_14346 Support.Prims.fst))
in (let head2 = (let _70_14347 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (Support.All.pipe_right _70_14347 Support.Prims.fst))
in (let may_equate = (fun ( head ) -> (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (_35_2909) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) -> begin
(Microsoft_FStar_Tc_Env.is_projector env tc.Microsoft_FStar_Absyn_Syntax.v)
end
| _35_2914 -> begin
false
end))
in (match ((((may_equate head1) || (may_equate head2)) && wl.smt_ok)) with
| true -> begin
(let _70_14353 = (let _70_14352 = (let _70_14351 = (Microsoft_FStar_Absyn_Util.mk_eq_typ t1 t2)
in (Support.All.pipe_left (fun ( _70_14350 ) -> Some (_70_14350)) _70_14351))
in (solve_prob orig _70_14352 [] wl))
in (solve env _70_14353))
end
| false -> begin
(giveup env "head mismatch" orig)
end))))
end
| (_35_2916, Some ((t1, t2))) -> begin
(solve_t env (let _35_2922 = problem
in {lhs = t1; relation = _35_2922.relation; rhs = t2; element = _35_2922.element; logical_guard = _35_2922.logical_guard; scope = _35_2922.scope; reason = _35_2922.reason; loc = _35_2922.loc; rank = _35_2922.rank}) wl)
end
| (_35_2925, None) -> begin
(let _35_2928 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14355 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _70_14354 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (Support.Microsoft.FStar.Util.fprint2 "Head matches: %s and %s\n" _70_14355 _70_14354)))
end
| false -> begin
()
end)
in (let _35_2932 = (Microsoft_FStar_Absyn_Util.head_and_args t1)
in (match (_35_2932) with
| (head, args) -> begin
(let _35_2935 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (match (_35_2935) with
| (head', args') -> begin
(let nargs = (Support.List.length args)
in (match ((nargs <> (Support.List.length args'))) with
| true -> begin
(let _70_14360 = (let _70_14359 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (let _70_14358 = (Microsoft_FStar_Absyn_Print.args_to_string args)
in (let _70_14357 = (Microsoft_FStar_Absyn_Print.typ_to_string head')
in (let _70_14356 = (Microsoft_FStar_Absyn_Print.args_to_string args')
in (Support.Microsoft.FStar.Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _70_14359 _70_14358 _70_14357 _70_14356)))))
in (giveup env _70_14360 orig))
end
| false -> begin
(match (((nargs = 0) || (eq_args args args'))) with
| true -> begin
(let _70_14361 = (solve_prob orig None [] wl)
in (solve env _70_14361))
end
| false -> begin
(let _35_2939 = (base_and_refinement env wl t1)
in (match (_35_2939) with
| (base1, refinement1) -> begin
(let _35_2942 = (base_and_refinement env wl t2)
in (match (_35_2942) with
| (base2, refinement2) -> begin
(match ((refinement1, refinement2)) with
| (None, None) -> begin
(let _35_2946 = (match (((head_matches head head) <> FullMatch)) with
| true -> begin
(let _70_14364 = (let _70_14363 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (let _70_14362 = (Microsoft_FStar_Absyn_Print.typ_to_string head')
in (Support.Microsoft.FStar.Util.format2 "Assertion failed: expected full match of %s and %s\n" _70_14363 _70_14362)))
in (Support.All.failwith _70_14364))
end
| false -> begin
()
end)
in (let subprobs = (Support.List.map2 (fun ( a ) ( a' ) -> (match (((Support.Prims.fst a), (Support.Prims.fst a'))) with
| (Support.Microsoft.FStar.Util.Inl (t), Support.Microsoft.FStar.Util.Inl (t')) -> begin
(let _70_14368 = (mk_problem (p_scope orig) orig t EQ t' None "type index")
in (Support.All.pipe_left (fun ( _70_14367 ) -> TProb (_70_14367)) _70_14368))
end
| (Support.Microsoft.FStar.Util.Inr (v), Support.Microsoft.FStar.Util.Inr (v')) -> begin
(let _70_14370 = (mk_problem (p_scope orig) orig v EQ v' None "term index")
in (Support.All.pipe_left (fun ( _70_14369 ) -> EProb (_70_14369)) _70_14370))
end
| _35_2961 -> begin
(Support.All.failwith "Impossible")
end)) args args')
in (let formula = (let _70_14372 = (Support.List.map (fun ( p ) -> (Support.Prims.fst (p_guard p))) subprobs)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _70_14372))
in (let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl))))))
end
| _35_2967 -> begin
(let lhs = (force_refinement (base1, refinement1))
in (let rhs = (force_refinement (base2, refinement2))
in (solve_t env (let _35_2970 = problem
in {lhs = lhs; relation = _35_2970.relation; rhs = rhs; element = _35_2970.element; logical_guard = _35_2970.logical_guard; scope = _35_2970.scope; reason = _35_2970.reason; loc = _35_2970.loc; rank = _35_2970.rank}) wl)))
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
(Support.All.failwith "Impossible")
end
| _35_3009 -> begin
(giveup env "head mismatch" orig)
end))))
end)))
end))))))))
and solve_c = (fun ( env ) ( problem ) ( wl ) -> (let c1 = problem.lhs
in (let c2 = problem.rhs
in (let orig = CProb (problem)
in (let sub_prob = (fun ( t1 ) ( rel ) ( t2 ) ( reason ) -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (let solve_eq = (fun ( c1_comp ) ( c2_comp ) -> (let _35_3026 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("EQ")))) with
| true -> begin
(Support.Microsoft.FStar.Util.print_string "solve_c is using an equality constraint\n")
end
| false -> begin
()
end)
in (let sub_probs = (Support.List.map2 (fun ( arg1 ) ( arg2 ) -> (match (((Support.Prims.fst arg1), (Support.Prims.fst arg2))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
(let _70_14387 = (sub_prob t1 EQ t2 "effect arg")
in (Support.All.pipe_left (fun ( _70_14386 ) -> TProb (_70_14386)) _70_14387))
end
| (Support.Microsoft.FStar.Util.Inr (e1), Support.Microsoft.FStar.Util.Inr (e2)) -> begin
(let _70_14389 = (sub_prob e1 EQ e2 "effect arg")
in (Support.All.pipe_left (fun ( _70_14388 ) -> EProb (_70_14388)) _70_14389))
end
| _35_3041 -> begin
(Support.All.failwith "impossible")
end)) c1_comp.Microsoft_FStar_Absyn_Syntax.effect_args c2_comp.Microsoft_FStar_Absyn_Syntax.effect_args)
in (let guard = (let _70_14391 = (Support.List.map (fun ( p ) -> (Support.All.pipe_right (p_guard p) Support.Prims.fst)) sub_probs)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _70_14391))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in (match ((Support.Microsoft.FStar.Util.physical_equality c1 c2)) with
| true -> begin
(let _70_14392 = (solve_prob orig None [] wl)
in (solve env _70_14392))
end
| false -> begin
(let _35_3046 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14394 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _70_14393 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (Support.Microsoft.FStar.Util.fprint3 "solve_c %s %s %s\n" _70_14394 (rel_to_string problem.relation) _70_14393)))
end
| false -> begin
()
end)
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let _35_3051 = (c1, c2)
in (match (_35_3051) with
| (c1_0, c2_0) -> begin
(match ((c1.Microsoft_FStar_Absyn_Syntax.n, c2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Total (t1), Microsoft_FStar_Absyn_Syntax.Total (t2)) -> begin
(solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl)
end
| (Microsoft_FStar_Absyn_Syntax.Total (_35_3058), Microsoft_FStar_Absyn_Syntax.Comp (_35_3061)) -> begin
(let _70_14396 = (let _35_3064 = problem
in (let _70_14395 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c1))
in {lhs = _70_14395; relation = _35_3064.relation; rhs = _35_3064.rhs; element = _35_3064.element; logical_guard = _35_3064.logical_guard; scope = _35_3064.scope; reason = _35_3064.reason; loc = _35_3064.loc; rank = _35_3064.rank}))
in (solve_c env _70_14396 wl))
end
| (Microsoft_FStar_Absyn_Syntax.Comp (_35_3067), Microsoft_FStar_Absyn_Syntax.Total (_35_3070)) -> begin
(let _70_14398 = (let _35_3073 = problem
in (let _70_14397 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c2))
in {lhs = _35_3073.lhs; relation = _35_3073.relation; rhs = _70_14397; element = _35_3073.element; logical_guard = _35_3073.logical_guard; scope = _35_3073.scope; reason = _35_3073.reason; loc = _35_3073.loc; rank = _35_3073.rank}))
in (solve_c env _70_14398 wl))
end
| (Microsoft_FStar_Absyn_Syntax.Comp (_35_3076), Microsoft_FStar_Absyn_Syntax.Comp (_35_3079)) -> begin
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
in (let _35_3086 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(Support.Microsoft.FStar.Util.fprint2 "solve_c for %s and %s\n" c1.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str c2.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str)
end
| false -> begin
()
end)
in (match ((Microsoft_FStar_Tc_Env.monad_leq env c1.Microsoft_FStar_Absyn_Syntax.effect_name c2.Microsoft_FStar_Absyn_Syntax.effect_name)) with
| None -> begin
(let _70_14401 = (let _70_14400 = (Microsoft_FStar_Absyn_Print.sli c1.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _70_14399 = (Microsoft_FStar_Absyn_Print.sli c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (Support.Microsoft.FStar.Util.format2 "incompatible monad ordering: %s </: %s" _70_14400 _70_14399)))
in (giveup env _70_14401 orig))
end
| Some (edge) -> begin
(match ((problem.relation = EQ)) with
| true -> begin
(let _35_3106 = (match (c1.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp1), _35_3099)::(Support.Microsoft.FStar.Util.Inl (wlp1), _35_3094)::[] -> begin
(wp1, wlp1)
end
| _35_3103 -> begin
(let _70_14404 = (let _70_14403 = (let _70_14402 = (Microsoft_FStar_Absyn_Syntax.range_of_lid c1.Microsoft_FStar_Absyn_Syntax.effect_name)
in (Support.Microsoft.FStar.Range.string_of_range _70_14402))
in (Support.Microsoft.FStar.Util.format1 "Unexpected number of indices on a normalized effect (%s)" _70_14403))
in (Support.All.failwith _70_14404))
end)
in (match (_35_3106) with
| (wp, wlp) -> begin
(let c1 = (let _70_14410 = (let _70_14409 = (let _70_14405 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wp)
in (Microsoft_FStar_Absyn_Syntax.targ _70_14405))
in (let _70_14408 = (let _70_14407 = (let _70_14406 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wlp)
in (Microsoft_FStar_Absyn_Syntax.targ _70_14406))
in (_70_14407)::[])
in (_70_14409)::_70_14408))
in {Microsoft_FStar_Absyn_Syntax.effect_name = c2.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = c1.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _70_14410; Microsoft_FStar_Absyn_Syntax.flags = c1.Microsoft_FStar_Absyn_Syntax.flags})
in (solve_eq c1 c2))
end))
end
| false -> begin
(let is_null_wp_2 = (Support.All.pipe_right c2.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _35_33 ) -> (match (_35_33) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.MLEFFECT) | (Microsoft_FStar_Absyn_Syntax.SOMETRIVIAL) -> begin
true
end
| _35_3113 -> begin
false
end))))
in (let _35_3136 = (match ((c1.Microsoft_FStar_Absyn_Syntax.effect_args, c2.Microsoft_FStar_Absyn_Syntax.effect_args)) with
| ((Support.Microsoft.FStar.Util.Inl (wp1), _35_3120)::_35_3116, (Support.Microsoft.FStar.Util.Inl (wp2), _35_3128)::_35_3124) -> begin
(wp1, wp2)
end
| _35_3133 -> begin
(let _70_14414 = (let _70_14413 = (Microsoft_FStar_Absyn_Print.sli c1.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _70_14412 = (Microsoft_FStar_Absyn_Print.sli c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (Support.Microsoft.FStar.Util.format2 "Got effects %s and %s, expected normalized effects" _70_14413 _70_14412)))
in (Support.All.failwith _70_14414))
end)
in (match (_35_3136) with
| (wpc1, wpc2) -> begin
(match ((Support.Microsoft.FStar.Util.physical_equality wpc1 wpc2)) with
| true -> begin
(solve_t env (problem_using_guard orig c1.Microsoft_FStar_Absyn_Syntax.result_typ problem.relation c2.Microsoft_FStar_Absyn_Syntax.result_typ None "result type") wl)
end
| false -> begin
(let c2_decl = (Microsoft_FStar_Tc_Env.get_effect_decl env c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let g = (match (is_null_wp_2) with
| true -> begin
(let _35_3138 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(Support.Microsoft.FStar.Util.print_string "Using trivial wp ... \n")
end
| false -> begin
()
end)
in (let _70_14420 = (let _70_14419 = (let _70_14418 = (Microsoft_FStar_Absyn_Syntax.targ c1.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _70_14417 = (let _70_14416 = (let _70_14415 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wpc1)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_14415))
in (_70_14416)::[])
in (_70_14418)::_70_14417))
in (c2_decl.Microsoft_FStar_Absyn_Syntax.trivial, _70_14419))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_14420 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)))
end
| false -> begin
(let wp2_imp_wp1 = (let _70_14432 = (let _70_14431 = (let _70_14430 = (Microsoft_FStar_Absyn_Syntax.targ c2.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _70_14429 = (let _70_14428 = (Microsoft_FStar_Absyn_Syntax.targ wpc2)
in (let _70_14427 = (let _70_14426 = (let _70_14422 = (let _70_14421 = (Microsoft_FStar_Absyn_Const.kbin Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.imp_lid _70_14421))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_14422))
in (let _70_14425 = (let _70_14424 = (let _70_14423 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wpc1)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_14423))
in (_70_14424)::[])
in (_70_14426)::_70_14425))
in (_70_14428)::_70_14427))
in (_70_14430)::_70_14429))
in (c2_decl.Microsoft_FStar_Absyn_Syntax.wp_binop, _70_14431))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_14432 None r))
in (let _70_14437 = (let _70_14436 = (let _70_14435 = (Microsoft_FStar_Absyn_Syntax.targ c2.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _70_14434 = (let _70_14433 = (Microsoft_FStar_Absyn_Syntax.targ wp2_imp_wp1)
in (_70_14433)::[])
in (_70_14435)::_70_14434))
in (c2_decl.Microsoft_FStar_Absyn_Syntax.wp_as_type, _70_14436))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_14437 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)))
end)
in (let base_prob = (let _70_14439 = (sub_prob c1.Microsoft_FStar_Absyn_Syntax.result_typ problem.relation c2.Microsoft_FStar_Absyn_Syntax.result_typ "result type")
in (Support.All.pipe_left (fun ( _70_14438 ) -> TProb (_70_14438)) _70_14439))
in (let wl = (let _70_14443 = (let _70_14442 = (let _70_14441 = (Support.All.pipe_right (p_guard base_prob) Support.Prims.fst)
in (Microsoft_FStar_Absyn_Util.mk_conj _70_14441 g))
in (Support.All.pipe_left (fun ( _70_14440 ) -> Some (_70_14440)) _70_14442))
in (solve_prob orig _70_14443 [] wl))
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
| _35_3150 -> begin
(Support.All.failwith "Impossible")
end))
and solve_e' = (fun ( env ) ( problem ) ( wl ) -> (let problem = (let _35_3154 = problem
in {lhs = _35_3154.lhs; relation = EQ; rhs = _35_3154.rhs; element = _35_3154.element; logical_guard = _35_3154.logical_guard; scope = _35_3154.scope; reason = _35_3154.reason; loc = _35_3154.loc; rank = _35_3154.rank})
in (let e1 = problem.lhs
in (let e2 = problem.rhs
in (let orig = EProb (problem)
in (let sub_prob = (fun ( lhs ) ( rhs ) ( reason ) -> (mk_problem (p_scope orig) orig lhs EQ rhs None reason))
in (let _35_3166 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14453 = (prob_to_string env orig)
in (Support.Microsoft.FStar.Util.fprint1 "Attempting:\n%s\n" _70_14453))
end
| false -> begin
()
end)
in (let flex_rigid = (fun ( _35_3173 ) ( e2 ) -> (match (_35_3173) with
| (e1, u1, t1, args1) -> begin
(let maybe_vars1 = (pat_vars env [] args1)
in (let sub_problems = (fun ( xs ) ( args2 ) -> (let _35_3200 = (let _70_14469 = (Support.All.pipe_right args2 (Support.List.map (fun ( _35_34 ) -> (match (_35_34) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (let _35_3187 = (new_tvar t.Microsoft_FStar_Absyn_Syntax.pos xs kk)
in (match (_35_3187) with
| (gi_xi, gi) -> begin
(let gi_pi = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (gi, args1) (Some (kk)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_14465 = (let _70_14464 = (sub_prob gi_pi t "type index")
in (Support.All.pipe_left (fun ( _70_14463 ) -> TProb (_70_14463)) _70_14464))
in ((Support.Microsoft.FStar.Util.Inl (gi_xi), imp), _70_14465)))
end)))
end
| (Support.Microsoft.FStar.Util.Inr (v), imp) -> begin
(let tt = (Microsoft_FStar_Tc_Recheck.recompute_typ v)
in (let _35_3196 = (new_evar v.Microsoft_FStar_Absyn_Syntax.pos xs tt)
in (match (_35_3196) with
| (gi_xi, gi) -> begin
(let gi_pi = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (gi, args1) (Some (tt)) v.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_14468 = (let _70_14467 = (sub_prob gi_pi v "expression index")
in (Support.All.pipe_left (fun ( _70_14466 ) -> EProb (_70_14466)) _70_14467))
in ((Support.Microsoft.FStar.Util.Inr (gi_xi), imp), _70_14468)))
end)))
end))))
in (Support.All.pipe_right _70_14469 Support.List.unzip))
in (match (_35_3200) with
| (gi_xi, gi_pi) -> begin
(let formula = (let _70_14471 = (Support.List.map (fun ( p ) -> (Support.All.pipe_right (p_guard p) Support.Prims.fst)) gi_pi)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _70_14471))
in (gi_xi, gi_pi, formula))
end)))
in (let project_e = (fun ( head2 ) ( args2 ) -> (let giveup = (fun ( reason ) -> (let _70_14478 = (Support.Microsoft.FStar.Util.format1 "flex-rigid: refusing to project expressions (%s)" reason)
in (giveup env _70_14478 orig)))
in (match ((let _70_14479 = (Microsoft_FStar_Absyn_Util.compress_exp head2)
in _70_14479.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (y) -> begin
(let _35_3217 = (match ((Microsoft_FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some ((xs, c)) -> begin
(xs, (Microsoft_FStar_Absyn_Util.comp_result c))
end)
in (match (_35_3217) with
| (all_xs, tres) -> begin
(match (((Support.List.length all_xs) <> (Support.List.length args1))) with
| true -> begin
(let _70_14482 = (let _70_14481 = (Microsoft_FStar_Absyn_Print.binders_to_string ", " all_xs)
in (let _70_14480 = (Microsoft_FStar_Absyn_Print.args_to_string args2)
in (Support.Microsoft.FStar.Util.format2 "unequal arity:\n\texpetced binders %s\n\tgot args {%s}" _70_14481 _70_14480)))
in (giveup _70_14482))
end
| false -> begin
(let rec aux = (fun ( xs ) ( args ) -> (match ((xs, args)) with
| ([], []) -> begin
(giveup "variable to project not found")
end
| (([], _)) | ((_, [])) -> begin
(Support.All.failwith "impossible")
end
| ((Support.Microsoft.FStar.Util.Inl (_35_3234), _35_3237)::xs, (Support.Microsoft.FStar.Util.Inl (_35_3242), _35_3245)::args) -> begin
(aux xs args)
end
| ((Support.Microsoft.FStar.Util.Inr (xi), _35_3253)::xs, (Support.Microsoft.FStar.Util.Inr (arg), _35_3260)::args) -> begin
(match ((let _70_14487 = (Microsoft_FStar_Absyn_Util.compress_exp arg)
in _70_14487.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (z) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvar_eq y z)) with
| true -> begin
(let _35_3269 = (sub_problems all_xs args2)
in (match (_35_3269) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (let _70_14491 = (let _70_14490 = (let _70_14489 = (let _70_14488 = (Microsoft_FStar_Absyn_Util.bvar_to_exp xi)
in (_70_14488, gi_xi))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _70_14489 None e1.Microsoft_FStar_Absyn_Syntax.pos))
in (all_xs, _70_14490))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _70_14491 None e1.Microsoft_FStar_Absyn_Syntax.pos))
in (let _35_3271 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14495 = (Microsoft_FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _70_14494 = (Microsoft_FStar_Absyn_Print.exp_to_string sol)
in (let _70_14493 = (let _70_14492 = (Support.All.pipe_right gi_pi (Support.List.map (prob_to_string env)))
in (Support.All.pipe_right _70_14492 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.fprint3 "Projected: %s -> %s\nSubprobs=\n%s\n" _70_14495 _70_14494 _70_14493))))
end
| false -> begin
()
end)
in (let _70_14497 = (let _70_14496 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _70_14496))
in (solve env _70_14497))))
end))
end
| false -> begin
(aux xs args)
end)
end
| _35_3274 -> begin
(aux xs args)
end)
end
| (x::xs, arg::args) -> begin
(let _70_14500 = (let _70_14499 = (Microsoft_FStar_Absyn_Print.binder_to_string x)
in (let _70_14498 = (Microsoft_FStar_Absyn_Print.arg_to_string arg)
in (Support.Microsoft.FStar.Util.format2 "type incorrect term---impossible: expected %s; got %s\n" _70_14499 _70_14498)))
in (giveup _70_14500))
end))
in (aux (Support.List.rev all_xs) (Support.List.rev args1)))
end)
end))
end
| _35_3283 -> begin
(giveup "rigid head term is not a variable")
end)))
in (let imitate_or_project_e = (fun ( _35_3285 ) -> (match (()) with
| () -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid: not a pattern" orig wl))
end
| false -> begin
(let _35_3286 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14504 = (Microsoft_FStar_Absyn_Print.exp_to_string e1)
in (let _70_14503 = (Microsoft_FStar_Absyn_Print.exp_to_string e2)
in (Support.Microsoft.FStar.Util.fprint2 "Imitating expressions: %s =?= %s\n" _70_14504 _70_14503)))
end
| false -> begin
()
end)
in (let _35_3290 = (Microsoft_FStar_Absyn_Util.head_and_args_e e2)
in (match (_35_3290) with
| (head2, args2) -> begin
(let fvhead = (Microsoft_FStar_Absyn_Util.freevars_exp head2)
in (let _35_3295 = (occurs_check_e env (u1, t1) head2)
in (match (_35_3295) with
| (occurs_ok, _35_3294) -> begin
(match (((Microsoft_FStar_Absyn_Util.fvs_included fvhead Microsoft_FStar_Absyn_Syntax.no_fvs) && occurs_ok)) with
| true -> begin
(let _35_3303 = (match ((Microsoft_FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some ((xs, c)) -> begin
(xs, (Microsoft_FStar_Absyn_Util.comp_result c))
end)
in (match (_35_3303) with
| (xs, tres) -> begin
(let _35_3307 = (sub_problems xs args2)
in (match (_35_3307) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (let body = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.Microsoft_FStar_Absyn_Syntax.pos)
in (match (xs) with
| [] -> begin
body
end
| _35_3311 -> begin
(let _70_14506 = (let _70_14505 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.Microsoft_FStar_Absyn_Syntax.pos)
in (xs, _70_14505))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _70_14506 None e1.Microsoft_FStar_Absyn_Syntax.pos))
end))
in (let _35_3313 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14510 = (Microsoft_FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _70_14509 = (Microsoft_FStar_Absyn_Print.exp_to_string sol)
in (let _70_14508 = (let _70_14507 = (Support.All.pipe_right gi_pi (Support.List.map (prob_to_string env)))
in (Support.All.pipe_right _70_14507 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.fprint3 "Imitated: %s -> %s\nSubprobs=\n%s\n" _70_14510 _70_14509 _70_14508))))
end
| false -> begin
()
end)
in (let _70_14512 = (let _70_14511 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _70_14511))
in (solve env _70_14512))))
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
in (let _35_3325 = (occurs_check_e env (u1, t1) e2)
in (match (_35_3325) with
| (occurs_ok, _35_3324) -> begin
(match ((((Support.Microsoft.FStar.Util.set_is_subset_of fvs2.Microsoft_FStar_Absyn_Syntax.ftvs fvs1.Microsoft_FStar_Absyn_Syntax.ftvs) && (Support.Microsoft.FStar.Util.set_is_subset_of fvs2.Microsoft_FStar_Absyn_Syntax.fxvs fvs1.Microsoft_FStar_Absyn_Syntax.fxvs)) && occurs_ok)) with
| true -> begin
(let sol = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs' (xs, e2) None e1.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_14513 = (solve_prob orig None ((UE (((u1, t1), sol)))::[]) wl)
in (solve env _70_14513)))
end
| false -> begin
(imitate_or_project_e ())
end)
end))))
end)))))
end))
in (let flex_flex = (fun ( _35_3332 ) ( _35_3337 ) -> (match ((_35_3332, _35_3337)) with
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
in (let _35_3358 = (let _70_14518 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_evar _70_14518 zs tt))
in (match (_35_3358) with
| (u, _35_3357) -> begin
(let sub1 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (xs, u) (Some (t1)) e1.Microsoft_FStar_Absyn_Syntax.pos)
in (let sub2 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (ys, u) (Some (t2)) e1.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_14519 = (solve_prob orig None ((UE (((u1, t1), sub1)))::(UE (((u2, t2), sub2)))::[]) wl)
in (solve env _70_14519))))
end))))
end)
end)))
end))
in (let smt_fallback = (fun ( e1 ) ( e2 ) -> (match (wl.smt_ok) with
| true -> begin
(let _35_3364 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14524 = (prob_to_string env orig)
in (Support.Microsoft.FStar.Util.fprint1 "Using SMT to solve:\n%s\n" _70_14524))
end
| false -> begin
()
end)
in (let _35_3369 = (let _70_14526 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_14525 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _70_14526 _70_14525 Microsoft_FStar_Absyn_Syntax.ktype)))
in (match (_35_3369) with
| (t, _35_3368) -> begin
(let _70_14530 = (let _70_14529 = (let _70_14528 = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (Support.All.pipe_left (fun ( _70_14527 ) -> Some (_70_14527)) _70_14528))
in (solve_prob orig _70_14529 [] wl))
in (solve env _70_14530))
end)))
end
| false -> begin
(giveup env "no SMT solution permitted" orig)
end))
in (match ((e1.Microsoft_FStar_Absyn_Syntax.n, e2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e1, _35_3372, _35_3374)), _35_3378) -> begin
(solve_e env (let _35_3380 = problem
in {lhs = e1; relation = _35_3380.relation; rhs = _35_3380.rhs; element = _35_3380.element; logical_guard = _35_3380.logical_guard; scope = _35_3380.scope; reason = _35_3380.reason; loc = _35_3380.loc; rank = _35_3380.rank}) wl)
end
| (_35_3383, Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e2, _35_3386, _35_3388))) -> begin
(solve_e env (let _35_3392 = problem
in {lhs = _35_3392.lhs; relation = _35_3392.relation; rhs = e2; element = _35_3392.element; logical_guard = _35_3392.logical_guard; scope = _35_3392.scope; reason = _35_3392.reason; loc = _35_3392.loc; rank = _35_3392.rank}) wl)
end
| ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) | ((Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) | ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) | ((Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) -> begin
(let _70_14532 = (destruct_flex_e e1)
in (let _70_14531 = (destruct_flex_e e2)
in (flex_flex _70_14532 _70_14531)))
end
| ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _)) -> begin
(let _70_14533 = (destruct_flex_e e1)
in (flex_rigid _70_14533 e2))
end
| ((_, Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) -> begin
(let _70_14534 = (destruct_flex_e e2)
in (flex_rigid _70_14534 e1))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (x1), Microsoft_FStar_Absyn_Syntax.Exp_bvar (x1')) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvd_eq x1.Microsoft_FStar_Absyn_Syntax.v x1'.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(let _70_14535 = (solve_prob orig None [] wl)
in (solve env _70_14535))
end
| false -> begin
(let _70_14541 = (let _70_14540 = (let _70_14539 = (let _70_14538 = (Microsoft_FStar_Tc_Recheck.recompute_typ e1)
in (let _70_14537 = (Microsoft_FStar_Tc_Recheck.recompute_typ e2)
in (Microsoft_FStar_Absyn_Util.mk_eq _70_14538 _70_14537 e1 e2)))
in (Support.All.pipe_left (fun ( _70_14536 ) -> Some (_70_14536)) _70_14539))
in (solve_prob orig _70_14540 [] wl))
in (solve env _70_14541))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv1, _35_3531)), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv1', _35_3536))) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv1.Microsoft_FStar_Absyn_Syntax.v fv1'.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(let _70_14542 = (solve_prob orig None [] wl)
in (solve env _70_14542))
end
| false -> begin
(giveup env "free-variables unequal" orig)
end)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_constant (s1), Microsoft_FStar_Absyn_Syntax.Exp_constant (s1')) -> begin
(let const_eq = (fun ( s1 ) ( s2 ) -> (match ((s1, s2)) with
| (Microsoft_FStar_Absyn_Syntax.Const_bytearray ((b1, _35_3550)), Microsoft_FStar_Absyn_Syntax.Const_bytearray ((b2, _35_3555))) -> begin
(b1 = b2)
end
| (Microsoft_FStar_Absyn_Syntax.Const_string ((b1, _35_3561)), Microsoft_FStar_Absyn_Syntax.Const_string ((b2, _35_3566))) -> begin
(b1 = b2)
end
| _35_3571 -> begin
(s1 = s2)
end))
in (match ((const_eq s1 s1')) with
| true -> begin
(let _70_14547 = (solve_prob orig None [] wl)
in (solve env _70_14547))
end
| false -> begin
(giveup env "constants unequal" orig)
end))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_35_3581); Microsoft_FStar_Absyn_Syntax.tk = _35_3579; Microsoft_FStar_Absyn_Syntax.pos = _35_3577; Microsoft_FStar_Absyn_Syntax.fvs = _35_3575; Microsoft_FStar_Absyn_Syntax.uvs = _35_3573}, _35_3585)), _35_3589) -> begin
(let _70_14549 = (let _35_3591 = problem
in (let _70_14548 = (whnf_e env e1)
in {lhs = _70_14548; relation = _35_3591.relation; rhs = _35_3591.rhs; element = _35_3591.element; logical_guard = _35_3591.logical_guard; scope = _35_3591.scope; reason = _35_3591.reason; loc = _35_3591.loc; rank = _35_3591.rank}))
in (solve_e env _70_14549 wl))
end
| (_35_3594, Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_35_3604); Microsoft_FStar_Absyn_Syntax.tk = _35_3602; Microsoft_FStar_Absyn_Syntax.pos = _35_3600; Microsoft_FStar_Absyn_Syntax.fvs = _35_3598; Microsoft_FStar_Absyn_Syntax.uvs = _35_3596}, _35_3608))) -> begin
(let _70_14551 = (let _35_3612 = problem
in (let _70_14550 = (whnf_e env e2)
in {lhs = _35_3612.lhs; relation = _35_3612.relation; rhs = _70_14550; element = _35_3612.element; logical_guard = _35_3612.logical_guard; scope = _35_3612.scope; reason = _35_3612.reason; loc = _35_3612.loc; rank = _35_3612.rank}))
in (solve_e env _70_14551 wl))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((head1, args1)), Microsoft_FStar_Absyn_Syntax.Exp_app ((head2, args2))) -> begin
(let orig_wl = wl
in (let rec solve_args = (fun ( sub_probs ) ( wl ) ( args1 ) ( args2 ) -> (match ((args1, args2)) with
| ([], []) -> begin
(let guard = (let _70_14561 = (let _70_14560 = (Support.List.map p_guard sub_probs)
in (Support.All.pipe_right _70_14560 (Support.List.map Support.Prims.fst)))
in (Microsoft_FStar_Absyn_Util.mk_conj_l _70_14561))
in (let g = (simplify_formula env guard)
in (let g = (Microsoft_FStar_Absyn_Util.compress_typ g)
in (match (g.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
(let _70_14562 = (solve_prob orig None wl.subst (let _35_3637 = orig_wl
in {attempting = _35_3637.attempting; deferred = _35_3637.deferred; subst = []; ctr = _35_3637.ctr; slack_vars = _35_3637.slack_vars; defer_ok = _35_3637.defer_ok; smt_ok = _35_3637.smt_ok; tcenv = _35_3637.tcenv}))
in (solve env _70_14562))
end
| _35_3640 -> begin
(let _35_3644 = (let _70_14564 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_14563 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _70_14564 _70_14563 Microsoft_FStar_Absyn_Syntax.ktype)))
in (match (_35_3644) with
| (t, _35_3643) -> begin
(let guard = (let _70_14565 = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (Microsoft_FStar_Absyn_Util.mk_disj g _70_14565))
in (let _70_14566 = (solve_prob orig (Some (guard)) wl.subst (let _35_3646 = orig_wl
in {attempting = _35_3646.attempting; deferred = _35_3646.deferred; subst = []; ctr = _35_3646.ctr; slack_vars = _35_3646.slack_vars; defer_ok = _35_3646.defer_ok; smt_ok = _35_3646.smt_ok; tcenv = _35_3646.tcenv}))
in (solve env _70_14566)))
end))
end))))
end
| (arg1::rest1, arg2::rest2) -> begin
(let prob = (match (((Support.Prims.fst arg1), (Support.Prims.fst arg2))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
(let _70_14568 = (mk_problem (p_scope orig) orig t1 EQ t2 None "expression type arg")
in (Support.All.pipe_left (fun ( _70_14567 ) -> TProb (_70_14567)) _70_14568))
end
| (Support.Microsoft.FStar.Util.Inr (e1), Support.Microsoft.FStar.Util.Inr (e2)) -> begin
(let _70_14570 = (mk_problem (p_scope orig) orig e1 EQ e2 None "expression arg")
in (Support.All.pipe_left (fun ( _70_14569 ) -> EProb (_70_14569)) _70_14570))
end
| _35_3666 -> begin
(Support.All.failwith "Impossible: ill-typed expression")
end)
in (match ((solve env (let _35_3668 = wl
in {attempting = (prob)::[]; deferred = []; subst = _35_3668.subst; ctr = _35_3668.ctr; slack_vars = _35_3668.slack_vars; defer_ok = false; smt_ok = false; tcenv = _35_3668.tcenv}))) with
| Failed (_35_3671) -> begin
(smt_fallback e1 e2)
end
| Success ((subst, _35_3675)) -> begin
(solve_args ((prob)::sub_probs) (let _35_3678 = wl
in {attempting = _35_3678.attempting; deferred = _35_3678.deferred; subst = subst; ctr = _35_3678.ctr; slack_vars = _35_3678.slack_vars; defer_ok = _35_3678.defer_ok; smt_ok = _35_3678.smt_ok; tcenv = _35_3678.tcenv}) rest1 rest2)
end))
end
| _35_3681 -> begin
(Support.All.failwith "Impossible: lengths defer")
end))
in (let rec match_head_and_args = (fun ( head1 ) ( head2 ) -> (match ((let _70_14578 = (let _70_14575 = (Microsoft_FStar_Absyn_Util.compress_exp head1)
in _70_14575.Microsoft_FStar_Absyn_Syntax.n)
in (let _70_14577 = (let _70_14576 = (Microsoft_FStar_Absyn_Util.compress_exp head2)
in _70_14576.Microsoft_FStar_Absyn_Syntax.n)
in (_70_14578, _70_14577)))) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (x), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) when ((Microsoft_FStar_Absyn_Util.bvar_eq x y) && ((Support.List.length args1) = (Support.List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _35_3692)), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((g, _35_3697))) when (((Microsoft_FStar_Absyn_Util.fvar_eq f g) && (not ((Microsoft_FStar_Absyn_Util.is_interpreted f.Microsoft_FStar_Absyn_Syntax.v)))) && ((Support.List.length args1) = (Support.List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _35_3703, _35_3705)), _35_3709) -> begin
(match_head_and_args e head2)
end
| (_35_3712, Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _35_3715, _35_3717))) -> begin
(match_head_and_args head1 e)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_abs (_35_3722), _35_3725) -> begin
(let _70_14580 = (let _35_3727 = problem
in (let _70_14579 = (whnf_e env e1)
in {lhs = _70_14579; relation = _35_3727.relation; rhs = _35_3727.rhs; element = _35_3727.element; logical_guard = _35_3727.logical_guard; scope = _35_3727.scope; reason = _35_3727.reason; loc = _35_3727.loc; rank = _35_3727.rank}))
in (solve_e env _70_14580 wl))
end
| (_35_3730, Microsoft_FStar_Absyn_Syntax.Exp_abs (_35_3732)) -> begin
(let _70_14582 = (let _35_3735 = problem
in (let _70_14581 = (whnf_e env e2)
in {lhs = _35_3735.lhs; relation = _35_3735.relation; rhs = _70_14581; element = _35_3735.element; logical_guard = _35_3735.logical_guard; scope = _35_3735.scope; reason = _35_3735.reason; loc = _35_3735.loc; rank = _35_3735.rank}))
in (solve_e env _70_14582 wl))
end
| _35_3738 -> begin
(smt_fallback e1 e2)
end))
in (match_head_and_args head1 head2))))
end
| _35_3740 -> begin
(let _35_3744 = (let _70_14584 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_14583 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _70_14584 _70_14583 Microsoft_FStar_Absyn_Syntax.ktype)))
in (match (_35_3744) with
| (t, _35_3743) -> begin
(let guard = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (let _35_3746 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14585 = (Microsoft_FStar_Absyn_Print.typ_to_string guard)
in (Support.Microsoft.FStar.Util.fprint1 "Emitting guard %s\n" _70_14585))
end
| false -> begin
()
end)
in (let _70_14589 = (let _70_14588 = (let _70_14587 = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (Support.All.pipe_left (fun ( _70_14586 ) -> Some (_70_14586)) _70_14587))
in (solve_prob orig _70_14588 [] wl))
in (solve env _70_14589))))
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

let is_Mkguard_t = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkguard_t"))

let guard_to_string = (fun ( env ) ( g ) -> (let form = (match (g.guard_f) with
| Trivial -> begin
"trivial"
end
| NonTrivial (f) -> begin
(match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(Microsoft_FStar_Tc_Normalize.formula_norm_to_string env f)
end
| false -> begin
"non-trivial"
end)
end)
in (let carry = (let _70_14613 = (Support.List.map (fun ( _35_3763 ) -> (match (_35_3763) with
| (_35_3761, x) -> begin
(prob_to_string env x)
end)) g.deferred.carry)
in (Support.All.pipe_right _70_14613 (Support.String.concat ",\n")))
in (Support.Microsoft.FStar.Util.format2 "\n\t{guard_f=%s;\n\t deferred={\n%s};}\n" form carry))))

let guard_of_guard_formula = (fun ( g ) -> {guard_f = g; deferred = {carry = []; slack = []}; implicits = []})

let guard_f = (fun ( g ) -> g.guard_f)

let is_trivial = (fun ( g ) -> (match (g) with
| {guard_f = Trivial; deferred = {carry = []; slack = []}; implicits = _35_3769} -> begin
true
end
| _35_3776 -> begin
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
| _35_3792 -> begin
(Support.All.failwith "impossible")
end)
in (let _70_14630 = (let _35_3794 = g
in (let _70_14629 = (let _70_14628 = (let _70_14627 = (let _70_14626 = (let _70_14625 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_70_14625)::[])
in (_70_14626, f))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_14627 None f.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.All.pipe_left (fun ( _70_14624 ) -> NonTrivial (_70_14624)) _70_14628))
in {guard_f = _70_14629; deferred = _35_3794.deferred; implicits = _35_3794.implicits}))
in Some (_70_14630)))
end))

let apply_guard = (fun ( g ) ( e ) -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _35_3801 = g
in (let _70_14642 = (let _70_14641 = (let _70_14640 = (let _70_14639 = (let _70_14638 = (let _70_14637 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_70_14637)::[])
in (f, _70_14638))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_14639))
in (Support.All.pipe_left (Microsoft_FStar_Absyn_Syntax.syn f.Microsoft_FStar_Absyn_Syntax.pos (Some (Microsoft_FStar_Absyn_Syntax.ktype))) _70_14640))
in NonTrivial (_70_14641))
in {guard_f = _70_14642; deferred = _35_3801.deferred; implicits = _35_3801.implicits}))
end))

let trivial = (fun ( t ) -> (match (t) with
| Trivial -> begin
()
end
| NonTrivial (_35_3806) -> begin
(Support.All.failwith "impossible")
end))

let conj_guard_f = (fun ( g1 ) ( g2 ) -> (match ((g1, g2)) with
| ((Trivial, g)) | ((g, Trivial)) -> begin
g
end
| (NonTrivial (f1), NonTrivial (f2)) -> begin
(let _70_14649 = (Microsoft_FStar_Absyn_Util.mk_conj f1 f2)
in NonTrivial (_70_14649))
end))

let check_trivial = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _35_3824 -> begin
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

let binop_guard = (fun ( f ) ( g1 ) ( g2 ) -> (let _70_14672 = (f g1.guard_f g2.guard_f)
in {guard_f = _70_14672; deferred = {carry = (Support.List.append g1.deferred.carry g2.deferred.carry); slack = (Support.List.append g1.deferred.slack g2.deferred.slack)}; implicits = (Support.List.append g1.implicits g2.implicits)}))

let conj_guard = (fun ( g1 ) ( g2 ) -> (binop_guard conj_guard_f g1 g2))

let imp_guard = (fun ( g1 ) ( g2 ) -> (binop_guard imp_guard_f g1 g2))

let close_guard = (fun ( binders ) ( g ) -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _35_3851 = g
in (let _70_14687 = (let _70_14686 = (Microsoft_FStar_Absyn_Util.close_forall binders f)
in (Support.All.pipe_right _70_14686 (fun ( _70_14685 ) -> NonTrivial (_70_14685))))
in {guard_f = _70_14687; deferred = _35_3851.deferred; implicits = _35_3851.implicits}))
end))

let mk_guard = (fun ( g ) ( ps ) ( slack ) ( locs ) -> {guard_f = g; deferred = {carry = ps; slack = slack}; implicits = []})

let new_t_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) -> (let reason = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _70_14699 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env lhs)
in (let _70_14698 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env rhs)
in (Support.Microsoft.FStar.Util.format3 "Top-level:\n%s\n\t%s\n%s" _70_14699 (rel_to_string rel) _70_14698)))
end
| false -> begin
"TOP"
end)
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

let new_t_prob = (fun ( env ) ( t1 ) ( rel ) ( t2 ) -> (let x = (let _70_14708 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p _70_14708 t1))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))))
in (let p = (let _70_14712 = (let _70_14710 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.All.pipe_left (fun ( _70_14709 ) -> Some (_70_14709)) _70_14710))
in (let _70_14711 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_t_problem env t1 rel t2 _70_14712 _70_14711)))
in (TProb (p), x)))))

let new_k_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) -> (let reason = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _70_14720 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env lhs)
in (let _70_14719 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env rhs)
in (Support.Microsoft.FStar.Util.format3 "Top-level:\n%s\n\t%s\n%s" _70_14720 (rel_to_string rel) _70_14719)))
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
(let _35_3885 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _70_14725 = (Microsoft_FStar_Absyn_Print.typ_to_string f)
in (Support.Microsoft.FStar.Util.fprint1 "Simplifying guard %s\n" _70_14725))
end
| false -> begin
()
end)
in (let f = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env f)
in (let f = (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _35_3891 -> begin
NonTrivial (f)
end)
in (let _35_3893 = g
in {guard_f = f; deferred = _35_3893.deferred; implicits = _35_3893.implicits}))))
end))

let solve_and_commit = (fun ( env ) ( probs ) ( err ) -> (let probs = (match ((Support.ST.read Microsoft_FStar_Options.eager_inference)) with
| true -> begin
(let _35_3898 = probs
in {attempting = _35_3898.attempting; deferred = _35_3898.deferred; subst = _35_3898.subst; ctr = _35_3898.ctr; slack_vars = _35_3898.slack_vars; defer_ok = false; smt_ok = _35_3898.smt_ok; tcenv = _35_3898.tcenv})
end
| false -> begin
probs
end)
in (let sol = (solve env probs)
in (match (sol) with
| Success ((s, deferred)) -> begin
(let _35_3906 = (commit env s)
in Some (deferred))
end
| Failed ((d, s)) -> begin
(let _35_3912 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _70_14737 = (explain env d s)
in (Support.All.pipe_left Support.Microsoft.FStar.Util.print_string _70_14737))
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
(let _70_14749 = (let _70_14748 = (let _70_14747 = (let _70_14746 = (Support.All.pipe_right (p_guard prob) Support.Prims.fst)
in (Support.All.pipe_right _70_14746 (fun ( _70_14745 ) -> NonTrivial (_70_14745))))
in {guard_f = _70_14747; deferred = d; implicits = []})
in (simplify_guard env _70_14748))
in (Support.All.pipe_left (fun ( _70_14744 ) -> Some (_70_14744)) _70_14749))
end))

let try_keq = (fun ( env ) ( k1 ) ( k2 ) -> (let _35_3923 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14757 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (let _70_14756 = (Microsoft_FStar_Absyn_Print.kind_to_string k2)
in (Support.Microsoft.FStar.Util.fprint2 "try_keq of %s and %s\n" _70_14757 _70_14756)))
end
| false -> begin
()
end)
in (let prob = (let _70_14762 = (let _70_14761 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env k1)
in (let _70_14760 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env k2)
in (let _70_14759 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_k_problem env _70_14761 EQ _70_14760 None _70_14759))))
in (Support.All.pipe_left (fun ( _70_14758 ) -> KProb (_70_14758)) _70_14762))
in (let _70_14764 = (solve_and_commit env (singleton env prob) (fun ( _35_3926 ) -> None))
in (Support.All.pipe_left (with_guard env prob) _70_14764)))))

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
(let _70_14775 = (let _70_14774 = (let _70_14773 = (Microsoft_FStar_Tc_Errors.incompatible_kinds env k2 k1)
in (_70_14773, r))
in Microsoft_FStar_Absyn_Syntax.Error (_70_14774))
in (raise (_70_14775)))
end
| Some (t) -> begin
(let _70_14778 = (let _70_14777 = (let _70_14776 = (Microsoft_FStar_Tc_Errors.expected_typ_of_kind env k2 t k1)
in (_70_14776, r))
in Microsoft_FStar_Absyn_Syntax.Error (_70_14777))
in (raise (_70_14778)))
end))
end
| Some (g) -> begin
g
end))

let subkind = (fun ( env ) ( k1 ) ( k2 ) -> (let _35_3945 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14788 = (let _70_14785 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _70_14785))
in (let _70_14787 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (let _70_14786 = (Microsoft_FStar_Absyn_Print.kind_to_string k2)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) subkind of %s and %s\n" _70_14788 _70_14787 _70_14786))))
end
| false -> begin
()
end)
in (let prob = (let _70_14793 = (let _70_14792 = (whnf_k env k1)
in (let _70_14791 = (whnf_k env k2)
in (let _70_14790 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_k_problem env _70_14792 SUB _70_14791 None _70_14790))))
in (Support.All.pipe_left (fun ( _70_14789 ) -> KProb (_70_14789)) _70_14793))
in (let res = (let _70_14800 = (let _70_14799 = (solve_and_commit env (singleton env prob) (fun ( _35_3948 ) -> (let _70_14798 = (let _70_14797 = (let _70_14796 = (Microsoft_FStar_Tc_Errors.incompatible_kinds env k1 k2)
in (let _70_14795 = (Microsoft_FStar_Tc_Env.get_range env)
in (_70_14796, _70_14795)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_14797))
in (raise (_70_14798)))))
in (Support.All.pipe_left (with_guard env prob) _70_14799))
in (Support.Microsoft.FStar.Util.must _70_14800))
in res))))

let try_teq = (fun ( env ) ( t1 ) ( t2 ) -> (let _35_3954 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14808 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _70_14807 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (Support.Microsoft.FStar.Util.fprint2 "try_teq of %s and %s\n" _70_14808 _70_14807)))
end
| false -> begin
()
end)
in (let prob = (let _70_14811 = (let _70_14810 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_t_problem env t1 EQ t2 None _70_14810))
in (Support.All.pipe_left (fun ( _70_14809 ) -> TProb (_70_14809)) _70_14811))
in (let g = (let _70_14813 = (solve_and_commit env (singleton env prob) (fun ( _35_3957 ) -> None))
in (Support.All.pipe_left (with_guard env prob) _70_14813))
in g))))

let teq = (fun ( env ) ( t1 ) ( t2 ) -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _70_14823 = (let _70_14822 = (let _70_14821 = (Microsoft_FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _70_14820 = (Microsoft_FStar_Tc_Env.get_range env)
in (_70_14821, _70_14820)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_14822))
in (raise (_70_14823)))
end
| Some (g) -> begin
(let _35_3966 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14826 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _70_14825 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (let _70_14824 = (guard_to_string env g)
in (Support.Microsoft.FStar.Util.fprint3 "teq of %s and %s succeeded with guard %s\n" _70_14826 _70_14825 _70_14824))))
end
| false -> begin
()
end)
in g)
end))

let try_subtype = (fun ( env ) ( t1 ) ( t2 ) -> (let _35_3971 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14834 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _70_14833 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.fprint2 "try_subtype of %s and %s\n" _70_14834 _70_14833)))
end
| false -> begin
()
end)
in (let _35_3975 = (new_t_prob env t1 SUB t2)
in (match (_35_3975) with
| (prob, x) -> begin
(let g = (let _70_14836 = (solve_and_commit env (singleton env prob) (fun ( _35_3976 ) -> None))
in (Support.All.pipe_left (with_guard env prob) _70_14836))
in (let _35_3979 = (match (((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) && (Support.Microsoft.FStar.Util.is_some g))) with
| true -> begin
(let _70_14840 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _70_14839 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _70_14838 = (let _70_14837 = (Support.Microsoft.FStar.Util.must g)
in (guard_to_string env _70_14837))
in (Support.Microsoft.FStar.Util.fprint3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _70_14840 _70_14839 _70_14838))))
end
| false -> begin
()
end)
in (abstract_guard x g)))
end))))

let subtype_fail = (fun ( env ) ( t1 ) ( t2 ) -> (let _70_14847 = (let _70_14846 = (let _70_14845 = (Microsoft_FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _70_14844 = (Microsoft_FStar_Tc_Env.get_range env)
in (_70_14845, _70_14844)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_14846))
in (raise (_70_14847))))

let subtype = (fun ( env ) ( t1 ) ( t2 ) -> (match ((try_subtype env t1 t2)) with
| Some (f) -> begin
f
end
| None -> begin
(subtype_fail env t1 t2)
end))

let sub_comp = (fun ( env ) ( c1 ) ( c2 ) -> (let _35_3993 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14861 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _70_14860 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (Support.Microsoft.FStar.Util.fprint2 "sub_comp of %s and %s\n" _70_14861 _70_14860)))
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
in (let prob = (let _70_14864 = (let _70_14863 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_problem env c1 rel c2 None _70_14863 "sub_comp"))
in (Support.All.pipe_left (fun ( _70_14862 ) -> CProb (_70_14862)) _70_14864))
in (let _70_14866 = (solve_and_commit env (singleton env prob) (fun ( _35_3997 ) -> None))
in (Support.All.pipe_left (with_guard env prob) _70_14866))))))

let solve_deferred_constraints = (fun ( env ) ( g ) -> (let fail = (fun ( _35_4004 ) -> (match (_35_4004) with
| (d, s) -> begin
(let msg = (explain env d s)
in (raise (Microsoft_FStar_Absyn_Syntax.Error ((msg, (p_loc d))))))
end))
in (let _35_4009 = (match (((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) && ((Support.List.length g.deferred.carry) <> 0))) with
| true -> begin
(let _70_14879 = (let _70_14878 = (Support.All.pipe_right g.deferred.carry (Support.List.map (fun ( _35_4008 ) -> (match (_35_4008) with
| (msg, x) -> begin
(let _70_14877 = (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range (p_loc x))
in (let _70_14876 = (prob_to_string env x)
in (let _70_14875 = (let _70_14874 = (Support.All.pipe_right (p_guard x) Support.Prims.fst)
in (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env _70_14874))
in (Support.Microsoft.FStar.Util.format4 "(At %s) %s\n%s\nguard is %s\n" _70_14877 msg _70_14876 _70_14875))))
end))))
in (Support.All.pipe_right _70_14878 (Support.String.concat "\n")))
in (Support.All.pipe_left (Support.Microsoft.FStar.Util.fprint1 "Trying to solve carried problems: begin\n%s\nend\n") _70_14879))
end
| false -> begin
()
end)
in (let gopt = (let _70_14880 = (wl_of_guard env g.deferred)
in (solve_and_commit env _70_14880 fail))
in (match (gopt) with
| Some ({carry = _35_4014; slack = slack}) -> begin
(let _35_4017 = (fix_slack_vars slack)
in (let _35_4019 = g
in {guard_f = _35_4019.guard_f; deferred = no_deferred; implicits = _35_4019.implicits}))
end
| _35_4022 -> begin
(Support.All.failwith "impossible")
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
(let _35_4033 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14887 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_14886 = (let _70_14885 = (Microsoft_FStar_Absyn_Print.formula_to_string vc)
in (Support.Microsoft.FStar.Util.format1 "Checking VC=\n%s\n" _70_14885))
in (Microsoft_FStar_Tc_Errors.diag _70_14887 _70_14886)))
end
| false -> begin
()
end)
in (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.solve env vc))
end))
end)
end)))




