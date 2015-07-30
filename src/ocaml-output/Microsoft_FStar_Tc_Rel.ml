
let new_kvar = (fun ( r ) ( binders ) -> (let wf = (fun ( k ) ( _33_39 ) -> (match (()) with
| () -> begin
true
end))
in (let u = (Support.Microsoft.FStar.Unionfind.fresh Microsoft_FStar_Absyn_Syntax.Uvar)
in (let _65_12880 = (let _65_12879 = (let _65_12878 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (u, _65_12878))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar _65_12879 r))
in (_65_12880, u)))))

let new_tvar = (fun ( r ) ( binders ) ( k ) -> (let wf = (fun ( t ) ( tk ) -> true)
in (let binders = (Support.Prims.pipe_right binders (Support.List.filter (fun ( x ) -> (let _65_12892 = (Microsoft_FStar_Absyn_Syntax.is_null_binder x)
in (Support.Prims.pipe_right _65_12892 Support.Prims.op_Negation)))))
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
in (let _65_12893 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (uv, args) None r)
in (_65_12893, uv)))))
end)))))

let new_evar = (fun ( r ) ( binders ) ( t ) -> (let wf = (fun ( e ) ( t ) -> true)
in (let binders = (Support.Prims.pipe_right binders (Support.List.filter (fun ( x ) -> (let _65_12905 = (Microsoft_FStar_Absyn_Syntax.is_null_binder x)
in (Support.Prims.pipe_right _65_12905 Support.Prims.op_Negation)))))
in (let uv = (Support.Microsoft.FStar.Unionfind.fresh Microsoft_FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (Microsoft_FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t) None r)
in (uv, uv))
end
| _ -> begin
(let args = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (let t' = (let _65_12907 = (let _65_12906 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (binders, _65_12906))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _65_12907 None r))
in (let uv = (Microsoft_FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t') None r)
in (match (args) with
| [] -> begin
(uv, uv)
end
| _ -> begin
(let _65_12908 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (uv, args) None r)
in (_65_12908, uv))
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

let is_Mkproblem = (fun ( _ ) -> (failwith ("Not yet implemented")))

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

let is_Mkworklist = (fun ( _ ) -> (failwith ("Not yet implemented")))

type deferred =
{carry : (string * prob) list; slack : (bool * Microsoft_FStar_Absyn_Syntax.typ) list}

let is_Mkdeferred = (fun ( _ ) -> (failwith ("Not yet implemented")))

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
(let _65_13047 = (Microsoft_FStar_Absyn_Print.kind_to_string p.lhs)
in (let _65_13046 = (Microsoft_FStar_Absyn_Print.kind_to_string p.rhs)
in (Support.Microsoft.FStar.Util.format3 "\t%s\n\t\t%s\n\t%s" _65_13047 (rel_to_string p.relation) _65_13046)))
end
| TProb (p) -> begin
(let _65_13060 = (let _65_13059 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env p.lhs)
in (let _65_13058 = (let _65_13057 = (Microsoft_FStar_Absyn_Print.tag_of_typ p.lhs)
in (let _65_13056 = (let _65_13055 = (let _65_13054 = (Support.Prims.pipe_right p.reason Support.List.hd)
in (let _65_13053 = (let _65_13052 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env p.rhs)
in (let _65_13051 = (let _65_13050 = (Microsoft_FStar_Absyn_Print.tag_of_typ p.rhs)
in (let _65_13049 = (let _65_13048 = (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env (Support.Prims.fst p.logical_guard))
in (_65_13048)::[])
in (_65_13050)::_65_13049))
in (_65_13052)::_65_13051))
in (_65_13054)::_65_13053))
in ((rel_to_string p.relation))::_65_13055)
in (_65_13057)::_65_13056))
in (_65_13059)::_65_13058))
in (Support.Microsoft.FStar.Util.format "\t%s (%s) \n\t\t%s(%s)\n\t%s (%s) (guard %s)" _65_13060))
end
| EProb (p) -> begin
(let _65_13062 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env p.lhs)
in (let _65_13061 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env p.rhs)
in (Support.Microsoft.FStar.Util.format3 "\t%s \n\t\t%s\n\t%s" _65_13062 (rel_to_string p.relation) _65_13061)))
end
| CProb (p) -> begin
(let _65_13064 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env p.lhs)
in (let _65_13063 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env p.rhs)
in (Support.Microsoft.FStar.Util.format3 "\t%s \n\t\t%s\n\t%s" _65_13064 (rel_to_string p.relation) _65_13063)))
end))

let uvi_to_string = (fun ( env ) ( uvi ) -> (let str = (fun ( u ) -> (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _65_13070 = (Support.Microsoft.FStar.Unionfind.uvar_id u)
in (Support.Prims.pipe_right _65_13070 Support.Microsoft.FStar.Util.string_of_int))
end))
in (match (uvi) with
| UK ((u, _)) -> begin
(let _65_13071 = (str u)
in (Support.Prims.pipe_right _65_13071 (Support.Microsoft.FStar.Util.format1 "UK %s")))
end
| UT (((u, _), t)) -> begin
(let _65_13074 = (str u)
in (Support.Prims.pipe_right _65_13074 (fun ( x ) -> (let _65_13073 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.format2 "UT %s %s" x _65_13073)))))
end
| UE (((u, _), _)) -> begin
(let _65_13075 = (str u)
in (Support.Prims.pipe_right _65_13075 (Support.Microsoft.FStar.Util.format1 "UE %s")))
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
(Support.Prims.pipe_right (maybe_invert p) (fun ( _65_13082 ) -> KProb (_65_13082)))
end
| TProb (p) -> begin
(Support.Prims.pipe_right (maybe_invert p) (fun ( _65_13083 ) -> TProb (_65_13083)))
end
| EProb (p) -> begin
(Support.Prims.pipe_right (maybe_invert p) (fun ( _65_13084 ) -> EProb (_65_13084)))
end
| CProb (p) -> begin
(Support.Prims.pipe_right (maybe_invert p) (fun ( _65_13085 ) -> CProb (_65_13085)))
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
(Support.Prims.pipe_left (fun ( _65_13104 ) -> KProb (_65_13104)) (invert p))
end
| TProb (p) -> begin
(Support.Prims.pipe_left (fun ( _65_13105 ) -> TProb (_65_13105)) (invert p))
end
| EProb (p) -> begin
(Support.Prims.pipe_left (fun ( _65_13106 ) -> EProb (_65_13106)) (invert p))
end
| CProb (p) -> begin
(Support.Prims.pipe_left (fun ( _65_13107 ) -> CProb (_65_13107)) (invert p))
end))

let is_top_level_prob = (fun ( p ) -> ((Support.Prims.pipe_right (p_reason p) Support.List.length) = 1))

let mk_problem = (fun ( scope ) ( orig ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( reason ) -> (let _65_13117 = (new_tvar (p_loc orig) scope Microsoft_FStar_Absyn_Syntax.ktype)
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _65_13117; scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None}))

let new_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) ( reason ) -> (let _65_13127 = (let _65_13126 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _65_13125 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _65_13126 _65_13125 Microsoft_FStar_Absyn_Syntax.ktype)))
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _65_13127; scope = []; reason = (reason)::[]; loc = loc; rank = None}))

let problem_using_guard = (fun ( orig ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( reason ) -> {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = (p_guard orig); scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None})

let guard_on_element = (fun ( problem ) ( x ) ( phi ) -> (match (problem.element) with
| None -> begin
(let _65_13138 = (let _65_13137 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_65_13137)::[])
in (Microsoft_FStar_Absyn_Util.close_forall _65_13138 phi))
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
(let _33_292 = (match ((let _65_13149 = (Microsoft_FStar_Absyn_Util.compress_typ uv)
in _65_13149.Microsoft_FStar_Absyn_Syntax.n)) with
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
(let _65_13151 = (let _65_13150 = (Support.List.map (uvi_to_string wl.tcenv) uvis)
in (Support.Prims.pipe_right _65_13150 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.fprint1 "Extending solution: %s\n" _65_13151))
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

let explain = (fun ( env ) ( d ) ( s ) -> (let _65_13172 = (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range (p_loc d))
in (let _65_13171 = (prob_to_string env d)
in (let _65_13170 = (Support.Prims.pipe_right (p_reason d) (Support.String.concat "\n\t>"))
in (Support.Microsoft.FStar.Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _65_13172 _65_13171 _65_13170 s)))))

let empty_worklist = (fun ( env ) -> {attempting = []; deferred = []; subst = []; ctr = 0; slack_vars = []; defer_ok = true; smt_ok = true; tcenv = env})

let singleton = (fun ( env ) ( prob ) -> (let _33_315 = (empty_worklist env)
in {attempting = (prob)::[]; deferred = _33_315.deferred; subst = _33_315.subst; ctr = _33_315.ctr; slack_vars = _33_315.slack_vars; defer_ok = _33_315.defer_ok; smt_ok = _33_315.smt_ok; tcenv = _33_315.tcenv}))

let wl_of_guard = (fun ( env ) ( g ) -> (let _33_319 = (empty_worklist env)
in (let _65_13183 = (Support.List.map Support.Prims.snd g.carry)
in {attempting = _65_13183; deferred = _33_319.deferred; subst = _33_319.subst; ctr = _33_319.ctr; slack_vars = g.slack; defer_ok = false; smt_ok = _33_319.smt_ok; tcenv = _33_319.tcenv})))

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
(let _65_13208 = (prob_to_string env prob)
in (Support.Microsoft.FStar.Util.fprint2 "Failed %s:\n%s\n" reason _65_13208))
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
(let _65_13239 = (let _65_13238 = (norm_targ env t)
in (Support.Prims.pipe_left (fun ( _65_13237 ) -> Support.Microsoft.FStar.Util.Inl (_65_13237)) _65_13238))
in (_65_13239, (Support.Prims.snd a)))
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
(let _65_13242 = (let _65_13241 = (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env v)
in (Support.Prims.pipe_left (fun ( _65_13240 ) -> Support.Microsoft.FStar.Util.Inr (_65_13240)) _65_13241))
in (_65_13242, (Support.Prims.snd a)))
end))

let whnf = (fun ( env ) ( t ) -> (let _65_13247 = (Microsoft_FStar_Tc_Normalize.whnf env t)
in (Support.Prims.pipe_right _65_13247 Microsoft_FStar_Absyn_Util.compress_typ)))

let sn = (fun ( env ) ( t ) -> (let _65_13252 = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::[]) env t)
in (Support.Prims.pipe_right _65_13252 Microsoft_FStar_Absyn_Util.compress_typ)))

let sn_binders = (fun ( env ) ( binders ) -> (Support.Prims.pipe_right binders (Support.List.map (fun ( _33_17 ) -> (match (_33_17) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _65_13258 = (let _65_13257 = (let _33_417 = a
in (let _65_13256 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env a.Microsoft_FStar_Absyn_Syntax.sort)
in {Microsoft_FStar_Absyn_Syntax.v = _33_417.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _65_13256; Microsoft_FStar_Absyn_Syntax.p = _33_417.Microsoft_FStar_Absyn_Syntax.p}))
in Support.Microsoft.FStar.Util.Inl (_65_13257))
in (_65_13258, imp))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _65_13261 = (let _65_13260 = (let _33_423 = x
in (let _65_13259 = (norm_targ env x.Microsoft_FStar_Absyn_Syntax.sort)
in {Microsoft_FStar_Absyn_Syntax.v = _33_423.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _65_13259; Microsoft_FStar_Absyn_Syntax.p = _33_423.Microsoft_FStar_Absyn_Syntax.p}))
in Support.Microsoft.FStar.Util.Inr (_65_13260))
in (_65_13261, imp))
end)))))

let whnf_k = (fun ( env ) ( k ) -> (let _65_13266 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.WHNF)::[]) env k)
in (Support.Prims.pipe_right _65_13266 Microsoft_FStar_Absyn_Util.compress_kind)))

let whnf_e = (fun ( env ) ( e ) -> (let _65_13271 = (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.WHNF)::[]) env e)
in (Support.Prims.pipe_right _65_13271 Microsoft_FStar_Absyn_Util.compress_exp)))

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
(let k = (let _65_13278 = (Microsoft_FStar_Absyn_Util.subst_of_list formals actuals)
in (Microsoft_FStar_Absyn_Util.subst_kind _65_13278 body))
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

let rec compress = (fun ( env ) ( wl ) ( t ) -> (let t = (let _65_13285 = (Microsoft_FStar_Absyn_Util.unmeta_typ t)
in (whnf env _65_13285))
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

let normalize_refinement = (fun ( env ) ( wl ) ( t0 ) -> (let _65_13298 = (compress env wl t0)
in (Microsoft_FStar_Tc_Normalize.normalize_refinement env _65_13298)))

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
(let _65_13311 = (let _65_13310 = (Microsoft_FStar_Absyn_Print.typ_to_string tt)
in (let _65_13309 = (Microsoft_FStar_Absyn_Print.tag_of_typ tt)
in (Support.Microsoft.FStar.Util.format2 "impossible: Got %s ... %s\n" _65_13310 _65_13309)))
in (failwith (_65_13311)))
end)
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (_)) -> begin
(match (norm) with
| true -> begin
(t1, None)
end
| false -> begin
(let _33_554 = (let _65_13312 = (normalize_refinement env wl t1)
in (aux true _65_13312))
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
(let _65_13315 = (let _65_13314 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _65_13313 = (Microsoft_FStar_Absyn_Print.tag_of_typ t1)
in (Support.Microsoft.FStar.Util.format2 "impossible (outer): Got %s ... %s\n" _65_13314 _65_13313)))
in (failwith (_65_13315)))
end))
in (let _65_13316 = (compress env wl t1)
in (aux false _65_13316))))

let unrefine = (fun ( env ) ( t ) -> (let _65_13321 = (base_and_refinement env (empty_worklist env) t)
in (Support.Prims.pipe_right _65_13321 Support.Prims.fst)))

let trivial_refinement = (fun ( t ) -> (let _65_13323 = (Microsoft_FStar_Absyn_Util.gen_bvar_p t.Microsoft_FStar_Absyn_Syntax.pos t)
in (_65_13323, Microsoft_FStar_Absyn_Util.t_true)))

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
in (let _65_13343 = (Support.Prims.pipe_right uvs.Microsoft_FStar_Absyn_Syntax.uvars_t Support.Microsoft.FStar.Util.set_elements)
in (Support.Prims.pipe_right _65_13343 (Support.Microsoft.FStar.Util.for_some (fun ( _33_615 ) -> (match (_33_615) with
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
(let _65_13356 = (let _65_13355 = (Microsoft_FStar_Absyn_Print.uvar_t_to_string uk)
in (let _65_13354 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (let _65_13353 = (let _65_13352 = (Support.Prims.pipe_right wl.subst (Support.List.map (uvi_to_string env)))
in (Support.Prims.pipe_right _65_13352 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format3 "occurs-check failed (%s occurs in %s) (with substitution %s)" _65_13355 _65_13354 _65_13353))))
in Some (_65_13356))
end)
in (occurs_ok, msg))))

let occurs_and_freevars_check = (fun ( env ) ( wl ) ( uk ) ( fvs ) ( t ) -> (let fvs_t = (Microsoft_FStar_Absyn_Util.freevars_typ t)
in (let _33_649 = (occurs_check env wl uk t)
in (match (_33_649) with
| (occurs_ok, msg) -> begin
(let _65_13367 = (Microsoft_FStar_Absyn_Util.fvs_included fvs_t fvs)
in (occurs_ok, _65_13367, (msg, fvs, fvs_t)))
end))))

let occurs_check_e = (fun ( env ) ( ut ) ( e ) -> (let uvs = (Microsoft_FStar_Absyn_Util.uvars_in_exp e)
in (let occurs_ok = (not ((Support.Microsoft.FStar.Util.set_mem ut uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)))
in (let msg = (match (occurs_ok) with
| true -> begin
None
end
| false -> begin
(let _65_13379 = (let _65_13378 = (Microsoft_FStar_Absyn_Print.uvar_e_to_string ut)
in (let _65_13377 = (let _65_13375 = (let _65_13374 = (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (Support.Prims.pipe_right _65_13374 (Support.List.map Microsoft_FStar_Absyn_Print.uvar_e_to_string)))
in (Support.Prims.pipe_right _65_13375 (Support.String.concat ", ")))
in (let _65_13376 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env e)
in (Support.Microsoft.FStar.Util.format3 "occurs-check failed (%s occurs in {%s} uvars of %s)" _65_13378 _65_13377 _65_13376))))
in Some (_65_13379))
end)
in (occurs_ok, msg)))))

let intersect_vars = (fun ( v1 ) ( v2 ) -> (let fvs1 = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders v1)
in (let fvs2 = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders v2)
in (let _65_13386 = (let _65_13385 = (Support.Microsoft.FStar.Util.set_intersect fvs1.Microsoft_FStar_Absyn_Syntax.ftvs fvs2.Microsoft_FStar_Absyn_Syntax.ftvs)
in (let _65_13384 = (Support.Microsoft.FStar.Util.set_intersect fvs1.Microsoft_FStar_Absyn_Syntax.fxvs fvs2.Microsoft_FStar_Absyn_Syntax.fxvs)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _65_13385; Microsoft_FStar_Absyn_Syntax.fxvs = _65_13384}))
in (Microsoft_FStar_Absyn_Syntax.binders_of_freevars _65_13386)))))

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
(let _65_13402 = (Microsoft_FStar_Absyn_Print.arg_to_string hd)
in (Support.Microsoft.FStar.Util.fprint1 "Not a pattern: %s\n" _65_13402))
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

let rec head_matches = (fun ( t1 ) ( t2 ) -> (match ((let _65_13419 = (let _65_13416 = (Microsoft_FStar_Absyn_Util.unmeta_typ t1)
in _65_13416.Microsoft_FStar_Absyn_Syntax.n)
in (let _65_13418 = (let _65_13417 = (Microsoft_FStar_Absyn_Util.unmeta_typ t2)
in _65_13417.Microsoft_FStar_Absyn_Syntax.n)
in (_65_13419, _65_13418)))) with
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
(let _65_13420 = (head_matches x.Microsoft_FStar_Absyn_Syntax.sort y.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Prims.pipe_right _65_13420 head_match))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _)), _) -> begin
(let _65_13421 = (head_matches x.Microsoft_FStar_Absyn_Syntax.sort t2)
in (Support.Prims.pipe_right _65_13421 head_match))
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _))) -> begin
(let _65_13422 = (head_matches t1 x.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Prims.pipe_right _65_13422 head_match))
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
in (let _65_13476 = (mk_b_ktecs ([], []) bs)
in (rebuild, _65_13476))))))

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
in (let _65_13559 = (let _65_13558 = (mk_problem scope orig gi_ps (vary_rel rel variance) ki None "kind subterm")
in (Support.Prims.pipe_left (fun ( _65_13557 ) -> KProb (_65_13557)) _65_13558))
in (Microsoft_FStar_Absyn_Syntax.K (gi_xs), _65_13559)))
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
in (let _65_13562 = (let _65_13561 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (Support.Prims.pipe_left (fun ( _65_13560 ) -> TProb (_65_13560)) _65_13561))
in (Microsoft_FStar_Absyn_Syntax.T ((gi_xs, Some (k))), _65_13562)))
end)))
end
| (_, variance, Microsoft_FStar_Absyn_Syntax.E (ei)) -> begin
(let t = (Microsoft_FStar_Tc_Recheck.recompute_typ ei)
in (let _33_1148 = (new_evar r scope t)
in (match (_33_1148) with
| (gi_xs, gi) -> begin
(let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (gi, args) (Some (t)) r)
in (let _65_13565 = (let _65_13564 = (mk_problem scope orig gi_ps (vary_rel rel variance) ei None "expression subterm")
in (Support.Prims.pipe_left (fun ( _65_13563 ) -> EProb (_65_13563)) _65_13564))
in (Microsoft_FStar_Absyn_Syntax.E (gi_xs), _65_13565)))
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
(let _65_13574 = (let _65_13573 = (Microsoft_FStar_Absyn_Syntax.mk_Total gi_xs)
in (Support.Prims.pipe_left (fun ( _65_13572 ) -> Microsoft_FStar_Absyn_Syntax.C (_65_13572)) _65_13573))
in (_65_13574, (prob)::[]))
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
in (let _33_1222 = (let _65_13576 = (Support.List.map (sub_prob scope args) components)
in (Support.Prims.pipe_right _65_13576 Support.List.unzip))
in (match (_33_1222) with
| (ktecs, sub_probs) -> begin
(let gi_xs = (let _65_13581 = (let _65_13580 = (let _65_13577 = (Support.List.hd ktecs)
in (Support.Prims.pipe_right _65_13577 un_T))
in (let _65_13579 = (let _65_13578 = (Support.List.tl ktecs)
in (Support.Prims.pipe_right _65_13578 (Support.List.map arg_of_ktec)))
in {Microsoft_FStar_Absyn_Syntax.effect_name = c.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _65_13580; Microsoft_FStar_Absyn_Syntax.effect_args = _65_13579; Microsoft_FStar_Absyn_Syntax.flags = c.Microsoft_FStar_Absyn_Syntax.flags}))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp _65_13581))
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
(let _65_13583 = (let _65_13582 = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder b)
in (_65_13582)::args)
in (Some (b), (b)::scope, _65_13583))
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
(let _65_13586 = (let _65_13585 = (Support.Prims.pipe_right probs (Support.List.map (fun ( prob ) -> (Support.Prims.pipe_right (p_guard prob) Support.Prims.fst))))
in (f)::_65_13585)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _65_13586))
end
| Some (b) -> begin
(let _65_13590 = (let _65_13589 = (Microsoft_FStar_Absyn_Util.close_forall ((b)::[]) f)
in (let _65_13588 = (Support.Prims.pipe_right probs (Support.List.map (fun ( prob ) -> (Support.Prims.pipe_right (p_guard prob) Support.Prims.fst))))
in (_65_13589)::_65_13588))
in (Microsoft_FStar_Absyn_Util.mk_conj_l _65_13590))
end)
in ((Support.List.append probs sub_probs), (ktec)::ktecs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

type slack =
{lower : (Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.typ); upper : (Microsoft_FStar_Absyn_Syntax.typ * Microsoft_FStar_Absyn_Syntax.typ); flag : bool ref}

let is_Mkslack = (fun ( _ ) -> (failwith ("Not yet implemented")))

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
(match ((let _65_13608 = (Microsoft_FStar_Absyn_Util.compress_typ s)
in _65_13608.Microsoft_FStar_Absyn_Syntax.n)) with
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

let new_slack_var = (fun ( env ) ( slack ) -> (let xs = (let _65_13616 = (let _65_13615 = (destruct_flex_pattern env (Support.Prims.snd slack.lower))
in (Support.Prims.pipe_right _65_13615 Support.Prims.snd))
in (Support.Prims.pipe_right _65_13616 Support.Microsoft.FStar.Util.must))
in (let _65_13617 = (new_tvar (Support.Prims.fst slack.lower).Microsoft_FStar_Absyn_Syntax.pos xs Microsoft_FStar_Absyn_Syntax.ktype)
in (_65_13617, xs))))

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
in (let _65_13627 = (let _65_13626 = (let _65_13625 = (let _65_13624 = (Support.Microsoft.FStar.Util.mk_ref false)
in (low, high, _65_13624))
in Microsoft_FStar_Absyn_Syntax.Meta_slack_formula (_65_13625))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _65_13626))
in (_65_13627, wl)))))
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
(let _65_13651 = (let _65_13650 = (mk_conn lhs rest)
in (_65_13650, uvar))
in Some (_65_13651))
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
(let _65_13652 = (Microsoft_FStar_Absyn_Util.unmeta_typ phi)
in Support.Microsoft.FStar.Util.Inl (_65_13652))
end
| false -> begin
(let low = (let _65_13653 = (compress env wl phi1)
in (Support.Prims.pipe_left (destruct Microsoft_FStar_Absyn_Const.or_lid Microsoft_FStar_Absyn_Util.mk_disj) _65_13653))
in (let hi = (let _65_13654 = (compress env wl phi2)
in (Support.Prims.pipe_left (destruct Microsoft_FStar_Absyn_Const.and_lid Microsoft_FStar_Absyn_Util.mk_disj) _65_13654))
in (match ((low, hi)) with
| (None, None) -> begin
(let _33_1392 = (Support.ST.op_Colon_Equals flag true)
in (let _65_13655 = (Microsoft_FStar_Absyn_Util.unmeta_typ phi)
in Support.Microsoft.FStar.Util.Inl (_65_13655)))
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
(let _65_13685 = (let _33_1515 = p
in (let _65_13683 = (compress_k wl.tcenv wl p.lhs)
in (let _65_13682 = (compress_k wl.tcenv wl p.rhs)
in {lhs = _65_13683; relation = _33_1515.relation; rhs = _65_13682; element = _33_1515.element; logical_guard = _33_1515.logical_guard; scope = _33_1515.scope; reason = _33_1515.reason; loc = _33_1515.loc; rank = _33_1515.rank})))
in (Support.Prims.pipe_right _65_13685 (fun ( _65_13684 ) -> KProb (_65_13684))))
end
| TProb (p) -> begin
(let _65_13689 = (let _33_1519 = p
in (let _65_13687 = (compress wl.tcenv wl p.lhs)
in (let _65_13686 = (compress wl.tcenv wl p.rhs)
in {lhs = _65_13687; relation = _33_1519.relation; rhs = _65_13686; element = _33_1519.element; logical_guard = _33_1519.logical_guard; scope = _33_1519.scope; reason = _33_1519.reason; loc = _33_1519.loc; rank = _33_1519.rank})))
in (Support.Prims.pipe_right _65_13689 (fun ( _65_13688 ) -> TProb (_65_13688))))
end
| EProb (p) -> begin
(let _65_13693 = (let _33_1523 = p
in (let _65_13691 = (compress_e wl.tcenv wl p.lhs)
in (let _65_13690 = (compress_e wl.tcenv wl p.rhs)
in {lhs = _65_13691; relation = _33_1523.relation; rhs = _65_13690; element = _33_1523.element; logical_guard = _33_1523.logical_guard; scope = _33_1523.scope; reason = _33_1523.reason; loc = _33_1523.loc; rank = _33_1523.rank})))
in (Support.Prims.pipe_right _65_13693 (fun ( _65_13692 ) -> EProb (_65_13692))))
end
| CProb (_) -> begin
p
end))

let rank = (fun ( wl ) ( prob ) -> (let prob = (let _65_13698 = (compress_prob wl prob)
in (Support.Prims.pipe_right _65_13698 maybe_invert_p))
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
in (let _65_13700 = (Support.Prims.pipe_right (let _33_1558 = kp
in {lhs = _33_1558.lhs; relation = _33_1558.relation; rhs = _33_1558.rhs; element = _33_1558.element; logical_guard = _33_1558.logical_guard; scope = _33_1558.scope; reason = _33_1558.reason; loc = _33_1558.loc; rank = Some (rank)}) (fun ( _65_13699 ) -> KProb (_65_13699)))
in (rank, _65_13700)))
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
in (let _65_13702 = (let _33_1602 = tp
in (let _65_13701 = (force_refinement (b, ref_opt))
in {lhs = _33_1602.lhs; relation = _33_1602.relation; rhs = _65_13701; element = _33_1602.element; logical_guard = _33_1602.logical_guard; scope = _33_1602.scope; reason = _33_1602.reason; loc = _33_1602.loc; rank = _33_1602.rank}))
in (rank, _65_13702)))
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
(let _65_13704 = (let _33_1616 = tp
in (let _65_13703 = (force_refinement (b, ref_opt))
in {lhs = _65_13703; relation = _33_1616.relation; rhs = _33_1616.rhs; element = _33_1616.element; logical_guard = _33_1616.logical_guard; scope = _33_1616.scope; reason = _33_1616.reason; loc = _33_1616.loc; rank = _33_1616.rank}))
in (refine_flex, _65_13704))
end)
end))
end
| (_, _) -> begin
(rigid_rigid, tp)
end)
in (match (_33_1625) with
| (rank, tp) -> begin
(let _65_13706 = (Support.Prims.pipe_right (let _33_1626 = tp
in {lhs = _33_1626.lhs; relation = _33_1626.relation; rhs = _33_1626.rhs; element = _33_1626.element; logical_guard = _33_1626.logical_guard; scope = _33_1626.scope; reason = _33_1626.reason; loc = _33_1626.loc; rank = Some (rank)}) (fun ( _65_13705 ) -> TProb (_65_13705)))
in (rank, _65_13706))
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
in (let _65_13708 = (Support.Prims.pipe_right (let _33_1663 = ep
in {lhs = _33_1663.lhs; relation = _33_1663.relation; rhs = _33_1663.rhs; element = _33_1663.element; logical_guard = _33_1663.logical_guard; scope = _33_1663.scope; reason = _33_1663.reason; loc = _33_1663.loc; rank = Some (rank)}) (fun ( _65_13707 ) -> EProb (_65_13707)))
in (rank, _65_13708)))
end))
end))
end
| CProb (cp) -> begin
(let _65_13710 = (Support.Prims.pipe_right (let _33_1667 = cp
in {lhs = _33_1667.lhs; relation = _33_1667.relation; rhs = _33_1667.rhs; element = _33_1667.element; logical_guard = _33_1667.logical_guard; scope = _33_1667.scope; reason = _33_1667.reason; loc = _33_1667.loc; rank = Some (rigid_rigid)}) (fun ( _65_13709 ) -> CProb (_65_13709)))
in (rigid_rigid, _65_13710))
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
(let _65_13760 = (prob_to_string env (TProb (tp)))
in (Support.Microsoft.FStar.Util.fprint1 "Trying to solve by joining refinements:%s\n" _65_13760))
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
(let _65_13772 = (let _65_13771 = (let _65_13770 = (new_problem env t1 EQ t2 None t1.Microsoft_FStar_Absyn_Syntax.pos "joining refinements")
in (Support.Prims.pipe_left (fun ( _65_13769 ) -> TProb (_65_13769)) _65_13770))
in (_65_13771)::[])
in Some (_65_13772))
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
(let phi2 = (let _65_13779 = (let _65_13778 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (let _65_13777 = (Microsoft_FStar_Absyn_Syntax.v_binder y)
in (Microsoft_FStar_Absyn_Util.mk_subst_one_binder _65_13778 _65_13777)))
in (Microsoft_FStar_Absyn_Util.subst_typ _65_13779 phi2))
in (let _65_13783 = (let _65_13782 = (let _65_13781 = (let _65_13780 = (Microsoft_FStar_Absyn_Util.mk_conj phi1 phi2)
in (x, _65_13780))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _65_13781 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) t1.Microsoft_FStar_Absyn_Syntax.pos))
in (_65_13782, m))
in Some (_65_13783)))
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
(match ((let _65_13785 = (compress env wl u')
in _65_13785.Microsoft_FStar_Absyn_Syntax.n)) with
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
(match ((let _65_13790 = (compress env wl hd.rhs)
in (conjoin bound _65_13790))) with
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
in (match ((let _65_13792 = (let _65_13791 = (compress env wl tp.rhs)
in (_65_13791, []))
in (make_upper_bound _65_13792 upper_bounds))) with
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
(let _65_13801 = (let _65_13800 = (let _65_13799 = (Support.List.map (fun ( _33_1893 ) -> (match (_33_1893) with
| (_, x, y) -> begin
(x, y)
end)) probs.deferred)
in {carry = _65_13799; slack = probs.slack_vars})
in (probs.subst, _65_13800))
in Success (_65_13801))
end
| _ -> begin
(let _65_13804 = (let _33_1896 = probs
in (let _65_13803 = (Support.Prims.pipe_right attempt (Support.List.map (fun ( _33_1903 ) -> (match (_33_1903) with
| (_, _, y) -> begin
y
end))))
in {attempting = _65_13803; deferred = rest; subst = _33_1896.subst; ctr = _33_1896.ctr; slack_vars = _33_1896.slack_vars; defer_ok = _33_1896.defer_ok; smt_ok = _33_1896.smt_ok; tcenv = _33_1896.tcenv}))
in (solve env _65_13804))
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
(let subst = (let _65_13830 = (Microsoft_FStar_Absyn_Util.mk_subst_one_binder hd2 hd1)
in (Support.List.append _65_13830 subst))
in (let env = (let _65_13831 = (Microsoft_FStar_Tc_Env.binding_of_binder hd2)
in (Microsoft_FStar_Tc_Env.push_local_binding env _65_13831))
in (let prob = (match (((Support.Prims.fst hd1), (Support.Prims.fst hd2))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(let _65_13835 = (let _65_13834 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _65_13833 = (Support.Prims.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _65_13834 _65_13833 b.Microsoft_FStar_Absyn_Syntax.sort None "Formal type parameter")))
in (Support.Prims.pipe_left (fun ( _65_13832 ) -> KProb (_65_13832)) _65_13835))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(let _65_13839 = (let _65_13838 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _65_13837 = (Support.Prims.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _65_13838 _65_13837 y.Microsoft_FStar_Absyn_Syntax.sort None "Formal value parameter")))
in (Support.Prims.pipe_left (fun ( _65_13836 ) -> TProb (_65_13836)) _65_13839))
end
| _ -> begin
(failwith ("impos"))
end)
in (match ((aux ((hd2)::scope) env subst xs ys)) with
| Support.Microsoft.FStar.Util.Inr (msg) -> begin
Support.Microsoft.FStar.Util.Inr (msg)
end
| Support.Microsoft.FStar.Util.Inl ((sub_probs, phi)) -> begin
(let phi = (let _65_13841 = (Support.Prims.pipe_right (p_guard prob) Support.Prims.fst)
in (let _65_13840 = (Microsoft_FStar_Absyn_Util.close_forall ((hd2)::[]) phi)
in (Microsoft_FStar_Absyn_Util.mk_conj _65_13841 _65_13840)))
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
(let _65_13848 = (solve_prob orig None [] wl)
in (solve env _65_13848))
end
| false -> begin
(let k1 = problem.lhs
in (let k2 = problem.rhs
in (match ((Support.Microsoft.FStar.Util.physical_equality k1 k2)) with
| true -> begin
(let _65_13849 = (solve_prob orig None [] wl)
in (solve env _65_13849))
end
| false -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let imitate_k = (fun ( _33_2020 ) -> (match (_33_2020) with
| (rel, u, ps, xs, (h, qs)) -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let _33_2025 = (imitation_sub_probs orig env xs ps qs)
in (match (_33_2025) with
| (sub_probs, gs_xs, f) -> begin
(let im = (let _65_13865 = (let _65_13864 = (h gs_xs)
in (xs, _65_13864))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam _65_13865 r))
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
in (let _65_13874 = (solve_prob orig None ((UK ((u, k1)))::[]) wl)
in (solve env _65_13874)))
end
| false -> begin
(let _65_13879 = (let _65_13878 = (Support.Prims.pipe_right xs Microsoft_FStar_Absyn_Util.args_of_non_null_binders)
in (let _65_13877 = (decompose_kind env k)
in (rel, u, _65_13878, xs, _65_13877)))
in (imitate_k _65_13879))
end))))
end
| None -> begin
(giveup env "flex-rigid: not a pattern" (KProb (problem)))
end)))
in (match ((k1.Microsoft_FStar_Absyn_Syntax.n, k2.Microsoft_FStar_Absyn_Syntax.n)) with
| ((Microsoft_FStar_Absyn_Syntax.Kind_type, Microsoft_FStar_Absyn_Syntax.Kind_type)) | ((Microsoft_FStar_Absyn_Syntax.Kind_effect, Microsoft_FStar_Absyn_Syntax.Kind_effect)) -> begin
(let _65_13880 = (solve_prob orig None [] wl)
in (Support.Prims.pipe_left (solve env) _65_13880))
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
(let sub_prob = (fun ( scope ) ( env ) ( subst ) -> (let _65_13889 = (let _65_13888 = (Microsoft_FStar_Absyn_Util.subst_kind subst k1')
in (mk_problem scope orig _65_13888 problem.relation k2' None "Arrow-kind result"))
in (Support.Prims.pipe_left (fun ( _65_13887 ) -> KProb (_65_13887)) _65_13889)))
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
(let _65_13900 = (prob_to_string env orig)
in (Support.Microsoft.FStar.Util.fprint2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _65_13900 msg))
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
(let im = (let _65_13911 = (let _65_13910 = (h gs_xs)
in (xs, _65_13910))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' _65_13911 None r))
in (let _33_2187 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _65_13916 = (Microsoft_FStar_Absyn_Print.typ_to_string im)
in (let _65_13915 = (Microsoft_FStar_Absyn_Print.tag_of_typ im)
in (let _65_13914 = (let _65_13912 = (Support.List.map (prob_to_string env) sub_probs)
in (Support.Prims.pipe_right _65_13912 (Support.String.concat ", ")))
in (let _65_13913 = (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env formula)
in (Support.Microsoft.FStar.Util.fprint4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _65_13916 _65_13915 _65_13914 _65_13913)))))
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
in (let _65_13936 = (Microsoft_FStar_Absyn_Syntax.targ gi_xs)
in (let _65_13935 = (Microsoft_FStar_Absyn_Syntax.targ gi_ps)
in (_65_13936, _65_13935, subst))))))
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
in (let _65_13938 = (Microsoft_FStar_Absyn_Syntax.varg gi_xs)
in (let _65_13937 = (Microsoft_FStar_Absyn_Syntax.varg gi_ps)
in (_65_13938, _65_13937, subst))))))
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
in (match ((let _65_13940 = (let _65_13939 = (Support.List.nth xs i)
in (Support.Prims.pipe_left Support.Prims.fst _65_13939))
in ((Support.Prims.fst pi), _65_13940))) with
| (Support.Microsoft.FStar.Util.Inl (pi), Support.Microsoft.FStar.Util.Inl (xi)) -> begin
(match ((let _65_13941 = (matches pi)
in (Support.Prims.pipe_left Support.Prims.op_Negation _65_13941))) with
| true -> begin
None
end
| false -> begin
(let _33_2251 = (gs xi.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_33_2251) with
| (g_xs, _) -> begin
(let xi = (Microsoft_FStar_Absyn_Util.btvar_to_typ xi)
in (let proj = (let _65_13943 = (let _65_13942 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (xi, g_xs) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)
in (xs, _65_13942))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _65_13943 None r))
in (let sub = (let _65_13949 = (let _65_13948 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (proj, ps) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)
in (let _65_13947 = (let _65_13946 = (Support.List.map (fun ( _33_2259 ) -> (match (_33_2259) with
| (_, _, y) -> begin
y
end)) qs)
in (Support.Prims.pipe_left h _65_13946))
in (mk_problem (p_scope orig) orig _65_13948 (p_rel orig) _65_13947 None "projection")))
in (Support.Prims.pipe_left (fun ( _65_13944 ) -> TProb (_65_13944)) _65_13949))
in (let _33_2261 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _65_13951 = (Microsoft_FStar_Absyn_Print.typ_to_string proj)
in (let _65_13950 = (prob_to_string env sub)
in (Support.Microsoft.FStar.Util.fprint2 "Projecting %s\n\tsubprob=%s\n" _65_13951 _65_13950)))
end
| false -> begin
()
end)
in (let wl = (let _65_13953 = (let _65_13952 = (Support.Prims.pipe_left Support.Prims.fst (p_guard sub))
in Some (_65_13952))
in (solve_prob orig _65_13953 ((UT ((u, proj)))::[]) wl))
in (let _65_13955 = (solve env (attempt ((sub)::[]) wl))
in (Support.Prims.pipe_left (fun ( _65_13954 ) -> Some (_65_13954)) _65_13955)))))))
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
(let subterms = (fun ( ps ) -> (let xs = (let _65_13982 = (Microsoft_FStar_Absyn_Util.kind_formals k)
in (Support.Prims.pipe_right _65_13982 Support.Prims.fst))
in (let xs = (Microsoft_FStar_Absyn_Util.name_binders xs)
in (let _65_13987 = (decompose_typ env t2)
in ((uv, k), ps, xs, _65_13987)))))
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
(let _65_13998 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs_hd)
in (Support.Microsoft.FStar.Util.fprint1 "Free variables are %s" _65_13998))
end
| false -> begin
()
end)
in false)
end))
end)
end)))
in (let imitate_ok = (fun ( t2 ) -> (let fvs_hd = (let _65_14002 = (let _65_14001 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (Support.Prims.pipe_right _65_14001 Support.Prims.fst))
in (Support.Prims.pipe_right _65_14002 Microsoft_FStar_Absyn_Util.freevars_typ))
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
(let _65_14004 = (let _65_14003 = (Support.Option.get msg)
in (Support.String.strcat "occurs-check failed: " _65_14003))
in (giveup_or_defer orig _65_14004))
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Util.fvs_included fvs2 fvs1)) with
| true -> begin
(match (((Microsoft_FStar_Absyn_Util.is_function_typ t2) && ((p_rel orig) <> EQ))) with
| true -> begin
(let _65_14005 = (subterms args_lhs)
in (imitate_t orig env wl _65_14005))
end
| false -> begin
(let _33_2330 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _65_14008 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _65_14007 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs1)
in (let _65_14006 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs2)
in (Support.Microsoft.FStar.Util.fprint3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _65_14008 _65_14007 _65_14006))))
end
| false -> begin
()
end)
in (let sol = (match (vars) with
| [] -> begin
t2
end
| _ -> begin
(let _65_14010 = (let _65_14009 = (sn_binders env vars)
in (_65_14009, t2))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _65_14010 None t1.Microsoft_FStar_Absyn_Syntax.pos))
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
(let _65_14013 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _65_14012 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs1)
in (let _65_14011 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs2)
in (Support.Microsoft.FStar.Util.fprint3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _65_14013 _65_14012 _65_14011))))
end
| false -> begin
()
end)
in (let _65_14014 = (subterms args_lhs)
in (imitate_or_project (Support.List.length args_lhs) _65_14014 (- (1)))))
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
(match ((let _65_14015 = (Microsoft_FStar_Absyn_Util.freevars_typ t1)
in (check_head _65_14015 t2))) with
| true -> begin
(let im_ok = (imitate_ok t2)
in (let _33_2341 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _65_14016 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Support.Microsoft.FStar.Util.fprint2 "Not a pattern (%s) ... %s\n" _65_14016 (match ((im_ok < 0)) with
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
in (let _65_14017 = (subterms args_lhs)
in (imitate_or_project (Support.List.length args_lhs) _65_14017 im_ok))))
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
(let sol = (let _65_14035 = (let _65_14034 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, u1_ys) (Some (k)) t.Microsoft_FStar_Absyn_Syntax.pos)
in ((u, k), _65_14034))
in UT (_65_14035))
in (sol, (t', u, k1, ys)))
end))
end)))))
end
| hd::tl -> begin
(let new_binder = (fun ( hd ) -> (match ((Support.Prims.fst hd)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _65_14039 = (let _65_14038 = (Microsoft_FStar_Tc_Recheck.recompute_kind a)
in (Support.Prims.pipe_right _65_14038 (Microsoft_FStar_Absyn_Util.gen_bvar_p a.Microsoft_FStar_Absyn_Syntax.pos)))
in (Support.Prims.pipe_right _65_14039 Microsoft_FStar_Absyn_Syntax.t_binder))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _65_14041 = (let _65_14040 = (Microsoft_FStar_Tc_Recheck.recompute_typ x)
in (Support.Prims.pipe_right _65_14040 (Microsoft_FStar_Absyn_Util.gen_bvar_p x.Microsoft_FStar_Absyn_Syntax.pos)))
in (Support.Prims.pipe_right _65_14041 Microsoft_FStar_Absyn_Syntax.v_binder))
end))
in (let _33_2390 = (match ((pat_var_opt env ys hd)) with
| None -> begin
(let _65_14042 = (new_binder hd)
in (_65_14042, ys))
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
(let _65_14043 = (new_binder hd)
in (_65_14043, ys))
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
(let _65_14054 = (solve_prob orig None [] wl)
in (solve env _65_14054))
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
(let _65_14060 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _65_14059 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (Support.Microsoft.FStar.Util.fprint2 "Trying flex-flex one pattern (%s) with %s\n" _65_14060 _65_14059)))
end
| false -> begin
()
end)
in (match ((Support.Microsoft.FStar.Unionfind.equivalent u1 u2)) with
| true -> begin
(let sub_probs = (Support.List.map2 (fun ( a ) ( b ) -> (let a = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder a)
in (match (((Support.Prims.fst a), (Support.Prims.fst b))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
(let _65_14064 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (Support.Prims.pipe_right _65_14064 (fun ( _65_14063 ) -> TProb (_65_14063))))
end
| (Support.Microsoft.FStar.Util.Inr (t1), Support.Microsoft.FStar.Util.Inr (t2)) -> begin
(let _65_14066 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (Support.Prims.pipe_right _65_14066 (fun ( _65_14065 ) -> EProb (_65_14065))))
end
| _ -> begin
(failwith ("Impossible"))
end))) xs args2)
in (let guard = (let _65_14068 = (Support.List.map (fun ( p ) -> (Support.Prims.pipe_right (p_guard p) Support.Prims.fst)) sub_probs)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _65_14068))
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
(let sol = (let _65_14070 = (let _65_14069 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' (xs, t2) (Some (k1)) t1.Microsoft_FStar_Absyn_Syntax.pos)
in ((u1, k1), _65_14069))
in UT (_65_14070))
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
(let _65_14071 = (uvi_to_string env sol)
in (Support.Microsoft.FStar.Util.fprint1 "flex-flex quasi pattern (2): %s\n" _65_14071))
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
(let _65_14072 = (Microsoft_FStar_Tc_Recheck.recompute_kind t2)
in (solve_both_pats wl (u1, k1, xs) (u2, k2, ys) _65_14072 t2.Microsoft_FStar_Absyn_Syntax.pos))
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
(let _65_14073 = (uvi_to_string env sol)
in (Support.Microsoft.FStar.Util.fprint1 "flex-flex quasi pattern (1): %s\n" _65_14073))
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
(let _65_14074 = (solve_prob orig None [] wl)
in (solve env _65_14074))
end
| false -> begin
(let t1 = problem.lhs
in (let t2 = problem.rhs
in (match ((Support.Microsoft.FStar.Util.physical_equality t1 t2)) with
| true -> begin
(let _65_14075 = (solve_prob orig None [] wl)
in (solve env _65_14075))
end
| false -> begin
(let _33_2520 = (match ((Microsoft_FStar_Tc_Env.debug env (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _65_14078 = (prob_to_string env orig)
in (let _65_14077 = (let _65_14076 = (Support.List.map (uvi_to_string wl.tcenv) wl.subst)
in (Support.Prims.pipe_right _65_14076 (Support.String.concat "; ")))
in (Support.Microsoft.FStar.Util.fprint2 "Attempting %s\n\tSubst is %s\n" _65_14078 _65_14077)))
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
(let _65_14108 = (mk_cod rest)
in (bs, _65_14108))
end)))
in (let l1 = (Support.List.length bs1)
in (let l2 = (Support.List.length bs2)
in (match ((l1 = l2)) with
| true -> begin
(let _65_14112 = (let _65_14109 = (mk_cod1 [])
in (bs1, _65_14109))
in (let _65_14111 = (let _65_14110 = (mk_cod2 [])
in (bs2, _65_14110))
in (_65_14112, _65_14111)))
end
| false -> begin
(match ((l1 > l2)) with
| true -> begin
(let _65_14115 = (curry l2 bs1 mk_cod1)
in (let _65_14114 = (let _65_14113 = (mk_cod2 [])
in (bs2, _65_14113))
in (_65_14115, _65_14114)))
end
| false -> begin
(let _65_14118 = (let _65_14116 = (mk_cod1 [])
in (bs1, _65_14116))
in (let _65_14117 = (curry l1 bs2 mk_cod2)
in (_65_14118, _65_14117)))
end)
end))))
end))
in (match ((t1.Microsoft_FStar_Absyn_Syntax.n, t2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvd_eq a.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(let _65_14119 = (solve_prob orig None [] wl)
in (solve env _65_14119))
end
| false -> begin
(let _65_14123 = (let _65_14122 = (let _65_14121 = (Microsoft_FStar_Absyn_Util.mk_eq_typ t1 t2)
in (Support.Prims.pipe_left (fun ( _65_14120 ) -> Some (_65_14120)) _65_14121))
in (solve_prob orig _65_14122 [] wl))
in (solve env _65_14123))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs1, c1)), Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs2, c2))) -> begin
(let mk_c = (fun ( c ) ( _33_31 ) -> (match (_33_31) with
| [] -> begin
c
end
| bs -> begin
(let _65_14128 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None c.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Total _65_14128))
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
(let _65_14135 = (let _65_14134 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.Prims.pipe_right _65_14134 Support.Microsoft.FStar.Range.string_of_range))
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Using relation %s at higher order\n" _65_14135 (rel_to_string rel)))
end
| false -> begin
()
end)
in (let _65_14137 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (Support.Prims.pipe_left (fun ( _65_14136 ) -> CProb (_65_14136)) _65_14137)))))))
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
in (let _65_14148 = (mk_problem scope orig t1' problem.relation t2' None "lambda co-domain")
in (Support.Prims.pipe_left (fun ( _65_14147 ) -> TProb (_65_14147)) _65_14148)))))
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine (_), Microsoft_FStar_Absyn_Syntax.Typ_refine (_)) -> begin
(let _33_2608 = (as_refinement env wl t1)
in (match (_33_2608) with
| (x1, phi1) -> begin
(let _33_2611 = (as_refinement env wl t2)
in (match (_33_2611) with
| (x2, phi2) -> begin
(let base_prob = (let _65_14150 = (mk_problem (p_scope orig) orig x1.Microsoft_FStar_Absyn_Syntax.sort problem.relation x2.Microsoft_FStar_Absyn_Syntax.sort problem.element "refinement base type")
in (Support.Prims.pipe_left (fun ( _65_14149 ) -> TProb (_65_14149)) _65_14150))
in (let x1_for_x2 = (let _65_14152 = (Microsoft_FStar_Absyn_Syntax.v_binder x1)
in (let _65_14151 = (Microsoft_FStar_Absyn_Syntax.v_binder x2)
in (Microsoft_FStar_Absyn_Util.mk_subst_one_binder _65_14152 _65_14151)))
in (let phi2 = (Microsoft_FStar_Absyn_Util.subst_typ x1_for_x2 phi2)
in (let mk_imp = (fun ( imp ) ( phi1 ) ( phi2 ) -> (let _65_14169 = (imp phi1 phi2)
in (Support.Prims.pipe_right _65_14169 (guard_on_element problem x1))))
in (let fallback = (fun ( _33_2620 ) -> (match (()) with
| () -> begin
(let impl = (match ((problem.relation = EQ)) with
| true -> begin
(mk_imp Microsoft_FStar_Absyn_Util.mk_iff phi1 phi2)
end
| false -> begin
(mk_imp Microsoft_FStar_Absyn_Util.mk_imp phi1 phi2)
end)
in (let guard = (let _65_14172 = (Support.Prims.pipe_right (p_guard base_prob) Support.Prims.fst)
in (Microsoft_FStar_Absyn_Util.mk_conj _65_14172 impl))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in (match ((problem.relation = EQ)) with
| true -> begin
(let ref_prob = (let _65_14174 = (mk_problem (p_scope orig) orig phi1 EQ phi2 None "refinement formula")
in (Support.Prims.pipe_left (fun ( _65_14173 ) -> TProb (_65_14173)) _65_14174))
in (match ((solve env (let _33_2625 = wl
in {attempting = (ref_prob)::[]; deferred = []; subst = _33_2625.subst; ctr = _33_2625.ctr; slack_vars = _33_2625.slack_vars; defer_ok = false; smt_ok = _33_2625.smt_ok; tcenv = _33_2625.tcenv}))) with
| Failed (_) -> begin
(fallback ())
end
| Success ((subst, _)) -> begin
(let guard = (let _65_14177 = (Support.Prims.pipe_right (p_guard base_prob) Support.Prims.fst)
in (let _65_14176 = (let _65_14175 = (Support.Prims.pipe_right (p_guard ref_prob) Support.Prims.fst)
in (Support.Prims.pipe_right _65_14175 (guard_on_element problem x1)))
in (Microsoft_FStar_Absyn_Util.mk_conj _65_14177 _65_14176)))
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
(let _65_14179 = (destruct_flex_t t1)
in (let _65_14178 = (destruct_flex_t t2)
in (flex_flex orig _65_14179 _65_14178)))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _)) when (problem.relation = EQ) -> begin
(let _65_14180 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _65_14180 t2 wl))
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
in (match ((let _65_14181 = (is_top_level_prob orig)
in (Support.Prims.pipe_left Support.Prims.op_Negation _65_14181))) with
| true -> begin
(let _65_14184 = (Support.Prims.pipe_left (fun ( _65_14182 ) -> TProb (_65_14182)) (let _33_2793 = problem
in {lhs = _33_2793.lhs; relation = new_rel; rhs = _33_2793.rhs; element = _33_2793.element; logical_guard = _33_2793.logical_guard; scope = _33_2793.scope; reason = _33_2793.reason; loc = _33_2793.loc; rank = _33_2793.rank}))
in (let _65_14183 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _65_14184 _65_14183 t2 wl)))
end
| false -> begin
(let _33_2797 = (base_and_refinement env wl t2)
in (match (_33_2797) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _65_14187 = (Support.Prims.pipe_left (fun ( _65_14185 ) -> TProb (_65_14185)) (let _33_2799 = problem
in {lhs = _33_2799.lhs; relation = new_rel; rhs = _33_2799.rhs; element = _33_2799.element; logical_guard = _33_2799.logical_guard; scope = _33_2799.scope; reason = _33_2799.reason; loc = _33_2799.loc; rank = _33_2799.rank}))
in (let _65_14186 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _65_14187 _65_14186 t_base wl)))
end
| Some ((y, phi)) -> begin
(let y' = (let _33_2805 = y
in {Microsoft_FStar_Absyn_Syntax.v = _33_2805.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t1; Microsoft_FStar_Absyn_Syntax.p = _33_2805.Microsoft_FStar_Absyn_Syntax.p})
in (let impl = (guard_on_element problem y' phi)
in (let base_prob = (let _65_14189 = (mk_problem problem.scope orig t1 new_rel y.Microsoft_FStar_Absyn_Syntax.sort problem.element "flex-rigid: base type")
in (Support.Prims.pipe_left (fun ( _65_14188 ) -> TProb (_65_14188)) _65_14189))
in (let guard = (let _65_14190 = (Support.Prims.pipe_right (p_guard base_prob) Support.Prims.fst)
in (Microsoft_FStar_Absyn_Util.mk_conj _65_14190 impl))
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
(let t2 = (let _65_14191 = (base_and_refinement env wl t2)
in (Support.Prims.pipe_left force_refinement _65_14191))
in (solve_t env (let _33_2850 = problem
in {lhs = _33_2850.lhs; relation = _33_2850.relation; rhs = t2; element = _33_2850.element; logical_guard = _33_2850.logical_guard; scope = _33_2850.scope; reason = _33_2850.reason; loc = _33_2850.loc; rank = _33_2850.rank}) wl))
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_refine (_)) -> begin
(let t1 = (let _65_14192 = (base_and_refinement env wl t1)
in (Support.Prims.pipe_left force_refinement _65_14192))
in (solve_t env (let _33_2859 = problem
in {lhs = t1; relation = _33_2859.relation; rhs = _33_2859.rhs; element = _33_2859.element; logical_guard = _33_2859.logical_guard; scope = _33_2859.scope; reason = _33_2859.reason; loc = _33_2859.loc; rank = _33_2859.rank}) wl))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_const (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_btvar (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_const (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_app (_))) -> begin
(let _33_2899 = (head_matches_delta env wl t1 t2)
in (match (_33_2899) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch, _) -> begin
(let head1 = (let _65_14193 = (Microsoft_FStar_Absyn_Util.head_and_args t1)
in (Support.Prims.pipe_right _65_14193 Support.Prims.fst))
in (let head2 = (let _65_14194 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (Support.Prims.pipe_right _65_14194 Support.Prims.fst))
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
(let _65_14200 = (let _65_14199 = (let _65_14198 = (Microsoft_FStar_Absyn_Util.mk_eq_typ t1 t2)
in (Support.Prims.pipe_left (fun ( _65_14197 ) -> Some (_65_14197)) _65_14198))
in (solve_prob orig _65_14199 [] wl))
in (solve env _65_14200))
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
(let _65_14202 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _65_14201 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (Support.Microsoft.FStar.Util.fprint2 "Head matches: %s and %s\n" _65_14202 _65_14201)))
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
(let _65_14207 = (let _65_14206 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (let _65_14205 = (Microsoft_FStar_Absyn_Print.args_to_string args)
in (let _65_14204 = (Microsoft_FStar_Absyn_Print.typ_to_string head')
in (let _65_14203 = (Microsoft_FStar_Absyn_Print.args_to_string args')
in (Support.Microsoft.FStar.Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _65_14206 _65_14205 _65_14204 _65_14203)))))
in (giveup env _65_14207 orig))
end
| false -> begin
(match (((nargs = 0) || (eq_args args args'))) with
| true -> begin
(let _65_14208 = (solve_prob orig None [] wl)
in (solve env _65_14208))
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
(let _65_14211 = (let _65_14210 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (let _65_14209 = (Microsoft_FStar_Absyn_Print.typ_to_string head')
in (Support.Microsoft.FStar.Util.format2 "Assertion failed: expected full match of %s and %s\n" _65_14210 _65_14209)))
in (failwith (_65_14211)))
end
| false -> begin
()
end)
in (let subprobs = (Support.List.map2 (fun ( a ) ( a' ) -> (match (((Support.Prims.fst a), (Support.Prims.fst a'))) with
| (Support.Microsoft.FStar.Util.Inl (t), Support.Microsoft.FStar.Util.Inl (t')) -> begin
(let _65_14215 = (mk_problem (p_scope orig) orig t EQ t' None "type index")
in (Support.Prims.pipe_left (fun ( _65_14214 ) -> TProb (_65_14214)) _65_14215))
end
| (Support.Microsoft.FStar.Util.Inr (v), Support.Microsoft.FStar.Util.Inr (v')) -> begin
(let _65_14217 = (mk_problem (p_scope orig) orig v EQ v' None "term index")
in (Support.Prims.pipe_left (fun ( _65_14216 ) -> EProb (_65_14216)) _65_14217))
end
| _ -> begin
(failwith ("Impossible"))
end)) args args')
in (let formula = (let _65_14219 = (Support.List.map (fun ( p ) -> (Support.Prims.fst (p_guard p))) subprobs)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _65_14219))
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
(let _65_14234 = (sub_prob t1 EQ t2 "effect arg")
in (Support.Prims.pipe_left (fun ( _65_14233 ) -> TProb (_65_14233)) _65_14234))
end
| (Support.Microsoft.FStar.Util.Inr (e1), Support.Microsoft.FStar.Util.Inr (e2)) -> begin
(let _65_14236 = (sub_prob e1 EQ e2 "effect arg")
in (Support.Prims.pipe_left (fun ( _65_14235 ) -> EProb (_65_14235)) _65_14236))
end
| _ -> begin
(failwith ("impossible"))
end)) c1_comp.Microsoft_FStar_Absyn_Syntax.effect_args c2_comp.Microsoft_FStar_Absyn_Syntax.effect_args)
in (let guard = (let _65_14238 = (Support.List.map (fun ( p ) -> (Support.Prims.pipe_right (p_guard p) Support.Prims.fst)) sub_probs)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _65_14238))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in (match ((Support.Microsoft.FStar.Util.physical_equality c1 c2)) with
| true -> begin
(let _65_14239 = (solve_prob orig None [] wl)
in (solve env _65_14239))
end
| false -> begin
(let _33_3046 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _65_14241 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _65_14240 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (Support.Microsoft.FStar.Util.fprint3 "solve_c %s %s %s\n" _65_14241 (rel_to_string problem.relation) _65_14240)))
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
(let _65_14243 = (let _33_3064 = problem
in (let _65_14242 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c1))
in {lhs = _65_14242; relation = _33_3064.relation; rhs = _33_3064.rhs; element = _33_3064.element; logical_guard = _33_3064.logical_guard; scope = _33_3064.scope; reason = _33_3064.reason; loc = _33_3064.loc; rank = _33_3064.rank}))
in (solve_c env _65_14243 wl))
end
| (Microsoft_FStar_Absyn_Syntax.Comp (_), Microsoft_FStar_Absyn_Syntax.Total (_)) -> begin
(let _65_14245 = (let _33_3073 = problem
in (let _65_14244 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c2))
in {lhs = _33_3073.lhs; relation = _33_3073.relation; rhs = _65_14244; element = _33_3073.element; logical_guard = _33_3073.logical_guard; scope = _33_3073.scope; reason = _33_3073.reason; loc = _33_3073.loc; rank = _33_3073.rank}))
in (solve_c env _65_14245 wl))
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
(let _65_14248 = (let _65_14247 = (Microsoft_FStar_Absyn_Print.sli c1.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _65_14246 = (Microsoft_FStar_Absyn_Print.sli c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (Support.Microsoft.FStar.Util.format2 "incompatible monad ordering: %s </: %s" _65_14247 _65_14246)))
in (giveup env _65_14248 orig))
end
| Some (edge) -> begin
(match ((problem.relation = EQ)) with
| true -> begin
(let _33_3106 = (match (c1.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp1), _)::(Support.Microsoft.FStar.Util.Inl (wlp1), _)::[] -> begin
(wp1, wlp1)
end
| _ -> begin
(let _65_14251 = (let _65_14250 = (let _65_14249 = (Microsoft_FStar_Absyn_Syntax.range_of_lid c1.Microsoft_FStar_Absyn_Syntax.effect_name)
in (Support.Microsoft.FStar.Range.string_of_range _65_14249))
in (Support.Microsoft.FStar.Util.format1 "Unexpected number of indices on a normalized effect (%s)" _65_14250))
in (failwith (_65_14251)))
end)
in (match (_33_3106) with
| (wp, wlp) -> begin
(let c1 = (let _65_14257 = (let _65_14256 = (let _65_14252 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wp)
in (Microsoft_FStar_Absyn_Syntax.targ _65_14252))
in (let _65_14255 = (let _65_14254 = (let _65_14253 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wlp)
in (Microsoft_FStar_Absyn_Syntax.targ _65_14253))
in (_65_14254)::[])
in (_65_14256)::_65_14255))
in {Microsoft_FStar_Absyn_Syntax.effect_name = c2.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = c1.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _65_14257; Microsoft_FStar_Absyn_Syntax.flags = c1.Microsoft_FStar_Absyn_Syntax.flags})
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
(let _65_14261 = (let _65_14260 = (Microsoft_FStar_Absyn_Print.sli c1.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _65_14259 = (Microsoft_FStar_Absyn_Print.sli c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (Support.Microsoft.FStar.Util.format2 "Got effects %s and %s, expected normalized effects" _65_14260 _65_14259)))
in (failwith (_65_14261)))
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
in (let _65_14267 = (let _65_14266 = (let _65_14265 = (Microsoft_FStar_Absyn_Syntax.targ c1.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _65_14264 = (let _65_14263 = (let _65_14262 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wpc1)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _65_14262))
in (_65_14263)::[])
in (_65_14265)::_65_14264))
in (c2_decl.Microsoft_FStar_Absyn_Syntax.trivial, _65_14266))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _65_14267 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)))
end
| false -> begin
(let wp2_imp_wp1 = (let _65_14279 = (let _65_14278 = (let _65_14277 = (Microsoft_FStar_Absyn_Syntax.targ c2.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _65_14276 = (let _65_14275 = (Microsoft_FStar_Absyn_Syntax.targ wpc2)
in (let _65_14274 = (let _65_14273 = (let _65_14269 = (let _65_14268 = (Microsoft_FStar_Absyn_Const.kbin Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.imp_lid _65_14268))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _65_14269))
in (let _65_14272 = (let _65_14271 = (let _65_14270 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wpc1)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _65_14270))
in (_65_14271)::[])
in (_65_14273)::_65_14272))
in (_65_14275)::_65_14274))
in (_65_14277)::_65_14276))
in (c2_decl.Microsoft_FStar_Absyn_Syntax.wp_binop, _65_14278))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _65_14279 None r))
in (let _65_14284 = (let _65_14283 = (let _65_14282 = (Microsoft_FStar_Absyn_Syntax.targ c2.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _65_14281 = (let _65_14280 = (Microsoft_FStar_Absyn_Syntax.targ wp2_imp_wp1)
in (_65_14280)::[])
in (_65_14282)::_65_14281))
in (c2_decl.Microsoft_FStar_Absyn_Syntax.wp_as_type, _65_14283))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _65_14284 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)))
end)
in (let base_prob = (let _65_14286 = (sub_prob c1.Microsoft_FStar_Absyn_Syntax.result_typ problem.relation c2.Microsoft_FStar_Absyn_Syntax.result_typ "result type")
in (Support.Prims.pipe_left (fun ( _65_14285 ) -> TProb (_65_14285)) _65_14286))
in (let wl = (let _65_14290 = (let _65_14289 = (let _65_14288 = (Support.Prims.pipe_right (p_guard base_prob) Support.Prims.fst)
in (Microsoft_FStar_Absyn_Util.mk_conj _65_14288 g))
in (Support.Prims.pipe_left (fun ( _65_14287 ) -> Some (_65_14287)) _65_14289))
in (solve_prob orig _65_14290 [] wl))
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
(let _65_14300 = (prob_to_string env orig)
in (Support.Microsoft.FStar.Util.fprint1 "Attempting:\n%s\n" _65_14300))
end
| false -> begin
()
end)
in (let flex_rigid = (fun ( _33_3173 ) ( e2 ) -> (match (_33_3173) with
| (e1, u1, t1, args1) -> begin
(let maybe_vars1 = (pat_vars env [] args1)
in (let sub_problems = (fun ( xs ) ( args2 ) -> (let _33_3200 = (let _65_14316 = (Support.Prims.pipe_right args2 (Support.List.map (fun ( _33_34 ) -> (match (_33_34) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (let _33_3187 = (new_tvar t.Microsoft_FStar_Absyn_Syntax.pos xs kk)
in (match (_33_3187) with
| (gi_xi, gi) -> begin
(let gi_pi = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (gi, args1) (Some (kk)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (let _65_14312 = (let _65_14311 = (sub_prob gi_pi t "type index")
in (Support.Prims.pipe_left (fun ( _65_14310 ) -> TProb (_65_14310)) _65_14311))
in ((Support.Microsoft.FStar.Util.Inl (gi_xi), imp), _65_14312)))
end)))
end
| (Support.Microsoft.FStar.Util.Inr (v), imp) -> begin
(let tt = (Microsoft_FStar_Tc_Recheck.recompute_typ v)
in (let _33_3196 = (new_evar v.Microsoft_FStar_Absyn_Syntax.pos xs tt)
in (match (_33_3196) with
| (gi_xi, gi) -> begin
(let gi_pi = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (gi, args1) (Some (tt)) v.Microsoft_FStar_Absyn_Syntax.pos)
in (let _65_14315 = (let _65_14314 = (sub_prob gi_pi v "expression index")
in (Support.Prims.pipe_left (fun ( _65_14313 ) -> EProb (_65_14313)) _65_14314))
in ((Support.Microsoft.FStar.Util.Inr (gi_xi), imp), _65_14315)))
end)))
end))))
in (Support.Prims.pipe_right _65_14316 Support.List.unzip))
in (match (_33_3200) with
| (gi_xi, gi_pi) -> begin
(let formula = (let _65_14318 = (Support.List.map (fun ( p ) -> (Support.Prims.pipe_right (p_guard p) Support.Prims.fst)) gi_pi)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _65_14318))
in (gi_xi, gi_pi, formula))
end)))
in (let project_e = (fun ( head2 ) ( args2 ) -> (let giveup = (fun ( reason ) -> (let _65_14325 = (Support.Microsoft.FStar.Util.format1 "flex-rigid: refusing to project expressions (%s)" reason)
in (giveup env _65_14325 orig)))
in (match ((let _65_14326 = (Microsoft_FStar_Absyn_Util.compress_exp head2)
in _65_14326.Microsoft_FStar_Absyn_Syntax.n)) with
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
(let _65_14329 = (let _65_14328 = (Microsoft_FStar_Absyn_Print.binders_to_string ", " all_xs)
in (let _65_14327 = (Microsoft_FStar_Absyn_Print.args_to_string args2)
in (Support.Microsoft.FStar.Util.format2 "unequal arity:\n\texpetced binders %s\n\tgot args {%s}" _65_14328 _65_14327)))
in (giveup _65_14329))
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
(match ((let _65_14334 = (Microsoft_FStar_Absyn_Util.compress_exp arg)
in _65_14334.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (z) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvar_eq y z)) with
| true -> begin
(let _33_3269 = (sub_problems all_xs args2)
in (match (_33_3269) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (let _65_14338 = (let _65_14337 = (let _65_14336 = (let _65_14335 = (Microsoft_FStar_Absyn_Util.bvar_to_exp xi)
in (_65_14335, gi_xi))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _65_14336 None e1.Microsoft_FStar_Absyn_Syntax.pos))
in (all_xs, _65_14337))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _65_14338 None e1.Microsoft_FStar_Absyn_Syntax.pos))
in (let _33_3271 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _65_14342 = (Microsoft_FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _65_14341 = (Microsoft_FStar_Absyn_Print.exp_to_string sol)
in (let _65_14340 = (let _65_14339 = (Support.Prims.pipe_right gi_pi (Support.List.map (prob_to_string env)))
in (Support.Prims.pipe_right _65_14339 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.fprint3 "Projected: %s -> %s\nSubprobs=\n%s\n" _65_14342 _65_14341 _65_14340))))
end
| false -> begin
()
end)
in (let _65_14344 = (let _65_14343 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _65_14343))
in (solve env _65_14344))))
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
(let _65_14347 = (let _65_14346 = (Microsoft_FStar_Absyn_Print.binder_to_string x)
in (let _65_14345 = (Microsoft_FStar_Absyn_Print.arg_to_string arg)
in (Support.Microsoft.FStar.Util.format2 "type incorrect term---impossible: expected %s; got %s\n" _65_14346 _65_14345)))
in (giveup _65_14347))
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
(let _65_14351 = (Microsoft_FStar_Absyn_Print.exp_to_string e1)
in (let _65_14350 = (Microsoft_FStar_Absyn_Print.exp_to_string e2)
in (Support.Microsoft.FStar.Util.fprint2 "Imitating expressions: %s =?= %s\n" _65_14351 _65_14350)))
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
(let _65_14353 = (let _65_14352 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.Microsoft_FStar_Absyn_Syntax.pos)
in (xs, _65_14352))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _65_14353 None e1.Microsoft_FStar_Absyn_Syntax.pos))
end))
in (let _33_3313 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _65_14357 = (Microsoft_FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _65_14356 = (Microsoft_FStar_Absyn_Print.exp_to_string sol)
in (let _65_14355 = (let _65_14354 = (Support.Prims.pipe_right gi_pi (Support.List.map (prob_to_string env)))
in (Support.Prims.pipe_right _65_14354 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.fprint3 "Imitated: %s -> %s\nSubprobs=\n%s\n" _65_14357 _65_14356 _65_14355))))
end
| false -> begin
()
end)
in (let _65_14359 = (let _65_14358 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _65_14358))
in (solve env _65_14359))))
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
in (let _65_14360 = (solve_prob orig None ((UE (((u1, t1), sol)))::[]) wl)
in (solve env _65_14360)))
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
in (let _33_3358 = (let _65_14365 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_evar _65_14365 zs tt))
in (match (_33_3358) with
| (u, _) -> begin
(let sub1 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (xs, u) (Some (t1)) e1.Microsoft_FStar_Absyn_Syntax.pos)
in (let sub2 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (ys, u) (Some (t2)) e1.Microsoft_FStar_Absyn_Syntax.pos)
in (let _65_14366 = (solve_prob orig None ((UE (((u1, t1), sub1)))::(UE (((u2, t2), sub2)))::[]) wl)
in (solve env _65_14366))))
end))))
end)
end)))
end))
in (let smt_fallback = (fun ( e1 ) ( e2 ) -> (match (wl.smt_ok) with
| true -> begin
(let _33_3364 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _65_14371 = (prob_to_string env orig)
in (Support.Microsoft.FStar.Util.fprint1 "Using SMT to solve:\n%s\n" _65_14371))
end
| false -> begin
()
end)
in (let _33_3369 = (let _65_14373 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _65_14372 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _65_14373 _65_14372 Microsoft_FStar_Absyn_Syntax.ktype)))
in (match (_33_3369) with
| (t, _) -> begin
(let _65_14377 = (let _65_14376 = (let _65_14375 = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (Support.Prims.pipe_left (fun ( _65_14374 ) -> Some (_65_14374)) _65_14375))
in (solve_prob orig _65_14376 [] wl))
in (solve env _65_14377))
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
(let _65_14379 = (destruct_flex_e e1)
in (let _65_14378 = (destruct_flex_e e2)
in (flex_flex _65_14379 _65_14378)))
end
| ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _)) -> begin
(let _65_14380 = (destruct_flex_e e1)
in (flex_rigid _65_14380 e2))
end
| ((_, Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) -> begin
(let _65_14381 = (destruct_flex_e e2)
in (flex_rigid _65_14381 e1))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (x1), Microsoft_FStar_Absyn_Syntax.Exp_bvar (x1')) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvd_eq x1.Microsoft_FStar_Absyn_Syntax.v x1'.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(let _65_14382 = (solve_prob orig None [] wl)
in (solve env _65_14382))
end
| false -> begin
(let _65_14388 = (let _65_14387 = (let _65_14386 = (let _65_14385 = (Microsoft_FStar_Tc_Recheck.recompute_typ e1)
in (let _65_14384 = (Microsoft_FStar_Tc_Recheck.recompute_typ e2)
in (Microsoft_FStar_Absyn_Util.mk_eq _65_14385 _65_14384 e1 e2)))
in (Support.Prims.pipe_left (fun ( _65_14383 ) -> Some (_65_14383)) _65_14386))
in (solve_prob orig _65_14387 [] wl))
in (solve env _65_14388))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv1, _)), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv1', _))) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv1.Microsoft_FStar_Absyn_Syntax.v fv1'.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(let _65_14389 = (solve_prob orig None [] wl)
in (solve env _65_14389))
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
(let _65_14394 = (solve_prob orig None [] wl)
in (solve env _65_14394))
end
| false -> begin
(giveup env "constants unequal" orig)
end))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _) -> begin
(let _65_14396 = (let _33_3591 = problem
in (let _65_14395 = (whnf_e env e1)
in {lhs = _65_14395; relation = _33_3591.relation; rhs = _33_3591.rhs; element = _33_3591.element; logical_guard = _33_3591.logical_guard; scope = _33_3591.scope; reason = _33_3591.reason; loc = _33_3591.loc; rank = _33_3591.rank}))
in (solve_e env _65_14396 wl))
end
| (_, Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _65_14398 = (let _33_3612 = problem
in (let _65_14397 = (whnf_e env e2)
in {lhs = _33_3612.lhs; relation = _33_3612.relation; rhs = _65_14397; element = _33_3612.element; logical_guard = _33_3612.logical_guard; scope = _33_3612.scope; reason = _33_3612.reason; loc = _33_3612.loc; rank = _33_3612.rank}))
in (solve_e env _65_14398 wl))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((head1, args1)), Microsoft_FStar_Absyn_Syntax.Exp_app ((head2, args2))) -> begin
(let orig_wl = wl
in (let rec solve_args = (fun ( sub_probs ) ( wl ) ( args1 ) ( args2 ) -> (match ((args1, args2)) with
| ([], []) -> begin
(let guard = (let _65_14408 = (let _65_14407 = (Support.List.map p_guard sub_probs)
in (Support.Prims.pipe_right _65_14407 (Support.List.map Support.Prims.fst)))
in (Microsoft_FStar_Absyn_Util.mk_conj_l _65_14408))
in (let g = (simplify_formula env guard)
in (let g = (Microsoft_FStar_Absyn_Util.compress_typ g)
in (match (g.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
(let _65_14409 = (solve_prob orig None wl.subst (let _33_3637 = orig_wl
in {attempting = _33_3637.attempting; deferred = _33_3637.deferred; subst = []; ctr = _33_3637.ctr; slack_vars = _33_3637.slack_vars; defer_ok = _33_3637.defer_ok; smt_ok = _33_3637.smt_ok; tcenv = _33_3637.tcenv}))
in (solve env _65_14409))
end
| _ -> begin
(let _33_3644 = (let _65_14411 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _65_14410 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _65_14411 _65_14410 Microsoft_FStar_Absyn_Syntax.ktype)))
in (match (_33_3644) with
| (t, _) -> begin
(let guard = (let _65_14412 = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (Microsoft_FStar_Absyn_Util.mk_disj g _65_14412))
in (let _65_14413 = (solve_prob orig (Some (guard)) wl.subst (let _33_3646 = orig_wl
in {attempting = _33_3646.attempting; deferred = _33_3646.deferred; subst = []; ctr = _33_3646.ctr; slack_vars = _33_3646.slack_vars; defer_ok = _33_3646.defer_ok; smt_ok = _33_3646.smt_ok; tcenv = _33_3646.tcenv}))
in (solve env _65_14413)))
end))
end))))
end
| (arg1::rest1, arg2::rest2) -> begin
(let prob = (match (((Support.Prims.fst arg1), (Support.Prims.fst arg2))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
(let _65_14415 = (mk_problem (p_scope orig) orig t1 EQ t2 None "expression type arg")
in (Support.Prims.pipe_left (fun ( _65_14414 ) -> TProb (_65_14414)) _65_14415))
end
| (Support.Microsoft.FStar.Util.Inr (e1), Support.Microsoft.FStar.Util.Inr (e2)) -> begin
(let _65_14417 = (mk_problem (p_scope orig) orig e1 EQ e2 None "expression arg")
in (Support.Prims.pipe_left (fun ( _65_14416 ) -> EProb (_65_14416)) _65_14417))
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
in (let rec match_head_and_args = (fun ( head1 ) ( head2 ) -> (match ((let _65_14425 = (let _65_14422 = (Microsoft_FStar_Absyn_Util.compress_exp head1)
in _65_14422.Microsoft_FStar_Absyn_Syntax.n)
in (let _65_14424 = (let _65_14423 = (Microsoft_FStar_Absyn_Util.compress_exp head2)
in _65_14423.Microsoft_FStar_Absyn_Syntax.n)
in (_65_14425, _65_14424)))) with
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
(let _65_14427 = (let _33_3727 = problem
in (let _65_14426 = (whnf_e env e1)
in {lhs = _65_14426; relation = _33_3727.relation; rhs = _33_3727.rhs; element = _33_3727.element; logical_guard = _33_3727.logical_guard; scope = _33_3727.scope; reason = _33_3727.reason; loc = _33_3727.loc; rank = _33_3727.rank}))
in (solve_e env _65_14427 wl))
end
| (_, Microsoft_FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(let _65_14429 = (let _33_3735 = problem
in (let _65_14428 = (whnf_e env e2)
in {lhs = _33_3735.lhs; relation = _33_3735.relation; rhs = _65_14428; element = _33_3735.element; logical_guard = _33_3735.logical_guard; scope = _33_3735.scope; reason = _33_3735.reason; loc = _33_3735.loc; rank = _33_3735.rank}))
in (solve_e env _65_14429 wl))
end
| _ -> begin
(smt_fallback e1 e2)
end))
in (match_head_and_args head1 head2))))
end
| _ -> begin
(let _33_3744 = (let _65_14431 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _65_14430 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _65_14431 _65_14430 Microsoft_FStar_Absyn_Syntax.ktype)))
in (match (_33_3744) with
| (t, _) -> begin
(let guard = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (let _33_3746 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _65_14432 = (Microsoft_FStar_Absyn_Print.typ_to_string guard)
in (Support.Microsoft.FStar.Util.fprint1 "Emitting guard %s\n" _65_14432))
end
| false -> begin
()
end)
in (let _65_14436 = (let _65_14435 = (let _65_14434 = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (Support.Prims.pipe_left (fun ( _65_14433 ) -> Some (_65_14433)) _65_14434))
in (solve_prob orig _65_14435 [] wl))
in (solve env _65_14436))))
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

let is_Mkguard_t = (fun ( _ ) -> (failwith ("Not yet implemented")))

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
in (let carry = (let _65_14460 = (Support.List.map (fun ( _33_3763 ) -> (match (_33_3763) with
| (_, x) -> begin
(prob_to_string env x)
end)) g.deferred.carry)
in (Support.Prims.pipe_right _65_14460 (Support.String.concat ",\n")))
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
in (let _65_14477 = (let _33_3794 = g
in (let _65_14476 = (let _65_14475 = (let _65_14474 = (let _65_14473 = (let _65_14472 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_65_14472)::[])
in (_65_14473, f))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _65_14474 None f.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.Prims.pipe_left (fun ( _65_14471 ) -> NonTrivial (_65_14471)) _65_14475))
in {guard_f = _65_14476; deferred = _33_3794.deferred; implicits = _33_3794.implicits}))
in Some (_65_14477)))
end))

let apply_guard = (fun ( g ) ( e ) -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _33_3801 = g
in (let _65_14489 = (let _65_14488 = (let _65_14487 = (let _65_14486 = (let _65_14485 = (let _65_14484 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_65_14484)::[])
in (f, _65_14485))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _65_14486))
in (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn f.Microsoft_FStar_Absyn_Syntax.pos (Some (Microsoft_FStar_Absyn_Syntax.ktype))) _65_14487))
in NonTrivial (_65_14488))
in {guard_f = _65_14489; deferred = _33_3801.deferred; implicits = _33_3801.implicits}))
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
(let _65_14496 = (Microsoft_FStar_Absyn_Util.mk_conj f1 f2)
in NonTrivial (_65_14496))
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

let binop_guard = (fun ( f ) ( g1 ) ( g2 ) -> (let _65_14519 = (f g1.guard_f g2.guard_f)
in {guard_f = _65_14519; deferred = {carry = (Support.List.append g1.deferred.carry g2.deferred.carry); slack = (Support.List.append g1.deferred.slack g2.deferred.slack)}; implicits = (Support.List.append g1.implicits g2.implicits)}))

let conj_guard = (fun ( g1 ) ( g2 ) -> (binop_guard conj_guard_f g1 g2))

let imp_guard = (fun ( g1 ) ( g2 ) -> (binop_guard imp_guard_f g1 g2))

let close_guard = (fun ( binders ) ( g ) -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _33_3851 = g
in (let _65_14534 = (let _65_14533 = (Microsoft_FStar_Absyn_Util.close_forall binders f)
in (Support.Prims.pipe_right _65_14533 (fun ( _65_14532 ) -> NonTrivial (_65_14532))))
in {guard_f = _65_14534; deferred = _33_3851.deferred; implicits = _33_3851.implicits}))
end))

let mk_guard = (fun ( g ) ( ps ) ( slack ) ( locs ) -> {guard_f = g; deferred = {carry = ps; slack = slack}; implicits = []})

let new_t_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) -> (let reason = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _65_14546 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env lhs)
in (let _65_14545 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env rhs)
in (Support.Microsoft.FStar.Util.format3 "Top-level:\n%s\n\t%s\n%s" _65_14546 (rel_to_string rel) _65_14545)))
end
| false -> begin
"TOP"
end)
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

let new_t_prob = (fun ( env ) ( t1 ) ( rel ) ( t2 ) -> (let x = (let _65_14555 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p _65_14555 t1))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))))
in (let p = (let _65_14559 = (let _65_14557 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.Prims.pipe_left (fun ( _65_14556 ) -> Some (_65_14556)) _65_14557))
in (let _65_14558 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_t_problem env t1 rel t2 _65_14559 _65_14558)))
in (TProb (p), x)))))

let new_k_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) -> (let reason = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _65_14567 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env lhs)
in (let _65_14566 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env rhs)
in (Support.Microsoft.FStar.Util.format3 "Top-level:\n%s\n\t%s\n%s" _65_14567 (rel_to_string rel) _65_14566)))
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
(let _65_14572 = (Microsoft_FStar_Absyn_Print.typ_to_string f)
in (Support.Microsoft.FStar.Util.fprint1 "Simplifying guard %s\n" _65_14572))
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
(let _65_14584 = (explain env d s)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.print_string _65_14584))
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
(let _65_14596 = (let _65_14595 = (let _65_14594 = (let _65_14593 = (Support.Prims.pipe_right (p_guard prob) Support.Prims.fst)
in (Support.Prims.pipe_right _65_14593 (fun ( _65_14592 ) -> NonTrivial (_65_14592))))
in {guard_f = _65_14594; deferred = d; implicits = []})
in (simplify_guard env _65_14595))
in (Support.Prims.pipe_left (fun ( _65_14591 ) -> Some (_65_14591)) _65_14596))
end))

let try_keq = (fun ( env ) ( k1 ) ( k2 ) -> (let _33_3923 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _65_14604 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (let _65_14603 = (Microsoft_FStar_Absyn_Print.kind_to_string k2)
in (Support.Microsoft.FStar.Util.fprint2 "try_keq of %s and %s\n" _65_14604 _65_14603)))
end
| false -> begin
()
end)
in (let prob = (let _65_14609 = (let _65_14608 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env k1)
in (let _65_14607 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env k2)
in (let _65_14606 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_k_problem env _65_14608 EQ _65_14607 None _65_14606))))
in (Support.Prims.pipe_left (fun ( _65_14605 ) -> KProb (_65_14605)) _65_14609))
in (let _65_14611 = (solve_and_commit env (singleton env prob) (fun ( _33_3926 ) -> None))
in (Support.Prims.pipe_left (with_guard env prob) _65_14611)))))

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
(let _65_14622 = (let _65_14621 = (let _65_14620 = (Microsoft_FStar_Tc_Errors.incompatible_kinds env k2 k1)
in (_65_14620, r))
in Microsoft_FStar_Absyn_Syntax.Error (_65_14621))
in (raise (_65_14622)))
end
| Some (t) -> begin
(let _65_14625 = (let _65_14624 = (let _65_14623 = (Microsoft_FStar_Tc_Errors.expected_typ_of_kind env k2 t k1)
in (_65_14623, r))
in Microsoft_FStar_Absyn_Syntax.Error (_65_14624))
in (raise (_65_14625)))
end))
end
| Some (g) -> begin
g
end))

let subkind = (fun ( env ) ( k1 ) ( k2 ) -> (let _33_3945 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _65_14635 = (let _65_14632 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _65_14632))
in (let _65_14634 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (let _65_14633 = (Microsoft_FStar_Absyn_Print.kind_to_string k2)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) subkind of %s and %s\n" _65_14635 _65_14634 _65_14633))))
end
| false -> begin
()
end)
in (let prob = (let _65_14640 = (let _65_14639 = (whnf_k env k1)
in (let _65_14638 = (whnf_k env k2)
in (let _65_14637 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_k_problem env _65_14639 SUB _65_14638 None _65_14637))))
in (Support.Prims.pipe_left (fun ( _65_14636 ) -> KProb (_65_14636)) _65_14640))
in (let res = (let _65_14647 = (let _65_14646 = (solve_and_commit env (singleton env prob) (fun ( _33_3948 ) -> (let _65_14645 = (let _65_14644 = (let _65_14643 = (Microsoft_FStar_Tc_Errors.incompatible_kinds env k1 k2)
in (let _65_14642 = (Microsoft_FStar_Tc_Env.get_range env)
in (_65_14643, _65_14642)))
in Microsoft_FStar_Absyn_Syntax.Error (_65_14644))
in (raise (_65_14645)))))
in (Support.Prims.pipe_left (with_guard env prob) _65_14646))
in (Support.Microsoft.FStar.Util.must _65_14647))
in res))))

let try_teq = (fun ( env ) ( t1 ) ( t2 ) -> (let _33_3954 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _65_14655 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _65_14654 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (Support.Microsoft.FStar.Util.fprint2 "try_teq of %s and %s\n" _65_14655 _65_14654)))
end
| false -> begin
()
end)
in (let prob = (let _65_14658 = (let _65_14657 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_t_problem env t1 EQ t2 None _65_14657))
in (Support.Prims.pipe_left (fun ( _65_14656 ) -> TProb (_65_14656)) _65_14658))
in (let g = (let _65_14660 = (solve_and_commit env (singleton env prob) (fun ( _33_3957 ) -> None))
in (Support.Prims.pipe_left (with_guard env prob) _65_14660))
in g))))

let teq = (fun ( env ) ( t1 ) ( t2 ) -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _65_14670 = (let _65_14669 = (let _65_14668 = (Microsoft_FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _65_14667 = (Microsoft_FStar_Tc_Env.get_range env)
in (_65_14668, _65_14667)))
in Microsoft_FStar_Absyn_Syntax.Error (_65_14669))
in (raise (_65_14670)))
end
| Some (g) -> begin
(let _33_3966 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _65_14673 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _65_14672 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (let _65_14671 = (guard_to_string env g)
in (Support.Microsoft.FStar.Util.fprint3 "teq of %s and %s succeeded with guard %s\n" _65_14673 _65_14672 _65_14671))))
end
| false -> begin
()
end)
in g)
end))

let try_subtype = (fun ( env ) ( t1 ) ( t2 ) -> (let _33_3971 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _65_14681 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _65_14680 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.fprint2 "try_subtype of %s and %s\n" _65_14681 _65_14680)))
end
| false -> begin
()
end)
in (let _33_3975 = (new_t_prob env t1 SUB t2)
in (match (_33_3975) with
| (prob, x) -> begin
(let g = (let _65_14683 = (solve_and_commit env (singleton env prob) (fun ( _33_3976 ) -> None))
in (Support.Prims.pipe_left (with_guard env prob) _65_14683))
in (let _33_3979 = (match (((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) && (Support.Microsoft.FStar.Util.is_some g))) with
| true -> begin
(let _65_14687 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _65_14686 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _65_14685 = (let _65_14684 = (Support.Microsoft.FStar.Util.must g)
in (guard_to_string env _65_14684))
in (Support.Microsoft.FStar.Util.fprint3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _65_14687 _65_14686 _65_14685))))
end
| false -> begin
()
end)
in (abstract_guard x g)))
end))))

let subtype_fail = (fun ( env ) ( t1 ) ( t2 ) -> (let _65_14694 = (let _65_14693 = (let _65_14692 = (Microsoft_FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _65_14691 = (Microsoft_FStar_Tc_Env.get_range env)
in (_65_14692, _65_14691)))
in Microsoft_FStar_Absyn_Syntax.Error (_65_14693))
in (raise (_65_14694))))

let subtype = (fun ( env ) ( t1 ) ( t2 ) -> (match ((try_subtype env t1 t2)) with
| Some (f) -> begin
f
end
| None -> begin
(subtype_fail env t1 t2)
end))

let sub_comp = (fun ( env ) ( c1 ) ( c2 ) -> (let _33_3993 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _65_14708 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _65_14707 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (Support.Microsoft.FStar.Util.fprint2 "sub_comp of %s and %s\n" _65_14708 _65_14707)))
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
in (let prob = (let _65_14711 = (let _65_14710 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_problem env c1 rel c2 None _65_14710 "sub_comp"))
in (Support.Prims.pipe_left (fun ( _65_14709 ) -> CProb (_65_14709)) _65_14711))
in (let _65_14713 = (solve_and_commit env (singleton env prob) (fun ( _33_3997 ) -> None))
in (Support.Prims.pipe_left (with_guard env prob) _65_14713))))))

let solve_deferred_constraints = (fun ( env ) ( g ) -> (let fail = (fun ( _33_4004 ) -> (match (_33_4004) with
| (d, s) -> begin
(let msg = (explain env d s)
in (raise (Microsoft_FStar_Absyn_Syntax.Error ((msg, (p_loc d))))))
end))
in (let _33_4009 = (match (((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) && ((Support.List.length g.deferred.carry) <> 0))) with
| true -> begin
(let _65_14726 = (let _65_14725 = (Support.Prims.pipe_right g.deferred.carry (Support.List.map (fun ( _33_4008 ) -> (match (_33_4008) with
| (msg, x) -> begin
(let _65_14724 = (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range (p_loc x))
in (let _65_14723 = (prob_to_string env x)
in (let _65_14722 = (let _65_14721 = (Support.Prims.pipe_right (p_guard x) Support.Prims.fst)
in (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env _65_14721))
in (Support.Microsoft.FStar.Util.format4 "(At %s) %s\n%s\nguard is %s\n" _65_14724 msg _65_14723 _65_14722))))
end))))
in (Support.Prims.pipe_right _65_14725 (Support.String.concat "\n")))
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.fprint1 "Trying to solve carried problems: begin\n%s\nend\n") _65_14726))
end
| false -> begin
()
end)
in (let gopt = (let _65_14727 = (wl_of_guard env g.deferred)
in (solve_and_commit env _65_14727 fail))
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
(let _65_14734 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _65_14733 = (let _65_14732 = (Microsoft_FStar_Absyn_Print.formula_to_string vc)
in (Support.Microsoft.FStar.Util.format1 "Checking VC=\n%s\n" _65_14732))
in (Microsoft_FStar_Tc_Errors.diag _65_14734 _65_14733)))
end
| false -> begin
()
end)
in (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.solve env vc))
end))
end)
end)))




