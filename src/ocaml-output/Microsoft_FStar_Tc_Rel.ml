
let new_kvar = (fun ( r ) ( binders ) -> (let wf = (fun ( k ) ( _35_39 ) -> (match (()) with
| () -> begin
true
end))
in (let u = (Support.Microsoft.FStar.Unionfind.fresh Microsoft_FStar_Absyn_Syntax.Uvar)
in (let _70_14483 = (let _70_14482 = (let _70_14481 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (u, _70_14481))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar _70_14482 r))
in (_70_14483, u)))))

let new_tvar = (fun ( r ) ( binders ) ( k ) -> (let wf = (fun ( t ) ( tk ) -> true)
in (let binders = (Support.All.pipe_right binders (Support.List.filter (fun ( x ) -> (let _70_14495 = (Microsoft_FStar_Absyn_Syntax.is_null_binder x)
in (Support.All.pipe_right _70_14495 Support.Prims.op_Negation)))))
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
in (let _70_14496 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (uv, args) None r)
in (_70_14496, uv)))))
end)))))

let new_evar = (fun ( r ) ( binders ) ( t ) -> (let wf = (fun ( e ) ( t ) -> true)
in (let binders = (Support.All.pipe_right binders (Support.List.filter (fun ( x ) -> (let _70_14508 = (Microsoft_FStar_Absyn_Syntax.is_null_binder x)
in (Support.All.pipe_right _70_14508 Support.Prims.op_Negation)))))
in (let uv = (Support.Microsoft.FStar.Unionfind.fresh Microsoft_FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (Microsoft_FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t) None r)
in (uv, uv))
end
| _35_69 -> begin
(let args = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (let t' = (let _70_14510 = (let _70_14509 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (binders, _70_14509))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _70_14510 None r))
in (let uv = (Microsoft_FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t') None r)
in (match (args) with
| [] -> begin
(uv, uv)
end
| _35_75 -> begin
(let _70_14511 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (uv, args) None r)
in (_70_14511, uv))
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

let ___KProb____0 = (fun ( projectee ) -> (match (projectee) with
| KProb (_35_92) -> begin
_35_92
end))

let ___TProb____0 = (fun ( projectee ) -> (match (projectee) with
| TProb (_35_95) -> begin
_35_95
end))

let ___EProb____0 = (fun ( projectee ) -> (match (projectee) with
| EProb (_35_98) -> begin
_35_98
end))

let ___CProb____0 = (fun ( projectee ) -> (match (projectee) with
| CProb (_35_101) -> begin
_35_101
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

let ___UK____0 = (fun ( projectee ) -> (match (projectee) with
| UK (_35_104) -> begin
_35_104
end))

let ___UT____0 = (fun ( projectee ) -> (match (projectee) with
| UT (_35_107) -> begin
_35_107
end))

let ___UE____0 = (fun ( projectee ) -> (match (projectee) with
| UE (_35_110) -> begin
_35_110
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

let ___Success____0 = (fun ( projectee ) -> (match (projectee) with
| Success (_35_125) -> begin
_35_125
end))

let ___Failed____0 = (fun ( projectee ) -> (match (projectee) with
| Failed (_35_128) -> begin
_35_128
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
(let _70_14713 = (Microsoft_FStar_Absyn_Print.kind_to_string p.lhs)
in (let _70_14712 = (Microsoft_FStar_Absyn_Print.kind_to_string p.rhs)
in (Support.Microsoft.FStar.Util.format3 "\t%s\n\t\t%s\n\t%s" _70_14713 (rel_to_string p.relation) _70_14712)))
end
| TProb (p) -> begin
(let _70_14726 = (let _70_14725 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env p.lhs)
in (let _70_14724 = (let _70_14723 = (Microsoft_FStar_Absyn_Print.tag_of_typ p.lhs)
in (let _70_14722 = (let _70_14721 = (let _70_14720 = (Support.All.pipe_right p.reason Support.List.hd)
in (let _70_14719 = (let _70_14718 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env p.rhs)
in (let _70_14717 = (let _70_14716 = (Microsoft_FStar_Absyn_Print.tag_of_typ p.rhs)
in (let _70_14715 = (let _70_14714 = (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env (Support.Prims.fst p.logical_guard))
in (_70_14714)::[])
in (_70_14716)::_70_14715))
in (_70_14718)::_70_14717))
in (_70_14720)::_70_14719))
in ((rel_to_string p.relation))::_70_14721)
in (_70_14723)::_70_14722))
in (_70_14725)::_70_14724))
in (Support.Microsoft.FStar.Util.format "\t%s (%s) \n\t\t%s(%s)\n\t%s (%s) (guard %s)" _70_14726))
end
| EProb (p) -> begin
(let _70_14728 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env p.lhs)
in (let _70_14727 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env p.rhs)
in (Support.Microsoft.FStar.Util.format3 "\t%s \n\t\t%s\n\t%s" _70_14728 (rel_to_string p.relation) _70_14727)))
end
| CProb (p) -> begin
(let _70_14730 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env p.lhs)
in (let _70_14729 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env p.rhs)
in (Support.Microsoft.FStar.Util.format3 "\t%s \n\t\t%s\n\t%s" _70_14730 (rel_to_string p.relation) _70_14729)))
end))

let uvi_to_string = (fun ( env ) ( uvi ) -> (let str = (fun ( u ) -> (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _70_14736 = (Support.Microsoft.FStar.Unionfind.uvar_id u)
in (Support.All.pipe_right _70_14736 Support.Microsoft.FStar.Util.string_of_int))
end))
in (match (uvi) with
| UK ((u, _35_150)) -> begin
(let _70_14737 = (str u)
in (Support.All.pipe_right _70_14737 (Support.Microsoft.FStar.Util.format1 "UK %s")))
end
| UT (((u, _35_155), t)) -> begin
(let _70_14740 = (str u)
in (Support.All.pipe_right _70_14740 (fun ( x ) -> (let _70_14739 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.format2 "UT %s %s" x _70_14739)))))
end
| UE (((u, _35_163), _35_166)) -> begin
(let _70_14741 = (str u)
in (Support.All.pipe_right _70_14741 (Support.Microsoft.FStar.Util.format1 "UE %s")))
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

let invert = (fun ( p ) -> (let _35_174 = p
in {lhs = p.rhs; relation = (invert_rel p.relation); rhs = p.lhs; element = _35_174.element; logical_guard = _35_174.logical_guard; scope = _35_174.scope; reason = _35_174.reason; loc = _35_174.loc; rank = _35_174.rank}))

let maybe_invert = (fun ( p ) -> (match ((p.relation = SUBINV)) with
| true -> begin
(invert p)
end
| false -> begin
p
end))

let maybe_invert_p = (fun ( _35_4 ) -> (match (_35_4) with
| KProb (p) -> begin
(Support.All.pipe_right (maybe_invert p) (fun ( _70_14748 ) -> KProb (_70_14748)))
end
| TProb (p) -> begin
(Support.All.pipe_right (maybe_invert p) (fun ( _70_14749 ) -> TProb (_70_14749)))
end
| EProb (p) -> begin
(Support.All.pipe_right (maybe_invert p) (fun ( _70_14750 ) -> EProb (_70_14750)))
end
| CProb (p) -> begin
(Support.All.pipe_right (maybe_invert p) (fun ( _70_14751 ) -> CProb (_70_14751)))
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
(Support.All.pipe_left (fun ( _70_14770 ) -> KProb (_70_14770)) (invert p))
end
| TProb (p) -> begin
(Support.All.pipe_left (fun ( _70_14771 ) -> TProb (_70_14771)) (invert p))
end
| EProb (p) -> begin
(Support.All.pipe_left (fun ( _70_14772 ) -> EProb (_70_14772)) (invert p))
end
| CProb (p) -> begin
(Support.All.pipe_left (fun ( _70_14773 ) -> CProb (_70_14773)) (invert p))
end))

let is_top_level_prob = (fun ( p ) -> ((Support.All.pipe_right (p_reason p) Support.List.length) = 1))

let mk_problem = (fun ( scope ) ( orig ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( reason ) -> (let _70_14783 = (new_tvar (p_loc orig) scope Microsoft_FStar_Absyn_Syntax.ktype)
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _70_14783; scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None}))

let new_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) ( reason ) -> (let _70_14793 = (let _70_14792 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_14791 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _70_14792 _70_14791 Microsoft_FStar_Absyn_Syntax.ktype)))
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _70_14793; scope = []; reason = (reason)::[]; loc = loc; rank = None}))

let problem_using_guard = (fun ( orig ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( reason ) -> {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = (p_guard orig); scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None})

let guard_on_element = (fun ( problem ) ( x ) ( phi ) -> (match (problem.element) with
| None -> begin
(let _70_14804 = (let _70_14803 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_70_14803)::[])
in (Microsoft_FStar_Absyn_Util.close_forall _70_14804 phi))
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
in (let _35_293 = (p_guard prob)
in (match (_35_293) with
| (_35_291, uv) -> begin
(let _35_301 = (match ((let _70_14815 = (Microsoft_FStar_Absyn_Util.compress_typ uv)
in _70_14815.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uvar, k)) -> begin
(let phi = (Microsoft_FStar_Absyn_Util.close_for_kind phi k)
in (Microsoft_FStar_Absyn_Util.unchecked_unify uvar phi))
end
| _35_300 -> begin
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
| _35_305 -> begin
(let _35_306 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug wl.tcenv) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14817 = (let _70_14816 = (Support.List.map (uvi_to_string wl.tcenv) uvis)
in (Support.All.pipe_right _70_14816 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.fprint1 "Extending solution: %s\n" _70_14817))
end
| false -> begin
()
end)
in (let _35_308 = wl
in {attempting = _35_308.attempting; deferred = _35_308.deferred; subst = (Support.List.append uvis wl.subst); ctr = (wl.ctr + 1); slack_vars = _35_308.slack_vars; defer_ok = _35_308.defer_ok; smt_ok = _35_308.smt_ok; tcenv = _35_308.tcenv}))
end))
end))))

let extend_solution = (fun ( sol ) ( wl ) -> (let _35_312 = wl
in {attempting = _35_312.attempting; deferred = _35_312.deferred; subst = (sol)::wl.subst; ctr = (wl.ctr + 1); slack_vars = _35_312.slack_vars; defer_ok = _35_312.defer_ok; smt_ok = _35_312.smt_ok; tcenv = _35_312.tcenv}))

let solve_prob = (fun ( prob ) ( logical_guard ) ( uvis ) ( wl ) -> (solve_prob' false prob logical_guard uvis wl))

let explain = (fun ( env ) ( d ) ( s ) -> (let _70_14838 = (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range (p_loc d))
in (let _70_14837 = (prob_to_string env d)
in (let _70_14836 = (Support.All.pipe_right (p_reason d) (Support.String.concat "\n\t>"))
in (Support.Microsoft.FStar.Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _70_14838 _70_14837 _70_14836 s)))))

let empty_worklist = (fun ( env ) -> {attempting = []; deferred = []; subst = []; ctr = 0; slack_vars = []; defer_ok = true; smt_ok = true; tcenv = env})

let singleton = (fun ( env ) ( prob ) -> (let _35_324 = (empty_worklist env)
in {attempting = (prob)::[]; deferred = _35_324.deferred; subst = _35_324.subst; ctr = _35_324.ctr; slack_vars = _35_324.slack_vars; defer_ok = _35_324.defer_ok; smt_ok = _35_324.smt_ok; tcenv = _35_324.tcenv}))

let wl_of_guard = (fun ( env ) ( g ) -> (let _35_328 = (empty_worklist env)
in (let _70_14849 = (Support.List.map Support.Prims.snd g.carry)
in {attempting = _70_14849; deferred = _35_328.deferred; subst = _35_328.subst; ctr = _35_328.ctr; slack_vars = g.slack; defer_ok = false; smt_ok = _35_328.smt_ok; tcenv = _35_328.tcenv})))

let defer = (fun ( reason ) ( prob ) ( wl ) -> (let _35_333 = wl
in {attempting = _35_333.attempting; deferred = ((wl.ctr, reason, prob))::wl.deferred; subst = _35_333.subst; ctr = _35_333.ctr; slack_vars = _35_333.slack_vars; defer_ok = _35_333.defer_ok; smt_ok = _35_333.smt_ok; tcenv = _35_333.tcenv}))

let attempt = (fun ( probs ) ( wl ) -> (let _35_337 = wl
in {attempting = (Support.List.append probs wl.attempting); deferred = _35_337.deferred; subst = _35_337.subst; ctr = _35_337.ctr; slack_vars = _35_337.slack_vars; defer_ok = _35_337.defer_ok; smt_ok = _35_337.smt_ok; tcenv = _35_337.tcenv}))

let add_slack_mul = (fun ( slack ) ( wl ) -> (let _35_341 = wl
in {attempting = _35_341.attempting; deferred = _35_341.deferred; subst = _35_341.subst; ctr = _35_341.ctr; slack_vars = ((true, slack))::wl.slack_vars; defer_ok = _35_341.defer_ok; smt_ok = _35_341.smt_ok; tcenv = _35_341.tcenv}))

let add_slack_add = (fun ( slack ) ( wl ) -> (let _35_345 = wl
in {attempting = _35_345.attempting; deferred = _35_345.deferred; subst = _35_345.subst; ctr = _35_345.ctr; slack_vars = ((false, slack))::wl.slack_vars; defer_ok = _35_345.defer_ok; smt_ok = _35_345.smt_ok; tcenv = _35_345.tcenv}))

let giveup = (fun ( env ) ( reason ) ( prob ) -> (let _35_350 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_14874 = (prob_to_string env prob)
in (Support.Microsoft.FStar.Util.fprint2 "Failed %s:\n%s\n" reason _70_14874))
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
| UE (((u, _35_367), e)) -> begin
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
| _35_380 -> begin
None
end))))

let find_uvar_t = (fun ( uv ) ( s ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _35_15 ) -> (match (_35_15) with
| UT (((u, _35_386), t)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.equivalent uv u)) with
| true -> begin
Some (t)
end
| false -> begin
None
end)
end
| _35_392 -> begin
None
end))))

let find_uvar_e = (fun ( uv ) ( s ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _35_16 ) -> (match (_35_16) with
| UE (((u, _35_398), t)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.equivalent uv u)) with
| true -> begin
Some (t)
end
| false -> begin
None
end)
end
| _35_404 -> begin
None
end))))

let simplify_formula = (fun ( env ) ( f ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env f))

let norm_targ = (fun ( env ) ( t ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env t))

let norm_arg = (fun ( env ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _70_14905 = (let _70_14904 = (norm_targ env t)
in (Support.All.pipe_left (fun ( _70_14903 ) -> Support.Microsoft.FStar.Util.Inl (_70_14903)) _70_14904))
in (_70_14905, (Support.Prims.snd a)))
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
(let _70_14908 = (let _70_14907 = (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env v)
in (Support.All.pipe_left (fun ( _70_14906 ) -> Support.Microsoft.FStar.Util.Inr (_70_14906)) _70_14907))
in (_70_14908, (Support.Prims.snd a)))
end))

let whnf = (fun ( env ) ( t ) -> (let _70_14913 = (Microsoft_FStar_Tc_Normalize.whnf env t)
in (Support.All.pipe_right _70_14913 Microsoft_FStar_Absyn_Util.compress_typ)))

let sn = (fun ( env ) ( t ) -> (let _70_14918 = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::[]) env t)
in (Support.All.pipe_right _70_14918 Microsoft_FStar_Absyn_Util.compress_typ)))

let sn_binders = (fun ( env ) ( binders ) -> (Support.All.pipe_right binders (Support.List.map (fun ( _35_17 ) -> (match (_35_17) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _70_14924 = (let _70_14923 = (let _35_426 = a
in (let _70_14922 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env a.Microsoft_FStar_Absyn_Syntax.sort)
in {Microsoft_FStar_Absyn_Syntax.v = _35_426.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _70_14922; Microsoft_FStar_Absyn_Syntax.p = _35_426.Microsoft_FStar_Absyn_Syntax.p}))
in Support.Microsoft.FStar.Util.Inl (_70_14923))
in (_70_14924, imp))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _70_14927 = (let _70_14926 = (let _35_432 = x
in (let _70_14925 = (norm_targ env x.Microsoft_FStar_Absyn_Syntax.sort)
in {Microsoft_FStar_Absyn_Syntax.v = _35_432.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _70_14925; Microsoft_FStar_Absyn_Syntax.p = _35_432.Microsoft_FStar_Absyn_Syntax.p}))
in Support.Microsoft.FStar.Util.Inr (_70_14926))
in (_70_14927, imp))
end)))))

let whnf_k = (fun ( env ) ( k ) -> (let _70_14932 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.WHNF)::[]) env k)
in (Support.All.pipe_right _70_14932 Microsoft_FStar_Absyn_Util.compress_kind)))

let whnf_e = (fun ( env ) ( e ) -> (let _70_14937 = (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.WHNF)::[]) env e)
in (Support.All.pipe_right _70_14937 Microsoft_FStar_Absyn_Util.compress_exp)))

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
(let k = (let _70_14944 = (Microsoft_FStar_Absyn_Util.subst_of_list formals actuals)
in (Microsoft_FStar_Absyn_Util.subst_kind _70_14944 body))
in (compress_k env wl k))
end
| _35_455 -> begin
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
| _35_457 -> begin
k
end)))

let rec compress = (fun ( env ) ( wl ) ( t ) -> (let t = (let _70_14951 = (Microsoft_FStar_Absyn_Util.unmeta_typ t)
in (whnf env _70_14951))
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _35_464)) -> begin
(match ((find_uvar_t uv wl.subst)) with
| None -> begin
t
end
| Some (t) -> begin
(compress env wl t)
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _35_480)); Microsoft_FStar_Absyn_Syntax.tk = _35_477; Microsoft_FStar_Absyn_Syntax.pos = _35_475; Microsoft_FStar_Absyn_Syntax.fvs = _35_473; Microsoft_FStar_Absyn_Syntax.uvs = _35_471}, args)) -> begin
(match ((find_uvar_t uv wl.subst)) with
| Some (t') -> begin
(let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t', args) None t.Microsoft_FStar_Absyn_Syntax.pos)
in (compress env wl t))
end
| _35_491 -> begin
t
end)
end
| _35_493 -> begin
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
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _35_515)); Microsoft_FStar_Absyn_Syntax.tk = _35_512; Microsoft_FStar_Absyn_Syntax.pos = _35_510; Microsoft_FStar_Absyn_Syntax.fvs = _35_508; Microsoft_FStar_Absyn_Syntax.uvs = _35_506}, args)) -> begin
(match ((find_uvar_e uv wl.subst)) with
| None -> begin
e
end
| Some (e') -> begin
(let e' = (compress_e env wl e')
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e', args) None e.Microsoft_FStar_Absyn_Syntax.pos))
end)
end
| _35_527 -> begin
e
end)))

let normalize_refinement = (fun ( env ) ( wl ) ( t0 ) -> (let _70_14964 = (compress env wl t0)
in (Microsoft_FStar_Tc_Normalize.normalize_refinement env _70_14964)))

let base_and_refinement = (fun ( env ) ( wl ) ( t1 ) -> (let rec aux = (fun ( norm ) ( t1 ) -> (match (t1.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi)) -> begin
(match (norm) with
| true -> begin
(x.Microsoft_FStar_Absyn_Syntax.sort, Some ((x, phi)))
end
| false -> begin
(match ((normalize_refinement env wl t1)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi)); Microsoft_FStar_Absyn_Syntax.tk = _35_548; Microsoft_FStar_Absyn_Syntax.pos = _35_546; Microsoft_FStar_Absyn_Syntax.fvs = _35_544; Microsoft_FStar_Absyn_Syntax.uvs = _35_542} -> begin
(x.Microsoft_FStar_Absyn_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _70_14977 = (let _70_14976 = (Microsoft_FStar_Absyn_Print.typ_to_string tt)
in (let _70_14975 = (Microsoft_FStar_Absyn_Print.tag_of_typ tt)
in (Support.Microsoft.FStar.Util.format2 "impossible: Got %s ... %s\n" _70_14976 _70_14975)))
in (Support.All.failwith _70_14977))
end)
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (_)) -> begin
(match (norm) with
| true -> begin
(t1, None)
end
| false -> begin
(let _35_563 = (let _70_14978 = (normalize_refinement env wl t1)
in (aux true _70_14978))
in (match (_35_563) with
| (t2', refinement) -> begin
(match (refinement) with
| None -> begin
(t1, None)
end
| _35_566 -> begin
(t2', refinement)
end)
end))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
(t1, None)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _70_14981 = (let _70_14980 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _70_14979 = (Microsoft_FStar_Absyn_Print.tag_of_typ t1)
in (Support.Microsoft.FStar.Util.format2 "impossible (outer): Got %s ... %s\n" _70_14980 _70_14979)))
in (Support.All.failwith _70_14981))
end))
in (let _70_14982 = (compress env wl t1)
in (aux false _70_14982))))

let unrefine = (fun ( env ) ( t ) -> (let _70_14987 = (base_and_refinement env (empty_worklist env) t)
in (Support.All.pipe_right _70_14987 Support.Prims.fst)))

let trivial_refinement = (fun ( t ) -> (let _70_14989 = (Microsoft_FStar_Absyn_Util.gen_bvar_p t.Microsoft_FStar_Absyn_Syntax.pos t)
in (_70_14989, Microsoft_FStar_Absyn_Util.t_true)))

let as_refinement = (fun ( env ) ( wl ) ( t ) -> (let _35_597 = (base_and_refinement env wl t)
in (match (_35_597) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some ((x, phi)) -> begin
(x, phi)
end)
end)))

let force_refinement = (fun ( _35_605 ) -> (match (_35_605) with
| (t_base, refopt) -> begin
(let _35_613 = (match (refopt) with
| Some ((y, phi)) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_35_613) with
| (y, phi) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (y, phi) None t_base.Microsoft_FStar_Absyn_Syntax.pos)
end))
end))

let rec occurs = (fun ( env ) ( wl ) ( uk ) ( t ) -> (let uvs = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (let _70_15009 = (Support.All.pipe_right uvs.Microsoft_FStar_Absyn_Syntax.uvars_t Support.Microsoft.FStar.Util.set_elements)
in (Support.All.pipe_right _70_15009 (Support.Microsoft.FStar.Util.for_some (fun ( _35_624 ) -> (match (_35_624) with
| (uvt, _35_623) -> begin
(match ((find_uvar_t uvt wl.subst)) with
| None -> begin
(Support.Microsoft.FStar.Unionfind.equivalent uvt (Support.Prims.fst uk))
end
| Some (t) -> begin
(let t = (match ((Microsoft_FStar_Absyn_Util.compress_typ t)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((_35_637, t)); Microsoft_FStar_Absyn_Syntax.tk = _35_635; Microsoft_FStar_Absyn_Syntax.pos = _35_633; Microsoft_FStar_Absyn_Syntax.fvs = _35_631; Microsoft_FStar_Absyn_Syntax.uvs = _35_629} -> begin
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
(let _70_15022 = (let _70_15021 = (Microsoft_FStar_Absyn_Print.uvar_t_to_string uk)
in (let _70_15020 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (let _70_15019 = (let _70_15018 = (Support.All.pipe_right wl.subst (Support.List.map (uvi_to_string env)))
in (Support.All.pipe_right _70_15018 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format3 "occurs-check failed (%s occurs in %s) (with substitution %s)" _70_15021 _70_15020 _70_15019))))
in Some (_70_15022))
end)
in (occurs_ok, msg))))

let occurs_and_freevars_check = (fun ( env ) ( wl ) ( uk ) ( fvs ) ( t ) -> (let fvs_t = (Microsoft_FStar_Absyn_Util.freevars_typ t)
in (let _35_658 = (occurs_check env wl uk t)
in (match (_35_658) with
| (occurs_ok, msg) -> begin
(let _70_15033 = (Microsoft_FStar_Absyn_Util.fvs_included fvs_t fvs)
in (occurs_ok, _70_15033, (msg, fvs, fvs_t)))
end))))

let occurs_check_e = (fun ( env ) ( ut ) ( e ) -> (let uvs = (Microsoft_FStar_Absyn_Util.uvars_in_exp e)
in (let occurs_ok = (not ((Support.Microsoft.FStar.Util.set_mem ut uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)))
in (let msg = (match (occurs_ok) with
| true -> begin
None
end
| false -> begin
(let _70_15045 = (let _70_15044 = (Microsoft_FStar_Absyn_Print.uvar_e_to_string ut)
in (let _70_15043 = (let _70_15041 = (let _70_15040 = (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (Support.All.pipe_right _70_15040 (Support.List.map Microsoft_FStar_Absyn_Print.uvar_e_to_string)))
in (Support.All.pipe_right _70_15041 (Support.String.concat ", ")))
in (let _70_15042 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env e)
in (Support.Microsoft.FStar.Util.format3 "occurs-check failed (%s occurs in {%s} uvars of %s)" _70_15044 _70_15043 _70_15042))))
in Some (_70_15045))
end)
in (occurs_ok, msg)))))

let intersect_vars = (fun ( v1 ) ( v2 ) -> (let fvs1 = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders v1)
in (let fvs2 = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders v2)
in (let _70_15052 = (let _70_15051 = (Support.Microsoft.FStar.Util.set_intersect fvs1.Microsoft_FStar_Absyn_Syntax.ftvs fvs2.Microsoft_FStar_Absyn_Syntax.ftvs)
in (let _70_15050 = (Support.Microsoft.FStar.Util.set_intersect fvs1.Microsoft_FStar_Absyn_Syntax.fxvs fvs2.Microsoft_FStar_Absyn_Syntax.fxvs)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _70_15051; Microsoft_FStar_Absyn_Syntax.fxvs = _70_15050}))
in (Microsoft_FStar_Absyn_Syntax.binders_of_freevars _70_15052)))))

let binders_eq = (fun ( v1 ) ( v2 ) -> (((Support.List.length v1) = (Support.List.length v2)) && (Support.List.forall2 (fun ( ax1 ) ( ax2 ) -> (match (((Support.Prims.fst ax1), (Support.Prims.fst ax2))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(Microsoft_FStar_Absyn_Util.bvar_eq a b)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Microsoft_FStar_Absyn_Util.bvar_eq x y)
end
| _35_684 -> begin
false
end)) v1 v2)))

let pat_var_opt = (fun ( env ) ( seen ) ( arg ) -> (let hd = (norm_arg env arg)
in (match ((Support.All.pipe_left Support.Prims.fst hd)) with
| Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (a); Microsoft_FStar_Absyn_Syntax.tk = _35_696; Microsoft_FStar_Absyn_Syntax.pos = _35_694; Microsoft_FStar_Absyn_Syntax.fvs = _35_692; Microsoft_FStar_Absyn_Syntax.uvs = _35_690}) -> begin
(match ((Support.All.pipe_right seen (Support.Microsoft.FStar.Util.for_some (fun ( _35_18 ) -> (match (_35_18) with
| (Support.Microsoft.FStar.Util.Inl (b), _35_705) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq a.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v)
end
| _35_708 -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
Some ((Support.Microsoft.FStar.Util.Inl (a), (Support.Prims.snd hd)))
end)
end
| Support.Microsoft.FStar.Util.Inr ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_bvar (x); Microsoft_FStar_Absyn_Syntax.tk = _35_716; Microsoft_FStar_Absyn_Syntax.pos = _35_714; Microsoft_FStar_Absyn_Syntax.fvs = _35_712; Microsoft_FStar_Absyn_Syntax.uvs = _35_710}) -> begin
(match ((Support.All.pipe_right seen (Support.Microsoft.FStar.Util.for_some (fun ( _35_19 ) -> (match (_35_19) with
| (Support.Microsoft.FStar.Util.Inr (y), _35_725) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| _35_728 -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
Some ((Support.Microsoft.FStar.Util.Inr (x), (Support.Prims.snd hd)))
end)
end
| _35_730 -> begin
None
end)))

let rec pat_vars = (fun ( env ) ( seen ) ( args ) -> (match (args) with
| [] -> begin
Some ((Support.List.rev seen))
end
| hd::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(let _35_739 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_15068 = (Microsoft_FStar_Absyn_Print.arg_to_string hd)
in (Support.Microsoft.FStar.Util.fprint1 "Not a pattern: %s\n" _70_15068))
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
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)); Microsoft_FStar_Absyn_Syntax.tk = _35_755; Microsoft_FStar_Absyn_Syntax.pos = _35_753; Microsoft_FStar_Absyn_Syntax.fvs = _35_751; Microsoft_FStar_Absyn_Syntax.uvs = _35_749}, args)) -> begin
(t, uv, k, args)
end
| _35_765 -> begin
(Support.All.failwith "Not a flex-uvar")
end))

let destruct_flex_e = (fun ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, k)) -> begin
(e, uv, k, [])
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, k)); Microsoft_FStar_Absyn_Syntax.tk = _35_778; Microsoft_FStar_Absyn_Syntax.pos = _35_776; Microsoft_FStar_Absyn_Syntax.fvs = _35_774; Microsoft_FStar_Absyn_Syntax.uvs = _35_772}, args)) -> begin
(e, uv, k, args)
end
| _35_788 -> begin
(Support.All.failwith "Not a flex-uvar")
end))

let destruct_flex_pattern = (fun ( env ) ( t ) -> (let _35_795 = (destruct_flex_t t)
in (match (_35_795) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _35_799 -> begin
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
| _35_803 -> begin
HeadMatch
end))

let rec head_matches = (fun ( t1 ) ( t2 ) -> (match ((let _70_15085 = (let _70_15082 = (Microsoft_FStar_Absyn_Util.unmeta_typ t1)
in _70_15082.Microsoft_FStar_Absyn_Syntax.n)
in (let _70_15084 = (let _70_15083 = (Microsoft_FStar_Absyn_Util.unmeta_typ t2)
in _70_15083.Microsoft_FStar_Absyn_Syntax.n)
in (_70_15085, _70_15084)))) with
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
| (Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _35_832)), Microsoft_FStar_Absyn_Syntax.Typ_refine ((y, _35_837))) -> begin
(let _70_15086 = (head_matches x.Microsoft_FStar_Absyn_Syntax.sort y.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.All.pipe_right _70_15086 head_match))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _35_843)), _35_847) -> begin
(let _70_15087 = (head_matches x.Microsoft_FStar_Absyn_Syntax.sort t2)
in (Support.All.pipe_right _70_15087 head_match))
end
| (_35_850, Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _35_853))) -> begin
(let _70_15088 = (head_matches t1 x.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.All.pipe_right _70_15088 head_match))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_35_858), Microsoft_FStar_Absyn_Syntax.Typ_fun (_35_861)) -> begin
HeadMatch
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app ((head, _35_866)), Microsoft_FStar_Absyn_Syntax.Typ_app ((head', _35_871))) -> begin
(head_matches head head')
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app ((head, _35_877)), _35_881) -> begin
(head_matches head t2)
end
| (_35_884, Microsoft_FStar_Absyn_Syntax.Typ_app ((head, _35_887))) -> begin
(head_matches t1 head)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _35_893)), Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv', _35_898))) -> begin
(match ((Support.Microsoft.FStar.Unionfind.equivalent uv uv')) with
| true -> begin
FullMatch
end
| false -> begin
MisMatch
end)
end
| (_35_903, Microsoft_FStar_Absyn_Syntax.Typ_lam (_35_905)) -> begin
HeadMatch
end
| _35_909 -> begin
MisMatch
end))

let head_matches_delta = (fun ( env ) ( wl ) ( t1 ) ( t2 ) -> (let success = (fun ( d ) ( r ) ( t1 ) ( t2 ) -> (r, (match (d) with
| true -> begin
Some ((t1, t2))
end
| false -> begin
None
end)))
in (let fail = (fun ( _35_920 ) -> (match (()) with
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

let decompose_binder = (fun ( bs ) ( v_ktec ) ( rebuild_base ) -> (let fail = (fun ( _35_934 ) -> (match (()) with
| () -> begin
(Support.All.failwith "Bad reconstruction")
end))
in (let rebuild = (fun ( ktecs ) -> (let rec aux = (fun ( new_bs ) ( bs ) ( ktecs ) -> (match ((bs, ktecs)) with
| ([], ktec::[]) -> begin
(rebuild_base (Support.List.rev new_bs) ktec)
end
| ((Support.Microsoft.FStar.Util.Inl (a), imp)::rest, Microsoft_FStar_Absyn_Syntax.K (k)::rest') -> begin
(aux (((Support.Microsoft.FStar.Util.Inl ((let _35_956 = a
in {Microsoft_FStar_Absyn_Syntax.v = _35_956.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _35_956.Microsoft_FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| ((Support.Microsoft.FStar.Util.Inr (x), imp)::rest, Microsoft_FStar_Absyn_Syntax.T ((t, _35_967))::rest') -> begin
(aux (((Support.Microsoft.FStar.Util.Inr ((let _35_972 = x
in {Microsoft_FStar_Absyn_Syntax.v = _35_972.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _35_972.Microsoft_FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| _35_975 -> begin
(fail ())
end))
in (aux [] bs ktecs)))
in (let rec mk_b_ktecs = (fun ( _35_979 ) ( _35_21 ) -> (match (_35_979) with
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
in (let _70_15142 = (mk_b_ktecs ([], []) bs)
in (rebuild, _70_15142))))))

let rec decompose_kind = (fun ( env ) ( k ) -> (let fail = (fun ( _35_998 ) -> (match (()) with
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
| _35_1006 -> begin
(fail ())
end))
in (rebuild, []))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(decompose_binder bs (Microsoft_FStar_Absyn_Syntax.K (k)) (fun ( bs ) ( _35_23 ) -> (match (_35_23) with
| Microsoft_FStar_Absyn_Syntax.K (k) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) k0.Microsoft_FStar_Absyn_Syntax.pos)
end
| _35_1017 -> begin
(fail ())
end)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_35_1019, k)) -> begin
(decompose_kind env k)
end
| _35_1024 -> begin
(Support.All.failwith "Impossible")
end)))))

let rec decompose_typ = (fun ( env ) ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.unmeta_typ t)
in (let matches = (fun ( t' ) -> ((head_matches t t') <> MisMatch))
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((hd, args)) -> begin
(let rebuild = (fun ( args' ) -> (let args = (Support.List.map2 (fun ( x ) ( y ) -> (match ((x, y)) with
| ((Support.Microsoft.FStar.Util.Inl (_35_1039), imp), Microsoft_FStar_Absyn_Syntax.T ((t, _35_1045))) -> begin
(Support.Microsoft.FStar.Util.Inl (t), imp)
end
| ((Support.Microsoft.FStar.Util.Inr (_35_1050), imp), Microsoft_FStar_Absyn_Syntax.E (e)) -> begin
(Support.Microsoft.FStar.Util.Inr (e), imp)
end
| _35_1058 -> begin
(Support.All.failwith "Bad reconstruction")
end)) args args')
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (hd, args) None t.Microsoft_FStar_Absyn_Syntax.pos)))
in (let b_ktecs = (Support.All.pipe_right args (Support.List.map (fun ( _35_24 ) -> (match (_35_24) with
| (Support.Microsoft.FStar.Util.Inl (t), _35_1064) -> begin
(None, INVARIANT, Microsoft_FStar_Absyn_Syntax.T ((t, None)))
end
| (Support.Microsoft.FStar.Util.Inr (e), _35_1069) -> begin
(None, INVARIANT, Microsoft_FStar_Absyn_Syntax.E (e))
end))))
in (rebuild, matches, b_ktecs)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let _35_1084 = (decompose_binder bs (Microsoft_FStar_Absyn_Syntax.C (c)) (fun ( bs ) ( _35_25 ) -> (match (_35_25) with
| Microsoft_FStar_Absyn_Syntax.C (c) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.Microsoft_FStar_Absyn_Syntax.pos)
end
| _35_1081 -> begin
(Support.All.failwith "Bad reconstruction")
end)))
in (match (_35_1084) with
| (rebuild, b_ktecs) -> begin
(rebuild, matches, b_ktecs)
end))
end
| _35_1086 -> begin
(let rebuild = (fun ( _35_26 ) -> (match (_35_26) with
| [] -> begin
t
end
| _35_1090 -> begin
(Support.All.failwith "Bad reconstruction")
end))
in (rebuild, (fun ( t ) -> true), []))
end))))

let un_T = (fun ( _35_27 ) -> (match (_35_27) with
| Microsoft_FStar_Absyn_Syntax.T ((x, _35_1096)) -> begin
x
end
| _35_1100 -> begin
(Support.All.failwith "impossible")
end))

let arg_of_ktec = (fun ( _35_28 ) -> (match (_35_28) with
| Microsoft_FStar_Absyn_Syntax.T ((t, _35_1104)) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| Microsoft_FStar_Absyn_Syntax.E (e) -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end
| _35_1110 -> begin
(Support.All.failwith "Impossible")
end))

let imitation_sub_probs = (fun ( orig ) ( env ) ( scope ) ( ps ) ( qs ) -> (let r = (p_loc orig)
in (let rel = (p_rel orig)
in (let sub_prob = (fun ( scope ) ( args ) ( q ) -> (match (q) with
| (_35_1123, variance, Microsoft_FStar_Absyn_Syntax.K (ki)) -> begin
(let _35_1130 = (new_kvar r scope)
in (match (_35_1130) with
| (gi_xs, gi) -> begin
(let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (gi, args) r)
in (let _70_15225 = (let _70_15224 = (mk_problem scope orig gi_ps (vary_rel rel variance) ki None "kind subterm")
in (Support.All.pipe_left (fun ( _70_15223 ) -> KProb (_70_15223)) _70_15224))
in (Microsoft_FStar_Absyn_Syntax.K (gi_xs), _70_15225)))
end))
end
| (_35_1133, variance, Microsoft_FStar_Absyn_Syntax.T ((ti, kopt))) -> begin
(let k = (match (kopt) with
| Some (k) -> begin
k
end
| None -> begin
(Microsoft_FStar_Tc_Recheck.recompute_kind ti)
end)
in (let _35_1146 = (new_tvar r scope k)
in (match (_35_1146) with
| (gi_xs, gi) -> begin
(let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (gi, args) None r)
in (let _70_15228 = (let _70_15227 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (Support.All.pipe_left (fun ( _70_15226 ) -> TProb (_70_15226)) _70_15227))
in (Microsoft_FStar_Absyn_Syntax.T ((gi_xs, Some (k))), _70_15228)))
end)))
end
| (_35_1149, variance, Microsoft_FStar_Absyn_Syntax.E (ei)) -> begin
(let t = (Microsoft_FStar_Tc_Recheck.recompute_typ ei)
in (let _35_1157 = (new_evar r scope t)
in (match (_35_1157) with
| (gi_xs, gi) -> begin
(let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (gi, args) (Some (t)) r)
in (let _70_15231 = (let _70_15230 = (mk_problem scope orig gi_ps (vary_rel rel variance) ei None "expression subterm")
in (Support.All.pipe_left (fun ( _70_15229 ) -> EProb (_70_15229)) _70_15230))
in (Microsoft_FStar_Absyn_Syntax.E (gi_xs), _70_15231)))
end)))
end
| (_35_1160, _35_1162, Microsoft_FStar_Absyn_Syntax.C (_35_1164)) -> begin
(Support.All.failwith "impos")
end))
in (let rec aux = (fun ( scope ) ( args ) ( qs ) -> (match (qs) with
| [] -> begin
([], [], Microsoft_FStar_Absyn_Util.t_true)
end
| q::qs -> begin
(let _35_1240 = (match (q) with
| (bopt, variance, Microsoft_FStar_Absyn_Syntax.C ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Total (ti); Microsoft_FStar_Absyn_Syntax.tk = _35_1184; Microsoft_FStar_Absyn_Syntax.pos = _35_1182; Microsoft_FStar_Absyn_Syntax.fvs = _35_1180; Microsoft_FStar_Absyn_Syntax.uvs = _35_1178})) -> begin
(match ((sub_prob scope args (bopt, variance, Microsoft_FStar_Absyn_Syntax.T ((ti, Some (Microsoft_FStar_Absyn_Syntax.ktype)))))) with
| (Microsoft_FStar_Absyn_Syntax.T ((gi_xs, _35_1192)), prob) -> begin
(let _70_15240 = (let _70_15239 = (Microsoft_FStar_Absyn_Syntax.mk_Total gi_xs)
in (Support.All.pipe_left (fun ( _70_15238 ) -> Microsoft_FStar_Absyn_Syntax.C (_70_15238)) _70_15239))
in (_70_15240, (prob)::[]))
end
| _35_1198 -> begin
(Support.All.failwith "impossible")
end)
end
| (_35_1200, _35_1202, Microsoft_FStar_Absyn_Syntax.C ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp (c); Microsoft_FStar_Absyn_Syntax.tk = _35_1210; Microsoft_FStar_Absyn_Syntax.pos = _35_1208; Microsoft_FStar_Absyn_Syntax.fvs = _35_1206; Microsoft_FStar_Absyn_Syntax.uvs = _35_1204})) -> begin
(let components = (Support.All.pipe_right c.Microsoft_FStar_Absyn_Syntax.effect_args (Support.List.map (fun ( _35_29 ) -> (match (_35_29) with
| (Support.Microsoft.FStar.Util.Inl (t), _35_1220) -> begin
(None, INVARIANT, Microsoft_FStar_Absyn_Syntax.T ((t, None)))
end
| (Support.Microsoft.FStar.Util.Inr (e), _35_1225) -> begin
(None, INVARIANT, Microsoft_FStar_Absyn_Syntax.E (e))
end))))
in (let components = ((None, COVARIANT, Microsoft_FStar_Absyn_Syntax.T ((c.Microsoft_FStar_Absyn_Syntax.result_typ, Some (Microsoft_FStar_Absyn_Syntax.ktype)))))::components
in (let _35_1231 = (let _70_15242 = (Support.List.map (sub_prob scope args) components)
in (Support.All.pipe_right _70_15242 Support.List.unzip))
in (match (_35_1231) with
| (ktecs, sub_probs) -> begin
(let gi_xs = (let _70_15247 = (let _70_15246 = (let _70_15243 = (Support.List.hd ktecs)
in (Support.All.pipe_right _70_15243 un_T))
in (let _70_15245 = (let _70_15244 = (Support.List.tl ktecs)
in (Support.All.pipe_right _70_15244 (Support.List.map arg_of_ktec)))
in {Microsoft_FStar_Absyn_Syntax.effect_name = c.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _70_15246; Microsoft_FStar_Absyn_Syntax.effect_args = _70_15245; Microsoft_FStar_Absyn_Syntax.flags = c.Microsoft_FStar_Absyn_Syntax.flags}))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp _70_15247))
in (Microsoft_FStar_Absyn_Syntax.C (gi_xs), sub_probs))
end))))
end
| _35_1234 -> begin
(let _35_1237 = (sub_prob scope args q)
in (match (_35_1237) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_35_1240) with
| (ktec, probs) -> begin
(let _35_1253 = (match (q) with
| (Some (b), _35_1244, _35_1246) -> begin
(let _70_15249 = (let _70_15248 = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder b)
in (_70_15248)::args)
in (Some (b), (b)::scope, _70_15249))
end
| _35_1249 -> begin
(None, scope, args)
end)
in (match (_35_1253) with
| (bopt, scope, args) -> begin
(let _35_1257 = (aux scope args qs)
in (match (_35_1257) with
| (sub_probs, ktecs, f) -> begin
(let f = (match (bopt) with
| None -> begin
(let _70_15252 = (let _70_15251 = (Support.All.pipe_right probs (Support.List.map (fun ( prob ) -> (Support.All.pipe_right (p_guard prob) Support.Prims.fst))))
in (f)::_70_15251)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _70_15252))
end
| Some (b) -> begin
(let _70_15256 = (let _70_15255 = (Microsoft_FStar_Absyn_Util.close_forall ((b)::[]) f)
in (let _70_15254 = (Support.All.pipe_right probs (Support.List.map (fun ( prob ) -> (Support.All.pipe_right (p_guard prob) Support.Prims.fst))))
in (_70_15255)::_70_15254))
in (Microsoft_FStar_Absyn_Util.mk_conj_l _70_15256))
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

let fix_slack_uv = (fun ( _35_1270 ) ( mul ) -> (match (_35_1270) with
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

let fix_slack_vars = (fun ( slack ) -> (Support.All.pipe_right slack (Support.List.iter (fun ( _35_1276 ) -> (match (_35_1276) with
| (mul, s) -> begin
(match ((let _70_15274 = (Microsoft_FStar_Absyn_Util.compress_typ s)
in _70_15274.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(fix_slack_uv (uv, k) mul)
end
| _35_1282 -> begin
()
end)
end)))))

let fix_slack = (fun ( slack ) -> (let _35_1290 = (Support.All.pipe_left destruct_flex_t (Support.Prims.snd slack.lower))
in (match (_35_1290) with
| (_35_1285, ul, kl, _35_1289) -> begin
(let _35_1297 = (Support.All.pipe_left destruct_flex_t (Support.Prims.snd slack.upper))
in (match (_35_1297) with
| (_35_1292, uh, kh, _35_1296) -> begin
(let _35_1298 = (fix_slack_uv (ul, kl) false)
in (let _35_1300 = (fix_slack_uv (uh, kh) true)
in (let _35_1302 = (Support.ST.op_Colon_Equals slack.flag true)
in (Microsoft_FStar_Absyn_Util.mk_conj (Support.Prims.fst slack.lower) (Support.Prims.fst slack.upper)))))
end))
end)))

let new_slack_var = (fun ( env ) ( slack ) -> (let xs = (let _70_15282 = (let _70_15281 = (destruct_flex_pattern env (Support.Prims.snd slack.lower))
in (Support.All.pipe_right _70_15281 Support.Prims.snd))
in (Support.All.pipe_right _70_15282 Support.Microsoft.FStar.Util.must))
in (let _70_15283 = (new_tvar (Support.Prims.fst slack.lower).Microsoft_FStar_Absyn_Syntax.pos xs Microsoft_FStar_Absyn_Syntax.ktype)
in (_70_15283, xs))))

let new_slack_formula = (fun ( p ) ( env ) ( wl ) ( xs ) ( low ) ( high ) -> (let _35_1315 = (new_tvar p xs Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_35_1315) with
| (low_var, uv1) -> begin
(let wl = (add_slack_add uv1 wl)
in (let _35_1319 = (new_tvar p xs Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_35_1319) with
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
in (let _70_15293 = (let _70_15292 = (let _70_15291 = (let _70_15290 = (Support.Microsoft.FStar.Util.mk_ref false)
in (low, high, _70_15290))
in Microsoft_FStar_Absyn_Syntax.Meta_slack_formula (_70_15291))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _70_15292))
in (_70_15293, wl)))))
end)))
end)))

let destruct_slack = (fun ( env ) ( wl ) ( phi ) -> (let rec destruct = (fun ( conn_lid ) ( mk_conn ) ( phi ) -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _35_1343; Microsoft_FStar_Absyn_Syntax.pos = _35_1341; Microsoft_FStar_Absyn_Syntax.fvs = _35_1339; Microsoft_FStar_Absyn_Syntax.uvs = _35_1337}, (Support.Microsoft.FStar.Util.Inl (lhs), _35_1355)::(Support.Microsoft.FStar.Util.Inl (rhs), _35_1350)::[])) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v conn_lid) -> begin
(let rhs = (compress env wl rhs)
in (match (rhs.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
Some ((lhs, rhs))
end
| _35_1381 -> begin
(match ((destruct conn_lid mk_conn rhs)) with
| None -> begin
None
end
| Some ((rest, uvar)) -> begin
(let _70_15317 = (let _70_15316 = (mk_conn lhs rest)
in (_70_15316, uvar))
in Some (_70_15317))
end)
end))
end
| _35_1388 -> begin
None
end))
in (let phi = (Microsoft_FStar_Absyn_Util.compress_typ phi)
in (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((phi1, phi2, flag))) -> begin
(match ((Support.ST.read flag)) with
| true -> begin
(let _70_15318 = (Microsoft_FStar_Absyn_Util.unmeta_typ phi)
in Support.Microsoft.FStar.Util.Inl (_70_15318))
end
| false -> begin
(let low = (let _70_15319 = (compress env wl phi1)
in (Support.All.pipe_left (destruct Microsoft_FStar_Absyn_Const.or_lid Microsoft_FStar_Absyn_Util.mk_disj) _70_15319))
in (let hi = (let _70_15320 = (compress env wl phi2)
in (Support.All.pipe_left (destruct Microsoft_FStar_Absyn_Const.and_lid Microsoft_FStar_Absyn_Util.mk_disj) _70_15320))
in (match ((low, hi)) with
| (None, None) -> begin
(let _35_1401 = (Support.ST.op_Colon_Equals flag true)
in (let _70_15321 = (Microsoft_FStar_Absyn_Util.unmeta_typ phi)
in Support.Microsoft.FStar.Util.Inl (_70_15321)))
end
| ((Some (_), None)) | ((None, Some (_))) -> begin
(Support.All.failwith "Impossible")
end
| (Some (l), Some (u)) -> begin
Support.Microsoft.FStar.Util.Inr ({lower = l; upper = u; flag = flag})
end)))
end)
end
| _35_1419 -> begin
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
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar ((u1, _35_1436)), Microsoft_FStar_Absyn_Syntax.Typ_uvar ((u2, _35_1441))) -> begin
(Support.Microsoft.FStar.Unionfind.equivalent u1 u2)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app ((h1, args1)), Microsoft_FStar_Absyn_Syntax.Typ_app ((h2, args2))) -> begin
((eq_typ h1 h2) && (eq_args args1 args2))
end
| _35_1455 -> begin
false
end))))
and eq_exp = (fun ( e1 ) ( e2 ) -> (let e1 = (Microsoft_FStar_Absyn_Util.compress_exp e1)
in (let e2 = (Microsoft_FStar_Absyn_Util.compress_exp e2)
in (match ((e1.Microsoft_FStar_Absyn_Syntax.n, e2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (a), Microsoft_FStar_Absyn_Syntax.Exp_bvar (b)) -> begin
(Microsoft_FStar_Absyn_Util.bvar_eq a b)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _35_1467)), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((g, _35_1472))) -> begin
(Microsoft_FStar_Absyn_Util.fvar_eq f g)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_constant (c), Microsoft_FStar_Absyn_Syntax.Exp_constant (d)) -> begin
(c = d)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((h1, args1)), Microsoft_FStar_Absyn_Syntax.Exp_app ((h2, args2))) -> begin
((eq_exp h1 h2) && (eq_args args1 args2))
end
| _35_1491 -> begin
false
end))))
and eq_args = (fun ( a1 ) ( a2 ) -> (match (((Support.List.length a1) = (Support.List.length a2))) with
| true -> begin
(Support.List.forall2 (fun ( a1 ) ( a2 ) -> (match ((a1, a2)) with
| ((Support.Microsoft.FStar.Util.Inl (t), _35_1499), (Support.Microsoft.FStar.Util.Inl (s), _35_1504)) -> begin
(eq_typ t s)
end
| ((Support.Microsoft.FStar.Util.Inr (e), _35_1510), (Support.Microsoft.FStar.Util.Inr (f), _35_1515)) -> begin
(eq_exp e f)
end
| _35_1519 -> begin
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
(let _70_15351 = (let _35_1524 = p
in (let _70_15349 = (compress_k wl.tcenv wl p.lhs)
in (let _70_15348 = (compress_k wl.tcenv wl p.rhs)
in {lhs = _70_15349; relation = _35_1524.relation; rhs = _70_15348; element = _35_1524.element; logical_guard = _35_1524.logical_guard; scope = _35_1524.scope; reason = _35_1524.reason; loc = _35_1524.loc; rank = _35_1524.rank})))
in (Support.All.pipe_right _70_15351 (fun ( _70_15350 ) -> KProb (_70_15350))))
end
| TProb (p) -> begin
(let _70_15355 = (let _35_1528 = p
in (let _70_15353 = (compress wl.tcenv wl p.lhs)
in (let _70_15352 = (compress wl.tcenv wl p.rhs)
in {lhs = _70_15353; relation = _35_1528.relation; rhs = _70_15352; element = _35_1528.element; logical_guard = _35_1528.logical_guard; scope = _35_1528.scope; reason = _35_1528.reason; loc = _35_1528.loc; rank = _35_1528.rank})))
in (Support.All.pipe_right _70_15355 (fun ( _70_15354 ) -> TProb (_70_15354))))
end
| EProb (p) -> begin
(let _70_15359 = (let _35_1532 = p
in (let _70_15357 = (compress_e wl.tcenv wl p.lhs)
in (let _70_15356 = (compress_e wl.tcenv wl p.rhs)
in {lhs = _70_15357; relation = _35_1532.relation; rhs = _70_15356; element = _35_1532.element; logical_guard = _35_1532.logical_guard; scope = _35_1532.scope; reason = _35_1532.reason; loc = _35_1532.loc; rank = _35_1532.rank})))
in (Support.All.pipe_right _70_15359 (fun ( _70_15358 ) -> EProb (_70_15358))))
end
| CProb (_35_1535) -> begin
p
end))

let rank = (fun ( wl ) ( prob ) -> (let prob = (let _70_15364 = (compress_prob wl prob)
in (Support.All.pipe_right _70_15364 maybe_invert_p))
in (match (prob) with
| KProb (kp) -> begin
(let rank = (match ((kp.lhs.Microsoft_FStar_Absyn_Syntax.n, kp.rhs.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_35_1543), Microsoft_FStar_Absyn_Syntax.Kind_uvar (_35_1546)) -> begin
flex_flex
end
| (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_35_1550), _35_1553) -> begin
(match ((kp.relation = EQ)) with
| true -> begin
flex_rigid_eq
end
| false -> begin
flex_rigid
end)
end
| (_35_1556, Microsoft_FStar_Absyn_Syntax.Kind_uvar (_35_1558)) -> begin
(match ((kp.relation = EQ)) with
| true -> begin
flex_rigid_eq
end
| false -> begin
rigid_flex
end)
end
| (_35_1562, _35_1564) -> begin
rigid_rigid
end)
in (let _70_15366 = (Support.All.pipe_right (let _35_1567 = kp
in {lhs = _35_1567.lhs; relation = _35_1567.relation; rhs = _35_1567.rhs; element = _35_1567.element; logical_guard = _35_1567.logical_guard; scope = _35_1567.scope; reason = _35_1567.reason; loc = _35_1567.loc; rank = Some (rank)}) (fun ( _70_15365 ) -> KProb (_70_15365)))
in (rank, _70_15366)))
end
| TProb (tp) -> begin
(let _35_1574 = (Microsoft_FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_35_1574) with
| (lh, _35_1573) -> begin
(let _35_1578 = (Microsoft_FStar_Absyn_Util.head_and_args tp.rhs)
in (match (_35_1578) with
| (rh, _35_1577) -> begin
(let _35_1634 = (match ((lh.Microsoft_FStar_Absyn_Syntax.n, rh.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_35_1580), Microsoft_FStar_Absyn_Syntax.Typ_uvar (_35_1583)) -> begin
(flex_flex, tp)
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_uvar (_))) when (tp.relation = EQ) -> begin
(flex_rigid_eq, tp)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_35_1599), _35_1602) -> begin
(let _35_1606 = (base_and_refinement wl.tcenv wl tp.rhs)
in (match (_35_1606) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _35_1609 -> begin
(let rank = (match ((is_top_level_prob prob)) with
| true -> begin
flex_refine
end
| false -> begin
flex_refine_inner
end)
in (let _70_15368 = (let _35_1611 = tp
in (let _70_15367 = (force_refinement (b, ref_opt))
in {lhs = _35_1611.lhs; relation = _35_1611.relation; rhs = _70_15367; element = _35_1611.element; logical_guard = _35_1611.logical_guard; scope = _35_1611.scope; reason = _35_1611.reason; loc = _35_1611.loc; rank = _35_1611.rank}))
in (rank, _70_15368)))
end)
end))
end
| (_35_1614, Microsoft_FStar_Absyn_Syntax.Typ_uvar (_35_1616)) -> begin
(let _35_1621 = (base_and_refinement wl.tcenv wl tp.lhs)
in (match (_35_1621) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _35_1624 -> begin
(let _70_15370 = (let _35_1625 = tp
in (let _70_15369 = (force_refinement (b, ref_opt))
in {lhs = _70_15369; relation = _35_1625.relation; rhs = _35_1625.rhs; element = _35_1625.element; logical_guard = _35_1625.logical_guard; scope = _35_1625.scope; reason = _35_1625.reason; loc = _35_1625.loc; rank = _35_1625.rank}))
in (refine_flex, _70_15370))
end)
end))
end
| (_35_1628, _35_1630) -> begin
(rigid_rigid, tp)
end)
in (match (_35_1634) with
| (rank, tp) -> begin
(let _70_15372 = (Support.All.pipe_right (let _35_1635 = tp
in {lhs = _35_1635.lhs; relation = _35_1635.relation; rhs = _35_1635.rhs; element = _35_1635.element; logical_guard = _35_1635.logical_guard; scope = _35_1635.scope; reason = _35_1635.reason; loc = _35_1635.loc; rank = Some (rank)}) (fun ( _70_15371 ) -> TProb (_70_15371)))
in (rank, _70_15372))
end))
end))
end))
end
| EProb (ep) -> begin
(let _35_1642 = (Microsoft_FStar_Absyn_Util.head_and_args_e ep.lhs)
in (match (_35_1642) with
| (lh, _35_1641) -> begin
(let _35_1646 = (Microsoft_FStar_Absyn_Util.head_and_args_e ep.rhs)
in (match (_35_1646) with
| (rh, _35_1645) -> begin
(let rank = (match ((lh.Microsoft_FStar_Absyn_Syntax.n, rh.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_35_1648), Microsoft_FStar_Absyn_Syntax.Exp_uvar (_35_1651)) -> begin
flex_flex
end
| ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) -> begin
flex_rigid_eq
end
| (_35_1667, _35_1669) -> begin
rigid_rigid
end)
in (let _70_15374 = (Support.All.pipe_right (let _35_1672 = ep
in {lhs = _35_1672.lhs; relation = _35_1672.relation; rhs = _35_1672.rhs; element = _35_1672.element; logical_guard = _35_1672.logical_guard; scope = _35_1672.scope; reason = _35_1672.reason; loc = _35_1672.loc; rank = Some (rank)}) (fun ( _70_15373 ) -> EProb (_70_15373)))
in (rank, _70_15374)))
end))
end))
end
| CProb (cp) -> begin
(let _70_15376 = (Support.All.pipe_right (let _35_1676 = cp
in {lhs = _35_1676.lhs; relation = _35_1676.relation; rhs = _35_1676.rhs; element = _35_1676.element; logical_guard = _35_1676.logical_guard; scope = _35_1676.scope; reason = _35_1676.reason; loc = _35_1676.loc; rank = Some (rigid_rigid)}) (fun ( _70_15375 ) -> CProb (_70_15375)))
in (rigid_rigid, _70_15376))
end)))

let next_prob = (fun ( wl ) -> (let rec aux = (fun ( _35_1683 ) ( probs ) -> (match (_35_1683) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(let _35_1691 = (rank wl hd)
in (match (_35_1691) with
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

let rec solve_flex_rigid_join = (fun ( env ) ( tp ) ( wl ) -> (let _35_1702 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_15426 = (prob_to_string env (TProb (tp)))
in (Support.Microsoft.FStar.Util.fprint1 "Trying to solve by joining refinements:%s\n" _70_15426))
end
| false -> begin
()
end)
in (let _35_1706 = (Microsoft_FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_35_1706) with
| (u, args) -> begin
(let _35_1712 = (0, 1, 2, 3, 4)
in (match (_35_1712) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(let max = (fun ( i ) ( j ) -> (match ((i < j)) with
| true -> begin
j
end
| false -> begin
i
end))
in (let base_types_match = (fun ( t1 ) ( t2 ) -> (let _35_1721 = (Microsoft_FStar_Absyn_Util.head_and_args t1)
in (match (_35_1721) with
| (h1, args1) -> begin
(let _35_1725 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (match (_35_1725) with
| (h2, _35_1724) -> begin
(match ((h1.Microsoft_FStar_Absyn_Syntax.n, h2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_const (tc1), Microsoft_FStar_Absyn_Syntax.Typ_const (tc2)) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals tc1.Microsoft_FStar_Absyn_Syntax.v tc2.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(match (((Support.List.length args1) = 0)) with
| true -> begin
Some ([])
end
| false -> begin
(let _70_15438 = (let _70_15437 = (let _70_15436 = (new_problem env t1 EQ t2 None t1.Microsoft_FStar_Absyn_Syntax.pos "joining refinements")
in (Support.All.pipe_left (fun ( _70_15435 ) -> TProb (_70_15435)) _70_15436))
in (_70_15437)::[])
in Some (_70_15438))
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
| _35_1737 -> begin
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
(let phi2 = (let _70_15445 = (let _70_15444 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (let _70_15443 = (Microsoft_FStar_Absyn_Syntax.v_binder y)
in (Microsoft_FStar_Absyn_Util.mk_subst_one_binder _70_15444 _70_15443)))
in (Microsoft_FStar_Absyn_Util.subst_typ _70_15445 phi2))
in (let _70_15449 = (let _70_15448 = (let _70_15447 = (let _70_15446 = (Microsoft_FStar_Absyn_Util.mk_conj phi1 phi2)
in (x, _70_15446))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _70_15447 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) t1.Microsoft_FStar_Absyn_Syntax.pos))
in (_70_15448, m))
in Some (_70_15449)))
end))
end
| (_35_1756, Microsoft_FStar_Absyn_Syntax.Typ_refine ((y, _35_1759))) -> begin
(let m = (base_types_match t1 y.Microsoft_FStar_Absyn_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _35_1769)), _35_1773) -> begin
(let m = (base_types_match x.Microsoft_FStar_Absyn_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _35_1780 -> begin
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
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _35_1788)) -> begin
(let _35_1813 = (Support.All.pipe_right wl.attempting (Support.List.partition (fun ( _35_30 ) -> (match (_35_30) with
| TProb (tp) -> begin
(match (tp.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(let _35_1799 = (Microsoft_FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_35_1799) with
| (u', _35_1798) -> begin
(match ((let _70_15451 = (compress env wl u')
in _70_15451.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv', _35_1802)) -> begin
(Support.Microsoft.FStar.Unionfind.equivalent uv uv')
end
| _35_1806 -> begin
false
end)
end))
end
| _35_1808 -> begin
false
end)
end
| _35_1810 -> begin
false
end))))
in (match (_35_1813) with
| (upper_bounds, rest) -> begin
(let rec make_upper_bound = (fun ( _35_1817 ) ( tps ) -> (match (_35_1817) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| TProb (hd)::tl -> begin
(match ((let _70_15456 = (compress env wl hd.rhs)
in (conjoin bound _70_15456))) with
| Some ((bound, sub)) -> begin
(make_upper_bound (bound, (Support.List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _35_1830 -> begin
None
end)
end))
in (match ((let _70_15458 = (let _70_15457 = (compress env wl tp.rhs)
in (_70_15457, []))
in (make_upper_bound _70_15458 upper_bounds))) with
| None -> begin
(let _35_1832 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
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
in (match ((solve_t env eq_prob (let _35_1839 = wl
in {attempting = sub_probs; deferred = _35_1839.deferred; subst = _35_1839.subst; ctr = _35_1839.ctr; slack_vars = _35_1839.slack_vars; defer_ok = _35_1839.defer_ok; smt_ok = _35_1839.smt_ok; tcenv = _35_1839.tcenv}))) with
| Success ((subst, _35_1843)) -> begin
(let wl = (let _35_1846 = wl
in {attempting = rest; deferred = _35_1846.deferred; subst = []; ctr = _35_1846.ctr; slack_vars = _35_1846.slack_vars; defer_ok = _35_1846.defer_ok; smt_ok = _35_1846.smt_ok; tcenv = _35_1846.tcenv})
in (let wl = (solve_prob (TProb (tp)) None subst wl)
in (let _35_1852 = (Support.List.fold_left (fun ( wl ) ( p ) -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _35_1855 -> begin
None
end))
end))
end))
end
| _35_1857 -> begin
(Support.All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve = (fun ( env ) ( probs ) -> (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(let probs = (let _35_1865 = probs
in {attempting = tl; deferred = _35_1865.deferred; subst = _35_1865.subst; ctr = _35_1865.ctr; slack_vars = _35_1865.slack_vars; defer_ok = _35_1865.defer_ok; smt_ok = _35_1865.smt_ok; tcenv = _35_1865.tcenv})
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
| (None, _35_1881, _35_1883) -> begin
(match (probs.deferred) with
| [] -> begin
Success ((probs.subst, {carry = []; slack = probs.slack_vars}))
end
| _35_1887 -> begin
(let _35_1896 = (Support.All.pipe_right probs.deferred (Support.List.partition (fun ( _35_1893 ) -> (match (_35_1893) with
| (c, _35_1890, _35_1892) -> begin
(c < probs.ctr)
end))))
in (match (_35_1896) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _70_15467 = (let _70_15466 = (let _70_15465 = (Support.List.map (fun ( _35_1902 ) -> (match (_35_1902) with
| (_35_1899, x, y) -> begin
(x, y)
end)) probs.deferred)
in {carry = _70_15465; slack = probs.slack_vars})
in (probs.subst, _70_15466))
in Success (_70_15467))
end
| _35_1904 -> begin
(let _70_15470 = (let _35_1905 = probs
in (let _70_15469 = (Support.All.pipe_right attempt (Support.List.map (fun ( _35_1912 ) -> (match (_35_1912) with
| (_35_1908, _35_1910, y) -> begin
y
end))))
in {attempting = _70_15469; deferred = rest; subst = _35_1905.subst; ctr = _35_1905.ctr; slack_vars = _35_1905.slack_vars; defer_ok = _35_1905.defer_ok; smt_ok = _35_1905.smt_ok; tcenv = _35_1905.tcenv}))
in (solve env _70_15470))
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
(let subst = (let _70_15496 = (Microsoft_FStar_Absyn_Util.mk_subst_one_binder hd2 hd1)
in (Support.List.append _70_15496 subst))
in (let env = (let _70_15497 = (Microsoft_FStar_Tc_Env.binding_of_binder hd2)
in (Microsoft_FStar_Tc_Env.push_local_binding env _70_15497))
in (let prob = (match (((Support.Prims.fst hd1), (Support.Prims.fst hd2))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(let _70_15501 = (let _70_15500 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _70_15499 = (Support.All.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _70_15500 _70_15499 b.Microsoft_FStar_Absyn_Syntax.sort None "Formal type parameter")))
in (Support.All.pipe_left (fun ( _70_15498 ) -> KProb (_70_15498)) _70_15501))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(let _70_15505 = (let _70_15504 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _70_15503 = (Support.All.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _70_15504 _70_15503 y.Microsoft_FStar_Absyn_Syntax.sort None "Formal value parameter")))
in (Support.All.pipe_left (fun ( _70_15502 ) -> TProb (_70_15502)) _70_15505))
end
| _35_1988 -> begin
(Support.All.failwith "impos")
end)
in (match ((aux ((hd2)::scope) env subst xs ys)) with
| Support.Microsoft.FStar.Util.Inr (msg) -> begin
Support.Microsoft.FStar.Util.Inr (msg)
end
| Support.Microsoft.FStar.Util.Inl ((sub_probs, phi)) -> begin
(let phi = (let _70_15507 = (Support.All.pipe_right (p_guard prob) Support.Prims.fst)
in (let _70_15506 = (Microsoft_FStar_Absyn_Util.close_forall ((hd2)::[]) phi)
in (Microsoft_FStar_Absyn_Util.mk_conj _70_15507 _70_15506)))
in Support.Microsoft.FStar.Util.Inl (((prob)::sub_probs, phi)))
end))))
end
| _35_1998 -> begin
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
| _35_2013 -> begin
(Support.All.failwith "impossible")
end))
and solve_k' = (fun ( env ) ( problem ) ( wl ) -> (let orig = KProb (problem)
in (match ((Support.Microsoft.FStar.Util.physical_equality problem.lhs problem.rhs)) with
| true -> begin
(let _70_15514 = (solve_prob orig None [] wl)
in (solve env _70_15514))
end
| false -> begin
(let k1 = problem.lhs
in (let k2 = problem.rhs
in (match ((Support.Microsoft.FStar.Util.physical_equality k1 k2)) with
| true -> begin
(let _70_15515 = (solve_prob orig None [] wl)
in (solve env _70_15515))
end
| false -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let imitate_k = (fun ( _35_2029 ) -> (match (_35_2029) with
| (rel, u, ps, xs, (h, qs)) -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let _35_2034 = (imitation_sub_probs orig env xs ps qs)
in (match (_35_2034) with
| (sub_probs, gs_xs, f) -> begin
(let im = (let _70_15531 = (let _70_15530 = (h gs_xs)
in (xs, _70_15530))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam _70_15531 r))
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
in (let _70_15540 = (solve_prob orig None ((UK ((u, k1)))::[]) wl)
in (solve env _70_15540)))
end
| false -> begin
(let _70_15545 = (let _70_15544 = (Support.All.pipe_right xs Microsoft_FStar_Absyn_Util.args_of_non_null_binders)
in (let _70_15543 = (decompose_kind env k)
in (rel, u, _70_15544, xs, _70_15543)))
in (imitate_k _70_15545))
end))))
end
| None -> begin
(giveup env "flex-rigid: not a pattern" (KProb (problem)))
end)))
in (match ((k1.Microsoft_FStar_Absyn_Syntax.n, k2.Microsoft_FStar_Absyn_Syntax.n)) with
| ((Microsoft_FStar_Absyn_Syntax.Kind_type, Microsoft_FStar_Absyn_Syntax.Kind_type)) | ((Microsoft_FStar_Absyn_Syntax.Kind_effect, Microsoft_FStar_Absyn_Syntax.Kind_effect)) -> begin
(let _70_15546 = (solve_prob orig None [] wl)
in (Support.All.pipe_left (solve env) _70_15546))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_35_2057, k1)), _35_2062) -> begin
(solve_k env (let _35_2064 = problem
in {lhs = k1; relation = _35_2064.relation; rhs = _35_2064.rhs; element = _35_2064.element; logical_guard = _35_2064.logical_guard; scope = _35_2064.scope; reason = _35_2064.reason; loc = _35_2064.loc; rank = _35_2064.rank}) wl)
end
| (_35_2067, Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_35_2069, k2))) -> begin
(solve_k env (let _35_2074 = problem
in {lhs = _35_2074.lhs; relation = _35_2074.relation; rhs = k2; element = _35_2074.element; logical_guard = _35_2074.logical_guard; scope = _35_2074.scope; reason = _35_2074.reason; loc = _35_2074.loc; rank = _35_2074.rank}) wl)
end
| (Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs1, k1')), Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs2, k2'))) -> begin
(let sub_prob = (fun ( scope ) ( env ) ( subst ) -> (let _70_15555 = (let _70_15554 = (Microsoft_FStar_Absyn_Util.subst_kind subst k1')
in (mk_problem scope orig _70_15554 problem.relation k2' None "Arrow-kind result"))
in (Support.All.pipe_left (fun ( _70_15553 ) -> KProb (_70_15553)) _70_15555)))
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
in (let _35_2117 = (new_kvar r zs)
in (match (_35_2117) with
| (u, _35_2116) -> begin
(let k1 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam (xs, u) r)
in (let k2 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam (ys, u) r)
in (let wl = (solve_prob orig None ((UK ((u1, k1)))::(UK ((u2, k2)))::[]) wl)
in (solve env wl))))
end)))
end)
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_uvar ((u, args)), _35_2126) -> begin
(flex_rigid problem.relation u args k2)
end
| (_35_2129, Microsoft_FStar_Absyn_Syntax.Kind_uvar ((u, args))) -> begin
(flex_rigid (invert_rel problem.relation) u args k1)
end
| ((Microsoft_FStar_Absyn_Syntax.Kind_delayed (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Kind_unknown, _)) | ((_, Microsoft_FStar_Absyn_Syntax.Kind_delayed (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Kind_unknown)) -> begin
(Support.All.failwith "Impossible")
end
| _35_2156 -> begin
(giveup env "head mismatch (k-1)" (KProb (problem)))
end))))
end)))
end)))
and solve_t = (fun ( env ) ( problem ) ( wl ) -> (let p = (compress_prob wl (TProb (problem)))
in (match (p) with
| TProb (p) -> begin
(solve_t' env p wl)
end
| _35_2164 -> begin
(Support.All.failwith "Impossible")
end)))
and solve_t' = (fun ( env ) ( problem ) ( wl ) -> (let giveup_or_defer = (fun ( orig ) ( msg ) -> (match (wl.defer_ok) with
| true -> begin
(let _35_2171 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_15566 = (prob_to_string env orig)
in (Support.Microsoft.FStar.Util.fprint2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _70_15566 msg))
end
| false -> begin
()
end)
in (solve env (defer msg orig wl)))
end
| false -> begin
(giveup env msg orig)
end))
in (let imitate_t = (fun ( orig ) ( env ) ( wl ) ( p ) -> (let _35_2188 = p
in (match (_35_2188) with
| ((u, k), ps, xs, (h, _35_2185, qs)) -> begin
(let xs = (sn_binders env xs)
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let _35_2194 = (imitation_sub_probs orig env xs ps qs)
in (match (_35_2194) with
| (sub_probs, gs_xs, formula) -> begin
(let im = (let _70_15578 = (let _70_15577 = (h gs_xs)
in (xs, _70_15577))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' _70_15578 None r))
in (let _35_2196 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_15583 = (Microsoft_FStar_Absyn_Print.typ_to_string im)
in (let _70_15582 = (Microsoft_FStar_Absyn_Print.tag_of_typ im)
in (let _70_15581 = (let _70_15579 = (Support.List.map (prob_to_string env) sub_probs)
in (Support.All.pipe_right _70_15579 (Support.String.concat ", ")))
in (let _70_15580 = (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env formula)
in (Support.Microsoft.FStar.Util.fprint4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _70_15583 _70_15582 _70_15581 _70_15580)))))
end
| false -> begin
()
end)
in (let wl = (solve_prob orig (Some (formula)) ((UT (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (let project_t = (fun ( orig ) ( env ) ( wl ) ( i ) ( p ) -> (let _35_2212 = p
in (match (_35_2212) with
| (u, ps, xs, (h, matches, qs)) -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let pi = (Support.List.nth ps i)
in (let rec gs = (fun ( k ) -> (let _35_2219 = (Microsoft_FStar_Absyn_Util.kind_formals k)
in (match (_35_2219) with
| (bs, k) -> begin
(let rec aux = (fun ( subst ) ( bs ) -> (match (bs) with
| [] -> begin
([], [])
end
| hd::tl -> begin
(let _35_2248 = (match ((Support.Prims.fst hd)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let k_a = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _35_2232 = (new_tvar r xs k_a)
in (match (_35_2232) with
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
in (let _70_15603 = (Microsoft_FStar_Absyn_Syntax.targ gi_xs)
in (let _70_15602 = (Microsoft_FStar_Absyn_Syntax.targ gi_ps)
in (_70_15603, _70_15602, subst))))))
end)))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let t_x = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _35_2241 = (new_evar r xs t_x)
in (match (_35_2241) with
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
in (let _70_15605 = (Microsoft_FStar_Absyn_Syntax.varg gi_xs)
in (let _70_15604 = (Microsoft_FStar_Absyn_Syntax.varg gi_ps)
in (_70_15605, _70_15604, subst))))))
end)))
end)
in (match (_35_2248) with
| (gi_xs, gi_ps, subst) -> begin
(let _35_2251 = (aux subst tl)
in (match (_35_2251) with
| (gi_xs', gi_ps') -> begin
((gi_xs)::gi_xs', (gi_ps)::gi_ps')
end))
end))
end))
in (aux [] bs))
end)))
in (match ((let _70_15607 = (let _70_15606 = (Support.List.nth xs i)
in (Support.All.pipe_left Support.Prims.fst _70_15606))
in ((Support.Prims.fst pi), _70_15607))) with
| (Support.Microsoft.FStar.Util.Inl (pi), Support.Microsoft.FStar.Util.Inl (xi)) -> begin
(match ((let _70_15608 = (matches pi)
in (Support.All.pipe_left Support.Prims.op_Negation _70_15608))) with
| true -> begin
None
end
| false -> begin
(let _35_2260 = (gs xi.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_35_2260) with
| (g_xs, _35_2259) -> begin
(let xi = (Microsoft_FStar_Absyn_Util.btvar_to_typ xi)
in (let proj = (let _70_15610 = (let _70_15609 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (xi, g_xs) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)
in (xs, _70_15609))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_15610 None r))
in (let sub = (let _70_15616 = (let _70_15615 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (proj, ps) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)
in (let _70_15614 = (let _70_15613 = (Support.List.map (fun ( _35_2268 ) -> (match (_35_2268) with
| (_35_2264, _35_2266, y) -> begin
y
end)) qs)
in (Support.All.pipe_left h _70_15613))
in (mk_problem (p_scope orig) orig _70_15615 (p_rel orig) _70_15614 None "projection")))
in (Support.All.pipe_left (fun ( _70_15611 ) -> TProb (_70_15611)) _70_15616))
in (let _35_2270 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_15618 = (Microsoft_FStar_Absyn_Print.typ_to_string proj)
in (let _70_15617 = (prob_to_string env sub)
in (Support.Microsoft.FStar.Util.fprint2 "Projecting %s\n\tsubprob=%s\n" _70_15618 _70_15617)))
end
| false -> begin
()
end)
in (let wl = (let _70_15620 = (let _70_15619 = (Support.All.pipe_left Support.Prims.fst (p_guard sub))
in Some (_70_15619))
in (solve_prob orig _70_15620 ((UT ((u, proj)))::[]) wl))
in (let _70_15622 = (solve env (attempt ((sub)::[]) wl))
in (Support.All.pipe_left (fun ( _70_15621 ) -> Some (_70_15621)) _70_15622)))))))
end))
end)
end
| _35_2274 -> begin
None
end))))
end)))
in (let solve_t_flex_rigid = (fun ( orig ) ( lhs ) ( t2 ) ( wl ) -> (let _35_2286 = lhs
in (match (_35_2286) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(let subterms = (fun ( ps ) -> (let xs = (let _70_15649 = (Microsoft_FStar_Absyn_Util.kind_formals k)
in (Support.All.pipe_right _70_15649 Support.Prims.fst))
in (let xs = (Microsoft_FStar_Absyn_Util.name_binders xs)
in (let _70_15654 = (decompose_typ env t2)
in ((uv, k), ps, xs, _70_15654)))))
in (let rec imitate_or_project = (fun ( n ) ( st ) ( i ) -> (match ((i >= n)) with
| true -> begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end
| false -> begin
(match ((i = (- (1)))) with
| true -> begin
(match ((imitate_t orig env wl st)) with
| Failed (_35_2296) -> begin
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
in (let check_head = (fun ( fvs1 ) ( t2 ) -> (let _35_2312 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (match (_35_2312) with
| (hd, _35_2311) -> begin
(match (hd.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| _35_2323 -> begin
(let fvs_hd = (Microsoft_FStar_Absyn_Util.freevars_typ hd)
in (match ((Microsoft_FStar_Absyn_Util.fvs_included fvs_hd fvs1)) with
| true -> begin
true
end
| false -> begin
(let _35_2325 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_15665 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs_hd)
in (Support.Microsoft.FStar.Util.fprint1 "Free variables are %s" _70_15665))
end
| false -> begin
()
end)
in false)
end))
end)
end)))
in (let imitate_ok = (fun ( t2 ) -> (let fvs_hd = (let _70_15669 = (let _70_15668 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (Support.All.pipe_right _70_15668 Support.Prims.fst))
in (Support.All.pipe_right _70_15669 Microsoft_FStar_Absyn_Util.freevars_typ))
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
in (let _35_2338 = (occurs_check env wl (uv, k) t2)
in (match (_35_2338) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(let _70_15671 = (let _70_15670 = (Support.Option.get msg)
in (Support.String.strcat "occurs-check failed: " _70_15670))
in (giveup_or_defer orig _70_15671))
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Util.fvs_included fvs2 fvs1)) with
| true -> begin
(match (((Microsoft_FStar_Absyn_Util.is_function_typ t2) && ((p_rel orig) <> EQ))) with
| true -> begin
(let _70_15672 = (subterms args_lhs)
in (imitate_t orig env wl _70_15672))
end
| false -> begin
(let _35_2339 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_15675 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _70_15674 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs1)
in (let _70_15673 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs2)
in (Support.Microsoft.FStar.Util.fprint3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _70_15675 _70_15674 _70_15673))))
end
| false -> begin
()
end)
in (let sol = (match (vars) with
| [] -> begin
t2
end
| _35_2343 -> begin
(let _70_15677 = (let _70_15676 = (sn_binders env vars)
in (_70_15676, t2))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_15677 None t1.Microsoft_FStar_Absyn_Syntax.pos))
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
(let _35_2346 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_15680 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _70_15679 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs1)
in (let _70_15678 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs2)
in (Support.Microsoft.FStar.Util.fprint3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _70_15680 _70_15679 _70_15678))))
end
| false -> begin
()
end)
in (let _70_15681 = (subterms args_lhs)
in (imitate_or_project (Support.List.length args_lhs) _70_15681 (- (1)))))
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
(match ((let _70_15682 = (Microsoft_FStar_Absyn_Util.freevars_typ t1)
in (check_head _70_15682 t2))) with
| true -> begin
(let im_ok = (imitate_ok t2)
in (let _35_2350 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_15683 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Support.Microsoft.FStar.Util.fprint2 "Not a pattern (%s) ... %s\n" _70_15683 (match ((im_ok < 0)) with
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
in (let _70_15684 = (subterms args_lhs)
in (imitate_or_project (Support.List.length args_lhs) _70_15684 im_ok))))
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
(let force_quasi_pattern = (fun ( xs_opt ) ( _35_2362 ) -> (match (_35_2362) with
| (t, u, k, args) -> begin
(let rec aux = (fun ( binders ) ( ys ) ( args ) -> (match (args) with
| [] -> begin
(let ys = (Support.List.rev ys)
in (let binders = (Support.List.rev binders)
in (let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (let _35_2374 = (new_tvar t.Microsoft_FStar_Absyn_Syntax.pos ys kk)
in (match (_35_2374) with
| (t', _35_2373) -> begin
(let _35_2380 = (destruct_flex_t t')
in (match (_35_2380) with
| (u1_ys, u1, k1, _35_2379) -> begin
(let sol = (let _70_15702 = (let _70_15701 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, u1_ys) (Some (k)) t.Microsoft_FStar_Absyn_Syntax.pos)
in ((u, k), _70_15701))
in UT (_70_15702))
in (sol, (t', u, k1, ys)))
end))
end)))))
end
| hd::tl -> begin
(let new_binder = (fun ( hd ) -> (match ((Support.Prims.fst hd)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _70_15706 = (let _70_15705 = (Microsoft_FStar_Tc_Recheck.recompute_kind a)
in (Support.All.pipe_right _70_15705 (Microsoft_FStar_Absyn_Util.gen_bvar_p a.Microsoft_FStar_Absyn_Syntax.pos)))
in (Support.All.pipe_right _70_15706 Microsoft_FStar_Absyn_Syntax.t_binder))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _70_15708 = (let _70_15707 = (Microsoft_FStar_Tc_Recheck.recompute_typ x)
in (Support.All.pipe_right _70_15707 (Microsoft_FStar_Absyn_Util.gen_bvar_p x.Microsoft_FStar_Absyn_Syntax.pos)))
in (Support.All.pipe_right _70_15708 Microsoft_FStar_Absyn_Syntax.v_binder))
end))
in (let _35_2399 = (match ((pat_var_opt env ys hd)) with
| None -> begin
(let _70_15709 = (new_binder hd)
in (_70_15709, ys))
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
(let _70_15710 = (new_binder hd)
in (_70_15710, ys))
end)
end)
end)
in (match (_35_2399) with
| (binder, ys) -> begin
(aux ((binder)::binders) ys tl)
end)))
end))
in (aux [] [] args))
end))
in (let solve_both_pats = (fun ( wl ) ( _35_2405 ) ( _35_2409 ) ( k ) ( r ) -> (match ((_35_2405, _35_2409)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
(match (((Support.Microsoft.FStar.Unionfind.equivalent u1 u2) && (binders_eq xs ys))) with
| true -> begin
(let _70_15721 = (solve_prob orig None [] wl)
in (solve env _70_15721))
end
| false -> begin
(let xs = (sn_binders env xs)
in (let ys = (sn_binders env ys)
in (let zs = (intersect_vars xs ys)
in (let _35_2418 = (new_tvar r zs k)
in (match (_35_2418) with
| (u_zs, _35_2417) -> begin
(let sub1 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' (xs, u_zs) (Some (k1)) r)
in (let _35_2422 = (occurs_check env wl (u1, k1) sub1)
in (match (_35_2422) with
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
in (let _35_2428 = (occurs_check env wl (u2, k2) sub2)
in (match (_35_2428) with
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
in (let solve_one_pat = (fun ( _35_2436 ) ( _35_2441 ) -> (match ((_35_2436, _35_2441)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(let _35_2442 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_15727 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _70_15726 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (Support.Microsoft.FStar.Util.fprint2 "Trying flex-flex one pattern (%s) with %s\n" _70_15727 _70_15726)))
end
| false -> begin
()
end)
in (match ((Support.Microsoft.FStar.Unionfind.equivalent u1 u2)) with
| true -> begin
(let sub_probs = (Support.List.map2 (fun ( a ) ( b ) -> (let a = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder a)
in (match (((Support.Prims.fst a), (Support.Prims.fst b))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
(let _70_15731 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (Support.All.pipe_right _70_15731 (fun ( _70_15730 ) -> TProb (_70_15730))))
end
| (Support.Microsoft.FStar.Util.Inr (t1), Support.Microsoft.FStar.Util.Inr (t2)) -> begin
(let _70_15733 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (Support.All.pipe_right _70_15733 (fun ( _70_15732 ) -> EProb (_70_15732))))
end
| _35_2458 -> begin
(Support.All.failwith "Impossible")
end))) xs args2)
in (let guard = (let _70_15735 = (Support.List.map (fun ( p ) -> (Support.All.pipe_right (p_guard p) Support.Prims.fst)) sub_probs)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _70_15735))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end
| false -> begin
(let t2 = (sn env t2)
in (let rhs_vars = (Microsoft_FStar_Absyn_Util.freevars_typ t2)
in (let _35_2468 = (occurs_check env wl (u1, k1) t2)
in (match (_35_2468) with
| (occurs_ok, _35_2467) -> begin
(let lhs_vars = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders xs)
in (match ((occurs_ok && (Microsoft_FStar_Absyn_Util.fvs_included rhs_vars lhs_vars))) with
| true -> begin
(let sol = (let _70_15737 = (let _70_15736 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' (xs, t2) (Some (k1)) t1.Microsoft_FStar_Absyn_Syntax.pos)
in ((u1, k1), _70_15736))
in UT (_70_15737))
in (let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end
| false -> begin
(match ((occurs_ok && (Support.All.pipe_left Support.Prims.op_Negation wl.defer_ok))) with
| true -> begin
(let _35_2479 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_35_2479) with
| (sol, (_35_2474, u2, k2, ys)) -> begin
(let wl = (extend_solution sol wl)
in (let _35_2481 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("QuasiPattern")))) with
| true -> begin
(let _70_15738 = (uvi_to_string env sol)
in (Support.Microsoft.FStar.Util.fprint1 "flex-flex quasi pattern (2): %s\n" _70_15738))
end
| false -> begin
()
end)
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _35_2486 -> begin
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
in (let _35_2491 = lhs
in (match (_35_2491) with
| (t1, u1, k1, args1) -> begin
(let _35_2496 = rhs
in (match (_35_2496) with
| (t2, u2, k2, args2) -> begin
(let maybe_pat_vars1 = (pat_vars env [] args1)
in (let maybe_pat_vars2 = (pat_vars env [] args2)
in (let r = t2.Microsoft_FStar_Absyn_Syntax.pos
in (match ((maybe_pat_vars1, maybe_pat_vars2)) with
| (Some (xs), Some (ys)) -> begin
(let _70_15739 = (Microsoft_FStar_Tc_Recheck.recompute_kind t2)
in (solve_both_pats wl (u1, k1, xs) (u2, k2, ys) _70_15739 t2.Microsoft_FStar_Absyn_Syntax.pos))
end
| (Some (xs), None) -> begin
(solve_one_pat (t1, u1, k1, xs) rhs)
end
| (None, Some (ys)) -> begin
(solve_one_pat (t2, u2, k2, ys) lhs)
end
| _35_2514 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end
| false -> begin
(let _35_2518 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_35_2518) with
| (sol, _35_2517) -> begin
(let wl = (extend_solution sol wl)
in (let _35_2520 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("QuasiPattern")))) with
| true -> begin
(let _70_15740 = (uvi_to_string env sol)
in (Support.Microsoft.FStar.Util.fprint1 "flex-flex quasi pattern (1): %s\n" _70_15740))
end
| false -> begin
()
end)
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _35_2525 -> begin
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
(let _70_15741 = (solve_prob orig None [] wl)
in (solve env _70_15741))
end
| false -> begin
(let t1 = problem.lhs
in (let t2 = problem.rhs
in (match ((Support.Microsoft.FStar.Util.physical_equality t1 t2)) with
| true -> begin
(let _70_15742 = (solve_prob orig None [] wl)
in (solve env _70_15742))
end
| false -> begin
(let _35_2529 = (match ((Microsoft_FStar_Tc_Env.debug env (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_15745 = (prob_to_string env orig)
in (let _70_15744 = (let _70_15743 = (Support.List.map (uvi_to_string wl.tcenv) wl.subst)
in (Support.All.pipe_right _70_15743 (Support.String.concat "; ")))
in (Support.Microsoft.FStar.Util.fprint2 "Attempting %s\n\tSubst is %s\n" _70_15745 _70_15744)))
end
| false -> begin
()
end)
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let match_num_binders = (fun ( _35_2534 ) ( _35_2537 ) -> (match ((_35_2534, _35_2537)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(let curry = (fun ( n ) ( bs ) ( mk_cod ) -> (let _35_2544 = (Support.Microsoft.FStar.Util.first_N n bs)
in (match (_35_2544) with
| (bs, rest) -> begin
(let _70_15775 = (mk_cod rest)
in (bs, _70_15775))
end)))
in (let l1 = (Support.List.length bs1)
in (let l2 = (Support.List.length bs2)
in (match ((l1 = l2)) with
| true -> begin
(let _70_15779 = (let _70_15776 = (mk_cod1 [])
in (bs1, _70_15776))
in (let _70_15778 = (let _70_15777 = (mk_cod2 [])
in (bs2, _70_15777))
in (_70_15779, _70_15778)))
end
| false -> begin
(match ((l1 > l2)) with
| true -> begin
(let _70_15782 = (curry l2 bs1 mk_cod1)
in (let _70_15781 = (let _70_15780 = (mk_cod2 [])
in (bs2, _70_15780))
in (_70_15782, _70_15781)))
end
| false -> begin
(let _70_15785 = (let _70_15783 = (mk_cod1 [])
in (bs1, _70_15783))
in (let _70_15784 = (curry l1 bs2 mk_cod2)
in (_70_15785, _70_15784)))
end)
end))))
end))
in (match ((t1.Microsoft_FStar_Absyn_Syntax.n, t2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvd_eq a.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(let _70_15786 = (solve_prob orig None [] wl)
in (solve env _70_15786))
end
| false -> begin
(let _70_15790 = (let _70_15789 = (let _70_15788 = (Microsoft_FStar_Absyn_Util.mk_eq_typ t1 t2)
in (Support.All.pipe_left (fun ( _70_15787 ) -> Some (_70_15787)) _70_15788))
in (solve_prob orig _70_15789 [] wl))
in (solve env _70_15790))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs1, c1)), Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs2, c2))) -> begin
(let mk_c = (fun ( c ) ( _35_31 ) -> (match (_35_31) with
| [] -> begin
c
end
| bs -> begin
(let _70_15795 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None c.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Total _70_15795))
end))
in (let _35_2575 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_35_2575) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun ( scope ) ( env ) ( subst ) -> (let c1 = (Microsoft_FStar_Absyn_Util.subst_comp subst c1)
in (let rel = (match ((Support.ST.read Microsoft_FStar_Options.use_eq_at_higher_order)) with
| true -> begin
EQ
end
| false -> begin
problem.relation
end)
in (let _35_2581 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("EQ")))) with
| true -> begin
(let _70_15802 = (let _70_15801 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.All.pipe_right _70_15801 Support.Microsoft.FStar.Range.string_of_range))
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Using relation %s at higher order\n" _70_15802 (rel_to_string rel)))
end
| false -> begin
()
end)
in (let _70_15804 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (Support.All.pipe_left (fun ( _70_15803 ) -> CProb (_70_15803)) _70_15804)))))))
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
in (let _35_2603 = (match_num_binders (bs1, (mk_t t1')) (bs2, (mk_t t2')))
in (match (_35_2603) with
| ((bs1, t1'), (bs2, t2')) -> begin
(solve_binders env bs1 bs2 orig wl (fun ( scope ) ( env ) ( subst ) -> (let t1' = (Microsoft_FStar_Absyn_Util.subst_typ subst t1')
in (let _70_15815 = (mk_problem scope orig t1' problem.relation t2' None "lambda co-domain")
in (Support.All.pipe_left (fun ( _70_15814 ) -> TProb (_70_15814)) _70_15815)))))
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine (_35_2609), Microsoft_FStar_Absyn_Syntax.Typ_refine (_35_2612)) -> begin
(let _35_2617 = (as_refinement env wl t1)
in (match (_35_2617) with
| (x1, phi1) -> begin
(let _35_2620 = (as_refinement env wl t2)
in (match (_35_2620) with
| (x2, phi2) -> begin
(let base_prob = (let _70_15817 = (mk_problem (p_scope orig) orig x1.Microsoft_FStar_Absyn_Syntax.sort problem.relation x2.Microsoft_FStar_Absyn_Syntax.sort problem.element "refinement base type")
in (Support.All.pipe_left (fun ( _70_15816 ) -> TProb (_70_15816)) _70_15817))
in (let x1_for_x2 = (let _70_15819 = (Microsoft_FStar_Absyn_Syntax.v_binder x1)
in (let _70_15818 = (Microsoft_FStar_Absyn_Syntax.v_binder x2)
in (Microsoft_FStar_Absyn_Util.mk_subst_one_binder _70_15819 _70_15818)))
in (let phi2 = (Microsoft_FStar_Absyn_Util.subst_typ x1_for_x2 phi2)
in (let mk_imp = (fun ( imp ) ( phi1 ) ( phi2 ) -> (let _70_15836 = (imp phi1 phi2)
in (Support.All.pipe_right _70_15836 (guard_on_element problem x1))))
in (let fallback = (fun ( _35_2629 ) -> (match (()) with
| () -> begin
(let impl = (match ((problem.relation = EQ)) with
| true -> begin
(mk_imp Microsoft_FStar_Absyn_Util.mk_iff phi1 phi2)
end
| false -> begin
(mk_imp Microsoft_FStar_Absyn_Util.mk_imp phi1 phi2)
end)
in (let guard = (let _70_15839 = (Support.All.pipe_right (p_guard base_prob) Support.Prims.fst)
in (Microsoft_FStar_Absyn_Util.mk_conj _70_15839 impl))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in (match ((problem.relation = EQ)) with
| true -> begin
(let ref_prob = (let _70_15841 = (mk_problem (p_scope orig) orig phi1 EQ phi2 None "refinement formula")
in (Support.All.pipe_left (fun ( _70_15840 ) -> TProb (_70_15840)) _70_15841))
in (match ((solve env (let _35_2634 = wl
in {attempting = (ref_prob)::[]; deferred = []; subst = _35_2634.subst; ctr = _35_2634.ctr; slack_vars = _35_2634.slack_vars; defer_ok = false; smt_ok = _35_2634.smt_ok; tcenv = _35_2634.tcenv}))) with
| Failed (_35_2637) -> begin
(fallback ())
end
| Success ((subst, _35_2641)) -> begin
(let guard = (let _70_15844 = (Support.All.pipe_right (p_guard base_prob) Support.Prims.fst)
in (let _70_15843 = (let _70_15842 = (Support.All.pipe_right (p_guard ref_prob) Support.Prims.fst)
in (Support.All.pipe_right _70_15842 (guard_on_element problem x1)))
in (Microsoft_FStar_Absyn_Util.mk_conj _70_15844 _70_15843)))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (let wl = (let _35_2646 = wl
in {attempting = _35_2646.attempting; deferred = _35_2646.deferred; subst = subst; ctr = (wl.ctr + 1); slack_vars = _35_2646.slack_vars; defer_ok = _35_2646.defer_ok; smt_ok = _35_2646.smt_ok; tcenv = _35_2646.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end
| false -> begin
(fallback ())
end))))))
end))
end))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), Microsoft_FStar_Absyn_Syntax.Typ_uvar (_))) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), Microsoft_FStar_Absyn_Syntax.Typ_uvar (_))) | ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) -> begin
(let _70_15846 = (destruct_flex_t t1)
in (let _70_15845 = (destruct_flex_t t2)
in (flex_flex orig _70_15846 _70_15845)))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _)) when (problem.relation = EQ) -> begin
(let _70_15847 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _70_15847 t2 wl))
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
in (match ((let _70_15848 = (is_top_level_prob orig)
in (Support.All.pipe_left Support.Prims.op_Negation _70_15848))) with
| true -> begin
(let _70_15851 = (Support.All.pipe_left (fun ( _70_15849 ) -> TProb (_70_15849)) (let _35_2805 = problem
in {lhs = _35_2805.lhs; relation = new_rel; rhs = _35_2805.rhs; element = _35_2805.element; logical_guard = _35_2805.logical_guard; scope = _35_2805.scope; reason = _35_2805.reason; loc = _35_2805.loc; rank = _35_2805.rank}))
in (let _70_15850 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _70_15851 _70_15850 t2 wl)))
end
| false -> begin
(let _35_2809 = (base_and_refinement env wl t2)
in (match (_35_2809) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _70_15854 = (Support.All.pipe_left (fun ( _70_15852 ) -> TProb (_70_15852)) (let _35_2811 = problem
in {lhs = _35_2811.lhs; relation = new_rel; rhs = _35_2811.rhs; element = _35_2811.element; logical_guard = _35_2811.logical_guard; scope = _35_2811.scope; reason = _35_2811.reason; loc = _35_2811.loc; rank = _35_2811.rank}))
in (let _70_15853 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _70_15854 _70_15853 t_base wl)))
end
| Some ((y, phi)) -> begin
(let y' = (let _35_2817 = y
in {Microsoft_FStar_Absyn_Syntax.v = _35_2817.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t1; Microsoft_FStar_Absyn_Syntax.p = _35_2817.Microsoft_FStar_Absyn_Syntax.p})
in (let impl = (guard_on_element problem y' phi)
in (let base_prob = (let _70_15856 = (mk_problem problem.scope orig t1 new_rel y.Microsoft_FStar_Absyn_Syntax.sort problem.element "flex-rigid: base type")
in (Support.All.pipe_left (fun ( _70_15855 ) -> TProb (_70_15855)) _70_15856))
in (let guard = (let _70_15857 = (Support.All.pipe_right (p_guard base_prob) Support.Prims.fst)
in (Microsoft_FStar_Absyn_Util.mk_conj _70_15857 impl))
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
(let _35_2852 = (base_and_refinement env wl t1)
in (match (_35_2852) with
| (t_base, _35_2851) -> begin
(solve_t env (let _35_2853 = problem
in {lhs = t_base; relation = EQ; rhs = _35_2853.rhs; element = _35_2853.element; logical_guard = _35_2853.logical_guard; scope = _35_2853.scope; reason = _35_2853.reason; loc = _35_2853.loc; rank = _35_2853.rank}) wl)
end))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine (_35_2856), _35_2859) -> begin
(let t2 = (let _70_15858 = (base_and_refinement env wl t2)
in (Support.All.pipe_left force_refinement _70_15858))
in (solve_t env (let _35_2862 = problem
in {lhs = _35_2862.lhs; relation = _35_2862.relation; rhs = t2; element = _35_2862.element; logical_guard = _35_2862.logical_guard; scope = _35_2862.scope; reason = _35_2862.reason; loc = _35_2862.loc; rank = _35_2862.rank}) wl))
end
| (_35_2865, Microsoft_FStar_Absyn_Syntax.Typ_refine (_35_2867)) -> begin
(let t1 = (let _70_15859 = (base_and_refinement env wl t1)
in (Support.All.pipe_left force_refinement _70_15859))
in (solve_t env (let _35_2871 = problem
in {lhs = t1; relation = _35_2871.relation; rhs = _35_2871.rhs; element = _35_2871.element; logical_guard = _35_2871.logical_guard; scope = _35_2871.scope; reason = _35_2871.reason; loc = _35_2871.loc; rank = _35_2871.rank}) wl))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_const (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_btvar (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_const (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_app (_))) -> begin
(let _35_2911 = (head_matches_delta env wl t1 t2)
in (match (_35_2911) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch, _35_2914) -> begin
(let head1 = (let _70_15860 = (Microsoft_FStar_Absyn_Util.head_and_args t1)
in (Support.All.pipe_right _70_15860 Support.Prims.fst))
in (let head2 = (let _70_15861 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (Support.All.pipe_right _70_15861 Support.Prims.fst))
in (let may_equate = (fun ( head ) -> (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (_35_2921) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) -> begin
(Microsoft_FStar_Tc_Env.is_projector env tc.Microsoft_FStar_Absyn_Syntax.v)
end
| _35_2926 -> begin
false
end))
in (match ((((may_equate head1) || (may_equate head2)) && wl.smt_ok)) with
| true -> begin
(let _70_15867 = (let _70_15866 = (let _70_15865 = (Microsoft_FStar_Absyn_Util.mk_eq_typ t1 t2)
in (Support.All.pipe_left (fun ( _70_15864 ) -> Some (_70_15864)) _70_15865))
in (solve_prob orig _70_15866 [] wl))
in (solve env _70_15867))
end
| false -> begin
(giveup env "head mismatch" orig)
end))))
end
| (_35_2928, Some ((t1, t2))) -> begin
(solve_t env (let _35_2934 = problem
in {lhs = t1; relation = _35_2934.relation; rhs = t2; element = _35_2934.element; logical_guard = _35_2934.logical_guard; scope = _35_2934.scope; reason = _35_2934.reason; loc = _35_2934.loc; rank = _35_2934.rank}) wl)
end
| (_35_2937, None) -> begin
(let _35_2940 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_15869 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _70_15868 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (Support.Microsoft.FStar.Util.fprint2 "Head matches: %s and %s\n" _70_15869 _70_15868)))
end
| false -> begin
()
end)
in (let _35_2944 = (Microsoft_FStar_Absyn_Util.head_and_args t1)
in (match (_35_2944) with
| (head, args) -> begin
(let _35_2947 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (match (_35_2947) with
| (head', args') -> begin
(let nargs = (Support.List.length args)
in (match ((nargs <> (Support.List.length args'))) with
| true -> begin
(let _70_15874 = (let _70_15873 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (let _70_15872 = (Microsoft_FStar_Absyn_Print.args_to_string args)
in (let _70_15871 = (Microsoft_FStar_Absyn_Print.typ_to_string head')
in (let _70_15870 = (Microsoft_FStar_Absyn_Print.args_to_string args')
in (Support.Microsoft.FStar.Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _70_15873 _70_15872 _70_15871 _70_15870)))))
in (giveup env _70_15874 orig))
end
| false -> begin
(match (((nargs = 0) || (eq_args args args'))) with
| true -> begin
(let _70_15875 = (solve_prob orig None [] wl)
in (solve env _70_15875))
end
| false -> begin
(let _35_2951 = (base_and_refinement env wl t1)
in (match (_35_2951) with
| (base1, refinement1) -> begin
(let _35_2954 = (base_and_refinement env wl t2)
in (match (_35_2954) with
| (base2, refinement2) -> begin
(match ((refinement1, refinement2)) with
| (None, None) -> begin
(let _35_2958 = (match (((head_matches head head) <> FullMatch)) with
| true -> begin
(let _70_15878 = (let _70_15877 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (let _70_15876 = (Microsoft_FStar_Absyn_Print.typ_to_string head')
in (Support.Microsoft.FStar.Util.format2 "Assertion failed: expected full match of %s and %s\n" _70_15877 _70_15876)))
in (Support.All.failwith _70_15878))
end
| false -> begin
()
end)
in (let subprobs = (Support.List.map2 (fun ( a ) ( a' ) -> (match (((Support.Prims.fst a), (Support.Prims.fst a'))) with
| (Support.Microsoft.FStar.Util.Inl (t), Support.Microsoft.FStar.Util.Inl (t')) -> begin
(let _70_15882 = (mk_problem (p_scope orig) orig t EQ t' None "type index")
in (Support.All.pipe_left (fun ( _70_15881 ) -> TProb (_70_15881)) _70_15882))
end
| (Support.Microsoft.FStar.Util.Inr (v), Support.Microsoft.FStar.Util.Inr (v')) -> begin
(let _70_15884 = (mk_problem (p_scope orig) orig v EQ v' None "term index")
in (Support.All.pipe_left (fun ( _70_15883 ) -> EProb (_70_15883)) _70_15884))
end
| _35_2973 -> begin
(Support.All.failwith "Impossible")
end)) args args')
in (let formula = (let _70_15886 = (Support.List.map (fun ( p ) -> (Support.Prims.fst (p_guard p))) subprobs)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _70_15886))
in (let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl))))))
end
| _35_2979 -> begin
(let lhs = (force_refinement (base1, refinement1))
in (let rhs = (force_refinement (base2, refinement2))
in (solve_t env (let _35_2982 = problem
in {lhs = lhs; relation = _35_2982.relation; rhs = rhs; element = _35_2982.element; logical_guard = _35_2982.logical_guard; scope = _35_2982.scope; reason = _35_2982.reason; loc = _35_2982.loc; rank = _35_2982.rank}) wl)))
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
| _35_3021 -> begin
(giveup env "head mismatch" orig)
end))))
end)))
end))))))))
and solve_c = (fun ( env ) ( problem ) ( wl ) -> (let c1 = problem.lhs
in (let c2 = problem.rhs
in (let orig = CProb (problem)
in (let sub_prob = (fun ( t1 ) ( rel ) ( t2 ) ( reason ) -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (let solve_eq = (fun ( c1_comp ) ( c2_comp ) -> (let _35_3038 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("EQ")))) with
| true -> begin
(Support.Microsoft.FStar.Util.print_string "solve_c is using an equality constraint\n")
end
| false -> begin
()
end)
in (let sub_probs = (Support.List.map2 (fun ( arg1 ) ( arg2 ) -> (match (((Support.Prims.fst arg1), (Support.Prims.fst arg2))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
(let _70_15901 = (sub_prob t1 EQ t2 "effect arg")
in (Support.All.pipe_left (fun ( _70_15900 ) -> TProb (_70_15900)) _70_15901))
end
| (Support.Microsoft.FStar.Util.Inr (e1), Support.Microsoft.FStar.Util.Inr (e2)) -> begin
(let _70_15903 = (sub_prob e1 EQ e2 "effect arg")
in (Support.All.pipe_left (fun ( _70_15902 ) -> EProb (_70_15902)) _70_15903))
end
| _35_3053 -> begin
(Support.All.failwith "impossible")
end)) c1_comp.Microsoft_FStar_Absyn_Syntax.effect_args c2_comp.Microsoft_FStar_Absyn_Syntax.effect_args)
in (let guard = (let _70_15905 = (Support.List.map (fun ( p ) -> (Support.All.pipe_right (p_guard p) Support.Prims.fst)) sub_probs)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _70_15905))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in (match ((Support.Microsoft.FStar.Util.physical_equality c1 c2)) with
| true -> begin
(let _70_15906 = (solve_prob orig None [] wl)
in (solve env _70_15906))
end
| false -> begin
(let _35_3058 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_15908 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _70_15907 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (Support.Microsoft.FStar.Util.fprint3 "solve_c %s %s %s\n" _70_15908 (rel_to_string problem.relation) _70_15907)))
end
| false -> begin
()
end)
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let _35_3063 = (c1, c2)
in (match (_35_3063) with
| (c1_0, c2_0) -> begin
(match ((c1.Microsoft_FStar_Absyn_Syntax.n, c2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Total (t1), Microsoft_FStar_Absyn_Syntax.Total (t2)) -> begin
(solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl)
end
| (Microsoft_FStar_Absyn_Syntax.Total (_35_3070), Microsoft_FStar_Absyn_Syntax.Comp (_35_3073)) -> begin
(let _70_15910 = (let _35_3076 = problem
in (let _70_15909 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c1))
in {lhs = _70_15909; relation = _35_3076.relation; rhs = _35_3076.rhs; element = _35_3076.element; logical_guard = _35_3076.logical_guard; scope = _35_3076.scope; reason = _35_3076.reason; loc = _35_3076.loc; rank = _35_3076.rank}))
in (solve_c env _70_15910 wl))
end
| (Microsoft_FStar_Absyn_Syntax.Comp (_35_3079), Microsoft_FStar_Absyn_Syntax.Total (_35_3082)) -> begin
(let _70_15912 = (let _35_3085 = problem
in (let _70_15911 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c2))
in {lhs = _35_3085.lhs; relation = _35_3085.relation; rhs = _70_15911; element = _35_3085.element; logical_guard = _35_3085.logical_guard; scope = _35_3085.scope; reason = _35_3085.reason; loc = _35_3085.loc; rank = _35_3085.rank}))
in (solve_c env _70_15912 wl))
end
| (Microsoft_FStar_Absyn_Syntax.Comp (_35_3088), Microsoft_FStar_Absyn_Syntax.Comp (_35_3091)) -> begin
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
in (let _35_3098 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(Support.Microsoft.FStar.Util.fprint2 "solve_c for %s and %s\n" c1.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str c2.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str)
end
| false -> begin
()
end)
in (match ((Microsoft_FStar_Tc_Env.monad_leq env c1.Microsoft_FStar_Absyn_Syntax.effect_name c2.Microsoft_FStar_Absyn_Syntax.effect_name)) with
| None -> begin
(let _70_15915 = (let _70_15914 = (Microsoft_FStar_Absyn_Print.sli c1.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _70_15913 = (Microsoft_FStar_Absyn_Print.sli c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (Support.Microsoft.FStar.Util.format2 "incompatible monad ordering: %s </: %s" _70_15914 _70_15913)))
in (giveup env _70_15915 orig))
end
| Some (edge) -> begin
(match ((problem.relation = EQ)) with
| true -> begin
(let _35_3118 = (match (c1.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp1), _35_3111)::(Support.Microsoft.FStar.Util.Inl (wlp1), _35_3106)::[] -> begin
(wp1, wlp1)
end
| _35_3115 -> begin
(let _70_15918 = (let _70_15917 = (let _70_15916 = (Microsoft_FStar_Absyn_Syntax.range_of_lid c1.Microsoft_FStar_Absyn_Syntax.effect_name)
in (Support.Microsoft.FStar.Range.string_of_range _70_15916))
in (Support.Microsoft.FStar.Util.format1 "Unexpected number of indices on a normalized effect (%s)" _70_15917))
in (Support.All.failwith _70_15918))
end)
in (match (_35_3118) with
| (wp, wlp) -> begin
(let c1 = (let _70_15924 = (let _70_15923 = (let _70_15919 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wp)
in (Microsoft_FStar_Absyn_Syntax.targ _70_15919))
in (let _70_15922 = (let _70_15921 = (let _70_15920 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wlp)
in (Microsoft_FStar_Absyn_Syntax.targ _70_15920))
in (_70_15921)::[])
in (_70_15923)::_70_15922))
in {Microsoft_FStar_Absyn_Syntax.effect_name = c2.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = c1.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _70_15924; Microsoft_FStar_Absyn_Syntax.flags = c1.Microsoft_FStar_Absyn_Syntax.flags})
in (solve_eq c1 c2))
end))
end
| false -> begin
(let is_null_wp_2 = (Support.All.pipe_right c2.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _35_33 ) -> (match (_35_33) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.MLEFFECT) | (Microsoft_FStar_Absyn_Syntax.SOMETRIVIAL) -> begin
true
end
| _35_3125 -> begin
false
end))))
in (let _35_3148 = (match ((c1.Microsoft_FStar_Absyn_Syntax.effect_args, c2.Microsoft_FStar_Absyn_Syntax.effect_args)) with
| ((Support.Microsoft.FStar.Util.Inl (wp1), _35_3132)::_35_3128, (Support.Microsoft.FStar.Util.Inl (wp2), _35_3140)::_35_3136) -> begin
(wp1, wp2)
end
| _35_3145 -> begin
(let _70_15928 = (let _70_15927 = (Microsoft_FStar_Absyn_Print.sli c1.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _70_15926 = (Microsoft_FStar_Absyn_Print.sli c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (Support.Microsoft.FStar.Util.format2 "Got effects %s and %s, expected normalized effects" _70_15927 _70_15926)))
in (Support.All.failwith _70_15928))
end)
in (match (_35_3148) with
| (wpc1, wpc2) -> begin
(match ((Support.Microsoft.FStar.Util.physical_equality wpc1 wpc2)) with
| true -> begin
(solve_t env (problem_using_guard orig c1.Microsoft_FStar_Absyn_Syntax.result_typ problem.relation c2.Microsoft_FStar_Absyn_Syntax.result_typ None "result type") wl)
end
| false -> begin
(let c2_decl = (Microsoft_FStar_Tc_Env.get_effect_decl env c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let g = (match (is_null_wp_2) with
| true -> begin
(let _35_3150 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(Support.Microsoft.FStar.Util.print_string "Using trivial wp ... \n")
end
| false -> begin
()
end)
in (let _70_15934 = (let _70_15933 = (let _70_15932 = (Microsoft_FStar_Absyn_Syntax.targ c1.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _70_15931 = (let _70_15930 = (let _70_15929 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wpc1)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_15929))
in (_70_15930)::[])
in (_70_15932)::_70_15931))
in (c2_decl.Microsoft_FStar_Absyn_Syntax.trivial, _70_15933))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15934 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)))
end
| false -> begin
(let wp2_imp_wp1 = (let _70_15946 = (let _70_15945 = (let _70_15944 = (Microsoft_FStar_Absyn_Syntax.targ c2.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _70_15943 = (let _70_15942 = (Microsoft_FStar_Absyn_Syntax.targ wpc2)
in (let _70_15941 = (let _70_15940 = (let _70_15936 = (let _70_15935 = (Microsoft_FStar_Absyn_Const.kbin Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.imp_lid _70_15935))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_15936))
in (let _70_15939 = (let _70_15938 = (let _70_15937 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wpc1)
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _70_15937))
in (_70_15938)::[])
in (_70_15940)::_70_15939))
in (_70_15942)::_70_15941))
in (_70_15944)::_70_15943))
in (c2_decl.Microsoft_FStar_Absyn_Syntax.wp_binop, _70_15945))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15946 None r))
in (let _70_15951 = (let _70_15950 = (let _70_15949 = (Microsoft_FStar_Absyn_Syntax.targ c2.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _70_15948 = (let _70_15947 = (Microsoft_FStar_Absyn_Syntax.targ wp2_imp_wp1)
in (_70_15947)::[])
in (_70_15949)::_70_15948))
in (c2_decl.Microsoft_FStar_Absyn_Syntax.wp_as_type, _70_15950))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_15951 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)))
end)
in (let base_prob = (let _70_15953 = (sub_prob c1.Microsoft_FStar_Absyn_Syntax.result_typ problem.relation c2.Microsoft_FStar_Absyn_Syntax.result_typ "result type")
in (Support.All.pipe_left (fun ( _70_15952 ) -> TProb (_70_15952)) _70_15953))
in (let wl = (let _70_15957 = (let _70_15956 = (let _70_15955 = (Support.All.pipe_right (p_guard base_prob) Support.Prims.fst)
in (Microsoft_FStar_Absyn_Util.mk_conj _70_15955 g))
in (Support.All.pipe_left (fun ( _70_15954 ) -> Some (_70_15954)) _70_15956))
in (solve_prob orig _70_15957 [] wl))
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
| _35_3162 -> begin
(Support.All.failwith "Impossible")
end))
and solve_e' = (fun ( env ) ( problem ) ( wl ) -> (let problem = (let _35_3166 = problem
in {lhs = _35_3166.lhs; relation = EQ; rhs = _35_3166.rhs; element = _35_3166.element; logical_guard = _35_3166.logical_guard; scope = _35_3166.scope; reason = _35_3166.reason; loc = _35_3166.loc; rank = _35_3166.rank})
in (let e1 = problem.lhs
in (let e2 = problem.rhs
in (let orig = EProb (problem)
in (let sub_prob = (fun ( lhs ) ( rhs ) ( reason ) -> (mk_problem (p_scope orig) orig lhs EQ rhs None reason))
in (let _35_3178 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_15967 = (prob_to_string env orig)
in (Support.Microsoft.FStar.Util.fprint1 "Attempting:\n%s\n" _70_15967))
end
| false -> begin
()
end)
in (let flex_rigid = (fun ( _35_3185 ) ( e2 ) -> (match (_35_3185) with
| (e1, u1, t1, args1) -> begin
(let maybe_vars1 = (pat_vars env [] args1)
in (let sub_problems = (fun ( xs ) ( args2 ) -> (let _35_3212 = (let _70_15983 = (Support.All.pipe_right args2 (Support.List.map (fun ( _35_34 ) -> (match (_35_34) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (let _35_3199 = (new_tvar t.Microsoft_FStar_Absyn_Syntax.pos xs kk)
in (match (_35_3199) with
| (gi_xi, gi) -> begin
(let gi_pi = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (gi, args1) (Some (kk)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_15979 = (let _70_15978 = (sub_prob gi_pi t "type index")
in (Support.All.pipe_left (fun ( _70_15977 ) -> TProb (_70_15977)) _70_15978))
in ((Support.Microsoft.FStar.Util.Inl (gi_xi), imp), _70_15979)))
end)))
end
| (Support.Microsoft.FStar.Util.Inr (v), imp) -> begin
(let tt = (Microsoft_FStar_Tc_Recheck.recompute_typ v)
in (let _35_3208 = (new_evar v.Microsoft_FStar_Absyn_Syntax.pos xs tt)
in (match (_35_3208) with
| (gi_xi, gi) -> begin
(let gi_pi = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (gi, args1) (Some (tt)) v.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_15982 = (let _70_15981 = (sub_prob gi_pi v "expression index")
in (Support.All.pipe_left (fun ( _70_15980 ) -> EProb (_70_15980)) _70_15981))
in ((Support.Microsoft.FStar.Util.Inr (gi_xi), imp), _70_15982)))
end)))
end))))
in (Support.All.pipe_right _70_15983 Support.List.unzip))
in (match (_35_3212) with
| (gi_xi, gi_pi) -> begin
(let formula = (let _70_15985 = (Support.List.map (fun ( p ) -> (Support.All.pipe_right (p_guard p) Support.Prims.fst)) gi_pi)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _70_15985))
in (gi_xi, gi_pi, formula))
end)))
in (let project_e = (fun ( head2 ) ( args2 ) -> (let giveup = (fun ( reason ) -> (let _70_15992 = (Support.Microsoft.FStar.Util.format1 "flex-rigid: refusing to project expressions (%s)" reason)
in (giveup env _70_15992 orig)))
in (match ((let _70_15993 = (Microsoft_FStar_Absyn_Util.compress_exp head2)
in _70_15993.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (y) -> begin
(let _35_3229 = (match ((Microsoft_FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some ((xs, c)) -> begin
(xs, (Microsoft_FStar_Absyn_Util.comp_result c))
end)
in (match (_35_3229) with
| (all_xs, tres) -> begin
(match (((Support.List.length all_xs) <> (Support.List.length args1))) with
| true -> begin
(let _70_15996 = (let _70_15995 = (Microsoft_FStar_Absyn_Print.binders_to_string ", " all_xs)
in (let _70_15994 = (Microsoft_FStar_Absyn_Print.args_to_string args2)
in (Support.Microsoft.FStar.Util.format2 "unequal arity:\n\texpetced binders %s\n\tgot args {%s}" _70_15995 _70_15994)))
in (giveup _70_15996))
end
| false -> begin
(let rec aux = (fun ( xs ) ( args ) -> (match ((xs, args)) with
| ([], []) -> begin
(giveup "variable to project not found")
end
| (([], _)) | ((_, [])) -> begin
(Support.All.failwith "impossible")
end
| ((Support.Microsoft.FStar.Util.Inl (_35_3246), _35_3249)::xs, (Support.Microsoft.FStar.Util.Inl (_35_3254), _35_3257)::args) -> begin
(aux xs args)
end
| ((Support.Microsoft.FStar.Util.Inr (xi), _35_3265)::xs, (Support.Microsoft.FStar.Util.Inr (arg), _35_3272)::args) -> begin
(match ((let _70_16001 = (Microsoft_FStar_Absyn_Util.compress_exp arg)
in _70_16001.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (z) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvar_eq y z)) with
| true -> begin
(let _35_3281 = (sub_problems all_xs args2)
in (match (_35_3281) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (let _70_16005 = (let _70_16004 = (let _70_16003 = (let _70_16002 = (Microsoft_FStar_Absyn_Util.bvar_to_exp xi)
in (_70_16002, gi_xi))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _70_16003 None e1.Microsoft_FStar_Absyn_Syntax.pos))
in (all_xs, _70_16004))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _70_16005 None e1.Microsoft_FStar_Absyn_Syntax.pos))
in (let _35_3283 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_16009 = (Microsoft_FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _70_16008 = (Microsoft_FStar_Absyn_Print.exp_to_string sol)
in (let _70_16007 = (let _70_16006 = (Support.All.pipe_right gi_pi (Support.List.map (prob_to_string env)))
in (Support.All.pipe_right _70_16006 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.fprint3 "Projected: %s -> %s\nSubprobs=\n%s\n" _70_16009 _70_16008 _70_16007))))
end
| false -> begin
()
end)
in (let _70_16011 = (let _70_16010 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _70_16010))
in (solve env _70_16011))))
end))
end
| false -> begin
(aux xs args)
end)
end
| _35_3286 -> begin
(aux xs args)
end)
end
| (x::xs, arg::args) -> begin
(let _70_16014 = (let _70_16013 = (Microsoft_FStar_Absyn_Print.binder_to_string x)
in (let _70_16012 = (Microsoft_FStar_Absyn_Print.arg_to_string arg)
in (Support.Microsoft.FStar.Util.format2 "type incorrect term---impossible: expected %s; got %s\n" _70_16013 _70_16012)))
in (giveup _70_16014))
end))
in (aux (Support.List.rev all_xs) (Support.List.rev args1)))
end)
end))
end
| _35_3295 -> begin
(giveup "rigid head term is not a variable")
end)))
in (let imitate_or_project_e = (fun ( _35_3297 ) -> (match (()) with
| () -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid: not a pattern" orig wl))
end
| false -> begin
(let _35_3298 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_16018 = (Microsoft_FStar_Absyn_Print.exp_to_string e1)
in (let _70_16017 = (Microsoft_FStar_Absyn_Print.exp_to_string e2)
in (Support.Microsoft.FStar.Util.fprint2 "Imitating expressions: %s =?= %s\n" _70_16018 _70_16017)))
end
| false -> begin
()
end)
in (let _35_3302 = (Microsoft_FStar_Absyn_Util.head_and_args_e e2)
in (match (_35_3302) with
| (head2, args2) -> begin
(let fvhead = (Microsoft_FStar_Absyn_Util.freevars_exp head2)
in (let _35_3307 = (occurs_check_e env (u1, t1) head2)
in (match (_35_3307) with
| (occurs_ok, _35_3306) -> begin
(match (((Microsoft_FStar_Absyn_Util.fvs_included fvhead Microsoft_FStar_Absyn_Syntax.no_fvs) && occurs_ok)) with
| true -> begin
(let _35_3315 = (match ((Microsoft_FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some ((xs, c)) -> begin
(xs, (Microsoft_FStar_Absyn_Util.comp_result c))
end)
in (match (_35_3315) with
| (xs, tres) -> begin
(let _35_3319 = (sub_problems xs args2)
in (match (_35_3319) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (let body = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.Microsoft_FStar_Absyn_Syntax.pos)
in (match (xs) with
| [] -> begin
body
end
| _35_3323 -> begin
(let _70_16020 = (let _70_16019 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.Microsoft_FStar_Absyn_Syntax.pos)
in (xs, _70_16019))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _70_16020 None e1.Microsoft_FStar_Absyn_Syntax.pos))
end))
in (let _35_3325 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_16024 = (Microsoft_FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _70_16023 = (Microsoft_FStar_Absyn_Print.exp_to_string sol)
in (let _70_16022 = (let _70_16021 = (Support.All.pipe_right gi_pi (Support.List.map (prob_to_string env)))
in (Support.All.pipe_right _70_16021 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.fprint3 "Imitated: %s -> %s\nSubprobs=\n%s\n" _70_16024 _70_16023 _70_16022))))
end
| false -> begin
()
end)
in (let _70_16026 = (let _70_16025 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _70_16025))
in (solve env _70_16026))))
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
in (let _35_3337 = (occurs_check_e env (u1, t1) e2)
in (match (_35_3337) with
| (occurs_ok, _35_3336) -> begin
(match ((((Support.Microsoft.FStar.Util.set_is_subset_of fvs2.Microsoft_FStar_Absyn_Syntax.ftvs fvs1.Microsoft_FStar_Absyn_Syntax.ftvs) && (Support.Microsoft.FStar.Util.set_is_subset_of fvs2.Microsoft_FStar_Absyn_Syntax.fxvs fvs1.Microsoft_FStar_Absyn_Syntax.fxvs)) && occurs_ok)) with
| true -> begin
(let sol = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs' (xs, e2) None e1.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_16027 = (solve_prob orig None ((UE (((u1, t1), sol)))::[]) wl)
in (solve env _70_16027)))
end
| false -> begin
(imitate_or_project_e ())
end)
end))))
end)))))
end))
in (let flex_flex = (fun ( _35_3344 ) ( _35_3349 ) -> (match ((_35_3344, _35_3349)) with
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
in (let _35_3370 = (let _70_16032 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_evar _70_16032 zs tt))
in (match (_35_3370) with
| (u, _35_3369) -> begin
(let sub1 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (xs, u) (Some (t1)) e1.Microsoft_FStar_Absyn_Syntax.pos)
in (let sub2 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (ys, u) (Some (t2)) e1.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_16033 = (solve_prob orig None ((UE (((u1, t1), sub1)))::(UE (((u2, t2), sub2)))::[]) wl)
in (solve env _70_16033))))
end))))
end)
end)))
end))
in (let smt_fallback = (fun ( e1 ) ( e2 ) -> (match (wl.smt_ok) with
| true -> begin
(let _35_3376 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_16038 = (prob_to_string env orig)
in (Support.Microsoft.FStar.Util.fprint1 "Using SMT to solve:\n%s\n" _70_16038))
end
| false -> begin
()
end)
in (let _35_3381 = (let _70_16040 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_16039 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _70_16040 _70_16039 Microsoft_FStar_Absyn_Syntax.ktype)))
in (match (_35_3381) with
| (t, _35_3380) -> begin
(let _70_16044 = (let _70_16043 = (let _70_16042 = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (Support.All.pipe_left (fun ( _70_16041 ) -> Some (_70_16041)) _70_16042))
in (solve_prob orig _70_16043 [] wl))
in (solve env _70_16044))
end)))
end
| false -> begin
(giveup env "no SMT solution permitted" orig)
end))
in (match ((e1.Microsoft_FStar_Absyn_Syntax.n, e2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e1, _35_3384, _35_3386)), _35_3390) -> begin
(solve_e env (let _35_3392 = problem
in {lhs = e1; relation = _35_3392.relation; rhs = _35_3392.rhs; element = _35_3392.element; logical_guard = _35_3392.logical_guard; scope = _35_3392.scope; reason = _35_3392.reason; loc = _35_3392.loc; rank = _35_3392.rank}) wl)
end
| (_35_3395, Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e2, _35_3398, _35_3400))) -> begin
(solve_e env (let _35_3404 = problem
in {lhs = _35_3404.lhs; relation = _35_3404.relation; rhs = e2; element = _35_3404.element; logical_guard = _35_3404.logical_guard; scope = _35_3404.scope; reason = _35_3404.reason; loc = _35_3404.loc; rank = _35_3404.rank}) wl)
end
| ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) | ((Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) | ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) | ((Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) -> begin
(let _70_16046 = (destruct_flex_e e1)
in (let _70_16045 = (destruct_flex_e e2)
in (flex_flex _70_16046 _70_16045)))
end
| ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _)) -> begin
(let _70_16047 = (destruct_flex_e e1)
in (flex_rigid _70_16047 e2))
end
| ((_, Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) -> begin
(let _70_16048 = (destruct_flex_e e2)
in (flex_rigid _70_16048 e1))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (x1), Microsoft_FStar_Absyn_Syntax.Exp_bvar (x1')) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvd_eq x1.Microsoft_FStar_Absyn_Syntax.v x1'.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(let _70_16049 = (solve_prob orig None [] wl)
in (solve env _70_16049))
end
| false -> begin
(let _70_16055 = (let _70_16054 = (let _70_16053 = (let _70_16052 = (Microsoft_FStar_Tc_Recheck.recompute_typ e1)
in (let _70_16051 = (Microsoft_FStar_Tc_Recheck.recompute_typ e2)
in (Microsoft_FStar_Absyn_Util.mk_eq _70_16052 _70_16051 e1 e2)))
in (Support.All.pipe_left (fun ( _70_16050 ) -> Some (_70_16050)) _70_16053))
in (solve_prob orig _70_16054 [] wl))
in (solve env _70_16055))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv1, _35_3543)), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv1', _35_3548))) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv1.Microsoft_FStar_Absyn_Syntax.v fv1'.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(let _70_16056 = (solve_prob orig None [] wl)
in (solve env _70_16056))
end
| false -> begin
(giveup env "free-variables unequal" orig)
end)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_constant (s1), Microsoft_FStar_Absyn_Syntax.Exp_constant (s1')) -> begin
(let const_eq = (fun ( s1 ) ( s2 ) -> (match ((s1, s2)) with
| (Microsoft_FStar_Absyn_Syntax.Const_bytearray ((b1, _35_3562)), Microsoft_FStar_Absyn_Syntax.Const_bytearray ((b2, _35_3567))) -> begin
(b1 = b2)
end
| (Microsoft_FStar_Absyn_Syntax.Const_string ((b1, _35_3573)), Microsoft_FStar_Absyn_Syntax.Const_string ((b2, _35_3578))) -> begin
(b1 = b2)
end
| _35_3583 -> begin
(s1 = s2)
end))
in (match ((const_eq s1 s1')) with
| true -> begin
(let _70_16061 = (solve_prob orig None [] wl)
in (solve env _70_16061))
end
| false -> begin
(giveup env "constants unequal" orig)
end))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_35_3593); Microsoft_FStar_Absyn_Syntax.tk = _35_3591; Microsoft_FStar_Absyn_Syntax.pos = _35_3589; Microsoft_FStar_Absyn_Syntax.fvs = _35_3587; Microsoft_FStar_Absyn_Syntax.uvs = _35_3585}, _35_3597)), _35_3601) -> begin
(let _70_16063 = (let _35_3603 = problem
in (let _70_16062 = (whnf_e env e1)
in {lhs = _70_16062; relation = _35_3603.relation; rhs = _35_3603.rhs; element = _35_3603.element; logical_guard = _35_3603.logical_guard; scope = _35_3603.scope; reason = _35_3603.reason; loc = _35_3603.loc; rank = _35_3603.rank}))
in (solve_e env _70_16063 wl))
end
| (_35_3606, Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_35_3616); Microsoft_FStar_Absyn_Syntax.tk = _35_3614; Microsoft_FStar_Absyn_Syntax.pos = _35_3612; Microsoft_FStar_Absyn_Syntax.fvs = _35_3610; Microsoft_FStar_Absyn_Syntax.uvs = _35_3608}, _35_3620))) -> begin
(let _70_16065 = (let _35_3624 = problem
in (let _70_16064 = (whnf_e env e2)
in {lhs = _35_3624.lhs; relation = _35_3624.relation; rhs = _70_16064; element = _35_3624.element; logical_guard = _35_3624.logical_guard; scope = _35_3624.scope; reason = _35_3624.reason; loc = _35_3624.loc; rank = _35_3624.rank}))
in (solve_e env _70_16065 wl))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((head1, args1)), Microsoft_FStar_Absyn_Syntax.Exp_app ((head2, args2))) -> begin
(let orig_wl = wl
in (let rec solve_args = (fun ( sub_probs ) ( wl ) ( args1 ) ( args2 ) -> (match ((args1, args2)) with
| ([], []) -> begin
(let guard = (let _70_16075 = (let _70_16074 = (Support.List.map p_guard sub_probs)
in (Support.All.pipe_right _70_16074 (Support.List.map Support.Prims.fst)))
in (Microsoft_FStar_Absyn_Util.mk_conj_l _70_16075))
in (let g = (simplify_formula env guard)
in (let g = (Microsoft_FStar_Absyn_Util.compress_typ g)
in (match (g.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
(let _70_16076 = (solve_prob orig None wl.subst (let _35_3649 = orig_wl
in {attempting = _35_3649.attempting; deferred = _35_3649.deferred; subst = []; ctr = _35_3649.ctr; slack_vars = _35_3649.slack_vars; defer_ok = _35_3649.defer_ok; smt_ok = _35_3649.smt_ok; tcenv = _35_3649.tcenv}))
in (solve env _70_16076))
end
| _35_3652 -> begin
(let _35_3656 = (let _70_16078 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_16077 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _70_16078 _70_16077 Microsoft_FStar_Absyn_Syntax.ktype)))
in (match (_35_3656) with
| (t, _35_3655) -> begin
(let guard = (let _70_16079 = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (Microsoft_FStar_Absyn_Util.mk_disj g _70_16079))
in (let _70_16080 = (solve_prob orig (Some (guard)) wl.subst (let _35_3658 = orig_wl
in {attempting = _35_3658.attempting; deferred = _35_3658.deferred; subst = []; ctr = _35_3658.ctr; slack_vars = _35_3658.slack_vars; defer_ok = _35_3658.defer_ok; smt_ok = _35_3658.smt_ok; tcenv = _35_3658.tcenv}))
in (solve env _70_16080)))
end))
end))))
end
| (arg1::rest1, arg2::rest2) -> begin
(let prob = (match (((Support.Prims.fst arg1), (Support.Prims.fst arg2))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
(let _70_16082 = (mk_problem (p_scope orig) orig t1 EQ t2 None "expression type arg")
in (Support.All.pipe_left (fun ( _70_16081 ) -> TProb (_70_16081)) _70_16082))
end
| (Support.Microsoft.FStar.Util.Inr (e1), Support.Microsoft.FStar.Util.Inr (e2)) -> begin
(let _70_16084 = (mk_problem (p_scope orig) orig e1 EQ e2 None "expression arg")
in (Support.All.pipe_left (fun ( _70_16083 ) -> EProb (_70_16083)) _70_16084))
end
| _35_3678 -> begin
(Support.All.failwith "Impossible: ill-typed expression")
end)
in (match ((solve env (let _35_3680 = wl
in {attempting = (prob)::[]; deferred = []; subst = _35_3680.subst; ctr = _35_3680.ctr; slack_vars = _35_3680.slack_vars; defer_ok = false; smt_ok = false; tcenv = _35_3680.tcenv}))) with
| Failed (_35_3683) -> begin
(smt_fallback e1 e2)
end
| Success ((subst, _35_3687)) -> begin
(solve_args ((prob)::sub_probs) (let _35_3690 = wl
in {attempting = _35_3690.attempting; deferred = _35_3690.deferred; subst = subst; ctr = _35_3690.ctr; slack_vars = _35_3690.slack_vars; defer_ok = _35_3690.defer_ok; smt_ok = _35_3690.smt_ok; tcenv = _35_3690.tcenv}) rest1 rest2)
end))
end
| _35_3693 -> begin
(Support.All.failwith "Impossible: lengths defer")
end))
in (let rec match_head_and_args = (fun ( head1 ) ( head2 ) -> (match ((let _70_16092 = (let _70_16089 = (Microsoft_FStar_Absyn_Util.compress_exp head1)
in _70_16089.Microsoft_FStar_Absyn_Syntax.n)
in (let _70_16091 = (let _70_16090 = (Microsoft_FStar_Absyn_Util.compress_exp head2)
in _70_16090.Microsoft_FStar_Absyn_Syntax.n)
in (_70_16092, _70_16091)))) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (x), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) when ((Microsoft_FStar_Absyn_Util.bvar_eq x y) && ((Support.List.length args1) = (Support.List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _35_3704)), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((g, _35_3709))) when (((Microsoft_FStar_Absyn_Util.fvar_eq f g) && (not ((Microsoft_FStar_Absyn_Util.is_interpreted f.Microsoft_FStar_Absyn_Syntax.v)))) && ((Support.List.length args1) = (Support.List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _35_3715, _35_3717)), _35_3721) -> begin
(match_head_and_args e head2)
end
| (_35_3724, Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _35_3727, _35_3729))) -> begin
(match_head_and_args head1 e)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_abs (_35_3734), _35_3737) -> begin
(let _70_16094 = (let _35_3739 = problem
in (let _70_16093 = (whnf_e env e1)
in {lhs = _70_16093; relation = _35_3739.relation; rhs = _35_3739.rhs; element = _35_3739.element; logical_guard = _35_3739.logical_guard; scope = _35_3739.scope; reason = _35_3739.reason; loc = _35_3739.loc; rank = _35_3739.rank}))
in (solve_e env _70_16094 wl))
end
| (_35_3742, Microsoft_FStar_Absyn_Syntax.Exp_abs (_35_3744)) -> begin
(let _70_16096 = (let _35_3747 = problem
in (let _70_16095 = (whnf_e env e2)
in {lhs = _35_3747.lhs; relation = _35_3747.relation; rhs = _70_16095; element = _35_3747.element; logical_guard = _35_3747.logical_guard; scope = _35_3747.scope; reason = _35_3747.reason; loc = _35_3747.loc; rank = _35_3747.rank}))
in (solve_e env _70_16096 wl))
end
| _35_3750 -> begin
(smt_fallback e1 e2)
end))
in (match_head_and_args head1 head2))))
end
| _35_3752 -> begin
(let _35_3756 = (let _70_16098 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_16097 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _70_16098 _70_16097 Microsoft_FStar_Absyn_Syntax.ktype)))
in (match (_35_3756) with
| (t, _35_3755) -> begin
(let guard = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (let _35_3758 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_16099 = (Microsoft_FStar_Absyn_Print.typ_to_string guard)
in (Support.Microsoft.FStar.Util.fprint1 "Emitting guard %s\n" _70_16099))
end
| false -> begin
()
end)
in (let _70_16103 = (let _70_16102 = (let _70_16101 = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (Support.All.pipe_left (fun ( _70_16100 ) -> Some (_70_16100)) _70_16101))
in (solve_prob orig _70_16102 [] wl))
in (solve env _70_16103))))
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

let ___NonTrivial____0 = (fun ( projectee ) -> (match (projectee) with
| NonTrivial (_35_3762) -> begin
_35_3762
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
in (let carry = (let _70_16134 = (Support.List.map (fun ( _35_3776 ) -> (match (_35_3776) with
| (_35_3774, x) -> begin
(prob_to_string env x)
end)) g.deferred.carry)
in (Support.All.pipe_right _70_16134 (Support.String.concat ",\n")))
in (Support.Microsoft.FStar.Util.format2 "\n\t{guard_f=%s;\n\t deferred={\n%s};}\n" form carry))))

let guard_of_guard_formula = (fun ( g ) -> {guard_f = g; deferred = {carry = []; slack = []}; implicits = []})

let guard_f = (fun ( g ) -> g.guard_f)

let is_trivial = (fun ( g ) -> (match (g) with
| {guard_f = Trivial; deferred = {carry = []; slack = []}; implicits = _35_3782} -> begin
true
end
| _35_3789 -> begin
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
| _35_3805 -> begin
(Support.All.failwith "impossible")
end)
in (let _70_16151 = (let _35_3807 = g
in (let _70_16150 = (let _70_16149 = (let _70_16148 = (let _70_16147 = (let _70_16146 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_70_16146)::[])
in (_70_16147, f))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_16148 None f.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.All.pipe_left (fun ( _70_16145 ) -> NonTrivial (_70_16145)) _70_16149))
in {guard_f = _70_16150; deferred = _35_3807.deferred; implicits = _35_3807.implicits}))
in Some (_70_16151)))
end))

let apply_guard = (fun ( g ) ( e ) -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _35_3814 = g
in (let _70_16163 = (let _70_16162 = (let _70_16161 = (let _70_16160 = (let _70_16159 = (let _70_16158 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_70_16158)::[])
in (f, _70_16159))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_16160))
in (Support.All.pipe_left (Microsoft_FStar_Absyn_Syntax.syn f.Microsoft_FStar_Absyn_Syntax.pos (Some (Microsoft_FStar_Absyn_Syntax.ktype))) _70_16161))
in NonTrivial (_70_16162))
in {guard_f = _70_16163; deferred = _35_3814.deferred; implicits = _35_3814.implicits}))
end))

let trivial = (fun ( t ) -> (match (t) with
| Trivial -> begin
()
end
| NonTrivial (_35_3819) -> begin
(Support.All.failwith "impossible")
end))

let conj_guard_f = (fun ( g1 ) ( g2 ) -> (match ((g1, g2)) with
| ((Trivial, g)) | ((g, Trivial)) -> begin
g
end
| (NonTrivial (f1), NonTrivial (f2)) -> begin
(let _70_16170 = (Microsoft_FStar_Absyn_Util.mk_conj f1 f2)
in NonTrivial (_70_16170))
end))

let check_trivial = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _35_3837 -> begin
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

let binop_guard = (fun ( f ) ( g1 ) ( g2 ) -> (let _70_16193 = (f g1.guard_f g2.guard_f)
in {guard_f = _70_16193; deferred = {carry = (Support.List.append g1.deferred.carry g2.deferred.carry); slack = (Support.List.append g1.deferred.slack g2.deferred.slack)}; implicits = (Support.List.append g1.implicits g2.implicits)}))

let conj_guard = (fun ( g1 ) ( g2 ) -> (binop_guard conj_guard_f g1 g2))

let imp_guard = (fun ( g1 ) ( g2 ) -> (binop_guard imp_guard_f g1 g2))

let close_guard = (fun ( binders ) ( g ) -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _35_3864 = g
in (let _70_16208 = (let _70_16207 = (Microsoft_FStar_Absyn_Util.close_forall binders f)
in (Support.All.pipe_right _70_16207 (fun ( _70_16206 ) -> NonTrivial (_70_16206))))
in {guard_f = _70_16208; deferred = _35_3864.deferred; implicits = _35_3864.implicits}))
end))

let mk_guard = (fun ( g ) ( ps ) ( slack ) ( locs ) -> {guard_f = g; deferred = {carry = ps; slack = slack}; implicits = []})

let new_t_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) -> (let reason = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _70_16220 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env lhs)
in (let _70_16219 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env rhs)
in (Support.Microsoft.FStar.Util.format3 "Top-level:\n%s\n\t%s\n%s" _70_16220 (rel_to_string rel) _70_16219)))
end
| false -> begin
"TOP"
end)
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

let new_t_prob = (fun ( env ) ( t1 ) ( rel ) ( t2 ) -> (let x = (let _70_16229 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p _70_16229 t1))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))))
in (let p = (let _70_16233 = (let _70_16231 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.All.pipe_left (fun ( _70_16230 ) -> Some (_70_16230)) _70_16231))
in (let _70_16232 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_t_problem env t1 rel t2 _70_16233 _70_16232)))
in (TProb (p), x)))))

let new_k_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) -> (let reason = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _70_16241 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env lhs)
in (let _70_16240 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env rhs)
in (Support.Microsoft.FStar.Util.format3 "Top-level:\n%s\n\t%s\n%s" _70_16241 (rel_to_string rel) _70_16240)))
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
(let _35_3898 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _70_16246 = (Microsoft_FStar_Absyn_Print.typ_to_string f)
in (Support.Microsoft.FStar.Util.fprint1 "Simplifying guard %s\n" _70_16246))
end
| false -> begin
()
end)
in (let f = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env f)
in (let f = (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _35_3904 -> begin
NonTrivial (f)
end)
in (let _35_3906 = g
in {guard_f = f; deferred = _35_3906.deferred; implicits = _35_3906.implicits}))))
end))

let solve_and_commit = (fun ( env ) ( probs ) ( err ) -> (let probs = (match ((Support.ST.read Microsoft_FStar_Options.eager_inference)) with
| true -> begin
(let _35_3911 = probs
in {attempting = _35_3911.attempting; deferred = _35_3911.deferred; subst = _35_3911.subst; ctr = _35_3911.ctr; slack_vars = _35_3911.slack_vars; defer_ok = false; smt_ok = _35_3911.smt_ok; tcenv = _35_3911.tcenv})
end
| false -> begin
probs
end)
in (let sol = (solve env probs)
in (match (sol) with
| Success ((s, deferred)) -> begin
(let _35_3919 = (commit env s)
in Some (deferred))
end
| Failed ((d, s)) -> begin
(let _35_3925 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _70_16258 = (explain env d s)
in (Support.All.pipe_left Support.Microsoft.FStar.Util.print_string _70_16258))
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
(let _70_16270 = (let _70_16269 = (let _70_16268 = (let _70_16267 = (Support.All.pipe_right (p_guard prob) Support.Prims.fst)
in (Support.All.pipe_right _70_16267 (fun ( _70_16266 ) -> NonTrivial (_70_16266))))
in {guard_f = _70_16268; deferred = d; implicits = []})
in (simplify_guard env _70_16269))
in (Support.All.pipe_left (fun ( _70_16265 ) -> Some (_70_16265)) _70_16270))
end))

let try_keq = (fun ( env ) ( k1 ) ( k2 ) -> (let _35_3936 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_16278 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (let _70_16277 = (Microsoft_FStar_Absyn_Print.kind_to_string k2)
in (Support.Microsoft.FStar.Util.fprint2 "try_keq of %s and %s\n" _70_16278 _70_16277)))
end
| false -> begin
()
end)
in (let prob = (let _70_16283 = (let _70_16282 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env k1)
in (let _70_16281 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env k2)
in (let _70_16280 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_k_problem env _70_16282 EQ _70_16281 None _70_16280))))
in (Support.All.pipe_left (fun ( _70_16279 ) -> KProb (_70_16279)) _70_16283))
in (let _70_16285 = (solve_and_commit env (singleton env prob) (fun ( _35_3939 ) -> None))
in (Support.All.pipe_left (with_guard env prob) _70_16285)))))

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
(let _70_16296 = (let _70_16295 = (let _70_16294 = (Microsoft_FStar_Tc_Errors.incompatible_kinds env k2 k1)
in (_70_16294, r))
in Microsoft_FStar_Absyn_Syntax.Error (_70_16295))
in (raise (_70_16296)))
end
| Some (t) -> begin
(let _70_16299 = (let _70_16298 = (let _70_16297 = (Microsoft_FStar_Tc_Errors.expected_typ_of_kind env k2 t k1)
in (_70_16297, r))
in Microsoft_FStar_Absyn_Syntax.Error (_70_16298))
in (raise (_70_16299)))
end))
end
| Some (g) -> begin
g
end))

let subkind = (fun ( env ) ( k1 ) ( k2 ) -> (let _35_3958 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_16309 = (let _70_16306 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _70_16306))
in (let _70_16308 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (let _70_16307 = (Microsoft_FStar_Absyn_Print.kind_to_string k2)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) subkind of %s and %s\n" _70_16309 _70_16308 _70_16307))))
end
| false -> begin
()
end)
in (let prob = (let _70_16314 = (let _70_16313 = (whnf_k env k1)
in (let _70_16312 = (whnf_k env k2)
in (let _70_16311 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_k_problem env _70_16313 SUB _70_16312 None _70_16311))))
in (Support.All.pipe_left (fun ( _70_16310 ) -> KProb (_70_16310)) _70_16314))
in (let res = (let _70_16321 = (let _70_16320 = (solve_and_commit env (singleton env prob) (fun ( _35_3961 ) -> (let _70_16319 = (let _70_16318 = (let _70_16317 = (Microsoft_FStar_Tc_Errors.incompatible_kinds env k1 k2)
in (let _70_16316 = (Microsoft_FStar_Tc_Env.get_range env)
in (_70_16317, _70_16316)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_16318))
in (raise (_70_16319)))))
in (Support.All.pipe_left (with_guard env prob) _70_16320))
in (Support.Microsoft.FStar.Util.must _70_16321))
in res))))

let try_teq = (fun ( env ) ( t1 ) ( t2 ) -> (let _35_3967 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_16329 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _70_16328 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (Support.Microsoft.FStar.Util.fprint2 "try_teq of %s and %s\n" _70_16329 _70_16328)))
end
| false -> begin
()
end)
in (let prob = (let _70_16332 = (let _70_16331 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_t_problem env t1 EQ t2 None _70_16331))
in (Support.All.pipe_left (fun ( _70_16330 ) -> TProb (_70_16330)) _70_16332))
in (let g = (let _70_16334 = (solve_and_commit env (singleton env prob) (fun ( _35_3970 ) -> None))
in (Support.All.pipe_left (with_guard env prob) _70_16334))
in g))))

let teq = (fun ( env ) ( t1 ) ( t2 ) -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _70_16344 = (let _70_16343 = (let _70_16342 = (Microsoft_FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _70_16341 = (Microsoft_FStar_Tc_Env.get_range env)
in (_70_16342, _70_16341)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_16343))
in (raise (_70_16344)))
end
| Some (g) -> begin
(let _35_3979 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_16347 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _70_16346 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (let _70_16345 = (guard_to_string env g)
in (Support.Microsoft.FStar.Util.fprint3 "teq of %s and %s succeeded with guard %s\n" _70_16347 _70_16346 _70_16345))))
end
| false -> begin
()
end)
in g)
end))

let try_subtype = (fun ( env ) ( t1 ) ( t2 ) -> (let _35_3984 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_16355 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _70_16354 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.fprint2 "try_subtype of %s and %s\n" _70_16355 _70_16354)))
end
| false -> begin
()
end)
in (let _35_3988 = (new_t_prob env t1 SUB t2)
in (match (_35_3988) with
| (prob, x) -> begin
(let g = (let _70_16357 = (solve_and_commit env (singleton env prob) (fun ( _35_3989 ) -> None))
in (Support.All.pipe_left (with_guard env prob) _70_16357))
in (let _35_3992 = (match (((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) && (Support.Microsoft.FStar.Util.is_some g))) with
| true -> begin
(let _70_16361 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _70_16360 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _70_16359 = (let _70_16358 = (Support.Microsoft.FStar.Util.must g)
in (guard_to_string env _70_16358))
in (Support.Microsoft.FStar.Util.fprint3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _70_16361 _70_16360 _70_16359))))
end
| false -> begin
()
end)
in (abstract_guard x g)))
end))))

let subtype_fail = (fun ( env ) ( t1 ) ( t2 ) -> (let _70_16368 = (let _70_16367 = (let _70_16366 = (Microsoft_FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _70_16365 = (Microsoft_FStar_Tc_Env.get_range env)
in (_70_16366, _70_16365)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_16367))
in (raise (_70_16368))))

let subtype = (fun ( env ) ( t1 ) ( t2 ) -> (match ((try_subtype env t1 t2)) with
| Some (f) -> begin
f
end
| None -> begin
(subtype_fail env t1 t2)
end))

let sub_comp = (fun ( env ) ( c1 ) ( c2 ) -> (let _35_4006 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_16382 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _70_16381 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (Support.Microsoft.FStar.Util.fprint2 "sub_comp of %s and %s\n" _70_16382 _70_16381)))
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
in (let prob = (let _70_16385 = (let _70_16384 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_problem env c1 rel c2 None _70_16384 "sub_comp"))
in (Support.All.pipe_left (fun ( _70_16383 ) -> CProb (_70_16383)) _70_16385))
in (let _70_16387 = (solve_and_commit env (singleton env prob) (fun ( _35_4010 ) -> None))
in (Support.All.pipe_left (with_guard env prob) _70_16387))))))

let solve_deferred_constraints = (fun ( env ) ( g ) -> (let fail = (fun ( _35_4017 ) -> (match (_35_4017) with
| (d, s) -> begin
(let msg = (explain env d s)
in (raise (Microsoft_FStar_Absyn_Syntax.Error ((msg, (p_loc d))))))
end))
in (let _35_4022 = (match (((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel"))) && ((Support.List.length g.deferred.carry) <> 0))) with
| true -> begin
(let _70_16400 = (let _70_16399 = (Support.All.pipe_right g.deferred.carry (Support.List.map (fun ( _35_4021 ) -> (match (_35_4021) with
| (msg, x) -> begin
(let _70_16398 = (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range (p_loc x))
in (let _70_16397 = (prob_to_string env x)
in (let _70_16396 = (let _70_16395 = (Support.All.pipe_right (p_guard x) Support.Prims.fst)
in (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env _70_16395))
in (Support.Microsoft.FStar.Util.format4 "(At %s) %s\n%s\nguard is %s\n" _70_16398 msg _70_16397 _70_16396))))
end))))
in (Support.All.pipe_right _70_16399 (Support.String.concat "\n")))
in (Support.All.pipe_left (Support.Microsoft.FStar.Util.fprint1 "Trying to solve carried problems: begin\n%s\nend\n") _70_16400))
end
| false -> begin
()
end)
in (let gopt = (let _70_16401 = (wl_of_guard env g.deferred)
in (solve_and_commit env _70_16401 fail))
in (match (gopt) with
| Some ({carry = _35_4027; slack = slack}) -> begin
(let _35_4030 = (fix_slack_vars slack)
in (let _35_4032 = g
in {guard_f = _35_4032.guard_f; deferred = no_deferred; implicits = _35_4032.implicits}))
end
| _35_4035 -> begin
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
(let _35_4046 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _70_16408 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _70_16407 = (let _70_16406 = (Microsoft_FStar_Absyn_Print.formula_to_string vc)
in (Support.Microsoft.FStar.Util.format1 "Checking VC=\n%s\n" _70_16406))
in (Microsoft_FStar_Tc_Errors.diag _70_16408 _70_16407)))
end
| false -> begin
()
end)
in (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.solve env vc))
end))
end)
end)))




