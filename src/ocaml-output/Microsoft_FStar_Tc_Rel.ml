
let new_kvar = (fun ( r ) ( binders ) -> (let wf = (fun ( k ) ( _33_39 ) -> (match (()) with
| () -> begin
true
end))
in (let u = (Support.Microsoft.FStar.Unionfind.fresh Microsoft_FStar_Absyn_Syntax.Uvar)
in (let _52_9467 = (let _52_9466 = (let _52_9465 = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (u, _52_9465))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar _52_9466 r))
in (_52_9467, u)))))

let new_tvar = (fun ( r ) ( binders ) ( k ) -> (let wf = (fun ( t ) ( tk ) -> true)
in (let binders = (Support.Prims.pipe_right binders (Support.List.filter (fun ( x ) -> (let _52_9479 = (Microsoft_FStar_Absyn_Syntax.is_null_binder x)
in (Support.Prims.pipe_right _52_9479 Support.Prims.op_Negation)))))
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
in (let _52_9480 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (uv, args) None r)
in (_52_9480, uv)))))
end)))))

let new_evar = (fun ( r ) ( binders ) ( t ) -> (let wf = (fun ( e ) ( t ) -> true)
in (let binders = (Support.Prims.pipe_right binders (Support.List.filter (fun ( x ) -> (let _52_9492 = (Microsoft_FStar_Absyn_Syntax.is_null_binder x)
in (Support.Prims.pipe_right _52_9492 Support.Prims.op_Negation)))))
in (let uv = (Support.Microsoft.FStar.Unionfind.fresh Microsoft_FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (Microsoft_FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t) None r)
in (uv, uv))
end
| _ -> begin
(let args = (Microsoft_FStar_Absyn_Util.args_of_non_null_binders binders)
in (let t' = (let _52_9494 = (let _52_9493 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (binders, _52_9493))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _52_9494 None r))
in (let uv = (Microsoft_FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t') None r)
in (match (args) with
| [] -> begin
(uv, uv)
end
| _ -> begin
(let _52_9495 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (uv, args) None r)
in (_52_9495, uv))
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
(let _52_9634 = (Microsoft_FStar_Absyn_Print.kind_to_string p.lhs)
in (let _52_9633 = (Microsoft_FStar_Absyn_Print.kind_to_string p.rhs)
in (Support.Microsoft.FStar.Util.format3 "\t%s\n\t\t%s\n\t%s" _52_9634 (rel_to_string p.relation) _52_9633)))
end
| TProb (p) -> begin
(let _52_9647 = (let _52_9646 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env p.lhs)
in (let _52_9645 = (let _52_9644 = (Microsoft_FStar_Absyn_Print.tag_of_typ p.lhs)
in (let _52_9643 = (let _52_9642 = (let _52_9641 = (Support.Prims.pipe_right p.reason Support.List.hd)
in (let _52_9640 = (let _52_9639 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env p.rhs)
in (let _52_9638 = (let _52_9637 = (Microsoft_FStar_Absyn_Print.tag_of_typ p.rhs)
in (let _52_9636 = (let _52_9635 = (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env (Support.Prims.fst p.logical_guard))
in (_52_9635)::[])
in (_52_9637)::_52_9636))
in (_52_9639)::_52_9638))
in (_52_9641)::_52_9640))
in ((rel_to_string p.relation))::_52_9642)
in (_52_9644)::_52_9643))
in (_52_9646)::_52_9645))
in (Support.Microsoft.FStar.Util.format "\t%s (%s) \n\t\t%s(%s)\n\t%s (%s) (guard %s)" _52_9647))
end
| EProb (p) -> begin
(let _52_9649 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env p.lhs)
in (let _52_9648 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env p.rhs)
in (Support.Microsoft.FStar.Util.format3 "\t%s \n\t\t%s\n\t%s" _52_9649 (rel_to_string p.relation) _52_9648)))
end
| CProb (p) -> begin
(let _52_9651 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env p.lhs)
in (let _52_9650 = (Microsoft_FStar_Tc_Normalize.comp_typ_norm_to_string env p.rhs)
in (Support.Microsoft.FStar.Util.format3 "\t%s \n\t\t%s\n\t%s" _52_9651 (rel_to_string p.relation) _52_9650)))
end))

let uvi_to_string = (fun ( env ) ( uvi ) -> (let str = (fun ( u ) -> (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _52_9657 = (Support.Microsoft.FStar.Unionfind.uvar_id u)
in (Support.Prims.pipe_right _52_9657 Support.Microsoft.FStar.Util.string_of_int))
end))
in (match (uvi) with
| UK ((u, _)) -> begin
(let _52_9658 = (str u)
in (Support.Prims.pipe_right _52_9658 (Support.Microsoft.FStar.Util.format1 "UK %s")))
end
| UT (((u, _), t)) -> begin
(let _52_9661 = (str u)
in (Support.Prims.pipe_right _52_9661 (fun ( x ) -> (let _52_9660 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.format2 "UT %s %s" x _52_9660)))))
end
| UE (((u, _), _)) -> begin
(let _52_9662 = (str u)
in (Support.Prims.pipe_right _52_9662 (Support.Microsoft.FStar.Util.format1 "UE %s")))
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
(Support.Prims.pipe_right (maybe_invert p) (fun ( _52_9669 ) -> KProb (_52_9669)))
end
| TProb (p) -> begin
(Support.Prims.pipe_right (maybe_invert p) (fun ( _52_9670 ) -> TProb (_52_9670)))
end
| EProb (p) -> begin
(Support.Prims.pipe_right (maybe_invert p) (fun ( _52_9671 ) -> EProb (_52_9671)))
end
| CProb (p) -> begin
(Support.Prims.pipe_right (maybe_invert p) (fun ( _52_9672 ) -> CProb (_52_9672)))
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
(Support.Prims.pipe_left (fun ( _52_9691 ) -> KProb (_52_9691)) (invert p))
end
| TProb (p) -> begin
(Support.Prims.pipe_left (fun ( _52_9692 ) -> TProb (_52_9692)) (invert p))
end
| EProb (p) -> begin
(Support.Prims.pipe_left (fun ( _52_9693 ) -> EProb (_52_9693)) (invert p))
end
| CProb (p) -> begin
(Support.Prims.pipe_left (fun ( _52_9694 ) -> CProb (_52_9694)) (invert p))
end))

let is_top_level_prob = (fun ( p ) -> (let _52_9697 = (Support.Prims.pipe_right (p_reason p) Support.List.length)
in (_52_9697 = 1)))

let mk_problem = (fun ( scope ) ( orig ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( reason ) -> (let _52_9705 = (new_tvar (p_loc orig) scope Microsoft_FStar_Absyn_Syntax.ktype)
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _52_9705; scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None}))

let new_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) ( reason ) -> (let _52_9715 = (let _52_9714 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _52_9713 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _52_9714 _52_9713 Microsoft_FStar_Absyn_Syntax.ktype)))
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _52_9715; scope = []; reason = (reason)::[]; loc = loc; rank = None}))

let problem_using_guard = (fun ( orig ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( reason ) -> {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = (p_guard orig); scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None})

let guard_on_element = (fun ( problem ) ( x ) ( phi ) -> (match (problem.element) with
| None -> begin
(let _52_9726 = (let _52_9725 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_52_9725)::[])
in (Microsoft_FStar_Absyn_Util.close_forall _52_9726 phi))
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
(let _33_292 = (match ((let _52_9737 = (Microsoft_FStar_Absyn_Util.compress_typ uv)
in _52_9737.Microsoft_FStar_Absyn_Syntax.n)) with
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
(let _52_9739 = (let _52_9738 = (Support.List.map (uvi_to_string wl.tcenv) uvis)
in (Support.Prims.pipe_right _52_9738 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.fprint1 "Extending solution: %s\n" _52_9739))
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

let explain = (fun ( env ) ( d ) ( s ) -> (let _52_9760 = (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range (p_loc d))
in (let _52_9759 = (prob_to_string env d)
in (let _52_9758 = (Support.Prims.pipe_right (p_reason d) (Support.String.concat "\n\t>"))
in (Support.Microsoft.FStar.Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _52_9760 _52_9759 _52_9758 s)))))

let empty_worklist = (fun ( env ) -> {attempting = []; deferred = []; subst = []; ctr = 0; slack_vars = []; defer_ok = true; smt_ok = true; tcenv = env})

let singleton = (fun ( env ) ( prob ) -> (let _33_315 = (empty_worklist env)
in {attempting = (prob)::[]; deferred = _33_315.deferred; subst = _33_315.subst; ctr = _33_315.ctr; slack_vars = _33_315.slack_vars; defer_ok = _33_315.defer_ok; smt_ok = _33_315.smt_ok; tcenv = _33_315.tcenv}))

let wl_of_guard = (fun ( env ) ( g ) -> (let _33_319 = (empty_worklist env)
in (let _52_9771 = (Support.List.map Support.Prims.snd g.carry)
in {attempting = _52_9771; deferred = _33_319.deferred; subst = _33_319.subst; ctr = _33_319.ctr; slack_vars = g.slack; defer_ok = false; smt_ok = _33_319.smt_ok; tcenv = _33_319.tcenv})))

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
(let _52_9796 = (prob_to_string env prob)
in (Support.Microsoft.FStar.Util.fprint2 "Failed %s:\n%s\n" reason _52_9796))
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
(let _52_9827 = (let _52_9826 = (norm_targ env t)
in (Support.Prims.pipe_left (fun ( _52_9825 ) -> Support.Microsoft.FStar.Util.Inl (_52_9825)) _52_9826))
in (_52_9827, (Support.Prims.snd a)))
end
| Support.Microsoft.FStar.Util.Inr (v) -> begin
(let _52_9830 = (let _52_9829 = (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env v)
in (Support.Prims.pipe_left (fun ( _52_9828 ) -> Support.Microsoft.FStar.Util.Inr (_52_9828)) _52_9829))
in (_52_9830, (Support.Prims.snd a)))
end))

let whnf = (fun ( env ) ( t ) -> (let _52_9835 = (Microsoft_FStar_Tc_Normalize.whnf env t)
in (Support.Prims.pipe_right _52_9835 Microsoft_FStar_Absyn_Util.compress_typ)))

let sn = (fun ( env ) ( t ) -> (let _52_9840 = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::[]) env t)
in (Support.Prims.pipe_right _52_9840 Microsoft_FStar_Absyn_Util.compress_typ)))

let sn_binders = (fun ( env ) ( binders ) -> (Support.Prims.pipe_right binders (Support.List.map (fun ( _33_17 ) -> (match (_33_17) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _52_9846 = (let _52_9845 = (let _33_417 = a
in (let _52_9844 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env a.Microsoft_FStar_Absyn_Syntax.sort)
in {Microsoft_FStar_Absyn_Syntax.v = _33_417.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _52_9844; Microsoft_FStar_Absyn_Syntax.p = _33_417.Microsoft_FStar_Absyn_Syntax.p}))
in Support.Microsoft.FStar.Util.Inl (_52_9845))
in (_52_9846, imp))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _52_9849 = (let _52_9848 = (let _33_423 = x
in (let _52_9847 = (norm_targ env x.Microsoft_FStar_Absyn_Syntax.sort)
in {Microsoft_FStar_Absyn_Syntax.v = _33_423.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _52_9847; Microsoft_FStar_Absyn_Syntax.p = _33_423.Microsoft_FStar_Absyn_Syntax.p}))
in Support.Microsoft.FStar.Util.Inr (_52_9848))
in (_52_9849, imp))
end)))))

let whnf_k = (fun ( env ) ( k ) -> (let _52_9854 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.WHNF)::[]) env k)
in (Support.Prims.pipe_right _52_9854 Microsoft_FStar_Absyn_Util.compress_kind)))

let whnf_e = (fun ( env ) ( e ) -> (let _52_9859 = (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.WHNF)::[]) env e)
in (Support.Prims.pipe_right _52_9859 Microsoft_FStar_Absyn_Util.compress_exp)))

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
(let k = (let _52_9866 = (Microsoft_FStar_Absyn_Util.subst_of_list formals actuals)
in (Microsoft_FStar_Absyn_Util.subst_kind _52_9866 body))
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

let rec compress = (fun ( env ) ( wl ) ( t ) -> (let t = (let _52_9873 = (Microsoft_FStar_Absyn_Util.unmeta_typ t)
in (whnf env _52_9873))
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

let normalize_refinement = (fun ( env ) ( wl ) ( t0 ) -> (let _52_9886 = (compress env wl t0)
in (Microsoft_FStar_Tc_Normalize.normalize_refinement env _52_9886)))

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
(let _52_9899 = (let _52_9898 = (Microsoft_FStar_Absyn_Print.typ_to_string tt)
in (let _52_9897 = (Microsoft_FStar_Absyn_Print.tag_of_typ tt)
in (Support.Microsoft.FStar.Util.format2 "impossible: Got %s ... %s\n" _52_9898 _52_9897)))
in (failwith (_52_9899)))
end)
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (_)) -> begin
(match (norm) with
| true -> begin
(t1, None)
end
| false -> begin
(let _33_554 = (let _52_9900 = (normalize_refinement env wl t1)
in (aux true _52_9900))
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
(let _52_9903 = (let _52_9902 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _52_9901 = (Microsoft_FStar_Absyn_Print.tag_of_typ t1)
in (Support.Microsoft.FStar.Util.format2 "impossible (outer): Got %s ... %s\n" _52_9902 _52_9901)))
in (failwith (_52_9903)))
end))
in (let _52_9904 = (compress env wl t1)
in (aux false _52_9904))))

let unrefine = (fun ( env ) ( t ) -> (let _52_9909 = (base_and_refinement env (empty_worklist env) t)
in (Support.Prims.pipe_right _52_9909 Support.Prims.fst)))

let trivial_refinement = (fun ( t ) -> (let _52_9911 = (Microsoft_FStar_Absyn_Util.gen_bvar_p t.Microsoft_FStar_Absyn_Syntax.pos t)
in (_52_9911, Microsoft_FStar_Absyn_Util.t_true)))

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
in (let _52_9925 = (Support.Prims.pipe_right uvs.Microsoft_FStar_Absyn_Syntax.uvars_t Support.Microsoft.FStar.Util.set_elements)
in (Support.Prims.pipe_right _52_9925 (Support.Microsoft.FStar.Util.for_some (fun ( _33_613 ) -> (match (_33_613) with
| (uvt, _) -> begin
(match ((find_uvar_t uvt wl.subst)) with
| None -> begin
(Support.Microsoft.FStar.Unionfind.equivalent uvt (Support.Prims.fst uk))
end
| Some (t) -> begin
(Obj.magic (let t = (match ((Microsoft_FStar_Absyn_Util.compress_typ t)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((_, t)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
t
end
| t -> begin
t
end)
in (occurs (Obj.magic uk) (Obj.magic t))))
end)
end)))))))

let occurs_check = (fun ( env ) ( wl ) ( uk ) ( t ) -> (let occurs_ok = (let _52_9934 = (occurs env wl uk t)
in (not (_52_9934)))
in (let msg = (match (occurs_ok) with
| true -> begin
None
end
| false -> begin
(let _52_9939 = (let _52_9938 = (Microsoft_FStar_Absyn_Print.uvar_t_to_string uk)
in (let _52_9937 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (let _52_9936 = (let _52_9935 = (Support.Prims.pipe_right wl.subst (Support.List.map (uvi_to_string env)))
in (Support.Prims.pipe_right _52_9935 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format3 "occurs-check failed (%s occurs in %s) (with substitution %s)" _52_9938 _52_9937 _52_9936))))
in Some (_52_9939))
end)
in (occurs_ok, msg))))

let occurs_and_freevars_check = (fun ( env ) ( wl ) ( uk ) ( fvs ) ( t ) -> (let fvs_t = (Microsoft_FStar_Absyn_Util.freevars_typ t)
in (let _33_647 = (occurs_check env wl uk t)
in (match (_33_647) with
| (occurs_ok, msg) -> begin
(let _52_9950 = (Microsoft_FStar_Absyn_Util.fvs_included fvs_t fvs)
in (occurs_ok, _52_9950, (msg, fvs, fvs_t)))
end))))

let occurs_check_e = (fun ( env ) ( ut ) ( e ) -> (let uvs = (Microsoft_FStar_Absyn_Util.uvars_in_exp e)
in (let occurs_ok = (let _52_9957 = (Support.Microsoft.FStar.Util.set_mem ut uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (not (_52_9957)))
in (let msg = (match (occurs_ok) with
| true -> begin
None
end
| false -> begin
(let _52_9963 = (let _52_9962 = (Microsoft_FStar_Absyn_Print.uvar_e_to_string ut)
in (let _52_9961 = (let _52_9959 = (let _52_9958 = (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (Support.Prims.pipe_right _52_9958 (Support.List.map Microsoft_FStar_Absyn_Print.uvar_e_to_string)))
in (Support.Prims.pipe_right _52_9959 (Support.String.concat ", ")))
in (let _52_9960 = (Microsoft_FStar_Tc_Normalize.exp_norm_to_string env e)
in (Support.Microsoft.FStar.Util.format3 "occurs-check failed (%s occurs in {%s} uvars of %s)" _52_9962 _52_9961 _52_9960))))
in Some (_52_9963))
end)
in (occurs_ok, msg)))))

let intersect_vars = (fun ( v1 ) ( v2 ) -> (let fvs1 = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders v1)
in (let fvs2 = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders v2)
in (let _52_9970 = (let _52_9969 = (Support.Microsoft.FStar.Util.set_intersect fvs1.Microsoft_FStar_Absyn_Syntax.ftvs fvs2.Microsoft_FStar_Absyn_Syntax.ftvs)
in (let _52_9968 = (Support.Microsoft.FStar.Util.set_intersect fvs1.Microsoft_FStar_Absyn_Syntax.fxvs fvs2.Microsoft_FStar_Absyn_Syntax.fxvs)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _52_9969; Microsoft_FStar_Absyn_Syntax.fxvs = _52_9968}))
in (Microsoft_FStar_Absyn_Syntax.binders_of_freevars _52_9970)))))

let binders_eq = (fun ( v1 ) ( v2 ) -> (let _52_9975 = (Support.List.forall2 (fun ( ax1 ) ( ax2 ) -> (match (((Support.Prims.fst ax1), (Support.Prims.fst ax2))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(Microsoft_FStar_Absyn_Util.bvar_eq a b)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Microsoft_FStar_Absyn_Util.bvar_eq x y)
end
| _ -> begin
false
end)) v1 v2)
in (((Support.List.length v1) = (Support.List.length v2)) && _52_9975)))

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
(let _33_728 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_9987 = (Microsoft_FStar_Absyn_Print.arg_to_string hd)
in (Support.Microsoft.FStar.Util.fprint1 "Not a pattern: %s\n" _52_9987))
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

let destruct_flex_pattern = (fun ( env ) ( t ) -> (let _33_784 = (destruct_flex_t t)
in (match (_33_784) with
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

let rec head_matches = (fun ( env ) ( t1 ) ( t2 ) -> (match ((let _52_10003 = (let _52_10000 = (Microsoft_FStar_Absyn_Util.unmeta_typ t1)
in _52_10000.Microsoft_FStar_Absyn_Syntax.n)
in (let _52_10002 = (let _52_10001 = (Microsoft_FStar_Absyn_Util.unmeta_typ t2)
in _52_10001.Microsoft_FStar_Absyn_Syntax.n)
in (_52_10003, _52_10002)))) with
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
(Support.Prims.pipe_right (Obj.magic (head_matches (Obj.magic x.Microsoft_FStar_Absyn_Syntax.sort) y.Microsoft_FStar_Absyn_Syntax.sort)) head_match)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _)), _) -> begin
(Support.Prims.pipe_right (Obj.magic (head_matches (Obj.magic x.Microsoft_FStar_Absyn_Syntax.sort) t2)) head_match)
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _))) -> begin
(Support.Prims.pipe_right (Obj.magic (head_matches (Obj.magic t1) x.Microsoft_FStar_Absyn_Syntax.sort)) head_match)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_), Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) -> begin
HeadMatch
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app ((head, _)), Microsoft_FStar_Absyn_Syntax.Typ_app ((head', _))) -> begin
(Obj.magic (head_matches (Obj.magic head) head'))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app ((head, _)), _) -> begin
(Obj.magic (head_matches (Obj.magic head) t2))
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_app ((head, _))) -> begin
(Obj.magic (head_matches (Obj.magic t1) head))
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
in (let fail = (fun ( _33_910 ) -> (match (()) with
| () -> begin
(MisMatch, None)
end))
in (let rec aux = (fun ( d ) ( t1 ) ( t2 ) -> (match ((head_matches env t1 t2)) with
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

let decompose_binder = (fun ( bs ) ( v_ktec ) ( rebuild_base ) -> (let fail = (fun ( _33_924 ) -> (match (()) with
| () -> begin
(failwith ("Bad reconstruction"))
end))
in (let rebuild = (fun ( ktecs ) -> (let rec aux = (fun ( new_bs ) ( bs ) ( ktecs ) -> (match ((bs, ktecs)) with
| ([], ktec::[]) -> begin
(rebuild_base (Support.List.rev new_bs) ktec)
end
| ((Support.Microsoft.FStar.Util.Inl (a), imp)::rest, Microsoft_FStar_Absyn_Syntax.K (k)::rest') -> begin
(aux (((Support.Microsoft.FStar.Util.Inl ((let _33_946 = a
in {Microsoft_FStar_Absyn_Syntax.v = _33_946.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _33_946.Microsoft_FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| ((Support.Microsoft.FStar.Util.Inr (x), imp)::rest, Microsoft_FStar_Absyn_Syntax.T ((t, _))::rest') -> begin
(aux (((Support.Microsoft.FStar.Util.Inr ((let _33_962 = x
in {Microsoft_FStar_Absyn_Syntax.v = _33_962.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _33_962.Microsoft_FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| _ -> begin
(fail ())
end))
in (aux [] bs ktecs)))
in (let rec mk_b_ktecs = (fun ( _33_969 ) ( _33_21 ) -> (match (_33_969) with
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
in (let _52_10057 = (mk_b_ktecs ([], []) bs)
in (rebuild, _52_10057))))))

let rec decompose_kind = (fun ( env ) ( k ) -> (let fail = (fun ( _33_988 ) -> (match (()) with
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
in (let matches = (fun ( t' ) -> (let _52_10095 = (head_matches env t t')
in (_52_10095 <> MisMatch)))
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
(let _33_1074 = (decompose_binder bs (Microsoft_FStar_Absyn_Syntax.C (c)) (fun ( bs ) ( _33_25 ) -> (match (_33_25) with
| Microsoft_FStar_Absyn_Syntax.C (c) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.Microsoft_FStar_Absyn_Syntax.pos)
end
| _ -> begin
(failwith ("Bad reconstruction"))
end)))
in (match (_33_1074) with
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
(let _33_1120 = (new_kvar r scope)
in (match (_33_1120) with
| (gi_xs, gi) -> begin
(let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (gi, args) r)
in (let _52_10141 = (let _52_10140 = (mk_problem scope orig gi_ps (vary_rel rel variance) ki None "kind subterm")
in (Support.Prims.pipe_left (fun ( _52_10139 ) -> KProb (_52_10139)) _52_10140))
in (Microsoft_FStar_Absyn_Syntax.K (gi_xs), _52_10141)))
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
in (let _33_1136 = (new_tvar r scope k)
in (match (_33_1136) with
| (gi_xs, gi) -> begin
(let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (gi, args) None r)
in (let _52_10144 = (let _52_10143 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (Support.Prims.pipe_left (fun ( _52_10142 ) -> TProb (_52_10142)) _52_10143))
in (Microsoft_FStar_Absyn_Syntax.T ((gi_xs, Some (k))), _52_10144)))
end)))
end
| (_, variance, Microsoft_FStar_Absyn_Syntax.E (ei)) -> begin
(let t = (Microsoft_FStar_Tc_Recheck.recompute_typ ei)
in (let _33_1147 = (new_evar r scope t)
in (match (_33_1147) with
| (gi_xs, gi) -> begin
(let gi_ps = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (gi, args) (Some (t)) r)
in (let _52_10147 = (let _52_10146 = (mk_problem scope orig gi_ps (vary_rel rel variance) ei None "expression subterm")
in (Support.Prims.pipe_left (fun ( _52_10145 ) -> EProb (_52_10145)) _52_10146))
in (Microsoft_FStar_Absyn_Syntax.E (gi_xs), _52_10147)))
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
(let _33_1230 = (match (q) with
| (bopt, variance, Microsoft_FStar_Absyn_Syntax.C ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Total (ti); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(match ((sub_prob scope args (bopt, variance, Microsoft_FStar_Absyn_Syntax.T ((ti, Some (Microsoft_FStar_Absyn_Syntax.ktype)))))) with
| (Microsoft_FStar_Absyn_Syntax.T ((gi_xs, _)), prob) -> begin
(let _52_10156 = (let _52_10155 = (Microsoft_FStar_Absyn_Syntax.mk_Total gi_xs)
in (Support.Prims.pipe_left (fun ( _52_10154 ) -> Microsoft_FStar_Absyn_Syntax.C (_52_10154)) _52_10155))
in (_52_10156, (prob)::[]))
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
in (let _33_1221 = (let _52_10158 = (Support.List.map (sub_prob scope args) components)
in (Support.Prims.pipe_right _52_10158 Support.List.unzip))
in (match (_33_1221) with
| (ktecs, sub_probs) -> begin
(let gi_xs = (let _52_10163 = (let _52_10162 = (let _52_10159 = (Support.List.hd ktecs)
in (Support.Prims.pipe_right _52_10159 un_T))
in (let _52_10161 = (let _52_10160 = (Support.List.tl ktecs)
in (Support.Prims.pipe_right _52_10160 (Support.List.map arg_of_ktec)))
in {Microsoft_FStar_Absyn_Syntax.effect_name = c.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _52_10162; Microsoft_FStar_Absyn_Syntax.effect_args = _52_10161; Microsoft_FStar_Absyn_Syntax.flags = c.Microsoft_FStar_Absyn_Syntax.flags}))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp _52_10163))
in (Microsoft_FStar_Absyn_Syntax.C (gi_xs), sub_probs))
end))))
end
| _ -> begin
(let _33_1227 = (sub_prob scope args q)
in (match (_33_1227) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_33_1230) with
| (ktec, probs) -> begin
(let _33_1243 = (match (q) with
| (Some (b), _, _) -> begin
(let _52_10165 = (let _52_10164 = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder b)
in (_52_10164)::args)
in (Some (b), (b)::scope, _52_10165))
end
| _ -> begin
(None, scope, args)
end)
in (match (_33_1243) with
| (bopt, scope, args) -> begin
(let _33_1247 = (aux scope args qs)
in (match (_33_1247) with
| (sub_probs, ktecs, f) -> begin
(let f = (match (bopt) with
| None -> begin
(let _52_10168 = (let _52_10167 = (Support.Prims.pipe_right probs (Support.List.map (fun ( prob ) -> (Support.Prims.pipe_right (p_guard prob) Support.Prims.fst))))
in (f)::_52_10167)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _52_10168))
end
| Some (b) -> begin
(let _52_10172 = (let _52_10171 = (Microsoft_FStar_Absyn_Util.close_forall ((b)::[]) f)
in (let _52_10170 = (Support.Prims.pipe_right probs (Support.List.map (fun ( prob ) -> (Support.Prims.pipe_right (p_guard prob) Support.Prims.fst))))
in (_52_10171)::_52_10170))
in (Microsoft_FStar_Absyn_Util.mk_conj_l _52_10172))
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

let fix_slack_uv = (fun ( _33_1260 ) ( mul ) -> (match (_33_1260) with
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

let fix_slack_vars = (fun ( slack ) -> (Support.Prims.pipe_right slack (Support.List.iter (fun ( _33_1266 ) -> (match (_33_1266) with
| (mul, s) -> begin
(match ((let _52_10190 = (Microsoft_FStar_Absyn_Util.compress_typ s)
in _52_10190.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(fix_slack_uv (uv, k) mul)
end
| _ -> begin
()
end)
end)))))

let fix_slack = (fun ( slack ) -> (let _33_1280 = (Support.Prims.pipe_left destruct_flex_t (Support.Prims.snd slack.lower))
in (match (_33_1280) with
| (_, ul, kl, _) -> begin
(let _33_1287 = (Support.Prims.pipe_left destruct_flex_t (Support.Prims.snd slack.upper))
in (match (_33_1287) with
| (_, uh, kh, _) -> begin
(let _33_1288 = (fix_slack_uv (ul, kl) false)
in (let _33_1290 = (fix_slack_uv (uh, kh) true)
in (let _33_1292 = (Support.ST.op_Colon_Equals slack.flag true)
in (Microsoft_FStar_Absyn_Util.mk_conj (Support.Prims.fst slack.lower) (Support.Prims.fst slack.upper)))))
end))
end)))

let new_slack_var = (fun ( env ) ( slack ) -> (let xs = (let _52_10198 = (let _52_10197 = (destruct_flex_pattern env (Support.Prims.snd slack.lower))
in (Support.Prims.pipe_right _52_10197 Support.Prims.snd))
in (Support.Prims.pipe_right _52_10198 Support.Microsoft.FStar.Util.must))
in (let _52_10199 = (new_tvar (Support.Prims.fst slack.lower).Microsoft_FStar_Absyn_Syntax.pos xs Microsoft_FStar_Absyn_Syntax.ktype)
in (_52_10199, xs))))

let new_slack_formula = (fun ( p ) ( env ) ( wl ) ( xs ) ( low ) ( high ) -> (let _33_1305 = (new_tvar p xs Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_33_1305) with
| (low_var, uv1) -> begin
(let wl = (add_slack_add uv1 wl)
in (let _33_1309 = (new_tvar p xs Microsoft_FStar_Absyn_Syntax.ktype)
in (match (_33_1309) with
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
in (let _52_10209 = (let _52_10208 = (let _52_10207 = (let _52_10206 = (Support.Microsoft.FStar.Util.mk_ref false)
in (low, high, _52_10206))
in Microsoft_FStar_Absyn_Syntax.Meta_slack_formula (_52_10207))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta _52_10208))
in (_52_10209, wl)))))
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
(let _52_10233 = (let _52_10232 = (mk_conn lhs rest)
in (_52_10232, uvar))
in Some (_52_10233))
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
(let _52_10234 = (Microsoft_FStar_Absyn_Util.unmeta_typ phi)
in Support.Microsoft.FStar.Util.Inl (_52_10234))
end
| false -> begin
(let low = (let _52_10235 = (compress env wl phi1)
in (Support.Prims.pipe_left (destruct Microsoft_FStar_Absyn_Const.or_lid Microsoft_FStar_Absyn_Util.mk_disj) _52_10235))
in (let hi = (let _52_10236 = (compress env wl phi2)
in (Support.Prims.pipe_left (destruct Microsoft_FStar_Absyn_Const.and_lid Microsoft_FStar_Absyn_Util.mk_disj) _52_10236))
in (match ((low, hi)) with
| (None, None) -> begin
(let _33_1391 = (Support.ST.op_Colon_Equals flag true)
in (let _52_10237 = (Microsoft_FStar_Absyn_Util.unmeta_typ phi)
in Support.Microsoft.FStar.Util.Inl (_52_10237)))
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
(let _52_10247 = (eq_typ h1 h2)
in (let _52_10246 = (eq_args args1 args2)
in (_52_10247 && _52_10246)))
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
(let _52_10251 = (eq_exp h1 h2)
in (let _52_10250 = (eq_args args1 args2)
in (_52_10251 && _52_10250)))
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
(let _52_10271 = (let _33_1514 = p
in (let _52_10269 = (compress_k wl.tcenv wl p.lhs)
in (let _52_10268 = (compress_k wl.tcenv wl p.rhs)
in {lhs = _52_10269; relation = _33_1514.relation; rhs = _52_10268; element = _33_1514.element; logical_guard = _33_1514.logical_guard; scope = _33_1514.scope; reason = _33_1514.reason; loc = _33_1514.loc; rank = _33_1514.rank})))
in (Support.Prims.pipe_right _52_10271 (fun ( _52_10270 ) -> KProb (_52_10270))))
end
| TProb (p) -> begin
(let _52_10275 = (let _33_1518 = p
in (let _52_10273 = (compress wl.tcenv wl p.lhs)
in (let _52_10272 = (compress wl.tcenv wl p.rhs)
in {lhs = _52_10273; relation = _33_1518.relation; rhs = _52_10272; element = _33_1518.element; logical_guard = _33_1518.logical_guard; scope = _33_1518.scope; reason = _33_1518.reason; loc = _33_1518.loc; rank = _33_1518.rank})))
in (Support.Prims.pipe_right _52_10275 (fun ( _52_10274 ) -> TProb (_52_10274))))
end
| EProb (p) -> begin
(let _52_10279 = (let _33_1522 = p
in (let _52_10277 = (compress_e wl.tcenv wl p.lhs)
in (let _52_10276 = (compress_e wl.tcenv wl p.rhs)
in {lhs = _52_10277; relation = _33_1522.relation; rhs = _52_10276; element = _33_1522.element; logical_guard = _33_1522.logical_guard; scope = _33_1522.scope; reason = _33_1522.reason; loc = _33_1522.loc; rank = _33_1522.rank})))
in (Support.Prims.pipe_right _52_10279 (fun ( _52_10278 ) -> EProb (_52_10278))))
end
| CProb (_) -> begin
p
end))

let rank = (fun ( wl ) ( prob ) -> (let prob = (let _52_10284 = (compress_prob wl prob)
in (Support.Prims.pipe_right _52_10284 maybe_invert_p))
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
in (let _52_10286 = (Support.Prims.pipe_right (let _33_1557 = kp
in {lhs = _33_1557.lhs; relation = _33_1557.relation; rhs = _33_1557.rhs; element = _33_1557.element; logical_guard = _33_1557.logical_guard; scope = _33_1557.scope; reason = _33_1557.reason; loc = _33_1557.loc; rank = Some (rank)}) (fun ( _52_10285 ) -> KProb (_52_10285)))
in (rank, _52_10286)))
end
| TProb (tp) -> begin
(let _33_1564 = (Microsoft_FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_33_1564) with
| (lh, _) -> begin
(let _33_1568 = (Microsoft_FStar_Absyn_Util.head_and_args tp.rhs)
in (match (_33_1568) with
| (rh, _) -> begin
(let _33_1624 = (match ((lh.Microsoft_FStar_Absyn_Syntax.n, rh.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
(flex_flex, tp)
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_uvar (_))) when (tp.relation = EQ) -> begin
(flex_rigid_eq, tp)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), _) -> begin
(let _33_1596 = (base_and_refinement wl.tcenv wl tp.rhs)
in (match (_33_1596) with
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
in (let _52_10288 = (let _33_1601 = tp
in (let _52_10287 = (force_refinement (b, ref_opt))
in {lhs = _33_1601.lhs; relation = _33_1601.relation; rhs = _52_10287; element = _33_1601.element; logical_guard = _33_1601.logical_guard; scope = _33_1601.scope; reason = _33_1601.reason; loc = _33_1601.loc; rank = _33_1601.rank}))
in (rank, _52_10288)))
end)
end))
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
(let _33_1611 = (base_and_refinement wl.tcenv wl tp.lhs)
in (match (_33_1611) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _ -> begin
(let _52_10290 = (let _33_1615 = tp
in (let _52_10289 = (force_refinement (b, ref_opt))
in {lhs = _52_10289; relation = _33_1615.relation; rhs = _33_1615.rhs; element = _33_1615.element; logical_guard = _33_1615.logical_guard; scope = _33_1615.scope; reason = _33_1615.reason; loc = _33_1615.loc; rank = _33_1615.rank}))
in (refine_flex, _52_10290))
end)
end))
end
| (_, _) -> begin
(rigid_rigid, tp)
end)
in (match (_33_1624) with
| (rank, tp) -> begin
(let _52_10292 = (Support.Prims.pipe_right (let _33_1625 = tp
in {lhs = _33_1625.lhs; relation = _33_1625.relation; rhs = _33_1625.rhs; element = _33_1625.element; logical_guard = _33_1625.logical_guard; scope = _33_1625.scope; reason = _33_1625.reason; loc = _33_1625.loc; rank = Some (rank)}) (fun ( _52_10291 ) -> TProb (_52_10291)))
in (rank, _52_10292))
end))
end))
end))
end
| EProb (ep) -> begin
(let _33_1632 = (Microsoft_FStar_Absyn_Util.head_and_args_e ep.lhs)
in (match (_33_1632) with
| (lh, _) -> begin
(let _33_1636 = (Microsoft_FStar_Absyn_Util.head_and_args_e ep.rhs)
in (match (_33_1636) with
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
in (let _52_10294 = (Support.Prims.pipe_right (let _33_1662 = ep
in {lhs = _33_1662.lhs; relation = _33_1662.relation; rhs = _33_1662.rhs; element = _33_1662.element; logical_guard = _33_1662.logical_guard; scope = _33_1662.scope; reason = _33_1662.reason; loc = _33_1662.loc; rank = Some (rank)}) (fun ( _52_10293 ) -> EProb (_52_10293)))
in (rank, _52_10294)))
end))
end))
end
| CProb (cp) -> begin
(let _52_10296 = (Support.Prims.pipe_right (let _33_1666 = cp
in {lhs = _33_1666.lhs; relation = _33_1666.relation; rhs = _33_1666.rhs; element = _33_1666.element; logical_guard = _33_1666.logical_guard; scope = _33_1666.scope; reason = _33_1666.reason; loc = _33_1666.loc; rank = Some (rigid_rigid)}) (fun ( _52_10295 ) -> CProb (_52_10295)))
in (rigid_rigid, _52_10296))
end)))

let next_prob = (fun ( wl ) -> (let rec aux = (fun ( _33_1673 ) ( probs ) -> (match (_33_1673) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(let _33_1681 = (rank wl hd)
in (match (_33_1681) with
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

let rec solve_flex_rigid_join = (fun ( env ) ( tp ) ( wl ) -> (let _33_1692 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10346 = (prob_to_string env (TProb (tp)))
in (Support.Microsoft.FStar.Util.fprint1 "Trying to solve by joining refinements:%s\n" _52_10346))
end
| false -> begin
()
end)
in (let _33_1696 = (Microsoft_FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_33_1696) with
| (u, args) -> begin
(let _33_1702 = (0, 1, 2, 3, 4)
in (match (_33_1702) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(let max = (fun ( i ) ( j ) -> (match ((i < j)) with
| true -> begin
j
end
| false -> begin
i
end))
in (let base_types_match = (fun ( t1 ) ( t2 ) -> (let _33_1711 = (Microsoft_FStar_Absyn_Util.head_and_args t1)
in (match (_33_1711) with
| (h1, args1) -> begin
(let _33_1715 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (match (_33_1715) with
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
(let _52_10358 = (let _52_10357 = (let _52_10356 = (new_problem env t1 EQ t2 None t1.Microsoft_FStar_Absyn_Syntax.pos "joining refinements")
in (Support.Prims.pipe_left (fun ( _52_10355 ) -> TProb (_52_10355)) _52_10356))
in (_52_10357)::[])
in Some (_52_10358))
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
(let phi2 = (let _52_10365 = (let _52_10364 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (let _52_10363 = (Microsoft_FStar_Absyn_Syntax.v_binder y)
in (Microsoft_FStar_Absyn_Util.mk_subst_one_binder _52_10364 _52_10363)))
in (Microsoft_FStar_Absyn_Util.subst_typ _52_10365 phi2))
in (let _52_10369 = (let _52_10368 = (let _52_10367 = (let _52_10366 = (Microsoft_FStar_Absyn_Util.mk_conj phi1 phi2)
in (x, _52_10366))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _52_10367 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) t1.Microsoft_FStar_Absyn_Syntax.pos))
in (_52_10368, m))
in Some (_52_10369)))
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
(let _33_1803 = (Support.Prims.pipe_right wl.attempting (Support.List.partition (fun ( _33_30 ) -> (match (_33_30) with
| TProb (tp) -> begin
(match (tp.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(let _33_1789 = (Microsoft_FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_33_1789) with
| (u', _) -> begin
(match ((let _52_10371 = (compress env wl u')
in _52_10371.Microsoft_FStar_Absyn_Syntax.n)) with
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
in (match (_33_1803) with
| (upper_bounds, rest) -> begin
(let rec make_upper_bound = (fun ( _33_1807 ) ( tps ) -> (match (_33_1807) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| TProb (hd)::tl -> begin
(match ((let _52_10376 = (compress env wl hd.rhs)
in (conjoin bound _52_10376))) with
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
in (match ((let _52_10378 = (let _52_10377 = (compress env wl tp.rhs)
in (_52_10377, []))
in (make_upper_bound _52_10378 upper_bounds))) with
| None -> begin
(let _33_1822 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
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
in (match ((solve_t env eq_prob (let _33_1829 = wl
in {attempting = sub_probs; deferred = _33_1829.deferred; subst = _33_1829.subst; ctr = _33_1829.ctr; slack_vars = _33_1829.slack_vars; defer_ok = _33_1829.defer_ok; smt_ok = _33_1829.smt_ok; tcenv = _33_1829.tcenv}))) with
| Success ((subst, _)) -> begin
(let wl = (let _33_1836 = wl
in {attempting = rest; deferred = _33_1836.deferred; subst = []; ctr = _33_1836.ctr; slack_vars = _33_1836.slack_vars; defer_ok = _33_1836.defer_ok; smt_ok = _33_1836.smt_ok; tcenv = _33_1836.tcenv})
in (let wl = (solve_prob (TProb (tp)) None subst wl)
in (let _33_1842 = (Support.List.fold_left (fun ( wl ) ( p ) -> (solve_prob' true p None [] wl)) wl upper_bounds)
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
(let probs = (let _33_1855 = probs
in {attempting = tl; deferred = _33_1855.deferred; subst = _33_1855.subst; ctr = _33_1855.ctr; slack_vars = _33_1855.slack_vars; defer_ok = _33_1855.defer_ok; smt_ok = _33_1855.smt_ok; tcenv = _33_1855.tcenv})
in (match (hd) with
| KProb (kp) -> begin
(solve_k' env (maybe_invert kp) probs)
end
| TProb (tp) -> begin
(match ((let _52_10384 = (let _52_10383 = (Support.ST.read Microsoft_FStar_Options.no_slack)
in (not (_52_10383)))
in ((((not (probs.defer_ok)) && (flex_refine_inner <= rank)) && (rank <= flex_rigid)) && _52_10384))) with
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
(let _33_1886 = (Support.Prims.pipe_right probs.deferred (Support.List.partition (fun ( _33_1883 ) -> (match (_33_1883) with
| (c, _, _) -> begin
(c < probs.ctr)
end))))
in (match (_33_1886) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _52_10389 = (let _52_10388 = (let _52_10387 = (Support.List.map (fun ( _33_1892 ) -> (match (_33_1892) with
| (_, x, y) -> begin
(x, y)
end)) probs.deferred)
in {carry = _52_10387; slack = probs.slack_vars})
in (probs.subst, _52_10388))
in Success (_52_10389))
end
| _ -> begin
(let _52_10392 = (let _33_1895 = probs
in (let _52_10391 = (Support.Prims.pipe_right attempt (Support.List.map (fun ( _33_1902 ) -> (match (_33_1902) with
| (_, _, y) -> begin
y
end))))
in {attempting = _52_10391; deferred = rest; subst = _33_1895.subst; ctr = _33_1895.ctr; slack_vars = _33_1895.slack_vars; defer_ok = _33_1895.defer_ok; smt_ok = _33_1895.smt_ok; tcenv = _33_1895.tcenv}))
in (solve env _52_10392))
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
(let subst = (let _52_10418 = (Microsoft_FStar_Absyn_Util.mk_subst_one_binder hd2 hd1)
in (Support.List.append _52_10418 subst))
in (let env = (let _52_10419 = (Microsoft_FStar_Tc_Env.binding_of_binder hd2)
in (Microsoft_FStar_Tc_Env.push_local_binding env _52_10419))
in (let prob = (match (((Support.Prims.fst hd1), (Support.Prims.fst hd2))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(let _52_10423 = (let _52_10422 = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _52_10421 = (Support.Prims.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _52_10422 _52_10421 b.Microsoft_FStar_Absyn_Syntax.sort None "Formal type parameter")))
in (Support.Prims.pipe_left (fun ( _52_10420 ) -> KProb (_52_10420)) _52_10423))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(let _52_10427 = (let _52_10426 = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _52_10425 = (Support.Prims.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _52_10426 _52_10425 y.Microsoft_FStar_Absyn_Syntax.sort None "Formal value parameter")))
in (Support.Prims.pipe_left (fun ( _52_10424 ) -> TProb (_52_10424)) _52_10427))
end
| _ -> begin
(failwith ("impos"))
end)
in (match ((aux ((hd2)::scope) env subst xs ys)) with
| Support.Microsoft.FStar.Util.Inr (msg) -> begin
Support.Microsoft.FStar.Util.Inr (msg)
end
| Support.Microsoft.FStar.Util.Inl ((sub_probs, phi)) -> begin
(let phi = (let _52_10429 = (Support.Prims.pipe_right (p_guard prob) Support.Prims.fst)
in (let _52_10428 = (Microsoft_FStar_Absyn_Util.close_forall ((hd2)::[]) phi)
in (Microsoft_FStar_Absyn_Util.mk_conj _52_10429 _52_10428)))
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
(let _52_10436 = (solve_prob orig None [] wl)
in (solve env _52_10436))
end
| false -> begin
(let k1 = problem.lhs
in (let k2 = problem.rhs
in (match ((Support.Microsoft.FStar.Util.physical_equality k1 k2)) with
| true -> begin
(let _52_10437 = (solve_prob orig None [] wl)
in (solve env _52_10437))
end
| false -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let imitate_k = (fun ( _33_2019 ) -> (match (_33_2019) with
| (rel, u, ps, xs, (h, qs)) -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let _33_2024 = (imitation_sub_probs orig env xs ps qs)
in (match (_33_2024) with
| (sub_probs, gs_xs, f) -> begin
(let im = (let _52_10453 = (let _52_10452 = (h gs_xs)
in (xs, _52_10452))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam _52_10453 r))
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
in (match ((let _52_10466 = (let _52_10463 = (Support.Microsoft.FStar.Util.set_is_subset_of fvs2.Microsoft_FStar_Absyn_Syntax.ftvs fvs1.Microsoft_FStar_Absyn_Syntax.ftvs)
in (let _52_10462 = (Support.Microsoft.FStar.Util.set_is_subset_of fvs2.Microsoft_FStar_Absyn_Syntax.fxvs fvs1.Microsoft_FStar_Absyn_Syntax.fxvs)
in (_52_10463 && _52_10462)))
in (let _52_10465 = (let _52_10464 = (Support.Microsoft.FStar.Util.set_mem u uvs2.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (not (_52_10464)))
in (_52_10466 && _52_10465)))) with
| true -> begin
(let k1 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_lam (xs, k2) r)
in (let _52_10467 = (solve_prob orig None ((UK ((u, k1)))::[]) wl)
in (solve env _52_10467)))
end
| false -> begin
(let _52_10472 = (let _52_10471 = (Support.Prims.pipe_right xs Microsoft_FStar_Absyn_Util.args_of_non_null_binders)
in (let _52_10470 = (decompose_kind env k)
in (rel, u, _52_10471, xs, _52_10470)))
in (imitate_k _52_10472))
end))))
end
| None -> begin
(giveup env "flex-rigid: not a pattern" (KProb (problem)))
end)))
in (match ((k1.Microsoft_FStar_Absyn_Syntax.n, k2.Microsoft_FStar_Absyn_Syntax.n)) with
| ((Microsoft_FStar_Absyn_Syntax.Kind_type, Microsoft_FStar_Absyn_Syntax.Kind_type)) | ((Microsoft_FStar_Absyn_Syntax.Kind_effect, Microsoft_FStar_Absyn_Syntax.Kind_effect)) -> begin
(let _52_10473 = (solve_prob orig None [] wl)
in (Support.Prims.pipe_left (solve env) _52_10473))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k1)), _) -> begin
(solve_k env (let _33_2054 = problem
in {lhs = k1; relation = _33_2054.relation; rhs = _33_2054.rhs; element = _33_2054.element; logical_guard = _33_2054.logical_guard; scope = _33_2054.scope; reason = _33_2054.reason; loc = _33_2054.loc; rank = _33_2054.rank}) wl)
end
| (_, Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k2))) -> begin
(solve_k env (let _33_2064 = problem
in {lhs = _33_2064.lhs; relation = _33_2064.relation; rhs = k2; element = _33_2064.element; logical_guard = _33_2064.logical_guard; scope = _33_2064.scope; reason = _33_2064.reason; loc = _33_2064.loc; rank = _33_2064.rank}) wl)
end
| (Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs1, k1')), Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs2, k2'))) -> begin
(let sub_prob = (fun ( scope ) ( env ) ( subst ) -> (let _52_10482 = (let _52_10481 = (Microsoft_FStar_Absyn_Util.subst_kind subst k1')
in (mk_problem scope orig _52_10481 problem.relation k2' None "Arrow-kind result"))
in (Support.Prims.pipe_left (fun ( _52_10480 ) -> KProb (_52_10480)) _52_10482)))
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
(match ((let _52_10483 = (binders_eq xs ys)
in ((Support.Microsoft.FStar.Unionfind.equivalent u1 u2) && _52_10483))) with
| true -> begin
(solve env wl)
end
| false -> begin
(let zs = (intersect_vars xs ys)
in (let _33_2107 = (new_kvar r zs)
in (match (_33_2107) with
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
(let _33_2161 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10494 = (prob_to_string env orig)
in (Support.Microsoft.FStar.Util.fprint2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _52_10494 msg))
end
| false -> begin
()
end)
in (solve env (defer msg orig wl)))
end
| false -> begin
(giveup env msg orig)
end))
in (let imitate_t = (fun ( orig ) ( env ) ( wl ) ( p ) -> (let _33_2178 = p
in (match (_33_2178) with
| ((u, k), ps, xs, (h, _, qs)) -> begin
(let xs = (sn_binders env xs)
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let _33_2184 = (imitation_sub_probs orig env xs ps qs)
in (match (_33_2184) with
| (sub_probs, gs_xs, formula) -> begin
(let im = (let _52_10505 = (let _52_10504 = (h gs_xs)
in (xs, _52_10504))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' _52_10505 None r))
in (let _33_2186 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10510 = (Microsoft_FStar_Absyn_Print.typ_to_string im)
in (let _52_10509 = (Microsoft_FStar_Absyn_Print.tag_of_typ im)
in (let _52_10508 = (let _52_10506 = (Support.List.map (prob_to_string env) sub_probs)
in (Support.Prims.pipe_right _52_10506 (Support.String.concat ", ")))
in (let _52_10507 = (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env formula)
in (Support.Microsoft.FStar.Util.fprint4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _52_10510 _52_10509 _52_10508 _52_10507)))))
end
| false -> begin
()
end)
in (let wl = (solve_prob orig (Some (formula)) ((UT (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (let project_t = (fun ( orig ) ( env ) ( wl ) ( i ) ( p ) -> (let _33_2202 = p
in (match (_33_2202) with
| (u, ps, xs, (h, matches, qs)) -> begin
(let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let pi = (Support.List.nth ps i)
in (let rec gs = (fun ( k ) -> (let _33_2209 = (Microsoft_FStar_Absyn_Util.kind_formals k)
in (match (_33_2209) with
| (bs, k) -> begin
(let rec aux = (fun ( subst ) ( bs ) -> (match (bs) with
| [] -> begin
([], [])
end
| hd::tl -> begin
(let _33_2238 = (match ((Support.Prims.fst hd)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let k_a = (Microsoft_FStar_Absyn_Util.subst_kind subst a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _33_2222 = (new_tvar r xs k_a)
in (match (_33_2222) with
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
in (let _52_10530 = (Microsoft_FStar_Absyn_Syntax.targ gi_xs)
in (let _52_10529 = (Microsoft_FStar_Absyn_Syntax.targ gi_ps)
in (_52_10530, _52_10529, subst))))))
end)))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let t_x = (Microsoft_FStar_Absyn_Util.subst_typ subst x.Microsoft_FStar_Absyn_Syntax.sort)
in (let _33_2231 = (new_evar r xs t_x)
in (match (_33_2231) with
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
in (let _52_10532 = (Microsoft_FStar_Absyn_Syntax.varg gi_xs)
in (let _52_10531 = (Microsoft_FStar_Absyn_Syntax.varg gi_ps)
in (_52_10532, _52_10531, subst))))))
end)))
end)
in (match (_33_2238) with
| (gi_xs, gi_ps, subst) -> begin
(let _33_2241 = (aux subst tl)
in (match (_33_2241) with
| (gi_xs', gi_ps') -> begin
((gi_xs)::gi_xs', (gi_ps)::gi_ps')
end))
end))
end))
in (aux [] bs))
end)))
in (match ((let _52_10534 = (let _52_10533 = (Support.List.nth xs i)
in (Support.Prims.pipe_left Support.Prims.fst _52_10533))
in ((Support.Prims.fst pi), _52_10534))) with
| (Support.Microsoft.FStar.Util.Inl (pi), Support.Microsoft.FStar.Util.Inl (xi)) -> begin
(match ((let _52_10535 = (matches pi)
in (Support.Prims.pipe_left Support.Prims.op_Negation _52_10535))) with
| true -> begin
None
end
| false -> begin
(let _33_2250 = (gs xi.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_33_2250) with
| (g_xs, _) -> begin
(let xi = (Microsoft_FStar_Absyn_Util.btvar_to_typ xi)
in (let proj = (let _52_10537 = (let _52_10536 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (xi, g_xs) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)
in (xs, _52_10536))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _52_10537 None r))
in (let sub = (let _52_10543 = (let _52_10542 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app' (proj, ps) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)
in (let _52_10541 = (let _52_10540 = (Support.List.map (fun ( _33_2258 ) -> (match (_33_2258) with
| (_, _, y) -> begin
y
end)) qs)
in (Support.Prims.pipe_left h _52_10540))
in (mk_problem (p_scope orig) orig _52_10542 (p_rel orig) _52_10541 None "projection")))
in (Support.Prims.pipe_left (fun ( _52_10538 ) -> TProb (_52_10538)) _52_10543))
in (let _33_2260 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10545 = (Microsoft_FStar_Absyn_Print.typ_to_string proj)
in (let _52_10544 = (prob_to_string env sub)
in (Support.Microsoft.FStar.Util.fprint2 "Projecting %s\n\tsubprob=%s\n" _52_10545 _52_10544)))
end
| false -> begin
()
end)
in (let wl = (let _52_10547 = (let _52_10546 = (Support.Prims.pipe_left Support.Prims.fst (p_guard sub))
in Some (_52_10546))
in (solve_prob orig _52_10547 ((UT ((u, proj)))::[]) wl))
in (let _52_10549 = (solve env (attempt ((sub)::[]) wl))
in (Support.Prims.pipe_left (fun ( _52_10548 ) -> Some (_52_10548)) _52_10549)))))))
end))
end)
end
| _ -> begin
None
end))))
end)))
in (let solve_t_flex_rigid = (fun ( orig ) ( lhs ) ( t2 ) ( wl ) -> (let _33_2276 = lhs
in (match (_33_2276) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(let subterms = (fun ( ps ) -> (let xs = (let _52_10576 = (Microsoft_FStar_Absyn_Util.kind_formals k)
in (Support.Prims.pipe_right _52_10576 Support.Prims.fst))
in (let xs = (Microsoft_FStar_Absyn_Util.name_binders xs)
in (let _52_10581 = (decompose_typ env t2)
in ((uv, k), ps, xs, _52_10581)))))
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
in (let check_head = (fun ( fvs1 ) ( t2 ) -> (let _33_2302 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (match (_33_2302) with
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
(let _33_2315 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10592 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs_hd)
in (Support.Microsoft.FStar.Util.fprint1 "Free variables are %s" _52_10592))
end
| false -> begin
()
end)
in false)
end))
end)
end)))
in (let imitate_ok = (fun ( t2 ) -> (let fvs_hd = (let _52_10596 = (let _52_10595 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (Support.Prims.pipe_right _52_10595 Support.Prims.fst))
in (Support.Prims.pipe_right _52_10596 Microsoft_FStar_Absyn_Util.freevars_typ))
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
in (let _33_2328 = (occurs_check env wl (uv, k) t2)
in (match (_33_2328) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(let _52_10598 = (let _52_10597 = (Support.Option.get msg)
in (Support.String.strcat "occurs-check failed: " _52_10597))
in (giveup_or_defer orig _52_10598))
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Util.fvs_included fvs2 fvs1)) with
| true -> begin
(match ((let _52_10599 = (Microsoft_FStar_Absyn_Util.is_function_typ t2)
in (_52_10599 && ((p_rel orig) <> EQ)))) with
| true -> begin
(let _52_10600 = (subterms args_lhs)
in (imitate_t orig env wl _52_10600))
end
| false -> begin
(let _33_2329 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10603 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _52_10602 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs1)
in (let _52_10601 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs2)
in (Support.Microsoft.FStar.Util.fprint3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _52_10603 _52_10602 _52_10601))))
end
| false -> begin
()
end)
in (let sol = (match (vars) with
| [] -> begin
t2
end
| _ -> begin
(let _52_10605 = (let _52_10604 = (sn_binders env vars)
in (_52_10604, t2))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _52_10605 None t1.Microsoft_FStar_Absyn_Syntax.pos))
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
(let _33_2336 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10608 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _52_10607 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs1)
in (let _52_10606 = (Microsoft_FStar_Absyn_Print.freevars_to_string fvs2)
in (Support.Microsoft.FStar.Util.fprint3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _52_10608 _52_10607 _52_10606))))
end
| false -> begin
()
end)
in (let _52_10609 = (subterms args_lhs)
in (imitate_or_project (Support.List.length args_lhs) _52_10609 (- (1)))))
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
(match ((let _52_10610 = (Microsoft_FStar_Absyn_Util.freevars_typ t1)
in (check_head _52_10610 t2))) with
| true -> begin
(let im_ok = (imitate_ok t2)
in (let _33_2340 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10611 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Support.Microsoft.FStar.Util.fprint2 "Not a pattern (%s) ... %s\n" _52_10611 (match ((im_ok < 0)) with
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
in (let _52_10612 = (subterms args_lhs)
in (imitate_or_project (Support.List.length args_lhs) _52_10612 im_ok))))
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
(let force_quasi_pattern = (fun ( xs_opt ) ( _33_2352 ) -> (match (_33_2352) with
| (t, u, k, args) -> begin
(let rec aux = (fun ( binders ) ( ys ) ( args ) -> (match (args) with
| [] -> begin
(let ys = (Support.List.rev ys)
in (let binders = (Support.List.rev binders)
in (let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (let _33_2364 = (new_tvar t.Microsoft_FStar_Absyn_Syntax.pos ys kk)
in (match (_33_2364) with
| (t', _) -> begin
(let _33_2370 = (destruct_flex_t t')
in (match (_33_2370) with
| (u1_ys, u1, k1, _) -> begin
(let sol = (let _52_10630 = (let _52_10629 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, u1_ys) (Some (k)) t.Microsoft_FStar_Absyn_Syntax.pos)
in ((u, k), _52_10629))
in UT (_52_10630))
in (sol, (t', u, k1, ys)))
end))
end)))))
end
| hd::tl -> begin
(let new_binder = (fun ( hd ) -> (match ((Support.Prims.fst hd)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _52_10634 = (let _52_10633 = (Microsoft_FStar_Tc_Recheck.recompute_kind a)
in (Support.Prims.pipe_right _52_10633 (Microsoft_FStar_Absyn_Util.gen_bvar_p a.Microsoft_FStar_Absyn_Syntax.pos)))
in (Support.Prims.pipe_right _52_10634 Microsoft_FStar_Absyn_Syntax.t_binder))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _52_10636 = (let _52_10635 = (Microsoft_FStar_Tc_Recheck.recompute_typ x)
in (Support.Prims.pipe_right _52_10635 (Microsoft_FStar_Absyn_Util.gen_bvar_p x.Microsoft_FStar_Absyn_Syntax.pos)))
in (Support.Prims.pipe_right _52_10636 Microsoft_FStar_Absyn_Syntax.v_binder))
end))
in (let _33_2389 = (match ((pat_var_opt env ys hd)) with
| None -> begin
(let _52_10637 = (new_binder hd)
in (_52_10637, ys))
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
(let _52_10638 = (new_binder hd)
in (_52_10638, ys))
end)
end)
end)
in (match (_33_2389) with
| (binder, ys) -> begin
(aux ((binder)::binders) ys tl)
end)))
end))
in (aux [] [] args))
end))
in (let solve_both_pats = (fun ( wl ) ( _33_2395 ) ( _33_2399 ) ( k ) ( r ) -> (match ((_33_2395, _33_2399)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
(match ((let _52_10649 = (binders_eq xs ys)
in ((Support.Microsoft.FStar.Unionfind.equivalent u1 u2) && _52_10649))) with
| true -> begin
(let _52_10650 = (solve_prob orig None [] wl)
in (solve env _52_10650))
end
| false -> begin
(let xs = (sn_binders env xs)
in (let ys = (sn_binders env ys)
in (let zs = (intersect_vars xs ys)
in (let _33_2408 = (new_tvar r zs k)
in (match (_33_2408) with
| (u_zs, _) -> begin
(let sub1 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' (xs, u_zs) (Some (k1)) r)
in (let _33_2412 = (occurs_check env wl (u1, k1) sub1)
in (match (_33_2412) with
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
in (let _33_2418 = (occurs_check env wl (u2, k2) sub2)
in (match (_33_2418) with
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
in (let solve_one_pat = (fun ( _33_2426 ) ( _33_2431 ) -> (match ((_33_2426, _33_2431)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(let _33_2432 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10656 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _52_10655 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (Support.Microsoft.FStar.Util.fprint2 "Trying flex-flex one pattern (%s) with %s\n" _52_10656 _52_10655)))
end
| false -> begin
()
end)
in (match ((Support.Microsoft.FStar.Unionfind.equivalent u1 u2)) with
| true -> begin
(let sub_probs = (Support.List.map2 (fun ( a ) ( b ) -> (let a = (Microsoft_FStar_Absyn_Util.arg_of_non_null_binder a)
in (match (((Support.Prims.fst a), (Support.Prims.fst b))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
(let _52_10660 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (Support.Prims.pipe_right _52_10660 (fun ( _52_10659 ) -> TProb (_52_10659))))
end
| (Support.Microsoft.FStar.Util.Inr (t1), Support.Microsoft.FStar.Util.Inr (t2)) -> begin
(let _52_10662 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (Support.Prims.pipe_right _52_10662 (fun ( _52_10661 ) -> EProb (_52_10661))))
end
| _ -> begin
(failwith ("Impossible"))
end))) xs args2)
in (let guard = (let _52_10664 = (Support.List.map (fun ( p ) -> (Support.Prims.pipe_right (p_guard p) Support.Prims.fst)) sub_probs)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _52_10664))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end
| false -> begin
(let t2 = (sn env t2)
in (let rhs_vars = (Microsoft_FStar_Absyn_Util.freevars_typ t2)
in (let _33_2458 = (occurs_check env wl (u1, k1) t2)
in (match (_33_2458) with
| (occurs_ok, _) -> begin
(let lhs_vars = (Microsoft_FStar_Absyn_Syntax.freevars_of_binders xs)
in (match ((let _52_10665 = (Microsoft_FStar_Absyn_Util.fvs_included rhs_vars lhs_vars)
in (occurs_ok && _52_10665))) with
| true -> begin
(let sol = (let _52_10667 = (let _52_10666 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam' (xs, t2) (Some (k1)) t1.Microsoft_FStar_Absyn_Syntax.pos)
in ((u1, k1), _52_10666))
in UT (_52_10667))
in (let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end
| false -> begin
(match ((let _52_10668 = (Support.Prims.pipe_left Support.Prims.op_Negation wl.defer_ok)
in (occurs_ok && _52_10668))) with
| true -> begin
(let _33_2469 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_33_2469) with
| (sol, (_, u2, k2, ys)) -> begin
(let wl = (extend_solution sol wl)
in (let _33_2471 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("QuasiPattern")))) with
| true -> begin
(let _52_10669 = (uvi_to_string env sol)
in (Support.Microsoft.FStar.Util.fprint1 "flex-flex quasi pattern (2): %s\n" _52_10669))
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
in (let _33_2481 = lhs
in (match (_33_2481) with
| (t1, u1, k1, args1) -> begin
(let _33_2486 = rhs
in (match (_33_2486) with
| (t2, u2, k2, args2) -> begin
(let maybe_pat_vars1 = (pat_vars env [] args1)
in (let maybe_pat_vars2 = (pat_vars env [] args2)
in (let r = t2.Microsoft_FStar_Absyn_Syntax.pos
in (match ((maybe_pat_vars1, maybe_pat_vars2)) with
| (Some (xs), Some (ys)) -> begin
(let _52_10670 = (Microsoft_FStar_Tc_Recheck.recompute_kind t2)
in (solve_both_pats wl (u1, k1, xs) (u2, k2, ys) _52_10670 t2.Microsoft_FStar_Absyn_Syntax.pos))
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
(let _33_2508 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_33_2508) with
| (sol, _) -> begin
(let wl = (extend_solution sol wl)
in (let _33_2510 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("QuasiPattern")))) with
| true -> begin
(let _52_10671 = (uvi_to_string env sol)
in (Support.Microsoft.FStar.Util.fprint1 "flex-flex quasi pattern (1): %s\n" _52_10671))
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
(let _52_10672 = (solve_prob orig None [] wl)
in (solve env _52_10672))
end
| false -> begin
(let t1 = problem.lhs
in (let t2 = problem.rhs
in (match ((Support.Microsoft.FStar.Util.physical_equality t1 t2)) with
| true -> begin
(let _52_10673 = (solve_prob orig None [] wl)
in (solve env _52_10673))
end
| false -> begin
(let _33_2519 = (match ((Microsoft_FStar_Tc_Env.debug env (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10676 = (prob_to_string env orig)
in (let _52_10675 = (let _52_10674 = (Support.List.map (uvi_to_string wl.tcenv) wl.subst)
in (Support.Prims.pipe_right _52_10674 (Support.String.concat "; ")))
in (Support.Microsoft.FStar.Util.fprint2 "Attempting %s\n\tSubst is %s\n" _52_10676 _52_10675)))
end
| false -> begin
()
end)
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let match_num_binders = (fun ( _33_2524 ) ( _33_2527 ) -> (match ((_33_2524, _33_2527)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(let curry = (fun ( n ) ( bs ) ( mk_cod ) -> (let _33_2534 = (Support.Microsoft.FStar.Util.first_N n bs)
in (match (_33_2534) with
| (bs, rest) -> begin
(let _52_10706 = (mk_cod rest)
in (bs, _52_10706))
end)))
in (let l1 = (Support.List.length bs1)
in (let l2 = (Support.List.length bs2)
in (match ((l1 = l2)) with
| true -> begin
(let _52_10710 = (let _52_10707 = (mk_cod1 [])
in (bs1, _52_10707))
in (let _52_10709 = (let _52_10708 = (mk_cod2 [])
in (bs2, _52_10708))
in (_52_10710, _52_10709)))
end
| false -> begin
(match ((l1 > l2)) with
| true -> begin
(let _52_10713 = (curry l2 bs1 mk_cod1)
in (let _52_10712 = (let _52_10711 = (mk_cod2 [])
in (bs2, _52_10711))
in (_52_10713, _52_10712)))
end
| false -> begin
(let _52_10716 = (let _52_10714 = (mk_cod1 [])
in (bs1, _52_10714))
in (let _52_10715 = (curry l1 bs2 mk_cod2)
in (_52_10716, _52_10715)))
end)
end))))
end))
in (match ((t1.Microsoft_FStar_Absyn_Syntax.n, t2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (a), Microsoft_FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvd_eq a.Microsoft_FStar_Absyn_Syntax.v b.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(let _52_10717 = (solve_prob orig None [] wl)
in (solve env _52_10717))
end
| false -> begin
(let _52_10721 = (let _52_10720 = (let _52_10719 = (Microsoft_FStar_Absyn_Util.mk_eq_typ t1 t2)
in (Support.Prims.pipe_left (fun ( _52_10718 ) -> Some (_52_10718)) _52_10719))
in (solve_prob orig _52_10720 [] wl))
in (solve env _52_10721))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs1, c1)), Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs2, c2))) -> begin
(let mk_c = (fun ( c ) ( _33_31 ) -> (match (_33_31) with
| [] -> begin
c
end
| bs -> begin
(let _52_10726 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None c.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Total _52_10726))
end))
in (let _33_2565 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_33_2565) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun ( scope ) ( env ) ( subst ) -> (let c1 = (Microsoft_FStar_Absyn_Util.subst_comp subst c1)
in (let rel = (match ((Support.ST.read Microsoft_FStar_Options.use_eq_at_higher_order)) with
| true -> begin
EQ
end
| false -> begin
problem.relation
end)
in (let _33_2571 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("EQ")))) with
| true -> begin
(let _52_10733 = (let _52_10732 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.Prims.pipe_right _52_10732 Support.Microsoft.FStar.Range.string_of_range))
in (Support.Microsoft.FStar.Util.fprint2 "(%s) Using relation %s at higher order\n" _52_10733 (rel_to_string rel)))
end
| false -> begin
()
end)
in (let _52_10735 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (Support.Prims.pipe_left (fun ( _52_10734 ) -> CProb (_52_10734)) _52_10735)))))))
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
in (let _33_2593 = (match_num_binders (bs1, (mk_t t1')) (bs2, (mk_t t2')))
in (match (_33_2593) with
| ((bs1, t1'), (bs2, t2')) -> begin
(solve_binders env bs1 bs2 orig wl (fun ( scope ) ( env ) ( subst ) -> (let t1' = (Microsoft_FStar_Absyn_Util.subst_typ subst t1')
in (let _52_10746 = (mk_problem scope orig t1' problem.relation t2' None "lambda co-domain")
in (Support.Prims.pipe_left (fun ( _52_10745 ) -> TProb (_52_10745)) _52_10746)))))
end)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine (_), Microsoft_FStar_Absyn_Syntax.Typ_refine (_)) -> begin
(let _33_2607 = (as_refinement env wl t1)
in (match (_33_2607) with
| (x1, phi1) -> begin
(let _33_2610 = (as_refinement env wl t2)
in (match (_33_2610) with
| (x2, phi2) -> begin
(let base_prob = (let _52_10748 = (mk_problem (p_scope orig) orig x1.Microsoft_FStar_Absyn_Syntax.sort problem.relation x2.Microsoft_FStar_Absyn_Syntax.sort problem.element "refinement base type")
in (Support.Prims.pipe_left (fun ( _52_10747 ) -> TProb (_52_10747)) _52_10748))
in (let x1_for_x2 = (let _52_10750 = (Microsoft_FStar_Absyn_Syntax.v_binder x1)
in (let _52_10749 = (Microsoft_FStar_Absyn_Syntax.v_binder x2)
in (Microsoft_FStar_Absyn_Util.mk_subst_one_binder _52_10750 _52_10749)))
in (let phi2 = (Microsoft_FStar_Absyn_Util.subst_typ x1_for_x2 phi2)
in (let mk_imp = (fun ( imp ) ( phi1 ) ( phi2 ) -> (let _52_10767 = (imp phi1 phi2)
in (Support.Prims.pipe_right _52_10767 (guard_on_element problem x1))))
in (let fallback = (fun ( _33_2619 ) -> (match (()) with
| () -> begin
(let impl = (match ((problem.relation = EQ)) with
| true -> begin
(mk_imp Microsoft_FStar_Absyn_Util.mk_iff phi1 phi2)
end
| false -> begin
(mk_imp Microsoft_FStar_Absyn_Util.mk_imp phi1 phi2)
end)
in (let guard = (let _52_10770 = (Support.Prims.pipe_right (p_guard base_prob) Support.Prims.fst)
in (Microsoft_FStar_Absyn_Util.mk_conj _52_10770 impl))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in (match ((problem.relation = EQ)) with
| true -> begin
(let ref_prob = (let _52_10772 = (mk_problem (p_scope orig) orig phi1 EQ phi2 None "refinement formula")
in (Support.Prims.pipe_left (fun ( _52_10771 ) -> TProb (_52_10771)) _52_10772))
in (match ((solve env (let _33_2624 = wl
in {attempting = (ref_prob)::[]; deferred = []; subst = _33_2624.subst; ctr = _33_2624.ctr; slack_vars = _33_2624.slack_vars; defer_ok = false; smt_ok = _33_2624.smt_ok; tcenv = _33_2624.tcenv}))) with
| Failed (_) -> begin
(fallback ())
end
| Success ((subst, _)) -> begin
(let guard = (let _52_10775 = (Support.Prims.pipe_right (p_guard base_prob) Support.Prims.fst)
in (let _52_10774 = (let _52_10773 = (Support.Prims.pipe_right (p_guard ref_prob) Support.Prims.fst)
in (Support.Prims.pipe_right _52_10773 (guard_on_element problem x1)))
in (Microsoft_FStar_Absyn_Util.mk_conj _52_10775 _52_10774)))
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
(let _52_10777 = (destruct_flex_t t1)
in (let _52_10776 = (destruct_flex_t t2)
in (flex_flex orig _52_10777 _52_10776)))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _)) when (problem.relation = EQ) -> begin
(let _52_10778 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _52_10778 t2 wl))
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
in (match ((let _52_10779 = (is_top_level_prob orig)
in (Support.Prims.pipe_left Support.Prims.op_Negation _52_10779))) with
| true -> begin
(let _52_10782 = (Support.Prims.pipe_left (fun ( _52_10780 ) -> TProb (_52_10780)) (let _33_2792 = problem
in {lhs = _33_2792.lhs; relation = new_rel; rhs = _33_2792.rhs; element = _33_2792.element; logical_guard = _33_2792.logical_guard; scope = _33_2792.scope; reason = _33_2792.reason; loc = _33_2792.loc; rank = _33_2792.rank}))
in (let _52_10781 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _52_10782 _52_10781 t2 wl)))
end
| false -> begin
(let _33_2796 = (base_and_refinement env wl t2)
in (match (_33_2796) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _52_10785 = (Support.Prims.pipe_left (fun ( _52_10783 ) -> TProb (_52_10783)) (let _33_2798 = problem
in {lhs = _33_2798.lhs; relation = new_rel; rhs = _33_2798.rhs; element = _33_2798.element; logical_guard = _33_2798.logical_guard; scope = _33_2798.scope; reason = _33_2798.reason; loc = _33_2798.loc; rank = _33_2798.rank}))
in (let _52_10784 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _52_10785 _52_10784 t_base wl)))
end
| Some ((y, phi)) -> begin
(let y' = (let _33_2804 = y
in {Microsoft_FStar_Absyn_Syntax.v = _33_2804.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t1; Microsoft_FStar_Absyn_Syntax.p = _33_2804.Microsoft_FStar_Absyn_Syntax.p})
in (let impl = (guard_on_element problem y' phi)
in (let base_prob = (let _52_10787 = (mk_problem problem.scope orig t1 new_rel y.Microsoft_FStar_Absyn_Syntax.sort problem.element "flex-rigid: base type")
in (Support.Prims.pipe_left (fun ( _52_10786 ) -> TProb (_52_10786)) _52_10787))
in (let guard = (let _52_10788 = (Support.Prims.pipe_right (p_guard base_prob) Support.Prims.fst)
in (Microsoft_FStar_Absyn_Util.mk_conj _52_10788 impl))
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
(let _33_2839 = (base_and_refinement env wl t1)
in (match (_33_2839) with
| (t_base, _) -> begin
(solve_t env (let _33_2840 = problem
in {lhs = t_base; relation = EQ; rhs = _33_2840.rhs; element = _33_2840.element; logical_guard = _33_2840.logical_guard; scope = _33_2840.scope; reason = _33_2840.reason; loc = _33_2840.loc; rank = _33_2840.rank}) wl)
end))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine (_), _) -> begin
(let t2 = (let _52_10789 = (base_and_refinement env wl t2)
in (Support.Prims.pipe_left force_refinement _52_10789))
in (solve_t env (let _33_2849 = problem
in {lhs = _33_2849.lhs; relation = _33_2849.relation; rhs = t2; element = _33_2849.element; logical_guard = _33_2849.logical_guard; scope = _33_2849.scope; reason = _33_2849.reason; loc = _33_2849.loc; rank = _33_2849.rank}) wl))
end
| (_, Microsoft_FStar_Absyn_Syntax.Typ_refine (_)) -> begin
(let t1 = (let _52_10790 = (base_and_refinement env wl t1)
in (Support.Prims.pipe_left force_refinement _52_10790))
in (solve_t env (let _33_2858 = problem
in {lhs = t1; relation = _33_2858.relation; rhs = _33_2858.rhs; element = _33_2858.element; logical_guard = _33_2858.logical_guard; scope = _33_2858.scope; reason = _33_2858.reason; loc = _33_2858.loc; rank = _33_2858.rank}) wl))
end
| ((Microsoft_FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_const (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_app (_), _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_btvar (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_const (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_app (_))) -> begin
(let _33_2898 = (head_matches_delta env wl t1 t2)
in (match (_33_2898) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch, _) -> begin
(let head1 = (let _52_10791 = (Microsoft_FStar_Absyn_Util.head_and_args t1)
in (Support.Prims.pipe_right _52_10791 Support.Prims.fst))
in (let head2 = (let _52_10792 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (Support.Prims.pipe_right _52_10792 Support.Prims.fst))
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
in (match ((let _52_10797 = (let _52_10796 = (may_equate head1)
in (let _52_10795 = (may_equate head2)
in (_52_10796 || _52_10795)))
in (_52_10797 && wl.smt_ok))) with
| true -> begin
(let _52_10801 = (let _52_10800 = (let _52_10799 = (Microsoft_FStar_Absyn_Util.mk_eq_typ t1 t2)
in (Support.Prims.pipe_left (fun ( _52_10798 ) -> Some (_52_10798)) _52_10799))
in (solve_prob orig _52_10800 [] wl))
in (solve env _52_10801))
end
| false -> begin
(giveup env "head mismatch" orig)
end))))
end
| (_, Some ((t1, t2))) -> begin
(solve_t env (let _33_2921 = problem
in {lhs = t1; relation = _33_2921.relation; rhs = t2; element = _33_2921.element; logical_guard = _33_2921.logical_guard; scope = _33_2921.scope; reason = _33_2921.reason; loc = _33_2921.loc; rank = _33_2921.rank}) wl)
end
| (_, None) -> begin
(let _33_2927 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10803 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _52_10802 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (Support.Microsoft.FStar.Util.fprint2 "Head matches: %s and %s\n" _52_10803 _52_10802)))
end
| false -> begin
()
end)
in (let _33_2931 = (Microsoft_FStar_Absyn_Util.head_and_args t1)
in (match (_33_2931) with
| (head, args) -> begin
(let _33_2934 = (Microsoft_FStar_Absyn_Util.head_and_args t2)
in (match (_33_2934) with
| (head', args') -> begin
(let nargs = (Support.List.length args)
in (match ((nargs <> (Support.List.length args'))) with
| true -> begin
(let _52_10808 = (let _52_10807 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (let _52_10806 = (Microsoft_FStar_Absyn_Print.args_to_string args)
in (let _52_10805 = (Microsoft_FStar_Absyn_Print.typ_to_string head')
in (let _52_10804 = (Microsoft_FStar_Absyn_Print.args_to_string args')
in (Support.Microsoft.FStar.Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _52_10807 _52_10806 _52_10805 _52_10804)))))
in (giveup env _52_10808 orig))
end
| false -> begin
(match ((let _52_10809 = (eq_args args args')
in ((nargs = 0) || _52_10809))) with
| true -> begin
(let _52_10810 = (solve_prob orig None [] wl)
in (solve env _52_10810))
end
| false -> begin
(let _33_2938 = (base_and_refinement env wl t1)
in (match (_33_2938) with
| (base1, refinement1) -> begin
(let _33_2941 = (base_and_refinement env wl t2)
in (match (_33_2941) with
| (base2, refinement2) -> begin
(match ((refinement1, refinement2)) with
| (None, None) -> begin
(let _33_2945 = (match ((let _52_10811 = (head_matches env head head)
in (_52_10811 <> FullMatch))) with
| true -> begin
(let _52_10814 = (let _52_10813 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (let _52_10812 = (Microsoft_FStar_Absyn_Print.typ_to_string head')
in (Support.Microsoft.FStar.Util.format2 "Assertion failed: expected full match of %s and %s\n" _52_10813 _52_10812)))
in (failwith (_52_10814)))
end
| false -> begin
()
end)
in (let subprobs = (Support.List.map2 (fun ( a ) ( a' ) -> (match (((Support.Prims.fst a), (Support.Prims.fst a'))) with
| (Support.Microsoft.FStar.Util.Inl (t), Support.Microsoft.FStar.Util.Inl (t')) -> begin
(let _52_10818 = (mk_problem (p_scope orig) orig t EQ t' None "type index")
in (Support.Prims.pipe_left (fun ( _52_10817 ) -> TProb (_52_10817)) _52_10818))
end
| (Support.Microsoft.FStar.Util.Inr (v), Support.Microsoft.FStar.Util.Inr (v')) -> begin
(let _52_10820 = (mk_problem (p_scope orig) orig v EQ v' None "term index")
in (Support.Prims.pipe_left (fun ( _52_10819 ) -> EProb (_52_10819)) _52_10820))
end
| _ -> begin
(failwith ("Impossible"))
end)) args args')
in (let formula = (let _52_10822 = (Support.List.map (fun ( p ) -> (Support.Prims.fst (p_guard p))) subprobs)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _52_10822))
in (let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl))))))
end
| _ -> begin
(let lhs = (force_refinement (base1, refinement1))
in (let rhs = (force_refinement (base2, refinement2))
in (solve_t env (let _33_2969 = problem
in {lhs = lhs; relation = _33_2969.relation; rhs = rhs; element = _33_2969.element; logical_guard = _33_2969.logical_guard; scope = _33_2969.scope; reason = _33_2969.reason; loc = _33_2969.loc; rank = _33_2969.rank}) wl)))
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
in (let solve_eq = (fun ( c1_comp ) ( c2_comp ) -> (let _33_3025 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("EQ")))) with
| true -> begin
(Support.Microsoft.FStar.Util.print_string "solve_c is using an equality constraint\n")
end
| false -> begin
()
end)
in (let sub_probs = (Support.List.map2 (fun ( arg1 ) ( arg2 ) -> (match (((Support.Prims.fst arg1), (Support.Prims.fst arg2))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
(let _52_10837 = (sub_prob t1 EQ t2 "effect arg")
in (Support.Prims.pipe_left (fun ( _52_10836 ) -> TProb (_52_10836)) _52_10837))
end
| (Support.Microsoft.FStar.Util.Inr (e1), Support.Microsoft.FStar.Util.Inr (e2)) -> begin
(let _52_10839 = (sub_prob e1 EQ e2 "effect arg")
in (Support.Prims.pipe_left (fun ( _52_10838 ) -> EProb (_52_10838)) _52_10839))
end
| _ -> begin
(failwith ("impossible"))
end)) c1_comp.Microsoft_FStar_Absyn_Syntax.effect_args c2_comp.Microsoft_FStar_Absyn_Syntax.effect_args)
in (let guard = (let _52_10841 = (Support.List.map (fun ( p ) -> (Support.Prims.pipe_right (p_guard p) Support.Prims.fst)) sub_probs)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _52_10841))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in (match ((Support.Microsoft.FStar.Util.physical_equality c1 c2)) with
| true -> begin
(let _52_10842 = (solve_prob orig None [] wl)
in (solve env _52_10842))
end
| false -> begin
(let _33_3045 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10844 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _52_10843 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (Support.Microsoft.FStar.Util.fprint3 "solve_c %s %s %s\n" _52_10844 (rel_to_string problem.relation) _52_10843)))
end
| false -> begin
()
end)
in (let r = (Microsoft_FStar_Tc_Env.get_range env)
in (let _33_3050 = (c1, c2)
in (match (_33_3050) with
| (c1_0, c2_0) -> begin
(match ((c1.Microsoft_FStar_Absyn_Syntax.n, c2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Total (t1), Microsoft_FStar_Absyn_Syntax.Total (t2)) -> begin
(solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl)
end
| (Microsoft_FStar_Absyn_Syntax.Total (_), Microsoft_FStar_Absyn_Syntax.Comp (_)) -> begin
(let _52_10846 = (let _33_3063 = problem
in (let _52_10845 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c1))
in {lhs = _52_10845; relation = _33_3063.relation; rhs = _33_3063.rhs; element = _33_3063.element; logical_guard = _33_3063.logical_guard; scope = _33_3063.scope; reason = _33_3063.reason; loc = _33_3063.loc; rank = _33_3063.rank}))
in (solve_c env _52_10846 wl))
end
| (Microsoft_FStar_Absyn_Syntax.Comp (_), Microsoft_FStar_Absyn_Syntax.Total (_)) -> begin
(let _52_10848 = (let _33_3072 = problem
in (let _52_10847 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c2))
in {lhs = _33_3072.lhs; relation = _33_3072.relation; rhs = _52_10847; element = _33_3072.element; logical_guard = _33_3072.logical_guard; scope = _33_3072.scope; reason = _33_3072.reason; loc = _33_3072.loc; rank = _33_3072.rank}))
in (solve_c env _52_10848 wl))
end
| (Microsoft_FStar_Absyn_Syntax.Comp (_), Microsoft_FStar_Absyn_Syntax.Comp (_)) -> begin
(match ((let _52_10856 = (let _52_10850 = (Microsoft_FStar_Absyn_Util.is_ml_comp c1)
in (let _52_10849 = (Microsoft_FStar_Absyn_Util.is_ml_comp c2)
in (_52_10850 && _52_10849)))
in (let _52_10855 = (let _52_10854 = (Microsoft_FStar_Absyn_Util.is_total_comp c1)
in (let _52_10853 = (let _52_10852 = (Microsoft_FStar_Absyn_Util.is_total_comp c2)
in (let _52_10851 = (Microsoft_FStar_Absyn_Util.is_ml_comp c2)
in (_52_10852 || _52_10851)))
in (_52_10854 && _52_10853)))
in (_52_10856 || _52_10855)))) with
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
in (let _33_3085 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(Support.Microsoft.FStar.Util.fprint2 "solve_c for %s and %s\n" c1.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str c2.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str)
end
| false -> begin
()
end)
in (match ((Microsoft_FStar_Tc_Env.monad_leq env c1.Microsoft_FStar_Absyn_Syntax.effect_name c2.Microsoft_FStar_Absyn_Syntax.effect_name)) with
| None -> begin
(let _52_10859 = (let _52_10858 = (Microsoft_FStar_Absyn_Print.sli c1.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _52_10857 = (Microsoft_FStar_Absyn_Print.sli c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (Support.Microsoft.FStar.Util.format2 "incompatible monad ordering: %s </: %s" _52_10858 _52_10857)))
in (giveup env _52_10859 orig))
end
| Some (edge) -> begin
(match ((problem.relation = EQ)) with
| true -> begin
(let _33_3105 = (match (c1.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (wp1), _)::(Support.Microsoft.FStar.Util.Inl (wlp1), _)::[] -> begin
(wp1, wlp1)
end
| _ -> begin
(let _52_10862 = (let _52_10861 = (let _52_10860 = (Microsoft_FStar_Absyn_Syntax.range_of_lid c1.Microsoft_FStar_Absyn_Syntax.effect_name)
in (Support.Microsoft.FStar.Range.string_of_range _52_10860))
in (Support.Microsoft.FStar.Util.format1 "Unexpected number of indices on a normalized effect (%s)" _52_10861))
in (failwith (_52_10862)))
end)
in (match (_33_3105) with
| (wp, wlp) -> begin
(let c1 = (let _52_10868 = (let _52_10867 = (let _52_10863 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wp)
in (Microsoft_FStar_Absyn_Syntax.targ _52_10863))
in (let _52_10866 = (let _52_10865 = (let _52_10864 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wlp)
in (Microsoft_FStar_Absyn_Syntax.targ _52_10864))
in (_52_10865)::[])
in (_52_10867)::_52_10866))
in {Microsoft_FStar_Absyn_Syntax.effect_name = c2.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = c1.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _52_10868; Microsoft_FStar_Absyn_Syntax.flags = c1.Microsoft_FStar_Absyn_Syntax.flags})
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
in (let _33_3135 = (match ((c1.Microsoft_FStar_Absyn_Syntax.effect_args, c2.Microsoft_FStar_Absyn_Syntax.effect_args)) with
| ((Support.Microsoft.FStar.Util.Inl (wp1), _)::_, (Support.Microsoft.FStar.Util.Inl (wp2), _)::_) -> begin
(wp1, wp2)
end
| _ -> begin
(let _52_10872 = (let _52_10871 = (Microsoft_FStar_Absyn_Print.sli c1.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _52_10870 = (Microsoft_FStar_Absyn_Print.sli c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (Support.Microsoft.FStar.Util.format2 "Got effects %s and %s, expected normalized effects" _52_10871 _52_10870)))
in (failwith (_52_10872)))
end)
in (match (_33_3135) with
| (wpc1, wpc2) -> begin
(match ((Support.Microsoft.FStar.Util.physical_equality wpc1 wpc2)) with
| true -> begin
(solve_t env (problem_using_guard orig c1.Microsoft_FStar_Absyn_Syntax.result_typ problem.relation c2.Microsoft_FStar_Absyn_Syntax.result_typ None "result type") wl)
end
| false -> begin
(let c2_decl = (Microsoft_FStar_Tc_Env.get_effect_decl env c2.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let g = (match (is_null_wp_2) with
| true -> begin
(let _33_3137 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(Support.Microsoft.FStar.Util.print_string "Using trivial wp ... \n")
end
| false -> begin
()
end)
in (let _52_10878 = (let _52_10877 = (let _52_10876 = (Microsoft_FStar_Absyn_Syntax.targ c1.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _52_10875 = (let _52_10874 = (let _52_10873 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wpc1)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _52_10873))
in (_52_10874)::[])
in (_52_10876)::_52_10875))
in (c2_decl.Microsoft_FStar_Absyn_Syntax.trivial, _52_10877))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_10878 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)))
end
| false -> begin
(let wp2_imp_wp1 = (let _52_10890 = (let _52_10889 = (let _52_10888 = (Microsoft_FStar_Absyn_Syntax.targ c2.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _52_10887 = (let _52_10886 = (Microsoft_FStar_Absyn_Syntax.targ wpc2)
in (let _52_10885 = (let _52_10884 = (let _52_10880 = (let _52_10879 = (Microsoft_FStar_Absyn_Const.kbin Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype)
in (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.imp_lid _52_10879))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _52_10880))
in (let _52_10883 = (let _52_10882 = (let _52_10881 = (edge.Microsoft_FStar_Tc_Env.mlift c1.Microsoft_FStar_Absyn_Syntax.result_typ wpc1)
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _52_10881))
in (_52_10882)::[])
in (_52_10884)::_52_10883))
in (_52_10886)::_52_10885))
in (_52_10888)::_52_10887))
in (c2_decl.Microsoft_FStar_Absyn_Syntax.wp_binop, _52_10889))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_10890 None r))
in (let _52_10895 = (let _52_10894 = (let _52_10893 = (Microsoft_FStar_Absyn_Syntax.targ c2.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _52_10892 = (let _52_10891 = (Microsoft_FStar_Absyn_Syntax.targ wp2_imp_wp1)
in (_52_10891)::[])
in (_52_10893)::_52_10892))
in (c2_decl.Microsoft_FStar_Absyn_Syntax.wp_as_type, _52_10894))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_10895 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) r)))
end)
in (let base_prob = (let _52_10897 = (sub_prob c1.Microsoft_FStar_Absyn_Syntax.result_typ problem.relation c2.Microsoft_FStar_Absyn_Syntax.result_typ "result type")
in (Support.Prims.pipe_left (fun ( _52_10896 ) -> TProb (_52_10896)) _52_10897))
in (let wl = (let _52_10901 = (let _52_10900 = (let _52_10899 = (Support.Prims.pipe_right (p_guard base_prob) Support.Prims.fst)
in (Microsoft_FStar_Absyn_Util.mk_conj _52_10899 g))
in (Support.Prims.pipe_left (fun ( _52_10898 ) -> Some (_52_10898)) _52_10900))
in (solve_prob orig _52_10901 [] wl))
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
and solve_e' = (fun ( env ) ( problem ) ( wl ) -> (let problem = (let _33_3153 = problem
in {lhs = _33_3153.lhs; relation = EQ; rhs = _33_3153.rhs; element = _33_3153.element; logical_guard = _33_3153.logical_guard; scope = _33_3153.scope; reason = _33_3153.reason; loc = _33_3153.loc; rank = _33_3153.rank})
in (let e1 = problem.lhs
in (let e2 = problem.rhs
in (let orig = EProb (problem)
in (let sub_prob = (fun ( lhs ) ( rhs ) ( reason ) -> (mk_problem (p_scope orig) orig lhs EQ rhs None reason))
in (let _33_3165 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10911 = (prob_to_string env orig)
in (Support.Microsoft.FStar.Util.fprint1 "Attempting:\n%s\n" _52_10911))
end
| false -> begin
()
end)
in (let flex_rigid = (fun ( _33_3172 ) ( e2 ) -> (match (_33_3172) with
| (e1, u1, t1, args1) -> begin
(let maybe_vars1 = (pat_vars env [] args1)
in (let sub_problems = (fun ( xs ) ( args2 ) -> (let _33_3199 = (let _52_10927 = (Support.Prims.pipe_right args2 (Support.List.map (fun ( _33_34 ) -> (match (_33_34) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (let _33_3186 = (new_tvar t.Microsoft_FStar_Absyn_Syntax.pos xs kk)
in (match (_33_3186) with
| (gi_xi, gi) -> begin
(let gi_pi = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (gi, args1) (Some (kk)) t.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_10923 = (let _52_10922 = (sub_prob gi_pi t "type index")
in (Support.Prims.pipe_left (fun ( _52_10921 ) -> TProb (_52_10921)) _52_10922))
in ((Support.Microsoft.FStar.Util.Inl (gi_xi), imp), _52_10923)))
end)))
end
| (Support.Microsoft.FStar.Util.Inr (v), imp) -> begin
(let tt = (Microsoft_FStar_Tc_Recheck.recompute_typ v)
in (let _33_3195 = (new_evar v.Microsoft_FStar_Absyn_Syntax.pos xs tt)
in (match (_33_3195) with
| (gi_xi, gi) -> begin
(let gi_pi = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (gi, args1) (Some (tt)) v.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_10926 = (let _52_10925 = (sub_prob gi_pi v "expression index")
in (Support.Prims.pipe_left (fun ( _52_10924 ) -> EProb (_52_10924)) _52_10925))
in ((Support.Microsoft.FStar.Util.Inr (gi_xi), imp), _52_10926)))
end)))
end))))
in (Support.Prims.pipe_right _52_10927 Support.List.unzip))
in (match (_33_3199) with
| (gi_xi, gi_pi) -> begin
(let formula = (let _52_10929 = (Support.List.map (fun ( p ) -> (Support.Prims.pipe_right (p_guard p) Support.Prims.fst)) gi_pi)
in (Microsoft_FStar_Absyn_Util.mk_conj_l _52_10929))
in (gi_xi, gi_pi, formula))
end)))
in (let project_e = (fun ( head2 ) ( args2 ) -> (let giveup = (fun ( reason ) -> (let _52_10936 = (Support.Microsoft.FStar.Util.format1 "flex-rigid: refusing to project expressions (%s)" reason)
in (giveup env _52_10936 orig)))
in (match ((let _52_10937 = (Microsoft_FStar_Absyn_Util.compress_exp head2)
in _52_10937.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (y) -> begin
(let _33_3216 = (match ((Microsoft_FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some ((xs, c)) -> begin
(xs, (Microsoft_FStar_Absyn_Util.comp_result c))
end)
in (match (_33_3216) with
| (all_xs, tres) -> begin
(match (((Support.List.length all_xs) <> (Support.List.length args1))) with
| true -> begin
(let _52_10940 = (let _52_10939 = (Microsoft_FStar_Absyn_Print.binders_to_string ", " all_xs)
in (let _52_10938 = (Microsoft_FStar_Absyn_Print.args_to_string args2)
in (Support.Microsoft.FStar.Util.format2 "unequal arity:\n\texpetced binders %s\n\tgot args {%s}" _52_10939 _52_10938)))
in (giveup _52_10940))
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
(match ((let _52_10945 = (Microsoft_FStar_Absyn_Util.compress_exp arg)
in _52_10945.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (z) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvar_eq y z)) with
| true -> begin
(let _33_3268 = (sub_problems all_xs args2)
in (match (_33_3268) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (let _52_10949 = (let _52_10948 = (let _52_10947 = (let _52_10946 = (Microsoft_FStar_Absyn_Util.bvar_to_exp xi)
in (_52_10946, gi_xi))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' _52_10947 None e1.Microsoft_FStar_Absyn_Syntax.pos))
in (all_xs, _52_10948))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _52_10949 None e1.Microsoft_FStar_Absyn_Syntax.pos))
in (let _33_3270 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10953 = (Microsoft_FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _52_10952 = (Microsoft_FStar_Absyn_Print.exp_to_string sol)
in (let _52_10951 = (let _52_10950 = (Support.Prims.pipe_right gi_pi (Support.List.map (prob_to_string env)))
in (Support.Prims.pipe_right _52_10950 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.fprint3 "Projected: %s -> %s\nSubprobs=\n%s\n" _52_10953 _52_10952 _52_10951))))
end
| false -> begin
()
end)
in (let _52_10955 = (let _52_10954 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _52_10954))
in (solve env _52_10955))))
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
(let _52_10958 = (let _52_10957 = (Microsoft_FStar_Absyn_Print.binder_to_string x)
in (let _52_10956 = (Microsoft_FStar_Absyn_Print.arg_to_string arg)
in (Support.Microsoft.FStar.Util.format2 "type incorrect term---impossible: expected %s; got %s\n" _52_10957 _52_10956)))
in (giveup _52_10958))
end))
in (aux (Support.List.rev all_xs) (Support.List.rev args1)))
end)
end))
end
| _ -> begin
(giveup "rigid head term is not a variable")
end)))
in (let imitate_or_project_e = (fun ( _33_3284 ) -> (match (()) with
| () -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid: not a pattern" orig wl))
end
| false -> begin
(let _33_3285 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10962 = (Microsoft_FStar_Absyn_Print.exp_to_string e1)
in (let _52_10961 = (Microsoft_FStar_Absyn_Print.exp_to_string e2)
in (Support.Microsoft.FStar.Util.fprint2 "Imitating expressions: %s =?= %s\n" _52_10962 _52_10961)))
end
| false -> begin
()
end)
in (let _33_3289 = (Microsoft_FStar_Absyn_Util.head_and_args_e e2)
in (match (_33_3289) with
| (head2, args2) -> begin
(let fvhead = (Microsoft_FStar_Absyn_Util.freevars_exp head2)
in (let _33_3294 = (occurs_check_e env (u1, t1) head2)
in (match (_33_3294) with
| (occurs_ok, _) -> begin
(match ((let _52_10963 = (Microsoft_FStar_Absyn_Util.fvs_included fvhead Microsoft_FStar_Absyn_Syntax.no_fvs)
in (_52_10963 && occurs_ok))) with
| true -> begin
(let _33_3302 = (match ((Microsoft_FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some ((xs, c)) -> begin
(xs, (Microsoft_FStar_Absyn_Util.comp_result c))
end)
in (match (_33_3302) with
| (xs, tres) -> begin
(let _33_3306 = (sub_problems xs args2)
in (match (_33_3306) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (let body = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.Microsoft_FStar_Absyn_Syntax.pos)
in (match (xs) with
| [] -> begin
body
end
| _ -> begin
(let _52_10965 = (let _52_10964 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.Microsoft_FStar_Absyn_Syntax.pos)
in (xs, _52_10964))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _52_10965 None e1.Microsoft_FStar_Absyn_Syntax.pos))
end))
in (let _33_3312 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10969 = (Microsoft_FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _52_10968 = (Microsoft_FStar_Absyn_Print.exp_to_string sol)
in (let _52_10967 = (let _52_10966 = (Support.Prims.pipe_right gi_pi (Support.List.map (prob_to_string env)))
in (Support.Prims.pipe_right _52_10966 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.fprint3 "Imitated: %s -> %s\nSubprobs=\n%s\n" _52_10969 _52_10968 _52_10967))))
end
| false -> begin
()
end)
in (let _52_10971 = (let _52_10970 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _52_10970))
in (solve env _52_10971))))
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
in (let _33_3324 = (occurs_check_e env (u1, t1) e2)
in (match (_33_3324) with
| (occurs_ok, _) -> begin
(match ((let _52_10974 = (let _52_10973 = (Support.Microsoft.FStar.Util.set_is_subset_of fvs2.Microsoft_FStar_Absyn_Syntax.ftvs fvs1.Microsoft_FStar_Absyn_Syntax.ftvs)
in (let _52_10972 = (Support.Microsoft.FStar.Util.set_is_subset_of fvs2.Microsoft_FStar_Absyn_Syntax.fxvs fvs1.Microsoft_FStar_Absyn_Syntax.fxvs)
in (_52_10973 && _52_10972)))
in (_52_10974 && occurs_ok))) with
| true -> begin
(let sol = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs' (xs, e2) None e1.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_10975 = (solve_prob orig None ((UE (((u1, t1), sol)))::[]) wl)
in (solve env _52_10975)))
end
| false -> begin
(imitate_or_project_e ())
end)
end))))
end)))))
end))
in (let flex_flex = (fun ( _33_3331 ) ( _33_3336 ) -> (match ((_33_3331, _33_3336)) with
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
(match ((let _52_10980 = (binders_eq xs ys)
in ((Support.Microsoft.FStar.Unionfind.equivalent u1 u2) && _52_10980))) with
| true -> begin
(solve env wl)
end
| false -> begin
(let zs = (intersect_vars xs ys)
in (let tt = (Microsoft_FStar_Tc_Recheck.recompute_typ e2)
in (let _33_3357 = (let _52_10981 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_evar _52_10981 zs tt))
in (match (_33_3357) with
| (u, _) -> begin
(let sub1 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (xs, u) (Some (t1)) e1.Microsoft_FStar_Absyn_Syntax.pos)
in (let sub2 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (ys, u) (Some (t2)) e1.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_10982 = (solve_prob orig None ((UE (((u1, t1), sub1)))::(UE (((u2, t2), sub2)))::[]) wl)
in (solve env _52_10982))))
end))))
end)
end)))
end))
in (let smt_fallback = (fun ( e1 ) ( e2 ) -> (match (wl.smt_ok) with
| true -> begin
(let _33_3363 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_10987 = (prob_to_string env orig)
in (Support.Microsoft.FStar.Util.fprint1 "Using SMT to solve:\n%s\n" _52_10987))
end
| false -> begin
()
end)
in (let _33_3368 = (let _52_10989 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _52_10988 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _52_10989 _52_10988 Microsoft_FStar_Absyn_Syntax.ktype)))
in (match (_33_3368) with
| (t, _) -> begin
(let _52_10993 = (let _52_10992 = (let _52_10991 = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (Support.Prims.pipe_left (fun ( _52_10990 ) -> Some (_52_10990)) _52_10991))
in (solve_prob orig _52_10992 [] wl))
in (solve env _52_10993))
end)))
end
| false -> begin
(giveup env "no SMT solution permitted" orig)
end))
in (match ((e1.Microsoft_FStar_Absyn_Syntax.n, e2.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e1, _, _)), _) -> begin
(solve_e env (let _33_3379 = problem
in {lhs = e1; relation = _33_3379.relation; rhs = _33_3379.rhs; element = _33_3379.element; logical_guard = _33_3379.logical_guard; scope = _33_3379.scope; reason = _33_3379.reason; loc = _33_3379.loc; rank = _33_3379.rank}) wl)
end
| (_, Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e2, _, _))) -> begin
(solve_e env (let _33_3391 = problem
in {lhs = _33_3391.lhs; relation = _33_3391.relation; rhs = e2; element = _33_3391.element; logical_guard = _33_3391.logical_guard; scope = _33_3391.scope; reason = _33_3391.reason; loc = _33_3391.loc; rank = _33_3391.rank}) wl)
end
| ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) | ((Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) | ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) | ((Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) -> begin
(let _52_10995 = (destruct_flex_e e1)
in (let _52_10994 = (destruct_flex_e e2)
in (flex_flex _52_10995 _52_10994)))
end
| ((Microsoft_FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _)) -> begin
(let _52_10996 = (destruct_flex_e e1)
in (flex_rigid _52_10996 e2))
end
| ((_, Microsoft_FStar_Absyn_Syntax.Exp_uvar (_))) | ((_, Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)))) -> begin
(let _52_10997 = (destruct_flex_e e2)
in (flex_rigid _52_10997 e1))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (x1), Microsoft_FStar_Absyn_Syntax.Exp_bvar (x1')) -> begin
(match ((Microsoft_FStar_Absyn_Util.bvd_eq x1.Microsoft_FStar_Absyn_Syntax.v x1'.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(let _52_10998 = (solve_prob orig None [] wl)
in (solve env _52_10998))
end
| false -> begin
(let _52_11004 = (let _52_11003 = (let _52_11002 = (let _52_11001 = (Microsoft_FStar_Tc_Recheck.recompute_typ e1)
in (let _52_11000 = (Microsoft_FStar_Tc_Recheck.recompute_typ e2)
in (Microsoft_FStar_Absyn_Util.mk_eq _52_11001 _52_11000 e1 e2)))
in (Support.Prims.pipe_left (fun ( _52_10999 ) -> Some (_52_10999)) _52_11002))
in (solve_prob orig _52_11003 [] wl))
in (solve env _52_11004))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv1, _)), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv1', _))) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv1.Microsoft_FStar_Absyn_Syntax.v fv1'.Microsoft_FStar_Absyn_Syntax.v)) with
| true -> begin
(let _52_11005 = (solve_prob orig None [] wl)
in (solve env _52_11005))
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
(let _52_11010 = (solve_prob orig None [] wl)
in (solve env _52_11010))
end
| false -> begin
(giveup env "constants unequal" orig)
end))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)), _) -> begin
(let _52_11012 = (let _33_3590 = problem
in (let _52_11011 = (whnf_e env e1)
in {lhs = _52_11011; relation = _33_3590.relation; rhs = _33_3590.rhs; element = _33_3590.element; logical_guard = _33_3590.logical_guard; scope = _33_3590.scope; reason = _33_3590.reason; loc = _33_3590.loc; rank = _33_3590.rank}))
in (solve_e env _52_11012 wl))
end
| (_, Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _52_11014 = (let _33_3611 = problem
in (let _52_11013 = (whnf_e env e2)
in {lhs = _33_3611.lhs; relation = _33_3611.relation; rhs = _52_11013; element = _33_3611.element; logical_guard = _33_3611.logical_guard; scope = _33_3611.scope; reason = _33_3611.reason; loc = _33_3611.loc; rank = _33_3611.rank}))
in (solve_e env _52_11014 wl))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app ((head1, args1)), Microsoft_FStar_Absyn_Syntax.Exp_app ((head2, args2))) -> begin
(let orig_wl = wl
in (let rec solve_args = (fun ( sub_probs ) ( wl ) ( args1 ) ( args2 ) -> (match ((args1, args2)) with
| ([], []) -> begin
(let guard = (let _52_11024 = (let _52_11023 = (Support.List.map p_guard sub_probs)
in (Support.Prims.pipe_right _52_11023 (Support.List.map Support.Prims.fst)))
in (Microsoft_FStar_Absyn_Util.mk_conj_l _52_11024))
in (let g = (simplify_formula env guard)
in (let g = (Microsoft_FStar_Absyn_Util.compress_typ g)
in (match (g.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
(let _52_11025 = (solve_prob orig None wl.subst (let _33_3636 = orig_wl
in {attempting = _33_3636.attempting; deferred = _33_3636.deferred; subst = []; ctr = _33_3636.ctr; slack_vars = _33_3636.slack_vars; defer_ok = _33_3636.defer_ok; smt_ok = _33_3636.smt_ok; tcenv = _33_3636.tcenv}))
in (solve env _52_11025))
end
| _ -> begin
(let _33_3643 = (let _52_11027 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _52_11026 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _52_11027 _52_11026 Microsoft_FStar_Absyn_Syntax.ktype)))
in (match (_33_3643) with
| (t, _) -> begin
(let guard = (let _52_11028 = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (Microsoft_FStar_Absyn_Util.mk_disj g _52_11028))
in (let _52_11029 = (solve_prob orig (Some (guard)) wl.subst (let _33_3645 = orig_wl
in {attempting = _33_3645.attempting; deferred = _33_3645.deferred; subst = []; ctr = _33_3645.ctr; slack_vars = _33_3645.slack_vars; defer_ok = _33_3645.defer_ok; smt_ok = _33_3645.smt_ok; tcenv = _33_3645.tcenv}))
in (solve env _52_11029)))
end))
end))))
end
| (arg1::rest1, arg2::rest2) -> begin
(let prob = (match (((Support.Prims.fst arg1), (Support.Prims.fst arg2))) with
| (Support.Microsoft.FStar.Util.Inl (t1), Support.Microsoft.FStar.Util.Inl (t2)) -> begin
(let _52_11031 = (mk_problem (p_scope orig) orig t1 EQ t2 None "expression type arg")
in (Support.Prims.pipe_left (fun ( _52_11030 ) -> TProb (_52_11030)) _52_11031))
end
| (Support.Microsoft.FStar.Util.Inr (e1), Support.Microsoft.FStar.Util.Inr (e2)) -> begin
(let _52_11033 = (mk_problem (p_scope orig) orig e1 EQ e2 None "expression arg")
in (Support.Prims.pipe_left (fun ( _52_11032 ) -> EProb (_52_11032)) _52_11033))
end
| _ -> begin
(failwith ("Impossible: ill-typed expression"))
end)
in (match ((solve env (let _33_3667 = wl
in {attempting = (prob)::[]; deferred = []; subst = _33_3667.subst; ctr = _33_3667.ctr; slack_vars = _33_3667.slack_vars; defer_ok = false; smt_ok = false; tcenv = _33_3667.tcenv}))) with
| Failed (_) -> begin
(smt_fallback e1 e2)
end
| Success ((subst, _)) -> begin
(solve_args ((prob)::sub_probs) (let _33_3677 = wl
in {attempting = _33_3677.attempting; deferred = _33_3677.deferred; subst = subst; ctr = _33_3677.ctr; slack_vars = _33_3677.slack_vars; defer_ok = _33_3677.defer_ok; smt_ok = _33_3677.smt_ok; tcenv = _33_3677.tcenv}) rest1 rest2)
end))
end
| _ -> begin
(failwith ("Impossible: lengths defer"))
end))
in (let rec match_head_and_args = (fun ( head1 ) ( head2 ) -> (match ((let _52_11041 = (let _52_11038 = (Microsoft_FStar_Absyn_Util.compress_exp head1)
in _52_11038.Microsoft_FStar_Absyn_Syntax.n)
in (let _52_11040 = (let _52_11039 = (Microsoft_FStar_Absyn_Util.compress_exp head2)
in _52_11039.Microsoft_FStar_Absyn_Syntax.n)
in (_52_11041, _52_11040)))) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (x), Microsoft_FStar_Absyn_Syntax.Exp_bvar (y)) when ((Microsoft_FStar_Absyn_Util.bvar_eq x y) && ((Support.List.length args1) = (Support.List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _)), Microsoft_FStar_Absyn_Syntax.Exp_fvar ((g, _))) when (let _52_11044 = (let _52_11043 = (let _52_11042 = (Microsoft_FStar_Absyn_Util.is_interpreted f.Microsoft_FStar_Absyn_Syntax.v)
in (not (_52_11042)))
in ((Microsoft_FStar_Absyn_Util.fvar_eq f g) && _52_11043))
in (_52_11044 && ((Support.List.length args1) = (Support.List.length args2)))) -> begin
(solve_args [] wl args1 args2)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _, _)), _) -> begin
(match_head_and_args e head2)
end
| (_, Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _, _))) -> begin
(match_head_and_args head1 e)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_abs (_), _) -> begin
(let _52_11046 = (let _33_3726 = problem
in (let _52_11045 = (whnf_e env e1)
in {lhs = _52_11045; relation = _33_3726.relation; rhs = _33_3726.rhs; element = _33_3726.element; logical_guard = _33_3726.logical_guard; scope = _33_3726.scope; reason = _33_3726.reason; loc = _33_3726.loc; rank = _33_3726.rank}))
in (solve_e env _52_11046 wl))
end
| (_, Microsoft_FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(let _52_11048 = (let _33_3734 = problem
in (let _52_11047 = (whnf_e env e2)
in {lhs = _33_3734.lhs; relation = _33_3734.relation; rhs = _52_11047; element = _33_3734.element; logical_guard = _33_3734.logical_guard; scope = _33_3734.scope; reason = _33_3734.reason; loc = _33_3734.loc; rank = _33_3734.rank}))
in (solve_e env _52_11048 wl))
end
| _ -> begin
(smt_fallback e1 e2)
end))
in (match_head_and_args head1 head2))))
end
| _ -> begin
(let _33_3743 = (let _52_11050 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _52_11049 = (Microsoft_FStar_Tc_Env.binders env)
in (new_tvar _52_11050 _52_11049 Microsoft_FStar_Absyn_Syntax.ktype)))
in (match (_33_3743) with
| (t, _) -> begin
(let guard = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (let _33_3745 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_11051 = (Microsoft_FStar_Absyn_Print.typ_to_string guard)
in (Support.Microsoft.FStar.Util.fprint1 "Emitting guard %s\n" _52_11051))
end
| false -> begin
()
end)
in (let _52_11055 = (let _52_11054 = (let _52_11053 = (Microsoft_FStar_Absyn_Util.mk_eq t t e1 e2)
in (Support.Prims.pipe_left (fun ( _52_11052 ) -> Some (_52_11052)) _52_11053))
in (solve_prob orig _52_11054 [] wl))
in (solve env _52_11055))))
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
in (let carry = (let _52_11079 = (Support.List.map (fun ( _33_3762 ) -> (match (_33_3762) with
| (_, x) -> begin
(prob_to_string env x)
end)) g.deferred.carry)
in (Support.Prims.pipe_right _52_11079 (Support.String.concat ",\n")))
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
in (let _52_11096 = (let _33_3793 = g
in (let _52_11095 = (let _52_11094 = (let _52_11093 = (let _52_11092 = (let _52_11091 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_52_11091)::[])
in (_52_11092, f))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _52_11093 None f.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.Prims.pipe_left (fun ( _52_11090 ) -> NonTrivial (_52_11090)) _52_11094))
in {guard_f = _52_11095; deferred = _33_3793.deferred; implicits = _33_3793.implicits}))
in Some (_52_11096)))
end))

let apply_guard = (fun ( g ) ( e ) -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _33_3800 = g
in (let _52_11108 = (let _52_11107 = (let _52_11106 = (let _52_11105 = (let _52_11104 = (let _52_11103 = (Microsoft_FStar_Absyn_Syntax.varg e)
in (_52_11103)::[])
in (f, _52_11104))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_11105))
in (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn f.Microsoft_FStar_Absyn_Syntax.pos (Some (Microsoft_FStar_Absyn_Syntax.ktype))) _52_11106))
in NonTrivial (_52_11107))
in {guard_f = _52_11108; deferred = _33_3800.deferred; implicits = _33_3800.implicits}))
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
(let _52_11115 = (Microsoft_FStar_Absyn_Util.mk_conj f1 f2)
in NonTrivial (_52_11115))
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

let binop_guard = (fun ( f ) ( g1 ) ( g2 ) -> (let _52_11138 = (f g1.guard_f g2.guard_f)
in {guard_f = _52_11138; deferred = {carry = (Support.List.append g1.deferred.carry g2.deferred.carry); slack = (Support.List.append g1.deferred.slack g2.deferred.slack)}; implicits = (Support.List.append g1.implicits g2.implicits)}))

let conj_guard = (fun ( g1 ) ( g2 ) -> (binop_guard conj_guard_f g1 g2))

let imp_guard = (fun ( g1 ) ( g2 ) -> (binop_guard imp_guard_f g1 g2))

let close_guard = (fun ( binders ) ( g ) -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _33_3850 = g
in (let _52_11153 = (let _52_11152 = (Microsoft_FStar_Absyn_Util.close_forall binders f)
in (Support.Prims.pipe_right _52_11152 (fun ( _52_11151 ) -> NonTrivial (_52_11151))))
in {guard_f = _52_11153; deferred = _33_3850.deferred; implicits = _33_3850.implicits}))
end))

let mk_guard = (fun ( g ) ( ps ) ( slack ) ( locs ) -> {guard_f = g; deferred = {carry = ps; slack = slack}; implicits = []})

let new_t_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) -> (let reason = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _52_11165 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env lhs)
in (let _52_11164 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env rhs)
in (Support.Microsoft.FStar.Util.format3 "Top-level:\n%s\n\t%s\n%s" _52_11165 (rel_to_string rel) _52_11164)))
end
| false -> begin
"TOP"
end)
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

let new_t_prob = (fun ( env ) ( t1 ) ( rel ) ( t2 ) -> (let x = (let _52_11174 = (Microsoft_FStar_Tc_Env.get_range env)
in (Microsoft_FStar_Absyn_Util.gen_bvar_p _52_11174 t1))
in (let env = (Microsoft_FStar_Tc_Env.push_local_binding env (Microsoft_FStar_Tc_Env.Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))))
in (let p = (let _52_11178 = (let _52_11176 = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (Support.Prims.pipe_left (fun ( _52_11175 ) -> Some (_52_11175)) _52_11176))
in (let _52_11177 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_t_problem env t1 rel t2 _52_11178 _52_11177)))
in (TProb (p), x)))))

let new_k_problem = (fun ( env ) ( lhs ) ( rel ) ( rhs ) ( elt ) ( loc ) -> (let reason = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _52_11186 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env lhs)
in (let _52_11185 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env rhs)
in (Support.Microsoft.FStar.Util.format3 "Top-level:\n%s\n\t%s\n%s" _52_11186 (rel_to_string rel) _52_11185)))
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
(let _33_3884 = (match ((Microsoft_FStar_Tc_Env.debug env Microsoft_FStar_Options.High)) with
| true -> begin
(let _52_11191 = (Microsoft_FStar_Absyn_Print.typ_to_string f)
in (Support.Microsoft.FStar.Util.fprint1 "Simplifying guard %s\n" _52_11191))
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
in (let _33_3892 = g
in {guard_f = f; deferred = _33_3892.deferred; implicits = _33_3892.implicits}))))
end))

let solve_and_commit = (fun ( env ) ( probs ) ( err ) -> (let probs = (match ((Support.ST.read Microsoft_FStar_Options.eager_inference)) with
| true -> begin
(let _33_3897 = probs
in {attempting = _33_3897.attempting; deferred = _33_3897.deferred; subst = _33_3897.subst; ctr = _33_3897.ctr; slack_vars = _33_3897.slack_vars; defer_ok = false; smt_ok = _33_3897.smt_ok; tcenv = _33_3897.tcenv})
end
| false -> begin
probs
end)
in (let sol = (solve env probs)
in (match (sol) with
| Success ((s, deferred)) -> begin
(let _33_3905 = (commit env s)
in Some (deferred))
end
| Failed ((d, s)) -> begin
(let _33_3911 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _52_11203 = (explain env d s)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.print_string _52_11203))
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
(let _52_11215 = (let _52_11214 = (let _52_11213 = (let _52_11212 = (Support.Prims.pipe_right (p_guard prob) Support.Prims.fst)
in (Support.Prims.pipe_right _52_11212 (fun ( _52_11211 ) -> NonTrivial (_52_11211))))
in {guard_f = _52_11213; deferred = d; implicits = []})
in (simplify_guard env _52_11214))
in (Support.Prims.pipe_left (fun ( _52_11210 ) -> Some (_52_11210)) _52_11215))
end))

let try_keq = (fun ( env ) ( k1 ) ( k2 ) -> (let _33_3922 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_11223 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (let _52_11222 = (Microsoft_FStar_Absyn_Print.kind_to_string k2)
in (Support.Microsoft.FStar.Util.fprint2 "try_keq of %s and %s\n" _52_11223 _52_11222)))
end
| false -> begin
()
end)
in (let prob = (let _52_11228 = (let _52_11227 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env k1)
in (let _52_11226 = (Microsoft_FStar_Tc_Normalize.norm_kind ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env k2)
in (let _52_11225 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_k_problem env _52_11227 EQ _52_11226 None _52_11225))))
in (Support.Prims.pipe_left (fun ( _52_11224 ) -> KProb (_52_11224)) _52_11228))
in (let _52_11230 = (solve_and_commit env (singleton env prob) (fun ( _33_3925 ) -> None))
in (Support.Prims.pipe_left (with_guard env prob) _52_11230)))))

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
(let _52_11241 = (let _52_11240 = (let _52_11239 = (Microsoft_FStar_Tc_Errors.incompatible_kinds env k2 k1)
in (_52_11239, r))
in Microsoft_FStar_Absyn_Syntax.Error (_52_11240))
in (raise (_52_11241)))
end
| Some (t) -> begin
(let _52_11244 = (let _52_11243 = (let _52_11242 = (Microsoft_FStar_Tc_Errors.expected_typ_of_kind env k2 t k1)
in (_52_11242, r))
in Microsoft_FStar_Absyn_Syntax.Error (_52_11243))
in (raise (_52_11244)))
end))
end
| Some (g) -> begin
g
end))

let subkind = (fun ( env ) ( k1 ) ( k2 ) -> (let _33_3944 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_11254 = (let _52_11251 = (Microsoft_FStar_Tc_Env.get_range env)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _52_11251))
in (let _52_11253 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (let _52_11252 = (Microsoft_FStar_Absyn_Print.kind_to_string k2)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) subkind of %s and %s\n" _52_11254 _52_11253 _52_11252))))
end
| false -> begin
()
end)
in (let prob = (let _52_11259 = (let _52_11258 = (whnf_k env k1)
in (let _52_11257 = (whnf_k env k2)
in (let _52_11256 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_k_problem env _52_11258 SUB _52_11257 None _52_11256))))
in (Support.Prims.pipe_left (fun ( _52_11255 ) -> KProb (_52_11255)) _52_11259))
in (let res = (let _52_11266 = (let _52_11265 = (solve_and_commit env (singleton env prob) (fun ( _33_3947 ) -> (let _52_11264 = (let _52_11263 = (let _52_11262 = (Microsoft_FStar_Tc_Errors.incompatible_kinds env k1 k2)
in (let _52_11261 = (Microsoft_FStar_Tc_Env.get_range env)
in (_52_11262, _52_11261)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_11263))
in (raise (_52_11264)))))
in (Support.Prims.pipe_left (with_guard env prob) _52_11265))
in (Support.Microsoft.FStar.Util.must _52_11266))
in res))))

let try_teq = (fun ( env ) ( t1 ) ( t2 ) -> (let _33_3953 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_11274 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _52_11273 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (Support.Microsoft.FStar.Util.fprint2 "try_teq of %s and %s\n" _52_11274 _52_11273)))
end
| false -> begin
()
end)
in (let prob = (let _52_11277 = (let _52_11276 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_t_problem env t1 EQ t2 None _52_11276))
in (Support.Prims.pipe_left (fun ( _52_11275 ) -> TProb (_52_11275)) _52_11277))
in (let g = (let _52_11279 = (solve_and_commit env (singleton env prob) (fun ( _33_3956 ) -> None))
in (Support.Prims.pipe_left (with_guard env prob) _52_11279))
in g))))

let teq = (fun ( env ) ( t1 ) ( t2 ) -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _52_11289 = (let _52_11288 = (let _52_11287 = (Microsoft_FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _52_11286 = (Microsoft_FStar_Tc_Env.get_range env)
in (_52_11287, _52_11286)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_11288))
in (raise (_52_11289)))
end
| Some (g) -> begin
(let _33_3965 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_11292 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (let _52_11291 = (Microsoft_FStar_Absyn_Print.typ_to_string t2)
in (let _52_11290 = (guard_to_string env g)
in (Support.Microsoft.FStar.Util.fprint3 "teq of %s and %s succeeded with guard %s\n" _52_11292 _52_11291 _52_11290))))
end
| false -> begin
()
end)
in g)
end))

let try_subtype = (fun ( env ) ( t1 ) ( t2 ) -> (let _33_3970 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_11300 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _52_11299 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.fprint2 "try_subtype of %s and %s\n" _52_11300 _52_11299)))
end
| false -> begin
()
end)
in (let _33_3974 = (new_t_prob env t1 SUB t2)
in (match (_33_3974) with
| (prob, x) -> begin
(let g = (let _52_11302 = (solve_and_commit env (singleton env prob) (fun ( _33_3975 ) -> None))
in (Support.Prims.pipe_left (with_guard env prob) _52_11302))
in (let _33_3978 = (match ((let _52_11303 = (Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))
in (_52_11303 && (Support.Microsoft.FStar.Util.is_some g)))) with
| true -> begin
(let _52_11307 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _52_11306 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _52_11305 = (let _52_11304 = (Support.Microsoft.FStar.Util.must g)
in (guard_to_string env _52_11304))
in (Support.Microsoft.FStar.Util.fprint3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _52_11307 _52_11306 _52_11305))))
end
| false -> begin
()
end)
in (abstract_guard x g)))
end))))

let subtype_fail = (fun ( env ) ( t1 ) ( t2 ) -> (let _52_11314 = (let _52_11313 = (let _52_11312 = (Microsoft_FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _52_11311 = (Microsoft_FStar_Tc_Env.get_range env)
in (_52_11312, _52_11311)))
in Microsoft_FStar_Absyn_Syntax.Error (_52_11313))
in (raise (_52_11314))))

let subtype = (fun ( env ) ( t1 ) ( t2 ) -> (match ((try_subtype env t1 t2)) with
| Some (f) -> begin
f
end
| None -> begin
(subtype_fail env t1 t2)
end))

let sub_comp = (fun ( env ) ( c1 ) ( c2 ) -> (let _33_3992 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_11328 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c1)
in (let _52_11327 = (Microsoft_FStar_Absyn_Print.comp_typ_to_string c2)
in (Support.Microsoft.FStar.Util.fprint2 "sub_comp of %s and %s\n" _52_11328 _52_11327)))
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
in (let prob = (let _52_11331 = (let _52_11330 = (Microsoft_FStar_Tc_Env.get_range env)
in (new_problem env c1 rel c2 None _52_11330 "sub_comp"))
in (Support.Prims.pipe_left (fun ( _52_11329 ) -> CProb (_52_11329)) _52_11331))
in (let _52_11333 = (solve_and_commit env (singleton env prob) (fun ( _33_3996 ) -> None))
in (Support.Prims.pipe_left (with_guard env prob) _52_11333))))))

let solve_deferred_constraints = (fun ( env ) ( g ) -> (let fail = (fun ( _33_4003 ) -> (match (_33_4003) with
| (d, s) -> begin
(let msg = (explain env d s)
in (raise (Microsoft_FStar_Absyn_Syntax.Error ((msg, (p_loc d))))))
end))
in (let _33_4008 = (match ((let _52_11340 = (Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))
in (_52_11340 && ((Support.List.length g.deferred.carry) <> 0)))) with
| true -> begin
(let _52_11347 = (let _52_11346 = (Support.Prims.pipe_right g.deferred.carry (Support.List.map (fun ( _33_4007 ) -> (match (_33_4007) with
| (msg, x) -> begin
(let _52_11345 = (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range (p_loc x))
in (let _52_11344 = (prob_to_string env x)
in (let _52_11343 = (let _52_11342 = (Support.Prims.pipe_right (p_guard x) Support.Prims.fst)
in (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env _52_11342))
in (Support.Microsoft.FStar.Util.format4 "(At %s) %s\n%s\nguard is %s\n" _52_11345 msg _52_11344 _52_11343))))
end))))
in (Support.Prims.pipe_right _52_11346 (Support.String.concat "\n")))
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.fprint1 "Trying to solve carried problems: begin\n%s\nend\n") _52_11347))
end
| false -> begin
()
end)
in (let gopt = (let _52_11348 = (wl_of_guard env g.deferred)
in (solve_and_commit env _52_11348 fail))
in (match (gopt) with
| Some ({carry = _; slack = slack}) -> begin
(let _33_4016 = (fix_slack_vars slack)
in (let _33_4018 = g
in {guard_f = _33_4018.guard_f; deferred = no_deferred; implicits = _33_4018.implicits}))
end
| _ -> begin
(failwith ("impossible"))
end)))))

let try_discharge_guard = (fun ( env ) ( g ) -> (let g = (solve_deferred_constraints env g)
in (match ((let _52_11353 = (Microsoft_FStar_Options.should_verify env.Microsoft_FStar_Tc_Env.curmodule.Microsoft_FStar_Absyn_Syntax.str)
in (not (_52_11353)))) with
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
(let _33_4032 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env) (Microsoft_FStar_Options.Other ("Rel")))) with
| true -> begin
(let _52_11356 = (Microsoft_FStar_Tc_Env.get_range env)
in (let _52_11355 = (let _52_11354 = (Microsoft_FStar_Absyn_Print.formula_to_string vc)
in (Support.Microsoft.FStar.Util.format1 "Checking VC=\n%s\n" _52_11354))
in (Microsoft_FStar_Tc_Errors.diag _52_11356 _52_11355)))
end
| false -> begin
()
end)
in (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.solve env vc))
end))
end)
end)))




