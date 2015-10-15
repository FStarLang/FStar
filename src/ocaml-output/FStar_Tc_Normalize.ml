
open Prims
type step =
| WHNF
| Eta
| EtaArgs
| Delta
| DeltaHard
| Beta
| DeltaComp
| Simplify
| SNComp
| Unmeta
| Unlabel
 and steps =
step Prims.list

let is_WHNF = (fun _discr_ -> (match (_discr_) with
| WHNF -> begin
true
end
| _ -> begin
false
end))

let is_Eta = (fun _discr_ -> (match (_discr_) with
| Eta -> begin
true
end
| _ -> begin
false
end))

let is_EtaArgs = (fun _discr_ -> (match (_discr_) with
| EtaArgs -> begin
true
end
| _ -> begin
false
end))

let is_Delta = (fun _discr_ -> (match (_discr_) with
| Delta -> begin
true
end
| _ -> begin
false
end))

let is_DeltaHard = (fun _discr_ -> (match (_discr_) with
| DeltaHard -> begin
true
end
| _ -> begin
false
end))

let is_Beta = (fun _discr_ -> (match (_discr_) with
| Beta -> begin
true
end
| _ -> begin
false
end))

let is_DeltaComp = (fun _discr_ -> (match (_discr_) with
| DeltaComp -> begin
true
end
| _ -> begin
false
end))

let is_Simplify = (fun _discr_ -> (match (_discr_) with
| Simplify -> begin
true
end
| _ -> begin
false
end))

let is_SNComp = (fun _discr_ -> (match (_discr_) with
| SNComp -> begin
true
end
| _ -> begin
false
end))

let is_Unmeta = (fun _discr_ -> (match (_discr_) with
| Unmeta -> begin
true
end
| _ -> begin
false
end))

let is_Unlabel = (fun _discr_ -> (match (_discr_) with
| Unlabel -> begin
true
end
| _ -> begin
false
end))

type 'a config =
{code : 'a; environment : environment; stack : stack; close : ('a  ->  'a) Prims.option; steps : step Prims.list}
 and environment =
{context : env_entry Prims.list; label_suffix : (Prims.bool Prims.option * FStar_Range.range) Prims.list}
 and stack =
{args : (FStar_Absyn_Syntax.arg * environment) Prims.list}
 and env_entry =
| T of (FStar_Absyn_Syntax.btvdef * tclos)
| V of (FStar_Absyn_Syntax.bvvdef * vclos)
 and tclos =
(FStar_Absyn_Syntax.typ * environment)
 and vclos =
(FStar_Absyn_Syntax.exp * environment)
 and 'a memo =
'a Prims.option FStar_ST.ref

let is_Mkconfig = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkconfig")))

let is_Mkenvironment = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenvironment")))

let is_Mkstack = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkstack")))

let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

let is_V = (fun _discr_ -> (match (_discr_) with
| V (_) -> begin
true
end
| _ -> begin
false
end))

let ___T____0 = (fun projectee -> (match (projectee) with
| T (_33_25) -> begin
_33_25
end))

let ___V____0 = (fun projectee -> (match (projectee) with
| V (_33_28) -> begin
_33_28
end))

let empty_env = {context = []; label_suffix = []}

let extend_env' = (fun env b -> (let _33_31 = env
in {context = (b)::env.context; label_suffix = _33_31.label_suffix}))

let extend_env = (fun env bindings -> (let _33_35 = env
in {context = (FStar_List.append bindings env.context); label_suffix = _33_35.label_suffix}))

let lookup_env = (fun env key -> (FStar_All.pipe_right env.context (FStar_Util.find_opt (fun _33_1 -> (match (_33_1) with
| T (a, _33_42) -> begin
(a.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText = key)
end
| V (x, _33_47) -> begin
(x.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText = key)
end)))))

let fold_env = (fun env f acc -> (FStar_List.fold_left (fun acc v -> (match (v) with
| T (a, _33_57) -> begin
(f a.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText v acc)
end
| V (x, _33_62) -> begin
(f x.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText v acc)
end)) acc env.context))

let empty_stack = {args = []}

let rec subst_of_env' = (fun env -> (fold_env env (fun _33_66 v acc -> (match (v) with
| T (a, (t, env')) -> begin
(let _98_112 = (let _98_111 = (let _98_110 = (let _98_109 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_typ _98_109 t))
in (a, _98_110))
in FStar_Util.Inl (_98_111))
in (_98_112)::acc)
end
| V (x, (v, env')) -> begin
(let _98_116 = (let _98_115 = (let _98_114 = (let _98_113 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_exp _98_113 v))
in (x, _98_114))
in FStar_Util.Inr (_98_115))
in (_98_116)::acc)
end)) []))

let subst_of_env = (fun tcenv env -> (subst_of_env' env))

let with_new_code = (fun c e -> {code = e; environment = c.environment; stack = empty_stack; close = None; steps = c.steps})

let rec eta_expand = (fun tcenv t -> (let k = (let _98_126 = (FStar_Tc_Recheck.recompute_kind t)
in (FStar_All.pipe_right _98_126 FStar_Absyn_Util.compress_kind))
in (let rec aux = (fun t k -> (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
t
end
| FStar_Absyn_Syntax.Kind_abbrev (_33_98, k) -> begin
(aux t k)
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k') -> begin
(match ((let _98_131 = (FStar_Absyn_Util.unascribe_typ t)
in _98_131.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam (real, body) -> begin
(let rec aux = (fun real expected -> (match ((real, expected)) with
| (_33_115::real, _33_119::expected) -> begin
(aux real expected)
end
| ([], []) -> begin
t
end
| (_33_128::_33_126, []) -> begin
(FStar_All.failwith "Ill-kinded type")
end
| ([], more) -> begin
(let _33_137 = (FStar_Absyn_Util.args_of_binders more)
in (match (_33_137) with
| (more, args) -> begin
(let body = (FStar_Absyn_Syntax.mk_Typ_app (body, args) None body.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_lam ((FStar_List.append binders more), body) None body.FStar_Absyn_Syntax.pos))
end))
end))
in (aux real binders))
end
| _33_140 -> begin
(let _33_143 = (FStar_Absyn_Util.args_of_binders binders)
in (match (_33_143) with
| (binders, args) -> begin
(let body = (FStar_Absyn_Syntax.mk_Typ_app (t, args) None t.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_lam (binders, body) None t.FStar_Absyn_Syntax.pos))
end))
end)
end
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_delayed (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _98_139 = (let _98_138 = (let _98_136 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _98_136 FStar_Range.string_of_range))
in (let _98_137 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "%s: Impossible: Kind_unknown: %s" _98_138 _98_137)))
in (FStar_All.failwith _98_139))
end))
in (aux t k))))

let is_var = (fun t -> (match ((FStar_Absyn_Util.compress_typ t)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (_33_162); FStar_Absyn_Syntax.tk = _33_160; FStar_Absyn_Syntax.pos = _33_158; FStar_Absyn_Syntax.fvs = _33_156; FStar_Absyn_Syntax.uvs = _33_154} -> begin
true
end
| _33_166 -> begin
false
end))

let rec eta_expand_exp = (fun tcenv e -> (let t = (let _98_146 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_All.pipe_right _98_146 FStar_Absyn_Util.compress_typ))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((let _98_147 = (FStar_Absyn_Util.compress_exp e)
in _98_147.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
(match (((FStar_List.length bs) = (FStar_List.length bs'))) with
| true -> begin
e
end
| false -> begin
(FStar_All.failwith "NYI")
end)
end
| _33_179 -> begin
(let _33_182 = (FStar_Absyn_Util.args_of_binders bs)
in (match (_33_182) with
| (bs, args) -> begin
(let _98_149 = (let _98_148 = (FStar_Absyn_Syntax.mk_Exp_app (e, args) None e.FStar_Absyn_Syntax.pos)
in (bs, _98_148))
in (FStar_Absyn_Syntax.mk_Exp_abs _98_149 (Some (t)) e.FStar_Absyn_Syntax.pos))
end))
end)
end
| _33_184 -> begin
e
end)))

let no_eta = (fun s -> (FStar_All.pipe_right s (FStar_List.filter (fun _33_2 -> (match (_33_2) with
| Eta -> begin
false
end
| _33_189 -> begin
true
end)))))

let no_eta_cfg = (fun c -> (let _33_191 = c
in (let _98_154 = (no_eta c.steps)
in {code = _33_191.code; environment = _33_191.environment; stack = _33_191.stack; close = _33_191.close; steps = _98_154})))

let whnf_only = (fun config -> (FStar_All.pipe_right config.steps (FStar_List.contains WHNF)))

let unmeta = (fun config -> (FStar_All.pipe_right config.steps (FStar_List.contains Unmeta)))

let unlabel = (fun config -> ((unmeta config) || (FStar_All.pipe_right config.steps (FStar_List.contains Unlabel))))

let is_stack_empty = (fun config -> (match (config.stack.args) with
| [] -> begin
true
end
| _33_199 -> begin
false
end))

let has_eta = (fun cfg -> (FStar_All.pipe_right cfg.steps (FStar_List.contains Eta)))

let rec weak_norm_comp = (fun env comp -> (let c = (FStar_Absyn_Util.comp_to_comp_typ comp)
in (match ((FStar_Tc_Env.lookup_effect_abbrev env c.FStar_Absyn_Syntax.effect_name)) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(let binders' = (FStar_List.map (fun _33_3 -> (match (_33_3) with
| (FStar_Util.Inl (b), imp) -> begin
(let _98_166 = (let _98_165 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inl (_98_165))
in (_98_166, imp))
end
| (FStar_Util.Inr (b), imp) -> begin
(let _98_168 = (let _98_167 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inr (_98_167))
in (_98_168, imp))
end)) binders)
in (let subst = (let _98_170 = (let _98_169 = (FStar_Absyn_Util.args_of_binders binders')
in (FStar_All.pipe_right _98_169 Prims.snd))
in (FStar_Absyn_Util.subst_of_list binders _98_170))
in (let cdef = (FStar_Absyn_Util.subst_comp subst cdef)
in (let subst = (let _98_172 = (let _98_171 = (FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ)
in (_98_171)::c.FStar_Absyn_Syntax.effect_args)
in (FStar_Absyn_Util.subst_of_list binders' _98_172))
in (let c1 = (FStar_Absyn_Util.subst_comp subst cdef)
in (let c = (FStar_All.pipe_right (let _33_223 = (FStar_Absyn_Util.comp_to_comp_typ c1)
in {FStar_Absyn_Syntax.effect_name = _33_223.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _33_223.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _33_223.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = c.FStar_Absyn_Syntax.flags}) FStar_Absyn_Syntax.mk_Comp)
in (weak_norm_comp env c)))))))
end)))

let t_config = (fun code env steps -> {code = code; environment = env; stack = empty_stack; close = None; steps = steps})

let k_config = (fun code env steps -> {code = code; environment = env; stack = empty_stack; close = None; steps = steps})

let e_config = (fun code env steps -> {code = code; environment = env; stack = empty_stack; close = None; steps = steps})

let c_config = (fun code env steps -> {code = code; environment = env; stack = empty_stack; close = None; steps = steps})

let close_with_config = (fun cfg f -> Some ((fun t -> (let t = (f t)
in (match (cfg.close) with
| None -> begin
t
end
| Some (g) -> begin
(g t)
end)))))

let rec is_head_symbol = (fun t -> (match ((let _98_203 = (FStar_Absyn_Util.compress_typ t)
in _98_203.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _33_254, _33_256)) -> begin
(is_head_symbol t)
end
| _33_261 -> begin
false
end))

let simplify_then_apply = (fun steps head args pos -> (let fallback = (fun _33_267 -> (match (()) with
| () -> begin
(FStar_Absyn_Syntax.mk_Typ_app (head, args) None pos)
end))
in (let simp_t = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
Some (true)
end
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid) -> begin
Some (false)
end
| _33_275 -> begin
None
end))
in (let simplify = (fun arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (t) -> begin
((simp_t t), arg)
end
| _33_281 -> begin
(None, arg)
end))
in (match ((FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps))) with
| true -> begin
(fallback ())
end
| false -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(match ((FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.and_lid)) with
| true -> begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _)::(_, (FStar_Util.Inl (arg), _))::[]) | ((_, (FStar_Util.Inl (arg), _))::(Some (true), _)::[]) -> begin
arg
end
| ((Some (false), _)::_::[]) | (_::(Some (false), _)::[]) -> begin
FStar_Absyn_Util.t_false
end
| _33_328 -> begin
(fallback ())
end)
end
| false -> begin
(match ((FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.or_lid)) with
| true -> begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _)::_::[]) | (_::(Some (true), _)::[]) -> begin
FStar_Absyn_Util.t_true
end
| ((Some (false), _)::(_, (FStar_Util.Inl (arg), _))::[]) | ((_, (FStar_Util.Inl (arg), _))::(Some (false), _)::[]) -> begin
arg
end
| _33_373 -> begin
(fallback ())
end)
end
| false -> begin
(match ((FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.imp_lid)) with
| true -> begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
FStar_Absyn_Util.t_true
end
| (Some (true), _33_401)::(_33_391, (FStar_Util.Inl (arg), _33_395))::[] -> begin
arg
end
| _33_405 -> begin
(fallback ())
end)
end
| false -> begin
(match ((FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.not_lid)) with
| true -> begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (Some (true), _33_409)::[] -> begin
FStar_Absyn_Util.t_false
end
| (Some (false), _33_415)::[] -> begin
FStar_Absyn_Util.t_true
end
| _33_419 -> begin
(fallback ())
end)
end
| false -> begin
(match (((((FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.forall_lid) || (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid)) || (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exists_lid)) || (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid))) with
| true -> begin
(match (args) with
| ((FStar_Util.Inl (t), _)::[]) | (_::(FStar_Util.Inl (t), _)::[]) -> begin
(match ((let _98_218 = (FStar_Absyn_Util.compress_typ t)
in _98_218.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam (_33_434::[], body) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
FStar_Absyn_Util.t_true
end
| Some (false) -> begin
FStar_Absyn_Util.t_false
end
| _33_444 -> begin
(fallback ())
end)
end
| _33_446 -> begin
(fallback ())
end)
end
| _33_448 -> begin
(fallback ())
end)
end
| false -> begin
(fallback ())
end)
end)
end)
end)
end)
end
| _33_450 -> begin
(fallback ())
end)
end)))))

let rec sn_delay = (fun tcenv cfg -> (let aux = (fun _33_454 -> (match (()) with
| () -> begin
(let _98_244 = (sn tcenv cfg)
in _98_244.code)
end))
in (let t = (FStar_Absyn_Syntax.mk_Typ_delayed' (FStar_Util.Inr (aux)) None cfg.code.FStar_Absyn_Syntax.pos)
in (let _33_456 = cfg
in {code = t; environment = _33_456.environment; stack = empty_stack; close = _33_456.close; steps = _33_456.steps}))))
and sn = (fun tcenv cfg -> (let rebuild = (fun config -> (let rebuild_stack = (fun config -> (match ((is_stack_empty config)) with
| true -> begin
config
end
| false -> begin
(let s' = (match ((FStar_List.contains EtaArgs config.steps)) with
| true -> begin
config.steps
end
| false -> begin
(no_eta config.steps)
end)
in (let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _33_4 -> (match (_33_4) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _98_256 = (let _98_255 = (let _98_254 = (sn tcenv (t_config t env s'))
in _98_254.code)
in (FStar_All.pipe_left (fun _98_253 -> FStar_Util.Inl (_98_253)) _98_255))
in (_98_256, imp))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _98_260 = (let _98_259 = (let _98_258 = (wne tcenv (e_config v env s'))
in _98_258.code)
in (FStar_All.pipe_left (fun _98_257 -> FStar_Util.Inr (_98_257)) _98_259))
in (_98_260, imp))
end))))
in (let t = (simplify_then_apply config.steps config.code args config.code.FStar_Absyn_Syntax.pos)
in (let _33_480 = config
in {code = t; environment = _33_480.environment; stack = empty_stack; close = _33_480.close; steps = _33_480.steps}))))
end))
in (let config = (rebuild_stack config)
in (let t = (match (config.close) with
| None -> begin
config.code
end
| Some (f) -> begin
(f config.code)
end)
in (match ((has_eta config)) with
| true -> begin
(let _33_487 = config
in (let _98_262 = (eta_expand tcenv t)
in {code = _98_262; environment = _33_487.environment; stack = _33_487.stack; close = _33_487.close; steps = _33_487.steps}))
end
| false -> begin
(let _33_489 = config
in {code = t; environment = _33_489.environment; stack = _33_489.stack; close = _33_489.close; steps = _33_489.steps})
end)))))
in (let wk = (fun f -> (match ((FStar_ST.read cfg.code.FStar_Absyn_Syntax.tk)) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _33_500; FStar_Absyn_Syntax.pos = _33_498; FStar_Absyn_Syntax.fvs = _33_496; FStar_Absyn_Syntax.uvs = _33_494}) -> begin
(f (Some (FStar_Absyn_Syntax.ktype)) cfg.code.FStar_Absyn_Syntax.pos)
end
| _33_505 -> begin
(f None cfg.code.FStar_Absyn_Syntax.pos)
end))
in (let config = (let _33_506 = cfg
in (let _98_275 = (FStar_Absyn_Util.compress_typ cfg.code)
in {code = _98_275; environment = _33_506.environment; stack = _33_506.stack; close = _33_506.close; steps = _33_506.steps}))
in (match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_33_510) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_uvar (_33_513) -> begin
(rebuild config)
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(match (((FStar_All.pipe_right config.steps (FStar_List.contains DeltaHard)) || ((FStar_All.pipe_right config.steps (FStar_List.contains Delta)) && (FStar_All.pipe_left Prims.op_Negation (is_stack_empty config))))) with
| true -> begin
(match ((FStar_Tc_Env.lookup_typ_abbrev tcenv fv.FStar_Absyn_Syntax.v)) with
| None -> begin
(rebuild config)
end
| Some (t) -> begin
(sn tcenv (let _33_520 = config
in {code = t; environment = _33_520.environment; stack = _33_520.stack; close = _33_520.close; steps = _33_520.steps}))
end)
end
| false -> begin
(rebuild config)
end)
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(match ((lookup_env config.environment a.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText)) with
| None -> begin
(rebuild config)
end
| Some (T (_33_526, (t, e))) -> begin
(sn tcenv (let _33_533 = config
in {code = t; environment = e; stack = _33_533.stack; close = _33_533.close; steps = _33_533.steps}))
end
| _33_536 -> begin
(FStar_All.failwith "Impossible: expected a type")
end)
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let args = (FStar_List.fold_right (fun a out -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _33_544 = config.stack
in {args = args})
in (sn tcenv (let _33_547 = config
in {code = head; environment = _33_547.environment; stack = stack; close = _33_547.close; steps = _33_547.steps}))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(match (config.stack.args) with
| [] -> begin
(let _33_556 = (sn_binders tcenv binders config.environment config.steps)
in (match (_33_556) with
| (binders, environment) -> begin
(let mk_lam = (fun t -> (let lam = (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_lam (binders, t)))
in (match (cfg.close) with
| None -> begin
lam
end
| Some (f) -> begin
(f lam)
end)))
in (let t2_cfg = (let _98_288 = (let _98_287 = (no_eta config.steps)
in {code = t2; environment = environment; stack = empty_stack; close = None; steps = _98_287})
in (sn_delay tcenv _98_288))
in (let _33_564 = t2_cfg
in (let _98_289 = (mk_lam t2_cfg.code)
in {code = _98_289; environment = _33_564.environment; stack = _33_564.stack; close = _33_564.close; steps = _33_564.steps}))))
end))
end
| args -> begin
(let rec beta = (fun env_entries binders args -> (match ((binders, args)) with
| ([], _33_573) -> begin
(let env = (extend_env config.environment env_entries)
in (sn tcenv (let _33_576 = config
in {code = t2; environment = env; stack = (let _33_578 = config.stack
in {args = args}); close = _33_576.close; steps = _33_576.steps})))
end
| (_33_581, []) -> begin
(let t = (FStar_Absyn_Syntax.mk_Typ_lam (binders, t2) None t2.FStar_Absyn_Syntax.pos)
in (let env = (extend_env config.environment env_entries)
in (sn tcenv (let _33_586 = config
in {code = t; environment = env; stack = empty_stack; close = _33_586.close; steps = _33_586.steps}))))
end
| (formal::rest, actual::rest') -> begin
(let m = (match ((formal, actual)) with
| ((FStar_Util.Inl (a), _33_598), ((FStar_Util.Inl (t), _33_603), env)) -> begin
T ((a.FStar_Absyn_Syntax.v, (t, env)))
end
| ((FStar_Util.Inr (x), _33_611), ((FStar_Util.Inr (v), _33_616), env)) -> begin
V ((x.FStar_Absyn_Syntax.v, (v, env)))
end
| _33_622 -> begin
(let _98_300 = (let _98_299 = (let _98_296 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _98_296))
in (let _98_298 = (FStar_Absyn_Print.binder_to_string formal)
in (let _98_297 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _98_299 _98_298 _98_297))))
in (FStar_All.failwith _98_300))
end)
in (beta ((m)::env_entries) rest rest'))
end))
in (beta [] binders args))
end)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _33_626) -> begin
(sn tcenv (let _33_629 = config
in {code = t; environment = _33_629.environment; stack = _33_629.stack; close = _33_629.close; steps = _33_629.steps}))
end
| _33_632 -> begin
(match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, comp) -> begin
(let _33_639 = (sn_binders tcenv bs config.environment config.steps)
in (match (_33_639) with
| (binders, environment) -> begin
(let c2 = (sncomp tcenv (c_config comp environment config.steps))
in (let _33_641 = config
in (let _98_303 = (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_fun (binders, c2.code)))
in {code = _98_303; environment = _33_641.environment; stack = _33_641.stack; close = _33_641.close; steps = _33_641.steps})))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((let _98_305 = (let _98_304 = (FStar_Absyn_Syntax.v_binder x)
in (_98_304)::[])
in (sn_binders tcenv _98_305 config.environment config.steps))) with
| ((FStar_Util.Inr (x), _33_650)::[], env) -> begin
(let refine = (fun t -> (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_refine (x, t))))
in (sn tcenv {code = t; environment = env; stack = empty_stack; close = (close_with_config config refine); steps = config.steps}))
end
| _33_658 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
(match ((unmeta config)) with
| true -> begin
(sn tcenv (let _33_664 = config
in {code = t; environment = _33_664.environment; stack = _33_664.stack; close = _33_664.close; steps = _33_664.steps}))
end
| false -> begin
(let pat = (fun t -> (let ps = (sn_args true tcenv config.environment config.steps ps)
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern ((t, ps)))))))
in (sn tcenv (let _33_669 = config
in {code = t; environment = _33_669.environment; stack = _33_669.stack; close = (close_with_config config pat); steps = _33_669.steps})))
end)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, b)) -> begin
(match ((unlabel config)) with
| true -> begin
(sn tcenv (let _33_678 = config
in {code = t; environment = _33_678.environment; stack = _33_678.stack; close = _33_678.close; steps = _33_678.steps}))
end
| false -> begin
(let lab = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when ((FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) && (FStar_All.pipe_right config.steps (FStar_List.contains Simplify))) -> begin
t
end
| _33_685 -> begin
(match (config.environment.label_suffix) with
| (b', sfx)::_33_687 -> begin
(match (((b' = None) || (Some (b) = b'))) with
| true -> begin
(let _33_692 = (match ((FStar_Tc_Env.debug tcenv FStar_Options.Low)) with
| true -> begin
(let _98_316 = (FStar_Range.string_of_range sfx)
in (FStar_Util.fprint2 "Stripping label %s because of enclosing refresh %s\n" l _98_316))
end
| false -> begin
()
end)
in t)
end
| false -> begin
(let _33_694 = (match ((FStar_Tc_Env.debug tcenv FStar_Options.Low)) with
| true -> begin
(let _98_317 = (FStar_Range.string_of_range sfx)
in (FStar_Util.fprint1 "Normalizer refreshing label: %s\n" _98_317))
end
| false -> begin
()
end)
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, sfx, b))))))
end)
end
| _33_697 -> begin
(FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b)))))
end)
end))
in (sn tcenv (let _33_698 = config
in {code = t; environment = _33_698.environment; stack = _33_698.stack; close = (close_with_config config lab); steps = _33_698.steps})))
end)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
(match ((unmeta config)) with
| true -> begin
(sn tcenv (let _33_706 = config
in {code = t; environment = _33_706.environment; stack = _33_706.stack; close = _33_706.close; steps = _33_706.steps}))
end
| false -> begin
(let sfx = (match (b) with
| Some (false) -> begin
r
end
| _33_711 -> begin
FStar_Absyn_Syntax.dummyRange
end)
in (let config = (let _33_713 = config
in {code = t; environment = (let _33_715 = config.environment
in {context = _33_715.context; label_suffix = ((b, sfx))::config.environment.label_suffix}); stack = _33_713.stack; close = _33_713.close; steps = _33_713.steps})
in (sn tcenv config)))
end)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
(match ((FStar_ST.read flag)) with
| true -> begin
(let _98_323 = (let _33_724 = config
in (let _98_322 = (FStar_Absyn_Util.mk_conj t1 t2)
in {code = _98_322; environment = _33_724.environment; stack = _33_724.stack; close = _33_724.close; steps = _33_724.steps}))
in (sn tcenv _98_323))
end
| false -> begin
(let c1 = (sn tcenv (t_config t1 config.environment config.steps))
in (let c2 = (sn tcenv (t_config t2 config.environment config.steps))
in (let _98_325 = (let _33_728 = config
in (let _98_324 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula ((c1.code, c2.code, flag))))
in {code = _98_324; environment = _33_728.environment; stack = _33_728.stack; close = _33_728.close; steps = _33_728.steps}))
in (rebuild _98_325))))
end)
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_))) | (FStar_Absyn_Syntax.Typ_unknown) | (_) -> begin
(let _98_330 = (let _98_329 = (let _98_326 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _98_326 FStar_Range.string_of_range))
in (let _98_328 = (FStar_Absyn_Print.tag_of_typ config.code)
in (let _98_327 = (FStar_Absyn_Print.typ_to_string config.code)
in (FStar_Util.format3 "(%s) Unexpected type (%s): %s" _98_329 _98_328 _98_327))))
in (FStar_All.failwith _98_330))
end)
end)))))
and sn_binders = (fun tcenv binders env steps -> (let rec aux = (fun out env _33_5 -> (match (_33_5) with
| (FStar_Util.Inl (a), imp)::rest -> begin
(let c = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort env steps))
in (let b = (let _98_341 = (FStar_Absyn_Util.freshen_bvd a.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _98_341 c.code))
in (let btyp = (FStar_Absyn_Util.btvar_to_typ b)
in (let b_for_a = T ((a.FStar_Absyn_Syntax.v, (btyp, empty_env)))
in (aux (((FStar_Util.Inl (b), imp))::out) (extend_env' env b_for_a) rest)))))
end
| (FStar_Util.Inr (x), imp)::rest -> begin
(let c = (sn_delay tcenv (t_config x.FStar_Absyn_Syntax.sort env steps))
in (let y = (let _98_342 = (FStar_Absyn_Util.freshen_bvd x.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _98_342 c.code))
in (let yexp = (FStar_Absyn_Util.bvar_to_exp y)
in (let y_for_x = V ((x.FStar_Absyn_Syntax.v, (yexp, empty_env)))
in (aux (((FStar_Util.Inr (y), imp))::out) (extend_env' env y_for_x) rest)))))
end
| [] -> begin
((FStar_List.rev out), env)
end))
in (aux [] env binders)))
and sncomp = (fun tcenv cfg -> (let m = cfg.code
in (match (m.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let ctconf = (sncomp_typ tcenv (with_new_code cfg ct))
in (let _33_772 = cfg
in (let _98_345 = (FStar_Absyn_Syntax.mk_Comp ctconf.code)
in {code = _98_345; environment = _33_772.environment; stack = _33_772.stack; close = _33_772.close; steps = _33_772.steps})))
end
| FStar_Absyn_Syntax.Total (t) -> begin
(match ((FStar_List.contains DeltaComp cfg.steps)) with
| true -> begin
(let _98_349 = (let _98_348 = (let _98_347 = (let _98_346 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_Absyn_Util.comp_to_comp_typ _98_346))
in (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp _98_347))
in (with_new_code cfg _98_348))
in (FStar_All.pipe_left (sncomp tcenv) _98_349))
end
| false -> begin
(let t = (sn tcenv (with_new_code cfg t))
in (let _98_350 = (FStar_Absyn_Syntax.mk_Total t.code)
in (with_new_code cfg _98_350)))
end)
end)))
and sncomp_typ = (fun tcenv cfg -> (let m = cfg.code
in (let norm = (fun _33_781 -> (match (()) with
| () -> begin
(let remake = (fun l r eargs flags -> (let c = {FStar_Absyn_Syntax.effect_name = l; FStar_Absyn_Syntax.result_typ = r; FStar_Absyn_Syntax.effect_args = eargs; FStar_Absyn_Syntax.flags = flags}
in (let _33_788 = cfg
in {code = c; environment = _33_788.environment; stack = _33_788.stack; close = _33_788.close; steps = _33_788.steps})))
in (let res = (let _98_363 = (sn tcenv (with_new_code cfg m.FStar_Absyn_Syntax.result_typ))
in _98_363.code)
in (let sn_flags = (fun flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _33_6 -> (match (_33_6) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let e = (let _98_367 = (wne tcenv (e_config e cfg.environment cfg.steps))
in _98_367.code)
in FStar_Absyn_Syntax.DECREASES (e))
end
| f -> begin
f
end)))))
in (let _33_800 = (let _98_369 = (sn_flags m.FStar_Absyn_Syntax.flags)
in (let _98_368 = (sn_args true tcenv cfg.environment cfg.steps m.FStar_Absyn_Syntax.effect_args)
in (_98_369, _98_368)))
in (match (_33_800) with
| (flags, args) -> begin
(remake m.FStar_Absyn_Syntax.effect_name res args flags)
end)))))
end))
in (match ((FStar_List.contains DeltaComp cfg.steps)) with
| true -> begin
(match ((FStar_Tc_Env.lookup_effect_abbrev tcenv m.FStar_Absyn_Syntax.effect_name)) with
| Some (_33_802) -> begin
(let c = (let _98_370 = (FStar_Absyn_Syntax.mk_Comp m)
in (weak_norm_comp tcenv _98_370))
in (sncomp_typ tcenv (let _33_805 = cfg
in {code = c; environment = _33_805.environment; stack = _33_805.stack; close = _33_805.close; steps = _33_805.steps})))
end
| _33_808 -> begin
(norm ())
end)
end
| false -> begin
(norm ())
end))))
and sn_args = (fun delay tcenv env steps args -> (FStar_All.pipe_right args (FStar_List.map (fun _33_7 -> (match (_33_7) with
| (FStar_Util.Inl (t), imp) when delay -> begin
(let _98_380 = (let _98_379 = (let _98_378 = (sn_delay tcenv (t_config t env steps))
in _98_378.code)
in (FStar_All.pipe_left (fun _98_377 -> FStar_Util.Inl (_98_377)) _98_379))
in (_98_380, imp))
end
| (FStar_Util.Inl (t), imp) -> begin
(let _98_384 = (let _98_383 = (let _98_382 = (sn tcenv (t_config t env steps))
in _98_382.code)
in (FStar_All.pipe_left (fun _98_381 -> FStar_Util.Inl (_98_381)) _98_383))
in (_98_384, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _98_388 = (let _98_387 = (let _98_386 = (wne tcenv (e_config e env steps))
in _98_386.code)
in (FStar_All.pipe_left (fun _98_385 -> FStar_Util.Inr (_98_385)) _98_387))
in (_98_388, imp))
end)))))
and snk = (fun tcenv cfg -> (let w = (fun f -> (f cfg.code.FStar_Absyn_Syntax.pos))
in (match ((let _98_398 = (FStar_Absyn_Util.compress_kind cfg.code)
in _98_398.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Kind_delayed (_)) | (FStar_Absyn_Syntax.Kind_lam (_)) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
cfg
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(let args = (let _98_399 = (no_eta cfg.steps)
in (sn_args false tcenv cfg.environment _98_399 args))
in (let _33_844 = cfg
in (let _98_401 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar (uv, args)))
in {code = _98_401; environment = _33_844.environment; stack = _33_844.stack; close = _33_844.close; steps = _33_844.steps})))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _33_856; FStar_Absyn_Syntax.pos = _33_854; FStar_Absyn_Syntax.fvs = _33_852; FStar_Absyn_Syntax.uvs = _33_850}) -> begin
(let _33_865 = (FStar_Tc_Env.lookup_kind_abbrev tcenv l)
in (match (_33_865) with
| (_33_862, binders, body) -> begin
(let subst = (FStar_Absyn_Util.subst_of_list binders args)
in (let _98_403 = (let _33_867 = cfg
in (let _98_402 = (FStar_Absyn_Util.subst_kind subst body)
in {code = _98_402; environment = _33_867.environment; stack = _33_867.stack; close = _33_867.close; steps = _33_867.steps}))
in (snk tcenv _98_403)))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_33_870, k) -> begin
(snk tcenv (let _33_874 = cfg
in {code = k; environment = _33_874.environment; stack = _33_874.stack; close = _33_874.close; steps = _33_874.steps}))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _33_882 = (sn_binders tcenv bs cfg.environment cfg.steps)
in (match (_33_882) with
| (bs, env) -> begin
(let c2 = (snk tcenv (k_config k env cfg.steps))
in (let _33_892 = (match (c2.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs', k) -> begin
((FStar_List.append bs bs'), k)
end
| _33_889 -> begin
(bs, c2.code)
end)
in (match (_33_892) with
| (bs, rhs) -> begin
(let _33_893 = cfg
in (let _98_405 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (bs, rhs)))
in {code = _98_405; environment = _33_893.environment; stack = _33_893.stack; close = _33_893.close; steps = _33_893.steps}))
end)))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(FStar_All.failwith "Impossible")
end)))
and wne = (fun tcenv cfg -> (let e = (FStar_Absyn_Util.compress_exp cfg.code)
in (let config = (let _33_899 = cfg
in {code = e; environment = _33_899.environment; stack = _33_899.stack; close = _33_899.close; steps = _33_899.steps})
in (let rebuild = (fun config -> (match ((is_stack_empty config)) with
| true -> begin
config
end
| false -> begin
(let s' = (match ((FStar_List.contains EtaArgs config.steps)) with
| true -> begin
config.steps
end
| false -> begin
(no_eta config.steps)
end)
in (let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _33_8 -> (match (_33_8) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _98_414 = (let _98_413 = (let _98_412 = (sn tcenv (t_config t env s'))
in _98_412.code)
in (FStar_All.pipe_left (fun _98_411 -> FStar_Util.Inl (_98_411)) _98_413))
in (_98_414, imp))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _98_418 = (let _98_417 = (let _98_416 = (wne tcenv (e_config v env s'))
in _98_416.code)
in (FStar_All.pipe_left (fun _98_415 -> FStar_Util.Inr (_98_415)) _98_417))
in (_98_418, imp))
end))))
in (let _33_919 = config
in (let _98_419 = (FStar_Absyn_Syntax.mk_Exp_app (config.code, args) None config.code.FStar_Absyn_Syntax.pos)
in {code = _98_419; environment = _33_919.environment; stack = empty_stack; close = _33_919.close; steps = _33_919.steps}))))
end))
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_33_922) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
(FStar_All.pipe_right config rebuild)
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(match ((lookup_env config.environment x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText)) with
| None -> begin
(FStar_All.pipe_right config rebuild)
end
| Some (V (_33_937, (vc, env))) -> begin
(wne tcenv (let _33_944 = config
in {code = vc; environment = env; stack = _33_944.stack; close = _33_944.close; steps = _33_944.steps}))
end
| _33_947 -> begin
(FStar_All.failwith "Impossible: ill-typed term")
end)
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let args = (FStar_List.fold_right (fun a out -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _33_955 = config.stack
in {args = args})
in (wne tcenv (let _33_958 = config
in {code = head; environment = _33_958.environment; stack = stack; close = _33_958.close; steps = _33_958.steps}))))
end
| FStar_Absyn_Syntax.Exp_abs (binders, body) -> begin
(let rec beta = (fun entries binders args -> (match ((binders, args)) with
| ([], _33_970) -> begin
(let env = (extend_env config.environment entries)
in (wne tcenv (let _33_973 = config
in {code = body; environment = env; stack = (let _33_975 = config.stack
in {args = args}); close = _33_973.close; steps = _33_973.steps})))
end
| (_33_978, []) -> begin
(let env = (extend_env config.environment entries)
in (let _33_984 = (sn_binders tcenv binders env config.steps)
in (match (_33_984) with
| (binders, env) -> begin
(let mk_abs = (fun t -> (FStar_Absyn_Syntax.mk_Exp_abs (binders, t) None body.FStar_Absyn_Syntax.pos))
in (let c = (let _98_431 = (let _33_987 = config
in (let _98_430 = (no_eta config.steps)
in {code = body; environment = env; stack = (let _33_989 = config.stack
in {args = []}); close = _33_987.close; steps = _98_430}))
in (wne tcenv _98_431))
in (let _33_992 = c
in (let _98_432 = (mk_abs c.code)
in {code = _98_432; environment = _33_992.environment; stack = _33_992.stack; close = _33_992.close; steps = _33_992.steps}))))
end)))
end
| (formal::rest, actual::rest') -> begin
(let m = (match ((formal, actual)) with
| ((FStar_Util.Inl (a), _33_1004), ((FStar_Util.Inl (t), _33_1009), env)) -> begin
T ((a.FStar_Absyn_Syntax.v, (t, env)))
end
| ((FStar_Util.Inr (x), _33_1017), ((FStar_Util.Inr (v), _33_1022), env)) -> begin
V ((x.FStar_Absyn_Syntax.v, (v, env)))
end
| _33_1028 -> begin
(let _98_437 = (let _98_436 = (let _98_433 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _98_433))
in (let _98_435 = (FStar_Absyn_Print.binder_to_string formal)
in (let _98_434 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _98_436 _98_435 _98_434))))
in (FStar_All.failwith _98_437))
end)
in (beta ((m)::entries) rest rest'))
end))
in (beta [] binders config.stack.args))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(let c_e1 = (wne tcenv (let _33_1034 = config
in {code = e1; environment = _33_1034.environment; stack = empty_stack; close = _33_1034.close; steps = _33_1034.steps}))
in (let wn_eqn = (fun _33_1041 -> (match (_33_1041) with
| (pat, w, body) -> begin
(let rec pat_vars = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_disj (p::_33_1047) -> begin
(pat_vars p)
end
| FStar_Absyn_Syntax.Pat_cons (_33_1052, _33_1054, pats) -> begin
(FStar_List.collect (fun _33_1061 -> (match (_33_1061) with
| (x, _33_1060) -> begin
(pat_vars x)
end)) pats)
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _98_443 = (FStar_Absyn_Syntax.v_binder x)
in (_98_443)::[])
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _98_444 = (FStar_Absyn_Syntax.t_binder a)
in (_98_444)::[])
end
| (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_constant (_)) | (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
[]
end))
in (let vars = (pat_vars pat)
in (let norm_bvvar = (fun x -> (let t = (sn tcenv (t_config x.FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _33_1085 = x
in {FStar_Absyn_Syntax.v = _33_1085.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t.code; FStar_Absyn_Syntax.p = _33_1085.FStar_Absyn_Syntax.p})))
in (let norm_btvar = (fun a -> (let k = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _33_1090 = a
in {FStar_Absyn_Syntax.v = _33_1090.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k.code; FStar_Absyn_Syntax.p = _33_1090.FStar_Absyn_Syntax.p})))
in (let rec norm_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (pats) -> begin
(let _98_452 = (let _98_451 = (FStar_List.map norm_pat pats)
in FStar_Absyn_Syntax.Pat_disj (_98_451))
in (FStar_Absyn_Util.withinfo _98_452 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _98_457 = (let _98_456 = (let _98_455 = (FStar_List.map (fun _33_1103 -> (match (_33_1103) with
| (x, i) -> begin
(let _98_454 = (norm_pat x)
in (_98_454, i))
end)) pats)
in (fv, q, _98_455))
in FStar_Absyn_Syntax.Pat_cons (_98_456))
in (FStar_Absyn_Util.withinfo _98_457 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _98_459 = (let _98_458 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_var (_98_458))
in (FStar_Absyn_Util.withinfo _98_459 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _98_461 = (let _98_460 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_tvar (_98_460))
in (FStar_Absyn_Util.withinfo _98_461 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let _98_463 = (let _98_462 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_wild (_98_462))
in (FStar_Absyn_Util.withinfo _98_463 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let _98_465 = (let _98_464 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_twild (_98_464))
in (FStar_Absyn_Util.withinfo _98_465 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_constant (_33_1113) -> begin
p
end
| FStar_Absyn_Syntax.Pat_dot_term (x, e) -> begin
(let e = (wne tcenv (e_config e config.environment config.steps))
in (let _98_468 = (let _98_467 = (let _98_466 = (norm_bvvar x)
in (_98_466, e.code))
in FStar_Absyn_Syntax.Pat_dot_term (_98_467))
in (FStar_Absyn_Util.withinfo _98_468 None p.FStar_Absyn_Syntax.p)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (let _98_471 = (let _98_470 = (let _98_469 = (norm_btvar a)
in (_98_469, t.code))
in FStar_Absyn_Syntax.Pat_dot_typ (_98_470))
in (FStar_Absyn_Util.withinfo _98_471 None p.FStar_Absyn_Syntax.p)))
end))
in (let env_entries = (FStar_List.fold_left (fun entries b -> (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let atyp = (FStar_Absyn_Util.btvar_to_typ a)
in (T ((a.FStar_Absyn_Syntax.v, (atyp, empty_env))))::entries)
end
| FStar_Util.Inr (x) -> begin
(let xexp = (FStar_Absyn_Util.bvar_to_exp x)
in (V ((x.FStar_Absyn_Syntax.v, (xexp, empty_env))))::entries)
end)) [] vars)
in (let env = (extend_env config.environment env_entries)
in (let w = (match (w) with
| None -> begin
None
end
| Some (w) -> begin
(let c_w = (wne tcenv (let _33_1138 = config
in {code = w; environment = env; stack = empty_stack; close = _33_1138.close; steps = _33_1138.steps}))
in Some (c_w.code))
end)
in (let c_body = (wne tcenv (let _33_1142 = config
in {code = body; environment = env; stack = empty_stack; close = _33_1142.close; steps = _33_1142.steps}))
in (let _98_474 = (norm_pat pat)
in (_98_474, w, c_body.code)))))))))))
end))
in (let eqns = (FStar_List.map wn_eqn eqns)
in (let e = (FStar_Absyn_Syntax.mk_Exp_match (c_e1.code, eqns) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (let _33_1147 = config
in {code = e; environment = _33_1147.environment; stack = _33_1147.stack; close = _33_1147.close; steps = _33_1147.steps}) rebuild)))))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), body) -> begin
(let _33_1179 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _33_1157 _33_1162 -> (match ((_33_1157, _33_1162)) with
| ((env, lbs), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = eff; FStar_Absyn_Syntax.lbdef = e}) -> begin
(let c = (wne tcenv (let _33_1163 = config
in {code = e; environment = _33_1163.environment; stack = empty_stack; close = _33_1163.close; steps = _33_1163.steps}))
in (let t = (sn tcenv (t_config t config.environment config.steps))
in (let _33_1176 = (match (x) with
| FStar_Util.Inl (x) -> begin
(let y = (let _98_477 = (match (is_rec) with
| true -> begin
x
end
| false -> begin
(FStar_Absyn_Util.freshen_bvd x)
end)
in (FStar_Absyn_Util.bvd_to_bvar_s _98_477 t.code))
in (let yexp = (FStar_Absyn_Util.bvar_to_exp y)
in (let y_for_x = V ((x, (yexp, empty_env)))
in (FStar_Util.Inl (y.FStar_Absyn_Syntax.v), (extend_env' env y_for_x)))))
end
| _33_1173 -> begin
(x, env)
end)
in (match (_33_1176) with
| (y, env) -> begin
(let _98_479 = (let _98_478 = (FStar_Absyn_Syntax.mk_lb (y, eff, t.code, c.code))
in (_98_478)::lbs)
in (env, _98_479))
end))))
end)) (config.environment, [])))
in (match (_33_1179) with
| (env, lbs) -> begin
(let lbs = (FStar_List.rev lbs)
in (let c_body = (wne tcenv (let _33_1181 = config
in {code = body; environment = env; stack = empty_stack; close = _33_1181.close; steps = _33_1181.steps}))
in (let e = (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), c_body.code) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (let _33_1185 = config
in {code = e; environment = _33_1185.environment; stack = _33_1185.stack; close = _33_1185.close; steps = _33_1185.steps}) rebuild))))
end))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, l) -> begin
(let c = (wne tcenv (let _33_1192 = config
in {code = e; environment = _33_1192.environment; stack = _33_1192.stack; close = _33_1192.close; steps = _33_1192.steps}))
in (match ((is_stack_empty config)) with
| true -> begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (let _98_481 = (let _33_1196 = config
in (let _98_480 = (FStar_Absyn_Syntax.mk_Exp_ascribed (c.code, t.code, l) None e.FStar_Absyn_Syntax.pos)
in {code = _98_480; environment = _33_1196.environment; stack = _33_1196.stack; close = _33_1196.close; steps = _33_1196.steps}))
in (rebuild _98_481)))
end
| false -> begin
c
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, info)) -> begin
(let c = (wne tcenv (let _33_1203 = config
in {code = e; environment = _33_1203.environment; stack = _33_1203.stack; close = _33_1203.close; steps = _33_1203.steps}))
in (match ((is_stack_empty config)) with
| true -> begin
(let _98_483 = (let _33_1206 = config
in (let _98_482 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((c.code, info))))
in {code = _98_482; environment = _33_1206.environment; stack = _33_1206.stack; close = _33_1206.close; steps = _33_1206.steps}))
in (rebuild _98_483))
end
| false -> begin
c
end))
end)))))

let norm_kind = (fun steps tcenv k -> (let c = (snk tcenv (k_config k empty_env steps))
in (FStar_Absyn_Util.compress_kind c.code)))

let norm_typ = (fun steps tcenv t -> (let c = (sn tcenv (t_config t empty_env steps))
in c.code))

let norm_exp = (fun steps tcenv e -> (let c = (wne tcenv (e_config e empty_env steps))
in c.code))

let norm_sigelt = (fun tcenv _33_9 -> (match (_33_9) with
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, b) -> begin
(let e = (let _98_507 = (let _98_506 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Absyn_Syntax.Const_unit None r)
in (lbs, _98_506))
in (FStar_Absyn_Syntax.mk_Exp_let _98_507 None r))
in (let e = (norm_exp ((Beta)::[]) tcenv e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_let (lbs, _33_1232) -> begin
FStar_Absyn_Syntax.Sig_let ((lbs, r, l, b))
end
| _33_1236 -> begin
(FStar_All.failwith "Impossible")
end)))
end
| s -> begin
s
end))

let whnf = (fun tcenv t -> (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_refine (_)) -> begin
t
end
| (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _98_512 = (eta_expand tcenv t)
in (FStar_All.pipe_right _98_512 FStar_Absyn_Util.compress_typ))
end
| (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) | (_) -> begin
(norm_typ ((WHNF)::(Beta)::(Eta)::[]) tcenv t)
end)))

let norm_comp = (fun steps tcenv c -> (let c = (sncomp tcenv (c_config c empty_env steps))
in c.code))

let normalize_kind = (fun tcenv k -> (let steps = (Eta)::(Delta)::(Beta)::[]
in (norm_kind steps tcenv k)))

let normalize_comp = (fun tcenv c -> (let steps = (Eta)::(Delta)::(Beta)::(SNComp)::(DeltaComp)::[]
in (norm_comp steps tcenv c)))

let normalize = (fun tcenv t -> (norm_typ ((DeltaHard)::(Beta)::(Eta)::[]) tcenv t))

let exp_norm_to_string = (fun tcenv e -> (let _98_535 = (norm_exp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv e)
in (FStar_Absyn_Print.exp_to_string _98_535)))

let typ_norm_to_string = (fun tcenv t -> (let _98_540 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv t)
in (FStar_Absyn_Print.typ_to_string _98_540)))

let kind_norm_to_string = (fun tcenv k -> (let _98_545 = (norm_kind ((Beta)::(SNComp)::(Unmeta)::[]) tcenv k)
in (FStar_Absyn_Print.kind_to_string _98_545)))

let formula_norm_to_string = (fun tcenv f -> (let _98_550 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv f)
in (FStar_Absyn_Print.formula_to_string _98_550)))

let comp_typ_norm_to_string = (fun tcenv c -> (let _98_555 = (norm_comp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv c)
in (FStar_Absyn_Print.comp_typ_to_string _98_555)))

let normalize_refinement = (fun env t0 -> (let t = (norm_typ ((Beta)::(WHNF)::(DeltaHard)::[]) env t0)
in (let rec aux = (fun t -> (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(let t0 = (aux x.FStar_Absyn_Syntax.sort)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (y, phi1) -> begin
(let _98_568 = (let _98_567 = (let _98_566 = (let _98_565 = (let _98_564 = (let _98_563 = (let _98_562 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _98_562))
in FStar_Util.Inr (_98_563))
in (_98_564)::[])
in (FStar_Absyn_Util.subst_typ _98_565 phi))
in (FStar_Absyn_Util.mk_conj phi1 _98_566))
in (y, _98_567))
in (FStar_Absyn_Syntax.mk_Typ_refine _98_568 (Some (FStar_Absyn_Syntax.ktype)) t0.FStar_Absyn_Syntax.pos))
end
| _33_1344 -> begin
t
end))
end
| _33_1346 -> begin
t
end)))
in (aux t))))
