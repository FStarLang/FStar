
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
{context : env_entry Prims.list; label_suffix : (Prims.bool Prims.option * Microsoft_FStar_Range.range) Prims.list} 
 and stack =
{args : (Microsoft_FStar_Absyn_Syntax.arg * environment) Prims.list} 
 and env_entry =
| T of (Microsoft_FStar_Absyn_Syntax.btvdef * tclos)
| V of (Microsoft_FStar_Absyn_Syntax.bvvdef * vclos) 
 and tclos =
(Microsoft_FStar_Absyn_Syntax.typ * environment) 
 and vclos =
(Microsoft_FStar_Absyn_Syntax.exp * environment) 
 and 'a memo =
'a Prims.option ST.ref

let is_Mkconfig = (fun _ -> (All.failwith "Not yet implemented:is_Mkconfig"))

let is_Mkenvironment = (fun _ -> (All.failwith "Not yet implemented:is_Mkenvironment"))

let is_Mkstack = (fun _ -> (All.failwith "Not yet implemented:is_Mkstack"))

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
| T (_32_25) -> begin
_32_25
end))

let ___V____0 = (fun projectee -> (match (projectee) with
| V (_32_28) -> begin
_32_28
end))

let empty_env = {context = []; label_suffix = []}

let extend_env' = (fun env b -> (let _32_31 = env
in {context = (b)::env.context; label_suffix = _32_31.label_suffix}))

let extend_env = (fun env bindings -> (let _32_35 = env
in {context = (Microsoft_FStar_List.append bindings env.context); label_suffix = _32_35.label_suffix}))

let lookup_env = (fun env key -> (All.pipe_right env.context (Microsoft_FStar_Util.find_opt (fun _32_1 -> (match (_32_1) with
| T (a, _32_42) -> begin
(a.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText = key)
end
| V (x, _32_47) -> begin
(x.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText = key)
end)))))

let fold_env = (fun env f acc -> (Microsoft_FStar_List.fold_left (fun acc v -> (match (v) with
| T (a, _32_57) -> begin
(f a.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText v acc)
end
| V (x, _32_62) -> begin
(f x.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText v acc)
end)) acc env.context))

let empty_stack = {args = []}

let rec subst_of_env' = (fun env -> (fold_env env (fun _32_66 v acc -> (match (v) with
| T (a, (t, env')) -> begin
(let _98_112 = (let _98_111 = (let _98_110 = (let _98_109 = (subst_of_env' env')
in (Microsoft_FStar_Absyn_Util.subst_typ _98_109 t))
in (a, _98_110))
in Microsoft_FStar_Util.Inl (_98_111))
in (_98_112)::acc)
end
| V (x, (v, env')) -> begin
(let _98_116 = (let _98_115 = (let _98_114 = (let _98_113 = (subst_of_env' env')
in (Microsoft_FStar_Absyn_Util.subst_exp _98_113 v))
in (x, _98_114))
in Microsoft_FStar_Util.Inr (_98_115))
in (_98_116)::acc)
end)) []))

let subst_of_env = (fun tcenv env -> (subst_of_env' env))

let with_new_code = (fun c e -> {code = e; environment = c.environment; stack = empty_stack; close = None; steps = c.steps})

let rec eta_expand = (fun tcenv t -> (let k = (let _98_126 = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (All.pipe_right _98_126 Microsoft_FStar_Absyn_Util.compress_kind))
in (let rec aux = (fun t k -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) | (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev (_32_98, k) -> begin
(aux t k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (binders, k') -> begin
(match ((let _98_131 = (Microsoft_FStar_Absyn_Util.unascribe_typ t)
in _98_131.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam (real, body) -> begin
(let rec aux = (fun real expected -> (match ((real, expected)) with
| (_32_115::real, _32_119::expected) -> begin
(aux real expected)
end
| ([], []) -> begin
t
end
| (_32_128::_32_126, []) -> begin
(All.failwith "Ill-kinded type")
end
| ([], more) -> begin
(let _32_137 = (Microsoft_FStar_Absyn_Util.args_of_binders more)
in (match (_32_137) with
| (more, args) -> begin
(let body = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (body, args) None body.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam ((Microsoft_FStar_List.append binders more), body) None body.Microsoft_FStar_Absyn_Syntax.pos))
end))
end))
in (aux real binders))
end
| _32_140 -> begin
(let _32_143 = (Microsoft_FStar_Absyn_Util.args_of_binders binders)
in (match (_32_143) with
| (binders, args) -> begin
(let body = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t, args) None t.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, body) None t.Microsoft_FStar_Absyn_Syntax.pos))
end))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Kind_lam (_)) | (Microsoft_FStar_Absyn_Syntax.Kind_delayed (_)) -> begin
(All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let _98_139 = (let _98_138 = (let _98_136 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (All.pipe_right _98_136 Microsoft_FStar_Range.string_of_range))
in (let _98_137 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Microsoft_FStar_Util.format2 "%s: Impossible: Kind_unknown: %s" _98_138 _98_137)))
in (All.failwith _98_139))
end))
in (aux t k))))

let is_var = (fun t -> (match ((Microsoft_FStar_Absyn_Util.compress_typ t)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (_32_162); Microsoft_FStar_Absyn_Syntax.tk = _32_160; Microsoft_FStar_Absyn_Syntax.pos = _32_158; Microsoft_FStar_Absyn_Syntax.fvs = _32_156; Microsoft_FStar_Absyn_Syntax.uvs = _32_154} -> begin
true
end
| _32_166 -> begin
false
end))

let rec eta_expand_exp = (fun tcenv e -> (let t = (let _98_146 = (Microsoft_FStar_Tc_Recheck.recompute_typ e)
in (All.pipe_right _98_146 Microsoft_FStar_Absyn_Util.compress_typ))
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((let _98_147 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _98_147.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
(match (((Microsoft_FStar_List.length bs) = (Microsoft_FStar_List.length bs'))) with
| true -> begin
e
end
| false -> begin
(All.failwith "NYI")
end)
end
| _32_179 -> begin
(let _32_182 = (Microsoft_FStar_Absyn_Util.args_of_binders bs)
in (match (_32_182) with
| (bs, args) -> begin
(let _98_149 = (let _98_148 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e, args) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (bs, _98_148))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _98_149 (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos))
end))
end)
end
| _32_184 -> begin
e
end)))

let no_eta = (fun s -> (All.pipe_right s (Microsoft_FStar_List.filter (fun _32_2 -> (match (_32_2) with
| Eta -> begin
false
end
| _32_189 -> begin
true
end)))))

let no_eta_cfg = (fun c -> (let _32_191 = c
in (let _98_154 = (no_eta c.steps)
in {code = _32_191.code; environment = _32_191.environment; stack = _32_191.stack; close = _32_191.close; steps = _98_154})))

let whnf_only = (fun config -> (All.pipe_right config.steps (Microsoft_FStar_List.contains WHNF)))

let unmeta = (fun config -> (All.pipe_right config.steps (Microsoft_FStar_List.contains Unmeta)))

let unlabel = (fun config -> ((unmeta config) || (All.pipe_right config.steps (Microsoft_FStar_List.contains Unlabel))))

let is_stack_empty = (fun config -> (match (config.stack.args) with
| [] -> begin
true
end
| _32_199 -> begin
false
end))

let has_eta = (fun cfg -> (All.pipe_right cfg.steps (Microsoft_FStar_List.contains Eta)))

let rec weak_norm_comp = (fun env comp -> (let c = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ comp)
in (match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev env c.Microsoft_FStar_Absyn_Syntax.effect_name)) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(let binders' = (Microsoft_FStar_List.map (fun _32_3 -> (match (_32_3) with
| (Microsoft_FStar_Util.Inl (b), imp) -> begin
(let _98_166 = (let _98_165 = (Microsoft_FStar_Absyn_Util.freshen_bvar b)
in Microsoft_FStar_Util.Inl (_98_165))
in (_98_166, imp))
end
| (Microsoft_FStar_Util.Inr (b), imp) -> begin
(let _98_168 = (let _98_167 = (Microsoft_FStar_Absyn_Util.freshen_bvar b)
in Microsoft_FStar_Util.Inr (_98_167))
in (_98_168, imp))
end)) binders)
in (let subst = (let _98_170 = (let _98_169 = (Microsoft_FStar_Absyn_Util.args_of_binders binders')
in (All.pipe_right _98_169 Prims.snd))
in (Microsoft_FStar_Absyn_Util.subst_of_list binders _98_170))
in (let cdef = (Microsoft_FStar_Absyn_Util.subst_comp subst cdef)
in (let subst = (let _98_172 = (let _98_171 = (Microsoft_FStar_Absyn_Syntax.targ c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (_98_171)::c.Microsoft_FStar_Absyn_Syntax.effect_args)
in (Microsoft_FStar_Absyn_Util.subst_of_list binders' _98_172))
in (let c1 = (Microsoft_FStar_Absyn_Util.subst_comp subst cdef)
in (let c = (All.pipe_right (let _32_223 = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c1)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _32_223.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _32_223.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _32_223.Microsoft_FStar_Absyn_Syntax.effect_args; Microsoft_FStar_Absyn_Syntax.flags = c.Microsoft_FStar_Absyn_Syntax.flags}) Microsoft_FStar_Absyn_Syntax.mk_Comp)
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

let rec is_head_symbol = (fun t -> (match ((let _98_203 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _98_203.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (t, _32_254, _32_256)) -> begin
(is_head_symbol t)
end
| _32_261 -> begin
false
end))

let simplify_then_apply = (fun steps head args pos -> (let fallback = (fun _32_267 -> (match (()) with
| () -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (head, args) None pos)
end))
in (let simp_t = (fun t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
Some (true)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.false_lid) -> begin
Some (false)
end
| _32_275 -> begin
None
end))
in (let simplify = (fun arg -> (match ((Prims.fst arg)) with
| Microsoft_FStar_Util.Inl (t) -> begin
((simp_t t), arg)
end
| _32_281 -> begin
(None, arg)
end))
in (match ((All.pipe_left Prims.op_Negation (Microsoft_FStar_List.contains Simplify steps))) with
| true -> begin
(fallback ())
end
| false -> begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.and_lid)) with
| true -> begin
(match ((All.pipe_right args (Microsoft_FStar_List.map simplify))) with
| ((Some (true), _)::(_, (Microsoft_FStar_Util.Inl (arg), _))::[]) | ((_, (Microsoft_FStar_Util.Inl (arg), _))::(Some (true), _)::[]) -> begin
arg
end
| ((Some (false), _)::_::[]) | (_::(Some (false), _)::[]) -> begin
Microsoft_FStar_Absyn_Util.t_false
end
| _32_328 -> begin
(fallback ())
end)
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.or_lid)) with
| true -> begin
(match ((All.pipe_right args (Microsoft_FStar_List.map simplify))) with
| ((Some (true), _)::_::[]) | (_::(Some (true), _)::[]) -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| ((Some (false), _)::(_, (Microsoft_FStar_Util.Inl (arg), _))::[]) | ((_, (Microsoft_FStar_Util.Inl (arg), _))::(Some (false), _)::[]) -> begin
arg
end
| _32_373 -> begin
(fallback ())
end)
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.imp_lid)) with
| true -> begin
(match ((All.pipe_right args (Microsoft_FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| (Some (true), _32_401)::(_32_391, (Microsoft_FStar_Util.Inl (arg), _32_395))::[] -> begin
arg
end
| _32_405 -> begin
(fallback ())
end)
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.not_lid)) with
| true -> begin
(match ((All.pipe_right args (Microsoft_FStar_List.map simplify))) with
| (Some (true), _32_409)::[] -> begin
Microsoft_FStar_Absyn_Util.t_false
end
| (Some (false), _32_415)::[] -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| _32_419 -> begin
(fallback ())
end)
end
| false -> begin
(match (((((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.forall_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.allTyp_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exists_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exTyp_lid))) with
| true -> begin
(match (args) with
| ((Microsoft_FStar_Util.Inl (t), _)::[]) | (_::(Microsoft_FStar_Util.Inl (t), _)::[]) -> begin
(match ((let _98_218 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _98_218.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam (_32_434::[], body) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| Some (false) -> begin
Microsoft_FStar_Absyn_Util.t_false
end
| _32_444 -> begin
(fallback ())
end)
end
| _32_446 -> begin
(fallback ())
end)
end
| _32_448 -> begin
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
| _32_450 -> begin
(fallback ())
end)
end)))))

let rec sn_delay = (fun tcenv cfg -> (let aux = (fun _32_454 -> (match (()) with
| () -> begin
(let _98_244 = (sn tcenv cfg)
in _98_244.code)
end))
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_delayed' (Microsoft_FStar_Util.Inr (aux)) None cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
in (let _32_456 = cfg
in {code = t; environment = _32_456.environment; stack = empty_stack; close = _32_456.close; steps = _32_456.steps}))))
and sn = (fun tcenv cfg -> (let rebuild = (fun config -> (let rebuild_stack = (fun config -> (match ((is_stack_empty config)) with
| true -> begin
config
end
| false -> begin
(let s' = (match ((Microsoft_FStar_List.contains EtaArgs config.steps)) with
| true -> begin
config.steps
end
| false -> begin
(no_eta config.steps)
end)
in (let args = (All.pipe_right config.stack.args (Microsoft_FStar_List.map (fun _32_4 -> (match (_32_4) with
| ((Microsoft_FStar_Util.Inl (t), imp), env) -> begin
(let _98_256 = (let _98_255 = (let _98_254 = (sn tcenv (t_config t env s'))
in _98_254.code)
in (All.pipe_left (fun _98_253 -> Microsoft_FStar_Util.Inl (_98_253)) _98_255))
in (_98_256, imp))
end
| ((Microsoft_FStar_Util.Inr (v), imp), env) -> begin
(let _98_260 = (let _98_259 = (let _98_258 = (wne tcenv (e_config v env s'))
in _98_258.code)
in (All.pipe_left (fun _98_257 -> Microsoft_FStar_Util.Inr (_98_257)) _98_259))
in (_98_260, imp))
end))))
in (let t = (simplify_then_apply config.steps config.code args config.code.Microsoft_FStar_Absyn_Syntax.pos)
in (let _32_480 = config
in {code = t; environment = _32_480.environment; stack = empty_stack; close = _32_480.close; steps = _32_480.steps}))))
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
(let _32_487 = config
in (let _98_262 = (eta_expand tcenv t)
in {code = _98_262; environment = _32_487.environment; stack = _32_487.stack; close = _32_487.close; steps = _32_487.steps}))
end
| false -> begin
(let _32_489 = config
in {code = t; environment = _32_489.environment; stack = _32_489.stack; close = _32_489.close; steps = _32_489.steps})
end)))))
in (let wk = (fun f -> (match ((ST.read cfg.code.Microsoft_FStar_Absyn_Syntax.tk)) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _32_500; Microsoft_FStar_Absyn_Syntax.pos = _32_498; Microsoft_FStar_Absyn_Syntax.fvs = _32_496; Microsoft_FStar_Absyn_Syntax.uvs = _32_494}) -> begin
(f (Some (Microsoft_FStar_Absyn_Syntax.ktype)) cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
end
| _32_505 -> begin
(f None cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (let config = (let _32_506 = cfg
in (let _98_275 = (Microsoft_FStar_Absyn_Util.compress_typ cfg.code)
in {code = _98_275; environment = _32_506.environment; stack = _32_506.stack; close = _32_506.close; steps = _32_506.steps}))
in (match (config.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_32_510) -> begin
(All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (_32_513) -> begin
(rebuild config)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(match (((All.pipe_right config.steps (Microsoft_FStar_List.contains DeltaHard)) || ((All.pipe_right config.steps (Microsoft_FStar_List.contains Delta)) && (All.pipe_left Prims.op_Negation (is_stack_empty config))))) with
| true -> begin
(match ((Microsoft_FStar_Tc_Env.lookup_typ_abbrev tcenv fv.Microsoft_FStar_Absyn_Syntax.v)) with
| None -> begin
(rebuild config)
end
| Some (t) -> begin
(sn tcenv (let _32_520 = config
in {code = t; environment = _32_520.environment; stack = _32_520.stack; close = _32_520.close; steps = _32_520.steps}))
end)
end
| false -> begin
(rebuild config)
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(match ((lookup_env config.environment a.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText)) with
| None -> begin
(rebuild config)
end
| Some (T (_32_526, (t, e))) -> begin
(sn tcenv (let _32_533 = config
in {code = t; environment = e; stack = _32_533.stack; close = _32_533.close; steps = _32_533.steps}))
end
| _32_536 -> begin
(All.failwith "Impossible: expected a type")
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let args = (Microsoft_FStar_List.fold_right (fun a out -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _32_544 = config.stack
in {args = args})
in (sn tcenv (let _32_547 = config
in {code = head; environment = _32_547.environment; stack = stack; close = _32_547.close; steps = _32_547.steps}))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(match (config.stack.args) with
| [] -> begin
(let _32_556 = (sn_binders tcenv binders config.environment config.steps)
in (match (_32_556) with
| (binders, environment) -> begin
(let mk_lam = (fun t -> (let lam = (All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, t)))
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
in (let _32_564 = t2_cfg
in (let _98_289 = (mk_lam t2_cfg.code)
in {code = _98_289; environment = _32_564.environment; stack = _32_564.stack; close = _32_564.close; steps = _32_564.steps}))))
end))
end
| args -> begin
(let rec beta = (fun env_entries binders args -> (match ((binders, args)) with
| ([], _32_573) -> begin
(let env = (extend_env config.environment env_entries)
in (sn tcenv (let _32_576 = config
in {code = t2; environment = env; stack = (let _32_578 = config.stack
in {args = args}); close = _32_576.close; steps = _32_576.steps})))
end
| (_32_581, []) -> begin
(let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, t2) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let env = (extend_env config.environment env_entries)
in (sn tcenv (let _32_586 = config
in {code = t; environment = env; stack = empty_stack; close = _32_586.close; steps = _32_586.steps}))))
end
| (formal::rest, actual::rest') -> begin
(let m = (match ((formal, actual)) with
| ((Microsoft_FStar_Util.Inl (a), _32_598), ((Microsoft_FStar_Util.Inl (t), _32_603), env)) -> begin
T ((a.Microsoft_FStar_Absyn_Syntax.v, (t, env)))
end
| ((Microsoft_FStar_Util.Inr (x), _32_611), ((Microsoft_FStar_Util.Inr (v), _32_616), env)) -> begin
V ((x.Microsoft_FStar_Absyn_Syntax.v, (v, env)))
end
| _32_622 -> begin
(let _98_300 = (let _98_299 = (let _98_296 = (All.pipe_left Microsoft_FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (Microsoft_FStar_Range.string_of_range _98_296))
in (let _98_298 = (Microsoft_FStar_Absyn_Print.binder_to_string formal)
in (let _98_297 = (All.pipe_left Microsoft_FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (Microsoft_FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _98_299 _98_298 _98_297))))
in (All.failwith _98_300))
end)
in (beta ((m)::env_entries) rest rest'))
end))
in (beta [] binders args))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed (t, _32_626) -> begin
(sn tcenv (let _32_629 = config
in {code = t; environment = _32_629.environment; stack = _32_629.stack; close = _32_629.close; steps = _32_629.steps}))
end
| _32_632 -> begin
(match (config.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (bs, comp) -> begin
(let _32_639 = (sn_binders tcenv bs config.environment config.steps)
in (match (_32_639) with
| (binders, environment) -> begin
(let c2 = (sncomp tcenv (c_config comp environment config.steps))
in (let _32_641 = config
in (let _98_303 = (All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (binders, c2.code)))
in {code = _98_303; environment = _32_641.environment; stack = _32_641.stack; close = _32_641.close; steps = _32_641.steps})))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((let _98_305 = (let _98_304 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_98_304)::[])
in (sn_binders tcenv _98_305 config.environment config.steps))) with
| ((Microsoft_FStar_Util.Inr (x), _32_650)::[], env) -> begin
(let refine = (fun t -> (All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, t))))
in (sn tcenv {code = t; environment = env; stack = empty_stack; close = (close_with_config config refine); steps = config.steps}))
end
| _32_658 -> begin
(All.failwith "Impossible")
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
(match ((unmeta config)) with
| true -> begin
(sn tcenv (let _32_664 = config
in {code = t; environment = _32_664.environment; stack = _32_664.stack; close = _32_664.close; steps = _32_664.steps}))
end
| false -> begin
(let pat = (fun t -> (let ps = (sn_args true tcenv config.environment config.steps ps)
in (All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps)))))))
in (sn tcenv (let _32_669 = config
in {code = t; environment = _32_669.environment; stack = _32_669.stack; close = (close_with_config config pat); steps = _32_669.steps})))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled (t, l, r, b)) -> begin
(match ((unlabel config)) with
| true -> begin
(sn tcenv (let _32_678 = config
in {code = t; environment = _32_678.environment; stack = _32_678.stack; close = _32_678.close; steps = _32_678.steps}))
end
| false -> begin
(let lab = (fun t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) && (All.pipe_right config.steps (Microsoft_FStar_List.contains Simplify))) -> begin
t
end
| _32_685 -> begin
(match (config.environment.label_suffix) with
| (b', sfx)::_32_687 -> begin
(match (((b' = None) || (Some (b) = b'))) with
| true -> begin
(let _32_692 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _98_316 = (Microsoft_FStar_Range.string_of_range sfx)
in (Microsoft_FStar_Util.fprint2 "Stripping label %s because of enclosing refresh %s\n" l _98_316))
end
| false -> begin
()
end)
in t)
end
| false -> begin
(let _32_694 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _98_317 = (Microsoft_FStar_Range.string_of_range sfx)
in (Microsoft_FStar_Util.fprint1 "Normalizer refreshing label: %s\n" _98_317))
end
| false -> begin
()
end)
in (All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, sfx, b))))))
end)
end
| _32_697 -> begin
(All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b)))))
end)
end))
in (sn tcenv (let _32_698 = config
in {code = t; environment = _32_698.environment; stack = _32_698.stack; close = (close_with_config config lab); steps = _32_698.steps})))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
(match ((unmeta config)) with
| true -> begin
(sn tcenv (let _32_706 = config
in {code = t; environment = _32_706.environment; stack = _32_706.stack; close = _32_706.close; steps = _32_706.steps}))
end
| false -> begin
(let sfx = (match (b) with
| Some (false) -> begin
r
end
| _32_711 -> begin
Microsoft_FStar_Absyn_Syntax.dummyRange
end)
in (let config = (let _32_713 = config
in {code = t; environment = (let _32_715 = config.environment
in {context = _32_715.context; label_suffix = ((b, sfx))::config.environment.label_suffix}); stack = _32_713.stack; close = _32_713.close; steps = _32_713.steps})
in (sn tcenv config)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
(match ((ST.read flag)) with
| true -> begin
(let _98_323 = (let _32_724 = config
in (let _98_322 = (Microsoft_FStar_Absyn_Util.mk_conj t1 t2)
in {code = _98_322; environment = _32_724.environment; stack = _32_724.stack; close = _32_724.close; steps = _32_724.steps}))
in (sn tcenv _98_323))
end
| false -> begin
(let c1 = (sn tcenv (t_config t1 config.environment config.steps))
in (let c2 = (sn tcenv (t_config t2 config.environment config.steps))
in (let _98_325 = (let _32_728 = config
in (let _98_324 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((c1.code, c2.code, flag))))
in {code = _98_324; environment = _32_728.environment; stack = _32_728.stack; close = _32_728.close; steps = _32_728.steps}))
in (rebuild _98_325))))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named (_))) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (_) -> begin
(let _98_330 = (let _98_329 = (let _98_326 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (All.pipe_right _98_326 Microsoft_FStar_Range.string_of_range))
in (let _98_328 = (Microsoft_FStar_Absyn_Print.tag_of_typ config.code)
in (let _98_327 = (Microsoft_FStar_Absyn_Print.typ_to_string config.code)
in (Microsoft_FStar_Util.format3 "(%s) Unexpected type (%s): %s" _98_329 _98_328 _98_327))))
in (All.failwith _98_330))
end)
end)))))
and sn_binders = (fun tcenv binders env steps -> (let rec aux = (fun out env _32_5 -> (match (_32_5) with
| (Microsoft_FStar_Util.Inl (a), imp)::rest -> begin
(let c = (snk tcenv (k_config a.Microsoft_FStar_Absyn_Syntax.sort env steps))
in (let b = (let _98_341 = (Microsoft_FStar_Absyn_Util.freshen_bvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _98_341 c.code))
in (let btyp = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (let b_for_a = T ((a.Microsoft_FStar_Absyn_Syntax.v, (btyp, empty_env)))
in (aux (((Microsoft_FStar_Util.Inl (b), imp))::out) (extend_env' env b_for_a) rest)))))
end
| (Microsoft_FStar_Util.Inr (x), imp)::rest -> begin
(let c = (sn_delay tcenv (t_config x.Microsoft_FStar_Absyn_Syntax.sort env steps))
in (let y = (let _98_342 = (Microsoft_FStar_Absyn_Util.freshen_bvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _98_342 c.code))
in (let yexp = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (let y_for_x = V ((x.Microsoft_FStar_Absyn_Syntax.v, (yexp, empty_env)))
in (aux (((Microsoft_FStar_Util.Inr (y), imp))::out) (extend_env' env y_for_x) rest)))))
end
| [] -> begin
((Microsoft_FStar_List.rev out), env)
end))
in (aux [] env binders)))
and sncomp = (fun tcenv cfg -> (let m = cfg.code
in (match (m.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let ctconf = (sncomp_typ tcenv (with_new_code cfg ct))
in (let _32_772 = cfg
in (let _98_345 = (Microsoft_FStar_Absyn_Syntax.mk_Comp ctconf.code)
in {code = _98_345; environment = _32_772.environment; stack = _32_772.stack; close = _32_772.close; steps = _32_772.steps})))
end
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(match ((Microsoft_FStar_List.contains DeltaComp cfg.steps)) with
| true -> begin
(let _98_349 = (let _98_348 = (let _98_347 = (let _98_346 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (Microsoft_FStar_Absyn_Util.comp_to_comp_typ _98_346))
in (All.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp _98_347))
in (with_new_code cfg _98_348))
in (All.pipe_left (sncomp tcenv) _98_349))
end
| false -> begin
(let t = (sn tcenv (with_new_code cfg t))
in (let _98_350 = (Microsoft_FStar_Absyn_Syntax.mk_Total t.code)
in (with_new_code cfg _98_350)))
end)
end)))
and sncomp_typ = (fun tcenv cfg -> (let m = cfg.code
in (let norm = (fun _32_781 -> (match (()) with
| () -> begin
(let remake = (fun l r eargs flags -> (let c = {Microsoft_FStar_Absyn_Syntax.effect_name = l; Microsoft_FStar_Absyn_Syntax.result_typ = r; Microsoft_FStar_Absyn_Syntax.effect_args = eargs; Microsoft_FStar_Absyn_Syntax.flags = flags}
in (let _32_788 = cfg
in {code = c; environment = _32_788.environment; stack = _32_788.stack; close = _32_788.close; steps = _32_788.steps})))
in (let res = (let _98_363 = (sn tcenv (with_new_code cfg m.Microsoft_FStar_Absyn_Syntax.result_typ))
in _98_363.code)
in (let sn_flags = (fun flags -> (All.pipe_right flags (Microsoft_FStar_List.map (fun _32_6 -> (match (_32_6) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let e = (let _98_367 = (wne tcenv (e_config e cfg.environment cfg.steps))
in _98_367.code)
in Microsoft_FStar_Absyn_Syntax.DECREASES (e))
end
| f -> begin
f
end)))))
in (let _32_800 = (let _98_369 = (sn_flags m.Microsoft_FStar_Absyn_Syntax.flags)
in (let _98_368 = (sn_args true tcenv cfg.environment cfg.steps m.Microsoft_FStar_Absyn_Syntax.effect_args)
in (_98_369, _98_368)))
in (match (_32_800) with
| (flags, args) -> begin
(remake m.Microsoft_FStar_Absyn_Syntax.effect_name res args flags)
end)))))
end))
in (match ((Microsoft_FStar_List.contains DeltaComp cfg.steps)) with
| true -> begin
(match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev tcenv m.Microsoft_FStar_Absyn_Syntax.effect_name)) with
| Some (_32_802) -> begin
(let c = (let _98_370 = (Microsoft_FStar_Absyn_Syntax.mk_Comp m)
in (weak_norm_comp tcenv _98_370))
in (sncomp_typ tcenv (let _32_805 = cfg
in {code = c; environment = _32_805.environment; stack = _32_805.stack; close = _32_805.close; steps = _32_805.steps})))
end
| _32_808 -> begin
(norm ())
end)
end
| false -> begin
(norm ())
end))))
and sn_args = (fun delay tcenv env steps args -> (All.pipe_right args (Microsoft_FStar_List.map (fun _32_7 -> (match (_32_7) with
| (Microsoft_FStar_Util.Inl (t), imp) when delay -> begin
(let _98_380 = (let _98_379 = (let _98_378 = (sn_delay tcenv (t_config t env steps))
in _98_378.code)
in (All.pipe_left (fun _98_377 -> Microsoft_FStar_Util.Inl (_98_377)) _98_379))
in (_98_380, imp))
end
| (Microsoft_FStar_Util.Inl (t), imp) -> begin
(let _98_384 = (let _98_383 = (let _98_382 = (sn tcenv (t_config t env steps))
in _98_382.code)
in (All.pipe_left (fun _98_381 -> Microsoft_FStar_Util.Inl (_98_381)) _98_383))
in (_98_384, imp))
end
| (Microsoft_FStar_Util.Inr (e), imp) -> begin
(let _98_388 = (let _98_387 = (let _98_386 = (wne tcenv (e_config e env steps))
in _98_386.code)
in (All.pipe_left (fun _98_385 -> Microsoft_FStar_Util.Inr (_98_385)) _98_387))
in (_98_388, imp))
end)))))
and snk = (fun tcenv cfg -> (let w = (fun f -> (f cfg.code.Microsoft_FStar_Absyn_Syntax.pos))
in (match ((let _98_398 = (Microsoft_FStar_Absyn_Util.compress_kind cfg.code)
in _98_398.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Kind_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Kind_lam (_)) -> begin
(All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) -> begin
cfg
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(let args = (let _98_399 = (no_eta cfg.steps)
in (sn_args false tcenv cfg.environment _98_399 args))
in (let _32_844 = cfg
in (let _98_401 = (All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (uv, args)))
in {code = _98_401; environment = _32_844.environment; stack = _32_844.stack; close = _32_844.close; steps = _32_844.steps})))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((l, args), {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_unknown; Microsoft_FStar_Absyn_Syntax.tk = _32_856; Microsoft_FStar_Absyn_Syntax.pos = _32_854; Microsoft_FStar_Absyn_Syntax.fvs = _32_852; Microsoft_FStar_Absyn_Syntax.uvs = _32_850}) -> begin
(let _32_865 = (Microsoft_FStar_Tc_Env.lookup_kind_abbrev tcenv l)
in (match (_32_865) with
| (_32_862, binders, body) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.subst_of_list binders args)
in (let _98_403 = (let _32_867 = cfg
in (let _98_402 = (Microsoft_FStar_Absyn_Util.subst_kind subst body)
in {code = _98_402; environment = _32_867.environment; stack = _32_867.stack; close = _32_867.close; steps = _32_867.steps}))
in (snk tcenv _98_403)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev (_32_870, k) -> begin
(snk tcenv (let _32_874 = cfg
in {code = k; environment = _32_874.environment; stack = _32_874.stack; close = _32_874.close; steps = _32_874.steps}))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _32_882 = (sn_binders tcenv bs cfg.environment cfg.steps)
in (match (_32_882) with
| (bs, env) -> begin
(let c2 = (snk tcenv (k_config k env cfg.steps))
in (let _32_892 = (match (c2.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (bs', k) -> begin
((Microsoft_FStar_List.append bs bs'), k)
end
| _32_889 -> begin
(bs, c2.code)
end)
in (match (_32_892) with
| (bs, rhs) -> begin
(let _32_893 = cfg
in (let _98_405 = (All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, rhs)))
in {code = _98_405; environment = _32_893.environment; stack = _32_893.stack; close = _32_893.close; steps = _32_893.steps}))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(All.failwith "Impossible")
end)))
and wne = (fun tcenv cfg -> (let e = (Microsoft_FStar_Absyn_Util.compress_exp cfg.code)
in (let config = (let _32_899 = cfg
in {code = e; environment = _32_899.environment; stack = _32_899.stack; close = _32_899.close; steps = _32_899.steps})
in (let rebuild = (fun config -> (match ((is_stack_empty config)) with
| true -> begin
config
end
| false -> begin
(let s' = (match ((Microsoft_FStar_List.contains EtaArgs config.steps)) with
| true -> begin
config.steps
end
| false -> begin
(no_eta config.steps)
end)
in (let args = (All.pipe_right config.stack.args (Microsoft_FStar_List.map (fun _32_8 -> (match (_32_8) with
| ((Microsoft_FStar_Util.Inl (t), imp), env) -> begin
(let _98_414 = (let _98_413 = (let _98_412 = (sn tcenv (t_config t env s'))
in _98_412.code)
in (All.pipe_left (fun _98_411 -> Microsoft_FStar_Util.Inl (_98_411)) _98_413))
in (_98_414, imp))
end
| ((Microsoft_FStar_Util.Inr (v), imp), env) -> begin
(let _98_418 = (let _98_417 = (let _98_416 = (wne tcenv (e_config v env s'))
in _98_416.code)
in (All.pipe_left (fun _98_415 -> Microsoft_FStar_Util.Inr (_98_415)) _98_417))
in (_98_418, imp))
end))))
in (let _32_919 = config
in (let _98_419 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (config.code, args) None config.code.Microsoft_FStar_Absyn_Syntax.pos)
in {code = _98_419; environment = _32_919.environment; stack = empty_stack; close = _32_919.close; steps = _32_919.steps}))))
end))
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_32_922) -> begin
(All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
(All.pipe_right config rebuild)
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(match ((lookup_env config.environment x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText)) with
| None -> begin
(All.pipe_right config rebuild)
end
| Some (V (_32_937, (vc, env))) -> begin
(wne tcenv (let _32_944 = config
in {code = vc; environment = env; stack = _32_944.stack; close = _32_944.close; steps = _32_944.steps}))
end
| _32_947 -> begin
(All.failwith "Impossible: ill-typed term")
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let args = (Microsoft_FStar_List.fold_right (fun a out -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _32_955 = config.stack
in {args = args})
in (wne tcenv (let _32_958 = config
in {code = head; environment = _32_958.environment; stack = stack; close = _32_958.close; steps = _32_958.steps}))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (binders, body) -> begin
(let rec beta = (fun entries binders args -> (match ((binders, args)) with
| ([], _32_970) -> begin
(let env = (extend_env config.environment entries)
in (wne tcenv (let _32_973 = config
in {code = body; environment = env; stack = (let _32_975 = config.stack
in {args = args}); close = _32_973.close; steps = _32_973.steps})))
end
| (_32_978, []) -> begin
(let env = (extend_env config.environment entries)
in (let _32_984 = (sn_binders tcenv binders env config.steps)
in (match (_32_984) with
| (binders, env) -> begin
(let mk_abs = (fun t -> (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (binders, t) None body.Microsoft_FStar_Absyn_Syntax.pos))
in (let c = (let _98_431 = (let _32_987 = config
in (let _98_430 = (no_eta config.steps)
in {code = body; environment = env; stack = (let _32_989 = config.stack
in {args = []}); close = _32_987.close; steps = _98_430}))
in (wne tcenv _98_431))
in (let _32_992 = c
in (let _98_432 = (mk_abs c.code)
in {code = _98_432; environment = _32_992.environment; stack = _32_992.stack; close = _32_992.close; steps = _32_992.steps}))))
end)))
end
| (formal::rest, actual::rest') -> begin
(let m = (match ((formal, actual)) with
| ((Microsoft_FStar_Util.Inl (a), _32_1004), ((Microsoft_FStar_Util.Inl (t), _32_1009), env)) -> begin
T ((a.Microsoft_FStar_Absyn_Syntax.v, (t, env)))
end
| ((Microsoft_FStar_Util.Inr (x), _32_1017), ((Microsoft_FStar_Util.Inr (v), _32_1022), env)) -> begin
V ((x.Microsoft_FStar_Absyn_Syntax.v, (v, env)))
end
| _32_1028 -> begin
(let _98_437 = (let _98_436 = (let _98_433 = (All.pipe_left Microsoft_FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (Microsoft_FStar_Range.string_of_range _98_433))
in (let _98_435 = (Microsoft_FStar_Absyn_Print.binder_to_string formal)
in (let _98_434 = (All.pipe_left Microsoft_FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (Microsoft_FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _98_436 _98_435 _98_434))))
in (All.failwith _98_437))
end)
in (beta ((m)::entries) rest rest'))
end))
in (beta [] binders config.stack.args))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(let c_e1 = (wne tcenv (let _32_1034 = config
in {code = e1; environment = _32_1034.environment; stack = empty_stack; close = _32_1034.close; steps = _32_1034.steps}))
in (let wn_eqn = (fun _32_1041 -> (match (_32_1041) with
| (pat, w, body) -> begin
(let rec pat_vars = (fun p -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (p::_32_1047) -> begin
(pat_vars p)
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons (_32_1052, _32_1054, pats) -> begin
(Microsoft_FStar_List.collect (fun _32_1061 -> (match (_32_1061) with
| (x, _32_1060) -> begin
(pat_vars x)
end)) pats)
end
| Microsoft_FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _98_443 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_98_443)::[])
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _98_444 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (_98_444)::[])
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
[]
end))
in (let vars = (pat_vars pat)
in (let norm_bvvar = (fun x -> (let t = (sn tcenv (t_config x.Microsoft_FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _32_1085 = x
in {Microsoft_FStar_Absyn_Syntax.v = _32_1085.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t.code; Microsoft_FStar_Absyn_Syntax.p = _32_1085.Microsoft_FStar_Absyn_Syntax.p})))
in (let norm_btvar = (fun a -> (let k = (snk tcenv (k_config a.Microsoft_FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _32_1090 = a
in {Microsoft_FStar_Absyn_Syntax.v = _32_1090.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k.code; Microsoft_FStar_Absyn_Syntax.p = _32_1090.Microsoft_FStar_Absyn_Syntax.p})))
in (let rec norm_pat = (fun p -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (pats) -> begin
(let _98_452 = (let _98_451 = (Microsoft_FStar_List.map norm_pat pats)
in Microsoft_FStar_Absyn_Syntax.Pat_disj (_98_451))
in (Microsoft_FStar_Absyn_Util.withinfo _98_452 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _98_457 = (let _98_456 = (let _98_455 = (Microsoft_FStar_List.map (fun _32_1103 -> (match (_32_1103) with
| (x, i) -> begin
(let _98_454 = (norm_pat x)
in (_98_454, i))
end)) pats)
in (fv, q, _98_455))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_98_456))
in (Microsoft_FStar_Absyn_Util.withinfo _98_457 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _98_459 = (let _98_458 = (norm_bvvar x)
in Microsoft_FStar_Absyn_Syntax.Pat_var (_98_458))
in (Microsoft_FStar_Absyn_Util.withinfo _98_459 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _98_461 = (let _98_460 = (norm_btvar a)
in Microsoft_FStar_Absyn_Syntax.Pat_tvar (_98_460))
in (Microsoft_FStar_Absyn_Util.withinfo _98_461 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let _98_463 = (let _98_462 = (norm_bvvar x)
in Microsoft_FStar_Absyn_Syntax.Pat_wild (_98_462))
in (Microsoft_FStar_Absyn_Util.withinfo _98_463 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let _98_465 = (let _98_464 = (norm_btvar a)
in Microsoft_FStar_Absyn_Syntax.Pat_twild (_98_464))
in (Microsoft_FStar_Absyn_Util.withinfo _98_465 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (_32_1113) -> begin
p
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term (x, e) -> begin
(let e = (wne tcenv (e_config e config.environment config.steps))
in (let _98_468 = (let _98_467 = (let _98_466 = (norm_bvvar x)
in (_98_466, e.code))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_98_467))
in (Microsoft_FStar_Absyn_Util.withinfo _98_468 None p.Microsoft_FStar_Absyn_Syntax.p)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (let _98_471 = (let _98_470 = (let _98_469 = (norm_btvar a)
in (_98_469, t.code))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_98_470))
in (Microsoft_FStar_Absyn_Util.withinfo _98_471 None p.Microsoft_FStar_Absyn_Syntax.p)))
end))
in (let env_entries = (Microsoft_FStar_List.fold_left (fun entries b -> (match ((Prims.fst b)) with
| Microsoft_FStar_Util.Inl (a) -> begin
(let atyp = (Microsoft_FStar_Absyn_Util.btvar_to_typ a)
in (T ((a.Microsoft_FStar_Absyn_Syntax.v, (atyp, empty_env))))::entries)
end
| Microsoft_FStar_Util.Inr (x) -> begin
(let xexp = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (V ((x.Microsoft_FStar_Absyn_Syntax.v, (xexp, empty_env))))::entries)
end)) [] vars)
in (let env = (extend_env config.environment env_entries)
in (let w = (match (w) with
| None -> begin
None
end
| Some (w) -> begin
(let c_w = (wne tcenv (let _32_1138 = config
in {code = w; environment = env; stack = empty_stack; close = _32_1138.close; steps = _32_1138.steps}))
in Some (c_w.code))
end)
in (let c_body = (wne tcenv (let _32_1142 = config
in {code = body; environment = env; stack = empty_stack; close = _32_1142.close; steps = _32_1142.steps}))
in (let _98_474 = (norm_pat pat)
in (_98_474, w, c_body.code)))))))))))
end))
in (let eqns = (Microsoft_FStar_List.map wn_eqn eqns)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_match (c_e1.code, eqns) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (All.pipe_right (let _32_1147 = config
in {code = e; environment = _32_1147.environment; stack = _32_1147.stack; close = _32_1147.close; steps = _32_1147.steps}) rebuild)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), body) -> begin
(let _32_1179 = (All.pipe_right lbs (Microsoft_FStar_List.fold_left (fun _32_1157 _32_1162 -> (match ((_32_1157, _32_1162)) with
| ((env, lbs), {Microsoft_FStar_Absyn_Syntax.lbname = x; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = eff; Microsoft_FStar_Absyn_Syntax.lbdef = e}) -> begin
(let c = (wne tcenv (let _32_1163 = config
in {code = e; environment = _32_1163.environment; stack = empty_stack; close = _32_1163.close; steps = _32_1163.steps}))
in (let t = (sn tcenv (t_config t config.environment config.steps))
in (let _32_1176 = (match (x) with
| Microsoft_FStar_Util.Inl (x) -> begin
(let y = (let _98_477 = (match (is_rec) with
| true -> begin
x
end
| false -> begin
(Microsoft_FStar_Absyn_Util.freshen_bvd x)
end)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _98_477 t.code))
in (let yexp = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (let y_for_x = V ((x, (yexp, empty_env)))
in (Microsoft_FStar_Util.Inl (y.Microsoft_FStar_Absyn_Syntax.v), (extend_env' env y_for_x)))))
end
| _32_1173 -> begin
(x, env)
end)
in (match (_32_1176) with
| (y, env) -> begin
(let _98_479 = (let _98_478 = (Microsoft_FStar_Absyn_Syntax.mk_lb (y, eff, t.code, c.code))
in (_98_478)::lbs)
in (env, _98_479))
end))))
end)) (config.environment, [])))
in (match (_32_1179) with
| (env, lbs) -> begin
(let lbs = (Microsoft_FStar_List.rev lbs)
in (let c_body = (wne tcenv (let _32_1181 = config
in {code = body; environment = env; stack = empty_stack; close = _32_1181.close; steps = _32_1181.steps}))
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), c_body.code) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (All.pipe_right (let _32_1185 = config
in {code = e; environment = _32_1185.environment; stack = _32_1185.stack; close = _32_1185.close; steps = _32_1185.steps}) rebuild))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed (e, t, l) -> begin
(let c = (wne tcenv (let _32_1192 = config
in {code = e; environment = _32_1192.environment; stack = _32_1192.stack; close = _32_1192.close; steps = _32_1192.steps}))
in (match ((is_stack_empty config)) with
| true -> begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (let _98_481 = (let _32_1196 = config
in (let _98_480 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (c.code, t.code, l) None e.Microsoft_FStar_Absyn_Syntax.pos)
in {code = _98_480; environment = _32_1196.environment; stack = _32_1196.stack; close = _32_1196.close; steps = _32_1196.steps}))
in (rebuild _98_481)))
end
| false -> begin
c
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared (e, info)) -> begin
(let c = (wne tcenv (let _32_1203 = config
in {code = e; environment = _32_1203.environment; stack = _32_1203.stack; close = _32_1203.close; steps = _32_1203.steps}))
in (match ((is_stack_empty config)) with
| true -> begin
(let _98_483 = (let _32_1206 = config
in (let _98_482 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((c.code, info))))
in {code = _98_482; environment = _32_1206.environment; stack = _32_1206.stack; close = _32_1206.close; steps = _32_1206.steps}))
in (rebuild _98_483))
end
| false -> begin
c
end))
end)))))

let norm_kind = (fun steps tcenv k -> (let c = (snk tcenv (k_config k empty_env steps))
in (Microsoft_FStar_Absyn_Util.compress_kind c.code)))

let norm_typ = (fun steps tcenv t -> (let c = (sn tcenv (t_config t empty_env steps))
in c.code))

let norm_exp = (fun steps tcenv e -> (let c = (wne tcenv (e_config e empty_env steps))
in c.code))

let norm_sigelt = (fun tcenv _32_9 -> (match (_32_9) with
| Microsoft_FStar_Absyn_Syntax.Sig_let (lbs, r, l, b) -> begin
(let e = (let _98_507 = (let _98_506 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant Microsoft_FStar_Absyn_Syntax.Const_unit None r)
in (lbs, _98_506))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_let _98_507 None r))
in (let e = (norm_exp ((Beta)::[]) tcenv e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_let (lbs, _32_1232) -> begin
Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, l, b))
end
| _32_1236 -> begin
(All.failwith "Impossible")
end)))
end
| s -> begin
s
end))

let whnf = (fun tcenv t -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_refine (_)) -> begin
t
end
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)) | (Microsoft_FStar_Absyn_Syntax.Typ_app ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _98_512 = (eta_expand tcenv t)
in (All.pipe_right _98_512 Microsoft_FStar_Absyn_Util.compress_typ))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)) | (_) -> begin
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
in (Microsoft_FStar_Absyn_Print.exp_to_string _98_535)))

let typ_norm_to_string = (fun tcenv t -> (let _98_540 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv t)
in (Microsoft_FStar_Absyn_Print.typ_to_string _98_540)))

let kind_norm_to_string = (fun tcenv k -> (let _98_545 = (norm_kind ((Beta)::(SNComp)::(Unmeta)::[]) tcenv k)
in (Microsoft_FStar_Absyn_Print.kind_to_string _98_545)))

let formula_norm_to_string = (fun tcenv f -> (let _98_550 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv f)
in (Microsoft_FStar_Absyn_Print.formula_to_string _98_550)))

let comp_typ_norm_to_string = (fun tcenv c -> (let _98_555 = (norm_comp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv c)
in (Microsoft_FStar_Absyn_Print.comp_typ_to_string _98_555)))

let normalize_refinement = (fun env t0 -> (let t = (norm_typ ((Beta)::(WHNF)::(DeltaHard)::[]) env t0)
in (let rec aux = (fun t -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(let t0 = (aux x.Microsoft_FStar_Absyn_Syntax.sort)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine (y, phi1) -> begin
(let _98_568 = (let _98_567 = (let _98_566 = (let _98_565 = (let _98_564 = (let _98_563 = (let _98_562 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _98_562))
in Microsoft_FStar_Util.Inr (_98_563))
in (_98_564)::[])
in (Microsoft_FStar_Absyn_Util.subst_typ _98_565 phi))
in (Microsoft_FStar_Absyn_Util.mk_conj phi1 _98_566))
in (y, _98_567))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _98_568 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) t0.Microsoft_FStar_Absyn_Syntax.pos))
end
| _32_1344 -> begin
t
end))
end
| _32_1346 -> begin
t
end)))
in (aux t))))




