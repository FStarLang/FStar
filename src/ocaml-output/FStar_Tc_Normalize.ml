
open Prims
type step =
| WHNF
| Eta
| EtaArgs
| Delta
| DeltaHard
| UnfoldOpaque
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

let is_UnfoldOpaque = (fun _discr_ -> (match (_discr_) with
| UnfoldOpaque -> begin
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

let is_Mkconfig = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkconfig"))))

let is_Mkenvironment = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenvironment"))))

let is_Mkstack = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkstack"))))

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
| T (_46_26) -> begin
_46_26
end))

let ___V____0 = (fun projectee -> (match (projectee) with
| V (_46_29) -> begin
_46_29
end))

let empty_env = {context = []; label_suffix = []}

let extend_env' = (fun env b -> (let _46_32 = env
in {context = (b)::env.context; label_suffix = _46_32.label_suffix}))

let extend_env = (fun env bindings -> (let _46_36 = env
in {context = (FStar_List.append bindings env.context); label_suffix = _46_36.label_suffix}))

let lookup_env = (fun env key -> (FStar_All.pipe_right env.context (FStar_Util.find_opt (fun _46_1 -> (match (_46_1) with
| T (a, _46_43) -> begin
(a.FStar_Absyn_Syntax.realname.FStar_Ident.idText = key)
end
| V (x, _46_48) -> begin
(x.FStar_Absyn_Syntax.realname.FStar_Ident.idText = key)
end)))))

let fold_env = (fun env f acc -> (FStar_List.fold_left (fun acc v -> (match (v) with
| T (a, _46_58) -> begin
(f a.FStar_Absyn_Syntax.realname.FStar_Ident.idText v acc)
end
| V (x, _46_63) -> begin
(f x.FStar_Absyn_Syntax.realname.FStar_Ident.idText v acc)
end)) acc env.context))

let empty_stack = {args = []}

let rec subst_of_env' = (fun env -> (fold_env env (fun _46_67 v acc -> (match (v) with
| T (a, (t, env')) -> begin
(let _99_113 = (let _99_112 = (let _99_111 = (let _99_110 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_typ _99_110 t))
in (a, _99_111))
in FStar_Util.Inl (_99_112))
in (_99_113)::acc)
end
| V (x, (v, env')) -> begin
(let _99_117 = (let _99_116 = (let _99_115 = (let _99_114 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_exp _99_114 v))
in (x, _99_115))
in FStar_Util.Inr (_99_116))
in (_99_117)::acc)
end)) []))

let subst_of_env = (fun tcenv env -> (subst_of_env' env))

let with_new_code = (fun c e -> {code = e; environment = c.environment; stack = empty_stack; close = None; steps = c.steps})

let rec eta_expand = (fun tcenv t -> (let k = (let _99_127 = (FStar_Tc_Recheck.recompute_kind t)
in (FStar_All.pipe_right _99_127 FStar_Absyn_Util.compress_kind))
in (let rec aux = (fun t k -> (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
t
end
| FStar_Absyn_Syntax.Kind_abbrev (_46_99, k) -> begin
(aux t k)
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k') -> begin
(match ((let _99_132 = (FStar_Absyn_Util.unascribe_typ t)
in _99_132.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam (real, body) -> begin
(let rec aux = (fun real expected -> (match ((real, expected)) with
| (_46_116::real, _46_120::expected) -> begin
(aux real expected)
end
| ([], []) -> begin
t
end
| (_46_129::_46_127, []) -> begin
(FStar_All.failwith "Ill-kinded type")
end
| ([], more) -> begin
(let _46_138 = (FStar_Absyn_Util.args_of_binders more)
in (match (_46_138) with
| (more, args) -> begin
(let body = (FStar_Absyn_Syntax.mk_Typ_app (body, args) None body.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_lam ((FStar_List.append binders more), body) None body.FStar_Absyn_Syntax.pos))
end))
end))
in (aux real binders))
end
| _46_141 -> begin
(let _46_144 = (FStar_Absyn_Util.args_of_binders binders)
in (match (_46_144) with
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
(let _99_140 = (let _99_139 = (let _99_137 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _99_137 FStar_Range.string_of_range))
in (let _99_138 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "%s: Impossible: Kind_unknown: %s" _99_139 _99_138)))
in (FStar_All.failwith _99_140))
end))
in (aux t k))))

let is_var = (fun t -> (match ((FStar_Absyn_Util.compress_typ t)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (_46_163); FStar_Absyn_Syntax.tk = _46_161; FStar_Absyn_Syntax.pos = _46_159; FStar_Absyn_Syntax.fvs = _46_157; FStar_Absyn_Syntax.uvs = _46_155} -> begin
true
end
| _46_167 -> begin
false
end))

let rec eta_expand_exp = (fun tcenv e -> (let t = (let _99_147 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_All.pipe_right _99_147 FStar_Absyn_Util.compress_typ))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((let _99_148 = (FStar_Absyn_Util.compress_exp e)
in _99_148.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
if ((FStar_List.length bs) = (FStar_List.length bs')) then begin
e
end else begin
(FStar_All.failwith "NYI")
end
end
| _46_180 -> begin
(let _46_183 = (FStar_Absyn_Util.args_of_binders bs)
in (match (_46_183) with
| (bs, args) -> begin
(let _99_150 = (let _99_149 = (FStar_Absyn_Syntax.mk_Exp_app (e, args) None e.FStar_Absyn_Syntax.pos)
in (bs, _99_149))
in (FStar_Absyn_Syntax.mk_Exp_abs _99_150 (Some (t)) e.FStar_Absyn_Syntax.pos))
end))
end)
end
| _46_185 -> begin
e
end)))

let no_eta = (fun s -> (FStar_All.pipe_right s (FStar_List.filter (fun _46_2 -> (match (_46_2) with
| Eta -> begin
false
end
| _46_190 -> begin
true
end)))))

let no_eta_cfg = (fun c -> (let _46_192 = c
in (let _99_155 = (no_eta c.steps)
in {code = _46_192.code; environment = _46_192.environment; stack = _46_192.stack; close = _46_192.close; steps = _99_155})))

let whnf_only = (fun config -> (FStar_All.pipe_right config.steps (FStar_List.contains WHNF)))

let unmeta = (fun config -> (FStar_All.pipe_right config.steps (FStar_List.contains Unmeta)))

let unlabel = (fun config -> ((unmeta config) || (FStar_All.pipe_right config.steps (FStar_List.contains Unlabel))))

let is_stack_empty = (fun config -> (match (config.stack.args) with
| [] -> begin
true
end
| _46_200 -> begin
false
end))

let has_eta = (fun cfg -> (FStar_All.pipe_right cfg.steps (FStar_List.contains Eta)))

let rec weak_norm_comp = (fun env comp -> (let c = (FStar_Absyn_Util.comp_to_comp_typ comp)
in (match ((FStar_Tc_Env.lookup_effect_abbrev env c.FStar_Absyn_Syntax.effect_name)) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(let binders' = (FStar_List.map (fun _46_3 -> (match (_46_3) with
| (FStar_Util.Inl (b), imp) -> begin
(let _99_167 = (let _99_166 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inl (_99_166))
in (_99_167, imp))
end
| (FStar_Util.Inr (b), imp) -> begin
(let _99_169 = (let _99_168 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inr (_99_168))
in (_99_169, imp))
end)) binders)
in (let subst = (let _99_171 = (let _99_170 = (FStar_Absyn_Util.args_of_binders binders')
in (FStar_All.pipe_right _99_170 Prims.snd))
in (FStar_Absyn_Util.subst_of_list binders _99_171))
in (let cdef = (FStar_Absyn_Util.subst_comp subst cdef)
in (let subst = (FStar_Absyn_Util.subst_of_list binders' (((FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ))::c.FStar_Absyn_Syntax.effect_args))
in (let c1 = (FStar_Absyn_Util.subst_comp subst cdef)
in (let c = (FStar_All.pipe_right (let _46_224 = (FStar_Absyn_Util.comp_to_comp_typ c1)
in {FStar_Absyn_Syntax.effect_name = _46_224.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _46_224.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _46_224.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = c.FStar_Absyn_Syntax.flags}) FStar_Absyn_Syntax.mk_Comp)
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

let rec is_head_symbol = (fun t -> (match ((let _99_202 = (FStar_Absyn_Util.compress_typ t)
in _99_202.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _46_255, _46_257)) -> begin
(is_head_symbol t)
end
| _46_262 -> begin
false
end))

let simplify_then_apply = (fun steps head args pos -> (let fallback = (fun _46_268 -> (match (()) with
| () -> begin
(FStar_Absyn_Syntax.mk_Typ_app (head, args) None pos)
end))
in (let simp_t = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
Some (true)
end
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid) -> begin
Some (false)
end
| _46_276 -> begin
None
end))
in (let simplify = (fun arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (t) -> begin
((simp_t t), arg)
end
| _46_282 -> begin
(None, arg)
end))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps)) then begin
(fallback ())
end else begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.and_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _)::(_, (FStar_Util.Inl (arg), _))::[]) | ((_, (FStar_Util.Inl (arg), _))::(Some (true), _)::[]) -> begin
arg
end
| ((Some (false), _)::_::[]) | (_::(Some (false), _)::[]) -> begin
FStar_Absyn_Util.t_false
end
| _46_329 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.or_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _)::_::[]) | (_::(Some (true), _)::[]) -> begin
FStar_Absyn_Util.t_true
end
| ((Some (false), _)::(_, (FStar_Util.Inl (arg), _))::[]) | ((_, (FStar_Util.Inl (arg), _))::(Some (false), _)::[]) -> begin
arg
end
| _46_374 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
FStar_Absyn_Util.t_true
end
| (Some (true), _46_402)::(_46_392, (FStar_Util.Inl (arg), _46_396))::[] -> begin
arg
end
| _46_406 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (Some (true), _46_410)::[] -> begin
FStar_Absyn_Util.t_false
end
| (Some (false), _46_416)::[] -> begin
FStar_Absyn_Util.t_true
end
| _46_420 -> begin
(fallback ())
end)
end else begin
if ((((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.forall_lid) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid)) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exists_lid)) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) then begin
(match (args) with
| ((FStar_Util.Inl (t), _)::[]) | (_::(FStar_Util.Inl (t), _)::[]) -> begin
(match ((let _99_217 = (FStar_Absyn_Util.compress_typ t)
in _99_217.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam (_46_435::[], body) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
FStar_Absyn_Util.t_true
end
| Some (false) -> begin
FStar_Absyn_Util.t_false
end
| _46_445 -> begin
(fallback ())
end)
end
| _46_447 -> begin
(fallback ())
end)
end
| _46_449 -> begin
(fallback ())
end)
end else begin
(fallback ())
end
end
end
end
end
end
| _46_451 -> begin
(fallback ())
end)
end))))

let rec sn_delay = (fun tcenv cfg -> (let aux = (fun _46_455 -> (match (()) with
| () -> begin
(let _99_243 = (sn tcenv cfg)
in _99_243.code)
end))
in (let t = (FStar_Absyn_Syntax.mk_Typ_delayed' (FStar_Util.Inr (aux)) None cfg.code.FStar_Absyn_Syntax.pos)
in (let _46_457 = cfg
in {code = t; environment = _46_457.environment; stack = empty_stack; close = _46_457.close; steps = _46_457.steps}))))
and sn = (fun tcenv cfg -> (let rebuild = (fun config -> (let rebuild_stack = (fun config -> if (is_stack_empty config) then begin
config
end else begin
(let s' = if (FStar_List.contains EtaArgs config.steps) then begin
config.steps
end else begin
(no_eta config.steps)
end
in (let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _46_4 -> (match (_46_4) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _99_255 = (let _99_254 = (let _99_253 = (sn tcenv (t_config t env s'))
in _99_253.code)
in (FStar_All.pipe_left (fun _99_252 -> FStar_Util.Inl (_99_252)) _99_254))
in (_99_255, imp))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _99_259 = (let _99_258 = (let _99_257 = (wne tcenv (e_config v env s'))
in _99_257.code)
in (FStar_All.pipe_left (fun _99_256 -> FStar_Util.Inr (_99_256)) _99_258))
in (_99_259, imp))
end))))
in (let t = (simplify_then_apply config.steps config.code args config.code.FStar_Absyn_Syntax.pos)
in (let _46_481 = config
in {code = t; environment = _46_481.environment; stack = empty_stack; close = _46_481.close; steps = _46_481.steps}))))
end)
in (let config = (rebuild_stack config)
in (let t = (match (config.close) with
| None -> begin
config.code
end
| Some (f) -> begin
(f config.code)
end)
in if (has_eta config) then begin
(let _46_488 = config
in (let _99_261 = (eta_expand tcenv t)
in {code = _99_261; environment = _46_488.environment; stack = _46_488.stack; close = _46_488.close; steps = _46_488.steps}))
end else begin
(let _46_490 = config
in {code = t; environment = _46_490.environment; stack = _46_490.stack; close = _46_490.close; steps = _46_490.steps})
end))))
in (let wk = (fun f -> (match ((FStar_ST.read cfg.code.FStar_Absyn_Syntax.tk)) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _46_501; FStar_Absyn_Syntax.pos = _46_499; FStar_Absyn_Syntax.fvs = _46_497; FStar_Absyn_Syntax.uvs = _46_495}) -> begin
(f (Some (FStar_Absyn_Syntax.ktype)) cfg.code.FStar_Absyn_Syntax.pos)
end
| _46_506 -> begin
(f None cfg.code.FStar_Absyn_Syntax.pos)
end))
in (let config = (let _46_507 = cfg
in (let _99_274 = (FStar_Absyn_Util.compress_typ cfg.code)
in {code = _99_274; environment = _46_507.environment; stack = _46_507.stack; close = _46_507.close; steps = _46_507.steps}))
in (match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_46_511) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_uvar (_46_514) -> begin
(rebuild config)
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let topt = if (FStar_All.pipe_right config.steps (FStar_List.contains UnfoldOpaque)) then begin
(FStar_Tc_Env.lookup_opaque_typ_abbrev tcenv fv.FStar_Absyn_Syntax.v)
end else begin
if ((FStar_All.pipe_right config.steps (FStar_List.contains DeltaHard)) || ((FStar_All.pipe_right config.steps (FStar_List.contains Delta)) && (FStar_All.pipe_left Prims.op_Negation (is_stack_empty config)))) then begin
(FStar_Tc_Env.lookup_typ_abbrev tcenv fv.FStar_Absyn_Syntax.v)
end else begin
None
end
end
in (match (topt) with
| None -> begin
(rebuild config)
end
| Some (t) -> begin
(sn tcenv (let _46_522 = config
in {code = t; environment = _46_522.environment; stack = _46_522.stack; close = _46_522.close; steps = _46_522.steps}))
end))
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(match ((lookup_env config.environment a.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname.FStar_Ident.idText)) with
| None -> begin
(rebuild config)
end
| Some (T (_46_528, (t, e))) -> begin
(sn tcenv (let _46_535 = config
in {code = t; environment = e; stack = _46_535.stack; close = _46_535.close; steps = _46_535.steps}))
end
| _46_538 -> begin
(FStar_All.failwith "Impossible: expected a type")
end)
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let args = (FStar_List.fold_right (fun a out -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _46_546 = config.stack
in {args = args})
in (sn tcenv (let _46_549 = config
in {code = head; environment = _46_549.environment; stack = stack; close = _46_549.close; steps = _46_549.steps}))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(match (config.stack.args) with
| [] -> begin
(let _46_558 = (sn_binders tcenv binders config.environment config.steps)
in (match (_46_558) with
| (binders, environment) -> begin
(let mk_lam = (fun t -> (let lam = (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_lam (binders, t)))
in (match (cfg.close) with
| None -> begin
lam
end
| Some (f) -> begin
(f lam)
end)))
in (let t2_cfg = (let _99_287 = (let _99_286 = (no_eta config.steps)
in {code = t2; environment = environment; stack = empty_stack; close = None; steps = _99_286})
in (sn_delay tcenv _99_287))
in (let _46_566 = t2_cfg
in (let _99_288 = (mk_lam t2_cfg.code)
in {code = _99_288; environment = _46_566.environment; stack = _46_566.stack; close = _46_566.close; steps = _46_566.steps}))))
end))
end
| args -> begin
(let rec beta = (fun env_entries binders args -> (match ((binders, args)) with
| ([], _46_575) -> begin
(let env = (extend_env config.environment env_entries)
in (sn tcenv (let _46_578 = config
in {code = t2; environment = env; stack = (let _46_580 = config.stack
in {args = args}); close = _46_578.close; steps = _46_578.steps})))
end
| (_46_583, []) -> begin
(let t = (FStar_Absyn_Syntax.mk_Typ_lam (binders, t2) None t2.FStar_Absyn_Syntax.pos)
in (let env = (extend_env config.environment env_entries)
in (sn tcenv (let _46_588 = config
in {code = t; environment = env; stack = empty_stack; close = _46_588.close; steps = _46_588.steps}))))
end
| (formal::rest, actual::rest') -> begin
(let m = (match ((formal, actual)) with
| ((FStar_Util.Inl (a), _46_600), ((FStar_Util.Inl (t), _46_605), env)) -> begin
T ((a.FStar_Absyn_Syntax.v, (t, env)))
end
| ((FStar_Util.Inr (x), _46_613), ((FStar_Util.Inr (v), _46_618), env)) -> begin
V ((x.FStar_Absyn_Syntax.v, (v, env)))
end
| _46_624 -> begin
(let _99_299 = (let _99_298 = (let _99_295 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _99_295))
in (let _99_297 = (FStar_Absyn_Print.binder_to_string formal)
in (let _99_296 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _99_298 _99_297 _99_296))))
in (FStar_All.failwith _99_299))
end)
in (beta ((m)::env_entries) rest rest'))
end))
in (beta [] binders args))
end)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _46_628) -> begin
(sn tcenv (let _46_631 = config
in {code = t; environment = _46_631.environment; stack = _46_631.stack; close = _46_631.close; steps = _46_631.steps}))
end
| _46_634 -> begin
(match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, comp) -> begin
(let _46_641 = (sn_binders tcenv bs config.environment config.steps)
in (match (_46_641) with
| (binders, environment) -> begin
(let c2 = (sncomp tcenv (c_config comp environment config.steps))
in (let _99_303 = (let _46_643 = config
in (let _99_302 = (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_fun (binders, c2.code)))
in {code = _99_302; environment = _46_643.environment; stack = _46_643.stack; close = _46_643.close; steps = _46_643.steps}))
in (rebuild _99_303)))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((sn_binders tcenv (((FStar_Absyn_Syntax.v_binder x))::[]) config.environment config.steps)) with
| ((FStar_Util.Inr (x), _46_652)::[], env) -> begin
(let refine = (fun t -> (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_refine (x, t))))
in (let _99_310 = (let _99_309 = (FStar_All.pipe_right config.steps (FStar_List.filter (fun _46_5 -> (match (_46_5) with
| UnfoldOpaque -> begin
false
end
| _46_662 -> begin
true
end))))
in {code = t; environment = env; stack = empty_stack; close = (close_with_config config refine); steps = _99_309})
in (sn tcenv _99_310)))
end
| _46_664 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
if (unmeta config) then begin
(sn tcenv (let _46_670 = config
in {code = t; environment = _46_670.environment; stack = _46_670.stack; close = _46_670.close; steps = _46_670.steps}))
end else begin
(let pat = (fun t -> (let ps = (FStar_All.pipe_right ps (FStar_List.map (sn_args true tcenv config.environment config.steps)))
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern ((t, ps)))))))
in (sn tcenv (let _46_675 = config
in {code = t; environment = _46_675.environment; stack = _46_675.stack; close = (close_with_config config pat); steps = _46_675.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, b)) -> begin
if (unlabel config) then begin
(sn tcenv (let _46_684 = config
in {code = t; environment = _46_684.environment; stack = _46_684.stack; close = _46_684.close; steps = _46_684.steps}))
end else begin
(let lab = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when ((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) && (FStar_All.pipe_right config.steps (FStar_List.contains Simplify))) -> begin
t
end
| _46_691 -> begin
(match (config.environment.label_suffix) with
| (b', sfx)::_46_693 -> begin
if ((b' = None) || (Some (b) = b')) then begin
(let _46_698 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _99_317 = (FStar_Range.string_of_range sfx)
in (FStar_Util.print2 "Stripping label %s because of enclosing refresh %s\n" l _99_317))
end else begin
()
end
in t)
end else begin
(let _46_700 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _99_318 = (FStar_Range.string_of_range sfx)
in (FStar_Util.print1 "Normalizer refreshing label: %s\n" _99_318))
end else begin
()
end
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, sfx, b))))))
end
end
| _46_703 -> begin
(FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b)))))
end)
end))
in (sn tcenv (let _46_704 = config
in {code = t; environment = _46_704.environment; stack = _46_704.stack; close = (close_with_config config lab); steps = _46_704.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
if (unmeta config) then begin
(sn tcenv (let _46_712 = config
in {code = t; environment = _46_712.environment; stack = _46_712.stack; close = _46_712.close; steps = _46_712.steps}))
end else begin
(let sfx = (match (b) with
| Some (false) -> begin
r
end
| _46_717 -> begin
FStar_Absyn_Syntax.dummyRange
end)
in (let config = (let _46_719 = config
in {code = t; environment = (let _46_721 = config.environment
in {context = _46_721.context; label_suffix = ((b, sfx))::config.environment.label_suffix}); stack = _46_719.stack; close = _46_719.close; steps = _46_719.steps})
in (sn tcenv config)))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
if (FStar_ST.read flag) then begin
(let _99_324 = (let _46_730 = config
in (let _99_323 = (FStar_Absyn_Util.mk_conj t1 t2)
in {code = _99_323; environment = _46_730.environment; stack = _46_730.stack; close = _46_730.close; steps = _46_730.steps}))
in (sn tcenv _99_324))
end else begin
(let c1 = (sn tcenv (t_config t1 config.environment config.steps))
in (let c2 = (sn tcenv (t_config t2 config.environment config.steps))
in (let _99_326 = (let _46_734 = config
in (let _99_325 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula ((c1.code, c2.code, flag))))
in {code = _99_325; environment = _46_734.environment; stack = _46_734.stack; close = _46_734.close; steps = _46_734.steps}))
in (rebuild _99_326))))
end
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_))) | (FStar_Absyn_Syntax.Typ_unknown) | (_) -> begin
(let _99_331 = (let _99_330 = (let _99_327 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _99_327 FStar_Range.string_of_range))
in (let _99_329 = (FStar_Absyn_Print.tag_of_typ config.code)
in (let _99_328 = (FStar_Absyn_Print.typ_to_string config.code)
in (FStar_Util.format3 "(%s) Unexpected type (%s): %s" _99_330 _99_329 _99_328))))
in (FStar_All.failwith _99_331))
end)
end)))))
and sn_binders = (fun tcenv binders env steps -> (let rec aux = (fun out env _46_6 -> (match (_46_6) with
| (FStar_Util.Inl (a), imp)::rest -> begin
(let c = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort env steps))
in (let b = (let _99_342 = (FStar_Absyn_Util.freshen_bvd a.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _99_342 c.code))
in (let btyp = (FStar_Absyn_Util.btvar_to_typ b)
in (let b_for_a = T ((a.FStar_Absyn_Syntax.v, (btyp, empty_env)))
in (aux (((FStar_Util.Inl (b), imp))::out) (extend_env' env b_for_a) rest)))))
end
| (FStar_Util.Inr (x), imp)::rest -> begin
(let c = (sn_delay tcenv (t_config x.FStar_Absyn_Syntax.sort env steps))
in (let y = (let _99_343 = (FStar_Absyn_Util.freshen_bvd x.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _99_343 c.code))
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
in (let _46_778 = cfg
in (let _99_346 = (FStar_Absyn_Syntax.mk_Comp ctconf.code)
in {code = _99_346; environment = _46_778.environment; stack = _46_778.stack; close = _46_778.close; steps = _46_778.steps})))
end
| FStar_Absyn_Syntax.Total (t) -> begin
if (FStar_List.contains DeltaComp cfg.steps) then begin
(let _99_350 = (let _99_349 = (let _99_348 = (let _99_347 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_Absyn_Util.comp_to_comp_typ _99_347))
in (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp _99_348))
in (with_new_code cfg _99_349))
in (FStar_All.pipe_left (sncomp tcenv) _99_350))
end else begin
(let t = (sn tcenv (with_new_code cfg t))
in (let _99_351 = (FStar_Absyn_Syntax.mk_Total t.code)
in (with_new_code cfg _99_351)))
end
end)))
and sncomp_typ = (fun tcenv cfg -> (let m = cfg.code
in (let norm = (fun _46_787 -> (match (()) with
| () -> begin
(let remake = (fun l r eargs flags -> (let c = {FStar_Absyn_Syntax.effect_name = l; FStar_Absyn_Syntax.result_typ = r; FStar_Absyn_Syntax.effect_args = eargs; FStar_Absyn_Syntax.flags = flags}
in (let _46_794 = cfg
in {code = c; environment = _46_794.environment; stack = _46_794.stack; close = _46_794.close; steps = _46_794.steps})))
in (let res = (let _99_364 = (sn tcenv (with_new_code cfg m.FStar_Absyn_Syntax.result_typ))
in _99_364.code)
in (let sn_flags = (fun flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _46_7 -> (match (_46_7) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let e = (let _99_368 = (wne tcenv (e_config e cfg.environment cfg.steps))
in _99_368.code)
in FStar_Absyn_Syntax.DECREASES (e))
end
| f -> begin
f
end)))))
in (let _46_806 = (let _99_370 = (sn_flags m.FStar_Absyn_Syntax.flags)
in (let _99_369 = (sn_args true tcenv cfg.environment cfg.steps m.FStar_Absyn_Syntax.effect_args)
in (_99_370, _99_369)))
in (match (_46_806) with
| (flags, args) -> begin
(remake m.FStar_Absyn_Syntax.effect_name res args flags)
end)))))
end))
in if (FStar_List.contains DeltaComp cfg.steps) then begin
(match ((FStar_Tc_Env.lookup_effect_abbrev tcenv m.FStar_Absyn_Syntax.effect_name)) with
| Some (_46_808) -> begin
(let c = (let _99_371 = (FStar_Absyn_Syntax.mk_Comp m)
in (weak_norm_comp tcenv _99_371))
in (sncomp_typ tcenv (let _46_811 = cfg
in {code = c; environment = _46_811.environment; stack = _46_811.stack; close = _46_811.close; steps = _46_811.steps})))
end
| _46_814 -> begin
(norm ())
end)
end else begin
(norm ())
end)))
and sn_args = (fun delay tcenv env steps args -> (FStar_All.pipe_right args (FStar_List.map (fun _46_8 -> (match (_46_8) with
| (FStar_Util.Inl (t), imp) when delay -> begin
(let _99_381 = (let _99_380 = (let _99_379 = (sn_delay tcenv (t_config t env steps))
in _99_379.code)
in (FStar_All.pipe_left (fun _99_378 -> FStar_Util.Inl (_99_378)) _99_380))
in (_99_381, imp))
end
| (FStar_Util.Inl (t), imp) -> begin
(let _99_385 = (let _99_384 = (let _99_383 = (sn tcenv (t_config t env steps))
in _99_383.code)
in (FStar_All.pipe_left (fun _99_382 -> FStar_Util.Inl (_99_382)) _99_384))
in (_99_385, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _99_389 = (let _99_388 = (let _99_387 = (wne tcenv (e_config e env steps))
in _99_387.code)
in (FStar_All.pipe_left (fun _99_386 -> FStar_Util.Inr (_99_386)) _99_388))
in (_99_389, imp))
end)))))
and snk = (fun tcenv cfg -> (let w = (fun f -> (f cfg.code.FStar_Absyn_Syntax.pos))
in (match ((let _99_399 = (FStar_Absyn_Util.compress_kind cfg.code)
in _99_399.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Kind_delayed (_)) | (FStar_Absyn_Syntax.Kind_lam (_)) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
cfg
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(let args = (let _99_400 = (no_eta cfg.steps)
in (sn_args false tcenv cfg.environment _99_400 args))
in (let _46_850 = cfg
in (let _99_402 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar (uv, args)))
in {code = _99_402; environment = _46_850.environment; stack = _46_850.stack; close = _46_850.close; steps = _46_850.steps})))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _46_862; FStar_Absyn_Syntax.pos = _46_860; FStar_Absyn_Syntax.fvs = _46_858; FStar_Absyn_Syntax.uvs = _46_856}) -> begin
(let _46_871 = (FStar_Tc_Env.lookup_kind_abbrev tcenv l)
in (match (_46_871) with
| (_46_868, binders, body) -> begin
(let subst = (FStar_Absyn_Util.subst_of_list binders args)
in (let _99_404 = (let _46_873 = cfg
in (let _99_403 = (FStar_Absyn_Util.subst_kind subst body)
in {code = _99_403; environment = _46_873.environment; stack = _46_873.stack; close = _46_873.close; steps = _46_873.steps}))
in (snk tcenv _99_404)))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_46_876, k) -> begin
(snk tcenv (let _46_880 = cfg
in {code = k; environment = _46_880.environment; stack = _46_880.stack; close = _46_880.close; steps = _46_880.steps}))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _46_888 = (sn_binders tcenv bs cfg.environment cfg.steps)
in (match (_46_888) with
| (bs, env) -> begin
(let c2 = (snk tcenv (k_config k env cfg.steps))
in (let _46_898 = (match (c2.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs', k) -> begin
((FStar_List.append bs bs'), k)
end
| _46_895 -> begin
(bs, c2.code)
end)
in (match (_46_898) with
| (bs, rhs) -> begin
(let _46_899 = cfg
in (let _99_406 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (bs, rhs)))
in {code = _99_406; environment = _46_899.environment; stack = _46_899.stack; close = _46_899.close; steps = _46_899.steps}))
end)))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(FStar_All.failwith "Impossible")
end)))
and wne = (fun tcenv cfg -> (let e = (FStar_Absyn_Util.compress_exp cfg.code)
in (let config = (let _46_905 = cfg
in {code = e; environment = _46_905.environment; stack = _46_905.stack; close = _46_905.close; steps = _46_905.steps})
in (let rebuild = (fun config -> if (is_stack_empty config) then begin
config
end else begin
(let s' = if (FStar_List.contains EtaArgs config.steps) then begin
config.steps
end else begin
(no_eta config.steps)
end
in (let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _46_9 -> (match (_46_9) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _99_415 = (let _99_414 = (let _99_413 = (sn tcenv (t_config t env s'))
in _99_413.code)
in (FStar_All.pipe_left (fun _99_412 -> FStar_Util.Inl (_99_412)) _99_414))
in (_99_415, imp))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _99_419 = (let _99_418 = (let _99_417 = (wne tcenv (e_config v env s'))
in _99_417.code)
in (FStar_All.pipe_left (fun _99_416 -> FStar_Util.Inr (_99_416)) _99_418))
in (_99_419, imp))
end))))
in (let _46_925 = config
in (let _99_420 = (FStar_Absyn_Syntax.mk_Exp_app (config.code, args) None config.code.FStar_Absyn_Syntax.pos)
in {code = _99_420; environment = _46_925.environment; stack = empty_stack; close = _46_925.close; steps = _46_925.steps}))))
end)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_46_928) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
(FStar_All.pipe_right config rebuild)
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(match ((lookup_env config.environment x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname.FStar_Ident.idText)) with
| None -> begin
(FStar_All.pipe_right config rebuild)
end
| Some (V (_46_943, (vc, env))) -> begin
(wne tcenv (let _46_950 = config
in {code = vc; environment = env; stack = _46_950.stack; close = _46_950.close; steps = _46_950.steps}))
end
| _46_953 -> begin
(FStar_All.failwith "Impossible: ill-typed term")
end)
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let args = (FStar_List.fold_right (fun a out -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _46_961 = config.stack
in {args = args})
in (wne tcenv (let _46_964 = config
in {code = head; environment = _46_964.environment; stack = stack; close = _46_964.close; steps = _46_964.steps}))))
end
| FStar_Absyn_Syntax.Exp_abs (binders, body) -> begin
(let rec beta = (fun entries binders args -> (match ((binders, args)) with
| ([], _46_976) -> begin
(let env = (extend_env config.environment entries)
in (wne tcenv (let _46_979 = config
in {code = body; environment = env; stack = (let _46_981 = config.stack
in {args = args}); close = _46_979.close; steps = _46_979.steps})))
end
| (_46_984, []) -> begin
(let env = (extend_env config.environment entries)
in (let _46_990 = (sn_binders tcenv binders env config.steps)
in (match (_46_990) with
| (binders, env) -> begin
(let mk_abs = (fun t -> (FStar_Absyn_Syntax.mk_Exp_abs (binders, t) None body.FStar_Absyn_Syntax.pos))
in (let c = (let _99_432 = (let _46_993 = config
in (let _99_431 = (no_eta config.steps)
in {code = body; environment = env; stack = (let _46_995 = config.stack
in {args = []}); close = _46_993.close; steps = _99_431}))
in (wne tcenv _99_432))
in (let _46_998 = c
in (let _99_433 = (mk_abs c.code)
in {code = _99_433; environment = _46_998.environment; stack = _46_998.stack; close = _46_998.close; steps = _46_998.steps}))))
end)))
end
| (formal::rest, actual::rest') -> begin
(let m = (match ((formal, actual)) with
| ((FStar_Util.Inl (a), _46_1010), ((FStar_Util.Inl (t), _46_1015), env)) -> begin
T ((a.FStar_Absyn_Syntax.v, (t, env)))
end
| ((FStar_Util.Inr (x), _46_1023), ((FStar_Util.Inr (v), _46_1028), env)) -> begin
V ((x.FStar_Absyn_Syntax.v, (v, env)))
end
| _46_1034 -> begin
(let _99_438 = (let _99_437 = (let _99_434 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _99_434))
in (let _99_436 = (FStar_Absyn_Print.binder_to_string formal)
in (let _99_435 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _99_437 _99_436 _99_435))))
in (FStar_All.failwith _99_438))
end)
in (beta ((m)::entries) rest rest'))
end))
in (beta [] binders config.stack.args))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(let c_e1 = (wne tcenv (let _46_1040 = config
in {code = e1; environment = _46_1040.environment; stack = empty_stack; close = _46_1040.close; steps = _46_1040.steps}))
in (let wn_eqn = (fun _46_1047 -> (match (_46_1047) with
| (pat, w, body) -> begin
(let rec pat_vars = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_disj (p::_46_1053) -> begin
(pat_vars p)
end
| FStar_Absyn_Syntax.Pat_cons (_46_1058, _46_1060, pats) -> begin
(FStar_List.collect (fun _46_1067 -> (match (_46_1067) with
| (x, _46_1066) -> begin
(pat_vars x)
end)) pats)
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
((FStar_Absyn_Syntax.v_binder x))::[]
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
((FStar_Absyn_Syntax.t_binder a))::[]
end
| (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_constant (_)) | (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
[]
end))
in (let vars = (pat_vars pat)
in (let norm_bvvar = (fun x -> (let t = (sn tcenv (t_config x.FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _46_1091 = x
in {FStar_Absyn_Syntax.v = _46_1091.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t.code; FStar_Absyn_Syntax.p = _46_1091.FStar_Absyn_Syntax.p})))
in (let norm_btvar = (fun a -> (let k = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _46_1096 = a
in {FStar_Absyn_Syntax.v = _46_1096.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k.code; FStar_Absyn_Syntax.p = _46_1096.FStar_Absyn_Syntax.p})))
in (let rec norm_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (pats) -> begin
(let _99_451 = (let _99_450 = (FStar_List.map norm_pat pats)
in FStar_Absyn_Syntax.Pat_disj (_99_450))
in (FStar_Absyn_Util.withinfo _99_451 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _99_456 = (let _99_455 = (let _99_454 = (FStar_List.map (fun _46_1109 -> (match (_46_1109) with
| (x, i) -> begin
(let _99_453 = (norm_pat x)
in (_99_453, i))
end)) pats)
in (fv, q, _99_454))
in FStar_Absyn_Syntax.Pat_cons (_99_455))
in (FStar_Absyn_Util.withinfo _99_456 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _99_458 = (let _99_457 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_var (_99_457))
in (FStar_Absyn_Util.withinfo _99_458 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _99_460 = (let _99_459 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_tvar (_99_459))
in (FStar_Absyn_Util.withinfo _99_460 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let _99_462 = (let _99_461 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_wild (_99_461))
in (FStar_Absyn_Util.withinfo _99_462 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let _99_464 = (let _99_463 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_twild (_99_463))
in (FStar_Absyn_Util.withinfo _99_464 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_constant (_46_1119) -> begin
p
end
| FStar_Absyn_Syntax.Pat_dot_term (x, e) -> begin
(let e = (wne tcenv (e_config e config.environment config.steps))
in (let _99_467 = (let _99_466 = (let _99_465 = (norm_bvvar x)
in (_99_465, e.code))
in FStar_Absyn_Syntax.Pat_dot_term (_99_466))
in (FStar_Absyn_Util.withinfo _99_467 None p.FStar_Absyn_Syntax.p)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (let _99_470 = (let _99_469 = (let _99_468 = (norm_btvar a)
in (_99_468, t.code))
in FStar_Absyn_Syntax.Pat_dot_typ (_99_469))
in (FStar_Absyn_Util.withinfo _99_470 None p.FStar_Absyn_Syntax.p)))
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
(let c_w = (wne tcenv (let _46_1144 = config
in {code = w; environment = env; stack = empty_stack; close = _46_1144.close; steps = _46_1144.steps}))
in Some (c_w.code))
end)
in (let c_body = (wne tcenv (let _46_1148 = config
in {code = body; environment = env; stack = empty_stack; close = _46_1148.close; steps = _46_1148.steps}))
in (let _99_473 = (norm_pat pat)
in (_99_473, w, c_body.code)))))))))))
end))
in (let eqns = (FStar_List.map wn_eqn eqns)
in (let e = (FStar_Absyn_Syntax.mk_Exp_match (c_e1.code, eqns) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (let _46_1153 = config
in {code = e; environment = _46_1153.environment; stack = _46_1153.stack; close = _46_1153.close; steps = _46_1153.steps}) rebuild)))))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), body) -> begin
(let _46_1185 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _46_1163 _46_1168 -> (match ((_46_1163, _46_1168)) with
| ((env, lbs), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = eff; FStar_Absyn_Syntax.lbdef = e}) -> begin
(let c = (wne tcenv (let _46_1169 = config
in {code = e; environment = _46_1169.environment; stack = empty_stack; close = _46_1169.close; steps = _46_1169.steps}))
in (let t = (sn tcenv (t_config t config.environment config.steps))
in (let _46_1182 = (match (x) with
| FStar_Util.Inl (x) -> begin
(let y = (let _99_476 = if is_rec then begin
x
end else begin
(FStar_Absyn_Util.freshen_bvd x)
end
in (FStar_Absyn_Util.bvd_to_bvar_s _99_476 t.code))
in (let yexp = (FStar_Absyn_Util.bvar_to_exp y)
in (let y_for_x = V ((x, (yexp, empty_env)))
in (FStar_Util.Inl (y.FStar_Absyn_Syntax.v), (extend_env' env y_for_x)))))
end
| _46_1179 -> begin
(x, env)
end)
in (match (_46_1182) with
| (y, env) -> begin
(env, ((FStar_Absyn_Syntax.mk_lb (y, eff, t.code, c.code)))::lbs)
end))))
end)) (config.environment, [])))
in (match (_46_1185) with
| (env, lbs) -> begin
(let lbs = (FStar_List.rev lbs)
in (let c_body = (wne tcenv (let _46_1187 = config
in {code = body; environment = env; stack = empty_stack; close = _46_1187.close; steps = _46_1187.steps}))
in (let e = (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), c_body.code) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (let _46_1191 = config
in {code = e; environment = _46_1191.environment; stack = _46_1191.stack; close = _46_1191.close; steps = _46_1191.steps}) rebuild))))
end))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, l) -> begin
(let c = (wne tcenv (let _46_1198 = config
in {code = e; environment = _46_1198.environment; stack = _46_1198.stack; close = _46_1198.close; steps = _46_1198.steps}))
in if (is_stack_empty config) then begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (let _99_478 = (let _46_1202 = config
in (let _99_477 = (FStar_Absyn_Syntax.mk_Exp_ascribed (c.code, t.code, l) None e.FStar_Absyn_Syntax.pos)
in {code = _99_477; environment = _46_1202.environment; stack = _46_1202.stack; close = _46_1202.close; steps = _46_1202.steps}))
in (rebuild _99_478)))
end else begin
c
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, info)) -> begin
(let c = (wne tcenv (let _46_1209 = config
in {code = e; environment = _46_1209.environment; stack = _46_1209.stack; close = _46_1209.close; steps = _46_1209.steps}))
in if (is_stack_empty config) then begin
(let _99_480 = (let _46_1212 = config
in (let _99_479 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((c.code, info))))
in {code = _99_479; environment = _46_1212.environment; stack = _46_1212.stack; close = _46_1212.close; steps = _46_1212.steps}))
in (rebuild _99_480))
end else begin
c
end)
end)))))

let norm_kind = (fun steps tcenv k -> (let c = (snk tcenv (k_config k empty_env steps))
in (FStar_Absyn_Util.compress_kind c.code)))

let norm_typ = (fun steps tcenv t -> (let c = (sn tcenv (t_config t empty_env steps))
in c.code))

let norm_exp = (fun steps tcenv e -> (let c = (wne tcenv (e_config e empty_env steps))
in c.code))

let norm_sigelt = (fun tcenv _46_10 -> (match (_46_10) with
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, b) -> begin
(let e = (let _99_504 = (let _99_503 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None r)
in (lbs, _99_503))
in (FStar_Absyn_Syntax.mk_Exp_let _99_504 None r))
in (let e = (norm_exp ((Beta)::[]) tcenv e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_let (lbs, _46_1238) -> begin
FStar_Absyn_Syntax.Sig_let ((lbs, r, l, b))
end
| _46_1242 -> begin
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
(let _99_509 = (eta_expand tcenv t)
in (FStar_All.pipe_right _99_509 FStar_Absyn_Util.compress_typ))
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

let exp_norm_to_string = (fun tcenv e -> (let _99_532 = (norm_exp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv e)
in (FStar_Absyn_Print.exp_to_string _99_532)))

let typ_norm_to_string = (fun tcenv t -> (let _99_537 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv t)
in (FStar_Absyn_Print.typ_to_string _99_537)))

let kind_norm_to_string = (fun tcenv k -> (let _99_542 = (norm_kind ((Beta)::(SNComp)::(Unmeta)::[]) tcenv k)
in (FStar_Absyn_Print.kind_to_string _99_542)))

let formula_norm_to_string = (fun tcenv f -> (let _99_547 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv f)
in (FStar_Absyn_Print.formula_to_string _99_547)))

let comp_typ_norm_to_string = (fun tcenv c -> (let _99_552 = (norm_comp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv c)
in (FStar_Absyn_Print.comp_typ_to_string _99_552)))

let normalize_refinement = (fun steps env t0 -> (let t = (norm_typ (FStar_List.append ((Beta)::(WHNF)::(DeltaHard)::[]) steps) env t0)
in (let rec aux = (fun t -> (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(let t0 = (aux x.FStar_Absyn_Syntax.sort)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (y, phi1) -> begin
(let _99_567 = (let _99_566 = (let _99_565 = (let _99_564 = (let _99_563 = (let _99_562 = (let _99_561 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _99_561))
in FStar_Util.Inr (_99_562))
in (_99_563)::[])
in (FStar_Absyn_Util.subst_typ _99_564 phi))
in (FStar_Absyn_Util.mk_conj phi1 _99_565))
in (y, _99_566))
in (FStar_Absyn_Syntax.mk_Typ_refine _99_567 (Some (FStar_Absyn_Syntax.ktype)) t0.FStar_Absyn_Syntax.pos))
end
| _46_1351 -> begin
t
end))
end
| _46_1353 -> begin
t
end)))
in (aux t))))




