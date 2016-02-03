
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
| T (_48_26) -> begin
_48_26
end))

let ___V____0 = (fun projectee -> (match (projectee) with
| V (_48_29) -> begin
_48_29
end))

let empty_env = {context = []; label_suffix = []}

let extend_env' = (fun env b -> (let _48_32 = env
in {context = (b)::env.context; label_suffix = _48_32.label_suffix}))

let extend_env = (fun env bindings -> (let _48_36 = env
in {context = (FStar_List.append bindings env.context); label_suffix = _48_36.label_suffix}))

let lookup_env = (fun env key -> (FStar_All.pipe_right env.context (FStar_Util.find_opt (fun _48_1 -> (match (_48_1) with
| T (a, _48_43) -> begin
(a.FStar_Absyn_Syntax.realname.FStar_Ident.idText = key)
end
| V (x, _48_48) -> begin
(x.FStar_Absyn_Syntax.realname.FStar_Ident.idText = key)
end)))))

let fold_env = (fun env f acc -> (FStar_List.fold_left (fun acc v -> (match (v) with
| T (a, _48_58) -> begin
(f a.FStar_Absyn_Syntax.realname.FStar_Ident.idText v acc)
end
| V (x, _48_63) -> begin
(f x.FStar_Absyn_Syntax.realname.FStar_Ident.idText v acc)
end)) acc env.context))

let empty_stack = {args = []}

let rec subst_of_env' = (fun env -> (fold_env env (fun _48_67 v acc -> (match (v) with
| T (a, (t, env')) -> begin
(let _139_113 = (let _139_112 = (let _139_111 = (let _139_110 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_typ _139_110 t))
in (a, _139_111))
in FStar_Util.Inl (_139_112))
in (_139_113)::acc)
end
| V (x, (v, env')) -> begin
(let _139_117 = (let _139_116 = (let _139_115 = (let _139_114 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_exp _139_114 v))
in (x, _139_115))
in FStar_Util.Inr (_139_116))
in (_139_117)::acc)
end)) []))

let subst_of_env = (fun tcenv env -> (subst_of_env' env))

let with_new_code = (fun c e -> {code = e; environment = c.environment; stack = empty_stack; close = None; steps = c.steps})

let rec eta_expand = (fun tcenv t -> (let k = (let _139_127 = (FStar_Tc_Recheck.recompute_kind t)
in (FStar_All.pipe_right _139_127 FStar_Absyn_Util.compress_kind))
in (let rec aux = (fun t k -> (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
t
end
| FStar_Absyn_Syntax.Kind_abbrev (_48_99, k) -> begin
(aux t k)
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k') -> begin
(match ((let _139_132 = (FStar_Absyn_Util.unascribe_typ t)
in _139_132.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam (real, body) -> begin
(let rec aux = (fun real expected -> (match ((real, expected)) with
| (_48_116::real, _48_120::expected) -> begin
(aux real expected)
end
| ([], []) -> begin
t
end
| (_48_129::_48_127, []) -> begin
(FStar_All.failwith "Ill-kinded type")
end
| ([], more) -> begin
(let _48_138 = (FStar_Absyn_Util.args_of_binders more)
in (match (_48_138) with
| (more, args) -> begin
(let body = (FStar_Absyn_Syntax.mk_Typ_app (body, args) None body.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_lam ((FStar_List.append binders more), body) None body.FStar_Absyn_Syntax.pos))
end))
end))
in (aux real binders))
end
| _48_141 -> begin
(let _48_144 = (FStar_Absyn_Util.args_of_binders binders)
in (match (_48_144) with
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
(let _139_140 = (let _139_139 = (let _139_137 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _139_137 FStar_Range.string_of_range))
in (let _139_138 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "%s: Impossible: Kind_unknown: %s" _139_139 _139_138)))
in (FStar_All.failwith _139_140))
end))
in (aux t k))))

let is_var = (fun t -> (match ((FStar_Absyn_Util.compress_typ t)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (_48_163); FStar_Absyn_Syntax.tk = _48_161; FStar_Absyn_Syntax.pos = _48_159; FStar_Absyn_Syntax.fvs = _48_157; FStar_Absyn_Syntax.uvs = _48_155} -> begin
true
end
| _48_167 -> begin
false
end))

let rec eta_expand_exp = (fun tcenv e -> (let t = (let _139_147 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_All.pipe_right _139_147 FStar_Absyn_Util.compress_typ))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((let _139_148 = (FStar_Absyn_Util.compress_exp e)
in _139_148.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
if ((FStar_List.length bs) = (FStar_List.length bs')) then begin
e
end else begin
(FStar_All.failwith "NYI")
end
end
| _48_180 -> begin
(let _48_183 = (FStar_Absyn_Util.args_of_binders bs)
in (match (_48_183) with
| (bs, args) -> begin
(let _139_150 = (let _139_149 = (FStar_Absyn_Syntax.mk_Exp_app (e, args) None e.FStar_Absyn_Syntax.pos)
in (bs, _139_149))
in (FStar_Absyn_Syntax.mk_Exp_abs _139_150 (Some (t)) e.FStar_Absyn_Syntax.pos))
end))
end)
end
| _48_185 -> begin
e
end)))

let no_eta = (fun s -> (FStar_All.pipe_right s (FStar_List.filter (fun _48_2 -> (match (_48_2) with
| Eta -> begin
false
end
| _48_190 -> begin
true
end)))))

let no_eta_cfg = (fun c -> (let _48_192 = c
in (let _139_155 = (no_eta c.steps)
in {code = _48_192.code; environment = _48_192.environment; stack = _48_192.stack; close = _48_192.close; steps = _139_155})))

let whnf_only = (fun config -> (FStar_All.pipe_right config.steps (FStar_List.contains WHNF)))

let unmeta = (fun config -> (FStar_All.pipe_right config.steps (FStar_List.contains Unmeta)))

let unlabel = (fun config -> ((unmeta config) || (FStar_All.pipe_right config.steps (FStar_List.contains Unlabel))))

let is_stack_empty = (fun config -> (match (config.stack.args) with
| [] -> begin
true
end
| _48_200 -> begin
false
end))

let has_eta = (fun cfg -> (FStar_All.pipe_right cfg.steps (FStar_List.contains Eta)))

let rec weak_norm_comp = (fun env comp -> (let c = (FStar_Absyn_Util.comp_to_comp_typ comp)
in (match ((FStar_Tc_Env.lookup_effect_abbrev env c.FStar_Absyn_Syntax.effect_name)) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(let binders' = (FStar_List.map (fun _48_3 -> (match (_48_3) with
| (FStar_Util.Inl (b), imp) -> begin
(let _139_167 = (let _139_166 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inl (_139_166))
in (_139_167, imp))
end
| (FStar_Util.Inr (b), imp) -> begin
(let _139_169 = (let _139_168 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inr (_139_168))
in (_139_169, imp))
end)) binders)
in (let subst = (let _139_171 = (let _139_170 = (FStar_Absyn_Util.args_of_binders binders')
in (FStar_All.pipe_right _139_170 Prims.snd))
in (FStar_Absyn_Util.subst_of_list binders _139_171))
in (let cdef = (FStar_Absyn_Util.subst_comp subst cdef)
in (let subst = (FStar_Absyn_Util.subst_of_list binders' (((FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ))::c.FStar_Absyn_Syntax.effect_args))
in (let c1 = (FStar_Absyn_Util.subst_comp subst cdef)
in (let c = (FStar_All.pipe_right (let _48_224 = (FStar_Absyn_Util.comp_to_comp_typ c1)
in {FStar_Absyn_Syntax.effect_name = _48_224.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _48_224.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _48_224.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = c.FStar_Absyn_Syntax.flags}) FStar_Absyn_Syntax.mk_Comp)
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

let rec is_head_symbol = (fun t -> (match ((let _139_202 = (FStar_Absyn_Util.compress_typ t)
in _139_202.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _48_255, _48_257)) -> begin
(is_head_symbol t)
end
| _48_262 -> begin
false
end))

let simplify_then_apply = (fun steps head args pos -> (let fallback = (fun _48_268 -> (match (()) with
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
| _48_276 -> begin
None
end))
in (let simplify = (fun arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (t) -> begin
((simp_t t), arg)
end
| _48_282 -> begin
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
| _48_329 -> begin
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
| _48_374 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
FStar_Absyn_Util.t_true
end
| (Some (true), _48_402)::(_48_392, (FStar_Util.Inl (arg), _48_396))::[] -> begin
arg
end
| _48_406 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (Some (true), _48_410)::[] -> begin
FStar_Absyn_Util.t_false
end
| (Some (false), _48_416)::[] -> begin
FStar_Absyn_Util.t_true
end
| _48_420 -> begin
(fallback ())
end)
end else begin
if ((((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.forall_lid) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid)) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exists_lid)) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) then begin
(match (args) with
| ((FStar_Util.Inl (t), _)::[]) | (_::(FStar_Util.Inl (t), _)::[]) -> begin
(match ((let _139_217 = (FStar_Absyn_Util.compress_typ t)
in _139_217.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam (_48_435::[], body) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
FStar_Absyn_Util.t_true
end
| Some (false) -> begin
FStar_Absyn_Util.t_false
end
| _48_445 -> begin
(fallback ())
end)
end
| _48_447 -> begin
(fallback ())
end)
end
| _48_449 -> begin
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
| _48_451 -> begin
(fallback ())
end)
end))))

let rec sn_delay = (fun tcenv cfg -> (let aux = (fun _48_455 -> (match (()) with
| () -> begin
(let _139_243 = (sn tcenv cfg)
in _139_243.code)
end))
in (let t = (FStar_Absyn_Syntax.mk_Typ_delayed' (FStar_Util.Inr (aux)) None cfg.code.FStar_Absyn_Syntax.pos)
in (let _48_457 = cfg
in {code = t; environment = _48_457.environment; stack = empty_stack; close = _48_457.close; steps = _48_457.steps}))))
and sn = (fun tcenv cfg -> (let rebuild = (fun config -> (let rebuild_stack = (fun config -> if (is_stack_empty config) then begin
config
end else begin
(let s' = if (FStar_List.contains EtaArgs config.steps) then begin
config.steps
end else begin
(no_eta config.steps)
end
in (let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _48_4 -> (match (_48_4) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _139_255 = (let _139_254 = (let _139_253 = (sn tcenv (t_config t env s'))
in _139_253.code)
in (FStar_All.pipe_left (fun _139_252 -> FStar_Util.Inl (_139_252)) _139_254))
in (_139_255, imp))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _139_259 = (let _139_258 = (let _139_257 = (wne tcenv (e_config v env s'))
in _139_257.code)
in (FStar_All.pipe_left (fun _139_256 -> FStar_Util.Inr (_139_256)) _139_258))
in (_139_259, imp))
end))))
in (let t = (simplify_then_apply config.steps config.code args config.code.FStar_Absyn_Syntax.pos)
in (let _48_481 = config
in {code = t; environment = _48_481.environment; stack = empty_stack; close = _48_481.close; steps = _48_481.steps}))))
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
(let _48_488 = config
in (let _139_261 = (eta_expand tcenv t)
in {code = _139_261; environment = _48_488.environment; stack = _48_488.stack; close = _48_488.close; steps = _48_488.steps}))
end else begin
(let _48_490 = config
in {code = t; environment = _48_490.environment; stack = _48_490.stack; close = _48_490.close; steps = _48_490.steps})
end))))
in (let wk = (fun f -> (match ((FStar_ST.read cfg.code.FStar_Absyn_Syntax.tk)) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _48_501; FStar_Absyn_Syntax.pos = _48_499; FStar_Absyn_Syntax.fvs = _48_497; FStar_Absyn_Syntax.uvs = _48_495}) -> begin
(f (Some (FStar_Absyn_Syntax.ktype)) cfg.code.FStar_Absyn_Syntax.pos)
end
| _48_506 -> begin
(f None cfg.code.FStar_Absyn_Syntax.pos)
end))
in (let config = (let _48_507 = cfg
in (let _139_274 = (FStar_Absyn_Util.compress_typ cfg.code)
in {code = _139_274; environment = _48_507.environment; stack = _48_507.stack; close = _48_507.close; steps = _48_507.steps}))
in (match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_48_511) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_uvar (_48_514) -> begin
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
(sn tcenv (let _48_522 = config
in {code = t; environment = _48_522.environment; stack = _48_522.stack; close = _48_522.close; steps = _48_522.steps}))
end))
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(match ((lookup_env config.environment a.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname.FStar_Ident.idText)) with
| None -> begin
(rebuild config)
end
| Some (T (_48_528, (t, e))) -> begin
(sn tcenv (let _48_535 = config
in {code = t; environment = e; stack = _48_535.stack; close = _48_535.close; steps = _48_535.steps}))
end
| _48_538 -> begin
(FStar_All.failwith "Impossible: expected a type")
end)
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let args = (FStar_List.fold_right (fun a out -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _48_546 = config.stack
in {args = args})
in (sn tcenv (let _48_549 = config
in {code = head; environment = _48_549.environment; stack = stack; close = _48_549.close; steps = _48_549.steps}))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(match (config.stack.args) with
| [] -> begin
(let _48_558 = (sn_binders tcenv binders config.environment config.steps)
in (match (_48_558) with
| (binders, environment) -> begin
(let mk_lam = (fun t -> (let lam = (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_lam (binders, t)))
in (match (cfg.close) with
| None -> begin
lam
end
| Some (f) -> begin
(f lam)
end)))
in (let t2_cfg = (let _139_287 = (let _139_286 = (no_eta config.steps)
in {code = t2; environment = environment; stack = empty_stack; close = None; steps = _139_286})
in (sn_delay tcenv _139_287))
in (let _48_566 = t2_cfg
in (let _139_288 = (mk_lam t2_cfg.code)
in {code = _139_288; environment = _48_566.environment; stack = _48_566.stack; close = _48_566.close; steps = _48_566.steps}))))
end))
end
| args -> begin
(let rec beta = (fun env_entries binders args -> (match ((binders, args)) with
| ([], _48_575) -> begin
(let env = (extend_env config.environment env_entries)
in (sn tcenv (let _48_578 = config
in {code = t2; environment = env; stack = (let _48_580 = config.stack
in {args = args}); close = _48_578.close; steps = _48_578.steps})))
end
| (_48_583, []) -> begin
(let t = (FStar_Absyn_Syntax.mk_Typ_lam (binders, t2) None t2.FStar_Absyn_Syntax.pos)
in (let env = (extend_env config.environment env_entries)
in (sn tcenv (let _48_588 = config
in {code = t; environment = env; stack = empty_stack; close = _48_588.close; steps = _48_588.steps}))))
end
| (formal::rest, actual::rest') -> begin
(let m = (match ((formal, actual)) with
| ((FStar_Util.Inl (a), _48_600), ((FStar_Util.Inl (t), _48_605), env)) -> begin
T ((a.FStar_Absyn_Syntax.v, (t, env)))
end
| ((FStar_Util.Inr (x), _48_613), ((FStar_Util.Inr (v), _48_618), env)) -> begin
V ((x.FStar_Absyn_Syntax.v, (v, env)))
end
| _48_624 -> begin
(let _139_299 = (let _139_298 = (let _139_295 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _139_295))
in (let _139_297 = (FStar_Absyn_Print.binder_to_string formal)
in (let _139_296 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _139_298 _139_297 _139_296))))
in (FStar_All.failwith _139_299))
end)
in (beta ((m)::env_entries) rest rest'))
end))
in (beta [] binders args))
end)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _48_628) -> begin
(sn tcenv (let _48_631 = config
in {code = t; environment = _48_631.environment; stack = _48_631.stack; close = _48_631.close; steps = _48_631.steps}))
end
| _48_634 -> begin
(match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, comp) -> begin
(let _48_641 = (sn_binders tcenv bs config.environment config.steps)
in (match (_48_641) with
| (binders, environment) -> begin
(let c2 = (sncomp tcenv (c_config comp environment config.steps))
in (let _139_303 = (let _48_643 = config
in (let _139_302 = (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_fun (binders, c2.code)))
in {code = _139_302; environment = _48_643.environment; stack = _48_643.stack; close = _48_643.close; steps = _48_643.steps}))
in (rebuild _139_303)))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((sn_binders tcenv (((FStar_Absyn_Syntax.v_binder x))::[]) config.environment config.steps)) with
| ((FStar_Util.Inr (x), _48_652)::[], env) -> begin
(let refine = (fun t -> (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_refine (x, t))))
in (let _139_310 = (let _139_309 = (FStar_All.pipe_right config.steps (FStar_List.filter (fun _48_5 -> (match (_48_5) with
| UnfoldOpaque -> begin
false
end
| _48_662 -> begin
true
end))))
in {code = t; environment = env; stack = empty_stack; close = (close_with_config config refine); steps = _139_309})
in (sn tcenv _139_310)))
end
| _48_664 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
if (unmeta config) then begin
(sn tcenv (let _48_670 = config
in {code = t; environment = _48_670.environment; stack = _48_670.stack; close = _48_670.close; steps = _48_670.steps}))
end else begin
(let pat = (fun t -> (let ps = (FStar_All.pipe_right ps (FStar_List.map (sn_args true tcenv config.environment config.steps)))
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern ((t, ps)))))))
in (sn tcenv (let _48_675 = config
in {code = t; environment = _48_675.environment; stack = _48_675.stack; close = (close_with_config config pat); steps = _48_675.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, b)) -> begin
if (unlabel config) then begin
(sn tcenv (let _48_684 = config
in {code = t; environment = _48_684.environment; stack = _48_684.stack; close = _48_684.close; steps = _48_684.steps}))
end else begin
(let lab = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when ((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) && (FStar_All.pipe_right config.steps (FStar_List.contains Simplify))) -> begin
t
end
| _48_691 -> begin
(match (config.environment.label_suffix) with
| (b', sfx)::_48_693 -> begin
if ((b' = None) || (Some (b) = b')) then begin
(let _48_698 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _139_317 = (FStar_Range.string_of_range sfx)
in (FStar_Util.print2 "Stripping label %s because of enclosing refresh %s\n" l _139_317))
end else begin
()
end
in t)
end else begin
(let _48_700 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _139_318 = (FStar_Range.string_of_range sfx)
in (FStar_Util.print1 "Normalizer refreshing label: %s\n" _139_318))
end else begin
()
end
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, sfx, b))))))
end
end
| _48_703 -> begin
(FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b)))))
end)
end))
in (sn tcenv (let _48_704 = config
in {code = t; environment = _48_704.environment; stack = _48_704.stack; close = (close_with_config config lab); steps = _48_704.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
if (unmeta config) then begin
(sn tcenv (let _48_712 = config
in {code = t; environment = _48_712.environment; stack = _48_712.stack; close = _48_712.close; steps = _48_712.steps}))
end else begin
(let sfx = (match (b) with
| Some (false) -> begin
r
end
| _48_717 -> begin
FStar_Absyn_Syntax.dummyRange
end)
in (let config = (let _48_719 = config
in {code = t; environment = (let _48_721 = config.environment
in {context = _48_721.context; label_suffix = ((b, sfx))::config.environment.label_suffix}); stack = _48_719.stack; close = _48_719.close; steps = _48_719.steps})
in (sn tcenv config)))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
if (FStar_ST.read flag) then begin
(let _139_324 = (let _48_730 = config
in (let _139_323 = (FStar_Absyn_Util.mk_conj t1 t2)
in {code = _139_323; environment = _48_730.environment; stack = _48_730.stack; close = _48_730.close; steps = _48_730.steps}))
in (sn tcenv _139_324))
end else begin
(let c1 = (sn tcenv (t_config t1 config.environment config.steps))
in (let c2 = (sn tcenv (t_config t2 config.environment config.steps))
in (let _139_326 = (let _48_734 = config
in (let _139_325 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula ((c1.code, c2.code, flag))))
in {code = _139_325; environment = _48_734.environment; stack = _48_734.stack; close = _48_734.close; steps = _48_734.steps}))
in (rebuild _139_326))))
end
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_))) | (FStar_Absyn_Syntax.Typ_unknown) | (_) -> begin
(let _139_331 = (let _139_330 = (let _139_327 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _139_327 FStar_Range.string_of_range))
in (let _139_329 = (FStar_Absyn_Print.tag_of_typ config.code)
in (let _139_328 = (FStar_Absyn_Print.typ_to_string config.code)
in (FStar_Util.format3 "(%s) Unexpected type (%s): %s" _139_330 _139_329 _139_328))))
in (FStar_All.failwith _139_331))
end)
end)))))
and sn_binders = (fun tcenv binders env steps -> (let rec aux = (fun out env _48_6 -> (match (_48_6) with
| (FStar_Util.Inl (a), imp)::rest -> begin
(let c = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort env steps))
in (let b = (let _139_342 = (FStar_Absyn_Util.freshen_bvd a.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _139_342 c.code))
in (let btyp = (FStar_Absyn_Util.btvar_to_typ b)
in (let b_for_a = T ((a.FStar_Absyn_Syntax.v, (btyp, empty_env)))
in (aux (((FStar_Util.Inl (b), imp))::out) (extend_env' env b_for_a) rest)))))
end
| (FStar_Util.Inr (x), imp)::rest -> begin
(let c = (sn_delay tcenv (t_config x.FStar_Absyn_Syntax.sort env steps))
in (let y = (let _139_343 = (FStar_Absyn_Util.freshen_bvd x.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _139_343 c.code))
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
in (let _48_778 = cfg
in (let _139_346 = (FStar_Absyn_Syntax.mk_Comp ctconf.code)
in {code = _139_346; environment = _48_778.environment; stack = _48_778.stack; close = _48_778.close; steps = _48_778.steps})))
end
| FStar_Absyn_Syntax.Total (t) -> begin
if (FStar_List.contains DeltaComp cfg.steps) then begin
(let _139_350 = (let _139_349 = (let _139_348 = (let _139_347 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_Absyn_Util.comp_to_comp_typ _139_347))
in (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp _139_348))
in (with_new_code cfg _139_349))
in (FStar_All.pipe_left (sncomp tcenv) _139_350))
end else begin
(let t = (sn tcenv (with_new_code cfg t))
in (let _139_351 = (FStar_Absyn_Syntax.mk_Total t.code)
in (with_new_code cfg _139_351)))
end
end)))
and sncomp_typ = (fun tcenv cfg -> (let m = cfg.code
in (let norm = (fun _48_787 -> (match (()) with
| () -> begin
(let remake = (fun l r eargs flags -> (let c = {FStar_Absyn_Syntax.effect_name = l; FStar_Absyn_Syntax.result_typ = r; FStar_Absyn_Syntax.effect_args = eargs; FStar_Absyn_Syntax.flags = flags}
in (let _48_794 = cfg
in {code = c; environment = _48_794.environment; stack = _48_794.stack; close = _48_794.close; steps = _48_794.steps})))
in (let res = (let _139_364 = (sn tcenv (with_new_code cfg m.FStar_Absyn_Syntax.result_typ))
in _139_364.code)
in (let sn_flags = (fun flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _48_7 -> (match (_48_7) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let e = (let _139_368 = (wne tcenv (e_config e cfg.environment cfg.steps))
in _139_368.code)
in FStar_Absyn_Syntax.DECREASES (e))
end
| f -> begin
f
end)))))
in (let _48_806 = (let _139_370 = (sn_flags m.FStar_Absyn_Syntax.flags)
in (let _139_369 = (sn_args true tcenv cfg.environment cfg.steps m.FStar_Absyn_Syntax.effect_args)
in (_139_370, _139_369)))
in (match (_48_806) with
| (flags, args) -> begin
(remake m.FStar_Absyn_Syntax.effect_name res args flags)
end)))))
end))
in if (FStar_List.contains DeltaComp cfg.steps) then begin
(match ((FStar_Tc_Env.lookup_effect_abbrev tcenv m.FStar_Absyn_Syntax.effect_name)) with
| Some (_48_808) -> begin
(let c = (let _139_371 = (FStar_Absyn_Syntax.mk_Comp m)
in (weak_norm_comp tcenv _139_371))
in (sncomp_typ tcenv (let _48_811 = cfg
in {code = c; environment = _48_811.environment; stack = _48_811.stack; close = _48_811.close; steps = _48_811.steps})))
end
| _48_814 -> begin
(norm ())
end)
end else begin
(norm ())
end)))
and sn_args = (fun delay tcenv env steps args -> (FStar_All.pipe_right args (FStar_List.map (fun _48_8 -> (match (_48_8) with
| (FStar_Util.Inl (t), imp) when delay -> begin
(let _139_381 = (let _139_380 = (let _139_379 = (sn_delay tcenv (t_config t env steps))
in _139_379.code)
in (FStar_All.pipe_left (fun _139_378 -> FStar_Util.Inl (_139_378)) _139_380))
in (_139_381, imp))
end
| (FStar_Util.Inl (t), imp) -> begin
(let _139_385 = (let _139_384 = (let _139_383 = (sn tcenv (t_config t env steps))
in _139_383.code)
in (FStar_All.pipe_left (fun _139_382 -> FStar_Util.Inl (_139_382)) _139_384))
in (_139_385, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _139_389 = (let _139_388 = (let _139_387 = (wne tcenv (e_config e env steps))
in _139_387.code)
in (FStar_All.pipe_left (fun _139_386 -> FStar_Util.Inr (_139_386)) _139_388))
in (_139_389, imp))
end)))))
and snk = (fun tcenv cfg -> (let w = (fun f -> (f cfg.code.FStar_Absyn_Syntax.pos))
in (match ((let _139_399 = (FStar_Absyn_Util.compress_kind cfg.code)
in _139_399.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Kind_delayed (_)) | (FStar_Absyn_Syntax.Kind_lam (_)) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
cfg
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(let args = (let _139_400 = (no_eta cfg.steps)
in (sn_args false tcenv cfg.environment _139_400 args))
in (let _48_850 = cfg
in (let _139_402 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar (uv, args)))
in {code = _139_402; environment = _48_850.environment; stack = _48_850.stack; close = _48_850.close; steps = _48_850.steps})))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _48_862; FStar_Absyn_Syntax.pos = _48_860; FStar_Absyn_Syntax.fvs = _48_858; FStar_Absyn_Syntax.uvs = _48_856}) -> begin
(let _48_871 = (FStar_Tc_Env.lookup_kind_abbrev tcenv l)
in (match (_48_871) with
| (_48_868, binders, body) -> begin
(let subst = (FStar_Absyn_Util.subst_of_list binders args)
in (let _139_404 = (let _48_873 = cfg
in (let _139_403 = (FStar_Absyn_Util.subst_kind subst body)
in {code = _139_403; environment = _48_873.environment; stack = _48_873.stack; close = _48_873.close; steps = _48_873.steps}))
in (snk tcenv _139_404)))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_48_876, k) -> begin
(snk tcenv (let _48_880 = cfg
in {code = k; environment = _48_880.environment; stack = _48_880.stack; close = _48_880.close; steps = _48_880.steps}))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _48_888 = (sn_binders tcenv bs cfg.environment cfg.steps)
in (match (_48_888) with
| (bs, env) -> begin
(let c2 = (snk tcenv (k_config k env cfg.steps))
in (let _48_898 = (match (c2.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs', k) -> begin
((FStar_List.append bs bs'), k)
end
| _48_895 -> begin
(bs, c2.code)
end)
in (match (_48_898) with
| (bs, rhs) -> begin
(let _48_899 = cfg
in (let _139_406 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (bs, rhs)))
in {code = _139_406; environment = _48_899.environment; stack = _48_899.stack; close = _48_899.close; steps = _48_899.steps}))
end)))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(FStar_All.failwith "Impossible")
end)))
and wne = (fun tcenv cfg -> (let e = (FStar_Absyn_Util.compress_exp cfg.code)
in (let config = (let _48_905 = cfg
in {code = e; environment = _48_905.environment; stack = _48_905.stack; close = _48_905.close; steps = _48_905.steps})
in (let rebuild = (fun config -> if (is_stack_empty config) then begin
config
end else begin
(let s' = if (FStar_List.contains EtaArgs config.steps) then begin
config.steps
end else begin
(no_eta config.steps)
end
in (let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _48_9 -> (match (_48_9) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _139_415 = (let _139_414 = (let _139_413 = (sn tcenv (t_config t env s'))
in _139_413.code)
in (FStar_All.pipe_left (fun _139_412 -> FStar_Util.Inl (_139_412)) _139_414))
in (_139_415, imp))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _139_419 = (let _139_418 = (let _139_417 = (wne tcenv (e_config v env s'))
in _139_417.code)
in (FStar_All.pipe_left (fun _139_416 -> FStar_Util.Inr (_139_416)) _139_418))
in (_139_419, imp))
end))))
in (let _48_925 = config
in (let _139_420 = (FStar_Absyn_Syntax.mk_Exp_app (config.code, args) None config.code.FStar_Absyn_Syntax.pos)
in {code = _139_420; environment = _48_925.environment; stack = empty_stack; close = _48_925.close; steps = _48_925.steps}))))
end)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_48_928) -> begin
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
| Some (V (_48_943, (vc, env))) -> begin
(wne tcenv (let _48_950 = config
in {code = vc; environment = env; stack = _48_950.stack; close = _48_950.close; steps = _48_950.steps}))
end
| _48_953 -> begin
(FStar_All.failwith "Impossible: ill-typed term")
end)
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let args = (FStar_List.fold_right (fun a out -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _48_961 = config.stack
in {args = args})
in (wne tcenv (let _48_964 = config
in {code = head; environment = _48_964.environment; stack = stack; close = _48_964.close; steps = _48_964.steps}))))
end
| FStar_Absyn_Syntax.Exp_abs (binders, body) -> begin
(let rec beta = (fun entries binders args -> (match ((binders, args)) with
| ([], _48_976) -> begin
(let env = (extend_env config.environment entries)
in (wne tcenv (let _48_979 = config
in {code = body; environment = env; stack = (let _48_981 = config.stack
in {args = args}); close = _48_979.close; steps = _48_979.steps})))
end
| (_48_984, []) -> begin
(let env = (extend_env config.environment entries)
in (let _48_990 = (sn_binders tcenv binders env config.steps)
in (match (_48_990) with
| (binders, env) -> begin
(let mk_abs = (fun t -> (FStar_Absyn_Syntax.mk_Exp_abs (binders, t) None body.FStar_Absyn_Syntax.pos))
in (let c = (let _139_432 = (let _48_993 = config
in (let _139_431 = (no_eta config.steps)
in {code = body; environment = env; stack = (let _48_995 = config.stack
in {args = []}); close = _48_993.close; steps = _139_431}))
in (wne tcenv _139_432))
in (let _48_998 = c
in (let _139_433 = (mk_abs c.code)
in {code = _139_433; environment = _48_998.environment; stack = _48_998.stack; close = _48_998.close; steps = _48_998.steps}))))
end)))
end
| (formal::rest, actual::rest') -> begin
(let m = (match ((formal, actual)) with
| ((FStar_Util.Inl (a), _48_1010), ((FStar_Util.Inl (t), _48_1015), env)) -> begin
T ((a.FStar_Absyn_Syntax.v, (t, env)))
end
| ((FStar_Util.Inr (x), _48_1023), ((FStar_Util.Inr (v), _48_1028), env)) -> begin
V ((x.FStar_Absyn_Syntax.v, (v, env)))
end
| _48_1034 -> begin
(let _139_438 = (let _139_437 = (let _139_434 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _139_434))
in (let _139_436 = (FStar_Absyn_Print.binder_to_string formal)
in (let _139_435 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _139_437 _139_436 _139_435))))
in (FStar_All.failwith _139_438))
end)
in (beta ((m)::entries) rest rest'))
end))
in (beta [] binders config.stack.args))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(let c_e1 = (wne tcenv (let _48_1040 = config
in {code = e1; environment = _48_1040.environment; stack = empty_stack; close = _48_1040.close; steps = _48_1040.steps}))
in (let wn_eqn = (fun _48_1047 -> (match (_48_1047) with
| (pat, w, body) -> begin
(let rec pat_vars = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_disj (p::_48_1053) -> begin
(pat_vars p)
end
| FStar_Absyn_Syntax.Pat_cons (_48_1058, _48_1060, pats) -> begin
(FStar_List.collect (fun _48_1067 -> (match (_48_1067) with
| (x, _48_1066) -> begin
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
in (let _48_1091 = x
in {FStar_Absyn_Syntax.v = _48_1091.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t.code; FStar_Absyn_Syntax.p = _48_1091.FStar_Absyn_Syntax.p})))
in (let norm_btvar = (fun a -> (let k = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _48_1096 = a
in {FStar_Absyn_Syntax.v = _48_1096.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k.code; FStar_Absyn_Syntax.p = _48_1096.FStar_Absyn_Syntax.p})))
in (let rec norm_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (pats) -> begin
(let _139_451 = (let _139_450 = (FStar_List.map norm_pat pats)
in FStar_Absyn_Syntax.Pat_disj (_139_450))
in (FStar_Absyn_Util.withinfo _139_451 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _139_456 = (let _139_455 = (let _139_454 = (FStar_List.map (fun _48_1109 -> (match (_48_1109) with
| (x, i) -> begin
(let _139_453 = (norm_pat x)
in (_139_453, i))
end)) pats)
in (fv, q, _139_454))
in FStar_Absyn_Syntax.Pat_cons (_139_455))
in (FStar_Absyn_Util.withinfo _139_456 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _139_458 = (let _139_457 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_var (_139_457))
in (FStar_Absyn_Util.withinfo _139_458 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _139_460 = (let _139_459 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_tvar (_139_459))
in (FStar_Absyn_Util.withinfo _139_460 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let _139_462 = (let _139_461 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_wild (_139_461))
in (FStar_Absyn_Util.withinfo _139_462 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let _139_464 = (let _139_463 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_twild (_139_463))
in (FStar_Absyn_Util.withinfo _139_464 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_constant (_48_1119) -> begin
p
end
| FStar_Absyn_Syntax.Pat_dot_term (x, e) -> begin
(let e = (wne tcenv (e_config e config.environment config.steps))
in (let _139_467 = (let _139_466 = (let _139_465 = (norm_bvvar x)
in (_139_465, e.code))
in FStar_Absyn_Syntax.Pat_dot_term (_139_466))
in (FStar_Absyn_Util.withinfo _139_467 None p.FStar_Absyn_Syntax.p)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (let _139_470 = (let _139_469 = (let _139_468 = (norm_btvar a)
in (_139_468, t.code))
in FStar_Absyn_Syntax.Pat_dot_typ (_139_469))
in (FStar_Absyn_Util.withinfo _139_470 None p.FStar_Absyn_Syntax.p)))
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
(let c_w = (wne tcenv (let _48_1144 = config
in {code = w; environment = env; stack = empty_stack; close = _48_1144.close; steps = _48_1144.steps}))
in Some (c_w.code))
end)
in (let c_body = (wne tcenv (let _48_1148 = config
in {code = body; environment = env; stack = empty_stack; close = _48_1148.close; steps = _48_1148.steps}))
in (let _139_473 = (norm_pat pat)
in (_139_473, w, c_body.code)))))))))))
end))
in (let eqns = (FStar_List.map wn_eqn eqns)
in (let e = (FStar_Absyn_Syntax.mk_Exp_match (c_e1.code, eqns) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (let _48_1153 = config
in {code = e; environment = _48_1153.environment; stack = _48_1153.stack; close = _48_1153.close; steps = _48_1153.steps}) rebuild)))))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), body) -> begin
(let _48_1185 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _48_1163 _48_1168 -> (match ((_48_1163, _48_1168)) with
| ((env, lbs), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = eff; FStar_Absyn_Syntax.lbdef = e}) -> begin
(let c = (wne tcenv (let _48_1169 = config
in {code = e; environment = _48_1169.environment; stack = empty_stack; close = _48_1169.close; steps = _48_1169.steps}))
in (let t = (sn tcenv (t_config t config.environment config.steps))
in (let _48_1182 = (match (x) with
| FStar_Util.Inl (x) -> begin
(let y = (let _139_476 = if is_rec then begin
x
end else begin
(FStar_Absyn_Util.freshen_bvd x)
end
in (FStar_Absyn_Util.bvd_to_bvar_s _139_476 t.code))
in (let yexp = (FStar_Absyn_Util.bvar_to_exp y)
in (let y_for_x = V ((x, (yexp, empty_env)))
in (FStar_Util.Inl (y.FStar_Absyn_Syntax.v), (extend_env' env y_for_x)))))
end
| _48_1179 -> begin
(x, env)
end)
in (match (_48_1182) with
| (y, env) -> begin
(env, ((FStar_Absyn_Syntax.mk_lb (y, eff, t.code, c.code)))::lbs)
end))))
end)) (config.environment, [])))
in (match (_48_1185) with
| (env, lbs) -> begin
(let lbs = (FStar_List.rev lbs)
in (let c_body = (wne tcenv (let _48_1187 = config
in {code = body; environment = env; stack = empty_stack; close = _48_1187.close; steps = _48_1187.steps}))
in (let e = (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), c_body.code) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (let _48_1191 = config
in {code = e; environment = _48_1191.environment; stack = _48_1191.stack; close = _48_1191.close; steps = _48_1191.steps}) rebuild))))
end))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, l) -> begin
(let c = (wne tcenv (let _48_1198 = config
in {code = e; environment = _48_1198.environment; stack = _48_1198.stack; close = _48_1198.close; steps = _48_1198.steps}))
in if (is_stack_empty config) then begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (let _139_478 = (let _48_1202 = config
in (let _139_477 = (FStar_Absyn_Syntax.mk_Exp_ascribed (c.code, t.code, l) None e.FStar_Absyn_Syntax.pos)
in {code = _139_477; environment = _48_1202.environment; stack = _48_1202.stack; close = _48_1202.close; steps = _48_1202.steps}))
in (rebuild _139_478)))
end else begin
c
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, info)) -> begin
(let c = (wne tcenv (let _48_1209 = config
in {code = e; environment = _48_1209.environment; stack = _48_1209.stack; close = _48_1209.close; steps = _48_1209.steps}))
in if (is_stack_empty config) then begin
(let _139_480 = (let _48_1212 = config
in (let _139_479 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((c.code, info))))
in {code = _139_479; environment = _48_1212.environment; stack = _48_1212.stack; close = _48_1212.close; steps = _48_1212.steps}))
in (rebuild _139_480))
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

let norm_sigelt = (fun tcenv _48_10 -> (match (_48_10) with
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, b) -> begin
(let e = (let _139_504 = (let _139_503 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None r)
in (lbs, _139_503))
in (FStar_Absyn_Syntax.mk_Exp_let _139_504 None r))
in (let e = (norm_exp ((Beta)::[]) tcenv e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_let (lbs, _48_1238) -> begin
FStar_Absyn_Syntax.Sig_let ((lbs, r, l, b))
end
| _48_1242 -> begin
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
(let _139_509 = (eta_expand tcenv t)
in (FStar_All.pipe_right _139_509 FStar_Absyn_Util.compress_typ))
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

let exp_norm_to_string = (fun tcenv e -> (let _139_532 = (norm_exp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv e)
in (FStar_Absyn_Print.exp_to_string _139_532)))

let typ_norm_to_string = (fun tcenv t -> (let _139_537 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv t)
in (FStar_Absyn_Print.typ_to_string _139_537)))

let kind_norm_to_string = (fun tcenv k -> (let _139_542 = (norm_kind ((Beta)::(SNComp)::(Unmeta)::[]) tcenv k)
in (FStar_Absyn_Print.kind_to_string _139_542)))

let formula_norm_to_string = (fun tcenv f -> (let _139_547 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv f)
in (FStar_Absyn_Print.formula_to_string _139_547)))

let comp_typ_norm_to_string = (fun tcenv c -> (let _139_552 = (norm_comp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv c)
in (FStar_Absyn_Print.comp_typ_to_string _139_552)))

let normalize_refinement = (fun steps env t0 -> (let t = (norm_typ (FStar_List.append ((Beta)::(WHNF)::(DeltaHard)::[]) steps) env t0)
in (let rec aux = (fun t -> (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(let t0 = (aux x.FStar_Absyn_Syntax.sort)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (y, phi1) -> begin
(let _139_567 = (let _139_566 = (let _139_565 = (let _139_564 = (let _139_563 = (let _139_562 = (let _139_561 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _139_561))
in FStar_Util.Inr (_139_562))
in (_139_563)::[])
in (FStar_Absyn_Util.subst_typ _139_564 phi))
in (FStar_Absyn_Util.mk_conj phi1 _139_565))
in (y, _139_566))
in (FStar_Absyn_Syntax.mk_Typ_refine _139_567 (Some (FStar_Absyn_Syntax.ktype)) t0.FStar_Absyn_Syntax.pos))
end
| _48_1351 -> begin
t
end))
end
| _48_1353 -> begin
t
end)))
in (aux t))))




