
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
(let _98_113 = (let _98_112 = (let _98_111 = (let _98_110 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_typ _98_110 t))
in (a, _98_111))
in FStar_Util.Inl (_98_112))
in (_98_113)::acc)
end
| V (x, (v, env')) -> begin
(let _98_117 = (let _98_116 = (let _98_115 = (let _98_114 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_exp _98_114 v))
in (x, _98_115))
in FStar_Util.Inr (_98_116))
in (_98_117)::acc)
end)) []))

let subst_of_env = (fun tcenv env -> (subst_of_env' env))

let with_new_code = (fun c e -> {code = e; environment = c.environment; stack = empty_stack; close = None; steps = c.steps})

let rec eta_expand = (fun tcenv t -> (let k = (let _98_127 = (FStar_Tc_Recheck.recompute_kind t)
in (FStar_All.pipe_right _98_127 FStar_Absyn_Util.compress_kind))
in (let rec aux = (fun t k -> (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
t
end
| FStar_Absyn_Syntax.Kind_abbrev (_33_98, k) -> begin
(aux t k)
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k') -> begin
(match ((let _98_132 = (FStar_Absyn_Util.unascribe_typ t)
in _98_132.FStar_Absyn_Syntax.n)) with
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
(let _98_140 = (let _98_139 = (let _98_137 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _98_137 FStar_Range.string_of_range))
in (let _98_138 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "%s: Impossible: Kind_unknown: %s" _98_139 _98_138)))
in (FStar_All.failwith _98_140))
end))
in (aux t k))))

let is_var = (fun t -> (match ((FStar_Absyn_Util.compress_typ t)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (_33_162); FStar_Absyn_Syntax.tk = _33_160; FStar_Absyn_Syntax.pos = _33_158; FStar_Absyn_Syntax.fvs = _33_156; FStar_Absyn_Syntax.uvs = _33_154} -> begin
true
end
| _33_166 -> begin
false
end))

let rec eta_expand_exp = (fun tcenv e -> (let t = (let _98_147 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_All.pipe_right _98_147 FStar_Absyn_Util.compress_typ))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((let _98_148 = (FStar_Absyn_Util.compress_exp e)
in _98_148.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
if ((FStar_List.length bs) = (FStar_List.length bs')) then begin
e
end else begin
(FStar_All.failwith "NYI")
end
end
| _33_179 -> begin
(let _33_182 = (FStar_Absyn_Util.args_of_binders bs)
in (match (_33_182) with
| (bs, args) -> begin
(let _98_150 = (let _98_149 = (FStar_Absyn_Syntax.mk_Exp_app (e, args) None e.FStar_Absyn_Syntax.pos)
in (bs, _98_149))
in (FStar_Absyn_Syntax.mk_Exp_abs _98_150 (Some (t)) e.FStar_Absyn_Syntax.pos))
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
in (let _98_155 = (no_eta c.steps)
in {code = _33_191.code; environment = _33_191.environment; stack = _33_191.stack; close = _33_191.close; steps = _98_155})))

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
(let _98_167 = (let _98_166 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inl (_98_166))
in (_98_167, imp))
end
| (FStar_Util.Inr (b), imp) -> begin
(let _98_169 = (let _98_168 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inr (_98_168))
in (_98_169, imp))
end)) binders)
in (let subst = (let _98_171 = (let _98_170 = (FStar_Absyn_Util.args_of_binders binders')
in (FStar_All.pipe_right _98_170 Prims.snd))
in (FStar_Absyn_Util.subst_of_list binders _98_171))
in (let cdef = (FStar_Absyn_Util.subst_comp subst cdef)
in (let subst = (let _98_173 = (let _98_172 = (FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ)
in (_98_172)::c.FStar_Absyn_Syntax.effect_args)
in (FStar_Absyn_Util.subst_of_list binders' _98_173))
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

let rec is_head_symbol = (fun t -> (match ((let _98_204 = (FStar_Absyn_Util.compress_typ t)
in _98_204.FStar_Absyn_Syntax.n)) with
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
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps)) then begin
(fallback ())
end else begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
if (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.and_lid) then begin
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
end else begin
if (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.or_lid) then begin
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
end else begin
if (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.imp_lid) then begin
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
end else begin
if (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.not_lid) then begin
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
end else begin
if ((((FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.forall_lid) || (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid)) || (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exists_lid)) || (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) then begin
(match (args) with
| ((FStar_Util.Inl (t), _)::[]) | (_::(FStar_Util.Inl (t), _)::[]) -> begin
(match ((let _98_219 = (FStar_Absyn_Util.compress_typ t)
in _98_219.FStar_Absyn_Syntax.n)) with
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
end else begin
(fallback ())
end
end
end
end
end
end
| _33_450 -> begin
(fallback ())
end)
end))))

let rec sn_delay = (fun tcenv cfg -> (let aux = (fun _33_454 -> (match (()) with
| () -> begin
(let _98_245 = (sn tcenv cfg)
in _98_245.code)
end))
in (let t = (FStar_Absyn_Syntax.mk_Typ_delayed' (FStar_Util.Inr (aux)) None cfg.code.FStar_Absyn_Syntax.pos)
in (let _33_456 = cfg
in {code = t; environment = _33_456.environment; stack = empty_stack; close = _33_456.close; steps = _33_456.steps}))))
and sn = (fun tcenv cfg -> (let rebuild = (fun config -> (let rebuild_stack = (fun config -> if (is_stack_empty config) then begin
config
end else begin
(let s' = if (FStar_List.contains EtaArgs config.steps) then begin
config.steps
end else begin
(no_eta config.steps)
end
in (let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _33_4 -> (match (_33_4) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _98_257 = (let _98_256 = (let _98_255 = (sn tcenv (t_config t env s'))
in _98_255.code)
in (FStar_All.pipe_left (fun _98_254 -> FStar_Util.Inl (_98_254)) _98_256))
in (_98_257, imp))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _98_261 = (let _98_260 = (let _98_259 = (wne tcenv (e_config v env s'))
in _98_259.code)
in (FStar_All.pipe_left (fun _98_258 -> FStar_Util.Inr (_98_258)) _98_260))
in (_98_261, imp))
end))))
in (let t = (simplify_then_apply config.steps config.code args config.code.FStar_Absyn_Syntax.pos)
in (let _33_480 = config
in {code = t; environment = _33_480.environment; stack = empty_stack; close = _33_480.close; steps = _33_480.steps}))))
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
(let _33_487 = config
in (let _98_263 = (eta_expand tcenv t)
in {code = _98_263; environment = _33_487.environment; stack = _33_487.stack; close = _33_487.close; steps = _33_487.steps}))
end else begin
(let _33_489 = config
in {code = t; environment = _33_489.environment; stack = _33_489.stack; close = _33_489.close; steps = _33_489.steps})
end))))
in (let wk = (fun f -> (match ((FStar_ST.read cfg.code.FStar_Absyn_Syntax.tk)) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _33_500; FStar_Absyn_Syntax.pos = _33_498; FStar_Absyn_Syntax.fvs = _33_496; FStar_Absyn_Syntax.uvs = _33_494}) -> begin
(f (Some (FStar_Absyn_Syntax.ktype)) cfg.code.FStar_Absyn_Syntax.pos)
end
| _33_505 -> begin
(f None cfg.code.FStar_Absyn_Syntax.pos)
end))
in (let config = (let _33_506 = cfg
in (let _98_276 = (FStar_Absyn_Util.compress_typ cfg.code)
in {code = _98_276; environment = _33_506.environment; stack = _33_506.stack; close = _33_506.close; steps = _33_506.steps}))
in (match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_33_510) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_uvar (_33_513) -> begin
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
(sn tcenv (let _33_521 = config
in {code = t; environment = _33_521.environment; stack = _33_521.stack; close = _33_521.close; steps = _33_521.steps}))
end))
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(match ((lookup_env config.environment a.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText)) with
| None -> begin
(rebuild config)
end
| Some (T (_33_527, (t, e))) -> begin
(sn tcenv (let _33_534 = config
in {code = t; environment = e; stack = _33_534.stack; close = _33_534.close; steps = _33_534.steps}))
end
| _33_537 -> begin
(FStar_All.failwith "Impossible: expected a type")
end)
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let args = (FStar_List.fold_right (fun a out -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _33_545 = config.stack
in {args = args})
in (sn tcenv (let _33_548 = config
in {code = head; environment = _33_548.environment; stack = stack; close = _33_548.close; steps = _33_548.steps}))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(match (config.stack.args) with
| [] -> begin
(let _33_557 = (sn_binders tcenv binders config.environment config.steps)
in (match (_33_557) with
| (binders, environment) -> begin
(let mk_lam = (fun t -> (let lam = (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_lam (binders, t)))
in (match (cfg.close) with
| None -> begin
lam
end
| Some (f) -> begin
(f lam)
end)))
in (let t2_cfg = (let _98_289 = (let _98_288 = (no_eta config.steps)
in {code = t2; environment = environment; stack = empty_stack; close = None; steps = _98_288})
in (sn_delay tcenv _98_289))
in (let _33_565 = t2_cfg
in (let _98_290 = (mk_lam t2_cfg.code)
in {code = _98_290; environment = _33_565.environment; stack = _33_565.stack; close = _33_565.close; steps = _33_565.steps}))))
end))
end
| args -> begin
(let rec beta = (fun env_entries binders args -> (match ((binders, args)) with
| ([], _33_574) -> begin
(let env = (extend_env config.environment env_entries)
in (sn tcenv (let _33_577 = config
in {code = t2; environment = env; stack = (let _33_579 = config.stack
in {args = args}); close = _33_577.close; steps = _33_577.steps})))
end
| (_33_582, []) -> begin
(let t = (FStar_Absyn_Syntax.mk_Typ_lam (binders, t2) None t2.FStar_Absyn_Syntax.pos)
in (let env = (extend_env config.environment env_entries)
in (sn tcenv (let _33_587 = config
in {code = t; environment = env; stack = empty_stack; close = _33_587.close; steps = _33_587.steps}))))
end
| (formal::rest, actual::rest') -> begin
(let m = (match ((formal, actual)) with
| ((FStar_Util.Inl (a), _33_599), ((FStar_Util.Inl (t), _33_604), env)) -> begin
T ((a.FStar_Absyn_Syntax.v, (t, env)))
end
| ((FStar_Util.Inr (x), _33_612), ((FStar_Util.Inr (v), _33_617), env)) -> begin
V ((x.FStar_Absyn_Syntax.v, (v, env)))
end
| _33_623 -> begin
(let _98_301 = (let _98_300 = (let _98_297 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _98_297))
in (let _98_299 = (FStar_Absyn_Print.binder_to_string formal)
in (let _98_298 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _98_300 _98_299 _98_298))))
in (FStar_All.failwith _98_301))
end)
in (beta ((m)::env_entries) rest rest'))
end))
in (beta [] binders args))
end)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _33_627) -> begin
(sn tcenv (let _33_630 = config
in {code = t; environment = _33_630.environment; stack = _33_630.stack; close = _33_630.close; steps = _33_630.steps}))
end
| _33_633 -> begin
(match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, comp) -> begin
(let _33_640 = (sn_binders tcenv bs config.environment config.steps)
in (match (_33_640) with
| (binders, environment) -> begin
(let c2 = (sncomp tcenv (c_config comp environment config.steps))
in (let _33_642 = config
in (let _98_304 = (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_fun (binders, c2.code)))
in {code = _98_304; environment = _33_642.environment; stack = _33_642.stack; close = _33_642.close; steps = _33_642.steps})))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((let _98_306 = (let _98_305 = (FStar_Absyn_Syntax.v_binder x)
in (_98_305)::[])
in (sn_binders tcenv _98_306 config.environment config.steps))) with
| ((FStar_Util.Inr (x), _33_651)::[], env) -> begin
(let refine = (fun t -> (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_refine (x, t))))
in (sn tcenv {code = t; environment = env; stack = empty_stack; close = (close_with_config config refine); steps = config.steps}))
end
| _33_659 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
if (unmeta config) then begin
(sn tcenv (let _33_665 = config
in {code = t; environment = _33_665.environment; stack = _33_665.stack; close = _33_665.close; steps = _33_665.steps}))
end else begin
(let pat = (fun t -> (let ps = (FStar_All.pipe_right ps (FStar_List.map (sn_args true tcenv config.environment config.steps)))
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern ((t, ps)))))))
in (sn tcenv (let _33_670 = config
in {code = t; environment = _33_670.environment; stack = _33_670.stack; close = (close_with_config config pat); steps = _33_670.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, b)) -> begin
if (unlabel config) then begin
(sn tcenv (let _33_679 = config
in {code = t; environment = _33_679.environment; stack = _33_679.stack; close = _33_679.close; steps = _33_679.steps}))
end else begin
(let lab = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when ((FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) && (FStar_All.pipe_right config.steps (FStar_List.contains Simplify))) -> begin
t
end
| _33_686 -> begin
(match (config.environment.label_suffix) with
| (b', sfx)::_33_688 -> begin
if ((b' = None) || (Some (b) = b')) then begin
(let _33_693 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _98_317 = (FStar_Range.string_of_range sfx)
in (FStar_Util.fprint2 "Stripping label %s because of enclosing refresh %s\n" l _98_317))
end else begin
()
end
in t)
end else begin
(let _33_695 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _98_318 = (FStar_Range.string_of_range sfx)
in (FStar_Util.fprint1 "Normalizer refreshing label: %s\n" _98_318))
end else begin
()
end
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, sfx, b))))))
end
end
| _33_698 -> begin
(FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b)))))
end)
end))
in (sn tcenv (let _33_699 = config
in {code = t; environment = _33_699.environment; stack = _33_699.stack; close = (close_with_config config lab); steps = _33_699.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
if (unmeta config) then begin
(sn tcenv (let _33_707 = config
in {code = t; environment = _33_707.environment; stack = _33_707.stack; close = _33_707.close; steps = _33_707.steps}))
end else begin
(let sfx = (match (b) with
| Some (false) -> begin
r
end
| _33_712 -> begin
FStar_Absyn_Syntax.dummyRange
end)
in (let config = (let _33_714 = config
in {code = t; environment = (let _33_716 = config.environment
in {context = _33_716.context; label_suffix = ((b, sfx))::config.environment.label_suffix}); stack = _33_714.stack; close = _33_714.close; steps = _33_714.steps})
in (sn tcenv config)))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
if (FStar_ST.read flag) then begin
(let _98_324 = (let _33_725 = config
in (let _98_323 = (FStar_Absyn_Util.mk_conj t1 t2)
in {code = _98_323; environment = _33_725.environment; stack = _33_725.stack; close = _33_725.close; steps = _33_725.steps}))
in (sn tcenv _98_324))
end else begin
(let c1 = (sn tcenv (t_config t1 config.environment config.steps))
in (let c2 = (sn tcenv (t_config t2 config.environment config.steps))
in (let _98_326 = (let _33_729 = config
in (let _98_325 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula ((c1.code, c2.code, flag))))
in {code = _98_325; environment = _33_729.environment; stack = _33_729.stack; close = _33_729.close; steps = _33_729.steps}))
in (rebuild _98_326))))
end
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_))) | (FStar_Absyn_Syntax.Typ_unknown) | (_) -> begin
(let _98_331 = (let _98_330 = (let _98_327 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _98_327 FStar_Range.string_of_range))
in (let _98_329 = (FStar_Absyn_Print.tag_of_typ config.code)
in (let _98_328 = (FStar_Absyn_Print.typ_to_string config.code)
in (FStar_Util.format3 "(%s) Unexpected type (%s): %s" _98_330 _98_329 _98_328))))
in (FStar_All.failwith _98_331))
end)
end)))))
and sn_binders = (fun tcenv binders env steps -> (let rec aux = (fun out env _33_5 -> (match (_33_5) with
| (FStar_Util.Inl (a), imp)::rest -> begin
(let c = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort env steps))
in (let b = (let _98_342 = (FStar_Absyn_Util.freshen_bvd a.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _98_342 c.code))
in (let btyp = (FStar_Absyn_Util.btvar_to_typ b)
in (let b_for_a = T ((a.FStar_Absyn_Syntax.v, (btyp, empty_env)))
in (aux (((FStar_Util.Inl (b), imp))::out) (extend_env' env b_for_a) rest)))))
end
| (FStar_Util.Inr (x), imp)::rest -> begin
(let c = (sn_delay tcenv (t_config x.FStar_Absyn_Syntax.sort env steps))
in (let y = (let _98_343 = (FStar_Absyn_Util.freshen_bvd x.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _98_343 c.code))
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
in (let _33_773 = cfg
in (let _98_346 = (FStar_Absyn_Syntax.mk_Comp ctconf.code)
in {code = _98_346; environment = _33_773.environment; stack = _33_773.stack; close = _33_773.close; steps = _33_773.steps})))
end
| FStar_Absyn_Syntax.Total (t) -> begin
if (FStar_List.contains DeltaComp cfg.steps) then begin
(let _98_350 = (let _98_349 = (let _98_348 = (let _98_347 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_Absyn_Util.comp_to_comp_typ _98_347))
in (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp _98_348))
in (with_new_code cfg _98_349))
in (FStar_All.pipe_left (sncomp tcenv) _98_350))
end else begin
(let t = (sn tcenv (with_new_code cfg t))
in (let _98_351 = (FStar_Absyn_Syntax.mk_Total t.code)
in (with_new_code cfg _98_351)))
end
end)))
and sncomp_typ = (fun tcenv cfg -> (let m = cfg.code
in (let norm = (fun _33_782 -> (match (()) with
| () -> begin
(let remake = (fun l r eargs flags -> (let c = {FStar_Absyn_Syntax.effect_name = l; FStar_Absyn_Syntax.result_typ = r; FStar_Absyn_Syntax.effect_args = eargs; FStar_Absyn_Syntax.flags = flags}
in (let _33_789 = cfg
in {code = c; environment = _33_789.environment; stack = _33_789.stack; close = _33_789.close; steps = _33_789.steps})))
in (let res = (let _98_364 = (sn tcenv (with_new_code cfg m.FStar_Absyn_Syntax.result_typ))
in _98_364.code)
in (let sn_flags = (fun flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _33_6 -> (match (_33_6) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let e = (let _98_368 = (wne tcenv (e_config e cfg.environment cfg.steps))
in _98_368.code)
in FStar_Absyn_Syntax.DECREASES (e))
end
| f -> begin
f
end)))))
in (let _33_801 = (let _98_370 = (sn_flags m.FStar_Absyn_Syntax.flags)
in (let _98_369 = (sn_args true tcenv cfg.environment cfg.steps m.FStar_Absyn_Syntax.effect_args)
in (_98_370, _98_369)))
in (match (_33_801) with
| (flags, args) -> begin
(remake m.FStar_Absyn_Syntax.effect_name res args flags)
end)))))
end))
in if (FStar_List.contains DeltaComp cfg.steps) then begin
(match ((FStar_Tc_Env.lookup_effect_abbrev tcenv m.FStar_Absyn_Syntax.effect_name)) with
| Some (_33_803) -> begin
(let c = (let _98_371 = (FStar_Absyn_Syntax.mk_Comp m)
in (weak_norm_comp tcenv _98_371))
in (sncomp_typ tcenv (let _33_806 = cfg
in {code = c; environment = _33_806.environment; stack = _33_806.stack; close = _33_806.close; steps = _33_806.steps})))
end
| _33_809 -> begin
(norm ())
end)
end else begin
(norm ())
end)))
and sn_args = (fun delay tcenv env steps args -> (FStar_All.pipe_right args (FStar_List.map (fun _33_7 -> (match (_33_7) with
| (FStar_Util.Inl (t), imp) when delay -> begin
(let _98_381 = (let _98_380 = (let _98_379 = (sn_delay tcenv (t_config t env steps))
in _98_379.code)
in (FStar_All.pipe_left (fun _98_378 -> FStar_Util.Inl (_98_378)) _98_380))
in (_98_381, imp))
end
| (FStar_Util.Inl (t), imp) -> begin
(let _98_385 = (let _98_384 = (let _98_383 = (sn tcenv (t_config t env steps))
in _98_383.code)
in (FStar_All.pipe_left (fun _98_382 -> FStar_Util.Inl (_98_382)) _98_384))
in (_98_385, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _98_389 = (let _98_388 = (let _98_387 = (wne tcenv (e_config e env steps))
in _98_387.code)
in (FStar_All.pipe_left (fun _98_386 -> FStar_Util.Inr (_98_386)) _98_388))
in (_98_389, imp))
end)))))
and snk = (fun tcenv cfg -> (let w = (fun f -> (f cfg.code.FStar_Absyn_Syntax.pos))
in (match ((let _98_399 = (FStar_Absyn_Util.compress_kind cfg.code)
in _98_399.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Kind_delayed (_)) | (FStar_Absyn_Syntax.Kind_lam (_)) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
cfg
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(let args = (let _98_400 = (no_eta cfg.steps)
in (sn_args false tcenv cfg.environment _98_400 args))
in (let _33_845 = cfg
in (let _98_402 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar (uv, args)))
in {code = _98_402; environment = _33_845.environment; stack = _33_845.stack; close = _33_845.close; steps = _33_845.steps})))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _33_857; FStar_Absyn_Syntax.pos = _33_855; FStar_Absyn_Syntax.fvs = _33_853; FStar_Absyn_Syntax.uvs = _33_851}) -> begin
(let _33_866 = (FStar_Tc_Env.lookup_kind_abbrev tcenv l)
in (match (_33_866) with
| (_33_863, binders, body) -> begin
(let subst = (FStar_Absyn_Util.subst_of_list binders args)
in (let _98_404 = (let _33_868 = cfg
in (let _98_403 = (FStar_Absyn_Util.subst_kind subst body)
in {code = _98_403; environment = _33_868.environment; stack = _33_868.stack; close = _33_868.close; steps = _33_868.steps}))
in (snk tcenv _98_404)))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_33_871, k) -> begin
(snk tcenv (let _33_875 = cfg
in {code = k; environment = _33_875.environment; stack = _33_875.stack; close = _33_875.close; steps = _33_875.steps}))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _33_883 = (sn_binders tcenv bs cfg.environment cfg.steps)
in (match (_33_883) with
| (bs, env) -> begin
(let c2 = (snk tcenv (k_config k env cfg.steps))
in (let _33_893 = (match (c2.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs', k) -> begin
((FStar_List.append bs bs'), k)
end
| _33_890 -> begin
(bs, c2.code)
end)
in (match (_33_893) with
| (bs, rhs) -> begin
(let _33_894 = cfg
in (let _98_406 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (bs, rhs)))
in {code = _98_406; environment = _33_894.environment; stack = _33_894.stack; close = _33_894.close; steps = _33_894.steps}))
end)))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(FStar_All.failwith "Impossible")
end)))
and wne = (fun tcenv cfg -> (let e = (FStar_Absyn_Util.compress_exp cfg.code)
in (let config = (let _33_900 = cfg
in {code = e; environment = _33_900.environment; stack = _33_900.stack; close = _33_900.close; steps = _33_900.steps})
in (let rebuild = (fun config -> if (is_stack_empty config) then begin
config
end else begin
(let s' = if (FStar_List.contains EtaArgs config.steps) then begin
config.steps
end else begin
(no_eta config.steps)
end
in (let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _33_8 -> (match (_33_8) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _98_415 = (let _98_414 = (let _98_413 = (sn tcenv (t_config t env s'))
in _98_413.code)
in (FStar_All.pipe_left (fun _98_412 -> FStar_Util.Inl (_98_412)) _98_414))
in (_98_415, imp))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _98_419 = (let _98_418 = (let _98_417 = (wne tcenv (e_config v env s'))
in _98_417.code)
in (FStar_All.pipe_left (fun _98_416 -> FStar_Util.Inr (_98_416)) _98_418))
in (_98_419, imp))
end))))
in (let _33_920 = config
in (let _98_420 = (FStar_Absyn_Syntax.mk_Exp_app (config.code, args) None config.code.FStar_Absyn_Syntax.pos)
in {code = _98_420; environment = _33_920.environment; stack = empty_stack; close = _33_920.close; steps = _33_920.steps}))))
end)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_33_923) -> begin
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
| Some (V (_33_938, (vc, env))) -> begin
(wne tcenv (let _33_945 = config
in {code = vc; environment = env; stack = _33_945.stack; close = _33_945.close; steps = _33_945.steps}))
end
| _33_948 -> begin
(FStar_All.failwith "Impossible: ill-typed term")
end)
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let args = (FStar_List.fold_right (fun a out -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _33_956 = config.stack
in {args = args})
in (wne tcenv (let _33_959 = config
in {code = head; environment = _33_959.environment; stack = stack; close = _33_959.close; steps = _33_959.steps}))))
end
| FStar_Absyn_Syntax.Exp_abs (binders, body) -> begin
(let rec beta = (fun entries binders args -> (match ((binders, args)) with
| ([], _33_971) -> begin
(let env = (extend_env config.environment entries)
in (wne tcenv (let _33_974 = config
in {code = body; environment = env; stack = (let _33_976 = config.stack
in {args = args}); close = _33_974.close; steps = _33_974.steps})))
end
| (_33_979, []) -> begin
(let env = (extend_env config.environment entries)
in (let _33_985 = (sn_binders tcenv binders env config.steps)
in (match (_33_985) with
| (binders, env) -> begin
(let mk_abs = (fun t -> (FStar_Absyn_Syntax.mk_Exp_abs (binders, t) None body.FStar_Absyn_Syntax.pos))
in (let c = (let _98_432 = (let _33_988 = config
in (let _98_431 = (no_eta config.steps)
in {code = body; environment = env; stack = (let _33_990 = config.stack
in {args = []}); close = _33_988.close; steps = _98_431}))
in (wne tcenv _98_432))
in (let _33_993 = c
in (let _98_433 = (mk_abs c.code)
in {code = _98_433; environment = _33_993.environment; stack = _33_993.stack; close = _33_993.close; steps = _33_993.steps}))))
end)))
end
| (formal::rest, actual::rest') -> begin
(let m = (match ((formal, actual)) with
| ((FStar_Util.Inl (a), _33_1005), ((FStar_Util.Inl (t), _33_1010), env)) -> begin
T ((a.FStar_Absyn_Syntax.v, (t, env)))
end
| ((FStar_Util.Inr (x), _33_1018), ((FStar_Util.Inr (v), _33_1023), env)) -> begin
V ((x.FStar_Absyn_Syntax.v, (v, env)))
end
| _33_1029 -> begin
(let _98_438 = (let _98_437 = (let _98_434 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _98_434))
in (let _98_436 = (FStar_Absyn_Print.binder_to_string formal)
in (let _98_435 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _98_437 _98_436 _98_435))))
in (FStar_All.failwith _98_438))
end)
in (beta ((m)::entries) rest rest'))
end))
in (beta [] binders config.stack.args))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(let c_e1 = (wne tcenv (let _33_1035 = config
in {code = e1; environment = _33_1035.environment; stack = empty_stack; close = _33_1035.close; steps = _33_1035.steps}))
in (let wn_eqn = (fun _33_1042 -> (match (_33_1042) with
| (pat, w, body) -> begin
(let rec pat_vars = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_disj (p::_33_1048) -> begin
(pat_vars p)
end
| FStar_Absyn_Syntax.Pat_cons (_33_1053, _33_1055, pats) -> begin
(FStar_List.collect (fun _33_1062 -> (match (_33_1062) with
| (x, _33_1061) -> begin
(pat_vars x)
end)) pats)
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _98_444 = (FStar_Absyn_Syntax.v_binder x)
in (_98_444)::[])
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _98_445 = (FStar_Absyn_Syntax.t_binder a)
in (_98_445)::[])
end
| (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_constant (_)) | (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
[]
end))
in (let vars = (pat_vars pat)
in (let norm_bvvar = (fun x -> (let t = (sn tcenv (t_config x.FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _33_1086 = x
in {FStar_Absyn_Syntax.v = _33_1086.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t.code; FStar_Absyn_Syntax.p = _33_1086.FStar_Absyn_Syntax.p})))
in (let norm_btvar = (fun a -> (let k = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _33_1091 = a
in {FStar_Absyn_Syntax.v = _33_1091.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k.code; FStar_Absyn_Syntax.p = _33_1091.FStar_Absyn_Syntax.p})))
in (let rec norm_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (pats) -> begin
(let _98_453 = (let _98_452 = (FStar_List.map norm_pat pats)
in FStar_Absyn_Syntax.Pat_disj (_98_452))
in (FStar_Absyn_Util.withinfo _98_453 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _98_458 = (let _98_457 = (let _98_456 = (FStar_List.map (fun _33_1104 -> (match (_33_1104) with
| (x, i) -> begin
(let _98_455 = (norm_pat x)
in (_98_455, i))
end)) pats)
in (fv, q, _98_456))
in FStar_Absyn_Syntax.Pat_cons (_98_457))
in (FStar_Absyn_Util.withinfo _98_458 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _98_460 = (let _98_459 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_var (_98_459))
in (FStar_Absyn_Util.withinfo _98_460 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _98_462 = (let _98_461 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_tvar (_98_461))
in (FStar_Absyn_Util.withinfo _98_462 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let _98_464 = (let _98_463 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_wild (_98_463))
in (FStar_Absyn_Util.withinfo _98_464 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let _98_466 = (let _98_465 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_twild (_98_465))
in (FStar_Absyn_Util.withinfo _98_466 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_constant (_33_1114) -> begin
p
end
| FStar_Absyn_Syntax.Pat_dot_term (x, e) -> begin
(let e = (wne tcenv (e_config e config.environment config.steps))
in (let _98_469 = (let _98_468 = (let _98_467 = (norm_bvvar x)
in (_98_467, e.code))
in FStar_Absyn_Syntax.Pat_dot_term (_98_468))
in (FStar_Absyn_Util.withinfo _98_469 None p.FStar_Absyn_Syntax.p)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (let _98_472 = (let _98_471 = (let _98_470 = (norm_btvar a)
in (_98_470, t.code))
in FStar_Absyn_Syntax.Pat_dot_typ (_98_471))
in (FStar_Absyn_Util.withinfo _98_472 None p.FStar_Absyn_Syntax.p)))
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
(let c_w = (wne tcenv (let _33_1139 = config
in {code = w; environment = env; stack = empty_stack; close = _33_1139.close; steps = _33_1139.steps}))
in Some (c_w.code))
end)
in (let c_body = (wne tcenv (let _33_1143 = config
in {code = body; environment = env; stack = empty_stack; close = _33_1143.close; steps = _33_1143.steps}))
in (let _98_475 = (norm_pat pat)
in (_98_475, w, c_body.code)))))))))))
end))
in (let eqns = (FStar_List.map wn_eqn eqns)
in (let e = (FStar_Absyn_Syntax.mk_Exp_match (c_e1.code, eqns) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (let _33_1148 = config
in {code = e; environment = _33_1148.environment; stack = _33_1148.stack; close = _33_1148.close; steps = _33_1148.steps}) rebuild)))))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), body) -> begin
(let _33_1180 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _33_1158 _33_1163 -> (match ((_33_1158, _33_1163)) with
| ((env, lbs), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = eff; FStar_Absyn_Syntax.lbdef = e}) -> begin
(let c = (wne tcenv (let _33_1164 = config
in {code = e; environment = _33_1164.environment; stack = empty_stack; close = _33_1164.close; steps = _33_1164.steps}))
in (let t = (sn tcenv (t_config t config.environment config.steps))
in (let _33_1177 = (match (x) with
| FStar_Util.Inl (x) -> begin
(let y = (let _98_478 = if is_rec then begin
x
end else begin
(FStar_Absyn_Util.freshen_bvd x)
end
in (FStar_Absyn_Util.bvd_to_bvar_s _98_478 t.code))
in (let yexp = (FStar_Absyn_Util.bvar_to_exp y)
in (let y_for_x = V ((x, (yexp, empty_env)))
in (FStar_Util.Inl (y.FStar_Absyn_Syntax.v), (extend_env' env y_for_x)))))
end
| _33_1174 -> begin
(x, env)
end)
in (match (_33_1177) with
| (y, env) -> begin
(let _98_480 = (let _98_479 = (FStar_Absyn_Syntax.mk_lb (y, eff, t.code, c.code))
in (_98_479)::lbs)
in (env, _98_480))
end))))
end)) (config.environment, [])))
in (match (_33_1180) with
| (env, lbs) -> begin
(let lbs = (FStar_List.rev lbs)
in (let c_body = (wne tcenv (let _33_1182 = config
in {code = body; environment = env; stack = empty_stack; close = _33_1182.close; steps = _33_1182.steps}))
in (let e = (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), c_body.code) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (let _33_1186 = config
in {code = e; environment = _33_1186.environment; stack = _33_1186.stack; close = _33_1186.close; steps = _33_1186.steps}) rebuild))))
end))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, l) -> begin
(let c = (wne tcenv (let _33_1193 = config
in {code = e; environment = _33_1193.environment; stack = _33_1193.stack; close = _33_1193.close; steps = _33_1193.steps}))
in if (is_stack_empty config) then begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (let _98_482 = (let _33_1197 = config
in (let _98_481 = (FStar_Absyn_Syntax.mk_Exp_ascribed (c.code, t.code, l) None e.FStar_Absyn_Syntax.pos)
in {code = _98_481; environment = _33_1197.environment; stack = _33_1197.stack; close = _33_1197.close; steps = _33_1197.steps}))
in (rebuild _98_482)))
end else begin
c
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, info)) -> begin
(let c = (wne tcenv (let _33_1204 = config
in {code = e; environment = _33_1204.environment; stack = _33_1204.stack; close = _33_1204.close; steps = _33_1204.steps}))
in if (is_stack_empty config) then begin
(let _98_484 = (let _33_1207 = config
in (let _98_483 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((c.code, info))))
in {code = _98_483; environment = _33_1207.environment; stack = _33_1207.stack; close = _33_1207.close; steps = _33_1207.steps}))
in (rebuild _98_484))
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

let norm_sigelt = (fun tcenv _33_9 -> (match (_33_9) with
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, b) -> begin
(let e = (let _98_508 = (let _98_507 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Absyn_Syntax.Const_unit None r)
in (lbs, _98_507))
in (FStar_Absyn_Syntax.mk_Exp_let _98_508 None r))
in (let e = (norm_exp ((Beta)::[]) tcenv e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_let (lbs, _33_1233) -> begin
FStar_Absyn_Syntax.Sig_let ((lbs, r, l, b))
end
| _33_1237 -> begin
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
(let _98_513 = (eta_expand tcenv t)
in (FStar_All.pipe_right _98_513 FStar_Absyn_Util.compress_typ))
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

let exp_norm_to_string = (fun tcenv e -> (let _98_536 = (norm_exp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv e)
in (FStar_Absyn_Print.exp_to_string _98_536)))

let typ_norm_to_string = (fun tcenv t -> (let _98_541 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv t)
in (FStar_Absyn_Print.typ_to_string _98_541)))

let kind_norm_to_string = (fun tcenv k -> (let _98_546 = (norm_kind ((Beta)::(SNComp)::(Unmeta)::[]) tcenv k)
in (FStar_Absyn_Print.kind_to_string _98_546)))

let formula_norm_to_string = (fun tcenv f -> (let _98_551 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv f)
in (FStar_Absyn_Print.formula_to_string _98_551)))

let comp_typ_norm_to_string = (fun tcenv c -> (let _98_556 = (norm_comp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv c)
in (FStar_Absyn_Print.comp_typ_to_string _98_556)))

let normalize_refinement = (fun steps env t0 -> (let t = (norm_typ (FStar_List.append ((Beta)::(WHNF)::(DeltaHard)::[]) steps) env t0)
in (let rec aux = (fun t -> (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(let t0 = (aux x.FStar_Absyn_Syntax.sort)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (y, phi1) -> begin
(let _98_571 = (let _98_570 = (let _98_569 = (let _98_568 = (let _98_567 = (let _98_566 = (let _98_565 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _98_565))
in FStar_Util.Inr (_98_566))
in (_98_567)::[])
in (FStar_Absyn_Util.subst_typ _98_568 phi))
in (FStar_Absyn_Util.mk_conj phi1 _98_569))
in (y, _98_570))
in (FStar_Absyn_Syntax.mk_Typ_refine _98_571 (Some (FStar_Absyn_Syntax.ktype)) t0.FStar_Absyn_Syntax.pos))
end
| _33_1346 -> begin
t
end))
end
| _33_1348 -> begin
t
end)))
in (aux t))))




