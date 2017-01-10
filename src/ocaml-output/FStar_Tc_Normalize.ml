
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
| WHNF (_) -> begin
true
end
| _ -> begin
false
end))


let is_Eta = (fun _discr_ -> (match (_discr_) with
| Eta (_) -> begin
true
end
| _ -> begin
false
end))


let is_EtaArgs = (fun _discr_ -> (match (_discr_) with
| EtaArgs (_) -> begin
true
end
| _ -> begin
false
end))


let is_Delta = (fun _discr_ -> (match (_discr_) with
| Delta (_) -> begin
true
end
| _ -> begin
false
end))


let is_DeltaHard = (fun _discr_ -> (match (_discr_) with
| DeltaHard (_) -> begin
true
end
| _ -> begin
false
end))


let is_UnfoldOpaque = (fun _discr_ -> (match (_discr_) with
| UnfoldOpaque (_) -> begin
true
end
| _ -> begin
false
end))


let is_Beta = (fun _discr_ -> (match (_discr_) with
| Beta (_) -> begin
true
end
| _ -> begin
false
end))


let is_DeltaComp = (fun _discr_ -> (match (_discr_) with
| DeltaComp (_) -> begin
true
end
| _ -> begin
false
end))


let is_Simplify = (fun _discr_ -> (match (_discr_) with
| Simplify (_) -> begin
true
end
| _ -> begin
false
end))


let is_SNComp = (fun _discr_ -> (match (_discr_) with
| SNComp (_) -> begin
true
end
| _ -> begin
false
end))


let is_Unmeta = (fun _discr_ -> (match (_discr_) with
| Unmeta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Unlabel = (fun _discr_ -> (match (_discr_) with
| Unlabel (_) -> begin
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


let is_Mkconfig = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkconfig"))))


let is_Mkenvironment : environment  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkenvironment"))))


let is_Mkstack : stack  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkstack"))))


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
| T (_44_26) -> begin
_44_26
end))


let ___V____0 = (fun projectee -> (match (projectee) with
| V (_44_29) -> begin
_44_29
end))


let empty_env : environment = {context = []; label_suffix = []}


let extend_env' : environment  ->  env_entry  ->  environment = (fun env b -> (

let _44_32 = env
in {context = (b)::env.context; label_suffix = _44_32.label_suffix}))


let extend_env : environment  ->  env_entry Prims.list  ->  environment = (fun env bindings -> (

let _44_36 = env
in {context = (FStar_List.append bindings env.context); label_suffix = _44_36.label_suffix}))


let lookup_env : environment  ->  Prims.string  ->  env_entry Prims.option = (fun env key -> (FStar_All.pipe_right env.context (FStar_Util.find_opt (fun _44_1 -> (match (_44_1) with
| T (a, _44_43) -> begin
(a.FStar_Absyn_Syntax.realname.FStar_Ident.idText = key)
end
| V (x, _44_48) -> begin
(x.FStar_Absyn_Syntax.realname.FStar_Ident.idText = key)
end)))))


let fold_env = (fun env f acc -> (FStar_List.fold_left (fun acc v -> (match (v) with
| T (a, _44_58) -> begin
(f a.FStar_Absyn_Syntax.realname.FStar_Ident.idText v acc)
end
| V (x, _44_63) -> begin
(f x.FStar_Absyn_Syntax.realname.FStar_Ident.idText v acc)
end)) acc env.context))


let empty_stack : stack = {args = []}


let rec subst_of_env' : environment  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list = (fun env -> (fold_env env (fun _44_67 v acc -> (match (v) with
| T (a, (t, env')) -> begin
(let _143_113 = (let _143_112 = (let _143_111 = (let _143_110 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_typ _143_110 t))
in ((a), (_143_111)))
in FStar_Util.Inl (_143_112))
in (_143_113)::acc)
end
| V (x, (v, env')) -> begin
(let _143_117 = (let _143_116 = (let _143_115 = (let _143_114 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_exp _143_114 v))
in ((x), (_143_115)))
in FStar_Util.Inr (_143_116))
in (_143_117)::acc)
end)) []))


let subst_of_env = (fun tcenv env -> (subst_of_env' env))


let with_new_code = (fun c e -> {code = e; environment = c.environment; stack = empty_stack; close = None; steps = c.steps})


let rec eta_expand : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun tcenv t -> (

let k = (let _143_127 = (FStar_Tc_Recheck.recompute_kind t)
in (FStar_All.pipe_right _143_127 FStar_Absyn_Util.compress_kind))
in (

let rec aux = (fun t k -> (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
t
end
| FStar_Absyn_Syntax.Kind_abbrev (_44_99, k) -> begin
(aux t k)
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k') -> begin
(match ((let _143_132 = (FStar_Absyn_Util.unascribe_typ t)
in _143_132.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam (real, body) -> begin
(

let rec aux = (fun real expected -> (match (((real), (expected))) with
| ((_44_116)::real, (_44_120)::expected) -> begin
(aux real expected)
end
| ([], []) -> begin
t
end
| ((_44_129)::_44_127, []) -> begin
(failwith "Ill-kinded type")
end
| ([], more) -> begin
(

let _44_138 = (FStar_Absyn_Util.args_of_binders more)
in (match (_44_138) with
| (more, args) -> begin
(

let body = (FStar_Absyn_Syntax.mk_Typ_app ((body), (args)) None body.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_List.append binders more)), (body)) None body.FStar_Absyn_Syntax.pos))
end))
end))
in (aux real binders))
end
| _44_141 -> begin
(

let _44_144 = (FStar_Absyn_Util.args_of_binders binders)
in (match (_44_144) with
| (binders, args) -> begin
(

let body = (FStar_Absyn_Syntax.mk_Typ_app ((t), (args)) None t.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_lam ((binders), (body)) None t.FStar_Absyn_Syntax.pos))
end))
end)
end
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_delayed (_)) -> begin
(failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _143_140 = (let _143_139 = (let _143_137 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _143_137 FStar_Range.string_of_range))
in (let _143_138 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "%s: Impossible: Kind_unknown: %s" _143_139 _143_138)))
in (failwith _143_140))
end))
in (aux t k))))


let is_var : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((FStar_Absyn_Util.compress_typ t)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (_44_163); FStar_Absyn_Syntax.tk = _44_161; FStar_Absyn_Syntax.pos = _44_159; FStar_Absyn_Syntax.fvs = _44_157; FStar_Absyn_Syntax.uvs = _44_155} -> begin
true
end
| _44_167 -> begin
false
end))


let rec eta_expand_exp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp = (fun tcenv e -> (

let t = (let _143_147 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_All.pipe_right _143_147 FStar_Absyn_Util.compress_typ))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((let _143_148 = (FStar_Absyn_Util.compress_exp e)
in _143_148.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
if ((FStar_List.length bs) = (FStar_List.length bs')) then begin
e
end else begin
(failwith "NYI")
end
end
| _44_180 -> begin
(

let _44_183 = (FStar_Absyn_Util.args_of_binders bs)
in (match (_44_183) with
| (bs, args) -> begin
(let _143_150 = (let _143_149 = (FStar_Absyn_Syntax.mk_Exp_app ((e), (args)) None e.FStar_Absyn_Syntax.pos)
in ((bs), (_143_149)))
in (FStar_Absyn_Syntax.mk_Exp_abs _143_150 (Some (t)) e.FStar_Absyn_Syntax.pos))
end))
end)
end
| _44_185 -> begin
e
end)))


let no_eta : step Prims.list  ->  step Prims.list = (fun s -> (FStar_All.pipe_right s (FStar_List.filter (fun _44_2 -> (match (_44_2) with
| Eta -> begin
false
end
| _44_190 -> begin
true
end)))))


let no_eta_cfg = (fun c -> (

let _44_192 = c
in (let _143_155 = (no_eta c.steps)
in {code = _44_192.code; environment = _44_192.environment; stack = _44_192.stack; close = _44_192.close; steps = _143_155})))


let whnf_only = (fun config -> (FStar_All.pipe_right config.steps (FStar_List.contains WHNF)))


let unmeta = (fun config -> (FStar_All.pipe_right config.steps (FStar_List.contains Unmeta)))


let unlabel = (fun config -> ((unmeta config) || (FStar_All.pipe_right config.steps (FStar_List.contains Unlabel))))


let is_stack_empty = (fun config -> (match (config.stack.args) with
| [] -> begin
true
end
| _44_200 -> begin
false
end))


let has_eta = (fun cfg -> (FStar_All.pipe_right cfg.steps (FStar_List.contains Eta)))


let rec weak_norm_comp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp_typ = (fun env comp -> (

let c = (FStar_Absyn_Util.comp_to_comp_typ comp)
in (match ((FStar_Tc_Env.lookup_effect_abbrev env c.FStar_Absyn_Syntax.effect_name)) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(

let binders' = (FStar_List.map (fun _44_3 -> (match (_44_3) with
| (FStar_Util.Inl (b), imp) -> begin
(let _143_167 = (let _143_166 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inl (_143_166))
in ((_143_167), (imp)))
end
| (FStar_Util.Inr (b), imp) -> begin
(let _143_169 = (let _143_168 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inr (_143_168))
in ((_143_169), (imp)))
end)) binders)
in (

let subst = (let _143_171 = (let _143_170 = (FStar_Absyn_Util.args_of_binders binders')
in (FStar_All.pipe_right _143_170 Prims.snd))
in (FStar_Absyn_Util.subst_of_list binders _143_171))
in (

let cdef = (FStar_Absyn_Util.subst_comp subst cdef)
in (

let subst = (let _143_173 = (let _143_172 = (FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ)
in (_143_172)::c.FStar_Absyn_Syntax.effect_args)
in (FStar_Absyn_Util.subst_of_list binders' _143_173))
in (

let c1 = (FStar_Absyn_Util.subst_comp subst cdef)
in (

let c = (FStar_All.pipe_right (

let _44_224 = (FStar_Absyn_Util.comp_to_comp_typ c1)
in {FStar_Absyn_Syntax.effect_name = _44_224.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _44_224.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _44_224.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = c.FStar_Absyn_Syntax.flags}) FStar_Absyn_Syntax.mk_Comp)
in (weak_norm_comp env c)))))))
end)))


let t_config = (fun code env steps -> {code = code; environment = env; stack = empty_stack; close = None; steps = steps})


let k_config = (fun code env steps -> {code = code; environment = env; stack = empty_stack; close = None; steps = steps})


let e_config = (fun code env steps -> {code = code; environment = env; stack = empty_stack; close = None; steps = steps})


let c_config = (fun code env steps -> {code = code; environment = env; stack = empty_stack; close = None; steps = steps})


let close_with_config = (fun cfg f -> Some ((fun t -> (

let t = (f t)
in (match (cfg.close) with
| None -> begin
t
end
| Some (g) -> begin
(g t)
end)))))


let rec is_head_symbol : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _143_204 = (FStar_Absyn_Util.compress_typ t)
in _143_204.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _44_255, _44_257)) -> begin
(is_head_symbol t)
end
| _44_262 -> begin
false
end))


let simplify_then_apply : step Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.args  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ = (fun steps head args pos -> (

let fallback = (fun _44_268 -> (match (()) with
| () -> begin
(FStar_Absyn_Syntax.mk_Typ_app ((head), (args)) None pos)
end))
in (

let simp_t = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
Some (true)
end
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid) -> begin
Some (false)
end
| _44_276 -> begin
None
end))
in (

let simplify = (fun arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (t) -> begin
(((simp_t t)), (arg))
end
| _44_282 -> begin
((None), (arg))
end))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps)) then begin
(fallback ())
end else begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.and_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (((Some (true), _))::((_, (FStar_Util.Inl (arg), _)))::[]) | (((_, (FStar_Util.Inl (arg), _)))::((Some (true), _))::[]) -> begin
arg
end
| (((Some (false), _))::(_)::[]) | ((_)::((Some (false), _))::[]) -> begin
FStar_Absyn_Util.t_false
end
| _44_329 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.or_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (((Some (true), _))::(_)::[]) | ((_)::((Some (true), _))::[]) -> begin
FStar_Absyn_Util.t_true
end
| (((Some (false), _))::((_, (FStar_Util.Inl (arg), _)))::[]) | (((_, (FStar_Util.Inl (arg), _)))::((Some (false), _))::[]) -> begin
arg
end
| _44_374 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
FStar_Absyn_Util.t_true
end
| ((Some (true), _44_402))::((_44_392, (FStar_Util.Inl (arg), _44_396)))::[] -> begin
arg
end
| _44_406 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _44_410))::[] -> begin
FStar_Absyn_Util.t_false
end
| ((Some (false), _44_416))::[] -> begin
FStar_Absyn_Util.t_true
end
| _44_420 -> begin
(fallback ())
end)
end else begin
if ((((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.forall_lid) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid)) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exists_lid)) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) then begin
(match (args) with
| (((FStar_Util.Inl (t), _))::[]) | ((_)::((FStar_Util.Inl (t), _))::[]) -> begin
(match ((let _143_219 = (FStar_Absyn_Util.compress_typ t)
in _143_219.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam ((_44_435)::[], body) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
FStar_Absyn_Util.t_true
end
| Some (false) -> begin
FStar_Absyn_Util.t_false
end
| _44_445 -> begin
(fallback ())
end)
end
| _44_447 -> begin
(fallback ())
end)
end
| _44_449 -> begin
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
| _44_451 -> begin
(fallback ())
end)
end))))


let rec sn_delay : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ config  ->  FStar_Absyn_Syntax.typ config = (fun tcenv cfg -> (

let aux = (fun _44_455 -> (match (()) with
| () -> begin
(let _143_245 = (sn tcenv cfg)
in _143_245.code)
end))
in (

let t = (FStar_Absyn_Syntax.mk_Typ_delayed' (FStar_Util.Inr (aux)) None cfg.code.FStar_Absyn_Syntax.pos)
in (

let _44_457 = cfg
in {code = t; environment = _44_457.environment; stack = empty_stack; close = _44_457.close; steps = _44_457.steps}))))
and sn : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ config  ->  FStar_Absyn_Syntax.typ config = (fun tcenv cfg -> (

let rebuild = (fun config -> (

let rebuild_stack = (fun config -> if (is_stack_empty config) then begin
config
end else begin
(

let s' = if (FStar_List.contains EtaArgs config.steps) then begin
config.steps
end else begin
(no_eta config.steps)
end
in (

let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _44_4 -> (match (_44_4) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _143_257 = (let _143_256 = (let _143_255 = (sn tcenv (t_config t env s'))
in _143_255.code)
in (FStar_All.pipe_left (fun _143_254 -> FStar_Util.Inl (_143_254)) _143_256))
in ((_143_257), (imp)))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _143_261 = (let _143_260 = (let _143_259 = (wne tcenv (e_config v env s'))
in _143_259.code)
in (FStar_All.pipe_left (fun _143_258 -> FStar_Util.Inr (_143_258)) _143_260))
in ((_143_261), (imp)))
end))))
in (

let t = (simplify_then_apply config.steps config.code args config.code.FStar_Absyn_Syntax.pos)
in (

let _44_481 = config
in {code = t; environment = _44_481.environment; stack = empty_stack; close = _44_481.close; steps = _44_481.steps}))))
end)
in (

let config = (rebuild_stack config)
in (

let t = (match (config.close) with
| None -> begin
config.code
end
| Some (f) -> begin
(f config.code)
end)
in if (has_eta config) then begin
(

let _44_488 = config
in (let _143_263 = (eta_expand tcenv t)
in {code = _143_263; environment = _44_488.environment; stack = _44_488.stack; close = _44_488.close; steps = _44_488.steps}))
end else begin
(

let _44_490 = config
in {code = t; environment = _44_490.environment; stack = _44_490.stack; close = _44_490.close; steps = _44_490.steps})
end))))
in (

let wk = (fun f -> (match ((FStar_ST.read cfg.code.FStar_Absyn_Syntax.tk)) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _44_501; FStar_Absyn_Syntax.pos = _44_499; FStar_Absyn_Syntax.fvs = _44_497; FStar_Absyn_Syntax.uvs = _44_495}) -> begin
(f (Some (FStar_Absyn_Syntax.ktype)) cfg.code.FStar_Absyn_Syntax.pos)
end
| _44_506 -> begin
(f None cfg.code.FStar_Absyn_Syntax.pos)
end))
in (

let config = (

let _44_507 = cfg
in (let _143_276 = (FStar_Absyn_Util.compress_typ cfg.code)
in {code = _143_276; environment = _44_507.environment; stack = _44_507.stack; close = _44_507.close; steps = _44_507.steps}))
in (match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_44_511) -> begin
(failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_uvar (_44_514) -> begin
(rebuild config)
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(

let topt = if (FStar_All.pipe_right config.steps (FStar_List.contains UnfoldOpaque)) then begin
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
(sn tcenv (

let _44_522 = config
in {code = t; environment = _44_522.environment; stack = _44_522.stack; close = _44_522.close; steps = _44_522.steps}))
end))
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(match ((lookup_env config.environment a.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname.FStar_Ident.idText)) with
| None -> begin
(rebuild config)
end
| Some (T (_44_528, (t, e))) -> begin
(sn tcenv (

let _44_535 = config
in {code = t; environment = e; stack = _44_535.stack; close = _44_535.close; steps = _44_535.steps}))
end
| _44_538 -> begin
(failwith "Impossible: expected a type")
end)
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(

let args = (FStar_List.fold_right (fun a out -> (((a), (config.environment)))::out) args config.stack.args)
in (

let stack = (

let _44_546 = config.stack
in {args = args})
in (sn tcenv (

let _44_549 = config
in {code = head; environment = _44_549.environment; stack = stack; close = _44_549.close; steps = _44_549.steps}))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(match (config.stack.args) with
| [] -> begin
(

let _44_558 = (sn_binders tcenv binders config.environment config.steps)
in (match (_44_558) with
| (binders, environment) -> begin
(

let mk_lam = (fun t -> (

let lam = (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_lam ((binders), (t))))
in (match (cfg.close) with
| None -> begin
lam
end
| Some (f) -> begin
(f lam)
end)))
in (

let t2_cfg = (let _143_289 = (let _143_288 = (no_eta config.steps)
in {code = t2; environment = environment; stack = empty_stack; close = None; steps = _143_288})
in (sn_delay tcenv _143_289))
in (

let _44_566 = t2_cfg
in (let _143_290 = (mk_lam t2_cfg.code)
in {code = _143_290; environment = _44_566.environment; stack = _44_566.stack; close = _44_566.close; steps = _44_566.steps}))))
end))
end
| args -> begin
(

let rec beta = (fun env_entries binders args -> (match (((binders), (args))) with
| ([], _44_575) -> begin
(

let env = (extend_env config.environment env_entries)
in (sn tcenv (

let _44_578 = config
in {code = t2; environment = env; stack = (

let _44_580 = config.stack
in {args = args}); close = _44_578.close; steps = _44_578.steps})))
end
| (_44_583, []) -> begin
(

let t = (FStar_Absyn_Syntax.mk_Typ_lam ((binders), (t2)) None t2.FStar_Absyn_Syntax.pos)
in (

let env = (extend_env config.environment env_entries)
in (sn tcenv (

let _44_588 = config
in {code = t; environment = env; stack = empty_stack; close = _44_588.close; steps = _44_588.steps}))))
end
| ((formal)::rest, (actual)::rest') -> begin
(

let m = (match (((formal), (actual))) with
| ((FStar_Util.Inl (a), _44_600), ((FStar_Util.Inl (t), _44_605), env)) -> begin
T (((a.FStar_Absyn_Syntax.v), (((t), (env)))))
end
| ((FStar_Util.Inr (x), _44_613), ((FStar_Util.Inr (v), _44_618), env)) -> begin
V (((x.FStar_Absyn_Syntax.v), (((v), (env)))))
end
| _44_624 -> begin
(let _143_301 = (let _143_300 = (let _143_297 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _143_297))
in (let _143_299 = (FStar_Absyn_Print.binder_to_string formal)
in (let _143_298 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _143_300 _143_299 _143_298))))
in (failwith _143_301))
end)
in (beta ((m)::env_entries) rest rest'))
end))
in (beta [] binders args))
end)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _44_628) -> begin
(sn tcenv (

let _44_631 = config
in {code = t; environment = _44_631.environment; stack = _44_631.stack; close = _44_631.close; steps = _44_631.steps}))
end
| _44_634 -> begin
(match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, comp) -> begin
(

let _44_641 = (sn_binders tcenv bs config.environment config.steps)
in (match (_44_641) with
| (binders, environment) -> begin
(

let c2 = (sncomp tcenv (c_config comp environment config.steps))
in (let _143_305 = (

let _44_643 = config
in (let _143_304 = (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_fun ((binders), (c2.code))))
in {code = _143_304; environment = _44_643.environment; stack = _44_643.stack; close = _44_643.close; steps = _44_643.steps}))
in (rebuild _143_305)))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((let _143_307 = (let _143_306 = (FStar_Absyn_Syntax.v_binder x)
in (_143_306)::[])
in (sn_binders tcenv _143_307 config.environment config.steps))) with
| (((FStar_Util.Inr (x), _44_652))::[], env) -> begin
(

let refine = (fun t -> (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_refine ((x), (t)))))
in (let _143_314 = (let _143_313 = (FStar_All.pipe_right config.steps (FStar_List.filter (fun _44_5 -> (match (_44_5) with
| UnfoldOpaque -> begin
false
end
| _44_662 -> begin
true
end))))
in {code = t; environment = env; stack = empty_stack; close = (close_with_config config refine); steps = _143_313})
in (sn tcenv _143_314)))
end
| _44_664 -> begin
(failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
if (unmeta config) then begin
(sn tcenv (

let _44_670 = config
in {code = t; environment = _44_670.environment; stack = _44_670.stack; close = _44_670.close; steps = _44_670.steps}))
end else begin
(

let pat = (fun t -> (

let ps = (FStar_All.pipe_right ps (FStar_List.map (sn_args true tcenv config.environment config.steps)))
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern (((t), (ps))))))))
in (sn tcenv (

let _44_675 = config
in {code = t; environment = _44_675.environment; stack = _44_675.stack; close = (close_with_config config pat); steps = _44_675.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, b)) -> begin
if (unlabel config) then begin
(sn tcenv (

let _44_684 = config
in {code = t; environment = _44_684.environment; stack = _44_684.stack; close = _44_684.close; steps = _44_684.steps}))
end else begin
(

let lab = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when ((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) && (FStar_All.pipe_right config.steps (FStar_List.contains Simplify))) -> begin
t
end
| _44_691 -> begin
(match (config.environment.label_suffix) with
| ((b', sfx))::_44_693 -> begin
if ((b' = None) || (Some (b) = b')) then begin
(

let _44_698 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _143_321 = (FStar_Range.string_of_range sfx)
in (FStar_Util.print2 "Stripping label %s because of enclosing refresh %s\n" l _143_321))
end else begin
()
end
in t)
end else begin
(

let _44_700 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _143_322 = (FStar_Range.string_of_range sfx)
in (FStar_Util.print1 "Normalizer refreshing label: %s\n" _143_322))
end else begin
()
end
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled (((t), (l), (sfx), (b)))))))
end
end
| _44_703 -> begin
(FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled (((t), (l), (r), (b))))))
end)
end))
in (sn tcenv (

let _44_704 = config
in {code = t; environment = _44_704.environment; stack = _44_704.stack; close = (close_with_config config lab); steps = _44_704.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
if (unmeta config) then begin
(sn tcenv (

let _44_712 = config
in {code = t; environment = _44_712.environment; stack = _44_712.stack; close = _44_712.close; steps = _44_712.steps}))
end else begin
(

let sfx = (match (b) with
| Some (false) -> begin
r
end
| _44_717 -> begin
FStar_Absyn_Syntax.dummyRange
end)
in (

let config = (

let _44_719 = config
in {code = t; environment = (

let _44_721 = config.environment
in {context = _44_721.context; label_suffix = (((b), (sfx)))::config.environment.label_suffix}); stack = _44_719.stack; close = _44_719.close; steps = _44_719.steps})
in (sn tcenv config)))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
if (FStar_ST.read flag) then begin
(let _143_328 = (

let _44_730 = config
in (let _143_327 = (FStar_Absyn_Util.mk_conj t1 t2)
in {code = _143_327; environment = _44_730.environment; stack = _44_730.stack; close = _44_730.close; steps = _44_730.steps}))
in (sn tcenv _143_328))
end else begin
(

let c1 = (sn tcenv (t_config t1 config.environment config.steps))
in (

let c2 = (sn tcenv (t_config t2 config.environment config.steps))
in (let _143_330 = (

let _44_734 = config
in (let _143_329 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (((c1.code), (c2.code), (flag)))))
in {code = _143_329; environment = _44_734.environment; stack = _44_734.stack; close = _44_734.close; steps = _44_734.steps}))
in (rebuild _143_330))))
end
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_))) | (FStar_Absyn_Syntax.Typ_unknown) | (_) -> begin
(let _143_335 = (let _143_334 = (let _143_331 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _143_331 FStar_Range.string_of_range))
in (let _143_333 = (FStar_Absyn_Print.tag_of_typ config.code)
in (let _143_332 = (FStar_Absyn_Print.typ_to_string config.code)
in (FStar_Util.format3 "(%s) Unexpected type (%s): %s" _143_334 _143_333 _143_332))))
in (failwith _143_335))
end)
end)))))
and sn_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  environment  ->  step Prims.list  ->  (FStar_Absyn_Syntax.binders * environment) = (fun tcenv binders env steps -> (

let rec aux = (fun out env _44_6 -> (match (_44_6) with
| ((FStar_Util.Inl (a), imp))::rest -> begin
(

let c = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort env steps))
in (

let b = (let _143_346 = (FStar_Absyn_Util.freshen_bvd a.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _143_346 c.code))
in (

let btyp = (FStar_Absyn_Util.btvar_to_typ b)
in (

let b_for_a = T (((a.FStar_Absyn_Syntax.v), (((btyp), (empty_env)))))
in (aux ((((FStar_Util.Inl (b)), (imp)))::out) (extend_env' env b_for_a) rest)))))
end
| ((FStar_Util.Inr (x), imp))::rest -> begin
(

let c = (sn_delay tcenv (t_config x.FStar_Absyn_Syntax.sort env steps))
in (

let y = (let _143_347 = (FStar_Absyn_Util.freshen_bvd x.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _143_347 c.code))
in (

let yexp = (FStar_Absyn_Util.bvar_to_exp y)
in (

let y_for_x = V (((x.FStar_Absyn_Syntax.v), (((yexp), (empty_env)))))
in (aux ((((FStar_Util.Inr (y)), (imp)))::out) (extend_env' env y_for_x) rest)))))
end
| [] -> begin
(((FStar_List.rev out)), (env))
end))
in (aux [] env binders)))
and sncomp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp config  ->  FStar_Absyn_Syntax.comp config = (fun tcenv cfg -> (

let m = cfg.code
in (match (m.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) -> begin
(

let ctconf = (sncomp_typ tcenv (with_new_code cfg ct))
in (

let _44_778 = cfg
in (let _143_350 = (FStar_Absyn_Syntax.mk_Comp ctconf.code)
in {code = _143_350; environment = _44_778.environment; stack = _44_778.stack; close = _44_778.close; steps = _44_778.steps})))
end
| FStar_Absyn_Syntax.Total (t) -> begin
if (FStar_List.contains DeltaComp cfg.steps) then begin
(let _143_354 = (let _143_353 = (let _143_352 = (let _143_351 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_Absyn_Util.comp_to_comp_typ _143_351))
in (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp _143_352))
in (with_new_code cfg _143_353))
in (FStar_All.pipe_left (sncomp tcenv) _143_354))
end else begin
(

let t = (sn tcenv (with_new_code cfg t))
in (let _143_355 = (FStar_Absyn_Syntax.mk_Total t.code)
in (with_new_code cfg _143_355)))
end
end)))
and sncomp_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp_typ config  ->  FStar_Absyn_Syntax.comp_typ config = (fun tcenv cfg -> (

let m = cfg.code
in (

let norm = (fun _44_787 -> (match (()) with
| () -> begin
(

let remake = (fun l r eargs flags -> (

let c = {FStar_Absyn_Syntax.effect_name = l; FStar_Absyn_Syntax.result_typ = r; FStar_Absyn_Syntax.effect_args = eargs; FStar_Absyn_Syntax.flags = flags}
in (

let _44_794 = cfg
in {code = c; environment = _44_794.environment; stack = _44_794.stack; close = _44_794.close; steps = _44_794.steps})))
in (

let res = (let _143_368 = (sn tcenv (with_new_code cfg m.FStar_Absyn_Syntax.result_typ))
in _143_368.code)
in (

let sn_flags = (fun flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _44_7 -> (match (_44_7) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(

let e = (let _143_372 = (wne tcenv (e_config e cfg.environment cfg.steps))
in _143_372.code)
in FStar_Absyn_Syntax.DECREASES (e))
end
| f -> begin
f
end)))))
in (

let _44_806 = (let _143_374 = (sn_flags m.FStar_Absyn_Syntax.flags)
in (let _143_373 = (sn_args true tcenv cfg.environment cfg.steps m.FStar_Absyn_Syntax.effect_args)
in ((_143_374), (_143_373))))
in (match (_44_806) with
| (flags, args) -> begin
(remake m.FStar_Absyn_Syntax.effect_name res args flags)
end)))))
end))
in if (FStar_List.contains DeltaComp cfg.steps) then begin
(match ((FStar_Tc_Env.lookup_effect_abbrev tcenv m.FStar_Absyn_Syntax.effect_name)) with
| Some (_44_808) -> begin
(

let c = (let _143_375 = (FStar_Absyn_Syntax.mk_Comp m)
in (weak_norm_comp tcenv _143_375))
in (sncomp_typ tcenv (

let _44_811 = cfg
in {code = c; environment = _44_811.environment; stack = _44_811.stack; close = _44_811.close; steps = _44_811.steps})))
end
| _44_814 -> begin
(norm ())
end)
end else begin
(norm ())
end)))
and sn_args : Prims.bool  ->  FStar_Tc_Env.env  ->  environment  ->  step Prims.list  ->  FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.arg Prims.list = (fun delay tcenv env steps args -> (FStar_All.pipe_right args (FStar_List.map (fun _44_8 -> (match (_44_8) with
| (FStar_Util.Inl (t), imp) when delay -> begin
(let _143_385 = (let _143_384 = (let _143_383 = (sn_delay tcenv (t_config t env steps))
in _143_383.code)
in (FStar_All.pipe_left (fun _143_382 -> FStar_Util.Inl (_143_382)) _143_384))
in ((_143_385), (imp)))
end
| (FStar_Util.Inl (t), imp) -> begin
(let _143_389 = (let _143_388 = (let _143_387 = (sn tcenv (t_config t env steps))
in _143_387.code)
in (FStar_All.pipe_left (fun _143_386 -> FStar_Util.Inl (_143_386)) _143_388))
in ((_143_389), (imp)))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _143_393 = (let _143_392 = (let _143_391 = (wne tcenv (e_config e env steps))
in _143_391.code)
in (FStar_All.pipe_left (fun _143_390 -> FStar_Util.Inr (_143_390)) _143_392))
in ((_143_393), (imp)))
end)))))
and snk : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd config  ->  FStar_Absyn_Syntax.knd config = (fun tcenv cfg -> (

let w = (fun f -> (f cfg.code.FStar_Absyn_Syntax.pos))
in (match ((let _143_403 = (FStar_Absyn_Util.compress_kind cfg.code)
in _143_403.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Kind_delayed (_)) | (FStar_Absyn_Syntax.Kind_lam (_)) -> begin
(failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
cfg
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(

let args = (let _143_404 = (no_eta cfg.steps)
in (sn_args false tcenv cfg.environment _143_404 args))
in (

let _44_850 = cfg
in (let _143_406 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar ((uv), (args))))
in {code = _143_406; environment = _44_850.environment; stack = _44_850.stack; close = _44_850.close; steps = _44_850.steps})))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _44_862; FStar_Absyn_Syntax.pos = _44_860; FStar_Absyn_Syntax.fvs = _44_858; FStar_Absyn_Syntax.uvs = _44_856}) -> begin
(

let _44_871 = (FStar_Tc_Env.lookup_kind_abbrev tcenv l)
in (match (_44_871) with
| (_44_868, binders, body) -> begin
(

let subst = (FStar_Absyn_Util.subst_of_list binders args)
in (let _143_408 = (

let _44_873 = cfg
in (let _143_407 = (FStar_Absyn_Util.subst_kind subst body)
in {code = _143_407; environment = _44_873.environment; stack = _44_873.stack; close = _44_873.close; steps = _44_873.steps}))
in (snk tcenv _143_408)))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_44_876, k) -> begin
(snk tcenv (

let _44_880 = cfg
in {code = k; environment = _44_880.environment; stack = _44_880.stack; close = _44_880.close; steps = _44_880.steps}))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(

let _44_888 = (sn_binders tcenv bs cfg.environment cfg.steps)
in (match (_44_888) with
| (bs, env) -> begin
(

let c2 = (snk tcenv (k_config k env cfg.steps))
in (

let _44_898 = (match (c2.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs', k) -> begin
(((FStar_List.append bs bs')), (k))
end
| _44_895 -> begin
((bs), (c2.code))
end)
in (match (_44_898) with
| (bs, rhs) -> begin
(

let _44_899 = cfg
in (let _143_410 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (rhs))))
in {code = _143_410; environment = _44_899.environment; stack = _44_899.stack; close = _44_899.close; steps = _44_899.steps}))
end)))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(failwith "Impossible")
end)))
and wne : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp config  ->  FStar_Absyn_Syntax.exp config = (fun tcenv cfg -> (

let e = (FStar_Absyn_Util.compress_exp cfg.code)
in (

let config = (

let _44_905 = cfg
in {code = e; environment = _44_905.environment; stack = _44_905.stack; close = _44_905.close; steps = _44_905.steps})
in (

let rebuild = (fun config -> if (is_stack_empty config) then begin
config
end else begin
(

let s' = if (FStar_List.contains EtaArgs config.steps) then begin
config.steps
end else begin
(no_eta config.steps)
end
in (

let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _44_9 -> (match (_44_9) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _143_419 = (let _143_418 = (let _143_417 = (sn tcenv (t_config t env s'))
in _143_417.code)
in (FStar_All.pipe_left (fun _143_416 -> FStar_Util.Inl (_143_416)) _143_418))
in ((_143_419), (imp)))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _143_423 = (let _143_422 = (let _143_421 = (wne tcenv (e_config v env s'))
in _143_421.code)
in (FStar_All.pipe_left (fun _143_420 -> FStar_Util.Inr (_143_420)) _143_422))
in ((_143_423), (imp)))
end))))
in (

let _44_925 = config
in (let _143_424 = (FStar_Absyn_Syntax.mk_Exp_app ((config.code), (args)) None config.code.FStar_Absyn_Syntax.pos)
in {code = _143_424; environment = _44_925.environment; stack = empty_stack; close = _44_925.close; steps = _44_925.steps}))))
end)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_44_928) -> begin
(failwith "Impossible")
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
(FStar_All.pipe_right config rebuild)
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(match ((lookup_env config.environment x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname.FStar_Ident.idText)) with
| None -> begin
(FStar_All.pipe_right config rebuild)
end
| Some (V (_44_943, (vc, env))) -> begin
(wne tcenv (

let _44_950 = config
in {code = vc; environment = env; stack = _44_950.stack; close = _44_950.close; steps = _44_950.steps}))
end
| _44_953 -> begin
(failwith "Impossible: ill-typed term")
end)
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(

let args = (FStar_List.fold_right (fun a out -> (((a), (config.environment)))::out) args config.stack.args)
in (

let stack = (

let _44_961 = config.stack
in {args = args})
in (wne tcenv (

let _44_964 = config
in {code = head; environment = _44_964.environment; stack = stack; close = _44_964.close; steps = _44_964.steps}))))
end
| FStar_Absyn_Syntax.Exp_abs (binders, body) -> begin
(

let rec beta = (fun entries binders args -> (match (((binders), (args))) with
| ([], _44_976) -> begin
(

let env = (extend_env config.environment entries)
in (wne tcenv (

let _44_979 = config
in {code = body; environment = env; stack = (

let _44_981 = config.stack
in {args = args}); close = _44_979.close; steps = _44_979.steps})))
end
| (_44_984, []) -> begin
(

let env = (extend_env config.environment entries)
in (

let _44_990 = (sn_binders tcenv binders env config.steps)
in (match (_44_990) with
| (binders, env) -> begin
(

let mk_abs = (fun t -> (FStar_Absyn_Syntax.mk_Exp_abs ((binders), (t)) None body.FStar_Absyn_Syntax.pos))
in (

let c = (let _143_436 = (

let _44_993 = config
in (let _143_435 = (no_eta config.steps)
in {code = body; environment = env; stack = (

let _44_995 = config.stack
in {args = []}); close = _44_993.close; steps = _143_435}))
in (wne tcenv _143_436))
in (

let _44_998 = c
in (let _143_437 = (mk_abs c.code)
in {code = _143_437; environment = _44_998.environment; stack = _44_998.stack; close = _44_998.close; steps = _44_998.steps}))))
end)))
end
| ((formal)::rest, (actual)::rest') -> begin
(

let m = (match (((formal), (actual))) with
| ((FStar_Util.Inl (a), _44_1010), ((FStar_Util.Inl (t), _44_1015), env)) -> begin
T (((a.FStar_Absyn_Syntax.v), (((t), (env)))))
end
| ((FStar_Util.Inr (x), _44_1023), ((FStar_Util.Inr (v), _44_1028), env)) -> begin
V (((x.FStar_Absyn_Syntax.v), (((v), (env)))))
end
| _44_1034 -> begin
(let _143_442 = (let _143_441 = (let _143_438 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _143_438))
in (let _143_440 = (FStar_Absyn_Print.binder_to_string formal)
in (let _143_439 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _143_441 _143_440 _143_439))))
in (failwith _143_442))
end)
in (beta ((m)::entries) rest rest'))
end))
in (beta [] binders config.stack.args))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(

let c_e1 = (wne tcenv (

let _44_1040 = config
in {code = e1; environment = _44_1040.environment; stack = empty_stack; close = _44_1040.close; steps = _44_1040.steps}))
in (

let wn_eqn = (fun _44_1047 -> (match (_44_1047) with
| (pat, w, body) -> begin
(

let rec pat_vars = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_disj ((p)::_44_1053) -> begin
(pat_vars p)
end
| FStar_Absyn_Syntax.Pat_cons (_44_1058, _44_1060, pats) -> begin
(FStar_List.collect (fun _44_1067 -> (match (_44_1067) with
| (x, _44_1066) -> begin
(pat_vars x)
end)) pats)
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _143_448 = (FStar_Absyn_Syntax.v_binder x)
in (_143_448)::[])
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _143_449 = (FStar_Absyn_Syntax.t_binder a)
in (_143_449)::[])
end
| (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_constant (_)) | (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
[]
end))
in (

let vars = (pat_vars pat)
in (

let norm_bvvar = (fun x -> (

let t = (sn tcenv (t_config x.FStar_Absyn_Syntax.sort config.environment config.steps))
in (

let _44_1091 = x
in {FStar_Absyn_Syntax.v = _44_1091.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t.code; FStar_Absyn_Syntax.p = _44_1091.FStar_Absyn_Syntax.p})))
in (

let norm_btvar = (fun a -> (

let k = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort config.environment config.steps))
in (

let _44_1096 = a
in {FStar_Absyn_Syntax.v = _44_1096.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k.code; FStar_Absyn_Syntax.p = _44_1096.FStar_Absyn_Syntax.p})))
in (

let rec norm_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (pats) -> begin
(let _143_457 = (let _143_456 = (FStar_List.map norm_pat pats)
in FStar_Absyn_Syntax.Pat_disj (_143_456))
in (FStar_Absyn_Util.withinfo _143_457 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _143_462 = (let _143_461 = (let _143_460 = (FStar_List.map (fun _44_1109 -> (match (_44_1109) with
| (x, i) -> begin
(let _143_459 = (norm_pat x)
in ((_143_459), (i)))
end)) pats)
in ((fv), (q), (_143_460)))
in FStar_Absyn_Syntax.Pat_cons (_143_461))
in (FStar_Absyn_Util.withinfo _143_462 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _143_464 = (let _143_463 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_var (_143_463))
in (FStar_Absyn_Util.withinfo _143_464 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _143_466 = (let _143_465 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_tvar (_143_465))
in (FStar_Absyn_Util.withinfo _143_466 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let _143_468 = (let _143_467 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_wild (_143_467))
in (FStar_Absyn_Util.withinfo _143_468 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let _143_470 = (let _143_469 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_twild (_143_469))
in (FStar_Absyn_Util.withinfo _143_470 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_constant (_44_1119) -> begin
p
end
| FStar_Absyn_Syntax.Pat_dot_term (x, e) -> begin
(

let e = (wne tcenv (e_config e config.environment config.steps))
in (let _143_473 = (let _143_472 = (let _143_471 = (norm_bvvar x)
in ((_143_471), (e.code)))
in FStar_Absyn_Syntax.Pat_dot_term (_143_472))
in (FStar_Absyn_Util.withinfo _143_473 None p.FStar_Absyn_Syntax.p)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
(

let t = (sn tcenv (t_config t config.environment config.steps))
in (let _143_476 = (let _143_475 = (let _143_474 = (norm_btvar a)
in ((_143_474), (t.code)))
in FStar_Absyn_Syntax.Pat_dot_typ (_143_475))
in (FStar_Absyn_Util.withinfo _143_476 None p.FStar_Absyn_Syntax.p)))
end))
in (

let env_entries = (FStar_List.fold_left (fun entries b -> (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(

let atyp = (FStar_Absyn_Util.btvar_to_typ a)
in (T (((a.FStar_Absyn_Syntax.v), (((atyp), (empty_env))))))::entries)
end
| FStar_Util.Inr (x) -> begin
(

let xexp = (FStar_Absyn_Util.bvar_to_exp x)
in (V (((x.FStar_Absyn_Syntax.v), (((xexp), (empty_env))))))::entries)
end)) [] vars)
in (

let env = (extend_env config.environment env_entries)
in (

let w = (match (w) with
| None -> begin
None
end
| Some (w) -> begin
(

let c_w = (wne tcenv (

let _44_1144 = config
in {code = w; environment = env; stack = empty_stack; close = _44_1144.close; steps = _44_1144.steps}))
in Some (c_w.code))
end)
in (

let c_body = (wne tcenv (

let _44_1148 = config
in {code = body; environment = env; stack = empty_stack; close = _44_1148.close; steps = _44_1148.steps}))
in (let _143_479 = (norm_pat pat)
in ((_143_479), (w), (c_body.code))))))))))))
end))
in (

let eqns = (FStar_List.map wn_eqn eqns)
in (

let e = (FStar_Absyn_Syntax.mk_Exp_match ((c_e1.code), (eqns)) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (

let _44_1153 = config
in {code = e; environment = _44_1153.environment; stack = _44_1153.stack; close = _44_1153.close; steps = _44_1153.steps}) rebuild)))))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), body) -> begin
(

let _44_1185 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _44_1163 _44_1168 -> (match (((_44_1163), (_44_1168))) with
| ((env, lbs), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = eff; FStar_Absyn_Syntax.lbdef = e}) -> begin
(

let c = (wne tcenv (

let _44_1169 = config
in {code = e; environment = _44_1169.environment; stack = empty_stack; close = _44_1169.close; steps = _44_1169.steps}))
in (

let t = (sn tcenv (t_config t config.environment config.steps))
in (

let _44_1182 = (match (x) with
| FStar_Util.Inl (x) -> begin
(

let y = (let _143_482 = if is_rec then begin
x
end else begin
(FStar_Absyn_Util.freshen_bvd x)
end
in (FStar_Absyn_Util.bvd_to_bvar_s _143_482 t.code))
in (

let yexp = (FStar_Absyn_Util.bvar_to_exp y)
in (

let y_for_x = V (((x), (((yexp), (empty_env)))))
in ((FStar_Util.Inl (y.FStar_Absyn_Syntax.v)), ((extend_env' env y_for_x))))))
end
| _44_1179 -> begin
((x), (env))
end)
in (match (_44_1182) with
| (y, env) -> begin
(let _143_484 = (let _143_483 = (FStar_Absyn_Syntax.mk_lb ((y), (eff), (t.code), (c.code)))
in (_143_483)::lbs)
in ((env), (_143_484)))
end))))
end)) ((config.environment), ([]))))
in (match (_44_1185) with
| (env, lbs) -> begin
(

let lbs = (FStar_List.rev lbs)
in (

let c_body = (wne tcenv (

let _44_1187 = config
in {code = body; environment = env; stack = empty_stack; close = _44_1187.close; steps = _44_1187.steps}))
in (

let e = (FStar_Absyn_Syntax.mk_Exp_let ((((is_rec), (lbs))), (c_body.code)) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (

let _44_1191 = config
in {code = e; environment = _44_1191.environment; stack = _44_1191.stack; close = _44_1191.close; steps = _44_1191.steps}) rebuild))))
end))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, l) -> begin
(

let c = (wne tcenv (

let _44_1198 = config
in {code = e; environment = _44_1198.environment; stack = _44_1198.stack; close = _44_1198.close; steps = _44_1198.steps}))
in if (is_stack_empty config) then begin
(

let t = (sn tcenv (t_config t config.environment config.steps))
in (let _143_486 = (

let _44_1202 = config
in (let _143_485 = (FStar_Absyn_Syntax.mk_Exp_ascribed ((c.code), (t.code), (l)) None e.FStar_Absyn_Syntax.pos)
in {code = _143_485; environment = _44_1202.environment; stack = _44_1202.stack; close = _44_1202.close; steps = _44_1202.steps}))
in (rebuild _143_486)))
end else begin
c
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, info)) -> begin
(

let c = (wne tcenv (

let _44_1209 = config
in {code = e; environment = _44_1209.environment; stack = _44_1209.stack; close = _44_1209.close; steps = _44_1209.steps}))
in if (is_stack_empty config) then begin
(let _143_488 = (

let _44_1212 = config
in (let _143_487 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((c.code), (info)))))
in {code = _143_487; environment = _44_1212.environment; stack = _44_1212.stack; close = _44_1212.close; steps = _44_1212.steps}))
in (rebuild _143_488))
end else begin
c
end)
end)))))


let norm_kind : steps  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun steps tcenv k -> (

let c = (snk tcenv (k_config k empty_env steps))
in (FStar_Absyn_Util.compress_kind c.code)))


let norm_typ : steps  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun steps tcenv t -> (

let c = (sn tcenv (t_config t empty_env steps))
in c.code))


let norm_exp : steps  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp = (fun steps tcenv e -> (

let c = (wne tcenv (e_config e empty_env steps))
in c.code))


let norm_sigelt : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt = (fun tcenv _44_10 -> (match (_44_10) with
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, b) -> begin
(

let e = (let _143_512 = (let _143_511 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None r)
in ((lbs), (_143_511)))
in (FStar_Absyn_Syntax.mk_Exp_let _143_512 None r))
in (

let e = (norm_exp ((Beta)::[]) tcenv e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_let (lbs, _44_1238) -> begin
FStar_Absyn_Syntax.Sig_let (((lbs), (r), (l), (b)))
end
| _44_1242 -> begin
(failwith "Impossible")
end)))
end
| s -> begin
s
end))


let whnf : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun tcenv t -> (

let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_refine (_)) -> begin
t
end
| (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _143_517 = (eta_expand tcenv t)
in (FStar_All.pipe_right _143_517 FStar_Absyn_Util.compress_typ))
end
| (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) | (_) -> begin
(norm_typ ((WHNF)::(Beta)::(Eta)::[]) tcenv t)
end)))


let norm_comp : steps  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp = (fun steps tcenv c -> (

let c = (sncomp tcenv (c_config c empty_env steps))
in c.code))


let normalize_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun tcenv k -> (

let steps = (Eta)::(Delta)::(Beta)::[]
in (norm_kind steps tcenv k)))


let normalize_comp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp = (fun tcenv c -> (

let steps = (Eta)::(Delta)::(Beta)::(SNComp)::(DeltaComp)::[]
in (norm_comp steps tcenv c)))


let normalize : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun tcenv t -> (norm_typ ((DeltaHard)::(Beta)::(Eta)::[]) tcenv t))


let exp_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  Prims.string = (fun tcenv e -> (let _143_540 = (norm_exp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv e)
in (FStar_Absyn_Print.exp_to_string _143_540)))


let typ_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun tcenv t -> (let _143_545 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv t)
in (FStar_Absyn_Print.typ_to_string _143_545)))


let kind_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun tcenv k -> (let _143_550 = (norm_kind ((Beta)::(SNComp)::(Unmeta)::[]) tcenv k)
in (FStar_Absyn_Print.kind_to_string _143_550)))


let formula_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun tcenv f -> (let _143_555 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv f)
in (FStar_Absyn_Print.formula_to_string _143_555)))


let comp_typ_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  Prims.string = (fun tcenv c -> (let _143_560 = (norm_comp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv c)
in (FStar_Absyn_Print.comp_typ_to_string _143_560)))


let normalize_refinement : steps  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun steps env t0 -> (

let t = (norm_typ (FStar_List.append ((Beta)::(WHNF)::(DeltaHard)::[]) steps) env t0)
in (

let rec aux = (fun t -> (

let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(

let t0 = (aux x.FStar_Absyn_Syntax.sort)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (y, phi1) -> begin
(let _143_575 = (let _143_574 = (let _143_573 = (let _143_572 = (let _143_571 = (let _143_570 = (let _143_569 = (FStar_Absyn_Util.bvar_to_exp y)
in ((x.FStar_Absyn_Syntax.v), (_143_569)))
in FStar_Util.Inr (_143_570))
in (_143_571)::[])
in (FStar_Absyn_Util.subst_typ _143_572 phi))
in (FStar_Absyn_Util.mk_conj phi1 _143_573))
in ((y), (_143_574)))
in (FStar_Absyn_Syntax.mk_Typ_refine _143_575 (Some (FStar_Absyn_Syntax.ktype)) t0.FStar_Absyn_Syntax.pos))
end
| _44_1351 -> begin
t
end))
end
| _44_1353 -> begin
t
end)))
in (aux t))))




