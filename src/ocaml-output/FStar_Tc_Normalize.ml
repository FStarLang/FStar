
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
| T (_45_26) -> begin
_45_26
end))


let ___V____0 = (fun projectee -> (match (projectee) with
| V (_45_29) -> begin
_45_29
end))


let empty_env : environment = {context = []; label_suffix = []}


let extend_env' : environment  ->  env_entry  ->  environment = (fun env b -> (

let _45_32 = env
in {context = (b)::env.context; label_suffix = _45_32.label_suffix}))


let extend_env : environment  ->  env_entry Prims.list  ->  environment = (fun env bindings -> (

let _45_36 = env
in {context = (FStar_List.append bindings env.context); label_suffix = _45_36.label_suffix}))


let lookup_env : environment  ->  Prims.string  ->  env_entry Prims.option = (fun env key -> (FStar_All.pipe_right env.context (FStar_Util.find_opt (fun _45_1 -> (match (_45_1) with
| T (a, _45_43) -> begin
(a.FStar_Absyn_Syntax.realname.FStar_Ident.idText = key)
end
| V (x, _45_48) -> begin
(x.FStar_Absyn_Syntax.realname.FStar_Ident.idText = key)
end)))))


let fold_env = (fun env f acc -> (FStar_List.fold_left (fun acc v -> (match (v) with
| T (a, _45_58) -> begin
(f a.FStar_Absyn_Syntax.realname.FStar_Ident.idText v acc)
end
| V (x, _45_63) -> begin
(f x.FStar_Absyn_Syntax.realname.FStar_Ident.idText v acc)
end)) acc env.context))


let empty_stack : stack = {args = []}


let rec subst_of_env' : environment  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list = (fun env -> (fold_env env (fun _45_67 v acc -> (match (v) with
| T (a, (t, env')) -> begin
(let _146_113 = (let _146_112 = (let _146_111 = (let _146_110 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_typ _146_110 t))
in ((a), (_146_111)))
in FStar_Util.Inl (_146_112))
in (_146_113)::acc)
end
| V (x, (v, env')) -> begin
(let _146_117 = (let _146_116 = (let _146_115 = (let _146_114 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_exp _146_114 v))
in ((x), (_146_115)))
in FStar_Util.Inr (_146_116))
in (_146_117)::acc)
end)) []))


let subst_of_env = (fun tcenv env -> (subst_of_env' env))


let with_new_code = (fun c e -> {code = e; environment = c.environment; stack = empty_stack; close = None; steps = c.steps})


let rec eta_expand : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun tcenv t -> (

let k = (let _146_127 = (FStar_Tc_Recheck.recompute_kind t)
in (FStar_All.pipe_right _146_127 FStar_Absyn_Util.compress_kind))
in (

let rec aux = (fun t k -> (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
t
end
| FStar_Absyn_Syntax.Kind_abbrev (_45_99, k) -> begin
(aux t k)
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k') -> begin
(match ((let _146_132 = (FStar_Absyn_Util.unascribe_typ t)
in _146_132.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam (real, body) -> begin
(

let rec aux = (fun real expected -> (match (((real), (expected))) with
| ((_45_116)::real, (_45_120)::expected) -> begin
(aux real expected)
end
| ([], []) -> begin
t
end
| ((_45_129)::_45_127, []) -> begin
(failwith "Ill-kinded type")
end
| ([], more) -> begin
(

let _45_138 = (FStar_Absyn_Util.args_of_binders more)
in (match (_45_138) with
| (more, args) -> begin
(

let body = (FStar_Absyn_Syntax.mk_Typ_app ((body), (args)) None body.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_List.append binders more)), (body)) None body.FStar_Absyn_Syntax.pos))
end))
end))
in (aux real binders))
end
| _45_141 -> begin
(

let _45_144 = (FStar_Absyn_Util.args_of_binders binders)
in (match (_45_144) with
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
(let _146_140 = (let _146_139 = (let _146_137 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _146_137 FStar_Range.string_of_range))
in (let _146_138 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "%s: Impossible: Kind_unknown: %s" _146_139 _146_138)))
in (failwith _146_140))
end))
in (aux t k))))


let is_var : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((FStar_Absyn_Util.compress_typ t)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (_45_163); FStar_Absyn_Syntax.tk = _45_161; FStar_Absyn_Syntax.pos = _45_159; FStar_Absyn_Syntax.fvs = _45_157; FStar_Absyn_Syntax.uvs = _45_155} -> begin
true
end
| _45_167 -> begin
false
end))


let rec eta_expand_exp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp = (fun tcenv e -> (

let t = (let _146_147 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_All.pipe_right _146_147 FStar_Absyn_Util.compress_typ))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((let _146_148 = (FStar_Absyn_Util.compress_exp e)
in _146_148.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
if ((FStar_List.length bs) = (FStar_List.length bs')) then begin
e
end else begin
(failwith "NYI")
end
end
| _45_180 -> begin
(

let _45_183 = (FStar_Absyn_Util.args_of_binders bs)
in (match (_45_183) with
| (bs, args) -> begin
(let _146_150 = (let _146_149 = (FStar_Absyn_Syntax.mk_Exp_app ((e), (args)) None e.FStar_Absyn_Syntax.pos)
in ((bs), (_146_149)))
in (FStar_Absyn_Syntax.mk_Exp_abs _146_150 (Some (t)) e.FStar_Absyn_Syntax.pos))
end))
end)
end
| _45_185 -> begin
e
end)))


let no_eta : step Prims.list  ->  step Prims.list = (fun s -> (FStar_All.pipe_right s (FStar_List.filter (fun _45_2 -> (match (_45_2) with
| Eta -> begin
false
end
| _45_190 -> begin
true
end)))))


let no_eta_cfg = (fun c -> (

let _45_192 = c
in (let _146_155 = (no_eta c.steps)
in {code = _45_192.code; environment = _45_192.environment; stack = _45_192.stack; close = _45_192.close; steps = _146_155})))


let whnf_only = (fun config -> (FStar_All.pipe_right config.steps (FStar_List.contains WHNF)))


let unmeta = (fun config -> (FStar_All.pipe_right config.steps (FStar_List.contains Unmeta)))


let unlabel = (fun config -> ((unmeta config) || (FStar_All.pipe_right config.steps (FStar_List.contains Unlabel))))


let is_stack_empty = (fun config -> (match (config.stack.args) with
| [] -> begin
true
end
| _45_200 -> begin
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

let binders' = (FStar_List.map (fun _45_3 -> (match (_45_3) with
| (FStar_Util.Inl (b), imp) -> begin
(let _146_167 = (let _146_166 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inl (_146_166))
in ((_146_167), (imp)))
end
| (FStar_Util.Inr (b), imp) -> begin
(let _146_169 = (let _146_168 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inr (_146_168))
in ((_146_169), (imp)))
end)) binders)
in (

let subst = (let _146_171 = (let _146_170 = (FStar_Absyn_Util.args_of_binders binders')
in (FStar_All.pipe_right _146_170 Prims.snd))
in (FStar_Absyn_Util.subst_of_list binders _146_171))
in (

let cdef = (FStar_Absyn_Util.subst_comp subst cdef)
in (

let subst = (let _146_173 = (let _146_172 = (FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ)
in (_146_172)::c.FStar_Absyn_Syntax.effect_args)
in (FStar_Absyn_Util.subst_of_list binders' _146_173))
in (

let c1 = (FStar_Absyn_Util.subst_comp subst cdef)
in (

let c = (FStar_All.pipe_right (

let _45_224 = (FStar_Absyn_Util.comp_to_comp_typ c1)
in {FStar_Absyn_Syntax.effect_name = _45_224.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _45_224.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _45_224.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = c.FStar_Absyn_Syntax.flags}) FStar_Absyn_Syntax.mk_Comp)
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


let rec is_head_symbol : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _146_204 = (FStar_Absyn_Util.compress_typ t)
in _146_204.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _45_255, _45_257)) -> begin
(is_head_symbol t)
end
| _45_262 -> begin
false
end))


let simplify_then_apply : step Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.args  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ = (fun steps head args pos -> (

let fallback = (fun _45_268 -> (match (()) with
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
| _45_276 -> begin
None
end))
in (

let simplify = (fun arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (t) -> begin
(((simp_t t)), (arg))
end
| _45_282 -> begin
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
| _45_329 -> begin
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
| _45_374 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
FStar_Absyn_Util.t_true
end
| ((Some (true), _45_402))::((_45_392, (FStar_Util.Inl (arg), _45_396)))::[] -> begin
arg
end
| _45_406 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _45_410))::[] -> begin
FStar_Absyn_Util.t_false
end
| ((Some (false), _45_416))::[] -> begin
FStar_Absyn_Util.t_true
end
| _45_420 -> begin
(fallback ())
end)
end else begin
if ((((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.forall_lid) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid)) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exists_lid)) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) then begin
(match (args) with
| (((FStar_Util.Inl (t), _))::[]) | ((_)::((FStar_Util.Inl (t), _))::[]) -> begin
(match ((let _146_219 = (FStar_Absyn_Util.compress_typ t)
in _146_219.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam ((_45_435)::[], body) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
FStar_Absyn_Util.t_true
end
| Some (false) -> begin
FStar_Absyn_Util.t_false
end
| _45_445 -> begin
(fallback ())
end)
end
| _45_447 -> begin
(fallback ())
end)
end
| _45_449 -> begin
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
| _45_451 -> begin
(fallback ())
end)
end))))


let rec sn_delay : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ config  ->  FStar_Absyn_Syntax.typ config = (fun tcenv cfg -> (

let aux = (fun _45_455 -> (match (()) with
| () -> begin
(let _146_245 = (sn tcenv cfg)
in _146_245.code)
end))
in (

let t = (FStar_Absyn_Syntax.mk_Typ_delayed' (FStar_Util.Inr (aux)) None cfg.code.FStar_Absyn_Syntax.pos)
in (

let _45_457 = cfg
in {code = t; environment = _45_457.environment; stack = empty_stack; close = _45_457.close; steps = _45_457.steps}))))
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

let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _45_4 -> (match (_45_4) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _146_257 = (let _146_256 = (let _146_255 = (sn tcenv (t_config t env s'))
in _146_255.code)
in (FStar_All.pipe_left (fun _146_254 -> FStar_Util.Inl (_146_254)) _146_256))
in ((_146_257), (imp)))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _146_261 = (let _146_260 = (let _146_259 = (wne tcenv (e_config v env s'))
in _146_259.code)
in (FStar_All.pipe_left (fun _146_258 -> FStar_Util.Inr (_146_258)) _146_260))
in ((_146_261), (imp)))
end))))
in (

let t = (simplify_then_apply config.steps config.code args config.code.FStar_Absyn_Syntax.pos)
in (

let _45_481 = config
in {code = t; environment = _45_481.environment; stack = empty_stack; close = _45_481.close; steps = _45_481.steps}))))
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

let _45_488 = config
in (let _146_263 = (eta_expand tcenv t)
in {code = _146_263; environment = _45_488.environment; stack = _45_488.stack; close = _45_488.close; steps = _45_488.steps}))
end else begin
(

let _45_490 = config
in {code = t; environment = _45_490.environment; stack = _45_490.stack; close = _45_490.close; steps = _45_490.steps})
end))))
in (

let wk = (fun f -> (match ((FStar_ST.read cfg.code.FStar_Absyn_Syntax.tk)) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _45_501; FStar_Absyn_Syntax.pos = _45_499; FStar_Absyn_Syntax.fvs = _45_497; FStar_Absyn_Syntax.uvs = _45_495}) -> begin
(f (Some (FStar_Absyn_Syntax.ktype)) cfg.code.FStar_Absyn_Syntax.pos)
end
| _45_506 -> begin
(f None cfg.code.FStar_Absyn_Syntax.pos)
end))
in (

let config = (

let _45_507 = cfg
in (let _146_276 = (FStar_Absyn_Util.compress_typ cfg.code)
in {code = _146_276; environment = _45_507.environment; stack = _45_507.stack; close = _45_507.close; steps = _45_507.steps}))
in (match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_45_511) -> begin
(failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_uvar (_45_514) -> begin
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

let _45_522 = config
in {code = t; environment = _45_522.environment; stack = _45_522.stack; close = _45_522.close; steps = _45_522.steps}))
end))
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(match ((lookup_env config.environment a.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname.FStar_Ident.idText)) with
| None -> begin
(rebuild config)
end
| Some (T (_45_528, (t, e))) -> begin
(sn tcenv (

let _45_535 = config
in {code = t; environment = e; stack = _45_535.stack; close = _45_535.close; steps = _45_535.steps}))
end
| _45_538 -> begin
(failwith "Impossible: expected a type")
end)
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(

let args = (FStar_List.fold_right (fun a out -> (((a), (config.environment)))::out) args config.stack.args)
in (

let stack = (

let _45_546 = config.stack
in {args = args})
in (sn tcenv (

let _45_549 = config
in {code = head; environment = _45_549.environment; stack = stack; close = _45_549.close; steps = _45_549.steps}))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(match (config.stack.args) with
| [] -> begin
(

let _45_558 = (sn_binders tcenv binders config.environment config.steps)
in (match (_45_558) with
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

let t2_cfg = (let _146_289 = (let _146_288 = (no_eta config.steps)
in {code = t2; environment = environment; stack = empty_stack; close = None; steps = _146_288})
in (sn_delay tcenv _146_289))
in (

let _45_566 = t2_cfg
in (let _146_290 = (mk_lam t2_cfg.code)
in {code = _146_290; environment = _45_566.environment; stack = _45_566.stack; close = _45_566.close; steps = _45_566.steps}))))
end))
end
| args -> begin
(

let rec beta = (fun env_entries binders args -> (match (((binders), (args))) with
| ([], _45_575) -> begin
(

let env = (extend_env config.environment env_entries)
in (sn tcenv (

let _45_578 = config
in {code = t2; environment = env; stack = (

let _45_580 = config.stack
in {args = args}); close = _45_578.close; steps = _45_578.steps})))
end
| (_45_583, []) -> begin
(

let t = (FStar_Absyn_Syntax.mk_Typ_lam ((binders), (t2)) None t2.FStar_Absyn_Syntax.pos)
in (

let env = (extend_env config.environment env_entries)
in (sn tcenv (

let _45_588 = config
in {code = t; environment = env; stack = empty_stack; close = _45_588.close; steps = _45_588.steps}))))
end
| ((formal)::rest, (actual)::rest') -> begin
(

let m = (match (((formal), (actual))) with
| ((FStar_Util.Inl (a), _45_600), ((FStar_Util.Inl (t), _45_605), env)) -> begin
T (((a.FStar_Absyn_Syntax.v), (((t), (env)))))
end
| ((FStar_Util.Inr (x), _45_613), ((FStar_Util.Inr (v), _45_618), env)) -> begin
V (((x.FStar_Absyn_Syntax.v), (((v), (env)))))
end
| _45_624 -> begin
(let _146_301 = (let _146_300 = (let _146_297 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _146_297))
in (let _146_299 = (FStar_Absyn_Print.binder_to_string formal)
in (let _146_298 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _146_300 _146_299 _146_298))))
in (failwith _146_301))
end)
in (beta ((m)::env_entries) rest rest'))
end))
in (beta [] binders args))
end)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _45_628) -> begin
(sn tcenv (

let _45_631 = config
in {code = t; environment = _45_631.environment; stack = _45_631.stack; close = _45_631.close; steps = _45_631.steps}))
end
| _45_634 -> begin
(match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, comp) -> begin
(

let _45_641 = (sn_binders tcenv bs config.environment config.steps)
in (match (_45_641) with
| (binders, environment) -> begin
(

let c2 = (sncomp tcenv (c_config comp environment config.steps))
in (let _146_305 = (

let _45_643 = config
in (let _146_304 = (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_fun ((binders), (c2.code))))
in {code = _146_304; environment = _45_643.environment; stack = _45_643.stack; close = _45_643.close; steps = _45_643.steps}))
in (rebuild _146_305)))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((let _146_307 = (let _146_306 = (FStar_Absyn_Syntax.v_binder x)
in (_146_306)::[])
in (sn_binders tcenv _146_307 config.environment config.steps))) with
| (((FStar_Util.Inr (x), _45_652))::[], env) -> begin
(

let refine = (fun t -> (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_refine ((x), (t)))))
in (let _146_314 = (let _146_313 = (FStar_All.pipe_right config.steps (FStar_List.filter (fun _45_5 -> (match (_45_5) with
| UnfoldOpaque -> begin
false
end
| _45_662 -> begin
true
end))))
in {code = t; environment = env; stack = empty_stack; close = (close_with_config config refine); steps = _146_313})
in (sn tcenv _146_314)))
end
| _45_664 -> begin
(failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
if (unmeta config) then begin
(sn tcenv (

let _45_670 = config
in {code = t; environment = _45_670.environment; stack = _45_670.stack; close = _45_670.close; steps = _45_670.steps}))
end else begin
(

let pat = (fun t -> (

let ps = (FStar_All.pipe_right ps (FStar_List.map (sn_args true tcenv config.environment config.steps)))
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern (((t), (ps))))))))
in (sn tcenv (

let _45_675 = config
in {code = t; environment = _45_675.environment; stack = _45_675.stack; close = (close_with_config config pat); steps = _45_675.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, b)) -> begin
if (unlabel config) then begin
(sn tcenv (

let _45_684 = config
in {code = t; environment = _45_684.environment; stack = _45_684.stack; close = _45_684.close; steps = _45_684.steps}))
end else begin
(

let lab = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when ((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) && (FStar_All.pipe_right config.steps (FStar_List.contains Simplify))) -> begin
t
end
| _45_691 -> begin
(match (config.environment.label_suffix) with
| ((b', sfx))::_45_693 -> begin
if ((b' = None) || (Some (b) = b')) then begin
(

let _45_698 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _146_321 = (FStar_Range.string_of_range sfx)
in (FStar_Util.print2 "Stripping label %s because of enclosing refresh %s\n" l _146_321))
end else begin
()
end
in t)
end else begin
(

let _45_700 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _146_322 = (FStar_Range.string_of_range sfx)
in (FStar_Util.print1 "Normalizer refreshing label: %s\n" _146_322))
end else begin
()
end
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled (((t), (l), (sfx), (b)))))))
end
end
| _45_703 -> begin
(FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled (((t), (l), (r), (b))))))
end)
end))
in (sn tcenv (

let _45_704 = config
in {code = t; environment = _45_704.environment; stack = _45_704.stack; close = (close_with_config config lab); steps = _45_704.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
if (unmeta config) then begin
(sn tcenv (

let _45_712 = config
in {code = t; environment = _45_712.environment; stack = _45_712.stack; close = _45_712.close; steps = _45_712.steps}))
end else begin
(

let sfx = (match (b) with
| Some (false) -> begin
r
end
| _45_717 -> begin
FStar_Absyn_Syntax.dummyRange
end)
in (

let config = (

let _45_719 = config
in {code = t; environment = (

let _45_721 = config.environment
in {context = _45_721.context; label_suffix = (((b), (sfx)))::config.environment.label_suffix}); stack = _45_719.stack; close = _45_719.close; steps = _45_719.steps})
in (sn tcenv config)))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
if (FStar_ST.read flag) then begin
(let _146_328 = (

let _45_730 = config
in (let _146_327 = (FStar_Absyn_Util.mk_conj t1 t2)
in {code = _146_327; environment = _45_730.environment; stack = _45_730.stack; close = _45_730.close; steps = _45_730.steps}))
in (sn tcenv _146_328))
end else begin
(

let c1 = (sn tcenv (t_config t1 config.environment config.steps))
in (

let c2 = (sn tcenv (t_config t2 config.environment config.steps))
in (let _146_330 = (

let _45_734 = config
in (let _146_329 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (((c1.code), (c2.code), (flag)))))
in {code = _146_329; environment = _45_734.environment; stack = _45_734.stack; close = _45_734.close; steps = _45_734.steps}))
in (rebuild _146_330))))
end
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_))) | (FStar_Absyn_Syntax.Typ_unknown) | (_) -> begin
(let _146_335 = (let _146_334 = (let _146_331 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _146_331 FStar_Range.string_of_range))
in (let _146_333 = (FStar_Absyn_Print.tag_of_typ config.code)
in (let _146_332 = (FStar_Absyn_Print.typ_to_string config.code)
in (FStar_Util.format3 "(%s) Unexpected type (%s): %s" _146_334 _146_333 _146_332))))
in (failwith _146_335))
end)
end)))))
and sn_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  environment  ->  step Prims.list  ->  (FStar_Absyn_Syntax.binders * environment) = (fun tcenv binders env steps -> (

let rec aux = (fun out env _45_6 -> (match (_45_6) with
| ((FStar_Util.Inl (a), imp))::rest -> begin
(

let c = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort env steps))
in (

let b = (let _146_346 = (FStar_Absyn_Util.freshen_bvd a.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _146_346 c.code))
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

let y = (let _146_347 = (FStar_Absyn_Util.freshen_bvd x.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _146_347 c.code))
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

let _45_778 = cfg
in (let _146_350 = (FStar_Absyn_Syntax.mk_Comp ctconf.code)
in {code = _146_350; environment = _45_778.environment; stack = _45_778.stack; close = _45_778.close; steps = _45_778.steps})))
end
| FStar_Absyn_Syntax.Total (t) -> begin
if (FStar_List.contains DeltaComp cfg.steps) then begin
(let _146_354 = (let _146_353 = (let _146_352 = (let _146_351 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_Absyn_Util.comp_to_comp_typ _146_351))
in (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp _146_352))
in (with_new_code cfg _146_353))
in (FStar_All.pipe_left (sncomp tcenv) _146_354))
end else begin
(

let t = (sn tcenv (with_new_code cfg t))
in (let _146_355 = (FStar_Absyn_Syntax.mk_Total t.code)
in (with_new_code cfg _146_355)))
end
end)))
and sncomp_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp_typ config  ->  FStar_Absyn_Syntax.comp_typ config = (fun tcenv cfg -> (

let m = cfg.code
in (

let norm = (fun _45_787 -> (match (()) with
| () -> begin
(

let remake = (fun l r eargs flags -> (

let c = {FStar_Absyn_Syntax.effect_name = l; FStar_Absyn_Syntax.result_typ = r; FStar_Absyn_Syntax.effect_args = eargs; FStar_Absyn_Syntax.flags = flags}
in (

let _45_794 = cfg
in {code = c; environment = _45_794.environment; stack = _45_794.stack; close = _45_794.close; steps = _45_794.steps})))
in (

let res = (let _146_368 = (sn tcenv (with_new_code cfg m.FStar_Absyn_Syntax.result_typ))
in _146_368.code)
in (

let sn_flags = (fun flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _45_7 -> (match (_45_7) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(

let e = (let _146_372 = (wne tcenv (e_config e cfg.environment cfg.steps))
in _146_372.code)
in FStar_Absyn_Syntax.DECREASES (e))
end
| f -> begin
f
end)))))
in (

let _45_806 = (let _146_374 = (sn_flags m.FStar_Absyn_Syntax.flags)
in (let _146_373 = (sn_args true tcenv cfg.environment cfg.steps m.FStar_Absyn_Syntax.effect_args)
in ((_146_374), (_146_373))))
in (match (_45_806) with
| (flags, args) -> begin
(remake m.FStar_Absyn_Syntax.effect_name res args flags)
end)))))
end))
in if (FStar_List.contains DeltaComp cfg.steps) then begin
(match ((FStar_Tc_Env.lookup_effect_abbrev tcenv m.FStar_Absyn_Syntax.effect_name)) with
| Some (_45_808) -> begin
(

let c = (let _146_375 = (FStar_Absyn_Syntax.mk_Comp m)
in (weak_norm_comp tcenv _146_375))
in (sncomp_typ tcenv (

let _45_811 = cfg
in {code = c; environment = _45_811.environment; stack = _45_811.stack; close = _45_811.close; steps = _45_811.steps})))
end
| _45_814 -> begin
(norm ())
end)
end else begin
(norm ())
end)))
and sn_args : Prims.bool  ->  FStar_Tc_Env.env  ->  environment  ->  step Prims.list  ->  FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.arg Prims.list = (fun delay tcenv env steps args -> (FStar_All.pipe_right args (FStar_List.map (fun _45_8 -> (match (_45_8) with
| (FStar_Util.Inl (t), imp) when delay -> begin
(let _146_385 = (let _146_384 = (let _146_383 = (sn_delay tcenv (t_config t env steps))
in _146_383.code)
in (FStar_All.pipe_left (fun _146_382 -> FStar_Util.Inl (_146_382)) _146_384))
in ((_146_385), (imp)))
end
| (FStar_Util.Inl (t), imp) -> begin
(let _146_389 = (let _146_388 = (let _146_387 = (sn tcenv (t_config t env steps))
in _146_387.code)
in (FStar_All.pipe_left (fun _146_386 -> FStar_Util.Inl (_146_386)) _146_388))
in ((_146_389), (imp)))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _146_393 = (let _146_392 = (let _146_391 = (wne tcenv (e_config e env steps))
in _146_391.code)
in (FStar_All.pipe_left (fun _146_390 -> FStar_Util.Inr (_146_390)) _146_392))
in ((_146_393), (imp)))
end)))))
and snk : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd config  ->  FStar_Absyn_Syntax.knd config = (fun tcenv cfg -> (

let w = (fun f -> (f cfg.code.FStar_Absyn_Syntax.pos))
in (match ((let _146_403 = (FStar_Absyn_Util.compress_kind cfg.code)
in _146_403.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Kind_delayed (_)) | (FStar_Absyn_Syntax.Kind_lam (_)) -> begin
(failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
cfg
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(

let args = (let _146_404 = (no_eta cfg.steps)
in (sn_args false tcenv cfg.environment _146_404 args))
in (

let _45_850 = cfg
in (let _146_406 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar ((uv), (args))))
in {code = _146_406; environment = _45_850.environment; stack = _45_850.stack; close = _45_850.close; steps = _45_850.steps})))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _45_862; FStar_Absyn_Syntax.pos = _45_860; FStar_Absyn_Syntax.fvs = _45_858; FStar_Absyn_Syntax.uvs = _45_856}) -> begin
(

let _45_871 = (FStar_Tc_Env.lookup_kind_abbrev tcenv l)
in (match (_45_871) with
| (_45_868, binders, body) -> begin
(

let subst = (FStar_Absyn_Util.subst_of_list binders args)
in (let _146_408 = (

let _45_873 = cfg
in (let _146_407 = (FStar_Absyn_Util.subst_kind subst body)
in {code = _146_407; environment = _45_873.environment; stack = _45_873.stack; close = _45_873.close; steps = _45_873.steps}))
in (snk tcenv _146_408)))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_45_876, k) -> begin
(snk tcenv (

let _45_880 = cfg
in {code = k; environment = _45_880.environment; stack = _45_880.stack; close = _45_880.close; steps = _45_880.steps}))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(

let _45_888 = (sn_binders tcenv bs cfg.environment cfg.steps)
in (match (_45_888) with
| (bs, env) -> begin
(

let c2 = (snk tcenv (k_config k env cfg.steps))
in (

let _45_898 = (match (c2.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs', k) -> begin
(((FStar_List.append bs bs')), (k))
end
| _45_895 -> begin
((bs), (c2.code))
end)
in (match (_45_898) with
| (bs, rhs) -> begin
(

let _45_899 = cfg
in (let _146_410 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (rhs))))
in {code = _146_410; environment = _45_899.environment; stack = _45_899.stack; close = _45_899.close; steps = _45_899.steps}))
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

let _45_905 = cfg
in {code = e; environment = _45_905.environment; stack = _45_905.stack; close = _45_905.close; steps = _45_905.steps})
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

let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _45_9 -> (match (_45_9) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _146_419 = (let _146_418 = (let _146_417 = (sn tcenv (t_config t env s'))
in _146_417.code)
in (FStar_All.pipe_left (fun _146_416 -> FStar_Util.Inl (_146_416)) _146_418))
in ((_146_419), (imp)))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _146_423 = (let _146_422 = (let _146_421 = (wne tcenv (e_config v env s'))
in _146_421.code)
in (FStar_All.pipe_left (fun _146_420 -> FStar_Util.Inr (_146_420)) _146_422))
in ((_146_423), (imp)))
end))))
in (

let _45_925 = config
in (let _146_424 = (FStar_Absyn_Syntax.mk_Exp_app ((config.code), (args)) None config.code.FStar_Absyn_Syntax.pos)
in {code = _146_424; environment = _45_925.environment; stack = empty_stack; close = _45_925.close; steps = _45_925.steps}))))
end)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_45_928) -> begin
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
| Some (V (_45_943, (vc, env))) -> begin
(wne tcenv (

let _45_950 = config
in {code = vc; environment = env; stack = _45_950.stack; close = _45_950.close; steps = _45_950.steps}))
end
| _45_953 -> begin
(failwith "Impossible: ill-typed term")
end)
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(

let args = (FStar_List.fold_right (fun a out -> (((a), (config.environment)))::out) args config.stack.args)
in (

let stack = (

let _45_961 = config.stack
in {args = args})
in (wne tcenv (

let _45_964 = config
in {code = head; environment = _45_964.environment; stack = stack; close = _45_964.close; steps = _45_964.steps}))))
end
| FStar_Absyn_Syntax.Exp_abs (binders, body) -> begin
(

let rec beta = (fun entries binders args -> (match (((binders), (args))) with
| ([], _45_976) -> begin
(

let env = (extend_env config.environment entries)
in (wne tcenv (

let _45_979 = config
in {code = body; environment = env; stack = (

let _45_981 = config.stack
in {args = args}); close = _45_979.close; steps = _45_979.steps})))
end
| (_45_984, []) -> begin
(

let env = (extend_env config.environment entries)
in (

let _45_990 = (sn_binders tcenv binders env config.steps)
in (match (_45_990) with
| (binders, env) -> begin
(

let mk_abs = (fun t -> (FStar_Absyn_Syntax.mk_Exp_abs ((binders), (t)) None body.FStar_Absyn_Syntax.pos))
in (

let c = (let _146_436 = (

let _45_993 = config
in (let _146_435 = (no_eta config.steps)
in {code = body; environment = env; stack = (

let _45_995 = config.stack
in {args = []}); close = _45_993.close; steps = _146_435}))
in (wne tcenv _146_436))
in (

let _45_998 = c
in (let _146_437 = (mk_abs c.code)
in {code = _146_437; environment = _45_998.environment; stack = _45_998.stack; close = _45_998.close; steps = _45_998.steps}))))
end)))
end
| ((formal)::rest, (actual)::rest') -> begin
(

let m = (match (((formal), (actual))) with
| ((FStar_Util.Inl (a), _45_1010), ((FStar_Util.Inl (t), _45_1015), env)) -> begin
T (((a.FStar_Absyn_Syntax.v), (((t), (env)))))
end
| ((FStar_Util.Inr (x), _45_1023), ((FStar_Util.Inr (v), _45_1028), env)) -> begin
V (((x.FStar_Absyn_Syntax.v), (((v), (env)))))
end
| _45_1034 -> begin
(let _146_442 = (let _146_441 = (let _146_438 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _146_438))
in (let _146_440 = (FStar_Absyn_Print.binder_to_string formal)
in (let _146_439 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _146_441 _146_440 _146_439))))
in (failwith _146_442))
end)
in (beta ((m)::entries) rest rest'))
end))
in (beta [] binders config.stack.args))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(

let c_e1 = (wne tcenv (

let _45_1040 = config
in {code = e1; environment = _45_1040.environment; stack = empty_stack; close = _45_1040.close; steps = _45_1040.steps}))
in (

let wn_eqn = (fun _45_1047 -> (match (_45_1047) with
| (pat, w, body) -> begin
(

let rec pat_vars = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_disj ((p)::_45_1053) -> begin
(pat_vars p)
end
| FStar_Absyn_Syntax.Pat_cons (_45_1058, _45_1060, pats) -> begin
(FStar_List.collect (fun _45_1067 -> (match (_45_1067) with
| (x, _45_1066) -> begin
(pat_vars x)
end)) pats)
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _146_448 = (FStar_Absyn_Syntax.v_binder x)
in (_146_448)::[])
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _146_449 = (FStar_Absyn_Syntax.t_binder a)
in (_146_449)::[])
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

let _45_1091 = x
in {FStar_Absyn_Syntax.v = _45_1091.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t.code; FStar_Absyn_Syntax.p = _45_1091.FStar_Absyn_Syntax.p})))
in (

let norm_btvar = (fun a -> (

let k = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort config.environment config.steps))
in (

let _45_1096 = a
in {FStar_Absyn_Syntax.v = _45_1096.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k.code; FStar_Absyn_Syntax.p = _45_1096.FStar_Absyn_Syntax.p})))
in (

let rec norm_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (pats) -> begin
(let _146_457 = (let _146_456 = (FStar_List.map norm_pat pats)
in FStar_Absyn_Syntax.Pat_disj (_146_456))
in (FStar_Absyn_Util.withinfo _146_457 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _146_462 = (let _146_461 = (let _146_460 = (FStar_List.map (fun _45_1109 -> (match (_45_1109) with
| (x, i) -> begin
(let _146_459 = (norm_pat x)
in ((_146_459), (i)))
end)) pats)
in ((fv), (q), (_146_460)))
in FStar_Absyn_Syntax.Pat_cons (_146_461))
in (FStar_Absyn_Util.withinfo _146_462 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _146_464 = (let _146_463 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_var (_146_463))
in (FStar_Absyn_Util.withinfo _146_464 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _146_466 = (let _146_465 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_tvar (_146_465))
in (FStar_Absyn_Util.withinfo _146_466 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let _146_468 = (let _146_467 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_wild (_146_467))
in (FStar_Absyn_Util.withinfo _146_468 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let _146_470 = (let _146_469 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_twild (_146_469))
in (FStar_Absyn_Util.withinfo _146_470 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_constant (_45_1119) -> begin
p
end
| FStar_Absyn_Syntax.Pat_dot_term (x, e) -> begin
(

let e = (wne tcenv (e_config e config.environment config.steps))
in (let _146_473 = (let _146_472 = (let _146_471 = (norm_bvvar x)
in ((_146_471), (e.code)))
in FStar_Absyn_Syntax.Pat_dot_term (_146_472))
in (FStar_Absyn_Util.withinfo _146_473 None p.FStar_Absyn_Syntax.p)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
(

let t = (sn tcenv (t_config t config.environment config.steps))
in (let _146_476 = (let _146_475 = (let _146_474 = (norm_btvar a)
in ((_146_474), (t.code)))
in FStar_Absyn_Syntax.Pat_dot_typ (_146_475))
in (FStar_Absyn_Util.withinfo _146_476 None p.FStar_Absyn_Syntax.p)))
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

let _45_1144 = config
in {code = w; environment = env; stack = empty_stack; close = _45_1144.close; steps = _45_1144.steps}))
in Some (c_w.code))
end)
in (

let c_body = (wne tcenv (

let _45_1148 = config
in {code = body; environment = env; stack = empty_stack; close = _45_1148.close; steps = _45_1148.steps}))
in (let _146_479 = (norm_pat pat)
in ((_146_479), (w), (c_body.code))))))))))))
end))
in (

let eqns = (FStar_List.map wn_eqn eqns)
in (

let e = (FStar_Absyn_Syntax.mk_Exp_match ((c_e1.code), (eqns)) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (

let _45_1153 = config
in {code = e; environment = _45_1153.environment; stack = _45_1153.stack; close = _45_1153.close; steps = _45_1153.steps}) rebuild)))))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), body) -> begin
(

let _45_1185 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _45_1163 _45_1168 -> (match (((_45_1163), (_45_1168))) with
| ((env, lbs), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = eff; FStar_Absyn_Syntax.lbdef = e}) -> begin
(

let c = (wne tcenv (

let _45_1169 = config
in {code = e; environment = _45_1169.environment; stack = empty_stack; close = _45_1169.close; steps = _45_1169.steps}))
in (

let t = (sn tcenv (t_config t config.environment config.steps))
in (

let _45_1182 = (match (x) with
| FStar_Util.Inl (x) -> begin
(

let y = (let _146_482 = if is_rec then begin
x
end else begin
(FStar_Absyn_Util.freshen_bvd x)
end
in (FStar_Absyn_Util.bvd_to_bvar_s _146_482 t.code))
in (

let yexp = (FStar_Absyn_Util.bvar_to_exp y)
in (

let y_for_x = V (((x), (((yexp), (empty_env)))))
in ((FStar_Util.Inl (y.FStar_Absyn_Syntax.v)), ((extend_env' env y_for_x))))))
end
| _45_1179 -> begin
((x), (env))
end)
in (match (_45_1182) with
| (y, env) -> begin
(let _146_484 = (let _146_483 = (FStar_Absyn_Syntax.mk_lb ((y), (eff), (t.code), (c.code)))
in (_146_483)::lbs)
in ((env), (_146_484)))
end))))
end)) ((config.environment), ([]))))
in (match (_45_1185) with
| (env, lbs) -> begin
(

let lbs = (FStar_List.rev lbs)
in (

let c_body = (wne tcenv (

let _45_1187 = config
in {code = body; environment = env; stack = empty_stack; close = _45_1187.close; steps = _45_1187.steps}))
in (

let e = (FStar_Absyn_Syntax.mk_Exp_let ((((is_rec), (lbs))), (c_body.code)) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (

let _45_1191 = config
in {code = e; environment = _45_1191.environment; stack = _45_1191.stack; close = _45_1191.close; steps = _45_1191.steps}) rebuild))))
end))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, l) -> begin
(

let c = (wne tcenv (

let _45_1198 = config
in {code = e; environment = _45_1198.environment; stack = _45_1198.stack; close = _45_1198.close; steps = _45_1198.steps}))
in if (is_stack_empty config) then begin
(

let t = (sn tcenv (t_config t config.environment config.steps))
in (let _146_486 = (

let _45_1202 = config
in (let _146_485 = (FStar_Absyn_Syntax.mk_Exp_ascribed ((c.code), (t.code), (l)) None e.FStar_Absyn_Syntax.pos)
in {code = _146_485; environment = _45_1202.environment; stack = _45_1202.stack; close = _45_1202.close; steps = _45_1202.steps}))
in (rebuild _146_486)))
end else begin
c
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, info)) -> begin
(

let c = (wne tcenv (

let _45_1209 = config
in {code = e; environment = _45_1209.environment; stack = _45_1209.stack; close = _45_1209.close; steps = _45_1209.steps}))
in if (is_stack_empty config) then begin
(let _146_488 = (

let _45_1212 = config
in (let _146_487 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((c.code), (info)))))
in {code = _146_487; environment = _45_1212.environment; stack = _45_1212.stack; close = _45_1212.close; steps = _45_1212.steps}))
in (rebuild _146_488))
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


let norm_sigelt : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt = (fun tcenv _45_10 -> (match (_45_10) with
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, b) -> begin
(

let e = (let _146_512 = (let _146_511 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None r)
in ((lbs), (_146_511)))
in (FStar_Absyn_Syntax.mk_Exp_let _146_512 None r))
in (

let e = (norm_exp ((Beta)::[]) tcenv e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_let (lbs, _45_1238) -> begin
FStar_Absyn_Syntax.Sig_let (((lbs), (r), (l), (b)))
end
| _45_1242 -> begin
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
(let _146_517 = (eta_expand tcenv t)
in (FStar_All.pipe_right _146_517 FStar_Absyn_Util.compress_typ))
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


let exp_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  Prims.string = (fun tcenv e -> (let _146_540 = (norm_exp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv e)
in (FStar_Absyn_Print.exp_to_string _146_540)))


let typ_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun tcenv t -> (let _146_545 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv t)
in (FStar_Absyn_Print.typ_to_string _146_545)))


let kind_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun tcenv k -> (let _146_550 = (norm_kind ((Beta)::(SNComp)::(Unmeta)::[]) tcenv k)
in (FStar_Absyn_Print.kind_to_string _146_550)))


let formula_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun tcenv f -> (let _146_555 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv f)
in (FStar_Absyn_Print.formula_to_string _146_555)))


let comp_typ_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  Prims.string = (fun tcenv c -> (let _146_560 = (norm_comp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv c)
in (FStar_Absyn_Print.comp_typ_to_string _146_560)))


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
(let _146_575 = (let _146_574 = (let _146_573 = (let _146_572 = (let _146_571 = (let _146_570 = (let _146_569 = (FStar_Absyn_Util.bvar_to_exp y)
in ((x.FStar_Absyn_Syntax.v), (_146_569)))
in FStar_Util.Inr (_146_570))
in (_146_571)::[])
in (FStar_Absyn_Util.subst_typ _146_572 phi))
in (FStar_Absyn_Util.mk_conj phi1 _146_573))
in ((y), (_146_574)))
in (FStar_Absyn_Syntax.mk_Typ_refine _146_575 (Some (FStar_Absyn_Syntax.ktype)) t0.FStar_Absyn_Syntax.pos))
end
| _45_1351 -> begin
t
end))
end
| _45_1353 -> begin
t
end)))
in (aux t))))




