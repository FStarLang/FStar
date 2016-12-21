
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


let is_Mkconfig = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkconfig"))))


let is_Mkenvironment : environment  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenvironment"))))


let is_Mkstack : stack  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkstack"))))


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
| T (_43_26) -> begin
_43_26
end))


let ___V____0 = (fun projectee -> (match (projectee) with
| V (_43_29) -> begin
_43_29
end))


let empty_env : environment = {context = []; label_suffix = []}


let extend_env' : environment  ->  env_entry  ->  environment = (fun env b -> (

let _43_32 = env
in {context = (b)::env.context; label_suffix = _43_32.label_suffix}))


let extend_env : environment  ->  env_entry Prims.list  ->  environment = (fun env bindings -> (

let _43_36 = env
in {context = (FStar_List.append bindings env.context); label_suffix = _43_36.label_suffix}))


let lookup_env : environment  ->  Prims.string  ->  env_entry Prims.option = (fun env key -> (FStar_All.pipe_right env.context (FStar_Util.find_opt (fun _43_1 -> (match (_43_1) with
| T (a, _43_43) -> begin
(a.FStar_Absyn_Syntax.realname.FStar_Ident.idText = key)
end
| V (x, _43_48) -> begin
(x.FStar_Absyn_Syntax.realname.FStar_Ident.idText = key)
end)))))


let fold_env = (fun env f acc -> (FStar_List.fold_left (fun acc v -> (match (v) with
| T (a, _43_58) -> begin
(f a.FStar_Absyn_Syntax.realname.FStar_Ident.idText v acc)
end
| V (x, _43_63) -> begin
(f x.FStar_Absyn_Syntax.realname.FStar_Ident.idText v acc)
end)) acc env.context))


let empty_stack : stack = {args = []}


let rec subst_of_env' : environment  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list = (fun env -> (fold_env env (fun _43_67 v acc -> (match (v) with
| T (a, (t, env')) -> begin
(let _140_113 = (let _140_112 = (let _140_111 = (let _140_110 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_typ _140_110 t))
in ((a), (_140_111)))
in FStar_Util.Inl (_140_112))
in (_140_113)::acc)
end
| V (x, (v, env')) -> begin
(let _140_117 = (let _140_116 = (let _140_115 = (let _140_114 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_exp _140_114 v))
in ((x), (_140_115)))
in FStar_Util.Inr (_140_116))
in (_140_117)::acc)
end)) []))


let subst_of_env = (fun tcenv env -> (subst_of_env' env))


let with_new_code = (fun c e -> {code = e; environment = c.environment; stack = empty_stack; close = None; steps = c.steps})


let rec eta_expand : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun tcenv t -> (

let k = (let _140_127 = (FStar_Tc_Recheck.recompute_kind t)
in (FStar_All.pipe_right _140_127 FStar_Absyn_Util.compress_kind))
in (

let rec aux = (fun t k -> (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
t
end
| FStar_Absyn_Syntax.Kind_abbrev (_43_99, k) -> begin
(aux t k)
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k') -> begin
(match ((let _140_132 = (FStar_Absyn_Util.unascribe_typ t)
in _140_132.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam (real, body) -> begin
(

let rec aux = (fun real expected -> (match (((real), (expected))) with
| ((_43_116)::real, (_43_120)::expected) -> begin
(aux real expected)
end
| ([], []) -> begin
t
end
| ((_43_129)::_43_127, []) -> begin
(FStar_All.failwith "Ill-kinded type")
end
| ([], more) -> begin
(

let _43_138 = (FStar_Absyn_Util.args_of_binders more)
in (match (_43_138) with
| (more, args) -> begin
(

let body = (FStar_Absyn_Syntax.mk_Typ_app ((body), (args)) None body.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_List.append binders more)), (body)) None body.FStar_Absyn_Syntax.pos))
end))
end))
in (aux real binders))
end
| _43_141 -> begin
(

let _43_144 = (FStar_Absyn_Util.args_of_binders binders)
in (match (_43_144) with
| (binders, args) -> begin
(

let body = (FStar_Absyn_Syntax.mk_Typ_app ((t), (args)) None t.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_lam ((binders), (body)) None t.FStar_Absyn_Syntax.pos))
end))
end)
end
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_delayed (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _140_140 = (let _140_139 = (let _140_137 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _140_137 FStar_Range.string_of_range))
in (let _140_138 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "%s: Impossible: Kind_unknown: %s" _140_139 _140_138)))
in (FStar_All.failwith _140_140))
end))
in (aux t k))))


let is_var : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((FStar_Absyn_Util.compress_typ t)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (_43_163); FStar_Absyn_Syntax.tk = _43_161; FStar_Absyn_Syntax.pos = _43_159; FStar_Absyn_Syntax.fvs = _43_157; FStar_Absyn_Syntax.uvs = _43_155} -> begin
true
end
| _43_167 -> begin
false
end))


let rec eta_expand_exp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp = (fun tcenv e -> (

let t = (let _140_147 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_All.pipe_right _140_147 FStar_Absyn_Util.compress_typ))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((let _140_148 = (FStar_Absyn_Util.compress_exp e)
in _140_148.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
if ((FStar_List.length bs) = (FStar_List.length bs')) then begin
e
end else begin
(FStar_All.failwith "NYI")
end
end
| _43_180 -> begin
(

let _43_183 = (FStar_Absyn_Util.args_of_binders bs)
in (match (_43_183) with
| (bs, args) -> begin
(let _140_150 = (let _140_149 = (FStar_Absyn_Syntax.mk_Exp_app ((e), (args)) None e.FStar_Absyn_Syntax.pos)
in ((bs), (_140_149)))
in (FStar_Absyn_Syntax.mk_Exp_abs _140_150 (Some (t)) e.FStar_Absyn_Syntax.pos))
end))
end)
end
| _43_185 -> begin
e
end)))


let no_eta : step Prims.list  ->  step Prims.list = (fun s -> (FStar_All.pipe_right s (FStar_List.filter (fun _43_2 -> (match (_43_2) with
| Eta -> begin
false
end
| _43_190 -> begin
true
end)))))


let no_eta_cfg = (fun c -> (

let _43_192 = c
in (let _140_155 = (no_eta c.steps)
in {code = _43_192.code; environment = _43_192.environment; stack = _43_192.stack; close = _43_192.close; steps = _140_155})))


let whnf_only = (fun config -> (FStar_All.pipe_right config.steps (FStar_List.contains WHNF)))


let unmeta = (fun config -> (FStar_All.pipe_right config.steps (FStar_List.contains Unmeta)))


let unlabel = (fun config -> ((unmeta config) || (FStar_All.pipe_right config.steps (FStar_List.contains Unlabel))))


let is_stack_empty = (fun config -> (match (config.stack.args) with
| [] -> begin
true
end
| _43_200 -> begin
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

let binders' = (FStar_List.map (fun _43_3 -> (match (_43_3) with
| (FStar_Util.Inl (b), imp) -> begin
(let _140_167 = (let _140_166 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inl (_140_166))
in ((_140_167), (imp)))
end
| (FStar_Util.Inr (b), imp) -> begin
(let _140_169 = (let _140_168 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inr (_140_168))
in ((_140_169), (imp)))
end)) binders)
in (

let subst = (let _140_171 = (let _140_170 = (FStar_Absyn_Util.args_of_binders binders')
in (FStar_All.pipe_right _140_170 Prims.snd))
in (FStar_Absyn_Util.subst_of_list binders _140_171))
in (

let cdef = (FStar_Absyn_Util.subst_comp subst cdef)
in (

let subst = (let _140_173 = (let _140_172 = (FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ)
in (_140_172)::c.FStar_Absyn_Syntax.effect_args)
in (FStar_Absyn_Util.subst_of_list binders' _140_173))
in (

let c1 = (FStar_Absyn_Util.subst_comp subst cdef)
in (

let c = (FStar_All.pipe_right (

let _43_224 = (FStar_Absyn_Util.comp_to_comp_typ c1)
in {FStar_Absyn_Syntax.effect_name = _43_224.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _43_224.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _43_224.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = c.FStar_Absyn_Syntax.flags}) FStar_Absyn_Syntax.mk_Comp)
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


let rec is_head_symbol : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _140_204 = (FStar_Absyn_Util.compress_typ t)
in _140_204.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _43_255, _43_257)) -> begin
(is_head_symbol t)
end
| _43_262 -> begin
false
end))


let simplify_then_apply : step Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.args  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ = (fun steps head args pos -> (

let fallback = (fun _43_268 -> (match (()) with
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
| _43_276 -> begin
None
end))
in (

let simplify = (fun arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (t) -> begin
(((simp_t t)), (arg))
end
| _43_282 -> begin
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
| _43_329 -> begin
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
| _43_374 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
FStar_Absyn_Util.t_true
end
| ((Some (true), _43_402))::((_43_392, (FStar_Util.Inl (arg), _43_396)))::[] -> begin
arg
end
| _43_406 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _43_410))::[] -> begin
FStar_Absyn_Util.t_false
end
| ((Some (false), _43_416))::[] -> begin
FStar_Absyn_Util.t_true
end
| _43_420 -> begin
(fallback ())
end)
end else begin
if ((((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.forall_lid) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid)) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exists_lid)) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) then begin
(match (args) with
| (((FStar_Util.Inl (t), _))::[]) | ((_)::((FStar_Util.Inl (t), _))::[]) -> begin
(match ((let _140_219 = (FStar_Absyn_Util.compress_typ t)
in _140_219.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam ((_43_435)::[], body) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
FStar_Absyn_Util.t_true
end
| Some (false) -> begin
FStar_Absyn_Util.t_false
end
| _43_445 -> begin
(fallback ())
end)
end
| _43_447 -> begin
(fallback ())
end)
end
| _43_449 -> begin
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
| _43_451 -> begin
(fallback ())
end)
end))))


let rec sn_delay : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ config  ->  FStar_Absyn_Syntax.typ config = (fun tcenv cfg -> (

let aux = (fun _43_455 -> (match (()) with
| () -> begin
(let _140_245 = (sn tcenv cfg)
in _140_245.code)
end))
in (

let t = (FStar_Absyn_Syntax.mk_Typ_delayed' (FStar_Util.Inr (aux)) None cfg.code.FStar_Absyn_Syntax.pos)
in (

let _43_457 = cfg
in {code = t; environment = _43_457.environment; stack = empty_stack; close = _43_457.close; steps = _43_457.steps}))))
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

let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _43_4 -> (match (_43_4) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _140_257 = (let _140_256 = (let _140_255 = (sn tcenv (t_config t env s'))
in _140_255.code)
in (FStar_All.pipe_left (fun _140_254 -> FStar_Util.Inl (_140_254)) _140_256))
in ((_140_257), (imp)))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _140_261 = (let _140_260 = (let _140_259 = (wne tcenv (e_config v env s'))
in _140_259.code)
in (FStar_All.pipe_left (fun _140_258 -> FStar_Util.Inr (_140_258)) _140_260))
in ((_140_261), (imp)))
end))))
in (

let t = (simplify_then_apply config.steps config.code args config.code.FStar_Absyn_Syntax.pos)
in (

let _43_481 = config
in {code = t; environment = _43_481.environment; stack = empty_stack; close = _43_481.close; steps = _43_481.steps}))))
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

let _43_488 = config
in (let _140_263 = (eta_expand tcenv t)
in {code = _140_263; environment = _43_488.environment; stack = _43_488.stack; close = _43_488.close; steps = _43_488.steps}))
end else begin
(

let _43_490 = config
in {code = t; environment = _43_490.environment; stack = _43_490.stack; close = _43_490.close; steps = _43_490.steps})
end))))
in (

let wk = (fun f -> (match ((FStar_ST.read cfg.code.FStar_Absyn_Syntax.tk)) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _43_501; FStar_Absyn_Syntax.pos = _43_499; FStar_Absyn_Syntax.fvs = _43_497; FStar_Absyn_Syntax.uvs = _43_495}) -> begin
(f (Some (FStar_Absyn_Syntax.ktype)) cfg.code.FStar_Absyn_Syntax.pos)
end
| _43_506 -> begin
(f None cfg.code.FStar_Absyn_Syntax.pos)
end))
in (

let config = (

let _43_507 = cfg
in (let _140_276 = (FStar_Absyn_Util.compress_typ cfg.code)
in {code = _140_276; environment = _43_507.environment; stack = _43_507.stack; close = _43_507.close; steps = _43_507.steps}))
in (match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_43_511) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_uvar (_43_514) -> begin
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

let _43_522 = config
in {code = t; environment = _43_522.environment; stack = _43_522.stack; close = _43_522.close; steps = _43_522.steps}))
end))
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(match ((lookup_env config.environment a.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname.FStar_Ident.idText)) with
| None -> begin
(rebuild config)
end
| Some (T (_43_528, (t, e))) -> begin
(sn tcenv (

let _43_535 = config
in {code = t; environment = e; stack = _43_535.stack; close = _43_535.close; steps = _43_535.steps}))
end
| _43_538 -> begin
(FStar_All.failwith "Impossible: expected a type")
end)
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(

let args = (FStar_List.fold_right (fun a out -> (((a), (config.environment)))::out) args config.stack.args)
in (

let stack = (

let _43_546 = config.stack
in {args = args})
in (sn tcenv (

let _43_549 = config
in {code = head; environment = _43_549.environment; stack = stack; close = _43_549.close; steps = _43_549.steps}))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(match (config.stack.args) with
| [] -> begin
(

let _43_558 = (sn_binders tcenv binders config.environment config.steps)
in (match (_43_558) with
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

let t2_cfg = (let _140_289 = (let _140_288 = (no_eta config.steps)
in {code = t2; environment = environment; stack = empty_stack; close = None; steps = _140_288})
in (sn_delay tcenv _140_289))
in (

let _43_566 = t2_cfg
in (let _140_290 = (mk_lam t2_cfg.code)
in {code = _140_290; environment = _43_566.environment; stack = _43_566.stack; close = _43_566.close; steps = _43_566.steps}))))
end))
end
| args -> begin
(

let rec beta = (fun env_entries binders args -> (match (((binders), (args))) with
| ([], _43_575) -> begin
(

let env = (extend_env config.environment env_entries)
in (sn tcenv (

let _43_578 = config
in {code = t2; environment = env; stack = (

let _43_580 = config.stack
in {args = args}); close = _43_578.close; steps = _43_578.steps})))
end
| (_43_583, []) -> begin
(

let t = (FStar_Absyn_Syntax.mk_Typ_lam ((binders), (t2)) None t2.FStar_Absyn_Syntax.pos)
in (

let env = (extend_env config.environment env_entries)
in (sn tcenv (

let _43_588 = config
in {code = t; environment = env; stack = empty_stack; close = _43_588.close; steps = _43_588.steps}))))
end
| ((formal)::rest, (actual)::rest') -> begin
(

let m = (match (((formal), (actual))) with
| ((FStar_Util.Inl (a), _43_600), ((FStar_Util.Inl (t), _43_605), env)) -> begin
T (((a.FStar_Absyn_Syntax.v), (((t), (env)))))
end
| ((FStar_Util.Inr (x), _43_613), ((FStar_Util.Inr (v), _43_618), env)) -> begin
V (((x.FStar_Absyn_Syntax.v), (((v), (env)))))
end
| _43_624 -> begin
(let _140_301 = (let _140_300 = (let _140_297 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _140_297))
in (let _140_299 = (FStar_Absyn_Print.binder_to_string formal)
in (let _140_298 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _140_300 _140_299 _140_298))))
in (FStar_All.failwith _140_301))
end)
in (beta ((m)::env_entries) rest rest'))
end))
in (beta [] binders args))
end)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _43_628) -> begin
(sn tcenv (

let _43_631 = config
in {code = t; environment = _43_631.environment; stack = _43_631.stack; close = _43_631.close; steps = _43_631.steps}))
end
| _43_634 -> begin
(match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, comp) -> begin
(

let _43_641 = (sn_binders tcenv bs config.environment config.steps)
in (match (_43_641) with
| (binders, environment) -> begin
(

let c2 = (sncomp tcenv (c_config comp environment config.steps))
in (let _140_305 = (

let _43_643 = config
in (let _140_304 = (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_fun ((binders), (c2.code))))
in {code = _140_304; environment = _43_643.environment; stack = _43_643.stack; close = _43_643.close; steps = _43_643.steps}))
in (rebuild _140_305)))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((let _140_307 = (let _140_306 = (FStar_Absyn_Syntax.v_binder x)
in (_140_306)::[])
in (sn_binders tcenv _140_307 config.environment config.steps))) with
| (((FStar_Util.Inr (x), _43_652))::[], env) -> begin
(

let refine = (fun t -> (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_refine ((x), (t)))))
in (let _140_314 = (let _140_313 = (FStar_All.pipe_right config.steps (FStar_List.filter (fun _43_5 -> (match (_43_5) with
| UnfoldOpaque -> begin
false
end
| _43_662 -> begin
true
end))))
in {code = t; environment = env; stack = empty_stack; close = (close_with_config config refine); steps = _140_313})
in (sn tcenv _140_314)))
end
| _43_664 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
if (unmeta config) then begin
(sn tcenv (

let _43_670 = config
in {code = t; environment = _43_670.environment; stack = _43_670.stack; close = _43_670.close; steps = _43_670.steps}))
end else begin
(

let pat = (fun t -> (

let ps = (FStar_All.pipe_right ps (FStar_List.map (sn_args true tcenv config.environment config.steps)))
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern (((t), (ps))))))))
in (sn tcenv (

let _43_675 = config
in {code = t; environment = _43_675.environment; stack = _43_675.stack; close = (close_with_config config pat); steps = _43_675.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, b)) -> begin
if (unlabel config) then begin
(sn tcenv (

let _43_684 = config
in {code = t; environment = _43_684.environment; stack = _43_684.stack; close = _43_684.close; steps = _43_684.steps}))
end else begin
(

let lab = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when ((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) && (FStar_All.pipe_right config.steps (FStar_List.contains Simplify))) -> begin
t
end
| _43_691 -> begin
(match (config.environment.label_suffix) with
| ((b', sfx))::_43_693 -> begin
if ((b' = None) || (Some (b) = b')) then begin
(

let _43_698 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _140_321 = (FStar_Range.string_of_range sfx)
in (FStar_Util.print2 "Stripping label %s because of enclosing refresh %s\n" l _140_321))
end else begin
()
end
in t)
end else begin
(

let _43_700 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _140_322 = (FStar_Range.string_of_range sfx)
in (FStar_Util.print1 "Normalizer refreshing label: %s\n" _140_322))
end else begin
()
end
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled (((t), (l), (sfx), (b)))))))
end
end
| _43_703 -> begin
(FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled (((t), (l), (r), (b))))))
end)
end))
in (sn tcenv (

let _43_704 = config
in {code = t; environment = _43_704.environment; stack = _43_704.stack; close = (close_with_config config lab); steps = _43_704.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
if (unmeta config) then begin
(sn tcenv (

let _43_712 = config
in {code = t; environment = _43_712.environment; stack = _43_712.stack; close = _43_712.close; steps = _43_712.steps}))
end else begin
(

let sfx = (match (b) with
| Some (false) -> begin
r
end
| _43_717 -> begin
FStar_Absyn_Syntax.dummyRange
end)
in (

let config = (

let _43_719 = config
in {code = t; environment = (

let _43_721 = config.environment
in {context = _43_721.context; label_suffix = (((b), (sfx)))::config.environment.label_suffix}); stack = _43_719.stack; close = _43_719.close; steps = _43_719.steps})
in (sn tcenv config)))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
if (FStar_ST.read flag) then begin
(let _140_328 = (

let _43_730 = config
in (let _140_327 = (FStar_Absyn_Util.mk_conj t1 t2)
in {code = _140_327; environment = _43_730.environment; stack = _43_730.stack; close = _43_730.close; steps = _43_730.steps}))
in (sn tcenv _140_328))
end else begin
(

let c1 = (sn tcenv (t_config t1 config.environment config.steps))
in (

let c2 = (sn tcenv (t_config t2 config.environment config.steps))
in (let _140_330 = (

let _43_734 = config
in (let _140_329 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (((c1.code), (c2.code), (flag)))))
in {code = _140_329; environment = _43_734.environment; stack = _43_734.stack; close = _43_734.close; steps = _43_734.steps}))
in (rebuild _140_330))))
end
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_))) | (FStar_Absyn_Syntax.Typ_unknown) | (_) -> begin
(let _140_335 = (let _140_334 = (let _140_331 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _140_331 FStar_Range.string_of_range))
in (let _140_333 = (FStar_Absyn_Print.tag_of_typ config.code)
in (let _140_332 = (FStar_Absyn_Print.typ_to_string config.code)
in (FStar_Util.format3 "(%s) Unexpected type (%s): %s" _140_334 _140_333 _140_332))))
in (FStar_All.failwith _140_335))
end)
end)))))
and sn_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  environment  ->  step Prims.list  ->  (FStar_Absyn_Syntax.binders * environment) = (fun tcenv binders env steps -> (

let rec aux = (fun out env _43_6 -> (match (_43_6) with
| ((FStar_Util.Inl (a), imp))::rest -> begin
(

let c = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort env steps))
in (

let b = (let _140_346 = (FStar_Absyn_Util.freshen_bvd a.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _140_346 c.code))
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

let y = (let _140_347 = (FStar_Absyn_Util.freshen_bvd x.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _140_347 c.code))
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

let _43_778 = cfg
in (let _140_350 = (FStar_Absyn_Syntax.mk_Comp ctconf.code)
in {code = _140_350; environment = _43_778.environment; stack = _43_778.stack; close = _43_778.close; steps = _43_778.steps})))
end
| FStar_Absyn_Syntax.Total (t) -> begin
if (FStar_List.contains DeltaComp cfg.steps) then begin
(let _140_354 = (let _140_353 = (let _140_352 = (let _140_351 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_Absyn_Util.comp_to_comp_typ _140_351))
in (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp _140_352))
in (with_new_code cfg _140_353))
in (FStar_All.pipe_left (sncomp tcenv) _140_354))
end else begin
(

let t = (sn tcenv (with_new_code cfg t))
in (let _140_355 = (FStar_Absyn_Syntax.mk_Total t.code)
in (with_new_code cfg _140_355)))
end
end)))
and sncomp_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp_typ config  ->  FStar_Absyn_Syntax.comp_typ config = (fun tcenv cfg -> (

let m = cfg.code
in (

let norm = (fun _43_787 -> (match (()) with
| () -> begin
(

let remake = (fun l r eargs flags -> (

let c = {FStar_Absyn_Syntax.effect_name = l; FStar_Absyn_Syntax.result_typ = r; FStar_Absyn_Syntax.effect_args = eargs; FStar_Absyn_Syntax.flags = flags}
in (

let _43_794 = cfg
in {code = c; environment = _43_794.environment; stack = _43_794.stack; close = _43_794.close; steps = _43_794.steps})))
in (

let res = (let _140_368 = (sn tcenv (with_new_code cfg m.FStar_Absyn_Syntax.result_typ))
in _140_368.code)
in (

let sn_flags = (fun flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _43_7 -> (match (_43_7) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(

let e = (let _140_372 = (wne tcenv (e_config e cfg.environment cfg.steps))
in _140_372.code)
in FStar_Absyn_Syntax.DECREASES (e))
end
| f -> begin
f
end)))))
in (

let _43_806 = (let _140_374 = (sn_flags m.FStar_Absyn_Syntax.flags)
in (let _140_373 = (sn_args true tcenv cfg.environment cfg.steps m.FStar_Absyn_Syntax.effect_args)
in ((_140_374), (_140_373))))
in (match (_43_806) with
| (flags, args) -> begin
(remake m.FStar_Absyn_Syntax.effect_name res args flags)
end)))))
end))
in if (FStar_List.contains DeltaComp cfg.steps) then begin
(match ((FStar_Tc_Env.lookup_effect_abbrev tcenv m.FStar_Absyn_Syntax.effect_name)) with
| Some (_43_808) -> begin
(

let c = (let _140_375 = (FStar_Absyn_Syntax.mk_Comp m)
in (weak_norm_comp tcenv _140_375))
in (sncomp_typ tcenv (

let _43_811 = cfg
in {code = c; environment = _43_811.environment; stack = _43_811.stack; close = _43_811.close; steps = _43_811.steps})))
end
| _43_814 -> begin
(norm ())
end)
end else begin
(norm ())
end)))
and sn_args : Prims.bool  ->  FStar_Tc_Env.env  ->  environment  ->  step Prims.list  ->  FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.arg Prims.list = (fun delay tcenv env steps args -> (FStar_All.pipe_right args (FStar_List.map (fun _43_8 -> (match (_43_8) with
| (FStar_Util.Inl (t), imp) when delay -> begin
(let _140_385 = (let _140_384 = (let _140_383 = (sn_delay tcenv (t_config t env steps))
in _140_383.code)
in (FStar_All.pipe_left (fun _140_382 -> FStar_Util.Inl (_140_382)) _140_384))
in ((_140_385), (imp)))
end
| (FStar_Util.Inl (t), imp) -> begin
(let _140_389 = (let _140_388 = (let _140_387 = (sn tcenv (t_config t env steps))
in _140_387.code)
in (FStar_All.pipe_left (fun _140_386 -> FStar_Util.Inl (_140_386)) _140_388))
in ((_140_389), (imp)))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _140_393 = (let _140_392 = (let _140_391 = (wne tcenv (e_config e env steps))
in _140_391.code)
in (FStar_All.pipe_left (fun _140_390 -> FStar_Util.Inr (_140_390)) _140_392))
in ((_140_393), (imp)))
end)))))
and snk : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd config  ->  FStar_Absyn_Syntax.knd config = (fun tcenv cfg -> (

let w = (fun f -> (f cfg.code.FStar_Absyn_Syntax.pos))
in (match ((let _140_403 = (FStar_Absyn_Util.compress_kind cfg.code)
in _140_403.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Kind_delayed (_)) | (FStar_Absyn_Syntax.Kind_lam (_)) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
cfg
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(

let args = (let _140_404 = (no_eta cfg.steps)
in (sn_args false tcenv cfg.environment _140_404 args))
in (

let _43_850 = cfg
in (let _140_406 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar ((uv), (args))))
in {code = _140_406; environment = _43_850.environment; stack = _43_850.stack; close = _43_850.close; steps = _43_850.steps})))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _43_862; FStar_Absyn_Syntax.pos = _43_860; FStar_Absyn_Syntax.fvs = _43_858; FStar_Absyn_Syntax.uvs = _43_856}) -> begin
(

let _43_871 = (FStar_Tc_Env.lookup_kind_abbrev tcenv l)
in (match (_43_871) with
| (_43_868, binders, body) -> begin
(

let subst = (FStar_Absyn_Util.subst_of_list binders args)
in (let _140_408 = (

let _43_873 = cfg
in (let _140_407 = (FStar_Absyn_Util.subst_kind subst body)
in {code = _140_407; environment = _43_873.environment; stack = _43_873.stack; close = _43_873.close; steps = _43_873.steps}))
in (snk tcenv _140_408)))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_43_876, k) -> begin
(snk tcenv (

let _43_880 = cfg
in {code = k; environment = _43_880.environment; stack = _43_880.stack; close = _43_880.close; steps = _43_880.steps}))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(

let _43_888 = (sn_binders tcenv bs cfg.environment cfg.steps)
in (match (_43_888) with
| (bs, env) -> begin
(

let c2 = (snk tcenv (k_config k env cfg.steps))
in (

let _43_898 = (match (c2.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs', k) -> begin
(((FStar_List.append bs bs')), (k))
end
| _43_895 -> begin
((bs), (c2.code))
end)
in (match (_43_898) with
| (bs, rhs) -> begin
(

let _43_899 = cfg
in (let _140_410 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (rhs))))
in {code = _140_410; environment = _43_899.environment; stack = _43_899.stack; close = _43_899.close; steps = _43_899.steps}))
end)))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(FStar_All.failwith "Impossible")
end)))
and wne : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp config  ->  FStar_Absyn_Syntax.exp config = (fun tcenv cfg -> (

let e = (FStar_Absyn_Util.compress_exp cfg.code)
in (

let config = (

let _43_905 = cfg
in {code = e; environment = _43_905.environment; stack = _43_905.stack; close = _43_905.close; steps = _43_905.steps})
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

let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _43_9 -> (match (_43_9) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _140_419 = (let _140_418 = (let _140_417 = (sn tcenv (t_config t env s'))
in _140_417.code)
in (FStar_All.pipe_left (fun _140_416 -> FStar_Util.Inl (_140_416)) _140_418))
in ((_140_419), (imp)))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _140_423 = (let _140_422 = (let _140_421 = (wne tcenv (e_config v env s'))
in _140_421.code)
in (FStar_All.pipe_left (fun _140_420 -> FStar_Util.Inr (_140_420)) _140_422))
in ((_140_423), (imp)))
end))))
in (

let _43_925 = config
in (let _140_424 = (FStar_Absyn_Syntax.mk_Exp_app ((config.code), (args)) None config.code.FStar_Absyn_Syntax.pos)
in {code = _140_424; environment = _43_925.environment; stack = empty_stack; close = _43_925.close; steps = _43_925.steps}))))
end)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_43_928) -> begin
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
| Some (V (_43_943, (vc, env))) -> begin
(wne tcenv (

let _43_950 = config
in {code = vc; environment = env; stack = _43_950.stack; close = _43_950.close; steps = _43_950.steps}))
end
| _43_953 -> begin
(FStar_All.failwith "Impossible: ill-typed term")
end)
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(

let args = (FStar_List.fold_right (fun a out -> (((a), (config.environment)))::out) args config.stack.args)
in (

let stack = (

let _43_961 = config.stack
in {args = args})
in (wne tcenv (

let _43_964 = config
in {code = head; environment = _43_964.environment; stack = stack; close = _43_964.close; steps = _43_964.steps}))))
end
| FStar_Absyn_Syntax.Exp_abs (binders, body) -> begin
(

let rec beta = (fun entries binders args -> (match (((binders), (args))) with
| ([], _43_976) -> begin
(

let env = (extend_env config.environment entries)
in (wne tcenv (

let _43_979 = config
in {code = body; environment = env; stack = (

let _43_981 = config.stack
in {args = args}); close = _43_979.close; steps = _43_979.steps})))
end
| (_43_984, []) -> begin
(

let env = (extend_env config.environment entries)
in (

let _43_990 = (sn_binders tcenv binders env config.steps)
in (match (_43_990) with
| (binders, env) -> begin
(

let mk_abs = (fun t -> (FStar_Absyn_Syntax.mk_Exp_abs ((binders), (t)) None body.FStar_Absyn_Syntax.pos))
in (

let c = (let _140_436 = (

let _43_993 = config
in (let _140_435 = (no_eta config.steps)
in {code = body; environment = env; stack = (

let _43_995 = config.stack
in {args = []}); close = _43_993.close; steps = _140_435}))
in (wne tcenv _140_436))
in (

let _43_998 = c
in (let _140_437 = (mk_abs c.code)
in {code = _140_437; environment = _43_998.environment; stack = _43_998.stack; close = _43_998.close; steps = _43_998.steps}))))
end)))
end
| ((formal)::rest, (actual)::rest') -> begin
(

let m = (match (((formal), (actual))) with
| ((FStar_Util.Inl (a), _43_1010), ((FStar_Util.Inl (t), _43_1015), env)) -> begin
T (((a.FStar_Absyn_Syntax.v), (((t), (env)))))
end
| ((FStar_Util.Inr (x), _43_1023), ((FStar_Util.Inr (v), _43_1028), env)) -> begin
V (((x.FStar_Absyn_Syntax.v), (((v), (env)))))
end
| _43_1034 -> begin
(let _140_442 = (let _140_441 = (let _140_438 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _140_438))
in (let _140_440 = (FStar_Absyn_Print.binder_to_string formal)
in (let _140_439 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _140_441 _140_440 _140_439))))
in (FStar_All.failwith _140_442))
end)
in (beta ((m)::entries) rest rest'))
end))
in (beta [] binders config.stack.args))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(

let c_e1 = (wne tcenv (

let _43_1040 = config
in {code = e1; environment = _43_1040.environment; stack = empty_stack; close = _43_1040.close; steps = _43_1040.steps}))
in (

let wn_eqn = (fun _43_1047 -> (match (_43_1047) with
| (pat, w, body) -> begin
(

let rec pat_vars = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_disj ((p)::_43_1053) -> begin
(pat_vars p)
end
| FStar_Absyn_Syntax.Pat_cons (_43_1058, _43_1060, pats) -> begin
(FStar_List.collect (fun _43_1067 -> (match (_43_1067) with
| (x, _43_1066) -> begin
(pat_vars x)
end)) pats)
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _140_448 = (FStar_Absyn_Syntax.v_binder x)
in (_140_448)::[])
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _140_449 = (FStar_Absyn_Syntax.t_binder a)
in (_140_449)::[])
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

let _43_1091 = x
in {FStar_Absyn_Syntax.v = _43_1091.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t.code; FStar_Absyn_Syntax.p = _43_1091.FStar_Absyn_Syntax.p})))
in (

let norm_btvar = (fun a -> (

let k = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort config.environment config.steps))
in (

let _43_1096 = a
in {FStar_Absyn_Syntax.v = _43_1096.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k.code; FStar_Absyn_Syntax.p = _43_1096.FStar_Absyn_Syntax.p})))
in (

let rec norm_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (pats) -> begin
(let _140_457 = (let _140_456 = (FStar_List.map norm_pat pats)
in FStar_Absyn_Syntax.Pat_disj (_140_456))
in (FStar_Absyn_Util.withinfo _140_457 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _140_462 = (let _140_461 = (let _140_460 = (FStar_List.map (fun _43_1109 -> (match (_43_1109) with
| (x, i) -> begin
(let _140_459 = (norm_pat x)
in ((_140_459), (i)))
end)) pats)
in ((fv), (q), (_140_460)))
in FStar_Absyn_Syntax.Pat_cons (_140_461))
in (FStar_Absyn_Util.withinfo _140_462 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _140_464 = (let _140_463 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_var (_140_463))
in (FStar_Absyn_Util.withinfo _140_464 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _140_466 = (let _140_465 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_tvar (_140_465))
in (FStar_Absyn_Util.withinfo _140_466 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let _140_468 = (let _140_467 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_wild (_140_467))
in (FStar_Absyn_Util.withinfo _140_468 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let _140_470 = (let _140_469 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_twild (_140_469))
in (FStar_Absyn_Util.withinfo _140_470 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_constant (_43_1119) -> begin
p
end
| FStar_Absyn_Syntax.Pat_dot_term (x, e) -> begin
(

let e = (wne tcenv (e_config e config.environment config.steps))
in (let _140_473 = (let _140_472 = (let _140_471 = (norm_bvvar x)
in ((_140_471), (e.code)))
in FStar_Absyn_Syntax.Pat_dot_term (_140_472))
in (FStar_Absyn_Util.withinfo _140_473 None p.FStar_Absyn_Syntax.p)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
(

let t = (sn tcenv (t_config t config.environment config.steps))
in (let _140_476 = (let _140_475 = (let _140_474 = (norm_btvar a)
in ((_140_474), (t.code)))
in FStar_Absyn_Syntax.Pat_dot_typ (_140_475))
in (FStar_Absyn_Util.withinfo _140_476 None p.FStar_Absyn_Syntax.p)))
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

let _43_1144 = config
in {code = w; environment = env; stack = empty_stack; close = _43_1144.close; steps = _43_1144.steps}))
in Some (c_w.code))
end)
in (

let c_body = (wne tcenv (

let _43_1148 = config
in {code = body; environment = env; stack = empty_stack; close = _43_1148.close; steps = _43_1148.steps}))
in (let _140_479 = (norm_pat pat)
in ((_140_479), (w), (c_body.code))))))))))))
end))
in (

let eqns = (FStar_List.map wn_eqn eqns)
in (

let e = (FStar_Absyn_Syntax.mk_Exp_match ((c_e1.code), (eqns)) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (

let _43_1153 = config
in {code = e; environment = _43_1153.environment; stack = _43_1153.stack; close = _43_1153.close; steps = _43_1153.steps}) rebuild)))))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), body) -> begin
(

let _43_1185 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _43_1163 _43_1168 -> (match (((_43_1163), (_43_1168))) with
| ((env, lbs), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = eff; FStar_Absyn_Syntax.lbdef = e}) -> begin
(

let c = (wne tcenv (

let _43_1169 = config
in {code = e; environment = _43_1169.environment; stack = empty_stack; close = _43_1169.close; steps = _43_1169.steps}))
in (

let t = (sn tcenv (t_config t config.environment config.steps))
in (

let _43_1182 = (match (x) with
| FStar_Util.Inl (x) -> begin
(

let y = (let _140_482 = if is_rec then begin
x
end else begin
(FStar_Absyn_Util.freshen_bvd x)
end
in (FStar_Absyn_Util.bvd_to_bvar_s _140_482 t.code))
in (

let yexp = (FStar_Absyn_Util.bvar_to_exp y)
in (

let y_for_x = V (((x), (((yexp), (empty_env)))))
in ((FStar_Util.Inl (y.FStar_Absyn_Syntax.v)), ((extend_env' env y_for_x))))))
end
| _43_1179 -> begin
((x), (env))
end)
in (match (_43_1182) with
| (y, env) -> begin
(let _140_484 = (let _140_483 = (FStar_Absyn_Syntax.mk_lb ((y), (eff), (t.code), (c.code)))
in (_140_483)::lbs)
in ((env), (_140_484)))
end))))
end)) ((config.environment), ([]))))
in (match (_43_1185) with
| (env, lbs) -> begin
(

let lbs = (FStar_List.rev lbs)
in (

let c_body = (wne tcenv (

let _43_1187 = config
in {code = body; environment = env; stack = empty_stack; close = _43_1187.close; steps = _43_1187.steps}))
in (

let e = (FStar_Absyn_Syntax.mk_Exp_let ((((is_rec), (lbs))), (c_body.code)) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (

let _43_1191 = config
in {code = e; environment = _43_1191.environment; stack = _43_1191.stack; close = _43_1191.close; steps = _43_1191.steps}) rebuild))))
end))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, l) -> begin
(

let c = (wne tcenv (

let _43_1198 = config
in {code = e; environment = _43_1198.environment; stack = _43_1198.stack; close = _43_1198.close; steps = _43_1198.steps}))
in if (is_stack_empty config) then begin
(

let t = (sn tcenv (t_config t config.environment config.steps))
in (let _140_486 = (

let _43_1202 = config
in (let _140_485 = (FStar_Absyn_Syntax.mk_Exp_ascribed ((c.code), (t.code), (l)) None e.FStar_Absyn_Syntax.pos)
in {code = _140_485; environment = _43_1202.environment; stack = _43_1202.stack; close = _43_1202.close; steps = _43_1202.steps}))
in (rebuild _140_486)))
end else begin
c
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, info)) -> begin
(

let c = (wne tcenv (

let _43_1209 = config
in {code = e; environment = _43_1209.environment; stack = _43_1209.stack; close = _43_1209.close; steps = _43_1209.steps}))
in if (is_stack_empty config) then begin
(let _140_488 = (

let _43_1212 = config
in (let _140_487 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((c.code), (info)))))
in {code = _140_487; environment = _43_1212.environment; stack = _43_1212.stack; close = _43_1212.close; steps = _43_1212.steps}))
in (rebuild _140_488))
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


let norm_sigelt : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt = (fun tcenv _43_10 -> (match (_43_10) with
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, b) -> begin
(

let e = (let _140_512 = (let _140_511 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None r)
in ((lbs), (_140_511)))
in (FStar_Absyn_Syntax.mk_Exp_let _140_512 None r))
in (

let e = (norm_exp ((Beta)::[]) tcenv e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_let (lbs, _43_1238) -> begin
FStar_Absyn_Syntax.Sig_let (((lbs), (r), (l), (b)))
end
| _43_1242 -> begin
(FStar_All.failwith "Impossible")
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
(let _140_517 = (eta_expand tcenv t)
in (FStar_All.pipe_right _140_517 FStar_Absyn_Util.compress_typ))
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


let exp_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  Prims.string = (fun tcenv e -> (let _140_540 = (norm_exp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv e)
in (FStar_Absyn_Print.exp_to_string _140_540)))


let typ_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun tcenv t -> (let _140_545 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv t)
in (FStar_Absyn_Print.typ_to_string _140_545)))


let kind_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun tcenv k -> (let _140_550 = (norm_kind ((Beta)::(SNComp)::(Unmeta)::[]) tcenv k)
in (FStar_Absyn_Print.kind_to_string _140_550)))


let formula_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun tcenv f -> (let _140_555 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv f)
in (FStar_Absyn_Print.formula_to_string _140_555)))


let comp_typ_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  Prims.string = (fun tcenv c -> (let _140_560 = (norm_comp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv c)
in (FStar_Absyn_Print.comp_typ_to_string _140_560)))


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
(let _140_575 = (let _140_574 = (let _140_573 = (let _140_572 = (let _140_571 = (let _140_570 = (let _140_569 = (FStar_Absyn_Util.bvar_to_exp y)
in ((x.FStar_Absyn_Syntax.v), (_140_569)))
in FStar_Util.Inr (_140_570))
in (_140_571)::[])
in (FStar_Absyn_Util.subst_typ _140_572 phi))
in (FStar_Absyn_Util.mk_conj phi1 _140_573))
in ((y), (_140_574)))
in (FStar_Absyn_Syntax.mk_Typ_refine _140_575 (Some (FStar_Absyn_Syntax.ktype)) t0.FStar_Absyn_Syntax.pos))
end
| _43_1351 -> begin
t
end))
end
| _43_1353 -> begin
t
end)))
in (aux t))))




