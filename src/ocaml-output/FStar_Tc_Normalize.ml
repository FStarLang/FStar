
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
| T (_45_16) -> begin
_45_16
end))


let ___V____0 = (fun projectee -> (match (projectee) with
| V (_45_19) -> begin
_45_19
end))


let empty_env : environment = {context = []; label_suffix = []}


let extend_env' : environment  ->  env_entry  ->  environment = (fun env b -> (

let _45_22 = env
in {context = (b)::env.context; label_suffix = _45_22.label_suffix}))


let extend_env : environment  ->  env_entry Prims.list  ->  environment = (fun env bindings -> (

let _45_26 = env
in {context = (FStar_List.append bindings env.context); label_suffix = _45_26.label_suffix}))


let lookup_env : environment  ->  Prims.string  ->  env_entry Prims.option = (fun env key -> (FStar_All.pipe_right env.context (FStar_Util.find_opt (fun uu___115 -> (match (uu___115) with
| T (a, _45_33) -> begin
(a.FStar_Absyn_Syntax.realname.FStar_Ident.idText = key)
end
| V (x, _45_38) -> begin
(x.FStar_Absyn_Syntax.realname.FStar_Ident.idText = key)
end)))))


let fold_env = (fun env f acc -> (FStar_List.fold_left (fun acc v -> (match (v) with
| T (a, _45_48) -> begin
(f a.FStar_Absyn_Syntax.realname.FStar_Ident.idText v acc)
end
| V (x, _45_53) -> begin
(f x.FStar_Absyn_Syntax.realname.FStar_Ident.idText v acc)
end)) acc env.context))


let empty_stack : stack = {args = []}


let rec subst_of_env' : environment  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list = (fun env -> (fold_env env (fun _45_57 v acc -> (match (v) with
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
| FStar_Absyn_Syntax.Kind_abbrev (_45_89, k) -> begin
(aux t k)
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k') -> begin
(match ((let _146_132 = (FStar_Absyn_Util.unascribe_typ t)
in _146_132.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam (real, body) -> begin
(

let rec aux = (fun real expected -> (match (((real), (expected))) with
| ((_45_106)::real, (_45_110)::expected) -> begin
(aux real expected)
end
| ([], []) -> begin
t
end
| ((_45_119)::_45_117, []) -> begin
(failwith "Ill-kinded type")
end
| ([], more) -> begin
(

let _45_128 = (FStar_Absyn_Util.args_of_binders more)
in (match (_45_128) with
| (more, args) -> begin
(

let body = (FStar_Absyn_Syntax.mk_Typ_app ((body), (args)) None body.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_List.append binders more)), (body)) None body.FStar_Absyn_Syntax.pos))
end))
end))
in (aux real binders))
end
| _45_131 -> begin
(

let _45_134 = (FStar_Absyn_Util.args_of_binders binders)
in (match (_45_134) with
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
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (_45_153); FStar_Absyn_Syntax.tk = _45_151; FStar_Absyn_Syntax.pos = _45_149; FStar_Absyn_Syntax.fvs = _45_147; FStar_Absyn_Syntax.uvs = _45_145} -> begin
true
end
| _45_157 -> begin
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
| _45_170 -> begin
(

let _45_173 = (FStar_Absyn_Util.args_of_binders bs)
in (match (_45_173) with
| (bs, args) -> begin
(let _146_150 = (let _146_149 = (FStar_Absyn_Syntax.mk_Exp_app ((e), (args)) None e.FStar_Absyn_Syntax.pos)
in ((bs), (_146_149)))
in (FStar_Absyn_Syntax.mk_Exp_abs _146_150 (Some (t)) e.FStar_Absyn_Syntax.pos))
end))
end)
end
| _45_175 -> begin
e
end)))


let no_eta : step Prims.list  ->  step Prims.list = (fun s -> (FStar_All.pipe_right s (FStar_List.filter (fun uu___116 -> (match (uu___116) with
| Eta -> begin
false
end
| _45_180 -> begin
true
end)))))


let no_eta_cfg = (fun c -> (

let _45_182 = c
in (let _146_155 = (no_eta c.steps)
in {code = _45_182.code; environment = _45_182.environment; stack = _45_182.stack; close = _45_182.close; steps = _146_155})))


let whnf_only = (fun config -> (FStar_All.pipe_right config.steps (FStar_List.contains WHNF)))


let unmeta = (fun config -> (FStar_All.pipe_right config.steps (FStar_List.contains Unmeta)))


let unlabel = (fun config -> ((unmeta config) || (FStar_All.pipe_right config.steps (FStar_List.contains Unlabel))))


let is_stack_empty = (fun config -> (match (config.stack.args) with
| [] -> begin
true
end
| _45_190 -> begin
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

let binders' = (FStar_List.map (fun uu___117 -> (match (uu___117) with
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

let _45_214 = (FStar_Absyn_Util.comp_to_comp_typ c1)
in {FStar_Absyn_Syntax.effect_name = _45_214.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _45_214.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _45_214.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = c.FStar_Absyn_Syntax.flags}) FStar_Absyn_Syntax.mk_Comp)
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
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _45_245, _45_247)) -> begin
(is_head_symbol t)
end
| _45_252 -> begin
false
end))


let simplify_then_apply : step Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.args  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ = (fun steps head args pos -> (

let fallback = (fun _45_258 -> (match (()) with
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
| _45_266 -> begin
None
end))
in (

let simplify = (fun arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (t) -> begin
(((simp_t t)), (arg))
end
| _45_272 -> begin
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
| _45_319 -> begin
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
| _45_364 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
FStar_Absyn_Util.t_true
end
| ((Some (true), _45_392))::((_45_382, (FStar_Util.Inl (arg), _45_386)))::[] -> begin
arg
end
| _45_396 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _45_400))::[] -> begin
FStar_Absyn_Util.t_false
end
| ((Some (false), _45_406))::[] -> begin
FStar_Absyn_Util.t_true
end
| _45_410 -> begin
(fallback ())
end)
end else begin
if ((((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.forall_lid) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid)) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exists_lid)) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) then begin
(match (args) with
| (((FStar_Util.Inl (t), _))::[]) | ((_)::((FStar_Util.Inl (t), _))::[]) -> begin
(match ((let _146_219 = (FStar_Absyn_Util.compress_typ t)
in _146_219.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam ((_45_425)::[], body) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
FStar_Absyn_Util.t_true
end
| Some (false) -> begin
FStar_Absyn_Util.t_false
end
| _45_435 -> begin
(fallback ())
end)
end
| _45_437 -> begin
(fallback ())
end)
end
| _45_439 -> begin
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
| _45_441 -> begin
(fallback ())
end)
end))))


let rec sn_delay : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ config  ->  FStar_Absyn_Syntax.typ config = (fun tcenv cfg -> (

let aux = (fun _45_445 -> (match (()) with
| () -> begin
(let _146_245 = (sn tcenv cfg)
in _146_245.code)
end))
in (

let t = (FStar_Absyn_Syntax.mk_Typ_delayed' (FStar_Util.Inr (aux)) None cfg.code.FStar_Absyn_Syntax.pos)
in (

let _45_447 = cfg
in {code = t; environment = _45_447.environment; stack = empty_stack; close = _45_447.close; steps = _45_447.steps}))))
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

let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun uu___118 -> (match (uu___118) with
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

let _45_471 = config
in {code = t; environment = _45_471.environment; stack = empty_stack; close = _45_471.close; steps = _45_471.steps}))))
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

let _45_478 = config
in (let _146_263 = (eta_expand tcenv t)
in {code = _146_263; environment = _45_478.environment; stack = _45_478.stack; close = _45_478.close; steps = _45_478.steps}))
end else begin
(

let _45_480 = config
in {code = t; environment = _45_480.environment; stack = _45_480.stack; close = _45_480.close; steps = _45_480.steps})
end))))
in (

let wk = (fun f -> (match ((FStar_ST.read cfg.code.FStar_Absyn_Syntax.tk)) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _45_491; FStar_Absyn_Syntax.pos = _45_489; FStar_Absyn_Syntax.fvs = _45_487; FStar_Absyn_Syntax.uvs = _45_485}) -> begin
(f (Some (FStar_Absyn_Syntax.ktype)) cfg.code.FStar_Absyn_Syntax.pos)
end
| _45_496 -> begin
(f None cfg.code.FStar_Absyn_Syntax.pos)
end))
in (

let config = (

let _45_497 = cfg
in (let _146_276 = (FStar_Absyn_Util.compress_typ cfg.code)
in {code = _146_276; environment = _45_497.environment; stack = _45_497.stack; close = _45_497.close; steps = _45_497.steps}))
in (match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_45_501) -> begin
(failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_uvar (_45_504) -> begin
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

let _45_512 = config
in {code = t; environment = _45_512.environment; stack = _45_512.stack; close = _45_512.close; steps = _45_512.steps}))
end))
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(match ((lookup_env config.environment a.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname.FStar_Ident.idText)) with
| None -> begin
(rebuild config)
end
| Some (T (_45_518, (t, e))) -> begin
(sn tcenv (

let _45_525 = config
in {code = t; environment = e; stack = _45_525.stack; close = _45_525.close; steps = _45_525.steps}))
end
| _45_528 -> begin
(failwith "Impossible: expected a type")
end)
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(

let args = (FStar_List.fold_right (fun a out -> (((a), (config.environment)))::out) args config.stack.args)
in (

let stack = (

let _45_536 = config.stack
in {args = args})
in (sn tcenv (

let _45_539 = config
in {code = head; environment = _45_539.environment; stack = stack; close = _45_539.close; steps = _45_539.steps}))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(match (config.stack.args) with
| [] -> begin
(

let _45_548 = (sn_binders tcenv binders config.environment config.steps)
in (match (_45_548) with
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

let _45_556 = t2_cfg
in (let _146_290 = (mk_lam t2_cfg.code)
in {code = _146_290; environment = _45_556.environment; stack = _45_556.stack; close = _45_556.close; steps = _45_556.steps}))))
end))
end
| args -> begin
(

let rec beta = (fun env_entries binders args -> (match (((binders), (args))) with
| ([], _45_565) -> begin
(

let env = (extend_env config.environment env_entries)
in (sn tcenv (

let _45_568 = config
in {code = t2; environment = env; stack = (

let _45_570 = config.stack
in {args = args}); close = _45_568.close; steps = _45_568.steps})))
end
| (_45_573, []) -> begin
(

let t = (FStar_Absyn_Syntax.mk_Typ_lam ((binders), (t2)) None t2.FStar_Absyn_Syntax.pos)
in (

let env = (extend_env config.environment env_entries)
in (sn tcenv (

let _45_578 = config
in {code = t; environment = env; stack = empty_stack; close = _45_578.close; steps = _45_578.steps}))))
end
| ((formal)::rest, (actual)::rest') -> begin
(

let m = (match (((formal), (actual))) with
| ((FStar_Util.Inl (a), _45_590), ((FStar_Util.Inl (t), _45_595), env)) -> begin
T (((a.FStar_Absyn_Syntax.v), (((t), (env)))))
end
| ((FStar_Util.Inr (x), _45_603), ((FStar_Util.Inr (v), _45_608), env)) -> begin
V (((x.FStar_Absyn_Syntax.v), (((v), (env)))))
end
| _45_614 -> begin
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
| FStar_Absyn_Syntax.Typ_ascribed (t, _45_618) -> begin
(sn tcenv (

let _45_621 = config
in {code = t; environment = _45_621.environment; stack = _45_621.stack; close = _45_621.close; steps = _45_621.steps}))
end
| _45_624 -> begin
(match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, comp) -> begin
(

let _45_631 = (sn_binders tcenv bs config.environment config.steps)
in (match (_45_631) with
| (binders, environment) -> begin
(

let c2 = (sncomp tcenv (c_config comp environment config.steps))
in (let _146_305 = (

let _45_633 = config
in (let _146_304 = (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_fun ((binders), (c2.code))))
in {code = _146_304; environment = _45_633.environment; stack = _45_633.stack; close = _45_633.close; steps = _45_633.steps}))
in (rebuild _146_305)))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((let _146_307 = (let _146_306 = (FStar_Absyn_Syntax.v_binder x)
in (_146_306)::[])
in (sn_binders tcenv _146_307 config.environment config.steps))) with
| (((FStar_Util.Inr (x), _45_642))::[], env) -> begin
(

let refine = (fun t -> (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_refine ((x), (t)))))
in (let _146_314 = (let _146_313 = (FStar_All.pipe_right config.steps (FStar_List.filter (fun uu___119 -> (match (uu___119) with
| UnfoldOpaque -> begin
false
end
| _45_652 -> begin
true
end))))
in {code = t; environment = env; stack = empty_stack; close = (close_with_config config refine); steps = _146_313})
in (sn tcenv _146_314)))
end
| _45_654 -> begin
(failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
if (unmeta config) then begin
(sn tcenv (

let _45_660 = config
in {code = t; environment = _45_660.environment; stack = _45_660.stack; close = _45_660.close; steps = _45_660.steps}))
end else begin
(

let pat = (fun t -> (

let ps = (FStar_All.pipe_right ps (FStar_List.map (sn_args true tcenv config.environment config.steps)))
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern (((t), (ps))))))))
in (sn tcenv (

let _45_665 = config
in {code = t; environment = _45_665.environment; stack = _45_665.stack; close = (close_with_config config pat); steps = _45_665.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, b)) -> begin
if (unlabel config) then begin
(sn tcenv (

let _45_674 = config
in {code = t; environment = _45_674.environment; stack = _45_674.stack; close = _45_674.close; steps = _45_674.steps}))
end else begin
(

let lab = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when ((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) && (FStar_All.pipe_right config.steps (FStar_List.contains Simplify))) -> begin
t
end
| _45_681 -> begin
(match (config.environment.label_suffix) with
| ((b', sfx))::_45_683 -> begin
if ((b' = None) || (Some (b) = b')) then begin
(

let _45_688 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _146_321 = (FStar_Range.string_of_range sfx)
in (FStar_Util.print2 "Stripping label %s because of enclosing refresh %s\n" l _146_321))
end else begin
()
end
in t)
end else begin
(

let _45_690 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _146_322 = (FStar_Range.string_of_range sfx)
in (FStar_Util.print1 "Normalizer refreshing label: %s\n" _146_322))
end else begin
()
end
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled (((t), (l), (sfx), (b)))))))
end
end
| _45_693 -> begin
(FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled (((t), (l), (r), (b))))))
end)
end))
in (sn tcenv (

let _45_694 = config
in {code = t; environment = _45_694.environment; stack = _45_694.stack; close = (close_with_config config lab); steps = _45_694.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
if (unmeta config) then begin
(sn tcenv (

let _45_702 = config
in {code = t; environment = _45_702.environment; stack = _45_702.stack; close = _45_702.close; steps = _45_702.steps}))
end else begin
(

let sfx = (match (b) with
| Some (false) -> begin
r
end
| _45_707 -> begin
FStar_Absyn_Syntax.dummyRange
end)
in (

let config = (

let _45_709 = config
in {code = t; environment = (

let _45_711 = config.environment
in {context = _45_711.context; label_suffix = (((b), (sfx)))::config.environment.label_suffix}); stack = _45_709.stack; close = _45_709.close; steps = _45_709.steps})
in (sn tcenv config)))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
if (FStar_ST.read flag) then begin
(let _146_328 = (

let _45_720 = config
in (let _146_327 = (FStar_Absyn_Util.mk_conj t1 t2)
in {code = _146_327; environment = _45_720.environment; stack = _45_720.stack; close = _45_720.close; steps = _45_720.steps}))
in (sn tcenv _146_328))
end else begin
(

let c1 = (sn tcenv (t_config t1 config.environment config.steps))
in (

let c2 = (sn tcenv (t_config t2 config.environment config.steps))
in (let _146_330 = (

let _45_724 = config
in (let _146_329 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (((c1.code), (c2.code), (flag)))))
in {code = _146_329; environment = _45_724.environment; stack = _45_724.stack; close = _45_724.close; steps = _45_724.steps}))
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

let rec aux = (fun out env uu___120 -> (match (uu___120) with
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

let _45_768 = cfg
in (let _146_350 = (FStar_Absyn_Syntax.mk_Comp ctconf.code)
in {code = _146_350; environment = _45_768.environment; stack = _45_768.stack; close = _45_768.close; steps = _45_768.steps})))
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

let norm = (fun _45_777 -> (match (()) with
| () -> begin
(

let remake = (fun l r eargs flags -> (

let c = {FStar_Absyn_Syntax.effect_name = l; FStar_Absyn_Syntax.result_typ = r; FStar_Absyn_Syntax.effect_args = eargs; FStar_Absyn_Syntax.flags = flags}
in (

let _45_784 = cfg
in {code = c; environment = _45_784.environment; stack = _45_784.stack; close = _45_784.close; steps = _45_784.steps})))
in (

let res = (let _146_368 = (sn tcenv (with_new_code cfg m.FStar_Absyn_Syntax.result_typ))
in _146_368.code)
in (

let sn_flags = (fun flags -> (FStar_All.pipe_right flags (FStar_List.map (fun uu___121 -> (match (uu___121) with
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

let _45_796 = (let _146_374 = (sn_flags m.FStar_Absyn_Syntax.flags)
in (let _146_373 = (sn_args true tcenv cfg.environment cfg.steps m.FStar_Absyn_Syntax.effect_args)
in ((_146_374), (_146_373))))
in (match (_45_796) with
| (flags, args) -> begin
(remake m.FStar_Absyn_Syntax.effect_name res args flags)
end)))))
end))
in if (FStar_List.contains DeltaComp cfg.steps) then begin
(match ((FStar_Tc_Env.lookup_effect_abbrev tcenv m.FStar_Absyn_Syntax.effect_name)) with
| Some (_45_798) -> begin
(

let c = (let _146_375 = (FStar_Absyn_Syntax.mk_Comp m)
in (weak_norm_comp tcenv _146_375))
in (sncomp_typ tcenv (

let _45_801 = cfg
in {code = c; environment = _45_801.environment; stack = _45_801.stack; close = _45_801.close; steps = _45_801.steps})))
end
| _45_804 -> begin
(norm ())
end)
end else begin
(norm ())
end)))
and sn_args : Prims.bool  ->  FStar_Tc_Env.env  ->  environment  ->  step Prims.list  ->  FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.arg Prims.list = (fun delay tcenv env steps args -> (FStar_All.pipe_right args (FStar_List.map (fun uu___122 -> (match (uu___122) with
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

let _45_840 = cfg
in (let _146_406 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar ((uv), (args))))
in {code = _146_406; environment = _45_840.environment; stack = _45_840.stack; close = _45_840.close; steps = _45_840.steps})))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _45_852; FStar_Absyn_Syntax.pos = _45_850; FStar_Absyn_Syntax.fvs = _45_848; FStar_Absyn_Syntax.uvs = _45_846}) -> begin
(

let _45_861 = (FStar_Tc_Env.lookup_kind_abbrev tcenv l)
in (match (_45_861) with
| (_45_858, binders, body) -> begin
(

let subst = (FStar_Absyn_Util.subst_of_list binders args)
in (let _146_408 = (

let _45_863 = cfg
in (let _146_407 = (FStar_Absyn_Util.subst_kind subst body)
in {code = _146_407; environment = _45_863.environment; stack = _45_863.stack; close = _45_863.close; steps = _45_863.steps}))
in (snk tcenv _146_408)))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_45_866, k) -> begin
(snk tcenv (

let _45_870 = cfg
in {code = k; environment = _45_870.environment; stack = _45_870.stack; close = _45_870.close; steps = _45_870.steps}))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(

let _45_878 = (sn_binders tcenv bs cfg.environment cfg.steps)
in (match (_45_878) with
| (bs, env) -> begin
(

let c2 = (snk tcenv (k_config k env cfg.steps))
in (

let _45_888 = (match (c2.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs', k) -> begin
(((FStar_List.append bs bs')), (k))
end
| _45_885 -> begin
((bs), (c2.code))
end)
in (match (_45_888) with
| (bs, rhs) -> begin
(

let _45_889 = cfg
in (let _146_410 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (rhs))))
in {code = _146_410; environment = _45_889.environment; stack = _45_889.stack; close = _45_889.close; steps = _45_889.steps}))
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

let _45_895 = cfg
in {code = e; environment = _45_895.environment; stack = _45_895.stack; close = _45_895.close; steps = _45_895.steps})
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

let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun uu___123 -> (match (uu___123) with
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

let _45_915 = config
in (let _146_424 = (FStar_Absyn_Syntax.mk_Exp_app ((config.code), (args)) None config.code.FStar_Absyn_Syntax.pos)
in {code = _146_424; environment = _45_915.environment; stack = empty_stack; close = _45_915.close; steps = _45_915.steps}))))
end)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_45_918) -> begin
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
| Some (V (_45_933, (vc, env))) -> begin
(wne tcenv (

let _45_940 = config
in {code = vc; environment = env; stack = _45_940.stack; close = _45_940.close; steps = _45_940.steps}))
end
| _45_943 -> begin
(failwith "Impossible: ill-typed term")
end)
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(

let args = (FStar_List.fold_right (fun a out -> (((a), (config.environment)))::out) args config.stack.args)
in (

let stack = (

let _45_951 = config.stack
in {args = args})
in (wne tcenv (

let _45_954 = config
in {code = head; environment = _45_954.environment; stack = stack; close = _45_954.close; steps = _45_954.steps}))))
end
| FStar_Absyn_Syntax.Exp_abs (binders, body) -> begin
(

let rec beta = (fun entries binders args -> (match (((binders), (args))) with
| ([], _45_966) -> begin
(

let env = (extend_env config.environment entries)
in (wne tcenv (

let _45_969 = config
in {code = body; environment = env; stack = (

let _45_971 = config.stack
in {args = args}); close = _45_969.close; steps = _45_969.steps})))
end
| (_45_974, []) -> begin
(

let env = (extend_env config.environment entries)
in (

let _45_980 = (sn_binders tcenv binders env config.steps)
in (match (_45_980) with
| (binders, env) -> begin
(

let mk_abs = (fun t -> (FStar_Absyn_Syntax.mk_Exp_abs ((binders), (t)) None body.FStar_Absyn_Syntax.pos))
in (

let c = (let _146_436 = (

let _45_983 = config
in (let _146_435 = (no_eta config.steps)
in {code = body; environment = env; stack = (

let _45_985 = config.stack
in {args = []}); close = _45_983.close; steps = _146_435}))
in (wne tcenv _146_436))
in (

let _45_988 = c
in (let _146_437 = (mk_abs c.code)
in {code = _146_437; environment = _45_988.environment; stack = _45_988.stack; close = _45_988.close; steps = _45_988.steps}))))
end)))
end
| ((formal)::rest, (actual)::rest') -> begin
(

let m = (match (((formal), (actual))) with
| ((FStar_Util.Inl (a), _45_1000), ((FStar_Util.Inl (t), _45_1005), env)) -> begin
T (((a.FStar_Absyn_Syntax.v), (((t), (env)))))
end
| ((FStar_Util.Inr (x), _45_1013), ((FStar_Util.Inr (v), _45_1018), env)) -> begin
V (((x.FStar_Absyn_Syntax.v), (((v), (env)))))
end
| _45_1024 -> begin
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

let _45_1030 = config
in {code = e1; environment = _45_1030.environment; stack = empty_stack; close = _45_1030.close; steps = _45_1030.steps}))
in (

let wn_eqn = (fun _45_1037 -> (match (_45_1037) with
| (pat, w, body) -> begin
(

let rec pat_vars = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_disj ((p)::_45_1043) -> begin
(pat_vars p)
end
| FStar_Absyn_Syntax.Pat_cons (_45_1048, _45_1050, pats) -> begin
(FStar_List.collect (fun _45_1057 -> (match (_45_1057) with
| (x, _45_1056) -> begin
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

let _45_1081 = x
in {FStar_Absyn_Syntax.v = _45_1081.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t.code; FStar_Absyn_Syntax.p = _45_1081.FStar_Absyn_Syntax.p})))
in (

let norm_btvar = (fun a -> (

let k = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort config.environment config.steps))
in (

let _45_1086 = a
in {FStar_Absyn_Syntax.v = _45_1086.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k.code; FStar_Absyn_Syntax.p = _45_1086.FStar_Absyn_Syntax.p})))
in (

let rec norm_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (pats) -> begin
(let _146_457 = (let _146_456 = (FStar_List.map norm_pat pats)
in FStar_Absyn_Syntax.Pat_disj (_146_456))
in (FStar_Absyn_Util.withinfo _146_457 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _146_462 = (let _146_461 = (let _146_460 = (FStar_List.map (fun _45_1099 -> (match (_45_1099) with
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
| FStar_Absyn_Syntax.Pat_constant (_45_1109) -> begin
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

let _45_1134 = config
in {code = w; environment = env; stack = empty_stack; close = _45_1134.close; steps = _45_1134.steps}))
in Some (c_w.code))
end)
in (

let c_body = (wne tcenv (

let _45_1138 = config
in {code = body; environment = env; stack = empty_stack; close = _45_1138.close; steps = _45_1138.steps}))
in (let _146_479 = (norm_pat pat)
in ((_146_479), (w), (c_body.code))))))))))))
end))
in (

let eqns = (FStar_List.map wn_eqn eqns)
in (

let e = (FStar_Absyn_Syntax.mk_Exp_match ((c_e1.code), (eqns)) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (

let _45_1143 = config
in {code = e; environment = _45_1143.environment; stack = _45_1143.stack; close = _45_1143.close; steps = _45_1143.steps}) rebuild)))))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), body) -> begin
(

let _45_1175 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _45_1153 _45_1158 -> (match (((_45_1153), (_45_1158))) with
| ((env, lbs), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = eff; FStar_Absyn_Syntax.lbdef = e}) -> begin
(

let c = (wne tcenv (

let _45_1159 = config
in {code = e; environment = _45_1159.environment; stack = empty_stack; close = _45_1159.close; steps = _45_1159.steps}))
in (

let t = (sn tcenv (t_config t config.environment config.steps))
in (

let _45_1172 = (match (x) with
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
| _45_1169 -> begin
((x), (env))
end)
in (match (_45_1172) with
| (y, env) -> begin
(let _146_484 = (let _146_483 = (FStar_Absyn_Syntax.mk_lb ((y), (eff), (t.code), (c.code)))
in (_146_483)::lbs)
in ((env), (_146_484)))
end))))
end)) ((config.environment), ([]))))
in (match (_45_1175) with
| (env, lbs) -> begin
(

let lbs = (FStar_List.rev lbs)
in (

let c_body = (wne tcenv (

let _45_1177 = config
in {code = body; environment = env; stack = empty_stack; close = _45_1177.close; steps = _45_1177.steps}))
in (

let e = (FStar_Absyn_Syntax.mk_Exp_let ((((is_rec), (lbs))), (c_body.code)) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (

let _45_1181 = config
in {code = e; environment = _45_1181.environment; stack = _45_1181.stack; close = _45_1181.close; steps = _45_1181.steps}) rebuild))))
end))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, l) -> begin
(

let c = (wne tcenv (

let _45_1188 = config
in {code = e; environment = _45_1188.environment; stack = _45_1188.stack; close = _45_1188.close; steps = _45_1188.steps}))
in if (is_stack_empty config) then begin
(

let t = (sn tcenv (t_config t config.environment config.steps))
in (let _146_486 = (

let _45_1192 = config
in (let _146_485 = (FStar_Absyn_Syntax.mk_Exp_ascribed ((c.code), (t.code), (l)) None e.FStar_Absyn_Syntax.pos)
in {code = _146_485; environment = _45_1192.environment; stack = _45_1192.stack; close = _45_1192.close; steps = _45_1192.steps}))
in (rebuild _146_486)))
end else begin
c
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, info)) -> begin
(

let c = (wne tcenv (

let _45_1199 = config
in {code = e; environment = _45_1199.environment; stack = _45_1199.stack; close = _45_1199.close; steps = _45_1199.steps}))
in if (is_stack_empty config) then begin
(let _146_488 = (

let _45_1202 = config
in (let _146_487 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((c.code), (info)))))
in {code = _146_487; environment = _45_1202.environment; stack = _45_1202.stack; close = _45_1202.close; steps = _45_1202.steps}))
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


let norm_sigelt : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt = (fun tcenv uu___124 -> (match (uu___124) with
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, b) -> begin
(

let e = (let _146_512 = (let _146_511 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None r)
in ((lbs), (_146_511)))
in (FStar_Absyn_Syntax.mk_Exp_let _146_512 None r))
in (

let e = (norm_exp ((Beta)::[]) tcenv e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_let (lbs, _45_1228) -> begin
FStar_Absyn_Syntax.Sig_let (((lbs), (r), (l), (b)))
end
| _45_1232 -> begin
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
| _45_1341 -> begin
t
end))
end
| _45_1343 -> begin
t
end)))
in (aux t))))




