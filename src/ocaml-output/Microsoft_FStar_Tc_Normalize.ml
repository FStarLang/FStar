
type step =
| WHNF
| Eta
| Delta
| DeltaHard
| Beta
| DeltaComp
| Simplify
| SNComp
| Unmeta
| Unlabel 
 and steps =
step list

let is_WHNF = (fun ( _discr_ ) -> (match (_discr_) with
| WHNF -> begin
true
end
| _ -> begin
false
end))

let is_Eta = (fun ( _discr_ ) -> (match (_discr_) with
| Eta -> begin
true
end
| _ -> begin
false
end))

let is_Delta = (fun ( _discr_ ) -> (match (_discr_) with
| Delta -> begin
true
end
| _ -> begin
false
end))

let is_DeltaHard = (fun ( _discr_ ) -> (match (_discr_) with
| DeltaHard -> begin
true
end
| _ -> begin
false
end))

let is_Beta = (fun ( _discr_ ) -> (match (_discr_) with
| Beta -> begin
true
end
| _ -> begin
false
end))

let is_DeltaComp = (fun ( _discr_ ) -> (match (_discr_) with
| DeltaComp -> begin
true
end
| _ -> begin
false
end))

let is_Simplify = (fun ( _discr_ ) -> (match (_discr_) with
| Simplify -> begin
true
end
| _ -> begin
false
end))

let is_SNComp = (fun ( _discr_ ) -> (match (_discr_) with
| SNComp -> begin
true
end
| _ -> begin
false
end))

let is_Unmeta = (fun ( _discr_ ) -> (match (_discr_) with
| Unmeta -> begin
true
end
| _ -> begin
false
end))

let is_Unlabel = (fun ( _discr_ ) -> (match (_discr_) with
| Unlabel -> begin
true
end
| _ -> begin
false
end))

type 'a config =
{code : 'a; environment : environment; stack : stack; close : ('a  ->  'a) option; steps : step list} 
 and environment =
{context : env_entry list; label_suffix : (bool option * Support.Microsoft.FStar.Range.range) list} 
 and stack =
{args : (Microsoft_FStar_Absyn_Syntax.arg * environment) list} 
 and env_entry =
| T of (Microsoft_FStar_Absyn_Syntax.btvdef * tclos)
| V of (Microsoft_FStar_Absyn_Syntax.bvvdef * vclos) 
 and tclos =
(Microsoft_FStar_Absyn_Syntax.typ * environment) 
 and vclos =
(Microsoft_FStar_Absyn_Syntax.exp * environment) 
 and 'a memo =
'a option ref

let is_Mkconfig = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkconfig"))

let is_Mkenvironment = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkenvironment"))

let is_Mkstack = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkstack"))

let is_T = (fun ( _discr_ ) -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

let is_V = (fun ( _discr_ ) -> (match (_discr_) with
| V (_) -> begin
true
end
| _ -> begin
false
end))

let empty_env = {context = []; label_suffix = []}

let extend_env' = (fun ( env ) ( b ) -> (let _32_29 = env
in {context = (b)::env.context; label_suffix = _32_29.label_suffix}))

let extend_env = (fun ( env ) ( bindings ) -> (let _32_33 = env
in {context = (Support.List.append bindings env.context); label_suffix = _32_33.label_suffix}))

let lookup_env = (fun ( env ) ( key ) -> (Support.All.pipe_right env.context (Support.Microsoft.FStar.Util.find_opt (fun ( _32_1 ) -> (match (_32_1) with
| T ((a, _32_40)) -> begin
(a.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText = key)
end
| V ((x, _32_45)) -> begin
(x.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText = key)
end)))))

let fold_env = (fun ( env ) ( f ) ( acc ) -> (Support.List.fold_left (fun ( acc ) ( v ) -> (match (v) with
| T ((a, _32_55)) -> begin
(f a.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText v acc)
end
| V ((x, _32_60)) -> begin
(f x.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText v acc)
end)) acc env.context))

let empty_stack = {args = []}

let rec subst_of_env' = (fun ( env ) -> (fold_env env (fun ( _32_64 ) ( v ) ( acc ) -> (match (v) with
| T ((a, (t, env'))) -> begin
(let _70_12292 = (let _70_12291 = (let _70_12290 = (let _70_12289 = (subst_of_env' env')
in (Microsoft_FStar_Absyn_Util.subst_typ _70_12289 t))
in (a, _70_12290))
in Support.Microsoft.FStar.Util.Inl (_70_12291))
in (_70_12292)::acc)
end
| V ((x, (v, env'))) -> begin
(let _70_12296 = (let _70_12295 = (let _70_12294 = (let _70_12293 = (subst_of_env' env')
in (Microsoft_FStar_Absyn_Util.subst_exp _70_12293 v))
in (x, _70_12294))
in Support.Microsoft.FStar.Util.Inr (_70_12295))
in (_70_12296)::acc)
end)) []))

let subst_of_env = (fun ( tcenv ) ( env ) -> (subst_of_env' env))

let with_new_code = (fun ( c ) ( e ) -> {code = e; environment = c.environment; stack = empty_stack; close = None; steps = c.steps})

let rec eta_expand = (fun ( tcenv ) ( t ) -> (let k = (let _70_12306 = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (Support.All.pipe_right _70_12306 Microsoft_FStar_Absyn_Util.compress_kind))
in (let rec aux = (fun ( t ) ( k ) -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) | (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_32_96, k)) -> begin
(aux t k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((binders, k')) -> begin
(match ((let _70_12311 = (Microsoft_FStar_Absyn_Util.unascribe_typ t)
in _70_12311.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((real, body)) -> begin
(let rec aux = (fun ( real ) ( expected ) -> (match ((real, expected)) with
| (_32_113::real, _32_117::expected) -> begin
(aux real expected)
end
| ([], []) -> begin
t
end
| (_32_126::_32_124, []) -> begin
(Support.All.failwith "Ill-kinded type")
end
| ([], more) -> begin
(let _32_135 = (Microsoft_FStar_Absyn_Util.args_of_binders more)
in (match (_32_135) with
| (more, args) -> begin
(let body = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (body, args) None body.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam ((Support.List.append binders more), body) None body.Microsoft_FStar_Absyn_Syntax.pos))
end))
end))
in (aux real binders))
end
| _32_138 -> begin
(let _32_141 = (Microsoft_FStar_Absyn_Util.args_of_binders binders)
in (match (_32_141) with
| (binders, args) -> begin
(let body = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t, args) None t.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, body) None t.Microsoft_FStar_Absyn_Syntax.pos))
end))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Kind_lam (_)) | (Microsoft_FStar_Absyn_Syntax.Kind_delayed (_)) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let _70_12319 = (let _70_12318 = (let _70_12316 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.All.pipe_right _70_12316 Support.Microsoft.FStar.Range.string_of_range))
in (let _70_12317 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "%s: Impossible: Kind_unknown: %s" _70_12318 _70_12317)))
in (Support.All.failwith _70_12319))
end))
in (aux t k))))

let is_var = (fun ( t ) -> (match ((Microsoft_FStar_Absyn_Util.compress_typ t)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (_32_160); Microsoft_FStar_Absyn_Syntax.tk = _32_158; Microsoft_FStar_Absyn_Syntax.pos = _32_156; Microsoft_FStar_Absyn_Syntax.fvs = _32_154; Microsoft_FStar_Absyn_Syntax.uvs = _32_152} -> begin
true
end
| _32_164 -> begin
false
end))

let rec eta_expand_exp = (fun ( tcenv ) ( e ) -> (let t = (let _70_12326 = (Microsoft_FStar_Tc_Recheck.recompute_typ e)
in (Support.All.pipe_right _70_12326 Microsoft_FStar_Absyn_Util.compress_typ))
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(match ((let _70_12327 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _70_12327.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs', body)) -> begin
(match (((Support.List.length bs) = (Support.List.length bs'))) with
| true -> begin
e
end
| false -> begin
(Support.All.failwith "NYI")
end)
end
| _32_177 -> begin
(let _32_180 = (Microsoft_FStar_Absyn_Util.args_of_binders bs)
in (match (_32_180) with
| (bs, args) -> begin
(let _70_12329 = (let _70_12328 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e, args) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (bs, _70_12328))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _70_12329 (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos))
end))
end)
end
| _32_182 -> begin
e
end)))

let no_eta = (Support.List.filter (fun ( _32_2 ) -> (match (_32_2) with
| Eta -> begin
false
end
| _32_186 -> begin
true
end)))

let no_eta_cfg = (fun ( c ) -> (let _32_188 = c
in (let _70_12333 = (no_eta c.steps)
in {code = _32_188.code; environment = _32_188.environment; stack = _32_188.stack; close = _32_188.close; steps = _70_12333})))

let whnf_only = (fun ( config ) -> (Support.All.pipe_right config.steps (Support.List.contains WHNF)))

let unmeta = (fun ( config ) -> (Support.All.pipe_right config.steps (Support.List.contains Unmeta)))

let unlabel = (fun ( config ) -> ((unmeta config) || (Support.All.pipe_right config.steps (Support.List.contains Unlabel))))

let is_stack_empty = (fun ( config ) -> (match (config.stack.args) with
| [] -> begin
true
end
| _32_196 -> begin
false
end))

let has_eta = (fun ( cfg ) -> (Support.All.pipe_right cfg.steps (Support.List.contains Eta)))

let rec weak_norm_comp = (fun ( env ) ( comp ) -> (let c = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ comp)
in (match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev env c.Microsoft_FStar_Absyn_Syntax.effect_name)) with
| None -> begin
c
end
| Some ((binders, cdef)) -> begin
(let binders' = (Support.List.map (fun ( _32_3 ) -> (match (_32_3) with
| (Support.Microsoft.FStar.Util.Inl (b), imp) -> begin
(let _70_12345 = (let _70_12344 = (Microsoft_FStar_Absyn_Util.freshen_bvar b)
in Support.Microsoft.FStar.Util.Inl (_70_12344))
in (_70_12345, imp))
end
| (Support.Microsoft.FStar.Util.Inr (b), imp) -> begin
(let _70_12347 = (let _70_12346 = (Microsoft_FStar_Absyn_Util.freshen_bvar b)
in Support.Microsoft.FStar.Util.Inr (_70_12346))
in (_70_12347, imp))
end)) binders)
in (let subst = (let _70_12349 = (let _70_12348 = (Microsoft_FStar_Absyn_Util.args_of_binders binders')
in (Support.All.pipe_right _70_12348 Support.Prims.snd))
in (Microsoft_FStar_Absyn_Util.subst_of_list binders _70_12349))
in (let cdef = (Microsoft_FStar_Absyn_Util.subst_comp subst cdef)
in (let subst = (let _70_12351 = (let _70_12350 = (Microsoft_FStar_Absyn_Syntax.targ c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (_70_12350)::c.Microsoft_FStar_Absyn_Syntax.effect_args)
in (Microsoft_FStar_Absyn_Util.subst_of_list binders' _70_12351))
in (let c1 = (Microsoft_FStar_Absyn_Util.subst_comp subst cdef)
in (let c = (Support.All.pipe_right (let _32_220 = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c1)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _32_220.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _32_220.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _32_220.Microsoft_FStar_Absyn_Syntax.effect_args; Microsoft_FStar_Absyn_Syntax.flags = c.Microsoft_FStar_Absyn_Syntax.flags}) Microsoft_FStar_Absyn_Syntax.mk_Comp)
in (weak_norm_comp env c)))))))
end)))

let t_config = (fun ( code ) ( env ) ( steps ) -> {code = code; environment = env; stack = empty_stack; close = None; steps = steps})

let k_config = (fun ( code ) ( env ) ( steps ) -> {code = code; environment = env; stack = empty_stack; close = None; steps = steps})

let e_config = (fun ( code ) ( env ) ( steps ) -> {code = code; environment = env; stack = empty_stack; close = None; steps = steps})

let c_config = (fun ( code ) ( env ) ( steps ) -> {code = code; environment = env; stack = empty_stack; close = None; steps = steps})

let close_with_config = (fun ( cfg ) ( f ) -> Some ((fun ( t ) -> (let t = (f t)
in (match (cfg.close) with
| None -> begin
t
end
| Some (g) -> begin
(g t)
end)))))

let rec is_head_symbol = (fun ( t ) -> (match ((let _70_12382 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _70_12382.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _32_251, _32_253))) -> begin
(is_head_symbol t)
end
| _32_258 -> begin
false
end))

let simplify_then_apply = (fun ( steps ) ( head ) ( args ) ( pos ) -> (let fallback = (fun ( _32_264 ) -> (match (()) with
| () -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (head, args) None pos)
end))
in (let simp_t = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
Some (true)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.false_lid) -> begin
Some (false)
end
| _32_272 -> begin
None
end))
in (let simplify = (fun ( arg ) -> (match ((Support.Prims.fst arg)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
((simp_t t), arg)
end
| _32_278 -> begin
(None, arg)
end))
in (match ((Support.All.pipe_left Support.Prims.op_Negation (Support.List.contains Simplify steps))) with
| true -> begin
(fallback ())
end
| false -> begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.and_lid)) with
| true -> begin
(match ((Support.All.pipe_right args (Support.List.map simplify))) with
| ((Some (true), _)::(_, (Support.Microsoft.FStar.Util.Inl (arg), _))::[]) | ((_, (Support.Microsoft.FStar.Util.Inl (arg), _))::(Some (true), _)::[]) -> begin
arg
end
| ((Some (false), _)::_::[]) | (_::(Some (false), _)::[]) -> begin
Microsoft_FStar_Absyn_Util.t_false
end
| _32_325 -> begin
(fallback ())
end)
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.or_lid)) with
| true -> begin
(match ((Support.All.pipe_right args (Support.List.map simplify))) with
| ((Some (true), _)::_::[]) | (_::(Some (true), _)::[]) -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| ((Some (false), _)::(_, (Support.Microsoft.FStar.Util.Inl (arg), _))::[]) | ((_, (Support.Microsoft.FStar.Util.Inl (arg), _))::(Some (false), _)::[]) -> begin
arg
end
| _32_370 -> begin
(fallback ())
end)
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.imp_lid)) with
| true -> begin
(match ((Support.All.pipe_right args (Support.List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| (Some (true), _32_398)::(_32_388, (Support.Microsoft.FStar.Util.Inl (arg), _32_392))::[] -> begin
arg
end
| _32_402 -> begin
(fallback ())
end)
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.not_lid)) with
| true -> begin
(match ((Support.All.pipe_right args (Support.List.map simplify))) with
| (Some (true), _32_406)::[] -> begin
Microsoft_FStar_Absyn_Util.t_false
end
| (Some (false), _32_412)::[] -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| _32_416 -> begin
(fallback ())
end)
end
| false -> begin
(match (((((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.forall_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.allTyp_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exists_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exTyp_lid))) with
| true -> begin
(match (args) with
| ((Support.Microsoft.FStar.Util.Inl (t), _)::[]) | (_::(Support.Microsoft.FStar.Util.Inl (t), _)::[]) -> begin
(match ((let _70_12397 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _70_12397.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((_32_431::[], body)) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| Some (false) -> begin
Microsoft_FStar_Absyn_Util.t_false
end
| _32_441 -> begin
(fallback ())
end)
end
| _32_443 -> begin
(fallback ())
end)
end
| _32_445 -> begin
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
| _32_447 -> begin
(fallback ())
end)
end)))))

let rec sn_delay = (fun ( tcenv ) ( cfg ) -> (let aux = (fun ( _32_451 ) -> (match (()) with
| () -> begin
(let _70_12423 = (sn tcenv cfg)
in _70_12423.code)
end))
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_delayed' (Support.Microsoft.FStar.Util.Inr (aux)) None cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
in (let _32_453 = cfg
in {code = t; environment = _32_453.environment; stack = empty_stack; close = _32_453.close; steps = _32_453.steps}))))
and sn = (fun ( tcenv ) ( cfg ) -> (let rebuild = (fun ( config ) -> (let rebuild_stack = (fun ( config ) -> (match ((is_stack_empty config)) with
| true -> begin
config
end
| false -> begin
(let s' = (no_eta config.steps)
in (let args = (Support.All.pipe_right config.stack.args (Support.List.map (fun ( _32_4 ) -> (match (_32_4) with
| ((Support.Microsoft.FStar.Util.Inl (t), imp), env) -> begin
(let _70_12435 = (let _70_12434 = (let _70_12433 = (sn tcenv (t_config t env s'))
in _70_12433.code)
in (Support.All.pipe_left (fun ( _70_12432 ) -> Support.Microsoft.FStar.Util.Inl (_70_12432)) _70_12434))
in (_70_12435, imp))
end
| ((Support.Microsoft.FStar.Util.Inr (v), imp), env) -> begin
(let _70_12439 = (let _70_12438 = (let _70_12437 = (wne tcenv (e_config v env s'))
in _70_12437.code)
in (Support.All.pipe_left (fun ( _70_12436 ) -> Support.Microsoft.FStar.Util.Inr (_70_12436)) _70_12438))
in (_70_12439, imp))
end))))
in (let t = (simplify_then_apply config.steps config.code args config.code.Microsoft_FStar_Absyn_Syntax.pos)
in (let _32_477 = config
in {code = t; environment = _32_477.environment; stack = empty_stack; close = _32_477.close; steps = _32_477.steps}))))
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
(let _32_484 = config
in (let _70_12441 = (eta_expand tcenv t)
in {code = _70_12441; environment = _32_484.environment; stack = _32_484.stack; close = _32_484.close; steps = _32_484.steps}))
end
| false -> begin
(let _32_486 = config
in {code = t; environment = _32_486.environment; stack = _32_486.stack; close = _32_486.close; steps = _32_486.steps})
end)))))
in (let wk = (fun ( f ) -> (match ((Support.ST.read cfg.code.Microsoft_FStar_Absyn_Syntax.tk)) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _32_497; Microsoft_FStar_Absyn_Syntax.pos = _32_495; Microsoft_FStar_Absyn_Syntax.fvs = _32_493; Microsoft_FStar_Absyn_Syntax.uvs = _32_491}) -> begin
(f (Some (Microsoft_FStar_Absyn_Syntax.ktype)) cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
end
| _32_502 -> begin
(f None cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (let config = (let _32_503 = cfg
in (let _70_12454 = (Microsoft_FStar_Absyn_Util.compress_typ cfg.code)
in {code = _70_12454; environment = _32_503.environment; stack = _32_503.stack; close = _32_503.close; steps = _32_503.steps}))
in (let is_flex = (fun ( u ) -> (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (_32_509) -> begin
false
end
| _32_512 -> begin
true
end))
in (match (config.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_32_514) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (_32_517) -> begin
(rebuild config)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(match (((Support.All.pipe_right config.steps (Support.List.contains DeltaHard)) || ((Support.All.pipe_right config.steps (Support.List.contains Delta)) && (Support.All.pipe_left Support.Prims.op_Negation (is_stack_empty config))))) with
| true -> begin
(match ((Microsoft_FStar_Tc_Env.lookup_typ_abbrev tcenv fv.Microsoft_FStar_Absyn_Syntax.v)) with
| None -> begin
(rebuild config)
end
| Some (t) -> begin
(sn tcenv (let _32_524 = config
in {code = t; environment = _32_524.environment; stack = _32_524.stack; close = _32_524.close; steps = _32_524.steps}))
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
| Some (T ((_32_530, (t, e)))) -> begin
(sn tcenv (let _32_537 = config
in {code = t; environment = e; stack = _32_537.stack; close = _32_537.close; steps = _32_537.steps}))
end
| _32_540 -> begin
(Support.All.failwith "Impossible: expected a type")
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let args = (Support.List.fold_right (fun ( a ) ( out ) -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _32_548 = config.stack
in {args = args})
in (sn tcenv (let _32_551 = config
in {code = head; environment = _32_551.environment; stack = stack; close = _32_551.close; steps = _32_551.steps}))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, t2)) -> begin
(match (config.stack.args) with
| [] -> begin
(let _32_560 = (sn_binders tcenv binders config.environment config.steps)
in (match (_32_560) with
| (binders, environment) -> begin
(let mk_lam = (fun ( t ) -> (let lam = (Support.All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, t)))
in (match (cfg.close) with
| None -> begin
lam
end
| Some (f) -> begin
(f lam)
end)))
in (let t2_cfg = (let _70_12469 = (let _70_12468 = (no_eta config.steps)
in {code = t2; environment = environment; stack = empty_stack; close = None; steps = _70_12468})
in (sn_delay tcenv _70_12469))
in (let _32_568 = t2_cfg
in (let _70_12470 = (mk_lam t2_cfg.code)
in {code = _70_12470; environment = _32_568.environment; stack = _32_568.stack; close = _32_568.close; steps = _32_568.steps}))))
end))
end
| args -> begin
(let rec beta = (fun ( env_entries ) ( binders ) ( args ) -> (match ((binders, args)) with
| ([], _32_577) -> begin
(let env = (extend_env config.environment env_entries)
in (sn tcenv (let _32_580 = config
in {code = t2; environment = env; stack = (let _32_582 = config.stack
in {args = args}); close = _32_580.close; steps = _32_580.steps})))
end
| (_32_585, []) -> begin
(let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, t2) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let env = (extend_env config.environment env_entries)
in (sn tcenv (let _32_590 = config
in {code = t; environment = env; stack = empty_stack; close = _32_590.close; steps = _32_590.steps}))))
end
| (formal::rest, actual::rest') -> begin
(let m = (match ((formal, actual)) with
| ((Support.Microsoft.FStar.Util.Inl (a), _32_602), ((Support.Microsoft.FStar.Util.Inl (t), _32_607), env)) -> begin
T ((a.Microsoft_FStar_Absyn_Syntax.v, (t, env)))
end
| ((Support.Microsoft.FStar.Util.Inr (x), _32_615), ((Support.Microsoft.FStar.Util.Inr (v), _32_620), env)) -> begin
V ((x.Microsoft_FStar_Absyn_Syntax.v, (v, env)))
end
| _32_626 -> begin
(let _70_12481 = (let _70_12480 = (let _70_12477 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.argpos (Support.Prims.fst actual))
in (Support.Microsoft.FStar.Range.string_of_range _70_12477))
in (let _70_12479 = (Microsoft_FStar_Absyn_Print.binder_to_string formal)
in (let _70_12478 = (Support.All.pipe_left Microsoft_FStar_Absyn_Print.arg_to_string (Support.Prims.fst actual))
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _70_12480 _70_12479 _70_12478))))
in (Support.All.failwith _70_12481))
end)
in (beta ((m)::env_entries) rest rest'))
end))
in (beta [] binders args))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _32_630)) -> begin
(sn tcenv (let _32_633 = config
in {code = t; environment = _32_633.environment; stack = _32_633.stack; close = _32_633.close; steps = _32_633.steps}))
end
| _32_636 -> begin
(match (config.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, comp)) -> begin
(let _32_643 = (sn_binders tcenv bs config.environment config.steps)
in (match (_32_643) with
| (binders, environment) -> begin
(let c2 = (sncomp tcenv (c_config comp environment config.steps))
in (let _32_645 = config
in (let _70_12484 = (Support.All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (binders, c2.code)))
in {code = _70_12484; environment = _32_645.environment; stack = _32_645.stack; close = _32_645.close; steps = _32_645.steps})))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, t)) -> begin
(match ((let _70_12486 = (let _70_12485 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_70_12485)::[])
in (sn_binders tcenv _70_12486 config.environment config.steps))) with
| ((Support.Microsoft.FStar.Util.Inr (x), _32_654)::[], env) -> begin
(let refine = (fun ( t ) -> (Support.All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, t))))
in (sn tcenv {code = t; environment = env; stack = empty_stack; close = (close_with_config config refine); steps = config.steps}))
end
| _32_662 -> begin
(Support.All.failwith "Impossible")
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps))) -> begin
(match ((unmeta config)) with
| true -> begin
(sn tcenv (let _32_668 = config
in {code = t; environment = _32_668.environment; stack = _32_668.stack; close = _32_668.close; steps = _32_668.steps}))
end
| false -> begin
(let pat = (fun ( t ) -> (let ps = (sn_args true tcenv config.environment config.steps ps)
in (Support.All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps)))))))
in (sn tcenv (let _32_673 = config
in {code = t; environment = _32_673.environment; stack = _32_673.stack; close = (close_with_config config pat); steps = _32_673.steps})))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b))) -> begin
(match ((unlabel config)) with
| true -> begin
(sn tcenv (let _32_682 = config
in {code = t; environment = _32_682.environment; stack = _32_682.stack; close = _32_682.close; steps = _32_682.steps}))
end
| false -> begin
(let lab = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) && (Support.All.pipe_right config.steps (Support.List.contains Simplify))) -> begin
t
end
| _32_689 -> begin
(match (config.environment.label_suffix) with
| (b', sfx)::_32_691 -> begin
(match (((b' = None) || (Some (b) = b'))) with
| true -> begin
(let _32_696 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_12497 = (Support.Microsoft.FStar.Range.string_of_range sfx)
in (Support.Microsoft.FStar.Util.fprint2 "Stripping label %s because of enclosing refresh %s\n" l _70_12497))
end
| false -> begin
()
end)
in t)
end
| false -> begin
(let _32_698 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_12498 = (Support.Microsoft.FStar.Range.string_of_range sfx)
in (Support.Microsoft.FStar.Util.fprint1 "Normalizer refreshing label: %s\n" _70_12498))
end
| false -> begin
()
end)
in (Support.All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, sfx, b))))))
end)
end
| _32_701 -> begin
(Support.All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b)))))
end)
end))
in (sn tcenv (let _32_702 = config
in {code = t; environment = _32_702.environment; stack = _32_702.stack; close = (close_with_config config lab); steps = _32_702.steps})))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))) -> begin
(match ((unmeta config)) with
| true -> begin
(sn tcenv (let _32_710 = config
in {code = t; environment = _32_710.environment; stack = _32_710.stack; close = _32_710.close; steps = _32_710.steps}))
end
| false -> begin
(let sfx = (match (b) with
| Some (false) -> begin
r
end
| _32_715 -> begin
Microsoft_FStar_Absyn_Syntax.dummyRange
end)
in (let config = (let _32_717 = config
in {code = t; environment = (let _32_719 = config.environment
in {context = _32_719.context; label_suffix = ((b, sfx))::config.environment.label_suffix}); stack = _32_717.stack; close = _32_717.close; steps = _32_717.steps})
in (sn tcenv config)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, flag))) -> begin
(match ((Support.ST.read flag)) with
| true -> begin
(let _70_12504 = (let _32_728 = config
in (let _70_12503 = (Microsoft_FStar_Absyn_Util.mk_conj t1 t2)
in {code = _70_12503; environment = _32_728.environment; stack = _32_728.stack; close = _32_728.close; steps = _32_728.steps}))
in (sn tcenv _70_12504))
end
| false -> begin
(let c1 = (sn tcenv (t_config t1 config.environment config.steps))
in (let c2 = (sn tcenv (t_config t2 config.environment config.steps))
in (let _70_12506 = (let _32_732 = config
in (let _70_12505 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((c1.code, c2.code, flag))))
in {code = _70_12505; environment = _32_732.environment; stack = _32_732.stack; close = _32_732.close; steps = _32_732.steps}))
in (rebuild _70_12506))))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named (_))) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (_) -> begin
(let _70_12511 = (let _70_12510 = (let _70_12507 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.All.pipe_right _70_12507 Support.Microsoft.FStar.Range.string_of_range))
in (let _70_12509 = (Microsoft_FStar_Absyn_Print.tag_of_typ config.code)
in (let _70_12508 = (Microsoft_FStar_Absyn_Print.typ_to_string config.code)
in (Support.Microsoft.FStar.Util.format3 "(%s) Unexpected type (%s): %s" _70_12510 _70_12509 _70_12508))))
in (Support.All.failwith _70_12511))
end)
end))))))
and sn_binders = (fun ( tcenv ) ( binders ) ( env ) ( steps ) -> (let rec aux = (fun ( out ) ( env ) ( _32_5 ) -> (match (_32_5) with
| (Support.Microsoft.FStar.Util.Inl (a), imp)::rest -> begin
(let c = (snk tcenv (k_config a.Microsoft_FStar_Absyn_Syntax.sort env steps))
in (let b = (let _70_12522 = (Microsoft_FStar_Absyn_Util.freshen_bvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _70_12522 c.code))
in (let btyp = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (let b_for_a = T ((a.Microsoft_FStar_Absyn_Syntax.v, (btyp, empty_env)))
in (aux (((Support.Microsoft.FStar.Util.Inl (b), imp))::out) (extend_env' env b_for_a) rest)))))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp)::rest -> begin
(let c = (sn_delay tcenv (t_config x.Microsoft_FStar_Absyn_Syntax.sort env steps))
in (let y = (let _70_12523 = (Microsoft_FStar_Absyn_Util.freshen_bvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _70_12523 c.code))
in (let yexp = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (let y_for_x = V ((x.Microsoft_FStar_Absyn_Syntax.v, (yexp, empty_env)))
in (aux (((Support.Microsoft.FStar.Util.Inr (y), imp))::out) (extend_env' env y_for_x) rest)))))
end
| [] -> begin
((Support.List.rev out), env)
end))
in (aux [] env binders)))
and sncomp = (fun ( tcenv ) ( cfg ) -> (let m = cfg.code
in (match (m.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let ctconf = (sncomp_typ tcenv (with_new_code cfg ct))
in (let _32_776 = cfg
in (let _70_12526 = (Microsoft_FStar_Absyn_Syntax.mk_Comp ctconf.code)
in {code = _70_12526; environment = _32_776.environment; stack = _32_776.stack; close = _32_776.close; steps = _32_776.steps})))
end
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(match ((Support.List.contains DeltaComp cfg.steps)) with
| true -> begin
(let _70_12530 = (let _70_12529 = (let _70_12528 = (let _70_12527 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (Microsoft_FStar_Absyn_Util.comp_to_comp_typ _70_12527))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp _70_12528))
in (with_new_code cfg _70_12529))
in (Support.All.pipe_left (sncomp tcenv) _70_12530))
end
| false -> begin
(let t = (sn tcenv (with_new_code cfg t))
in (let _70_12531 = (Microsoft_FStar_Absyn_Syntax.mk_Total t.code)
in (with_new_code cfg _70_12531)))
end)
end)))
and sncomp_typ = (fun ( tcenv ) ( cfg ) -> (let m = cfg.code
in (let norm = (fun ( _32_785 ) -> (match (()) with
| () -> begin
(let remake = (fun ( l ) ( r ) ( eargs ) ( flags ) -> (let c = {Microsoft_FStar_Absyn_Syntax.effect_name = l; Microsoft_FStar_Absyn_Syntax.result_typ = r; Microsoft_FStar_Absyn_Syntax.effect_args = eargs; Microsoft_FStar_Absyn_Syntax.flags = flags}
in (let _32_792 = cfg
in {code = c; environment = _32_792.environment; stack = _32_792.stack; close = _32_792.close; steps = _32_792.steps})))
in (let res = (let _70_12544 = (sn tcenv (with_new_code cfg m.Microsoft_FStar_Absyn_Syntax.result_typ))
in _70_12544.code)
in (let sn_flags = (fun ( flags ) -> (Support.All.pipe_right flags (Support.List.map (fun ( _32_6 ) -> (match (_32_6) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let e = (let _70_12548 = (wne tcenv (e_config e cfg.environment cfg.steps))
in _70_12548.code)
in Microsoft_FStar_Absyn_Syntax.DECREASES (e))
end
| f -> begin
f
end)))))
in (let _32_804 = (let _70_12550 = (sn_flags m.Microsoft_FStar_Absyn_Syntax.flags)
in (let _70_12549 = (sn_args true tcenv cfg.environment cfg.steps m.Microsoft_FStar_Absyn_Syntax.effect_args)
in (_70_12550, _70_12549)))
in (match (_32_804) with
| (flags, args) -> begin
(remake m.Microsoft_FStar_Absyn_Syntax.effect_name res args flags)
end)))))
end))
in (match ((Support.List.contains DeltaComp cfg.steps)) with
| true -> begin
(match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev tcenv m.Microsoft_FStar_Absyn_Syntax.effect_name)) with
| Some (_32_806) -> begin
(let c = (let _70_12551 = (Microsoft_FStar_Absyn_Syntax.mk_Comp m)
in (weak_norm_comp tcenv _70_12551))
in (sncomp_typ tcenv (let _32_809 = cfg
in {code = c; environment = _32_809.environment; stack = _32_809.stack; close = _32_809.close; steps = _32_809.steps})))
end
| _32_812 -> begin
(norm ())
end)
end
| false -> begin
(norm ())
end))))
and sn_args = (fun ( delay ) ( tcenv ) ( env ) ( steps ) ( args ) -> (Support.All.pipe_right args (Support.List.map (fun ( _32_7 ) -> (match (_32_7) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) when delay -> begin
(let _70_12561 = (let _70_12560 = (let _70_12559 = (sn_delay tcenv (t_config t env steps))
in _70_12559.code)
in (Support.All.pipe_left (fun ( _70_12558 ) -> Support.Microsoft.FStar.Util.Inl (_70_12558)) _70_12560))
in (_70_12561, imp))
end
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _70_12565 = (let _70_12564 = (let _70_12563 = (sn tcenv (t_config t env steps))
in _70_12563.code)
in (Support.All.pipe_left (fun ( _70_12562 ) -> Support.Microsoft.FStar.Util.Inl (_70_12562)) _70_12564))
in (_70_12565, imp))
end
| (Support.Microsoft.FStar.Util.Inr (e), imp) -> begin
(let _70_12569 = (let _70_12568 = (let _70_12567 = (wne tcenv (e_config e env steps))
in _70_12567.code)
in (Support.All.pipe_left (fun ( _70_12566 ) -> Support.Microsoft.FStar.Util.Inr (_70_12566)) _70_12568))
in (_70_12569, imp))
end)))))
and snk = (fun ( tcenv ) ( cfg ) -> (let w = (fun ( f ) -> (f cfg.code.Microsoft_FStar_Absyn_Syntax.pos))
in (match ((let _70_12579 = (Microsoft_FStar_Absyn_Util.compress_kind cfg.code)
in _70_12579.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Kind_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Kind_lam (_)) -> begin
(Support.All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) -> begin
cfg
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, args)) -> begin
(let args = (let _70_12580 = (no_eta cfg.steps)
in (sn_args false tcenv cfg.environment _70_12580 args))
in (let _32_848 = cfg
in (let _70_12582 = (Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (uv, args)))
in {code = _70_12582; environment = _32_848.environment; stack = _32_848.stack; close = _32_848.close; steps = _32_848.steps})))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev (((l, args), {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_unknown; Microsoft_FStar_Absyn_Syntax.tk = _32_860; Microsoft_FStar_Absyn_Syntax.pos = _32_858; Microsoft_FStar_Absyn_Syntax.fvs = _32_856; Microsoft_FStar_Absyn_Syntax.uvs = _32_854})) -> begin
(let _32_869 = (Microsoft_FStar_Tc_Env.lookup_kind_abbrev tcenv l)
in (match (_32_869) with
| (_32_866, binders, body) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.subst_of_list binders args)
in (let _70_12584 = (let _32_871 = cfg
in (let _70_12583 = (Microsoft_FStar_Absyn_Util.subst_kind subst body)
in {code = _70_12583; environment = _32_871.environment; stack = _32_871.stack; close = _32_871.close; steps = _32_871.steps}))
in (snk tcenv _70_12584)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_32_874, k)) -> begin
(snk tcenv (let _32_878 = cfg
in {code = k; environment = _32_878.environment; stack = _32_878.stack; close = _32_878.close; steps = _32_878.steps}))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _32_886 = (sn_binders tcenv bs cfg.environment cfg.steps)
in (match (_32_886) with
| (bs, env) -> begin
(let c2 = (snk tcenv (k_config k env cfg.steps))
in (let _32_896 = (match (c2.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs', k)) -> begin
((Support.List.append bs bs'), k)
end
| _32_893 -> begin
(bs, c2.code)
end)
in (match (_32_896) with
| (bs, rhs) -> begin
(let _32_897 = cfg
in (let _70_12586 = (Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, rhs)))
in {code = _70_12586; environment = _32_897.environment; stack = _32_897.stack; close = _32_897.close; steps = _32_897.steps}))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(Support.All.failwith "Impossible")
end)))
and wne = (fun ( tcenv ) ( cfg ) -> (let e = (Microsoft_FStar_Absyn_Util.compress_exp cfg.code)
in (let config = (let _32_903 = cfg
in {code = e; environment = _32_903.environment; stack = _32_903.stack; close = _32_903.close; steps = _32_903.steps})
in (let rebuild = (fun ( config ) -> (match ((is_stack_empty config)) with
| true -> begin
config
end
| false -> begin
(let s' = (no_eta config.steps)
in (let args = (Support.All.pipe_right config.stack.args (Support.List.map (fun ( _32_8 ) -> (match (_32_8) with
| ((Support.Microsoft.FStar.Util.Inl (t), imp), env) -> begin
(let _70_12595 = (let _70_12594 = (let _70_12593 = (sn tcenv (t_config t env s'))
in _70_12593.code)
in (Support.All.pipe_left (fun ( _70_12592 ) -> Support.Microsoft.FStar.Util.Inl (_70_12592)) _70_12594))
in (_70_12595, imp))
end
| ((Support.Microsoft.FStar.Util.Inr (v), imp), env) -> begin
(let _70_12599 = (let _70_12598 = (let _70_12597 = (wne tcenv (e_config v env s'))
in _70_12597.code)
in (Support.All.pipe_left (fun ( _70_12596 ) -> Support.Microsoft.FStar.Util.Inr (_70_12596)) _70_12598))
in (_70_12599, imp))
end))))
in (let _32_923 = config
in (let _70_12600 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (config.code, args) None config.code.Microsoft_FStar_Absyn_Syntax.pos)
in {code = _70_12600; environment = _32_923.environment; stack = empty_stack; close = _32_923.close; steps = _32_923.steps}))))
end))
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_32_926) -> begin
(Support.All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
(Support.All.pipe_right config rebuild)
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(match ((lookup_env config.environment x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText)) with
| None -> begin
(Support.All.pipe_right config rebuild)
end
| Some (V ((_32_941, (vc, env)))) -> begin
(wne tcenv (let _32_948 = config
in {code = vc; environment = env; stack = _32_948.stack; close = _32_948.close; steps = _32_948.steps}))
end
| _32_951 -> begin
(Support.All.failwith "Impossible: ill-typed term")
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(let args = (Support.List.fold_right (fun ( a ) ( out ) -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _32_959 = config.stack
in {args = args})
in (wne tcenv (let _32_962 = config
in {code = head; environment = _32_962.environment; stack = stack; close = _32_962.close; steps = _32_962.steps}))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((binders, body)) -> begin
(let rec beta = (fun ( entries ) ( binders ) ( args ) -> (match ((binders, args)) with
| ([], _32_974) -> begin
(let env = (extend_env config.environment entries)
in (wne tcenv (let _32_977 = config
in {code = body; environment = env; stack = (let _32_979 = config.stack
in {args = args}); close = _32_977.close; steps = _32_977.steps})))
end
| (_32_982, []) -> begin
(let env = (extend_env config.environment entries)
in (let _32_988 = (sn_binders tcenv binders env config.steps)
in (match (_32_988) with
| (binders, env) -> begin
(let mk_abs = (fun ( t ) -> (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (binders, t) None body.Microsoft_FStar_Absyn_Syntax.pos))
in (let c = (let _70_12612 = (let _32_991 = config
in (let _70_12611 = (no_eta config.steps)
in {code = body; environment = env; stack = (let _32_993 = config.stack
in {args = []}); close = _32_991.close; steps = _70_12611}))
in (wne tcenv _70_12612))
in (let _32_996 = c
in (let _70_12613 = (mk_abs c.code)
in {code = _70_12613; environment = _32_996.environment; stack = _32_996.stack; close = _32_996.close; steps = _32_996.steps}))))
end)))
end
| (formal::rest, actual::rest') -> begin
(let m = (match ((formal, actual)) with
| ((Support.Microsoft.FStar.Util.Inl (a), _32_1008), ((Support.Microsoft.FStar.Util.Inl (t), _32_1013), env)) -> begin
T ((a.Microsoft_FStar_Absyn_Syntax.v, (t, env)))
end
| ((Support.Microsoft.FStar.Util.Inr (x), _32_1021), ((Support.Microsoft.FStar.Util.Inr (v), _32_1026), env)) -> begin
V ((x.Microsoft_FStar_Absyn_Syntax.v, (v, env)))
end
| _32_1032 -> begin
(let _70_12618 = (let _70_12617 = (let _70_12614 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.argpos (Support.Prims.fst actual))
in (Support.Microsoft.FStar.Range.string_of_range _70_12614))
in (let _70_12616 = (Microsoft_FStar_Absyn_Print.binder_to_string formal)
in (let _70_12615 = (Support.All.pipe_left Microsoft_FStar_Absyn_Print.arg_to_string (Support.Prims.fst actual))
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _70_12617 _70_12616 _70_12615))))
in (Support.All.failwith _70_12618))
end)
in (beta ((m)::entries) rest rest'))
end))
in (beta [] binders config.stack.args))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e1, eqns)) -> begin
(let c_e1 = (wne tcenv (let _32_1038 = config
in {code = e1; environment = _32_1038.environment; stack = empty_stack; close = _32_1038.close; steps = _32_1038.steps}))
in (let wn_eqn = (fun ( _32_1045 ) -> (match (_32_1045) with
| (pat, w, body) -> begin
(let rec pat_vars = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (p::_32_1051) -> begin
(pat_vars p)
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((_32_1056, _32_1058, pats)) -> begin
(Support.List.collect pat_vars pats)
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _32_1064)) -> begin
(let _70_12623 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_70_12623)::[])
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _70_12624 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (_70_12624)::[])
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
[]
end))
in (let vars = (pat_vars pat)
in (let norm_bvvar = (fun ( x ) -> (let t = (sn tcenv (t_config x.Microsoft_FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _32_1088 = x
in {Microsoft_FStar_Absyn_Syntax.v = _32_1088.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t.code; Microsoft_FStar_Absyn_Syntax.p = _32_1088.Microsoft_FStar_Absyn_Syntax.p})))
in (let norm_btvar = (fun ( a ) -> (let k = (snk tcenv (k_config a.Microsoft_FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _32_1093 = a
in {Microsoft_FStar_Absyn_Syntax.v = _32_1093.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k.code; Microsoft_FStar_Absyn_Syntax.p = _32_1093.Microsoft_FStar_Absyn_Syntax.p})))
in (let rec norm_pat = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (pats) -> begin
(let _70_12632 = (let _70_12631 = (Support.List.map norm_pat pats)
in Microsoft_FStar_Absyn_Syntax.Pat_disj (_70_12631))
in (Microsoft_FStar_Absyn_Util.withinfo _70_12632 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let _70_12635 = (let _70_12634 = (let _70_12633 = (Support.List.map norm_pat pats)
in (fv, q, _70_12633))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_70_12634))
in (Microsoft_FStar_Absyn_Util.withinfo _70_12635 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, b)) -> begin
(let _70_12638 = (let _70_12637 = (let _70_12636 = (norm_bvvar x)
in (_70_12636, b))
in Microsoft_FStar_Absyn_Syntax.Pat_var (_70_12637))
in (Microsoft_FStar_Absyn_Util.withinfo _70_12638 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _70_12640 = (let _70_12639 = (norm_btvar a)
in Microsoft_FStar_Absyn_Syntax.Pat_tvar (_70_12639))
in (Microsoft_FStar_Absyn_Util.withinfo _70_12640 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let _70_12642 = (let _70_12641 = (norm_bvvar x)
in Microsoft_FStar_Absyn_Syntax.Pat_wild (_70_12641))
in (Microsoft_FStar_Absyn_Util.withinfo _70_12642 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let _70_12644 = (let _70_12643 = (norm_btvar a)
in Microsoft_FStar_Absyn_Syntax.Pat_twild (_70_12643))
in (Microsoft_FStar_Absyn_Util.withinfo _70_12644 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (_32_1115) -> begin
p
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e)) -> begin
(let e = (wne tcenv (e_config e config.environment config.steps))
in (let _70_12647 = (let _70_12646 = (let _70_12645 = (norm_bvvar x)
in (_70_12645, e.code))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_70_12646))
in (Microsoft_FStar_Absyn_Util.withinfo _70_12647 None p.Microsoft_FStar_Absyn_Syntax.p)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)) -> begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (let _70_12650 = (let _70_12649 = (let _70_12648 = (norm_btvar a)
in (_70_12648, t.code))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_70_12649))
in (Microsoft_FStar_Absyn_Util.withinfo _70_12650 None p.Microsoft_FStar_Absyn_Syntax.p)))
end))
in (let env_entries = (Support.List.fold_left (fun ( entries ) ( b ) -> (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let atyp = (Microsoft_FStar_Absyn_Util.btvar_to_typ a)
in (T ((a.Microsoft_FStar_Absyn_Syntax.v, (atyp, empty_env))))::entries)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let xexp = (Microsoft_FStar_Absyn_Util.bvar_to_exp x)
in (V ((x.Microsoft_FStar_Absyn_Syntax.v, (xexp, empty_env))))::entries)
end)) [] vars)
in (let env = (extend_env config.environment env_entries)
in (let w = (match (w) with
| None -> begin
None
end
| Some (w) -> begin
(let c_w = (wne tcenv (let _32_1140 = config
in {code = w; environment = env; stack = empty_stack; close = _32_1140.close; steps = _32_1140.steps}))
in Some (c_w.code))
end)
in (let c_body = (wne tcenv (let _32_1144 = config
in {code = body; environment = env; stack = empty_stack; close = _32_1144.close; steps = _32_1144.steps}))
in (let _70_12653 = (norm_pat pat)
in (_70_12653, w, c_body.code)))))))))))
end))
in (let eqns = (Support.List.map wn_eqn eqns)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_match (c_e1.code, eqns) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_right (let _32_1149 = config
in {code = e; environment = _32_1149.environment; stack = _32_1149.stack; close = _32_1149.close; steps = _32_1149.steps}) rebuild)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((is_rec, lbs), body)) -> begin
(let _32_1181 = (Support.All.pipe_right lbs (Support.List.fold_left (fun ( _32_1159 ) ( _32_1164 ) -> (match ((_32_1159, _32_1164)) with
| ((env, lbs), {Microsoft_FStar_Absyn_Syntax.lbname = x; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = eff; Microsoft_FStar_Absyn_Syntax.lbdef = e}) -> begin
(let c = (wne tcenv (let _32_1165 = config
in {code = e; environment = _32_1165.environment; stack = empty_stack; close = _32_1165.close; steps = _32_1165.steps}))
in (let t = (sn tcenv (t_config t config.environment config.steps))
in (let _32_1178 = (match (x) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(let y = (let _70_12656 = (match (is_rec) with
| true -> begin
x
end
| false -> begin
(Microsoft_FStar_Absyn_Util.freshen_bvd x)
end)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _70_12656 t.code))
in (let yexp = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (let y_for_x = V ((x, (yexp, empty_env)))
in (Support.Microsoft.FStar.Util.Inl (y.Microsoft_FStar_Absyn_Syntax.v), (extend_env' env y_for_x)))))
end
| _32_1175 -> begin
(x, env)
end)
in (match (_32_1178) with
| (y, env) -> begin
(let _70_12658 = (let _70_12657 = (Microsoft_FStar_Absyn_Syntax.mk_lb (y, eff, t.code, c.code))
in (_70_12657)::lbs)
in (env, _70_12658))
end))))
end)) (config.environment, [])))
in (match (_32_1181) with
| (env, lbs) -> begin
(let lbs = (Support.List.rev lbs)
in (let c_body = (wne tcenv (let _32_1183 = config
in {code = body; environment = env; stack = empty_stack; close = _32_1183.close; steps = _32_1183.steps}))
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), c_body.code) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_right (let _32_1187 = config
in {code = e; environment = _32_1187.environment; stack = _32_1187.stack; close = _32_1187.close; steps = _32_1187.steps}) rebuild))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, l)) -> begin
(let c = (wne tcenv (let _32_1194 = config
in {code = e; environment = _32_1194.environment; stack = _32_1194.stack; close = _32_1194.close; steps = _32_1194.steps}))
in (match ((is_stack_empty config)) with
| true -> begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (let _70_12660 = (let _32_1198 = config
in (let _70_12659 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (c.code, t.code, l) None e.Microsoft_FStar_Absyn_Syntax.pos)
in {code = _70_12659; environment = _32_1198.environment; stack = _32_1198.stack; close = _32_1198.close; steps = _32_1198.steps}))
in (rebuild _70_12660)))
end
| false -> begin
c
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, info))) -> begin
(let c = (wne tcenv (let _32_1205 = config
in {code = e; environment = _32_1205.environment; stack = _32_1205.stack; close = _32_1205.close; steps = _32_1205.steps}))
in (match ((is_stack_empty config)) with
| true -> begin
(let _70_12662 = (let _32_1208 = config
in (let _70_12661 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((c.code, info))))
in {code = _70_12661; environment = _32_1208.environment; stack = _32_1208.stack; close = _32_1208.close; steps = _32_1208.steps}))
in (rebuild _70_12662))
end
| false -> begin
c
end))
end)))))

let norm_kind = (fun ( steps ) ( tcenv ) ( k ) -> (let c = (snk tcenv (k_config k empty_env steps))
in (Microsoft_FStar_Absyn_Util.compress_kind c.code)))

let norm_typ = (fun ( steps ) ( tcenv ) ( t ) -> (let c = (sn tcenv (t_config t empty_env steps))
in c.code))

let norm_exp = (fun ( steps ) ( tcenv ) ( e ) -> (let c = (wne tcenv (e_config e empty_env steps))
in c.code))

let norm_sigelt = (fun ( tcenv ) ( _32_9 ) -> (match (_32_9) with
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, l, b)) -> begin
(let e = (let _70_12686 = (let _70_12685 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant Microsoft_FStar_Absyn_Syntax.Const_unit None r)
in (lbs, _70_12685))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_let _70_12686 None r))
in (let e = (norm_exp ((Beta)::[]) tcenv e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, _32_1234)) -> begin
Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, l, b))
end
| _32_1238 -> begin
(Support.All.failwith "Impossible")
end)))
end
| s -> begin
s
end))

let whnf = (fun ( tcenv ) ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_refine (_)) -> begin
t
end
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _70_12691 = (eta_expand tcenv t)
in (Support.All.pipe_right _70_12691 Microsoft_FStar_Absyn_Util.compress_typ))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) | (_) -> begin
(norm_typ ((WHNF)::(Beta)::(Eta)::[]) tcenv t)
end)))

let norm_comp = (fun ( steps ) ( tcenv ) ( c ) -> (let c = (sncomp tcenv (c_config c empty_env steps))
in c.code))

let normalize_kind = (fun ( tcenv ) ( k ) -> (let steps = (Eta)::(Delta)::(Beta)::[]
in (norm_kind steps tcenv k)))

let normalize_comp = (fun ( tcenv ) ( c ) -> (let steps = (Eta)::(Delta)::(Beta)::(SNComp)::(DeltaComp)::[]
in (norm_comp steps tcenv c)))

let normalize = (fun ( tcenv ) ( t ) -> (norm_typ ((DeltaHard)::(Beta)::(Eta)::[]) tcenv t))

let exp_norm_to_string = (fun ( tcenv ) ( e ) -> (let _70_12714 = (norm_exp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv e)
in (Microsoft_FStar_Absyn_Print.exp_to_string _70_12714)))

let typ_norm_to_string = (fun ( tcenv ) ( t ) -> (let _70_12719 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv t)
in (Microsoft_FStar_Absyn_Print.typ_to_string _70_12719)))

let kind_norm_to_string = (fun ( tcenv ) ( k ) -> (let _70_12724 = (norm_kind ((Beta)::(SNComp)::(Unmeta)::[]) tcenv k)
in (Microsoft_FStar_Absyn_Print.kind_to_string _70_12724)))

let formula_norm_to_string = (fun ( tcenv ) ( f ) -> (let _70_12729 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv f)
in (Microsoft_FStar_Absyn_Print.formula_to_string _70_12729)))

let comp_typ_norm_to_string = (fun ( tcenv ) ( c ) -> (let _70_12734 = (norm_comp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv c)
in (Microsoft_FStar_Absyn_Print.comp_typ_to_string _70_12734)))

let normalize_refinement = (fun ( env ) ( t0 ) -> (let t = (norm_typ ((Beta)::(WHNF)::(DeltaHard)::[]) env t0)
in (let rec aux = (fun ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi)) -> begin
(let t0 = (aux x.Microsoft_FStar_Absyn_Syntax.sort)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((y, phi1)) -> begin
(let _70_12747 = (let _70_12746 = (let _70_12745 = (let _70_12744 = (let _70_12743 = (let _70_12742 = (let _70_12741 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _70_12741))
in Support.Microsoft.FStar.Util.Inr (_70_12742))
in (_70_12743)::[])
in (Microsoft_FStar_Absyn_Util.subst_typ _70_12744 phi))
in (Microsoft_FStar_Absyn_Util.mk_conj phi1 _70_12745))
in (y, _70_12746))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _70_12747 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) t0.Microsoft_FStar_Absyn_Syntax.pos))
end
| _32_1346 -> begin
t
end))
end
| _32_1348 -> begin
t
end)))
in (aux t))))




