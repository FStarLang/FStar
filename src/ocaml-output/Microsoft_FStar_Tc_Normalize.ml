
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
'a option Support.ST.ref

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

let ___T____0 = (fun ( projectee ) -> (match (projectee) with
| T (_32_25) -> begin
_32_25
end))

let ___V____0 = (fun ( projectee ) -> (match (projectee) with
| V (_32_28) -> begin
_32_28
end))

let empty_env = {context = []; label_suffix = []}

let extend_env' = (fun ( env ) ( b ) -> (let _32_31 = env
in {context = (b)::env.context; label_suffix = _32_31.label_suffix}))

let extend_env = (fun ( env ) ( bindings ) -> (let _32_35 = env
in {context = (Support.List.append bindings env.context); label_suffix = _32_35.label_suffix}))

let lookup_env = (fun ( env ) ( key ) -> (Support.All.pipe_right env.context (Support.Microsoft.FStar.Util.find_opt (fun ( _32_1 ) -> (match (_32_1) with
| T ((a, _32_42)) -> begin
(a.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText = key)
end
| V ((x, _32_47)) -> begin
(x.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText = key)
end)))))

let fold_env = (fun ( env ) ( f ) ( acc ) -> (Support.List.fold_left (fun ( acc ) ( v ) -> (match (v) with
| T ((a, _32_57)) -> begin
(f a.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText v acc)
end
| V ((x, _32_62)) -> begin
(f x.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText v acc)
end)) acc env.context))

let empty_stack = {args = []}

let rec subst_of_env' = (fun ( env ) -> (fold_env env (fun ( _32_66 ) ( v ) ( acc ) -> (match (v) with
| T ((a, (t, env'))) -> begin
(let _70_13706 = (let _70_13705 = (let _70_13704 = (let _70_13703 = (subst_of_env' env')
in (Microsoft_FStar_Absyn_Util.subst_typ _70_13703 t))
in (a, _70_13704))
in Support.Microsoft.FStar.Util.Inl (_70_13705))
in (_70_13706)::acc)
end
| V ((x, (v, env'))) -> begin
(let _70_13710 = (let _70_13709 = (let _70_13708 = (let _70_13707 = (subst_of_env' env')
in (Microsoft_FStar_Absyn_Util.subst_exp _70_13707 v))
in (x, _70_13708))
in Support.Microsoft.FStar.Util.Inr (_70_13709))
in (_70_13710)::acc)
end)) []))

let subst_of_env = (fun ( tcenv ) ( env ) -> (subst_of_env' env))

let with_new_code = (fun ( c ) ( e ) -> {code = e; environment = c.environment; stack = empty_stack; close = None; steps = c.steps})

let rec eta_expand = (fun ( tcenv ) ( t ) -> (let k = (let _70_13720 = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (Support.All.pipe_right _70_13720 Microsoft_FStar_Absyn_Util.compress_kind))
in (let rec aux = (fun ( t ) ( k ) -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) | (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_32_98, k)) -> begin
(aux t k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((binders, k')) -> begin
(match ((let _70_13725 = (Microsoft_FStar_Absyn_Util.unascribe_typ t)
in _70_13725.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((real, body)) -> begin
(let rec aux = (fun ( real ) ( expected ) -> (match ((real, expected)) with
| (_32_115::real, _32_119::expected) -> begin
(aux real expected)
end
| ([], []) -> begin
t
end
| (_32_128::_32_126, []) -> begin
(Support.All.failwith "Ill-kinded type")
end
| ([], more) -> begin
(let _32_137 = (Microsoft_FStar_Absyn_Util.args_of_binders more)
in (match (_32_137) with
| (more, args) -> begin
(let body = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (body, args) None body.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam ((Support.List.append binders more), body) None body.Microsoft_FStar_Absyn_Syntax.pos))
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
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let _70_13733 = (let _70_13732 = (let _70_13730 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.All.pipe_right _70_13730 Support.Microsoft.FStar.Range.string_of_range))
in (let _70_13731 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "%s: Impossible: Kind_unknown: %s" _70_13732 _70_13731)))
in (Support.All.failwith _70_13733))
end))
in (aux t k))))

let is_var = (fun ( t ) -> (match ((Microsoft_FStar_Absyn_Util.compress_typ t)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (_32_162); Microsoft_FStar_Absyn_Syntax.tk = _32_160; Microsoft_FStar_Absyn_Syntax.pos = _32_158; Microsoft_FStar_Absyn_Syntax.fvs = _32_156; Microsoft_FStar_Absyn_Syntax.uvs = _32_154} -> begin
true
end
| _32_166 -> begin
false
end))

let rec eta_expand_exp = (fun ( tcenv ) ( e ) -> (let t = (let _70_13740 = (Microsoft_FStar_Tc_Recheck.recompute_typ e)
in (Support.All.pipe_right _70_13740 Microsoft_FStar_Absyn_Util.compress_typ))
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(match ((let _70_13741 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _70_13741.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs', body)) -> begin
(match (((Support.List.length bs) = (Support.List.length bs'))) with
| true -> begin
e
end
| false -> begin
(Support.All.failwith "NYI")
end)
end
| _32_179 -> begin
(let _32_182 = (Microsoft_FStar_Absyn_Util.args_of_binders bs)
in (match (_32_182) with
| (bs, args) -> begin
(let _70_13743 = (let _70_13742 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e, args) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (bs, _70_13742))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _70_13743 (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos))
end))
end)
end
| _32_184 -> begin
e
end)))

let no_eta = (Support.List.filter (fun ( _32_2 ) -> (match (_32_2) with
| Eta -> begin
false
end
| _32_188 -> begin
true
end)))

let no_eta_cfg = (fun ( c ) -> (let _32_190 = c
in (let _70_13747 = (no_eta c.steps)
in {code = _32_190.code; environment = _32_190.environment; stack = _32_190.stack; close = _32_190.close; steps = _70_13747})))

let whnf_only = (fun ( config ) -> (Support.All.pipe_right config.steps (Support.List.contains WHNF)))

let unmeta = (fun ( config ) -> (Support.All.pipe_right config.steps (Support.List.contains Unmeta)))

let unlabel = (fun ( config ) -> ((unmeta config) || (Support.All.pipe_right config.steps (Support.List.contains Unlabel))))

let is_stack_empty = (fun ( config ) -> (match (config.stack.args) with
| [] -> begin
true
end
| _32_198 -> begin
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
(let _70_13759 = (let _70_13758 = (Microsoft_FStar_Absyn_Util.freshen_bvar b)
in Support.Microsoft.FStar.Util.Inl (_70_13758))
in (_70_13759, imp))
end
| (Support.Microsoft.FStar.Util.Inr (b), imp) -> begin
(let _70_13761 = (let _70_13760 = (Microsoft_FStar_Absyn_Util.freshen_bvar b)
in Support.Microsoft.FStar.Util.Inr (_70_13760))
in (_70_13761, imp))
end)) binders)
in (let subst = (let _70_13763 = (let _70_13762 = (Microsoft_FStar_Absyn_Util.args_of_binders binders')
in (Support.All.pipe_right _70_13762 Support.Prims.snd))
in (Microsoft_FStar_Absyn_Util.subst_of_list binders _70_13763))
in (let cdef = (Microsoft_FStar_Absyn_Util.subst_comp subst cdef)
in (let subst = (let _70_13765 = (let _70_13764 = (Microsoft_FStar_Absyn_Syntax.targ c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (_70_13764)::c.Microsoft_FStar_Absyn_Syntax.effect_args)
in (Microsoft_FStar_Absyn_Util.subst_of_list binders' _70_13765))
in (let c1 = (Microsoft_FStar_Absyn_Util.subst_comp subst cdef)
in (let c = (Support.All.pipe_right (let _32_222 = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c1)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _32_222.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _32_222.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _32_222.Microsoft_FStar_Absyn_Syntax.effect_args; Microsoft_FStar_Absyn_Syntax.flags = c.Microsoft_FStar_Absyn_Syntax.flags}) Microsoft_FStar_Absyn_Syntax.mk_Comp)
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

let rec is_head_symbol = (fun ( t ) -> (match ((let _70_13796 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _70_13796.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _32_253, _32_255))) -> begin
(is_head_symbol t)
end
| _32_260 -> begin
false
end))

let simplify_then_apply = (fun ( steps ) ( head ) ( args ) ( pos ) -> (let fallback = (fun ( _32_266 ) -> (match (()) with
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
| _32_274 -> begin
None
end))
in (let simplify = (fun ( arg ) -> (match ((Support.Prims.fst arg)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
((simp_t t), arg)
end
| _32_280 -> begin
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
| _32_327 -> begin
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
| _32_372 -> begin
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
| (Some (true), _32_400)::(_32_390, (Support.Microsoft.FStar.Util.Inl (arg), _32_394))::[] -> begin
arg
end
| _32_404 -> begin
(fallback ())
end)
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.not_lid)) with
| true -> begin
(match ((Support.All.pipe_right args (Support.List.map simplify))) with
| (Some (true), _32_408)::[] -> begin
Microsoft_FStar_Absyn_Util.t_false
end
| (Some (false), _32_414)::[] -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| _32_418 -> begin
(fallback ())
end)
end
| false -> begin
(match (((((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.forall_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.allTyp_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exists_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exTyp_lid))) with
| true -> begin
(match (args) with
| ((Support.Microsoft.FStar.Util.Inl (t), _)::[]) | (_::(Support.Microsoft.FStar.Util.Inl (t), _)::[]) -> begin
(match ((let _70_13811 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _70_13811.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((_32_433::[], body)) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| Some (false) -> begin
Microsoft_FStar_Absyn_Util.t_false
end
| _32_443 -> begin
(fallback ())
end)
end
| _32_445 -> begin
(fallback ())
end)
end
| _32_447 -> begin
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
| _32_449 -> begin
(fallback ())
end)
end)))))

let rec sn_delay = (fun ( tcenv ) ( cfg ) -> (let aux = (fun ( _32_453 ) -> (match (()) with
| () -> begin
(let _70_13837 = (sn tcenv cfg)
in _70_13837.code)
end))
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_delayed' (Support.Microsoft.FStar.Util.Inr (aux)) None cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
in (let _32_455 = cfg
in {code = t; environment = _32_455.environment; stack = empty_stack; close = _32_455.close; steps = _32_455.steps}))))
and sn = (fun ( tcenv ) ( cfg ) -> (let rebuild = (fun ( config ) -> (let rebuild_stack = (fun ( config ) -> (match ((is_stack_empty config)) with
| true -> begin
config
end
| false -> begin
(let s' = (no_eta config.steps)
in (let args = (Support.All.pipe_right config.stack.args (Support.List.map (fun ( _32_4 ) -> (match (_32_4) with
| ((Support.Microsoft.FStar.Util.Inl (t), imp), env) -> begin
(let _70_13849 = (let _70_13848 = (let _70_13847 = (sn tcenv (t_config t env s'))
in _70_13847.code)
in (Support.All.pipe_left (fun ( _70_13846 ) -> Support.Microsoft.FStar.Util.Inl (_70_13846)) _70_13848))
in (_70_13849, imp))
end
| ((Support.Microsoft.FStar.Util.Inr (v), imp), env) -> begin
(let _70_13853 = (let _70_13852 = (let _70_13851 = (wne tcenv (e_config v env s'))
in _70_13851.code)
in (Support.All.pipe_left (fun ( _70_13850 ) -> Support.Microsoft.FStar.Util.Inr (_70_13850)) _70_13852))
in (_70_13853, imp))
end))))
in (let t = (simplify_then_apply config.steps config.code args config.code.Microsoft_FStar_Absyn_Syntax.pos)
in (let _32_479 = config
in {code = t; environment = _32_479.environment; stack = empty_stack; close = _32_479.close; steps = _32_479.steps}))))
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
(let _32_486 = config
in (let _70_13855 = (eta_expand tcenv t)
in {code = _70_13855; environment = _32_486.environment; stack = _32_486.stack; close = _32_486.close; steps = _32_486.steps}))
end
| false -> begin
(let _32_488 = config
in {code = t; environment = _32_488.environment; stack = _32_488.stack; close = _32_488.close; steps = _32_488.steps})
end)))))
in (let wk = (fun ( f ) -> (match ((Support.ST.read cfg.code.Microsoft_FStar_Absyn_Syntax.tk)) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _32_499; Microsoft_FStar_Absyn_Syntax.pos = _32_497; Microsoft_FStar_Absyn_Syntax.fvs = _32_495; Microsoft_FStar_Absyn_Syntax.uvs = _32_493}) -> begin
(f (Some (Microsoft_FStar_Absyn_Syntax.ktype)) cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
end
| _32_504 -> begin
(f None cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (let config = (let _32_505 = cfg
in (let _70_13868 = (Microsoft_FStar_Absyn_Util.compress_typ cfg.code)
in {code = _70_13868; environment = _32_505.environment; stack = _32_505.stack; close = _32_505.close; steps = _32_505.steps}))
in (let is_flex = (fun ( u ) -> (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (_32_511) -> begin
false
end
| _32_514 -> begin
true
end))
in (match (config.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_32_516) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (_32_519) -> begin
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
(sn tcenv (let _32_526 = config
in {code = t; environment = _32_526.environment; stack = _32_526.stack; close = _32_526.close; steps = _32_526.steps}))
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
| Some (T ((_32_532, (t, e)))) -> begin
(sn tcenv (let _32_539 = config
in {code = t; environment = e; stack = _32_539.stack; close = _32_539.close; steps = _32_539.steps}))
end
| _32_542 -> begin
(Support.All.failwith "Impossible: expected a type")
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let args = (Support.List.fold_right (fun ( a ) ( out ) -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _32_550 = config.stack
in {args = args})
in (sn tcenv (let _32_553 = config
in {code = head; environment = _32_553.environment; stack = stack; close = _32_553.close; steps = _32_553.steps}))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, t2)) -> begin
(match (config.stack.args) with
| [] -> begin
(let _32_562 = (sn_binders tcenv binders config.environment config.steps)
in (match (_32_562) with
| (binders, environment) -> begin
(let mk_lam = (fun ( t ) -> (let lam = (Support.All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, t)))
in (match (cfg.close) with
| None -> begin
lam
end
| Some (f) -> begin
(f lam)
end)))
in (let t2_cfg = (let _70_13883 = (let _70_13882 = (no_eta config.steps)
in {code = t2; environment = environment; stack = empty_stack; close = None; steps = _70_13882})
in (sn_delay tcenv _70_13883))
in (let _32_570 = t2_cfg
in (let _70_13884 = (mk_lam t2_cfg.code)
in {code = _70_13884; environment = _32_570.environment; stack = _32_570.stack; close = _32_570.close; steps = _32_570.steps}))))
end))
end
| args -> begin
(let rec beta = (fun ( env_entries ) ( binders ) ( args ) -> (match ((binders, args)) with
| ([], _32_579) -> begin
(let env = (extend_env config.environment env_entries)
in (sn tcenv (let _32_582 = config
in {code = t2; environment = env; stack = (let _32_584 = config.stack
in {args = args}); close = _32_582.close; steps = _32_582.steps})))
end
| (_32_587, []) -> begin
(let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, t2) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let env = (extend_env config.environment env_entries)
in (sn tcenv (let _32_592 = config
in {code = t; environment = env; stack = empty_stack; close = _32_592.close; steps = _32_592.steps}))))
end
| (formal::rest, actual::rest') -> begin
(let m = (match ((formal, actual)) with
| ((Support.Microsoft.FStar.Util.Inl (a), _32_604), ((Support.Microsoft.FStar.Util.Inl (t), _32_609), env)) -> begin
T ((a.Microsoft_FStar_Absyn_Syntax.v, (t, env)))
end
| ((Support.Microsoft.FStar.Util.Inr (x), _32_617), ((Support.Microsoft.FStar.Util.Inr (v), _32_622), env)) -> begin
V ((x.Microsoft_FStar_Absyn_Syntax.v, (v, env)))
end
| _32_628 -> begin
(let _70_13895 = (let _70_13894 = (let _70_13891 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.argpos (Support.Prims.fst actual))
in (Support.Microsoft.FStar.Range.string_of_range _70_13891))
in (let _70_13893 = (Microsoft_FStar_Absyn_Print.binder_to_string formal)
in (let _70_13892 = (Support.All.pipe_left Microsoft_FStar_Absyn_Print.arg_to_string (Support.Prims.fst actual))
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _70_13894 _70_13893 _70_13892))))
in (Support.All.failwith _70_13895))
end)
in (beta ((m)::env_entries) rest rest'))
end))
in (beta [] binders args))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _32_632)) -> begin
(sn tcenv (let _32_635 = config
in {code = t; environment = _32_635.environment; stack = _32_635.stack; close = _32_635.close; steps = _32_635.steps}))
end
| _32_638 -> begin
(match (config.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, comp)) -> begin
(let _32_645 = (sn_binders tcenv bs config.environment config.steps)
in (match (_32_645) with
| (binders, environment) -> begin
(let c2 = (sncomp tcenv (c_config comp environment config.steps))
in (let _32_647 = config
in (let _70_13898 = (Support.All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (binders, c2.code)))
in {code = _70_13898; environment = _32_647.environment; stack = _32_647.stack; close = _32_647.close; steps = _32_647.steps})))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, t)) -> begin
(match ((let _70_13900 = (let _70_13899 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_70_13899)::[])
in (sn_binders tcenv _70_13900 config.environment config.steps))) with
| ((Support.Microsoft.FStar.Util.Inr (x), _32_656)::[], env) -> begin
(let refine = (fun ( t ) -> (Support.All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, t))))
in (sn tcenv {code = t; environment = env; stack = empty_stack; close = (close_with_config config refine); steps = config.steps}))
end
| _32_664 -> begin
(Support.All.failwith "Impossible")
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps))) -> begin
(match ((unmeta config)) with
| true -> begin
(sn tcenv (let _32_670 = config
in {code = t; environment = _32_670.environment; stack = _32_670.stack; close = _32_670.close; steps = _32_670.steps}))
end
| false -> begin
(let pat = (fun ( t ) -> (let ps = (sn_args true tcenv config.environment config.steps ps)
in (Support.All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps)))))))
in (sn tcenv (let _32_675 = config
in {code = t; environment = _32_675.environment; stack = _32_675.stack; close = (close_with_config config pat); steps = _32_675.steps})))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b))) -> begin
(match ((unlabel config)) with
| true -> begin
(sn tcenv (let _32_684 = config
in {code = t; environment = _32_684.environment; stack = _32_684.stack; close = _32_684.close; steps = _32_684.steps}))
end
| false -> begin
(let lab = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) && (Support.All.pipe_right config.steps (Support.List.contains Simplify))) -> begin
t
end
| _32_691 -> begin
(match (config.environment.label_suffix) with
| (b', sfx)::_32_693 -> begin
(match (((b' = None) || (Some (b) = b'))) with
| true -> begin
(let _32_698 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_13911 = (Support.Microsoft.FStar.Range.string_of_range sfx)
in (Support.Microsoft.FStar.Util.fprint2 "Stripping label %s because of enclosing refresh %s\n" l _70_13911))
end
| false -> begin
()
end)
in t)
end
| false -> begin
(let _32_700 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_13912 = (Support.Microsoft.FStar.Range.string_of_range sfx)
in (Support.Microsoft.FStar.Util.fprint1 "Normalizer refreshing label: %s\n" _70_13912))
end
| false -> begin
()
end)
in (Support.All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, sfx, b))))))
end)
end
| _32_703 -> begin
(Support.All.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b)))))
end)
end))
in (sn tcenv (let _32_704 = config
in {code = t; environment = _32_704.environment; stack = _32_704.stack; close = (close_with_config config lab); steps = _32_704.steps})))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))) -> begin
(match ((unmeta config)) with
| true -> begin
(sn tcenv (let _32_712 = config
in {code = t; environment = _32_712.environment; stack = _32_712.stack; close = _32_712.close; steps = _32_712.steps}))
end
| false -> begin
(let sfx = (match (b) with
| Some (false) -> begin
r
end
| _32_717 -> begin
Microsoft_FStar_Absyn_Syntax.dummyRange
end)
in (let config = (let _32_719 = config
in {code = t; environment = (let _32_721 = config.environment
in {context = _32_721.context; label_suffix = ((b, sfx))::config.environment.label_suffix}); stack = _32_719.stack; close = _32_719.close; steps = _32_719.steps})
in (sn tcenv config)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, flag))) -> begin
(match ((Support.ST.read flag)) with
| true -> begin
(let _70_13918 = (let _32_730 = config
in (let _70_13917 = (Microsoft_FStar_Absyn_Util.mk_conj t1 t2)
in {code = _70_13917; environment = _32_730.environment; stack = _32_730.stack; close = _32_730.close; steps = _32_730.steps}))
in (sn tcenv _70_13918))
end
| false -> begin
(let c1 = (sn tcenv (t_config t1 config.environment config.steps))
in (let c2 = (sn tcenv (t_config t2 config.environment config.steps))
in (let _70_13920 = (let _32_734 = config
in (let _70_13919 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((c1.code, c2.code, flag))))
in {code = _70_13919; environment = _32_734.environment; stack = _32_734.stack; close = _32_734.close; steps = _32_734.steps}))
in (rebuild _70_13920))))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named (_))) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (_) -> begin
(let _70_13925 = (let _70_13924 = (let _70_13921 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.All.pipe_right _70_13921 Support.Microsoft.FStar.Range.string_of_range))
in (let _70_13923 = (Microsoft_FStar_Absyn_Print.tag_of_typ config.code)
in (let _70_13922 = (Microsoft_FStar_Absyn_Print.typ_to_string config.code)
in (Support.Microsoft.FStar.Util.format3 "(%s) Unexpected type (%s): %s" _70_13924 _70_13923 _70_13922))))
in (Support.All.failwith _70_13925))
end)
end))))))
and sn_binders = (fun ( tcenv ) ( binders ) ( env ) ( steps ) -> (let rec aux = (fun ( out ) ( env ) ( _32_5 ) -> (match (_32_5) with
| (Support.Microsoft.FStar.Util.Inl (a), imp)::rest -> begin
(let c = (snk tcenv (k_config a.Microsoft_FStar_Absyn_Syntax.sort env steps))
in (let b = (let _70_13936 = (Microsoft_FStar_Absyn_Util.freshen_bvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _70_13936 c.code))
in (let btyp = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (let b_for_a = T ((a.Microsoft_FStar_Absyn_Syntax.v, (btyp, empty_env)))
in (aux (((Support.Microsoft.FStar.Util.Inl (b), imp))::out) (extend_env' env b_for_a) rest)))))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp)::rest -> begin
(let c = (sn_delay tcenv (t_config x.Microsoft_FStar_Absyn_Syntax.sort env steps))
in (let y = (let _70_13937 = (Microsoft_FStar_Absyn_Util.freshen_bvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _70_13937 c.code))
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
in (let _32_778 = cfg
in (let _70_13940 = (Microsoft_FStar_Absyn_Syntax.mk_Comp ctconf.code)
in {code = _70_13940; environment = _32_778.environment; stack = _32_778.stack; close = _32_778.close; steps = _32_778.steps})))
end
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(match ((Support.List.contains DeltaComp cfg.steps)) with
| true -> begin
(let _70_13944 = (let _70_13943 = (let _70_13942 = (let _70_13941 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (Microsoft_FStar_Absyn_Util.comp_to_comp_typ _70_13941))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp _70_13942))
in (with_new_code cfg _70_13943))
in (Support.All.pipe_left (sncomp tcenv) _70_13944))
end
| false -> begin
(let t = (sn tcenv (with_new_code cfg t))
in (let _70_13945 = (Microsoft_FStar_Absyn_Syntax.mk_Total t.code)
in (with_new_code cfg _70_13945)))
end)
end)))
and sncomp_typ = (fun ( tcenv ) ( cfg ) -> (let m = cfg.code
in (let norm = (fun ( _32_787 ) -> (match (()) with
| () -> begin
(let remake = (fun ( l ) ( r ) ( eargs ) ( flags ) -> (let c = {Microsoft_FStar_Absyn_Syntax.effect_name = l; Microsoft_FStar_Absyn_Syntax.result_typ = r; Microsoft_FStar_Absyn_Syntax.effect_args = eargs; Microsoft_FStar_Absyn_Syntax.flags = flags}
in (let _32_794 = cfg
in {code = c; environment = _32_794.environment; stack = _32_794.stack; close = _32_794.close; steps = _32_794.steps})))
in (let res = (let _70_13958 = (sn tcenv (with_new_code cfg m.Microsoft_FStar_Absyn_Syntax.result_typ))
in _70_13958.code)
in (let sn_flags = (fun ( flags ) -> (Support.All.pipe_right flags (Support.List.map (fun ( _32_6 ) -> (match (_32_6) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let e = (let _70_13962 = (wne tcenv (e_config e cfg.environment cfg.steps))
in _70_13962.code)
in Microsoft_FStar_Absyn_Syntax.DECREASES (e))
end
| f -> begin
f
end)))))
in (let _32_806 = (let _70_13964 = (sn_flags m.Microsoft_FStar_Absyn_Syntax.flags)
in (let _70_13963 = (sn_args true tcenv cfg.environment cfg.steps m.Microsoft_FStar_Absyn_Syntax.effect_args)
in (_70_13964, _70_13963)))
in (match (_32_806) with
| (flags, args) -> begin
(remake m.Microsoft_FStar_Absyn_Syntax.effect_name res args flags)
end)))))
end))
in (match ((Support.List.contains DeltaComp cfg.steps)) with
| true -> begin
(match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev tcenv m.Microsoft_FStar_Absyn_Syntax.effect_name)) with
| Some (_32_808) -> begin
(let c = (let _70_13965 = (Microsoft_FStar_Absyn_Syntax.mk_Comp m)
in (weak_norm_comp tcenv _70_13965))
in (sncomp_typ tcenv (let _32_811 = cfg
in {code = c; environment = _32_811.environment; stack = _32_811.stack; close = _32_811.close; steps = _32_811.steps})))
end
| _32_814 -> begin
(norm ())
end)
end
| false -> begin
(norm ())
end))))
and sn_args = (fun ( delay ) ( tcenv ) ( env ) ( steps ) ( args ) -> (Support.All.pipe_right args (Support.List.map (fun ( _32_7 ) -> (match (_32_7) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) when delay -> begin
(let _70_13975 = (let _70_13974 = (let _70_13973 = (sn_delay tcenv (t_config t env steps))
in _70_13973.code)
in (Support.All.pipe_left (fun ( _70_13972 ) -> Support.Microsoft.FStar.Util.Inl (_70_13972)) _70_13974))
in (_70_13975, imp))
end
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _70_13979 = (let _70_13978 = (let _70_13977 = (sn tcenv (t_config t env steps))
in _70_13977.code)
in (Support.All.pipe_left (fun ( _70_13976 ) -> Support.Microsoft.FStar.Util.Inl (_70_13976)) _70_13978))
in (_70_13979, imp))
end
| (Support.Microsoft.FStar.Util.Inr (e), imp) -> begin
(let _70_13983 = (let _70_13982 = (let _70_13981 = (wne tcenv (e_config e env steps))
in _70_13981.code)
in (Support.All.pipe_left (fun ( _70_13980 ) -> Support.Microsoft.FStar.Util.Inr (_70_13980)) _70_13982))
in (_70_13983, imp))
end)))))
and snk = (fun ( tcenv ) ( cfg ) -> (let w = (fun ( f ) -> (f cfg.code.Microsoft_FStar_Absyn_Syntax.pos))
in (match ((let _70_13993 = (Microsoft_FStar_Absyn_Util.compress_kind cfg.code)
in _70_13993.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Kind_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Kind_lam (_)) -> begin
(Support.All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) -> begin
cfg
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, args)) -> begin
(let args = (let _70_13994 = (no_eta cfg.steps)
in (sn_args false tcenv cfg.environment _70_13994 args))
in (let _32_850 = cfg
in (let _70_13996 = (Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (uv, args)))
in {code = _70_13996; environment = _32_850.environment; stack = _32_850.stack; close = _32_850.close; steps = _32_850.steps})))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev (((l, args), {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_unknown; Microsoft_FStar_Absyn_Syntax.tk = _32_862; Microsoft_FStar_Absyn_Syntax.pos = _32_860; Microsoft_FStar_Absyn_Syntax.fvs = _32_858; Microsoft_FStar_Absyn_Syntax.uvs = _32_856})) -> begin
(let _32_871 = (Microsoft_FStar_Tc_Env.lookup_kind_abbrev tcenv l)
in (match (_32_871) with
| (_32_868, binders, body) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.subst_of_list binders args)
in (let _70_13998 = (let _32_873 = cfg
in (let _70_13997 = (Microsoft_FStar_Absyn_Util.subst_kind subst body)
in {code = _70_13997; environment = _32_873.environment; stack = _32_873.stack; close = _32_873.close; steps = _32_873.steps}))
in (snk tcenv _70_13998)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_32_876, k)) -> begin
(snk tcenv (let _32_880 = cfg
in {code = k; environment = _32_880.environment; stack = _32_880.stack; close = _32_880.close; steps = _32_880.steps}))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _32_888 = (sn_binders tcenv bs cfg.environment cfg.steps)
in (match (_32_888) with
| (bs, env) -> begin
(let c2 = (snk tcenv (k_config k env cfg.steps))
in (let _32_898 = (match (c2.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs', k)) -> begin
((Support.List.append bs bs'), k)
end
| _32_895 -> begin
(bs, c2.code)
end)
in (match (_32_898) with
| (bs, rhs) -> begin
(let _32_899 = cfg
in (let _70_14000 = (Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, rhs)))
in {code = _70_14000; environment = _32_899.environment; stack = _32_899.stack; close = _32_899.close; steps = _32_899.steps}))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(Support.All.failwith "Impossible")
end)))
and wne = (fun ( tcenv ) ( cfg ) -> (let e = (Microsoft_FStar_Absyn_Util.compress_exp cfg.code)
in (let config = (let _32_905 = cfg
in {code = e; environment = _32_905.environment; stack = _32_905.stack; close = _32_905.close; steps = _32_905.steps})
in (let rebuild = (fun ( config ) -> (match ((is_stack_empty config)) with
| true -> begin
config
end
| false -> begin
(let s' = (no_eta config.steps)
in (let args = (Support.All.pipe_right config.stack.args (Support.List.map (fun ( _32_8 ) -> (match (_32_8) with
| ((Support.Microsoft.FStar.Util.Inl (t), imp), env) -> begin
(let _70_14009 = (let _70_14008 = (let _70_14007 = (sn tcenv (t_config t env s'))
in _70_14007.code)
in (Support.All.pipe_left (fun ( _70_14006 ) -> Support.Microsoft.FStar.Util.Inl (_70_14006)) _70_14008))
in (_70_14009, imp))
end
| ((Support.Microsoft.FStar.Util.Inr (v), imp), env) -> begin
(let _70_14013 = (let _70_14012 = (let _70_14011 = (wne tcenv (e_config v env s'))
in _70_14011.code)
in (Support.All.pipe_left (fun ( _70_14010 ) -> Support.Microsoft.FStar.Util.Inr (_70_14010)) _70_14012))
in (_70_14013, imp))
end))))
in (let _32_925 = config
in (let _70_14014 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (config.code, args) None config.code.Microsoft_FStar_Absyn_Syntax.pos)
in {code = _70_14014; environment = _32_925.environment; stack = empty_stack; close = _32_925.close; steps = _32_925.steps}))))
end))
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_32_928) -> begin
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
| Some (V ((_32_943, (vc, env)))) -> begin
(wne tcenv (let _32_950 = config
in {code = vc; environment = env; stack = _32_950.stack; close = _32_950.close; steps = _32_950.steps}))
end
| _32_953 -> begin
(Support.All.failwith "Impossible: ill-typed term")
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(let args = (Support.List.fold_right (fun ( a ) ( out ) -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _32_961 = config.stack
in {args = args})
in (wne tcenv (let _32_964 = config
in {code = head; environment = _32_964.environment; stack = stack; close = _32_964.close; steps = _32_964.steps}))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((binders, body)) -> begin
(let rec beta = (fun ( entries ) ( binders ) ( args ) -> (match ((binders, args)) with
| ([], _32_976) -> begin
(let env = (extend_env config.environment entries)
in (wne tcenv (let _32_979 = config
in {code = body; environment = env; stack = (let _32_981 = config.stack
in {args = args}); close = _32_979.close; steps = _32_979.steps})))
end
| (_32_984, []) -> begin
(let env = (extend_env config.environment entries)
in (let _32_990 = (sn_binders tcenv binders env config.steps)
in (match (_32_990) with
| (binders, env) -> begin
(let mk_abs = (fun ( t ) -> (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (binders, t) None body.Microsoft_FStar_Absyn_Syntax.pos))
in (let c = (let _70_14026 = (let _32_993 = config
in (let _70_14025 = (no_eta config.steps)
in {code = body; environment = env; stack = (let _32_995 = config.stack
in {args = []}); close = _32_993.close; steps = _70_14025}))
in (wne tcenv _70_14026))
in (let _32_998 = c
in (let _70_14027 = (mk_abs c.code)
in {code = _70_14027; environment = _32_998.environment; stack = _32_998.stack; close = _32_998.close; steps = _32_998.steps}))))
end)))
end
| (formal::rest, actual::rest') -> begin
(let m = (match ((formal, actual)) with
| ((Support.Microsoft.FStar.Util.Inl (a), _32_1010), ((Support.Microsoft.FStar.Util.Inl (t), _32_1015), env)) -> begin
T ((a.Microsoft_FStar_Absyn_Syntax.v, (t, env)))
end
| ((Support.Microsoft.FStar.Util.Inr (x), _32_1023), ((Support.Microsoft.FStar.Util.Inr (v), _32_1028), env)) -> begin
V ((x.Microsoft_FStar_Absyn_Syntax.v, (v, env)))
end
| _32_1034 -> begin
(let _70_14032 = (let _70_14031 = (let _70_14028 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.argpos (Support.Prims.fst actual))
in (Support.Microsoft.FStar.Range.string_of_range _70_14028))
in (let _70_14030 = (Microsoft_FStar_Absyn_Print.binder_to_string formal)
in (let _70_14029 = (Support.All.pipe_left Microsoft_FStar_Absyn_Print.arg_to_string (Support.Prims.fst actual))
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _70_14031 _70_14030 _70_14029))))
in (Support.All.failwith _70_14032))
end)
in (beta ((m)::entries) rest rest'))
end))
in (beta [] binders config.stack.args))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e1, eqns)) -> begin
(let c_e1 = (wne tcenv (let _32_1040 = config
in {code = e1; environment = _32_1040.environment; stack = empty_stack; close = _32_1040.close; steps = _32_1040.steps}))
in (let wn_eqn = (fun ( _32_1047 ) -> (match (_32_1047) with
| (pat, w, body) -> begin
(let rec pat_vars = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (p::_32_1053) -> begin
(pat_vars p)
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((_32_1058, _32_1060, pats)) -> begin
(Support.List.collect (fun ( _32_1067 ) -> (match (_32_1067) with
| (x, _32_1066) -> begin
(pat_vars x)
end)) pats)
end
| Microsoft_FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _70_14038 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_70_14038)::[])
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _70_14039 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (_70_14039)::[])
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
[]
end))
in (let vars = (pat_vars pat)
in (let norm_bvvar = (fun ( x ) -> (let t = (sn tcenv (t_config x.Microsoft_FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _32_1091 = x
in {Microsoft_FStar_Absyn_Syntax.v = _32_1091.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t.code; Microsoft_FStar_Absyn_Syntax.p = _32_1091.Microsoft_FStar_Absyn_Syntax.p})))
in (let norm_btvar = (fun ( a ) -> (let k = (snk tcenv (k_config a.Microsoft_FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _32_1096 = a
in {Microsoft_FStar_Absyn_Syntax.v = _32_1096.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k.code; Microsoft_FStar_Absyn_Syntax.p = _32_1096.Microsoft_FStar_Absyn_Syntax.p})))
in (let rec norm_pat = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (pats) -> begin
(let _70_14047 = (let _70_14046 = (Support.List.map norm_pat pats)
in Microsoft_FStar_Absyn_Syntax.Pat_disj (_70_14046))
in (Microsoft_FStar_Absyn_Util.withinfo _70_14047 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let _70_14052 = (let _70_14051 = (let _70_14050 = (Support.List.map (fun ( _32_1109 ) -> (match (_32_1109) with
| (x, i) -> begin
(let _70_14049 = (norm_pat x)
in (_70_14049, i))
end)) pats)
in (fv, q, _70_14050))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_70_14051))
in (Microsoft_FStar_Absyn_Util.withinfo _70_14052 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _70_14054 = (let _70_14053 = (norm_bvvar x)
in Microsoft_FStar_Absyn_Syntax.Pat_var (_70_14053))
in (Microsoft_FStar_Absyn_Util.withinfo _70_14054 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _70_14056 = (let _70_14055 = (norm_btvar a)
in Microsoft_FStar_Absyn_Syntax.Pat_tvar (_70_14055))
in (Microsoft_FStar_Absyn_Util.withinfo _70_14056 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let _70_14058 = (let _70_14057 = (norm_bvvar x)
in Microsoft_FStar_Absyn_Syntax.Pat_wild (_70_14057))
in (Microsoft_FStar_Absyn_Util.withinfo _70_14058 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let _70_14060 = (let _70_14059 = (norm_btvar a)
in Microsoft_FStar_Absyn_Syntax.Pat_twild (_70_14059))
in (Microsoft_FStar_Absyn_Util.withinfo _70_14060 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (_32_1119) -> begin
p
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e)) -> begin
(let e = (wne tcenv (e_config e config.environment config.steps))
in (let _70_14063 = (let _70_14062 = (let _70_14061 = (norm_bvvar x)
in (_70_14061, e.code))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_70_14062))
in (Microsoft_FStar_Absyn_Util.withinfo _70_14063 None p.Microsoft_FStar_Absyn_Syntax.p)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)) -> begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (let _70_14066 = (let _70_14065 = (let _70_14064 = (norm_btvar a)
in (_70_14064, t.code))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_70_14065))
in (Microsoft_FStar_Absyn_Util.withinfo _70_14066 None p.Microsoft_FStar_Absyn_Syntax.p)))
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
(let c_w = (wne tcenv (let _32_1144 = config
in {code = w; environment = env; stack = empty_stack; close = _32_1144.close; steps = _32_1144.steps}))
in Some (c_w.code))
end)
in (let c_body = (wne tcenv (let _32_1148 = config
in {code = body; environment = env; stack = empty_stack; close = _32_1148.close; steps = _32_1148.steps}))
in (let _70_14069 = (norm_pat pat)
in (_70_14069, w, c_body.code)))))))))))
end))
in (let eqns = (Support.List.map wn_eqn eqns)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_match (c_e1.code, eqns) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_right (let _32_1153 = config
in {code = e; environment = _32_1153.environment; stack = _32_1153.stack; close = _32_1153.close; steps = _32_1153.steps}) rebuild)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((is_rec, lbs), body)) -> begin
(let _32_1185 = (Support.All.pipe_right lbs (Support.List.fold_left (fun ( _32_1163 ) ( _32_1168 ) -> (match ((_32_1163, _32_1168)) with
| ((env, lbs), {Microsoft_FStar_Absyn_Syntax.lbname = x; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = eff; Microsoft_FStar_Absyn_Syntax.lbdef = e}) -> begin
(let c = (wne tcenv (let _32_1169 = config
in {code = e; environment = _32_1169.environment; stack = empty_stack; close = _32_1169.close; steps = _32_1169.steps}))
in (let t = (sn tcenv (t_config t config.environment config.steps))
in (let _32_1182 = (match (x) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(let y = (let _70_14072 = (match (is_rec) with
| true -> begin
x
end
| false -> begin
(Microsoft_FStar_Absyn_Util.freshen_bvd x)
end)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _70_14072 t.code))
in (let yexp = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (let y_for_x = V ((x, (yexp, empty_env)))
in (Support.Microsoft.FStar.Util.Inl (y.Microsoft_FStar_Absyn_Syntax.v), (extend_env' env y_for_x)))))
end
| _32_1179 -> begin
(x, env)
end)
in (match (_32_1182) with
| (y, env) -> begin
(let _70_14074 = (let _70_14073 = (Microsoft_FStar_Absyn_Syntax.mk_lb (y, eff, t.code, c.code))
in (_70_14073)::lbs)
in (env, _70_14074))
end))))
end)) (config.environment, [])))
in (match (_32_1185) with
| (env, lbs) -> begin
(let lbs = (Support.List.rev lbs)
in (let c_body = (wne tcenv (let _32_1187 = config
in {code = body; environment = env; stack = empty_stack; close = _32_1187.close; steps = _32_1187.steps}))
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), c_body.code) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_right (let _32_1191 = config
in {code = e; environment = _32_1191.environment; stack = _32_1191.stack; close = _32_1191.close; steps = _32_1191.steps}) rebuild))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, l)) -> begin
(let c = (wne tcenv (let _32_1198 = config
in {code = e; environment = _32_1198.environment; stack = _32_1198.stack; close = _32_1198.close; steps = _32_1198.steps}))
in (match ((is_stack_empty config)) with
| true -> begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (let _70_14076 = (let _32_1202 = config
in (let _70_14075 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (c.code, t.code, l) None e.Microsoft_FStar_Absyn_Syntax.pos)
in {code = _70_14075; environment = _32_1202.environment; stack = _32_1202.stack; close = _32_1202.close; steps = _32_1202.steps}))
in (rebuild _70_14076)))
end
| false -> begin
c
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, info))) -> begin
(let c = (wne tcenv (let _32_1209 = config
in {code = e; environment = _32_1209.environment; stack = _32_1209.stack; close = _32_1209.close; steps = _32_1209.steps}))
in (match ((is_stack_empty config)) with
| true -> begin
(let _70_14078 = (let _32_1212 = config
in (let _70_14077 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((c.code, info))))
in {code = _70_14077; environment = _32_1212.environment; stack = _32_1212.stack; close = _32_1212.close; steps = _32_1212.steps}))
in (rebuild _70_14078))
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
(let e = (let _70_14102 = (let _70_14101 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant Microsoft_FStar_Absyn_Syntax.Const_unit None r)
in (lbs, _70_14101))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_let _70_14102 None r))
in (let e = (norm_exp ((Beta)::[]) tcenv e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, _32_1238)) -> begin
Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, l, b))
end
| _32_1242 -> begin
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
(let _70_14107 = (eta_expand tcenv t)
in (Support.All.pipe_right _70_14107 Microsoft_FStar_Absyn_Util.compress_typ))
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

let exp_norm_to_string = (fun ( tcenv ) ( e ) -> (let _70_14130 = (norm_exp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv e)
in (Microsoft_FStar_Absyn_Print.exp_to_string _70_14130)))

let typ_norm_to_string = (fun ( tcenv ) ( t ) -> (let _70_14135 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv t)
in (Microsoft_FStar_Absyn_Print.typ_to_string _70_14135)))

let kind_norm_to_string = (fun ( tcenv ) ( k ) -> (let _70_14140 = (norm_kind ((Beta)::(SNComp)::(Unmeta)::[]) tcenv k)
in (Microsoft_FStar_Absyn_Print.kind_to_string _70_14140)))

let formula_norm_to_string = (fun ( tcenv ) ( f ) -> (let _70_14145 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv f)
in (Microsoft_FStar_Absyn_Print.formula_to_string _70_14145)))

let comp_typ_norm_to_string = (fun ( tcenv ) ( c ) -> (let _70_14150 = (norm_comp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv c)
in (Microsoft_FStar_Absyn_Print.comp_typ_to_string _70_14150)))

let normalize_refinement = (fun ( env ) ( t0 ) -> (let t = (norm_typ ((Beta)::(WHNF)::(DeltaHard)::[]) env t0)
in (let rec aux = (fun ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi)) -> begin
(let t0 = (aux x.Microsoft_FStar_Absyn_Syntax.sort)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((y, phi1)) -> begin
(let _70_14163 = (let _70_14162 = (let _70_14161 = (let _70_14160 = (let _70_14159 = (let _70_14158 = (let _70_14157 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _70_14157))
in Support.Microsoft.FStar.Util.Inr (_70_14158))
in (_70_14159)::[])
in (Microsoft_FStar_Absyn_Util.subst_typ _70_14160 phi))
in (Microsoft_FStar_Absyn_Util.mk_conj phi1 _70_14161))
in (y, _70_14162))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _70_14163 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) t0.Microsoft_FStar_Absyn_Syntax.pos))
end
| _32_1350 -> begin
t
end))
end
| _32_1352 -> begin
t
end)))
in (aux t))))




