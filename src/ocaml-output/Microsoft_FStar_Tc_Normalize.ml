
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

let is_Mkconfig = (fun ( _ ) -> (failwith ("Not yet implemented")))

let is_Mkenvironment = (fun ( _ ) -> (failwith ("Not yet implemented")))

let is_Mkstack = (fun ( _ ) -> (failwith ("Not yet implemented")))

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

let extend_env' = (fun ( env ) ( b ) -> (let _30_29 = env
in {context = (b)::env.context; label_suffix = _30_29.label_suffix}))

let extend_env = (fun ( env ) ( bindings ) -> (let _30_33 = env
in {context = (Support.List.append bindings env.context); label_suffix = _30_33.label_suffix}))

let lookup_env = (fun ( env ) ( key ) -> (Support.Prims.pipe_right env.context (Support.Microsoft.FStar.Util.find_opt (fun ( _30_1 ) -> (match (_30_1) with
| T ((a, _)) -> begin
(a.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText = key)
end
| V ((x, _)) -> begin
(x.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText = key)
end)))))

let fold_env = (fun ( env ) ( f ) ( acc ) -> (Support.List.fold_left (fun ( acc ) ( v ) -> (match (v) with
| T ((a, _)) -> begin
(f a.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText v acc)
end
| V ((x, _)) -> begin
(f x.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText v acc)
end)) acc env.context))

let empty_stack = {args = []}

let rec subst_of_env' = (fun ( env ) -> (fold_env env (fun ( _30_64 ) ( v ) ( acc ) -> (match (v) with
| T ((a, (t, env'))) -> begin
(let _52_8724 = (let _52_8723 = (let _52_8722 = (let _52_8721 = (subst_of_env' env')
in (Microsoft_FStar_Absyn_Util.subst_typ _52_8721 t))
in (a, _52_8722))
in Support.Microsoft.FStar.Util.Inl (_52_8723))
in (_52_8724)::acc)
end
| V ((x, (v, env'))) -> begin
(let _52_8728 = (let _52_8727 = (let _52_8726 = (let _52_8725 = (subst_of_env' env')
in (Microsoft_FStar_Absyn_Util.subst_exp _52_8725 v))
in (x, _52_8726))
in Support.Microsoft.FStar.Util.Inr (_52_8727))
in (_52_8728)::acc)
end)) []))

let subst_of_env = (fun ( tcenv ) ( env ) -> (subst_of_env' env))

let with_new_code = (fun ( c ) ( e ) -> {code = e; environment = c.environment; stack = empty_stack; close = None; steps = c.steps})

let rec eta_expand = (fun ( tcenv ) ( t ) -> (let k = (let _52_8738 = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (Support.Prims.pipe_right _52_8738 Microsoft_FStar_Absyn_Util.compress_kind))
in (let rec aux = (fun ( t ) ( k ) -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) | (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(aux t k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((binders, k')) -> begin
(match ((let _52_8743 = (Microsoft_FStar_Absyn_Util.unascribe_typ t)
in _52_8743.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((real, body)) -> begin
(let rec aux = (fun ( real ) ( expected ) -> (match ((real, expected)) with
| (_::real, _::expected) -> begin
(aux real expected)
end
| ([], []) -> begin
t
end
| (_::_, []) -> begin
(failwith ("Ill-kinded type"))
end
| ([], more) -> begin
(let _30_135 = (Microsoft_FStar_Absyn_Util.args_of_binders more)
in (match (_30_135) with
| (more, args) -> begin
(let body = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (body, args) None body.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam ((Support.List.append binders more), body) None body.Microsoft_FStar_Absyn_Syntax.pos))
end))
end))
in (aux real binders))
end
| _ -> begin
(let _30_141 = (Microsoft_FStar_Absyn_Util.args_of_binders binders)
in (match (_30_141) with
| (binders, args) -> begin
(let body = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t, args) None t.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, body) None t.Microsoft_FStar_Absyn_Syntax.pos))
end))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Kind_lam (_)) | (Microsoft_FStar_Absyn_Syntax.Kind_delayed (_)) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(let _52_8751 = (let _52_8750 = (let _52_8748 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.Prims.pipe_right _52_8748 Support.Microsoft.FStar.Range.string_of_range))
in (let _52_8749 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "%s: Impossible: Kind_unknown: %s" _52_8750 _52_8749)))
in (failwith (_52_8751)))
end))
in (aux t k))))

let is_var = (fun ( t ) -> (match ((Microsoft_FStar_Absyn_Util.compress_typ t)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
true
end
| _ -> begin
false
end))

let rec eta_expand_exp = (fun ( tcenv ) ( e ) -> (let t = (let _52_8758 = (Microsoft_FStar_Tc_Recheck.recompute_typ e)
in (Support.Prims.pipe_right _52_8758 Microsoft_FStar_Absyn_Util.compress_typ))
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(match ((let _52_8759 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _52_8759.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs', body)) -> begin
(match (((Support.List.length bs) = (Support.List.length bs'))) with
| true -> begin
e
end
| false -> begin
(failwith ("NYI"))
end)
end
| _ -> begin
(let _30_180 = (Microsoft_FStar_Absyn_Util.args_of_binders bs)
in (match (_30_180) with
| (bs, args) -> begin
(let _52_8761 = (let _52_8760 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e, args) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (bs, _52_8760))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _52_8761 (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos))
end))
end)
end
| _ -> begin
e
end)))

let no_eta = (Support.List.filter (fun ( _30_2 ) -> (match (_30_2) with
| Eta -> begin
false
end
| _ -> begin
true
end)))

let no_eta_cfg = (fun ( c ) -> (let _30_188 = c
in (let _52_8765 = (no_eta c.steps)
in {code = _30_188.code; environment = _30_188.environment; stack = _30_188.stack; close = _30_188.close; steps = _52_8765})))

let whnf_only = (fun ( config ) -> (Support.Prims.pipe_right config.steps (Support.List.contains WHNF)))

let unmeta = (fun ( config ) -> (Support.Prims.pipe_right config.steps (Support.List.contains Unmeta)))

let unlabel = (fun ( config ) -> (let _52_8770 = (unmeta config)
in (let _52_8769 = (Support.Prims.pipe_right config.steps (Support.List.contains Unlabel))
in (_52_8770 || _52_8769))))

let is_stack_empty = (fun ( config ) -> (match (config.stack.args) with
| [] -> begin
true
end
| _ -> begin
false
end))

let has_eta = (fun ( cfg ) -> (Support.Prims.pipe_right cfg.steps (Support.List.contains Eta)))

let rec weak_norm_comp = (fun ( env ) ( comp ) -> (let c = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ comp)
in (match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev env c.Microsoft_FStar_Absyn_Syntax.effect_name)) with
| None -> begin
c
end
| Some ((binders, cdef)) -> begin
(let binders' = (Support.List.map (fun ( _30_3 ) -> (match (_30_3) with
| (Support.Microsoft.FStar.Util.Inl (b), imp) -> begin
(let _52_8779 = (let _52_8778 = (Microsoft_FStar_Absyn_Util.freshen_bvar b)
in Support.Microsoft.FStar.Util.Inl (_52_8778))
in (_52_8779, imp))
end
| (Support.Microsoft.FStar.Util.Inr (b), imp) -> begin
(let _52_8781 = (let _52_8780 = (Microsoft_FStar_Absyn_Util.freshen_bvar b)
in Support.Microsoft.FStar.Util.Inr (_52_8780))
in (_52_8781, imp))
end)) binders)
in (let subst = (let _52_8783 = (let _52_8782 = (Microsoft_FStar_Absyn_Util.args_of_binders binders')
in (Support.Prims.pipe_right _52_8782 Support.Prims.snd))
in (Microsoft_FStar_Absyn_Util.subst_of_list binders _52_8783))
in (let cdef = (Microsoft_FStar_Absyn_Util.subst_comp subst cdef)
in (let subst = (let _52_8785 = (let _52_8784 = (Microsoft_FStar_Absyn_Syntax.targ c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (_52_8784)::c.Microsoft_FStar_Absyn_Syntax.effect_args)
in (Microsoft_FStar_Absyn_Util.subst_of_list binders' _52_8785))
in (let c1 = (Microsoft_FStar_Absyn_Util.subst_comp subst cdef)
in (let c = (Support.Prims.pipe_right (let _30_220 = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c1)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _30_220.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _30_220.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _30_220.Microsoft_FStar_Absyn_Syntax.effect_args; Microsoft_FStar_Absyn_Syntax.flags = c.Microsoft_FStar_Absyn_Syntax.flags}) Microsoft_FStar_Absyn_Syntax.mk_Comp)
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

let rec is_head_symbol = (fun ( t ) -> (match ((let _52_8816 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _52_8816.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _, _))) -> begin
(is_head_symbol t)
end
| _ -> begin
false
end))

let simplify_then_apply = (fun ( steps ) ( head ) ( args ) ( pos ) -> (let fallback = (fun ( _30_264 ) -> (match (()) with
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
| _ -> begin
None
end))
in (let simplify = (fun ( arg ) -> (match ((Support.Prims.fst arg)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
((simp_t t), arg)
end
| _ -> begin
(None, arg)
end))
in (match ((Support.Prims.pipe_left Support.Prims.op_Negation (Support.List.contains Simplify steps))) with
| true -> begin
(fallback ())
end
| false -> begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.and_lid)) with
| true -> begin
(match ((Support.Prims.pipe_right args (Support.List.map simplify))) with
| ((Some (true), _)::(_, (Support.Microsoft.FStar.Util.Inl (arg), _))::[]) | ((_, (Support.Microsoft.FStar.Util.Inl (arg), _))::(Some (true), _)::[]) -> begin
arg
end
| ((Some (false), _)::_::[]) | (_::(Some (false), _)::[]) -> begin
Microsoft_FStar_Absyn_Util.t_false
end
| _ -> begin
(fallback ())
end)
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.or_lid)) with
| true -> begin
(match ((Support.Prims.pipe_right args (Support.List.map simplify))) with
| ((Some (true), _)::_::[]) | (_::(Some (true), _)::[]) -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| ((Some (false), _)::(_, (Support.Microsoft.FStar.Util.Inl (arg), _))::[]) | ((_, (Support.Microsoft.FStar.Util.Inl (arg), _))::(Some (false), _)::[]) -> begin
arg
end
| _ -> begin
(fallback ())
end)
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.imp_lid)) with
| true -> begin
(match ((Support.Prims.pipe_right args (Support.List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| (Some (true), _)::(_, (Support.Microsoft.FStar.Util.Inl (arg), _))::[] -> begin
arg
end
| _ -> begin
(fallback ())
end)
end
| false -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.not_lid)) with
| true -> begin
(match ((Support.Prims.pipe_right args (Support.List.map simplify))) with
| (Some (true), _)::[] -> begin
Microsoft_FStar_Absyn_Util.t_false
end
| (Some (false), _)::[] -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| _ -> begin
(fallback ())
end)
end
| false -> begin
(match (((((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.forall_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.allTyp_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exists_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exTyp_lid))) with
| true -> begin
(match (args) with
| ((Support.Microsoft.FStar.Util.Inl (t), _)::[]) | (_::(Support.Microsoft.FStar.Util.Inl (t), _)::[]) -> begin
(match ((let _52_8831 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _52_8831.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((_::[], body)) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| Some (false) -> begin
Microsoft_FStar_Absyn_Util.t_false
end
| _ -> begin
(fallback ())
end)
end
| _ -> begin
(fallback ())
end)
end
| _ -> begin
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
| _ -> begin
(fallback ())
end)
end)))))

let rec sn_delay = (fun ( tcenv ) ( cfg ) -> (let aux = (fun ( _30_451 ) -> (match (()) with
| () -> begin
(let _52_8857 = (sn tcenv cfg)
in _52_8857.code)
end))
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_delayed' (Support.Microsoft.FStar.Util.Inr (aux)) None cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
in (let _30_453 = cfg
in {code = t; environment = _30_453.environment; stack = empty_stack; close = _30_453.close; steps = _30_453.steps}))))
and sn = (fun ( tcenv ) ( cfg ) -> (let rebuild = (fun ( config ) -> (let rebuild_stack = (fun ( config ) -> (match ((is_stack_empty config)) with
| true -> begin
config
end
| false -> begin
(let s' = (no_eta config.steps)
in (let args = (Support.Prims.pipe_right config.stack.args (Support.List.map (fun ( _30_4 ) -> (match (_30_4) with
| ((Support.Microsoft.FStar.Util.Inl (t), imp), env) -> begin
(let _52_8869 = (let _52_8868 = (let _52_8867 = (sn tcenv (t_config t env s'))
in _52_8867.code)
in (Support.Prims.pipe_left (fun ( _52_8866 ) -> Support.Microsoft.FStar.Util.Inl (_52_8866)) _52_8868))
in (_52_8869, imp))
end
| ((Support.Microsoft.FStar.Util.Inr (v), imp), env) -> begin
(let _52_8873 = (let _52_8872 = (let _52_8871 = (wne tcenv (e_config v env s'))
in _52_8871.code)
in (Support.Prims.pipe_left (fun ( _52_8870 ) -> Support.Microsoft.FStar.Util.Inr (_52_8870)) _52_8872))
in (_52_8873, imp))
end))))
in (let t = (simplify_then_apply config.steps config.code args config.code.Microsoft_FStar_Absyn_Syntax.pos)
in (let _30_477 = config
in {code = t; environment = _30_477.environment; stack = empty_stack; close = _30_477.close; steps = _30_477.steps}))))
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
(let _30_484 = config
in (let _52_8875 = (eta_expand tcenv t)
in {code = _52_8875; environment = _30_484.environment; stack = _30_484.stack; close = _30_484.close; steps = _30_484.steps}))
end
| false -> begin
(let _30_486 = config
in {code = t; environment = _30_486.environment; stack = _30_486.stack; close = _30_486.close; steps = _30_486.steps})
end)))))
in (let wk = (fun ( f ) -> (match ((Support.ST.read cfg.code.Microsoft_FStar_Absyn_Syntax.tk)) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) -> begin
(f (Some (Microsoft_FStar_Absyn_Syntax.ktype)) cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
end
| _ -> begin
(f None cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (let config = (let _30_503 = cfg
in (let _52_8888 = (Microsoft_FStar_Absyn_Util.compress_typ cfg.code)
in {code = _52_8888; environment = _30_503.environment; stack = _30_503.stack; close = _30_503.close; steps = _30_503.steps}))
in (let is_flex = (fun ( u ) -> (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (_) -> begin
false
end
| _ -> begin
true
end))
in (match (config.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (_) -> begin
(rebuild config)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(match ((let _52_8894 = (Support.Prims.pipe_right config.steps (Support.List.contains DeltaHard))
in (let _52_8893 = (let _52_8892 = (Support.Prims.pipe_right config.steps (Support.List.contains Delta))
in (let _52_8891 = (Support.Prims.pipe_left Support.Prims.op_Negation (is_stack_empty config))
in (_52_8892 && _52_8891)))
in (_52_8894 || _52_8893)))) with
| true -> begin
(match ((Microsoft_FStar_Tc_Env.lookup_typ_abbrev tcenv fv.Microsoft_FStar_Absyn_Syntax.v)) with
| None -> begin
(rebuild config)
end
| Some (t) -> begin
(sn tcenv (let _30_524 = config
in {code = t; environment = _30_524.environment; stack = _30_524.stack; close = _30_524.close; steps = _30_524.steps}))
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
| Some (T ((_, (t, e)))) -> begin
(sn tcenv (let _30_537 = config
in {code = t; environment = e; stack = _30_537.stack; close = _30_537.close; steps = _30_537.steps}))
end
| _ -> begin
(failwith ("Impossible: expected a type"))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let args = (Support.List.fold_right (fun ( a ) ( out ) -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _30_548 = config.stack
in {args = args})
in (sn tcenv (let _30_551 = config
in {code = head; environment = _30_551.environment; stack = stack; close = _30_551.close; steps = _30_551.steps}))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, t2)) -> begin
(match (config.stack.args) with
| [] -> begin
(let _30_560 = (sn_binders tcenv binders config.environment config.steps)
in (match (_30_560) with
| (binders, environment) -> begin
(let mk_lam = (fun ( t ) -> (let lam = (Support.Prims.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, t)))
in (match (cfg.close) with
| None -> begin
lam
end
| Some (f) -> begin
(f lam)
end)))
in (let t2_cfg = (let _52_8904 = (let _52_8903 = (no_eta config.steps)
in {code = t2; environment = environment; stack = empty_stack; close = None; steps = _52_8903})
in (sn_delay tcenv _52_8904))
in (let _30_568 = t2_cfg
in (let _52_8905 = (mk_lam t2_cfg.code)
in {code = _52_8905; environment = _30_568.environment; stack = _30_568.stack; close = _30_568.close; steps = _30_568.steps}))))
end))
end
| args -> begin
(let rec beta = (fun ( env_entries ) ( binders ) ( args ) -> (match ((binders, args)) with
| ([], _) -> begin
(let env = (extend_env config.environment env_entries)
in (sn tcenv (let _30_580 = config
in {code = t2; environment = env; stack = (let _30_582 = config.stack
in {args = args}); close = _30_580.close; steps = _30_580.steps})))
end
| (_, []) -> begin
(let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, t2) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let env = (extend_env config.environment env_entries)
in (sn tcenv (let _30_590 = config
in {code = t; environment = env; stack = empty_stack; close = _30_590.close; steps = _30_590.steps}))))
end
| (formal::rest, actual::rest') -> begin
(let m = (match ((formal, actual)) with
| ((Support.Microsoft.FStar.Util.Inl (a), _), ((Support.Microsoft.FStar.Util.Inl (t), _), env)) -> begin
T ((a.Microsoft_FStar_Absyn_Syntax.v, (t, env)))
end
| ((Support.Microsoft.FStar.Util.Inr (x), _), ((Support.Microsoft.FStar.Util.Inr (v), _), env)) -> begin
V ((x.Microsoft_FStar_Absyn_Syntax.v, (v, env)))
end
| _ -> begin
(let _52_8916 = (let _52_8915 = (let _52_8912 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.argpos (Support.Prims.fst actual))
in (Support.Microsoft.FStar.Range.string_of_range _52_8912))
in (let _52_8914 = (Microsoft_FStar_Absyn_Print.binder_to_string formal)
in (let _52_8913 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Print.arg_to_string (Support.Prims.fst actual))
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _52_8915 _52_8914 _52_8913))))
in (failwith (_52_8916)))
end)
in (beta ((m)::env_entries) rest rest'))
end))
in (beta [] binders args))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _)) -> begin
(sn tcenv (let _30_633 = config
in {code = t; environment = _30_633.environment; stack = _30_633.stack; close = _30_633.close; steps = _30_633.steps}))
end
| _ -> begin
(match (config.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, comp)) -> begin
(let _30_643 = (sn_binders tcenv bs config.environment config.steps)
in (match (_30_643) with
| (binders, environment) -> begin
(let c2 = (sncomp tcenv (c_config comp environment config.steps))
in (let _30_645 = config
in (let _52_8919 = (Support.Prims.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (binders, c2.code)))
in {code = _52_8919; environment = _30_645.environment; stack = _30_645.stack; close = _30_645.close; steps = _30_645.steps})))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, t)) -> begin
(match ((let _52_8921 = (let _52_8920 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_52_8920)::[])
in (sn_binders tcenv _52_8921 config.environment config.steps))) with
| ((Support.Microsoft.FStar.Util.Inr (x), _)::[], env) -> begin
(let refine = (fun ( t ) -> (Support.Prims.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, t))))
in (sn tcenv {code = t; environment = env; stack = empty_stack; close = (close_with_config config refine); steps = config.steps}))
end
| _ -> begin
(failwith ("Impossible"))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps))) -> begin
(match ((unmeta config)) with
| true -> begin
(sn tcenv (let _30_668 = config
in {code = t; environment = _30_668.environment; stack = _30_668.stack; close = _30_668.close; steps = _30_668.steps}))
end
| false -> begin
(let pat = (fun ( t ) -> (let ps = (sn_args true tcenv config.environment config.steps ps)
in (Support.Prims.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps)))))))
in (sn tcenv (let _30_673 = config
in {code = t; environment = _30_673.environment; stack = _30_673.stack; close = (close_with_config config pat); steps = _30_673.steps})))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b))) -> begin
(match ((unlabel config)) with
| true -> begin
(sn tcenv (let _30_682 = config
in {code = t; environment = _30_682.environment; stack = _30_682.stack; close = _30_682.close; steps = _30_682.steps}))
end
| false -> begin
(let lab = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (let _52_8932 = (Support.Prims.pipe_right config.steps (Support.List.contains Simplify))
in ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) && _52_8932)) -> begin
t
end
| _ -> begin
(match (config.environment.label_suffix) with
| (b', sfx)::_ -> begin
(match (((b' = None) || (Some (b) = b'))) with
| true -> begin
(let _30_696 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_8933 = (Support.Microsoft.FStar.Range.string_of_range sfx)
in (Support.Microsoft.FStar.Util.fprint2 "Stripping label %s because of enclosing refresh %s\n" l _52_8933))
end
| false -> begin
()
end)
in t)
end
| false -> begin
(let _30_698 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_8934 = (Support.Microsoft.FStar.Range.string_of_range sfx)
in (Support.Microsoft.FStar.Util.fprint1 "Normalizer refreshing label: %s\n" _52_8934))
end
| false -> begin
()
end)
in (Support.Prims.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, sfx, b))))))
end)
end
| _ -> begin
(Support.Prims.pipe_left wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b)))))
end)
end))
in (sn tcenv (let _30_702 = config
in {code = t; environment = _30_702.environment; stack = _30_702.stack; close = (close_with_config config lab); steps = _30_702.steps})))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))) -> begin
(match ((unmeta config)) with
| true -> begin
(sn tcenv (let _30_710 = config
in {code = t; environment = _30_710.environment; stack = _30_710.stack; close = _30_710.close; steps = _30_710.steps}))
end
| false -> begin
(let sfx = (match (b) with
| Some (false) -> begin
r
end
| _ -> begin
Microsoft_FStar_Absyn_Syntax.dummyRange
end)
in (let config = (let _30_717 = config
in {code = t; environment = (let _30_719 = config.environment
in {context = _30_719.context; label_suffix = ((b, sfx))::config.environment.label_suffix}); stack = _30_717.stack; close = _30_717.close; steps = _30_717.steps})
in (sn tcenv config)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, flag))) -> begin
(match ((Support.ST.read flag)) with
| true -> begin
(let _52_8940 = (let _30_728 = config
in (let _52_8939 = (Microsoft_FStar_Absyn_Util.mk_conj t1 t2)
in {code = _52_8939; environment = _30_728.environment; stack = _30_728.stack; close = _30_728.close; steps = _30_728.steps}))
in (sn tcenv _52_8940))
end
| false -> begin
(let c1 = (sn tcenv (t_config t1 config.environment config.steps))
in (let c2 = (sn tcenv (t_config t2 config.environment config.steps))
in (let _52_8942 = (let _30_732 = config
in (let _52_8941 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((c1.code, c2.code, flag))))
in {code = _52_8941; environment = _30_732.environment; stack = _30_732.stack; close = _30_732.close; steps = _30_732.steps}))
in (rebuild _52_8942))))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named (_))) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (_) -> begin
(let _52_8947 = (let _52_8946 = (let _52_8943 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.Prims.pipe_right _52_8943 Support.Microsoft.FStar.Range.string_of_range))
in (let _52_8945 = (Microsoft_FStar_Absyn_Print.tag_of_typ config.code)
in (let _52_8944 = (Microsoft_FStar_Absyn_Print.typ_to_string config.code)
in (Support.Microsoft.FStar.Util.format3 "(%s) Unexpected type (%s): %s" _52_8946 _52_8945 _52_8944))))
in (failwith (_52_8947)))
end)
end))))))
and sn_binders = (fun ( tcenv ) ( binders ) ( env ) ( steps ) -> (let rec aux = (fun ( out ) ( env ) ( _30_5 ) -> (match (_30_5) with
| (Support.Microsoft.FStar.Util.Inl (a), imp)::rest -> begin
(let c = (snk tcenv (k_config a.Microsoft_FStar_Absyn_Syntax.sort env steps))
in (let b = (let _52_8958 = (Microsoft_FStar_Absyn_Util.freshen_bvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _52_8958 c.code))
in (let btyp = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (let b_for_a = T ((a.Microsoft_FStar_Absyn_Syntax.v, (btyp, empty_env)))
in (aux (((Support.Microsoft.FStar.Util.Inl (b), imp))::out) (extend_env' env b_for_a) rest)))))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp)::rest -> begin
(let c = (sn_delay tcenv (t_config x.Microsoft_FStar_Absyn_Syntax.sort env steps))
in (let y = (let _52_8959 = (Microsoft_FStar_Absyn_Util.freshen_bvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _52_8959 c.code))
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
in (let _30_776 = cfg
in (let _52_8962 = (Microsoft_FStar_Absyn_Syntax.mk_Comp ctconf.code)
in {code = _52_8962; environment = _30_776.environment; stack = _30_776.stack; close = _30_776.close; steps = _30_776.steps})))
end
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(match ((Support.List.contains DeltaComp cfg.steps)) with
| true -> begin
(let _52_8966 = (let _52_8965 = (let _52_8964 = (let _52_8963 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (Microsoft_FStar_Absyn_Util.comp_to_comp_typ _52_8963))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.mk_Comp _52_8964))
in (with_new_code cfg _52_8965))
in (Support.Prims.pipe_left (sncomp tcenv) _52_8966))
end
| false -> begin
(let t = (sn tcenv (with_new_code cfg t))
in (let _52_8967 = (Microsoft_FStar_Absyn_Syntax.mk_Total t.code)
in (with_new_code cfg _52_8967)))
end)
end)))
and sncomp_typ = (fun ( tcenv ) ( cfg ) -> (let m = cfg.code
in (let norm = (fun ( _30_785 ) -> (match (()) with
| () -> begin
(let remake = (fun ( l ) ( r ) ( eargs ) ( flags ) -> (let c = {Microsoft_FStar_Absyn_Syntax.effect_name = l; Microsoft_FStar_Absyn_Syntax.result_typ = r; Microsoft_FStar_Absyn_Syntax.effect_args = eargs; Microsoft_FStar_Absyn_Syntax.flags = flags}
in (let _30_792 = cfg
in {code = c; environment = _30_792.environment; stack = _30_792.stack; close = _30_792.close; steps = _30_792.steps})))
in (let res = (let _52_8980 = (sn tcenv (with_new_code cfg m.Microsoft_FStar_Absyn_Syntax.result_typ))
in _52_8980.code)
in (let sn_flags = (fun ( flags ) -> (Support.Prims.pipe_right flags (Support.List.map (fun ( _30_6 ) -> (match (_30_6) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let e = (let _52_8984 = (wne tcenv (e_config e cfg.environment cfg.steps))
in _52_8984.code)
in Microsoft_FStar_Absyn_Syntax.DECREASES (e))
end
| f -> begin
f
end)))))
in (let _30_804 = (let _52_8986 = (sn_flags m.Microsoft_FStar_Absyn_Syntax.flags)
in (let _52_8985 = (sn_args true tcenv cfg.environment cfg.steps m.Microsoft_FStar_Absyn_Syntax.effect_args)
in (_52_8986, _52_8985)))
in (match (_30_804) with
| (flags, args) -> begin
(remake m.Microsoft_FStar_Absyn_Syntax.effect_name res args flags)
end)))))
end))
in (match ((Support.List.contains DeltaComp cfg.steps)) with
| true -> begin
(match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev tcenv m.Microsoft_FStar_Absyn_Syntax.effect_name)) with
| Some (_) -> begin
(let c = (let _52_8987 = (Microsoft_FStar_Absyn_Syntax.mk_Comp m)
in (weak_norm_comp tcenv _52_8987))
in (sncomp_typ tcenv (let _30_809 = cfg
in {code = c; environment = _30_809.environment; stack = _30_809.stack; close = _30_809.close; steps = _30_809.steps})))
end
| _ -> begin
(norm ())
end)
end
| false -> begin
(norm ())
end))))
and sn_args = (fun ( delay ) ( tcenv ) ( env ) ( steps ) ( args ) -> (Support.Prims.pipe_right args (Support.List.map (fun ( _30_7 ) -> (match (_30_7) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) when delay -> begin
(let _52_8997 = (let _52_8996 = (let _52_8995 = (sn_delay tcenv (t_config t env steps))
in _52_8995.code)
in (Support.Prims.pipe_left (fun ( _52_8994 ) -> Support.Microsoft.FStar.Util.Inl (_52_8994)) _52_8996))
in (_52_8997, imp))
end
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _52_9001 = (let _52_9000 = (let _52_8999 = (sn tcenv (t_config t env steps))
in _52_8999.code)
in (Support.Prims.pipe_left (fun ( _52_8998 ) -> Support.Microsoft.FStar.Util.Inl (_52_8998)) _52_9000))
in (_52_9001, imp))
end
| (Support.Microsoft.FStar.Util.Inr (e), imp) -> begin
(let _52_9005 = (let _52_9004 = (let _52_9003 = (wne tcenv (e_config e env steps))
in _52_9003.code)
in (Support.Prims.pipe_left (fun ( _52_9002 ) -> Support.Microsoft.FStar.Util.Inr (_52_9002)) _52_9004))
in (_52_9005, imp))
end)))))
and snk = (fun ( tcenv ) ( cfg ) -> (let w = (fun ( f ) -> (f cfg.code.Microsoft_FStar_Absyn_Syntax.pos))
in (match ((let _52_9015 = (Microsoft_FStar_Absyn_Util.compress_kind cfg.code)
in _52_9015.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Kind_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Kind_lam (_)) -> begin
(failwith ("Impossible"))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) -> begin
cfg
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, args)) -> begin
(let args = (let _52_9016 = (no_eta cfg.steps)
in (sn_args false tcenv cfg.environment _52_9016 args))
in (let _30_848 = cfg
in (let _52_9018 = (Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (uv, args)))
in {code = _52_9018; environment = _30_848.environment; stack = _30_848.stack; close = _30_848.close; steps = _30_848.steps})))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev (((l, args), {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_unknown; Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(let _30_869 = (Microsoft_FStar_Tc_Env.lookup_kind_abbrev tcenv l)
in (match (_30_869) with
| (_, binders, body) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.subst_of_list binders args)
in (let _52_9020 = (let _30_871 = cfg
in (let _52_9019 = (Microsoft_FStar_Absyn_Util.subst_kind subst body)
in {code = _52_9019; environment = _30_871.environment; stack = _30_871.stack; close = _30_871.close; steps = _30_871.steps}))
in (snk tcenv _52_9020)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(snk tcenv (let _30_878 = cfg
in {code = k; environment = _30_878.environment; stack = _30_878.stack; close = _30_878.close; steps = _30_878.steps}))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _30_886 = (sn_binders tcenv bs cfg.environment cfg.steps)
in (match (_30_886) with
| (bs, env) -> begin
(let c2 = (snk tcenv (k_config k env cfg.steps))
in (let _30_896 = (match (c2.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs', k)) -> begin
((Support.List.append bs bs'), k)
end
| _ -> begin
(bs, c2.code)
end)
in (match (_30_896) with
| (bs, rhs) -> begin
(let _30_897 = cfg
in (let _52_9022 = (Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, rhs)))
in {code = _52_9022; environment = _30_897.environment; stack = _30_897.stack; close = _30_897.close; steps = _30_897.steps}))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(failwith ("Impossible"))
end)))
and wne = (fun ( tcenv ) ( cfg ) -> (let e = (Microsoft_FStar_Absyn_Util.compress_exp cfg.code)
in (let config = (let _30_903 = cfg
in {code = e; environment = _30_903.environment; stack = _30_903.stack; close = _30_903.close; steps = _30_903.steps})
in (let rebuild = (fun ( config ) -> (match ((is_stack_empty config)) with
| true -> begin
config
end
| false -> begin
(let s' = (no_eta config.steps)
in (let args = (Support.Prims.pipe_right config.stack.args (Support.List.map (fun ( _30_8 ) -> (match (_30_8) with
| ((Support.Microsoft.FStar.Util.Inl (t), imp), env) -> begin
(let _52_9031 = (let _52_9030 = (let _52_9029 = (sn tcenv (t_config t env s'))
in _52_9029.code)
in (Support.Prims.pipe_left (fun ( _52_9028 ) -> Support.Microsoft.FStar.Util.Inl (_52_9028)) _52_9030))
in (_52_9031, imp))
end
| ((Support.Microsoft.FStar.Util.Inr (v), imp), env) -> begin
(let _52_9035 = (let _52_9034 = (let _52_9033 = (wne tcenv (e_config v env s'))
in _52_9033.code)
in (Support.Prims.pipe_left (fun ( _52_9032 ) -> Support.Microsoft.FStar.Util.Inr (_52_9032)) _52_9034))
in (_52_9035, imp))
end))))
in (let _30_923 = config
in (let _52_9036 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (config.code, args) None config.code.Microsoft_FStar_Absyn_Syntax.pos)
in {code = _52_9036; environment = _30_923.environment; stack = empty_stack; close = _30_923.close; steps = _30_923.steps}))))
end))
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_) -> begin
(failwith ("Impossible"))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
(Support.Prims.pipe_right config rebuild)
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(match ((lookup_env config.environment x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText)) with
| None -> begin
(Support.Prims.pipe_right config rebuild)
end
| Some (V ((_, (vc, env)))) -> begin
(wne tcenv (let _30_948 = config
in {code = vc; environment = env; stack = _30_948.stack; close = _30_948.close; steps = _30_948.steps}))
end
| _ -> begin
(failwith ("Impossible: ill-typed term"))
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(let args = (Support.List.fold_right (fun ( a ) ( out ) -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _30_959 = config.stack
in {args = args})
in (wne tcenv (let _30_962 = config
in {code = head; environment = _30_962.environment; stack = stack; close = _30_962.close; steps = _30_962.steps}))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((binders, body)) -> begin
(let rec beta = (fun ( entries ) ( binders ) ( args ) -> (match ((binders, args)) with
| ([], _) -> begin
(let env = (extend_env config.environment entries)
in (wne tcenv (let _30_977 = config
in {code = body; environment = env; stack = (let _30_979 = config.stack
in {args = args}); close = _30_977.close; steps = _30_977.steps})))
end
| (_, []) -> begin
(let env = (extend_env config.environment entries)
in (let _30_988 = (sn_binders tcenv binders env config.steps)
in (match (_30_988) with
| (binders, env) -> begin
(let mk_abs = (fun ( t ) -> (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (binders, t) None body.Microsoft_FStar_Absyn_Syntax.pos))
in (let c = (let _52_9048 = (let _30_991 = config
in (let _52_9047 = (no_eta config.steps)
in {code = body; environment = env; stack = (let _30_993 = config.stack
in {args = []}); close = _30_991.close; steps = _52_9047}))
in (wne tcenv _52_9048))
in (let _30_996 = c
in (let _52_9049 = (mk_abs c.code)
in {code = _52_9049; environment = _30_996.environment; stack = _30_996.stack; close = _30_996.close; steps = _30_996.steps}))))
end)))
end
| (formal::rest, actual::rest') -> begin
(let m = (match ((formal, actual)) with
| ((Support.Microsoft.FStar.Util.Inl (a), _), ((Support.Microsoft.FStar.Util.Inl (t), _), env)) -> begin
T ((a.Microsoft_FStar_Absyn_Syntax.v, (t, env)))
end
| ((Support.Microsoft.FStar.Util.Inr (x), _), ((Support.Microsoft.FStar.Util.Inr (v), _), env)) -> begin
V ((x.Microsoft_FStar_Absyn_Syntax.v, (v, env)))
end
| _ -> begin
(let _52_9054 = (let _52_9053 = (let _52_9050 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.argpos (Support.Prims.fst actual))
in (Support.Microsoft.FStar.Range.string_of_range _52_9050))
in (let _52_9052 = (Microsoft_FStar_Absyn_Print.binder_to_string formal)
in (let _52_9051 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Print.arg_to_string (Support.Prims.fst actual))
in (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _52_9053 _52_9052 _52_9051))))
in (failwith (_52_9054)))
end)
in (beta ((m)::entries) rest rest'))
end))
in (beta [] binders config.stack.args))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e1, eqns)) -> begin
(let c_e1 = (wne tcenv (let _30_1038 = config
in {code = e1; environment = _30_1038.environment; stack = empty_stack; close = _30_1038.close; steps = _30_1038.steps}))
in (let wn_eqn = (fun ( _30_1045 ) -> (match (_30_1045) with
| (pat, w, body) -> begin
(let rec pat_vars = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (p::_) -> begin
(pat_vars p)
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((_, _, pats)) -> begin
(Support.List.collect pat_vars pats)
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _)) -> begin
(let _52_9059 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_52_9059)::[])
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _52_9060 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (_52_9060)::[])
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
[]
end))
in (let vars = (pat_vars pat)
in (let norm_bvvar = (fun ( x ) -> (let t = (sn tcenv (t_config x.Microsoft_FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _30_1088 = x
in {Microsoft_FStar_Absyn_Syntax.v = _30_1088.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t.code; Microsoft_FStar_Absyn_Syntax.p = _30_1088.Microsoft_FStar_Absyn_Syntax.p})))
in (let norm_btvar = (fun ( a ) -> (let k = (snk tcenv (k_config a.Microsoft_FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _30_1093 = a
in {Microsoft_FStar_Absyn_Syntax.v = _30_1093.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k.code; Microsoft_FStar_Absyn_Syntax.p = _30_1093.Microsoft_FStar_Absyn_Syntax.p})))
in (let rec norm_pat = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (pats) -> begin
(let _52_9068 = (let _52_9067 = (Support.List.map norm_pat pats)
in Microsoft_FStar_Absyn_Syntax.Pat_disj (_52_9067))
in (Microsoft_FStar_Absyn_Util.withinfo _52_9068 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, q, pats)) -> begin
(let _52_9071 = (let _52_9070 = (let _52_9069 = (Support.List.map norm_pat pats)
in (fv, q, _52_9069))
in Microsoft_FStar_Absyn_Syntax.Pat_cons (_52_9070))
in (Microsoft_FStar_Absyn_Util.withinfo _52_9071 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, b)) -> begin
(let _52_9074 = (let _52_9073 = (let _52_9072 = (norm_bvvar x)
in (_52_9072, b))
in Microsoft_FStar_Absyn_Syntax.Pat_var (_52_9073))
in (Microsoft_FStar_Absyn_Util.withinfo _52_9074 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _52_9076 = (let _52_9075 = (norm_btvar a)
in Microsoft_FStar_Absyn_Syntax.Pat_tvar (_52_9075))
in (Microsoft_FStar_Absyn_Util.withinfo _52_9076 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let _52_9078 = (let _52_9077 = (norm_bvvar x)
in Microsoft_FStar_Absyn_Syntax.Pat_wild (_52_9077))
in (Microsoft_FStar_Absyn_Util.withinfo _52_9078 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let _52_9080 = (let _52_9079 = (norm_btvar a)
in Microsoft_FStar_Absyn_Syntax.Pat_twild (_52_9079))
in (Microsoft_FStar_Absyn_Util.withinfo _52_9080 None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (_) -> begin
p
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e)) -> begin
(let e = (wne tcenv (e_config e config.environment config.steps))
in (let _52_9083 = (let _52_9082 = (let _52_9081 = (norm_bvvar x)
in (_52_9081, e.code))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_52_9082))
in (Microsoft_FStar_Absyn_Util.withinfo _52_9083 None p.Microsoft_FStar_Absyn_Syntax.p)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)) -> begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (let _52_9086 = (let _52_9085 = (let _52_9084 = (norm_btvar a)
in (_52_9084, t.code))
in Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_52_9085))
in (Microsoft_FStar_Absyn_Util.withinfo _52_9086 None p.Microsoft_FStar_Absyn_Syntax.p)))
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
(let c_w = (wne tcenv (let _30_1140 = config
in {code = w; environment = env; stack = empty_stack; close = _30_1140.close; steps = _30_1140.steps}))
in Some (c_w.code))
end)
in (let c_body = (wne tcenv (let _30_1144 = config
in {code = body; environment = env; stack = empty_stack; close = _30_1144.close; steps = _30_1144.steps}))
in (let _52_9089 = (norm_pat pat)
in (_52_9089, w, c_body.code)))))))))))
end))
in (let eqns = (Support.List.map wn_eqn eqns)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_match (c_e1.code, eqns) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Prims.pipe_right (let _30_1149 = config
in {code = e; environment = _30_1149.environment; stack = _30_1149.stack; close = _30_1149.close; steps = _30_1149.steps}) rebuild)))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((is_rec, lbs), body)) -> begin
(let _30_1181 = (Support.Prims.pipe_right lbs (Support.List.fold_left (fun ( _30_1159 ) ( _30_1164 ) -> (match ((_30_1159, _30_1164)) with
| ((env, lbs), {Microsoft_FStar_Absyn_Syntax.lbname = x; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = eff; Microsoft_FStar_Absyn_Syntax.lbdef = e}) -> begin
(let c = (wne tcenv (let _30_1165 = config
in {code = e; environment = _30_1165.environment; stack = empty_stack; close = _30_1165.close; steps = _30_1165.steps}))
in (let t = (sn tcenv (t_config t config.environment config.steps))
in (let _30_1178 = (match (x) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(let y = (let _52_9092 = (match (is_rec) with
| true -> begin
x
end
| false -> begin
(Microsoft_FStar_Absyn_Util.freshen_bvd x)
end)
in (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s _52_9092 t.code))
in (let yexp = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (let y_for_x = V ((x, (yexp, empty_env)))
in (Support.Microsoft.FStar.Util.Inl (y.Microsoft_FStar_Absyn_Syntax.v), (extend_env' env y_for_x)))))
end
| _ -> begin
(x, env)
end)
in (match (_30_1178) with
| (y, env) -> begin
(let _52_9094 = (let _52_9093 = (Microsoft_FStar_Absyn_Syntax.mk_lb (y, eff, t.code, c.code))
in (_52_9093)::lbs)
in (env, _52_9094))
end))))
end)) (config.environment, [])))
in (match (_30_1181) with
| (env, lbs) -> begin
(let lbs = (Support.List.rev lbs)
in (let c_body = (wne tcenv (let _30_1183 = config
in {code = body; environment = env; stack = empty_stack; close = _30_1183.close; steps = _30_1183.steps}))
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), c_body.code) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Prims.pipe_right (let _30_1187 = config
in {code = e; environment = _30_1187.environment; stack = _30_1187.stack; close = _30_1187.close; steps = _30_1187.steps}) rebuild))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, l)) -> begin
(let c = (wne tcenv (let _30_1194 = config
in {code = e; environment = _30_1194.environment; stack = _30_1194.stack; close = _30_1194.close; steps = _30_1194.steps}))
in (match ((is_stack_empty config)) with
| true -> begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (let _52_9096 = (let _30_1198 = config
in (let _52_9095 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (c.code, t.code, l) None e.Microsoft_FStar_Absyn_Syntax.pos)
in {code = _52_9095; environment = _30_1198.environment; stack = _30_1198.stack; close = _30_1198.close; steps = _30_1198.steps}))
in (rebuild _52_9096)))
end
| false -> begin
c
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, info))) -> begin
(let c = (wne tcenv (let _30_1205 = config
in {code = e; environment = _30_1205.environment; stack = _30_1205.stack; close = _30_1205.close; steps = _30_1205.steps}))
in (match ((is_stack_empty config)) with
| true -> begin
(let _52_9098 = (let _30_1208 = config
in (let _52_9097 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((c.code, info))))
in {code = _52_9097; environment = _30_1208.environment; stack = _30_1208.stack; close = _30_1208.close; steps = _30_1208.steps}))
in (rebuild _52_9098))
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

let norm_sigelt = (fun ( tcenv ) ( _30_9 ) -> (match (_30_9) with
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, l, b)) -> begin
(let e = (let _52_9122 = (let _52_9121 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant Microsoft_FStar_Absyn_Syntax.Const_unit None r)
in (lbs, _52_9121))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_let _52_9122 None r))
in (let e = (norm_exp ((Beta)::[]) tcenv e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, _)) -> begin
Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, l, b))
end
| _ -> begin
(failwith ("Impossible"))
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
(let _52_9127 = (eta_expand tcenv t)
in (Support.Prims.pipe_right _52_9127 Microsoft_FStar_Absyn_Util.compress_typ))
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

let exp_norm_to_string = (fun ( tcenv ) ( e ) -> (let _52_9150 = (norm_exp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv e)
in (Microsoft_FStar_Absyn_Print.exp_to_string _52_9150)))

let typ_norm_to_string = (fun ( tcenv ) ( t ) -> (let _52_9155 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv t)
in (Microsoft_FStar_Absyn_Print.typ_to_string _52_9155)))

let kind_norm_to_string = (fun ( tcenv ) ( k ) -> (let _52_9160 = (norm_kind ((Beta)::(SNComp)::(Unmeta)::[]) tcenv k)
in (Microsoft_FStar_Absyn_Print.kind_to_string _52_9160)))

let formula_norm_to_string = (fun ( tcenv ) ( f ) -> (let _52_9165 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv f)
in (Microsoft_FStar_Absyn_Print.formula_to_string _52_9165)))

let comp_typ_norm_to_string = (fun ( tcenv ) ( c ) -> (let _52_9170 = (norm_comp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv c)
in (Microsoft_FStar_Absyn_Print.comp_typ_to_string _52_9170)))

let normalize_refinement = (fun ( env ) ( t0 ) -> (let t = (norm_typ ((Beta)::(WHNF)::(DeltaHard)::[]) env t0)
in (let rec aux = (fun ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi)) -> begin
(let t0 = (aux x.Microsoft_FStar_Absyn_Syntax.sort)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((y, phi1)) -> begin
(let _52_9183 = (let _52_9182 = (let _52_9181 = (let _52_9180 = (let _52_9179 = (let _52_9178 = (let _52_9177 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _52_9177))
in Support.Microsoft.FStar.Util.Inr (_52_9178))
in (_52_9179)::[])
in (Microsoft_FStar_Absyn_Util.subst_typ _52_9180 phi))
in (Microsoft_FStar_Absyn_Util.mk_conj phi1 _52_9181))
in (y, _52_9182))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine _52_9183 (Some (Microsoft_FStar_Absyn_Syntax.ktype)) t0.Microsoft_FStar_Absyn_Syntax.pos))
end
| _ -> begin
t
end))
end
| _ -> begin
t
end)))
in (aux t))))




