
type step =
| WHNF
| Eta
| Delta
| DeltaHard
| Beta
| DeltaComp
| Simplify
| SNComp
| Unmeta and steps =
step list

type 'a config =
{code : 'a; environment : environment; stack : stack; close : ('a  ->  'a) option; steps : step list} and environment =
{context : env_entry list; label_suffix : (bool option * Support.Microsoft.FStar.Range.range) list} and stack =
{args : (Microsoft_FStar_Absyn_Syntax.arg * environment) list} and env_entry =
| T of (Microsoft_FStar_Absyn_Syntax.btvdef * tclos)
| V of (Microsoft_FStar_Absyn_Syntax.bvvdef * vclos) and tclos =
(Microsoft_FStar_Absyn_Syntax.typ * environment) and vclos =
(Microsoft_FStar_Absyn_Syntax.exp * environment) and 'a memo =
'a option ref

let empty_env = {context = []; label_suffix = []}

let extend_env' = (fun env b -> (let _126204 = env
in {context = (b)::env.context; label_suffix = _126204.label_suffix}))

let extend_env = (fun env bindings -> (let _126208 = env
in {context = (Support.List.append bindings env.context); label_suffix = _126208.label_suffix}))

let lookup_env = (fun env key -> ((Support.Microsoft.FStar.Util.find_opt (fun _126176 -> (match (_126176) with
| T ((a, _)) -> begin
(a.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText = key)
end
| V ((x, _)) -> begin
(x.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText = key)
end))) env.context))

let fold_env = (fun env f acc -> (Support.List.fold_left (fun acc v -> (match (v) with
| T ((a, _)) -> begin
(f a.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText v acc)
end
| V ((x, _)) -> begin
(f x.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText v acc)
end)) acc env.context))

let empty_stack = {args = []}

let rec subst_of_env' = (fun env -> (fold_env env (fun _126239 v acc -> (match (v) with
| T ((a, (t, env'))) -> begin
(Support.Microsoft.FStar.Util.Inl ((a, (Microsoft_FStar_Absyn_Util.subst_typ (subst_of_env' env') t))))::acc
end
| V ((x, (v, env'))) -> begin
(Support.Microsoft.FStar.Util.Inr ((x, (Microsoft_FStar_Absyn_Util.subst_exp (subst_of_env' env') v))))::acc
end)) []))

let subst_of_env = (fun tcenv env -> (subst_of_env' env))

let with_new_code = (fun c e -> {code = e; environment = c.environment; stack = empty_stack; close = None; steps = c.steps})

let rec eta_expand = (fun tcenv t -> (let k = (Microsoft_FStar_Absyn_Util.compress_kind (Microsoft_FStar_Tc_Recheck.recompute_kind t))
in (let rec aux = (fun t k -> (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) | (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(aux t k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((binders, k')) -> begin
(match ((Microsoft_FStar_Absyn_Util.unascribe_typ t).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((real, body)) -> begin
(let rec aux = (fun real expected -> (match ((real, expected)) with
| (_::real, _::expected) -> begin
(aux real expected)
end
| ([], []) -> begin
t
end
| (_::_, []) -> begin
(failwith "Ill-kinded type")
end
| ([], more) -> begin
(let _126310 = (Microsoft_FStar_Absyn_Util.args_of_binders more)
in (match (_126310) with
| (more, args) -> begin
(let body = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (body, args) None body.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam ((Support.List.append binders more), body) None body.Microsoft_FStar_Absyn_Syntax.pos))
end))
end))
in (aux real binders))
end
| _ -> begin
(let _126316 = (Microsoft_FStar_Absyn_Util.args_of_binders binders)
in (match (_126316) with
| (binders, args) -> begin
(let body = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t, args) None t.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, body) None t.Microsoft_FStar_Absyn_Syntax.pos))
end))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Kind_lam (_)) | (Microsoft_FStar_Absyn_Syntax.Kind_delayed (_)) -> begin
(failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(failwith (Support.Microsoft.FStar.Util.format2 "%s: Impossible: Kind_unknown: %s" (Support.Microsoft.FStar.Range.string_of_range (Microsoft_FStar_Tc_Env.get_range tcenv)) (Microsoft_FStar_Absyn_Print.typ_to_string t)))
end))
in (aux t k))))

let is_var = (fun t -> (match ((Microsoft_FStar_Absyn_Util.compress_typ t)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
true
end
| _ -> begin
false
end))

let rec eta_expand_exp = (fun tcenv e -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ (Microsoft_FStar_Tc_Recheck.recompute_typ e))
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(match ((Microsoft_FStar_Absyn_Util.compress_exp e).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs', body)) -> begin
if ((Support.List.length bs) = (Support.List.length bs')) then begin
e
end else begin
(failwith "NYI")
end
end
| _ -> begin
(let _126355 = (Microsoft_FStar_Absyn_Util.args_of_binders bs)
in (match (_126355) with
| (bs, args) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e, args) None e.Microsoft_FStar_Absyn_Syntax.pos)) (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
end))
end)
end
| _ -> begin
e
end)))

let no_eta = (Support.List.filter (fun _126177 -> (match (_126177) with
| Eta -> begin
false
end
| _ -> begin
true
end)))

let no_eta_cfg = (fun c -> (let _126363 = c
in {code = _126363.code; environment = _126363.environment; stack = _126363.stack; close = _126363.close; steps = (no_eta c.steps)}))

let whnf_only = (fun config -> ((Support.List.contains WHNF) config.steps))

let unmeta = (fun config -> ((Support.List.contains Unmeta) config.steps))

let is_stack_empty = (fun config -> (match (config.stack.args) with
| [] -> begin
true
end
| _ -> begin
false
end))

let has_eta = (fun cfg -> ((Support.List.contains Eta) cfg.steps))

let rec weak_norm_comp = (fun env comp -> (let c = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ comp)
in (match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev env c.Microsoft_FStar_Absyn_Syntax.effect_name)) with
| None -> begin
c
end
| Some ((binders, cdef)) -> begin
(let binders' = (Support.List.map (fun _126178 -> (match (_126178) with
| (Support.Microsoft.FStar.Util.Inl (b), imp) -> begin
(Support.Microsoft.FStar.Util.Inl ((Microsoft_FStar_Absyn_Util.freshen_bvar b)), imp)
end
| (Support.Microsoft.FStar.Util.Inr (b), imp) -> begin
(Support.Microsoft.FStar.Util.Inr ((Microsoft_FStar_Absyn_Util.freshen_bvar b)), imp)
end)) binders)
in (let subst = (Microsoft_FStar_Absyn_Util.subst_of_list binders ((Support.Prims.snd) (Microsoft_FStar_Absyn_Util.args_of_binders binders')))
in (let cdef = (Microsoft_FStar_Absyn_Util.subst_comp subst cdef)
in (let subst = (Microsoft_FStar_Absyn_Util.subst_of_list binders' (((Microsoft_FStar_Absyn_Syntax.targ c.Microsoft_FStar_Absyn_Syntax.result_typ))::c.Microsoft_FStar_Absyn_Syntax.effect_args))
in (let c1 = (Microsoft_FStar_Absyn_Util.subst_comp subst cdef)
in (let c = (Microsoft_FStar_Absyn_Syntax.mk_Comp (let _126394 = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c1)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _126394.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _126394.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _126394.Microsoft_FStar_Absyn_Syntax.effect_args; Microsoft_FStar_Absyn_Syntax.flags = c.Microsoft_FStar_Absyn_Syntax.flags}))
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

let rec is_head_symbol = (fun t -> (match ((Microsoft_FStar_Absyn_Util.compress_typ t).Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _, _))) -> begin
(is_head_symbol t)
end
| _ -> begin
false
end))

let simplify_then_apply = (fun steps head args pos -> (let fallback = (fun _126438 -> (match (_126438) with
| () -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (head, args) None pos)
end))
in (let simp_t = (fun t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
Some (true)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.false_lid) -> begin
Some (false)
end
| _ -> begin
None
end))
in (let simplify = (fun arg -> (match ((Support.Prims.fst arg)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
((simp_t t), arg)
end
| _ -> begin
(None, arg)
end))
in if (not ((Support.List.contains Simplify steps))) then begin
(fallback ())
end else begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.and_lid) then begin
(match (((Support.List.map simplify) args)) with
| ((Some (true), _)::(_, (Support.Microsoft.FStar.Util.Inl (arg), _))::[]) | ((_, (Support.Microsoft.FStar.Util.Inl (arg), _))::(Some (true), _)::[]) -> begin
arg
end
| ((Some (false), _)::_::[]) | (_::(Some (false), _)::[]) -> begin
Microsoft_FStar_Absyn_Util.t_false
end
| _ -> begin
(fallback ())
end)
end else begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.or_lid) then begin
(match (((Support.List.map simplify) args)) with
| ((Some (true), _)::_::[]) | (_::(Some (true), _)::[]) -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| ((Some (false), _)::(_, (Support.Microsoft.FStar.Util.Inl (arg), _))::[]) | ((_, (Support.Microsoft.FStar.Util.Inl (arg), _))::(Some (false), _)::[]) -> begin
arg
end
| _ -> begin
(fallback ())
end)
end else begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.imp_lid) then begin
(match (((Support.List.map simplify) args)) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| (Some (true), _)::(_, (Support.Microsoft.FStar.Util.Inl (arg), _))::[] -> begin
arg
end
| _ -> begin
(fallback ())
end)
end else begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.not_lid) then begin
(match (((Support.List.map simplify) args)) with
| (Some (true), _)::[] -> begin
Microsoft_FStar_Absyn_Util.t_false
end
| (Some (false), _)::[] -> begin
Microsoft_FStar_Absyn_Util.t_true
end
| _ -> begin
(fallback ())
end)
end else begin
if ((((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.forall_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.allTyp_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exists_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exTyp_lid)) then begin
(match (args) with
| ((Support.Microsoft.FStar.Util.Inl (t), _)::[]) | (_::(Support.Microsoft.FStar.Util.Inl (t), _)::[]) -> begin
(match ((Microsoft_FStar_Absyn_Util.compress_typ t).Microsoft_FStar_Absyn_Syntax.n) with
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
end else begin
(fallback ())
end
end
end
end
end
end
| _ -> begin
(fallback ())
end)
end))))

let rec sn_delay = (fun tcenv cfg -> (let aux = (fun _126625 -> (match (_126625) with
| () -> begin
(sn tcenv cfg).code
end))
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_delayed' (Support.Microsoft.FStar.Util.Inr (aux)) None cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
in (let _126627 = cfg
in {code = t; environment = _126627.environment; stack = empty_stack; close = _126627.close; steps = _126627.steps}))))
and sn = (fun tcenv cfg -> (let rebuild = (fun config -> (let rebuild_stack = (fun config -> if (is_stack_empty config) then begin
config
end else begin
(let s' = (no_eta config.steps)
in (let args = ((Support.List.map (fun _126179 -> (match (_126179) with
| ((Support.Microsoft.FStar.Util.Inl (t), imp), env) -> begin
((Support.Microsoft.FStar.Util.Inl (sn tcenv (t_config t env s')).code), imp)
end
| ((Support.Microsoft.FStar.Util.Inr (v), imp), env) -> begin
((Support.Microsoft.FStar.Util.Inr (wne tcenv (e_config v env s')).code), imp)
end))) config.stack.args)
in (let t = (simplify_then_apply config.steps config.code args config.code.Microsoft_FStar_Absyn_Syntax.pos)
in (let _126651 = config
in {code = t; environment = _126651.environment; stack = empty_stack; close = _126651.close; steps = _126651.steps}))))
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
(let _126658 = config
in {code = (eta_expand tcenv t); environment = _126658.environment; stack = _126658.stack; close = _126658.close; steps = _126658.steps})
end else begin
(let _126660 = config
in {code = t; environment = _126660.environment; stack = _126660.stack; close = _126660.close; steps = _126660.steps})
end))))
in (let wk = (fun f -> (match ((! (cfg.code.Microsoft_FStar_Absyn_Syntax.tk))) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) -> begin
(f (Some (Microsoft_FStar_Absyn_Syntax.ktype)) cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
end
| _ -> begin
(f None cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (let config = (let _126677 = cfg
in {code = (Microsoft_FStar_Absyn_Util.compress_typ cfg.code); environment = _126677.environment; stack = _126677.stack; close = _126677.close; steps = _126677.steps})
in (let is_flex = (fun u -> (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (_) -> begin
false
end
| _ -> begin
true
end))
in (match (config.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_) -> begin
(failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (_) -> begin
(rebuild config)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
if (((Support.List.contains DeltaHard) config.steps) || (((Support.List.contains Delta) config.steps) && (not ((is_stack_empty config))))) then begin
(match ((Microsoft_FStar_Tc_Env.lookup_typ_abbrev tcenv fv.Microsoft_FStar_Absyn_Syntax.v)) with
| None -> begin
(rebuild config)
end
| Some (t) -> begin
(sn tcenv (let _126698 = config
in {code = t; environment = _126698.environment; stack = _126698.stack; close = _126698.close; steps = _126698.steps}))
end)
end else begin
(rebuild config)
end
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(match ((lookup_env config.environment a.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText)) with
| None -> begin
(rebuild config)
end
| Some (T ((_, (t, e)))) -> begin
(sn tcenv (let _126711 = config
in {code = t; environment = e; stack = _126711.stack; close = _126711.close; steps = _126711.steps}))
end
| _ -> begin
(failwith "Impossible: expected a type")
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let args = (Support.List.fold_right (fun a out -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _126722 = config.stack
in {args = args})
in (sn tcenv (let _126725 = config
in {code = head; environment = _126725.environment; stack = stack; close = _126725.close; steps = _126725.steps}))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, t2)) -> begin
(match (config.stack.args) with
| [] -> begin
(let _126734 = (sn_binders tcenv binders config.environment config.steps)
in (match (_126734) with
| (binders, environment) -> begin
(let mk_lam = (fun t -> (let lam = (wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, t)))
in (match (cfg.close) with
| None -> begin
lam
end
| Some (f) -> begin
(f lam)
end)))
in (let t2_cfg = (sn_delay tcenv {code = t2; environment = environment; stack = empty_stack; close = None; steps = (no_eta config.steps)})
in (let _126742 = t2_cfg
in {code = (mk_lam t2_cfg.code); environment = _126742.environment; stack = _126742.stack; close = _126742.close; steps = _126742.steps})))
end))
end
| args -> begin
(let rec beta = (fun env_entries binders args -> (match ((binders, args)) with
| ([], _) -> begin
(let env = (extend_env config.environment env_entries)
in (sn tcenv (let _126754 = config
in {code = t2; environment = env; stack = (let _126756 = config.stack
in {args = args}); close = _126754.close; steps = _126754.steps})))
end
| (_, []) -> begin
(let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, t2) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let env = (extend_env config.environment env_entries)
in (sn tcenv (let _126764 = config
in {code = t; environment = env; stack = empty_stack; close = _126764.close; steps = _126764.steps}))))
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
(failwith (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" (Support.Microsoft.FStar.Range.string_of_range (Microsoft_FStar_Absyn_Syntax.argpos (Support.Prims.fst actual))) (Microsoft_FStar_Absyn_Print.binder_to_string formal) (Microsoft_FStar_Absyn_Print.arg_to_string (Support.Prims.fst actual))))
end)
in (beta ((m)::env_entries) rest rest'))
end))
in (beta [] binders args))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _)) -> begin
(sn tcenv (let _126807 = config
in {code = t; environment = _126807.environment; stack = _126807.stack; close = _126807.close; steps = _126807.steps}))
end
| _ -> begin
(match (config.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, comp)) -> begin
(let _126817 = (sn_binders tcenv bs config.environment config.steps)
in (match (_126817) with
| (binders, environment) -> begin
(let c2 = (sncomp tcenv (c_config comp environment config.steps))
in (let _126819 = config
in {code = (wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (binders, c2.code))); environment = _126819.environment; stack = _126819.stack; close = _126819.close; steps = _126819.steps}))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, t)) -> begin
(match ((sn_binders tcenv (((Microsoft_FStar_Absyn_Syntax.v_binder x))::[]) config.environment config.steps)) with
| ((Support.Microsoft.FStar.Util.Inr (x), _)::[], env) -> begin
(let refine = (fun t -> (wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, t))))
in (sn tcenv {code = t; environment = env; stack = empty_stack; close = (close_with_config config refine); steps = config.steps}))
end
| _ -> begin
(failwith "Impossible")
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps))) -> begin
if (unmeta config) then begin
(sn tcenv (let _126842 = config
in {code = t; environment = _126842.environment; stack = _126842.stack; close = _126842.close; steps = _126842.steps}))
end else begin
(let pat = (fun t -> (let ps = (sn_args true tcenv config.environment config.steps ps)
in (wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps)))))))
in (sn tcenv (let _126847 = config
in {code = t; environment = _126847.environment; stack = _126847.stack; close = (close_with_config config pat); steps = _126847.steps})))
end
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b))) -> begin
if (unmeta config) then begin
(sn tcenv (let _126856 = config
in {code = t; environment = _126856.environment; stack = _126856.stack; close = _126856.close; steps = _126856.steps}))
end else begin
(let lab = (fun t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) && ((Support.List.contains Simplify) config.steps)) -> begin
t
end
| _ -> begin
(match (config.environment.label_suffix) with
| (b', sfx)::_ -> begin
if ((b' = None) || (Some (b) = b')) then begin
(let _126870 = if (Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint2 "Stripping label %s because of enclosing refresh %s\n" l (Support.Microsoft.FStar.Range.string_of_range sfx))
end
in t)
end else begin
(let _126872 = if (Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint1 "Normalizer refreshing label: %s\n" (Support.Microsoft.FStar.Range.string_of_range sfx))
end
in (wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, sfx, b))))))
end
end
| _ -> begin
(wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b)))))
end)
end))
in (sn tcenv (let _126876 = config
in {code = t; environment = _126876.environment; stack = _126876.stack; close = (close_with_config config lab); steps = _126876.steps})))
end
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))) -> begin
if (unmeta config) then begin
(sn tcenv (let _126884 = config
in {code = t; environment = _126884.environment; stack = _126884.stack; close = _126884.close; steps = _126884.steps}))
end else begin
(let sfx = (match (b) with
| Some (false) -> begin
r
end
| _ -> begin
Microsoft_FStar_Absyn_Syntax.dummyRange
end)
in (let config = (let _126891 = config
in {code = t; environment = (let _126893 = config.environment
in {context = _126893.context; label_suffix = ((b, sfx))::config.environment.label_suffix}); stack = _126891.stack; close = _126891.close; steps = _126891.steps})
in (sn tcenv config)))
end
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, flag))) -> begin
if (! (flag)) then begin
(sn tcenv (let _126902 = config
in {code = (Microsoft_FStar_Absyn_Util.mk_conj t1 t2); environment = _126902.environment; stack = _126902.stack; close = _126902.close; steps = _126902.steps}))
end else begin
(let c1 = (sn tcenv (t_config t1 config.environment config.steps))
in (let c2 = (sn tcenv (t_config t2 config.environment config.steps))
in (rebuild (let _126906 = config
in {code = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((c1.code, c2.code, flag)))); environment = _126906.environment; stack = _126906.stack; close = _126906.close; steps = _126906.steps}))))
end
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named (_))) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (_) -> begin
(failwith (Support.Microsoft.FStar.Util.format3 "(%s) Unexpected type (%s): %s" (Support.Microsoft.FStar.Range.string_of_range (Microsoft_FStar_Tc_Env.get_range tcenv)) (Microsoft_FStar_Absyn_Print.tag_of_typ config.code) (Microsoft_FStar_Absyn_Print.typ_to_string config.code)))
end)
end))))))
and sn_binders = (fun tcenv binders env steps -> (let rec aux = (fun out env _126180 -> (match (_126180) with
| (Support.Microsoft.FStar.Util.Inl (a), imp)::rest -> begin
(let c = (snk tcenv (k_config a.Microsoft_FStar_Absyn_Syntax.sort env steps))
in (let b = (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s (Microsoft_FStar_Absyn_Util.freshen_bvd a.Microsoft_FStar_Absyn_Syntax.v) c.code)
in (let btyp = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (let b_for_a = T ((a.Microsoft_FStar_Absyn_Syntax.v, (btyp, empty_env)))
in (aux (((Support.Microsoft.FStar.Util.Inl (b), imp))::out) (extend_env' env b_for_a) rest)))))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp)::rest -> begin
(let c = (sn_delay tcenv (t_config x.Microsoft_FStar_Absyn_Syntax.sort env steps))
in (let y = (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s (Microsoft_FStar_Absyn_Util.freshen_bvd x.Microsoft_FStar_Absyn_Syntax.v) c.code)
in (let yexp = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (let y_for_x = V ((x.Microsoft_FStar_Absyn_Syntax.v, (yexp, empty_env)))
in (aux (((Support.Microsoft.FStar.Util.Inr (y), imp))::out) (extend_env' env y_for_x) rest)))))
end
| [] -> begin
((Support.List.rev out), env)
end))
in (aux [] env binders)))
and sncomp = (fun tcenv cfg -> (let m = cfg.code
in (match (m.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let ctconf = (sncomp_typ tcenv (with_new_code cfg ct))
in (let _126950 = cfg
in {code = (Microsoft_FStar_Absyn_Syntax.mk_Comp ctconf.code); environment = _126950.environment; stack = _126950.stack; close = _126950.close; steps = _126950.steps}))
end
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
if (Support.List.contains DeltaComp cfg.steps) then begin
((sncomp tcenv) (with_new_code cfg (Microsoft_FStar_Absyn_Syntax.mk_Comp (Microsoft_FStar_Absyn_Util.comp_to_comp_typ (Microsoft_FStar_Absyn_Syntax.mk_Total t)))))
end else begin
(let t = (sn tcenv (with_new_code cfg t))
in (with_new_code cfg (Microsoft_FStar_Absyn_Syntax.mk_Total t.code)))
end
end)))
and sncomp_typ = (fun tcenv cfg -> (let m = cfg.code
in (let norm = (fun _126959 -> (match (_126959) with
| () -> begin
(let remake = (fun l r eargs flags -> (let c = {Microsoft_FStar_Absyn_Syntax.effect_name = l; Microsoft_FStar_Absyn_Syntax.result_typ = r; Microsoft_FStar_Absyn_Syntax.effect_args = eargs; Microsoft_FStar_Absyn_Syntax.flags = flags}
in (let _126966 = cfg
in {code = c; environment = _126966.environment; stack = _126966.stack; close = _126966.close; steps = _126966.steps})))
in (let res = (sn tcenv (with_new_code cfg m.Microsoft_FStar_Absyn_Syntax.result_typ)).code
in (let sn_flags = (fun flags -> ((Support.List.map (fun _126181 -> (match (_126181) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let e = (wne tcenv (e_config e cfg.environment cfg.steps)).code
in Microsoft_FStar_Absyn_Syntax.DECREASES (e))
end
| f -> begin
f
end))) flags))
in (let _126978 = ((sn_flags m.Microsoft_FStar_Absyn_Syntax.flags), (sn_args true tcenv cfg.environment cfg.steps m.Microsoft_FStar_Absyn_Syntax.effect_args))
in (match (_126978) with
| (flags, args) -> begin
(remake m.Microsoft_FStar_Absyn_Syntax.effect_name res args flags)
end)))))
end))
in if (Support.List.contains DeltaComp cfg.steps) then begin
(match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev tcenv m.Microsoft_FStar_Absyn_Syntax.effect_name)) with
| Some (_) -> begin
(let c = (weak_norm_comp tcenv (Microsoft_FStar_Absyn_Syntax.mk_Comp m))
in (sncomp_typ tcenv (let _126983 = cfg
in {code = c; environment = _126983.environment; stack = _126983.stack; close = _126983.close; steps = _126983.steps})))
end
| _ -> begin
(norm ())
end)
end else begin
(norm ())
end)))
and sn_args = (fun delay tcenv env steps args -> ((Support.List.map (fun _126182 -> (match (_126182) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) when delay -> begin
((Support.Microsoft.FStar.Util.Inl (sn_delay tcenv (t_config t env steps)).code), imp)
end
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
((Support.Microsoft.FStar.Util.Inl (sn tcenv (t_config t env steps)).code), imp)
end
| (Support.Microsoft.FStar.Util.Inr (e), imp) -> begin
((Support.Microsoft.FStar.Util.Inr (wne tcenv (e_config e env steps)).code), imp)
end))) args))
and snk = (fun tcenv cfg -> (let w = (fun f -> (f cfg.code.Microsoft_FStar_Absyn_Syntax.pos))
in (match ((Microsoft_FStar_Absyn_Util.compress_kind cfg.code).Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Kind_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Kind_lam (_)) -> begin
(failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) -> begin
cfg
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, args)) -> begin
(let args = (sn_args false tcenv cfg.environment (no_eta cfg.steps) args)
in (let _127022 = cfg
in {code = (w (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (uv, args))); environment = _127022.environment; stack = _127022.stack; close = _127022.close; steps = _127022.steps}))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev (((l, args), {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_unknown; Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(let _127043 = (Microsoft_FStar_Tc_Env.lookup_kind_abbrev tcenv l)
in (match (_127043) with
| (_, binders, body) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.subst_of_list binders args)
in (snk tcenv (let _127045 = cfg
in {code = (Microsoft_FStar_Absyn_Util.subst_kind subst body); environment = _127045.environment; stack = _127045.stack; close = _127045.close; steps = _127045.steps})))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(snk tcenv (let _127052 = cfg
in {code = k; environment = _127052.environment; stack = _127052.stack; close = _127052.close; steps = _127052.steps}))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _127060 = (sn_binders tcenv bs cfg.environment cfg.steps)
in (match (_127060) with
| (bs, env) -> begin
(let c2 = (snk tcenv (k_config k env cfg.steps))
in (let _127070 = (match (c2.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs', k)) -> begin
((Support.List.append bs bs'), k)
end
| _ -> begin
(bs, c2.code)
end)
in (match (_127070) with
| (bs, rhs) -> begin
(let _127071 = cfg
in {code = (w (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, rhs))); environment = _127071.environment; stack = _127071.stack; close = _127071.close; steps = _127071.steps})
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(failwith "Impossible")
end)))
and wne = (fun tcenv cfg -> (let e = (Microsoft_FStar_Absyn_Util.compress_exp cfg.code)
in (let config = (let _127077 = cfg
in {code = e; environment = _127077.environment; stack = _127077.stack; close = _127077.close; steps = _127077.steps})
in (let rebuild = (fun config -> if (is_stack_empty config) then begin
config
end else begin
(let s' = (no_eta config.steps)
in (let args = ((Support.List.map (fun _126183 -> (match (_126183) with
| ((Support.Microsoft.FStar.Util.Inl (t), imp), env) -> begin
((Support.Microsoft.FStar.Util.Inl (sn tcenv (t_config t env s')).code), imp)
end
| ((Support.Microsoft.FStar.Util.Inr (v), imp), env) -> begin
((Support.Microsoft.FStar.Util.Inr (wne tcenv (e_config v env s')).code), imp)
end))) config.stack.args)
in (let _127097 = config
in {code = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (config.code, args) None config.code.Microsoft_FStar_Absyn_Syntax.pos); environment = _127097.environment; stack = empty_stack; close = _127097.close; steps = _127097.steps})))
end)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_) -> begin
(failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
(rebuild config)
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(match ((lookup_env config.environment x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText)) with
| None -> begin
(rebuild config)
end
| Some (V ((_, (vc, env)))) -> begin
(wne tcenv (let _127122 = config
in {code = vc; environment = env; stack = _127122.stack; close = _127122.close; steps = _127122.steps}))
end
| _ -> begin
(failwith "Impossible: ill-typed term")
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(let args = (Support.List.fold_right (fun a out -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _127133 = config.stack
in {args = args})
in (wne tcenv (let _127136 = config
in {code = head; environment = _127136.environment; stack = stack; close = _127136.close; steps = _127136.steps}))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((binders, body)) -> begin
(let rec beta = (fun entries binders args -> (match ((binders, args)) with
| ([], _) -> begin
(let env = (extend_env config.environment entries)
in (wne tcenv (let _127151 = config
in {code = body; environment = env; stack = (let _127153 = config.stack
in {args = args}); close = _127151.close; steps = _127151.steps})))
end
| (_, []) -> begin
(let env = (extend_env config.environment entries)
in (let _127162 = (sn_binders tcenv binders env config.steps)
in (match (_127162) with
| (binders, env) -> begin
(let mk_abs = (fun t -> (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (binders, t) None body.Microsoft_FStar_Absyn_Syntax.pos))
in (let c = (wne tcenv (let _127165 = config
in {code = body; environment = env; stack = (let _127167 = config.stack
in {args = []}); close = _127165.close; steps = (no_eta config.steps)}))
in (let _127170 = c
in {code = (mk_abs c.code); environment = _127170.environment; stack = _127170.stack; close = _127170.close; steps = _127170.steps})))
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
(failwith (Support.Microsoft.FStar.Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" (Support.Microsoft.FStar.Range.string_of_range (Microsoft_FStar_Absyn_Syntax.argpos (Support.Prims.fst actual))) (Microsoft_FStar_Absyn_Print.binder_to_string formal) (Microsoft_FStar_Absyn_Print.arg_to_string (Support.Prims.fst actual))))
end)
in (beta ((m)::entries) rest rest'))
end))
in (beta [] binders config.stack.args))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e1, eqns)) -> begin
(let c_e1 = (wne tcenv (let _127212 = config
in {code = e1; environment = _127212.environment; stack = empty_stack; close = _127212.close; steps = _127212.steps}))
in (let wn_eqn = (fun _127219 -> (match (_127219) with
| (pat, w, body) -> begin
(let rec pat_vars = (fun p -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (p::_) -> begin
(pat_vars p)
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((_, pats)) -> begin
(Support.List.collect pat_vars pats)
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _)) -> begin
((Microsoft_FStar_Absyn_Syntax.v_binder x))::[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
((Microsoft_FStar_Absyn_Syntax.t_binder a))::[]
end
| (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_constant (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
[]
end))
in (let vars = (pat_vars pat)
in (let norm_bvvar = (fun x -> (let t = (sn tcenv (t_config x.Microsoft_FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _127260 = x
in {Microsoft_FStar_Absyn_Syntax.v = _127260.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t.code; Microsoft_FStar_Absyn_Syntax.p = _127260.Microsoft_FStar_Absyn_Syntax.p})))
in (let norm_btvar = (fun a -> (let k = (snk tcenv (k_config a.Microsoft_FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _127265 = a
in {Microsoft_FStar_Absyn_Syntax.v = _127265.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k.code; Microsoft_FStar_Absyn_Syntax.p = _127265.Microsoft_FStar_Absyn_Syntax.p})))
in (let rec norm_pat = (fun p -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (pats) -> begin
(Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_disj ((Support.List.map norm_pat pats))) None p.Microsoft_FStar_Absyn_Syntax.p)
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, pats)) -> begin
(Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_cons ((fv, (Support.List.map norm_pat pats)))) None p.Microsoft_FStar_Absyn_Syntax.p)
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, b)) -> begin
(Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_var (((norm_bvvar x), b))) None p.Microsoft_FStar_Absyn_Syntax.p)
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_tvar ((norm_btvar a))) None p.Microsoft_FStar_Absyn_Syntax.p)
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (x) -> begin
(Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_wild ((norm_bvvar x))) None p.Microsoft_FStar_Absyn_Syntax.p)
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (a) -> begin
(Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_twild ((norm_btvar a))) None p.Microsoft_FStar_Absyn_Syntax.p)
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (_) -> begin
p
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, e)) -> begin
(let e = (wne tcenv (e_config e config.environment config.steps))
in (Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (((norm_bvvar x), e.code))) None p.Microsoft_FStar_Absyn_Syntax.p))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, t)) -> begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (Microsoft_FStar_Absyn_Util.withinfo (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (((norm_btvar a), t.code))) None p.Microsoft_FStar_Absyn_Syntax.p))
end))
in (let env_entries = (Support.List.fold_left (fun entries b -> (match ((Support.Prims.fst b)) with
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
(let c_w = (wne tcenv (let _127311 = config
in {code = w; environment = env; stack = empty_stack; close = _127311.close; steps = _127311.steps}))
in Some (c_w.code))
end)
in (let c_body = (wne tcenv (let _127315 = config
in {code = body; environment = env; stack = empty_stack; close = _127315.close; steps = _127315.steps}))
in ((norm_pat pat), w, c_body.code))))))))))
end))
in (let eqns = (Support.List.map wn_eqn eqns)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_match (c_e1.code, eqns) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (rebuild (let _127320 = config
in {code = e; environment = _127320.environment; stack = _127320.stack; close = _127320.close; steps = _127320.steps}))))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((is_rec, lbs), body)) -> begin
(let _127351 = ((Support.List.fold_left (fun _127330 _127334 -> (match ((_127330, _127334)) with
| ((env, lbs), (x, t, e)) -> begin
(let c = (wne tcenv (let _127335 = config
in {code = e; environment = _127335.environment; stack = empty_stack; close = _127335.close; steps = _127335.steps}))
in (let t = (sn tcenv (t_config t config.environment config.steps))
in (let _127348 = (match (x) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(let y = (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s (if is_rec then begin
x
end else begin
(Microsoft_FStar_Absyn_Util.freshen_bvd x)
end) t.code)
in (let yexp = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (let y_for_x = V ((x, (yexp, empty_env)))
in (Support.Microsoft.FStar.Util.Inl (y.Microsoft_FStar_Absyn_Syntax.v), (extend_env' env y_for_x)))))
end
| _ -> begin
(x, env)
end)
in (match (_127348) with
| (y, env) -> begin
(env, ((y, t.code, c.code))::lbs)
end))))
end)) (config.environment, [])) lbs)
in (match (_127351) with
| (env, lbs) -> begin
(let lbs = (Support.List.rev lbs)
in (let c_body = (wne tcenv (let _127353 = config
in {code = body; environment = env; stack = empty_stack; close = _127353.close; steps = _127353.steps}))
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), c_body.code) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (rebuild (let _127357 = config
in {code = e; environment = _127357.environment; stack = _127357.stack; close = _127357.close; steps = _127357.steps})))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t)) -> begin
(let c = (wne tcenv (let _127363 = config
in {code = e; environment = _127363.environment; stack = _127363.stack; close = _127363.close; steps = _127363.steps}))
in if (is_stack_empty config) then begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (rebuild (let _127367 = config
in {code = (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (c.code, t.code) e.Microsoft_FStar_Absyn_Syntax.pos); environment = _127367.environment; stack = _127367.stack; close = _127367.close; steps = _127367.steps})))
end else begin
c
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, info))) -> begin
(let c = (wne tcenv (let _127374 = config
in {code = e; environment = _127374.environment; stack = _127374.stack; close = _127374.close; steps = _127374.steps}))
in if (is_stack_empty config) then begin
(rebuild (let _127377 = config
in {code = (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((c.code, info)))); environment = _127377.environment; stack = _127377.stack; close = _127377.close; steps = _127377.steps}))
end else begin
c
end)
end)))))

let norm_kind = (fun steps tcenv k -> (let c = (snk tcenv (k_config k empty_env steps))
in (Microsoft_FStar_Absyn_Util.compress_kind c.code)))

let norm_typ = (fun steps tcenv t -> (let c = (sn tcenv (t_config t empty_env steps))
in c.code))

let norm_exp = (fun steps tcenv e -> (let c = (wne tcenv (e_config e empty_env steps))
in c.code))

let norm_sigelt = (fun tcenv _126184 -> (match (_126184) with
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, l, b)) -> begin
(let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_let (lbs, (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant Microsoft_FStar_Absyn_Syntax.Const_unit None r)) None r)
in (let e = (norm_exp ((Beta)::[]) tcenv e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, _)) -> begin
Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, r, l, b))
end
| _ -> begin
(failwith "Impossible")
end)))
end
| s -> begin
s
end))

let whnf = (fun tcenv t -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_refine (_)) -> begin
t
end
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_btvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(Microsoft_FStar_Absyn_Util.compress_typ (eta_expand tcenv t))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) | (_) -> begin
(norm_typ ((WHNF)::(Beta)::(Eta)::[]) tcenv t)
end)))

let norm_comp = (fun steps tcenv c -> (let c = (sncomp tcenv (c_config c empty_env steps))
in c.code))

let normalize_kind = (fun tcenv k -> (let steps = (Eta)::(Delta)::(Beta)::[]
in (norm_kind steps tcenv k)))

let normalize_comp = (fun tcenv c -> (let steps = (Eta)::(Delta)::(Beta)::(SNComp)::(DeltaComp)::[]
in (norm_comp steps tcenv c)))

let normalize = (fun tcenv t -> (norm_typ ((DeltaHard)::(Beta)::(Eta)::[]) tcenv t))

let exp_norm_to_string = (fun tcenv e -> (Microsoft_FStar_Absyn_Print.exp_to_string (norm_exp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv e)))

let typ_norm_to_string = (fun tcenv t -> (Microsoft_FStar_Absyn_Print.typ_to_string (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv t)))

let kind_norm_to_string = (fun tcenv k -> (Microsoft_FStar_Absyn_Print.kind_to_string (norm_kind ((Beta)::(SNComp)::(Unmeta)::[]) tcenv k)))

let formula_norm_to_string = (fun tcenv f -> (Microsoft_FStar_Absyn_Print.formula_to_string (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv f)))

let comp_typ_norm_to_string = (fun tcenv c -> (Microsoft_FStar_Absyn_Print.comp_typ_to_string (norm_comp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv c)))

let normalize_refinement = (fun env t0 -> (let t = (norm_typ ((Beta)::(WHNF)::(DeltaHard)::[]) env t0)
in (let rec aux = (fun t -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, phi)) -> begin
(let t0 = (aux x.Microsoft_FStar_Absyn_Syntax.sort)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((y, phi1)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (y, (Microsoft_FStar_Absyn_Util.mk_conj phi1 (Microsoft_FStar_Absyn_Util.subst_typ ((Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, (Microsoft_FStar_Absyn_Util.bvar_to_exp y))))::[]) phi))) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) t0.Microsoft_FStar_Absyn_Syntax.pos)
end
| _ -> begin
t
end))
end
| _ -> begin
t
end)))
in (aux t))))




