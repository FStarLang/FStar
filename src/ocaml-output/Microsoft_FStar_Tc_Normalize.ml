
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

let extend_env' = (fun env b -> (let _125337 = env
in {context = (b)::env.context; label_suffix = _125337.label_suffix}))

let extend_env = (fun env bindings -> (let _125341 = env
in {context = (Support.List.append bindings env.context); label_suffix = _125341.label_suffix}))

let lookup_env = (fun env key -> ((Support.Microsoft.FStar.Util.find_opt (fun _125309 -> (match (_125309) with
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

let rec subst_of_env' = (fun env -> (fold_env env (fun _125372 v acc -> (match (v) with
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
(let _125443 = (Microsoft_FStar_Absyn_Util.args_of_binders more)
in (match (_125443) with
| (more, args) -> begin
(let body = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (body, args) None body.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam ((Support.List.append binders more), body) None body.Microsoft_FStar_Absyn_Syntax.pos))
end))
end))
in (aux real binders))
end
| _ -> begin
(let _125449 = (Microsoft_FStar_Absyn_Util.args_of_binders binders)
in (match (_125449) with
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
(let _125488 = (Microsoft_FStar_Absyn_Util.args_of_binders bs)
in (match (_125488) with
| (bs, args) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e, args) None e.Microsoft_FStar_Absyn_Syntax.pos)) (Some (t)) e.Microsoft_FStar_Absyn_Syntax.pos)
end))
end)
end
| _ -> begin
e
end)))

let no_eta = (Support.List.filter (fun _125310 -> (match (_125310) with
| Eta -> begin
false
end
| _ -> begin
true
end)))

let no_eta_cfg = (fun c -> (let _125496 = c
in {code = _125496.code; environment = _125496.environment; stack = _125496.stack; close = _125496.close; steps = (no_eta c.steps)}))

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
(let binders' = (Support.List.map (fun _125311 -> (match (_125311) with
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
in (let c = (Microsoft_FStar_Absyn_Syntax.mk_Comp (let _125527 = (Microsoft_FStar_Absyn_Util.comp_to_comp_typ c1)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _125527.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _125527.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _125527.Microsoft_FStar_Absyn_Syntax.effect_args; Microsoft_FStar_Absyn_Syntax.flags = c.Microsoft_FStar_Absyn_Syntax.flags}))
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

let simplify_then_apply = (fun steps head args pos -> (let fallback = (fun _125571 -> (match (_125571) with
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

let rec sn_delay = (fun tcenv cfg -> (let aux = (fun _125758 -> (match (_125758) with
| () -> begin
(sn tcenv cfg).code
end))
in (let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_delayed' (Support.Microsoft.FStar.Util.Inr (aux)) None cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
in (let _125760 = cfg
in {code = t; environment = _125760.environment; stack = empty_stack; close = _125760.close; steps = _125760.steps}))))
and sn = (fun tcenv cfg -> (let rebuild = (fun config -> (let rebuild_stack = (fun config -> if (is_stack_empty config) then begin
config
end else begin
(let s' = (no_eta config.steps)
in (let args = ((Support.List.map (fun _125312 -> (match (_125312) with
| ((Support.Microsoft.FStar.Util.Inl (t), imp), env) -> begin
((Support.Microsoft.FStar.Util.Inl (sn tcenv (t_config t env s')).code), imp)
end
| ((Support.Microsoft.FStar.Util.Inr (v), imp), env) -> begin
((Support.Microsoft.FStar.Util.Inr (wne tcenv (e_config v env s')).code), imp)
end))) config.stack.args)
in (let t = (simplify_then_apply config.steps config.code args config.code.Microsoft_FStar_Absyn_Syntax.pos)
in (let _125784 = config
in {code = t; environment = _125784.environment; stack = empty_stack; close = _125784.close; steps = _125784.steps}))))
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
(let _125791 = config
in {code = (eta_expand tcenv t); environment = _125791.environment; stack = _125791.stack; close = _125791.close; steps = _125791.steps})
end else begin
(let _125793 = config
in {code = t; environment = _125793.environment; stack = _125793.stack; close = _125793.close; steps = _125793.steps})
end))))
in (let wk = (fun f -> (match ((! (cfg.code.Microsoft_FStar_Absyn_Syntax.tk))) with
| Some ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_type; Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}) -> begin
(f (Some (Microsoft_FStar_Absyn_Syntax.ktype)) cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
end
| _ -> begin
(f None cfg.code.Microsoft_FStar_Absyn_Syntax.pos)
end))
in (let config = (let _125810 = cfg
in {code = (Microsoft_FStar_Absyn_Util.compress_typ cfg.code); environment = _125810.environment; stack = _125810.stack; close = _125810.close; steps = _125810.steps})
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
(sn tcenv (let _125831 = config
in {code = t; environment = _125831.environment; stack = _125831.stack; close = _125831.close; steps = _125831.steps}))
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
(sn tcenv (let _125844 = config
in {code = t; environment = e; stack = _125844.stack; close = _125844.close; steps = _125844.steps}))
end
| _ -> begin
(failwith "Impossible: expected a type")
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let args = (Support.List.fold_right (fun a out -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _125855 = config.stack
in {args = args})
in (sn tcenv (let _125858 = config
in {code = head; environment = _125858.environment; stack = stack; close = _125858.close; steps = _125858.steps}))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, t2)) -> begin
(match (config.stack.args) with
| [] -> begin
(let _125867 = (sn_binders tcenv binders config.environment config.steps)
in (match (_125867) with
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
in (let _125875 = t2_cfg
in {code = (mk_lam t2_cfg.code); environment = _125875.environment; stack = _125875.stack; close = _125875.close; steps = _125875.steps})))
end))
end
| args -> begin
(let rec beta = (fun env_entries binders args -> (match ((binders, args)) with
| ([], _) -> begin
(let env = (extend_env config.environment env_entries)
in (sn tcenv (let _125887 = config
in {code = t2; environment = env; stack = (let _125889 = config.stack
in {args = args}); close = _125887.close; steps = _125887.steps})))
end
| (_, []) -> begin
(let t = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (binders, t2) None t2.Microsoft_FStar_Absyn_Syntax.pos)
in (let env = (extend_env config.environment env_entries)
in (sn tcenv (let _125897 = config
in {code = t; environment = env; stack = empty_stack; close = _125897.close; steps = _125897.steps}))))
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
(sn tcenv (let _125940 = config
in {code = t; environment = _125940.environment; stack = _125940.stack; close = _125940.close; steps = _125940.steps}))
end
| _ -> begin
(match (config.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, comp)) -> begin
(let _125950 = (sn_binders tcenv bs config.environment config.steps)
in (match (_125950) with
| (binders, environment) -> begin
(let c2 = (sncomp tcenv (c_config comp environment config.steps))
in (let _125952 = config
in {code = (wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (binders, c2.code))); environment = _125952.environment; stack = _125952.stack; close = _125952.close; steps = _125952.steps}))
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
(sn tcenv (let _125975 = config
in {code = t; environment = _125975.environment; stack = _125975.stack; close = _125975.close; steps = _125975.steps}))
end else begin
(let pat = (fun t -> (let ps = (sn_args true tcenv config.environment config.steps ps)
in (wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps)))))))
in (sn tcenv (let _125980 = config
in {code = t; environment = _125980.environment; stack = _125980.stack; close = (close_with_config config pat); steps = _125980.steps})))
end
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b))) -> begin
if (unmeta config) then begin
(sn tcenv (let _125989 = config
in {code = t; environment = _125989.environment; stack = _125989.stack; close = _125989.close; steps = _125989.steps}))
end else begin
(let lab = (fun t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) when ((Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) && ((Support.List.contains Simplify) config.steps)) -> begin
t
end
| _ -> begin
(match (config.environment.label_suffix) with
| (b', sfx)::_ -> begin
if ((b' = None) || (Some (b) = b')) then begin
(let _126003 = if (Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint2 "Stripping label %s because of enclosing refresh %s\n" l (Support.Microsoft.FStar.Range.string_of_range sfx))
end
in t)
end else begin
(let _126005 = if (Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint1 "Normalizer refreshing label: %s\n" (Support.Microsoft.FStar.Range.string_of_range sfx))
end
in (wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, sfx, b))))))
end
end
| _ -> begin
(wk (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b)))))
end)
end))
in (sn tcenv (let _126009 = config
in {code = t; environment = _126009.environment; stack = _126009.stack; close = (close_with_config config lab); steps = _126009.steps})))
end
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))) -> begin
if (unmeta config) then begin
(sn tcenv (let _126017 = config
in {code = t; environment = _126017.environment; stack = _126017.stack; close = _126017.close; steps = _126017.steps}))
end else begin
(let sfx = (match (b) with
| Some (false) -> begin
r
end
| _ -> begin
Microsoft_FStar_Absyn_Syntax.dummyRange
end)
in (let config = (let _126024 = config
in {code = t; environment = (let _126026 = config.environment
in {context = _126026.context; label_suffix = ((b, sfx))::config.environment.label_suffix}); stack = _126024.stack; close = _126024.close; steps = _126024.steps})
in (sn tcenv config)))
end
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, flag))) -> begin
if (! (flag)) then begin
(sn tcenv (let _126035 = config
in {code = (Microsoft_FStar_Absyn_Util.mk_conj t1 t2); environment = _126035.environment; stack = _126035.stack; close = _126035.close; steps = _126035.steps}))
end else begin
(let c1 = (sn tcenv (t_config t1 config.environment config.steps))
in (let c2 = (sn tcenv (t_config t2 config.environment config.steps))
in (rebuild (let _126039 = config
in {code = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((c1.code, c2.code, flag)))); environment = _126039.environment; stack = _126039.stack; close = _126039.close; steps = _126039.steps}))))
end
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named (_))) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (_) -> begin
(failwith (Support.Microsoft.FStar.Util.format3 "(%s) Unexpected type (%s): %s" (Support.Microsoft.FStar.Range.string_of_range (Microsoft_FStar_Tc_Env.get_range tcenv)) (Microsoft_FStar_Absyn_Print.tag_of_typ config.code) (Microsoft_FStar_Absyn_Print.typ_to_string config.code)))
end)
end))))))
and sn_binders = (fun tcenv binders env steps -> (let rec aux = (fun out env _125313 -> (match (_125313) with
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
in (let _126083 = cfg
in {code = (Microsoft_FStar_Absyn_Syntax.mk_Comp ctconf.code); environment = _126083.environment; stack = _126083.stack; close = _126083.close; steps = _126083.steps}))
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
in (let norm = (fun _126092 -> (match (_126092) with
| () -> begin
(let remake = (fun l r eargs flags -> (let c = {Microsoft_FStar_Absyn_Syntax.effect_name = l; Microsoft_FStar_Absyn_Syntax.result_typ = r; Microsoft_FStar_Absyn_Syntax.effect_args = eargs; Microsoft_FStar_Absyn_Syntax.flags = flags}
in (let _126099 = cfg
in {code = c; environment = _126099.environment; stack = _126099.stack; close = _126099.close; steps = _126099.steps})))
in (let res = (sn tcenv (with_new_code cfg m.Microsoft_FStar_Absyn_Syntax.result_typ)).code
in (let sn_flags = (fun flags -> ((Support.List.map (fun _125314 -> (match (_125314) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let e = (wne tcenv (e_config e cfg.environment cfg.steps)).code
in Microsoft_FStar_Absyn_Syntax.DECREASES (e))
end
| f -> begin
f
end))) flags))
in (let _126111 = ((sn_flags m.Microsoft_FStar_Absyn_Syntax.flags), (sn_args true tcenv cfg.environment cfg.steps m.Microsoft_FStar_Absyn_Syntax.effect_args))
in (match (_126111) with
| (flags, args) -> begin
(remake m.Microsoft_FStar_Absyn_Syntax.effect_name res args flags)
end)))))
end))
in if (Support.List.contains DeltaComp cfg.steps) then begin
(match ((Microsoft_FStar_Tc_Env.lookup_effect_abbrev tcenv m.Microsoft_FStar_Absyn_Syntax.effect_name)) with
| Some (_) -> begin
(let c = (weak_norm_comp tcenv (Microsoft_FStar_Absyn_Syntax.mk_Comp m))
in (sncomp_typ tcenv (let _126116 = cfg
in {code = c; environment = _126116.environment; stack = _126116.stack; close = _126116.close; steps = _126116.steps})))
end
| _ -> begin
(norm ())
end)
end else begin
(norm ())
end)))
and sn_args = (fun delay tcenv env steps args -> ((Support.List.map (fun _125315 -> (match (_125315) with
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
in (let _126155 = cfg
in {code = (w (Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (uv, args))); environment = _126155.environment; stack = _126155.stack; close = _126155.close; steps = _126155.steps}))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev (((l, args), {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_unknown; Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(let _126176 = (Microsoft_FStar_Tc_Env.lookup_kind_abbrev tcenv l)
in (match (_126176) with
| (_, binders, body) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.subst_of_list binders args)
in (snk tcenv (let _126178 = cfg
in {code = (Microsoft_FStar_Absyn_Util.subst_kind subst body); environment = _126178.environment; stack = _126178.stack; close = _126178.close; steps = _126178.steps})))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(snk tcenv (let _126185 = cfg
in {code = k; environment = _126185.environment; stack = _126185.stack; close = _126185.close; steps = _126185.steps}))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _126193 = (sn_binders tcenv bs cfg.environment cfg.steps)
in (match (_126193) with
| (bs, env) -> begin
(let c2 = (snk tcenv (k_config k env cfg.steps))
in (let _126203 = (match (c2.code.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs', k)) -> begin
((Support.List.append bs bs'), k)
end
| _ -> begin
(bs, c2.code)
end)
in (match (_126203) with
| (bs, rhs) -> begin
(let _126204 = cfg
in {code = (w (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, rhs))); environment = _126204.environment; stack = _126204.stack; close = _126204.close; steps = _126204.steps})
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
(failwith "Impossible")
end)))
and wne = (fun tcenv cfg -> (let e = (Microsoft_FStar_Absyn_Util.compress_exp cfg.code)
in (let config = (let _126210 = cfg
in {code = e; environment = _126210.environment; stack = _126210.stack; close = _126210.close; steps = _126210.steps})
in (let rebuild = (fun config -> if (is_stack_empty config) then begin
config
end else begin
(let s' = (no_eta config.steps)
in (let args = ((Support.List.map (fun _125316 -> (match (_125316) with
| ((Support.Microsoft.FStar.Util.Inl (t), imp), env) -> begin
((Support.Microsoft.FStar.Util.Inl (sn tcenv (t_config t env s')).code), imp)
end
| ((Support.Microsoft.FStar.Util.Inr (v), imp), env) -> begin
((Support.Microsoft.FStar.Util.Inr (wne tcenv (e_config v env s')).code), imp)
end))) config.stack.args)
in (let _126230 = config
in {code = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (config.code, args) None config.code.Microsoft_FStar_Absyn_Syntax.pos); environment = _126230.environment; stack = empty_stack; close = _126230.close; steps = _126230.steps})))
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
(wne tcenv (let _126255 = config
in {code = vc; environment = env; stack = _126255.stack; close = _126255.close; steps = _126255.steps}))
end
| _ -> begin
(failwith "Impossible: ill-typed term")
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(let args = (Support.List.fold_right (fun a out -> ((a, config.environment))::out) args config.stack.args)
in (let stack = (let _126266 = config.stack
in {args = args})
in (wne tcenv (let _126269 = config
in {code = head; environment = _126269.environment; stack = stack; close = _126269.close; steps = _126269.steps}))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((binders, body)) -> begin
(let rec beta = (fun entries binders args -> (match ((binders, args)) with
| ([], _) -> begin
(let env = (extend_env config.environment entries)
in (wne tcenv (let _126284 = config
in {code = body; environment = env; stack = (let _126286 = config.stack
in {args = args}); close = _126284.close; steps = _126284.steps})))
end
| (_, []) -> begin
(let env = (extend_env config.environment entries)
in (let _126295 = (sn_binders tcenv binders env config.steps)
in (match (_126295) with
| (binders, env) -> begin
(let mk_abs = (fun t -> (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (binders, t) None body.Microsoft_FStar_Absyn_Syntax.pos))
in (let c = (wne tcenv (let _126298 = config
in {code = body; environment = env; stack = (let _126300 = config.stack
in {args = []}); close = _126298.close; steps = (no_eta config.steps)}))
in (let _126303 = c
in {code = (mk_abs c.code); environment = _126303.environment; stack = _126303.stack; close = _126303.close; steps = _126303.steps})))
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
(let c_e1 = (wne tcenv (let _126345 = config
in {code = e1; environment = _126345.environment; stack = empty_stack; close = _126345.close; steps = _126345.steps}))
in (let wn_eqn = (fun _126352 -> (match (_126352) with
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
in (let _126393 = x
in {Microsoft_FStar_Absyn_Syntax.v = _126393.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t.code; Microsoft_FStar_Absyn_Syntax.p = _126393.Microsoft_FStar_Absyn_Syntax.p})))
in (let norm_btvar = (fun a -> (let k = (snk tcenv (k_config a.Microsoft_FStar_Absyn_Syntax.sort config.environment config.steps))
in (let _126398 = a
in {Microsoft_FStar_Absyn_Syntax.v = _126398.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k.code; Microsoft_FStar_Absyn_Syntax.p = _126398.Microsoft_FStar_Absyn_Syntax.p})))
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
(let c_w = (wne tcenv (let _126444 = config
in {code = w; environment = env; stack = empty_stack; close = _126444.close; steps = _126444.steps}))
in Some (c_w.code))
end)
in (let c_body = (wne tcenv (let _126448 = config
in {code = body; environment = env; stack = empty_stack; close = _126448.close; steps = _126448.steps}))
in ((norm_pat pat), w, c_body.code))))))))))
end))
in (let eqns = (Support.List.map wn_eqn eqns)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_match (c_e1.code, eqns) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (rebuild (let _126453 = config
in {code = e; environment = _126453.environment; stack = _126453.stack; close = _126453.close; steps = _126453.steps}))))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((is_rec, lbs), body)) -> begin
(let _126484 = ((Support.List.fold_left (fun _126463 _126467 -> (match ((_126463, _126467)) with
| ((env, lbs), (x, t, e)) -> begin
(let c = (wne tcenv (let _126468 = config
in {code = e; environment = _126468.environment; stack = empty_stack; close = _126468.close; steps = _126468.steps}))
in (let t = (sn tcenv (t_config t config.environment config.steps))
in (let _126481 = (match (x) with
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
in (match (_126481) with
| (y, env) -> begin
(env, ((y, t.code, c.code))::lbs)
end))))
end)) (config.environment, [])) lbs)
in (match (_126484) with
| (env, lbs) -> begin
(let lbs = (Support.List.rev lbs)
in (let c_body = (wne tcenv (let _126486 = config
in {code = body; environment = env; stack = empty_stack; close = _126486.close; steps = _126486.steps}))
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), c_body.code) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (rebuild (let _126490 = config
in {code = e; environment = _126490.environment; stack = _126490.stack; close = _126490.close; steps = _126490.steps})))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t)) -> begin
(let c = (wne tcenv (let _126496 = config
in {code = e; environment = _126496.environment; stack = _126496.stack; close = _126496.close; steps = _126496.steps}))
in if (is_stack_empty config) then begin
(let t = (sn tcenv (t_config t config.environment config.steps))
in (rebuild (let _126500 = config
in {code = (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (c.code, t.code) e.Microsoft_FStar_Absyn_Syntax.pos); environment = _126500.environment; stack = _126500.stack; close = _126500.close; steps = _126500.steps})))
end else begin
c
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, info))) -> begin
(let c = (wne tcenv (let _126507 = config
in {code = e; environment = _126507.environment; stack = _126507.stack; close = _126507.close; steps = _126507.steps}))
in if (is_stack_empty config) then begin
(rebuild (let _126510 = config
in {code = (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((c.code, info)))); environment = _126510.environment; stack = _126510.stack; close = _126510.close; steps = _126510.steps}))
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

let norm_sigelt = (fun tcenv _125317 -> (match (_125317) with
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




