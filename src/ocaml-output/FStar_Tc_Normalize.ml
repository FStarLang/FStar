
open Prims
# 40 "FStar.Tc.Normalize.fst"
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

# 41 "FStar.Tc.Normalize.fst"
let is_WHNF = (fun _discr_ -> (match (_discr_) with
| WHNF (_) -> begin
true
end
| _ -> begin
false
end))

# 42 "FStar.Tc.Normalize.fst"
let is_Eta = (fun _discr_ -> (match (_discr_) with
| Eta (_) -> begin
true
end
| _ -> begin
false
end))

# 43 "FStar.Tc.Normalize.fst"
let is_EtaArgs = (fun _discr_ -> (match (_discr_) with
| EtaArgs (_) -> begin
true
end
| _ -> begin
false
end))

# 44 "FStar.Tc.Normalize.fst"
let is_Delta = (fun _discr_ -> (match (_discr_) with
| Delta (_) -> begin
true
end
| _ -> begin
false
end))

# 45 "FStar.Tc.Normalize.fst"
let is_DeltaHard = (fun _discr_ -> (match (_discr_) with
| DeltaHard (_) -> begin
true
end
| _ -> begin
false
end))

# 46 "FStar.Tc.Normalize.fst"
let is_UnfoldOpaque = (fun _discr_ -> (match (_discr_) with
| UnfoldOpaque (_) -> begin
true
end
| _ -> begin
false
end))

# 47 "FStar.Tc.Normalize.fst"
let is_Beta = (fun _discr_ -> (match (_discr_) with
| Beta (_) -> begin
true
end
| _ -> begin
false
end))

# 48 "FStar.Tc.Normalize.fst"
let is_DeltaComp = (fun _discr_ -> (match (_discr_) with
| DeltaComp (_) -> begin
true
end
| _ -> begin
false
end))

# 49 "FStar.Tc.Normalize.fst"
let is_Simplify = (fun _discr_ -> (match (_discr_) with
| Simplify (_) -> begin
true
end
| _ -> begin
false
end))

# 50 "FStar.Tc.Normalize.fst"
let is_SNComp = (fun _discr_ -> (match (_discr_) with
| SNComp (_) -> begin
true
end
| _ -> begin
false
end))

# 51 "FStar.Tc.Normalize.fst"
let is_Unmeta = (fun _discr_ -> (match (_discr_) with
| Unmeta (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.Tc.Normalize.fst"
let is_Unlabel = (fun _discr_ -> (match (_discr_) with
| Unlabel (_) -> begin
true
end
| _ -> begin
false
end))

# 74 "FStar.Tc.Normalize.fst"
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

# 74 "FStar.Tc.Normalize.fst"
let is_Mkconfig = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkconfig"))))

# 79 "FStar.Tc.Normalize.fst"
let is_Mkenvironment : environment  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenvironment"))))

# 83 "FStar.Tc.Normalize.fst"
let is_Mkstack : stack  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkstack"))))

# 87 "FStar.Tc.Normalize.fst"
let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

# 88 "FStar.Tc.Normalize.fst"
let is_V = (fun _discr_ -> (match (_discr_) with
| V (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "FStar.Tc.Normalize.fst"
let ___T____0 : env_entry  ->  (FStar_Absyn_Syntax.btvdef * tclos) = (fun projectee -> (match (projectee) with
| T (_39_26) -> begin
_39_26
end))

# 88 "FStar.Tc.Normalize.fst"
let ___V____0 : env_entry  ->  (FStar_Absyn_Syntax.bvvdef * vclos) = (fun projectee -> (match (projectee) with
| V (_39_29) -> begin
_39_29
end))

# 93 "FStar.Tc.Normalize.fst"
let empty_env : environment = {context = []; label_suffix = []}

# 97 "FStar.Tc.Normalize.fst"
let extend_env' : environment  ->  env_entry  ->  environment = (fun env b -> (
# 97 "FStar.Tc.Normalize.fst"
let _39_32 = env
in {context = (b)::env.context; label_suffix = _39_32.label_suffix}))

# 98 "FStar.Tc.Normalize.fst"
let extend_env : environment  ->  env_entry Prims.list  ->  environment = (fun env bindings -> (
# 98 "FStar.Tc.Normalize.fst"
let _39_36 = env
in {context = (FStar_List.append bindings env.context); label_suffix = _39_36.label_suffix}))

# 99 "FStar.Tc.Normalize.fst"
let lookup_env : environment  ->  Prims.string  ->  env_entry Prims.option = (fun env key -> (FStar_All.pipe_right env.context (FStar_Util.find_opt (fun _39_1 -> (match (_39_1) with
| T (a, _39_43) -> begin
(a.FStar_Absyn_Syntax.realname.FStar_Ident.idText = key)
end
| V (x, _39_48) -> begin
(x.FStar_Absyn_Syntax.realname.FStar_Ident.idText = key)
end)))))

# 102 "FStar.Tc.Normalize.fst"
let fold_env = (fun env f acc -> (FStar_List.fold_left (fun acc v -> (match (v) with
| T (a, _39_58) -> begin
(f a.FStar_Absyn_Syntax.realname.FStar_Ident.idText v acc)
end
| V (x, _39_63) -> begin
(f x.FStar_Absyn_Syntax.realname.FStar_Ident.idText v acc)
end)) acc env.context))

# 106 "FStar.Tc.Normalize.fst"
let empty_stack : stack = {args = []}

# 111 "FStar.Tc.Normalize.fst"
let rec subst_of_env' : environment  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list = (fun env -> (fold_env env (fun _39_67 v acc -> (match (v) with
| T (a, (t, env')) -> begin
(let _118_113 = (let _118_112 = (let _118_111 = (let _118_110 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_typ _118_110 t))
in (a, _118_111))
in FStar_Util.Inl (_118_112))
in (_118_113)::acc)
end
| V (x, (v, env')) -> begin
(let _118_117 = (let _118_116 = (let _118_115 = (let _118_114 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_exp _118_114 v))
in (x, _118_115))
in FStar_Util.Inr (_118_116))
in (_118_117)::acc)
end)) []))

# 118 "FStar.Tc.Normalize.fst"
let subst_of_env = (fun tcenv env -> (subst_of_env' env))

# 120 "FStar.Tc.Normalize.fst"
let with_new_code = (fun c e -> {code = e; environment = c.environment; stack = empty_stack; close = None; steps = c.steps})

# 128 "FStar.Tc.Normalize.fst"
let rec eta_expand : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun tcenv t -> (
# 129 "FStar.Tc.Normalize.fst"
let k = (let _118_127 = (FStar_Tc_Recheck.recompute_kind t)
in (FStar_All.pipe_right _118_127 FStar_Absyn_Util.compress_kind))
in (
# 130 "FStar.Tc.Normalize.fst"
let rec aux = (fun t k -> (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
t
end
| FStar_Absyn_Syntax.Kind_abbrev (_39_99, k) -> begin
(aux t k)
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k') -> begin
(match ((let _118_132 = (FStar_Absyn_Util.unascribe_typ t)
in _118_132.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam (real, body) -> begin
(
# 138 "FStar.Tc.Normalize.fst"
let rec aux = (fun real expected -> (match ((real, expected)) with
| (_39_116::real, _39_120::expected) -> begin
(aux real expected)
end
| ([], []) -> begin
t
end
| (_39_129::_39_127, []) -> begin
(FStar_All.failwith "Ill-kinded type")
end
| ([], more) -> begin
(
# 144 "FStar.Tc.Normalize.fst"
let _39_138 = (FStar_Absyn_Util.args_of_binders more)
in (match (_39_138) with
| (more, args) -> begin
(
# 145 "FStar.Tc.Normalize.fst"
let body = (FStar_Absyn_Syntax.mk_Typ_app (body, args) None body.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_lam ((FStar_List.append binders more), body) None body.FStar_Absyn_Syntax.pos))
end))
end))
in (aux real binders))
end
| _39_141 -> begin
(
# 151 "FStar.Tc.Normalize.fst"
let _39_144 = (FStar_Absyn_Util.args_of_binders binders)
in (match (_39_144) with
| (binders, args) -> begin
(
# 152 "FStar.Tc.Normalize.fst"
let body = (FStar_Absyn_Syntax.mk_Typ_app (t, args) None t.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_lam (binders, body) None t.FStar_Absyn_Syntax.pos))
end))
end)
end
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_delayed (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _118_140 = (let _118_139 = (let _118_137 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _118_137 FStar_Range.string_of_range))
in (let _118_138 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "%s: Impossible: Kind_unknown: %s" _118_139 _118_138)))
in (FStar_All.failwith _118_140))
end))
in (aux t k))))

# 160 "FStar.Tc.Normalize.fst"
let is_var : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((FStar_Absyn_Util.compress_typ t)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (_39_163); FStar_Absyn_Syntax.tk = _39_161; FStar_Absyn_Syntax.pos = _39_159; FStar_Absyn_Syntax.fvs = _39_157; FStar_Absyn_Syntax.uvs = _39_155} -> begin
true
end
| _39_167 -> begin
false
end))

# 164 "FStar.Tc.Normalize.fst"
let rec eta_expand_exp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp = (fun tcenv e -> (
# 165 "FStar.Tc.Normalize.fst"
let t = (let _118_147 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_All.pipe_right _118_147 FStar_Absyn_Util.compress_typ))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((let _118_148 = (FStar_Absyn_Util.compress_exp e)
in _118_148.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
if ((FStar_List.length bs) = (FStar_List.length bs')) then begin
e
end else begin
(FStar_All.failwith "NYI")
end
end
| _39_180 -> begin
(
# 174 "FStar.Tc.Normalize.fst"
let _39_183 = (FStar_Absyn_Util.args_of_binders bs)
in (match (_39_183) with
| (bs, args) -> begin
(let _118_150 = (let _118_149 = (FStar_Absyn_Syntax.mk_Exp_app (e, args) None e.FStar_Absyn_Syntax.pos)
in (bs, _118_149))
in (FStar_Absyn_Syntax.mk_Exp_abs _118_150 (Some (t)) e.FStar_Absyn_Syntax.pos))
end))
end)
end
| _39_185 -> begin
e
end)))

# 179 "FStar.Tc.Normalize.fst"
let no_eta : step Prims.list  ->  step Prims.list = (fun s -> (FStar_All.pipe_right s (FStar_List.filter (fun _39_2 -> (match (_39_2) with
| Eta -> begin
false
end
| _39_190 -> begin
true
end)))))

# 180 "FStar.Tc.Normalize.fst"
let no_eta_cfg = (fun c -> (
# 180 "FStar.Tc.Normalize.fst"
let _39_192 = c
in (let _118_155 = (no_eta c.steps)
in {code = _39_192.code; environment = _39_192.environment; stack = _39_192.stack; close = _39_192.close; steps = _118_155})))

# 181 "FStar.Tc.Normalize.fst"
let whnf_only = (fun config -> (FStar_All.pipe_right config.steps (FStar_List.contains WHNF)))

# 182 "FStar.Tc.Normalize.fst"
let unmeta = (fun config -> (FStar_All.pipe_right config.steps (FStar_List.contains Unmeta)))

# 183 "FStar.Tc.Normalize.fst"
let unlabel = (fun config -> ((unmeta config) || (FStar_All.pipe_right config.steps (FStar_List.contains Unlabel))))

# 184 "FStar.Tc.Normalize.fst"
let is_stack_empty = (fun config -> (match (config.stack.args) with
| [] -> begin
true
end
| _39_200 -> begin
false
end))

# 187 "FStar.Tc.Normalize.fst"
let has_eta = (fun cfg -> (FStar_All.pipe_right cfg.steps (FStar_List.contains Eta)))

# 189 "FStar.Tc.Normalize.fst"
let rec weak_norm_comp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp_typ = (fun env comp -> (
# 190 "FStar.Tc.Normalize.fst"
let c = (FStar_Absyn_Util.comp_to_comp_typ comp)
in (match ((FStar_Tc_Env.lookup_effect_abbrev env c.FStar_Absyn_Syntax.effect_name)) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(
# 195 "FStar.Tc.Normalize.fst"
let binders' = (FStar_List.map (fun _39_3 -> (match (_39_3) with
| (FStar_Util.Inl (b), imp) -> begin
(let _118_167 = (let _118_166 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inl (_118_166))
in (_118_167, imp))
end
| (FStar_Util.Inr (b), imp) -> begin
(let _118_169 = (let _118_168 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inr (_118_168))
in (_118_169, imp))
end)) binders)
in (
# 198 "FStar.Tc.Normalize.fst"
let subst = (let _118_171 = (let _118_170 = (FStar_Absyn_Util.args_of_binders binders')
in (FStar_All.pipe_right _118_170 Prims.snd))
in (FStar_Absyn_Util.subst_of_list binders _118_171))
in (
# 199 "FStar.Tc.Normalize.fst"
let cdef = (FStar_Absyn_Util.subst_comp subst cdef)
in (
# 200 "FStar.Tc.Normalize.fst"
let subst = (let _118_173 = (let _118_172 = (FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ)
in (_118_172)::c.FStar_Absyn_Syntax.effect_args)
in (FStar_Absyn_Util.subst_of_list binders' _118_173))
in (
# 201 "FStar.Tc.Normalize.fst"
let c1 = (FStar_Absyn_Util.subst_comp subst cdef)
in (
# 202 "FStar.Tc.Normalize.fst"
let c = (FStar_All.pipe_right (
# 202 "FStar.Tc.Normalize.fst"
let _39_224 = (FStar_Absyn_Util.comp_to_comp_typ c1)
in {FStar_Absyn_Syntax.effect_name = _39_224.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _39_224.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _39_224.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = c.FStar_Absyn_Syntax.flags}) FStar_Absyn_Syntax.mk_Comp)
in (weak_norm_comp env c)))))))
end)))

# 205 "FStar.Tc.Normalize.fst"
let t_config = (fun code env steps -> {code = code; environment = env; stack = empty_stack; close = None; steps = steps})

# 211 "FStar.Tc.Normalize.fst"
let k_config = (fun code env steps -> {code = code; environment = env; stack = empty_stack; close = None; steps = steps})

# 217 "FStar.Tc.Normalize.fst"
let e_config = (fun code env steps -> {code = code; environment = env; stack = empty_stack; close = None; steps = steps})

# 223 "FStar.Tc.Normalize.fst"
let c_config = (fun code env steps -> {code = code; environment = env; stack = empty_stack; close = None; steps = steps})

# 231 "FStar.Tc.Normalize.fst"
let close_with_config = (fun cfg f -> Some ((fun t -> (
# 233 "FStar.Tc.Normalize.fst"
let t = (f t)
in (match (cfg.close) with
| None -> begin
t
end
| Some (g) -> begin
(g t)
end)))))

# 238 "FStar.Tc.Normalize.fst"
let rec is_head_symbol : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _118_204 = (FStar_Absyn_Util.compress_typ t)
in _118_204.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _39_255, _39_257)) -> begin
(is_head_symbol t)
end
| _39_262 -> begin
false
end))

# 244 "FStar.Tc.Normalize.fst"
let simplify_then_apply : step Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.args  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ = (fun steps head args pos -> (
# 245 "FStar.Tc.Normalize.fst"
let fallback = (fun _39_268 -> (match (()) with
| () -> begin
(FStar_Absyn_Syntax.mk_Typ_app (head, args) None pos)
end))
in (
# 246 "FStar.Tc.Normalize.fst"
let simp_t = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
Some (true)
end
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid) -> begin
Some (false)
end
| _39_276 -> begin
None
end))
in (
# 250 "FStar.Tc.Normalize.fst"
let simplify = (fun arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (t) -> begin
((simp_t t), arg)
end
| _39_282 -> begin
(None, arg)
end))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps)) then begin
(fallback ())
end else begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.and_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _)::(_, (FStar_Util.Inl (arg), _))::[]) | ((_, (FStar_Util.Inl (arg), _))::(Some (true), _)::[]) -> begin
arg
end
| ((Some (false), _)::_::[]) | (_::(Some (false), _)::[]) -> begin
FStar_Absyn_Util.t_false
end
| _39_329 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.or_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _)::_::[]) | (_::(Some (true), _)::[]) -> begin
FStar_Absyn_Util.t_true
end
| ((Some (false), _)::(_, (FStar_Util.Inl (arg), _))::[]) | ((_, (FStar_Util.Inl (arg), _))::(Some (false), _)::[]) -> begin
arg
end
| _39_374 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
FStar_Absyn_Util.t_true
end
| (Some (true), _39_402)::(_39_392, (FStar_Util.Inl (arg), _39_396))::[] -> begin
arg
end
| _39_406 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (Some (true), _39_410)::[] -> begin
FStar_Absyn_Util.t_false
end
| (Some (false), _39_416)::[] -> begin
FStar_Absyn_Util.t_true
end
| _39_420 -> begin
(fallback ())
end)
end else begin
if ((((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.forall_lid) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid)) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exists_lid)) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) then begin
(match (args) with
| ((FStar_Util.Inl (t), _)::[]) | (_::(FStar_Util.Inl (t), _)::[]) -> begin
(match ((let _118_219 = (FStar_Absyn_Util.compress_typ t)
in _118_219.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam (_39_435::[], body) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
FStar_Absyn_Util.t_true
end
| Some (false) -> begin
FStar_Absyn_Util.t_false
end
| _39_445 -> begin
(fallback ())
end)
end
| _39_447 -> begin
(fallback ())
end)
end
| _39_449 -> begin
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
| _39_451 -> begin
(fallback ())
end)
end))))

# 301 "FStar.Tc.Normalize.fst"
let rec sn_delay : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ config  ->  FStar_Absyn_Syntax.typ config = (fun tcenv cfg -> (
# 302 "FStar.Tc.Normalize.fst"
let aux = (fun _39_455 -> (match (()) with
| () -> begin
(let _118_245 = (sn tcenv cfg)
in _118_245.code)
end))
in (
# 303 "FStar.Tc.Normalize.fst"
let t = (FStar_Absyn_Syntax.mk_Typ_delayed' (FStar_Util.Inr (aux)) None cfg.code.FStar_Absyn_Syntax.pos)
in (
# 304 "FStar.Tc.Normalize.fst"
let _39_457 = cfg
in {code = t; environment = _39_457.environment; stack = empty_stack; close = _39_457.close; steps = _39_457.steps}))))
and sn : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ config  ->  FStar_Absyn_Syntax.typ config = (fun tcenv cfg -> (
# 307 "FStar.Tc.Normalize.fst"
let rebuild = (fun config -> (
# 308 "FStar.Tc.Normalize.fst"
let rebuild_stack = (fun config -> if (is_stack_empty config) then begin
config
end else begin
(
# 310 "FStar.Tc.Normalize.fst"
let s' = if (FStar_List.contains EtaArgs config.steps) then begin
config.steps
end else begin
(no_eta config.steps)
end
in (
# 313 "FStar.Tc.Normalize.fst"
let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _39_4 -> (match (_39_4) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _118_257 = (let _118_256 = (let _118_255 = (sn tcenv (t_config t env s'))
in _118_255.code)
in (FStar_All.pipe_left (fun _118_254 -> FStar_Util.Inl (_118_254)) _118_256))
in (_118_257, imp))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _118_261 = (let _118_260 = (let _118_259 = (wne tcenv (e_config v env s'))
in _118_259.code)
in (FStar_All.pipe_left (fun _118_258 -> FStar_Util.Inr (_118_258)) _118_260))
in (_118_261, imp))
end))))
in (
# 316 "FStar.Tc.Normalize.fst"
let t = (simplify_then_apply config.steps config.code args config.code.FStar_Absyn_Syntax.pos)
in (
# 317 "FStar.Tc.Normalize.fst"
let _39_481 = config
in {code = t; environment = _39_481.environment; stack = empty_stack; close = _39_481.close; steps = _39_481.steps}))))
end)
in (
# 319 "FStar.Tc.Normalize.fst"
let config = (rebuild_stack config)
in (
# 320 "FStar.Tc.Normalize.fst"
let t = (match (config.close) with
| None -> begin
config.code
end
| Some (f) -> begin
(f config.code)
end)
in if (has_eta config) then begin
(
# 324 "FStar.Tc.Normalize.fst"
let _39_488 = config
in (let _118_263 = (eta_expand tcenv t)
in {code = _118_263; environment = _39_488.environment; stack = _39_488.stack; close = _39_488.close; steps = _39_488.steps}))
end else begin
(
# 325 "FStar.Tc.Normalize.fst"
let _39_490 = config
in {code = t; environment = _39_490.environment; stack = _39_490.stack; close = _39_490.close; steps = _39_490.steps})
end))))
in (
# 328 "FStar.Tc.Normalize.fst"
let wk = (fun f -> (match ((FStar_ST.read cfg.code.FStar_Absyn_Syntax.tk)) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _39_501; FStar_Absyn_Syntax.pos = _39_499; FStar_Absyn_Syntax.fvs = _39_497; FStar_Absyn_Syntax.uvs = _39_495}) -> begin
(f (Some (FStar_Absyn_Syntax.ktype)) cfg.code.FStar_Absyn_Syntax.pos)
end
| _39_506 -> begin
(f None cfg.code.FStar_Absyn_Syntax.pos)
end))
in (
# 332 "FStar.Tc.Normalize.fst"
let config = (
# 332 "FStar.Tc.Normalize.fst"
let _39_507 = cfg
in (let _118_276 = (FStar_Absyn_Util.compress_typ cfg.code)
in {code = _118_276; environment = _39_507.environment; stack = _39_507.stack; close = _39_507.close; steps = _39_507.steps}))
in (match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_39_511) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_uvar (_39_514) -> begin
(rebuild config)
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(
# 340 "FStar.Tc.Normalize.fst"
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
# 349 "FStar.Tc.Normalize.fst"
let _39_522 = config
in {code = t; environment = _39_522.environment; stack = _39_522.stack; close = _39_522.close; steps = _39_522.steps}))
end))
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(match ((lookup_env config.environment a.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname.FStar_Ident.idText)) with
| None -> begin
(rebuild config)
end
| Some (T (_39_528, (t, e))) -> begin
(sn tcenv (
# 355 "FStar.Tc.Normalize.fst"
let _39_535 = config
in {code = t; environment = e; stack = _39_535.stack; close = _39_535.close; steps = _39_535.steps}))
end
| _39_538 -> begin
(FStar_All.failwith "Impossible: expected a type")
end)
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(
# 360 "FStar.Tc.Normalize.fst"
let args = (FStar_List.fold_right (fun a out -> ((a, config.environment))::out) args config.stack.args)
in (
# 361 "FStar.Tc.Normalize.fst"
let stack = (
# 361 "FStar.Tc.Normalize.fst"
let _39_546 = config.stack
in {args = args})
in (sn tcenv (
# 362 "FStar.Tc.Normalize.fst"
let _39_549 = config
in {code = head; environment = _39_549.environment; stack = stack; close = _39_549.close; steps = _39_549.steps}))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(match (config.stack.args) with
| [] -> begin
(
# 368 "FStar.Tc.Normalize.fst"
let _39_558 = (sn_binders tcenv binders config.environment config.steps)
in (match (_39_558) with
| (binders, environment) -> begin
(
# 369 "FStar.Tc.Normalize.fst"
let mk_lam = (fun t -> (
# 370 "FStar.Tc.Normalize.fst"
let lam = (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_lam (binders, t)))
in (match (cfg.close) with
| None -> begin
lam
end
| Some (f) -> begin
(f lam)
end)))
in (
# 374 "FStar.Tc.Normalize.fst"
let t2_cfg = (let _118_289 = (let _118_288 = (no_eta config.steps)
in {code = t2; environment = environment; stack = empty_stack; close = None; steps = _118_288})
in (sn_delay tcenv _118_289))
in (
# 379 "FStar.Tc.Normalize.fst"
let _39_566 = t2_cfg
in (let _118_290 = (mk_lam t2_cfg.code)
in {code = _118_290; environment = _39_566.environment; stack = _39_566.stack; close = _39_566.close; steps = _39_566.steps}))))
end))
end
| args -> begin
(
# 382 "FStar.Tc.Normalize.fst"
let rec beta = (fun env_entries binders args -> (match ((binders, args)) with
| ([], _39_575) -> begin
(
# 384 "FStar.Tc.Normalize.fst"
let env = (extend_env config.environment env_entries)
in (sn tcenv (
# 385 "FStar.Tc.Normalize.fst"
let _39_578 = config
in {code = t2; environment = env; stack = (
# 385 "FStar.Tc.Normalize.fst"
let _39_580 = config.stack
in {args = args}); close = _39_578.close; steps = _39_578.steps})))
end
| (_39_583, []) -> begin
(
# 388 "FStar.Tc.Normalize.fst"
let t = (FStar_Absyn_Syntax.mk_Typ_lam (binders, t2) None t2.FStar_Absyn_Syntax.pos)
in (
# 389 "FStar.Tc.Normalize.fst"
let env = (extend_env config.environment env_entries)
in (sn tcenv (
# 390 "FStar.Tc.Normalize.fst"
let _39_588 = config
in {code = t; environment = env; stack = empty_stack; close = _39_588.close; steps = _39_588.steps}))))
end
| (formal::rest, actual::rest') -> begin
(
# 393 "FStar.Tc.Normalize.fst"
let m = (match ((formal, actual)) with
| ((FStar_Util.Inl (a), _39_600), ((FStar_Util.Inl (t), _39_605), env)) -> begin
T ((a.FStar_Absyn_Syntax.v, (t, env)))
end
| ((FStar_Util.Inr (x), _39_613), ((FStar_Util.Inr (v), _39_618), env)) -> begin
V ((x.FStar_Absyn_Syntax.v, (v, env)))
end
| _39_624 -> begin
(let _118_301 = (let _118_300 = (let _118_297 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _118_297))
in (let _118_299 = (FStar_Absyn_Print.binder_to_string formal)
in (let _118_298 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _118_300 _118_299 _118_298))))
in (FStar_All.failwith _118_301))
end)
in (beta ((m)::env_entries) rest rest'))
end))
in (beta [] binders args))
end)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _39_628) -> begin
(sn tcenv (
# 407 "FStar.Tc.Normalize.fst"
let _39_631 = config
in {code = t; environment = _39_631.environment; stack = _39_631.stack; close = _39_631.close; steps = _39_631.steps}))
end
| _39_634 -> begin
(match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, comp) -> begin
(
# 413 "FStar.Tc.Normalize.fst"
let _39_641 = (sn_binders tcenv bs config.environment config.steps)
in (match (_39_641) with
| (binders, environment) -> begin
(
# 414 "FStar.Tc.Normalize.fst"
let c2 = (sncomp tcenv (c_config comp environment config.steps))
in (let _118_305 = (
# 415 "FStar.Tc.Normalize.fst"
let _39_643 = config
in (let _118_304 = (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_fun (binders, c2.code)))
in {code = _118_304; environment = _39_643.environment; stack = _39_643.stack; close = _39_643.close; steps = _39_643.steps}))
in (rebuild _118_305)))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((let _118_307 = (let _118_306 = (FStar_Absyn_Syntax.v_binder x)
in (_118_306)::[])
in (sn_binders tcenv _118_307 config.environment config.steps))) with
| ((FStar_Util.Inr (x), _39_652)::[], env) -> begin
(
# 420 "FStar.Tc.Normalize.fst"
let refine = (fun t -> (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_refine (x, t))))
in (let _118_314 = (let _118_313 = (FStar_All.pipe_right config.steps (FStar_List.filter (fun _39_5 -> (match (_39_5) with
| UnfoldOpaque -> begin
false
end
| _39_662 -> begin
true
end))))
in {code = t; environment = env; stack = empty_stack; close = (close_with_config config refine); steps = _118_313})
in (sn tcenv _118_314)))
end
| _39_664 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
if (unmeta config) then begin
(sn tcenv (
# 431 "FStar.Tc.Normalize.fst"
let _39_670 = config
in {code = t; environment = _39_670.environment; stack = _39_670.stack; close = _39_670.close; steps = _39_670.steps}))
end else begin
(
# 433 "FStar.Tc.Normalize.fst"
let pat = (fun t -> (
# 434 "FStar.Tc.Normalize.fst"
let ps = (FStar_All.pipe_right ps (FStar_List.map (sn_args true tcenv config.environment config.steps)))
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern ((t, ps)))))))
in (sn tcenv (
# 436 "FStar.Tc.Normalize.fst"
let _39_675 = config
in {code = t; environment = _39_675.environment; stack = _39_675.stack; close = (close_with_config config pat); steps = _39_675.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, b)) -> begin
if (unlabel config) then begin
(sn tcenv (
# 440 "FStar.Tc.Normalize.fst"
let _39_684 = config
in {code = t; environment = _39_684.environment; stack = _39_684.stack; close = _39_684.close; steps = _39_684.steps}))
end else begin
(
# 442 "FStar.Tc.Normalize.fst"
let lab = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when ((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) && (FStar_All.pipe_right config.steps (FStar_List.contains Simplify))) -> begin
t
end
| _39_691 -> begin
(match (config.environment.label_suffix) with
| (b', sfx)::_39_693 -> begin
if ((b' = None) || (Some (b) = b')) then begin
(
# 448 "FStar.Tc.Normalize.fst"
let _39_698 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _118_321 = (FStar_Range.string_of_range sfx)
in (FStar_Util.print2 "Stripping label %s because of enclosing refresh %s\n" l _118_321))
end else begin
()
end
in t)
end else begin
(
# 449 "FStar.Tc.Normalize.fst"
let _39_700 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _118_322 = (FStar_Range.string_of_range sfx)
in (FStar_Util.print1 "Normalizer refreshing label: %s\n" _118_322))
end else begin
()
end
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, sfx, b))))))
end
end
| _39_703 -> begin
(FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b)))))
end)
end))
in (sn tcenv (
# 452 "FStar.Tc.Normalize.fst"
let _39_704 = config
in {code = t; environment = _39_704.environment; stack = _39_704.stack; close = (close_with_config config lab); steps = _39_704.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
if (unmeta config) then begin
(sn tcenv (
# 456 "FStar.Tc.Normalize.fst"
let _39_712 = config
in {code = t; environment = _39_712.environment; stack = _39_712.stack; close = _39_712.close; steps = _39_712.steps}))
end else begin
(
# 458 "FStar.Tc.Normalize.fst"
let sfx = (match (b) with
| Some (false) -> begin
r
end
| _39_717 -> begin
FStar_Absyn_Syntax.dummyRange
end)
in (
# 459 "FStar.Tc.Normalize.fst"
let config = (
# 459 "FStar.Tc.Normalize.fst"
let _39_719 = config
in {code = t; environment = (
# 459 "FStar.Tc.Normalize.fst"
let _39_721 = config.environment
in {context = _39_721.context; label_suffix = ((b, sfx))::config.environment.label_suffix}); stack = _39_719.stack; close = _39_719.close; steps = _39_719.steps})
in (sn tcenv config)))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
if (FStar_ST.read flag) then begin
(let _118_328 = (
# 464 "FStar.Tc.Normalize.fst"
let _39_730 = config
in (let _118_327 = (FStar_Absyn_Util.mk_conj t1 t2)
in {code = _118_327; environment = _39_730.environment; stack = _39_730.stack; close = _39_730.close; steps = _39_730.steps}))
in (sn tcenv _118_328))
end else begin
(
# 465 "FStar.Tc.Normalize.fst"
let c1 = (sn tcenv (t_config t1 config.environment config.steps))
in (
# 466 "FStar.Tc.Normalize.fst"
let c2 = (sn tcenv (t_config t2 config.environment config.steps))
in (let _118_330 = (
# 467 "FStar.Tc.Normalize.fst"
let _39_734 = config
in (let _118_329 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula ((c1.code, c2.code, flag))))
in {code = _118_329; environment = _39_734.environment; stack = _39_734.stack; close = _39_734.close; steps = _39_734.steps}))
in (rebuild _118_330))))
end
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_))) | (FStar_Absyn_Syntax.Typ_unknown) | (_) -> begin
(let _118_335 = (let _118_334 = (let _118_331 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _118_331 FStar_Range.string_of_range))
in (let _118_333 = (FStar_Absyn_Print.tag_of_typ config.code)
in (let _118_332 = (FStar_Absyn_Print.typ_to_string config.code)
in (FStar_Util.format3 "(%s) Unexpected type (%s): %s" _118_334 _118_333 _118_332))))
in (FStar_All.failwith _118_335))
end)
end)))))
and sn_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  environment  ->  step Prims.list  ->  (FStar_Absyn_Syntax.binders * environment) = (fun tcenv binders env steps -> (
# 475 "FStar.Tc.Normalize.fst"
let rec aux = (fun out env _39_6 -> (match (_39_6) with
| (FStar_Util.Inl (a), imp)::rest -> begin
(
# 477 "FStar.Tc.Normalize.fst"
let c = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort env steps))
in (
# 478 "FStar.Tc.Normalize.fst"
let b = (let _118_346 = (FStar_Absyn_Util.freshen_bvd a.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _118_346 c.code))
in (
# 479 "FStar.Tc.Normalize.fst"
let btyp = (FStar_Absyn_Util.btvar_to_typ b)
in (
# 480 "FStar.Tc.Normalize.fst"
let b_for_a = T ((a.FStar_Absyn_Syntax.v, (btyp, empty_env)))
in (aux (((FStar_Util.Inl (b), imp))::out) (extend_env' env b_for_a) rest)))))
end
| (FStar_Util.Inr (x), imp)::rest -> begin
(
# 484 "FStar.Tc.Normalize.fst"
let c = (sn_delay tcenv (t_config x.FStar_Absyn_Syntax.sort env steps))
in (
# 485 "FStar.Tc.Normalize.fst"
let y = (let _118_347 = (FStar_Absyn_Util.freshen_bvd x.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _118_347 c.code))
in (
# 486 "FStar.Tc.Normalize.fst"
let yexp = (FStar_Absyn_Util.bvar_to_exp y)
in (
# 487 "FStar.Tc.Normalize.fst"
let y_for_x = V ((x.FStar_Absyn_Syntax.v, (yexp, empty_env)))
in (aux (((FStar_Util.Inr (y), imp))::out) (extend_env' env y_for_x) rest)))))
end
| [] -> begin
((FStar_List.rev out), env)
end))
in (aux [] env binders)))
and sncomp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp config  ->  FStar_Absyn_Syntax.comp config = (fun tcenv cfg -> (
# 494 "FStar.Tc.Normalize.fst"
let m = cfg.code
in (match (m.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) -> begin
(
# 497 "FStar.Tc.Normalize.fst"
let ctconf = (sncomp_typ tcenv (with_new_code cfg ct))
in (
# 498 "FStar.Tc.Normalize.fst"
let _39_778 = cfg
in (let _118_350 = (FStar_Absyn_Syntax.mk_Comp ctconf.code)
in {code = _118_350; environment = _39_778.environment; stack = _39_778.stack; close = _39_778.close; steps = _39_778.steps})))
end
| FStar_Absyn_Syntax.Total (t) -> begin
if (FStar_List.contains DeltaComp cfg.steps) then begin
(let _118_354 = (let _118_353 = (let _118_352 = (let _118_351 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_Absyn_Util.comp_to_comp_typ _118_351))
in (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp _118_352))
in (with_new_code cfg _118_353))
in (FStar_All.pipe_left (sncomp tcenv) _118_354))
end else begin
(
# 503 "FStar.Tc.Normalize.fst"
let t = (sn tcenv (with_new_code cfg t))
in (let _118_355 = (FStar_Absyn_Syntax.mk_Total t.code)
in (with_new_code cfg _118_355)))
end
end)))
and sncomp_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp_typ config  ->  FStar_Absyn_Syntax.comp_typ config = (fun tcenv cfg -> (
# 507 "FStar.Tc.Normalize.fst"
let m = cfg.code
in (
# 508 "FStar.Tc.Normalize.fst"
let norm = (fun _39_787 -> (match (()) with
| () -> begin
(
# 509 "FStar.Tc.Normalize.fst"
let remake = (fun l r eargs flags -> (
# 510 "FStar.Tc.Normalize.fst"
let c = {FStar_Absyn_Syntax.effect_name = l; FStar_Absyn_Syntax.result_typ = r; FStar_Absyn_Syntax.effect_args = eargs; FStar_Absyn_Syntax.flags = flags}
in (
# 511 "FStar.Tc.Normalize.fst"
let _39_794 = cfg
in {code = c; environment = _39_794.environment; stack = _39_794.stack; close = _39_794.close; steps = _39_794.steps})))
in (
# 512 "FStar.Tc.Normalize.fst"
let res = (let _118_368 = (sn tcenv (with_new_code cfg m.FStar_Absyn_Syntax.result_typ))
in _118_368.code)
in (
# 513 "FStar.Tc.Normalize.fst"
let sn_flags = (fun flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _39_7 -> (match (_39_7) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(
# 516 "FStar.Tc.Normalize.fst"
let e = (let _118_372 = (wne tcenv (e_config e cfg.environment cfg.steps))
in _118_372.code)
in FStar_Absyn_Syntax.DECREASES (e))
end
| f -> begin
f
end)))))
in (
# 519 "FStar.Tc.Normalize.fst"
let _39_806 = (let _118_374 = (sn_flags m.FStar_Absyn_Syntax.flags)
in (let _118_373 = (sn_args true tcenv cfg.environment cfg.steps m.FStar_Absyn_Syntax.effect_args)
in (_118_374, _118_373)))
in (match (_39_806) with
| (flags, args) -> begin
(remake m.FStar_Absyn_Syntax.effect_name res args flags)
end)))))
end))
in if (FStar_List.contains DeltaComp cfg.steps) then begin
(match ((FStar_Tc_Env.lookup_effect_abbrev tcenv m.FStar_Absyn_Syntax.effect_name)) with
| Some (_39_808) -> begin
(
# 525 "FStar.Tc.Normalize.fst"
let c = (let _118_375 = (FStar_Absyn_Syntax.mk_Comp m)
in (weak_norm_comp tcenv _118_375))
in (sncomp_typ tcenv (
# 526 "FStar.Tc.Normalize.fst"
let _39_811 = cfg
in {code = c; environment = _39_811.environment; stack = _39_811.stack; close = _39_811.close; steps = _39_811.steps})))
end
| _39_814 -> begin
(norm ())
end)
end else begin
(norm ())
end)))
and sn_args : Prims.bool  ->  FStar_Tc_Env.env  ->  environment  ->  step Prims.list  ->  FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.arg Prims.list = (fun delay tcenv env steps args -> (FStar_All.pipe_right args (FStar_List.map (fun _39_8 -> (match (_39_8) with
| (FStar_Util.Inl (t), imp) when delay -> begin
(let _118_385 = (let _118_384 = (let _118_383 = (sn_delay tcenv (t_config t env steps))
in _118_383.code)
in (FStar_All.pipe_left (fun _118_382 -> FStar_Util.Inl (_118_382)) _118_384))
in (_118_385, imp))
end
| (FStar_Util.Inl (t), imp) -> begin
(let _118_389 = (let _118_388 = (let _118_387 = (sn tcenv (t_config t env steps))
in _118_387.code)
in (FStar_All.pipe_left (fun _118_386 -> FStar_Util.Inl (_118_386)) _118_388))
in (_118_389, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _118_393 = (let _118_392 = (let _118_391 = (wne tcenv (e_config e env steps))
in _118_391.code)
in (FStar_All.pipe_left (fun _118_390 -> FStar_Util.Inr (_118_390)) _118_392))
in (_118_393, imp))
end)))))
and snk : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd config  ->  FStar_Absyn_Syntax.knd config = (fun tcenv cfg -> (
# 537 "FStar.Tc.Normalize.fst"
let w = (fun f -> (f cfg.code.FStar_Absyn_Syntax.pos))
in (match ((let _118_403 = (FStar_Absyn_Util.compress_kind cfg.code)
in _118_403.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Kind_delayed (_)) | (FStar_Absyn_Syntax.Kind_lam (_)) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
cfg
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(
# 544 "FStar.Tc.Normalize.fst"
let args = (let _118_404 = (no_eta cfg.steps)
in (sn_args false tcenv cfg.environment _118_404 args))
in (
# 545 "FStar.Tc.Normalize.fst"
let _39_850 = cfg
in (let _118_406 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar (uv, args)))
in {code = _118_406; environment = _39_850.environment; stack = _39_850.stack; close = _39_850.close; steps = _39_850.steps})))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _39_862; FStar_Absyn_Syntax.pos = _39_860; FStar_Absyn_Syntax.fvs = _39_858; FStar_Absyn_Syntax.uvs = _39_856}) -> begin
(
# 547 "FStar.Tc.Normalize.fst"
let _39_871 = (FStar_Tc_Env.lookup_kind_abbrev tcenv l)
in (match (_39_871) with
| (_39_868, binders, body) -> begin
(
# 548 "FStar.Tc.Normalize.fst"
let subst = (FStar_Absyn_Util.subst_of_list binders args)
in (let _118_408 = (
# 549 "FStar.Tc.Normalize.fst"
let _39_873 = cfg
in (let _118_407 = (FStar_Absyn_Util.subst_kind subst body)
in {code = _118_407; environment = _39_873.environment; stack = _39_873.stack; close = _39_873.close; steps = _39_873.steps}))
in (snk tcenv _118_408)))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_39_876, k) -> begin
(snk tcenv (
# 551 "FStar.Tc.Normalize.fst"
let _39_880 = cfg
in {code = k; environment = _39_880.environment; stack = _39_880.stack; close = _39_880.close; steps = _39_880.steps}))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(
# 553 "FStar.Tc.Normalize.fst"
let _39_888 = (sn_binders tcenv bs cfg.environment cfg.steps)
in (match (_39_888) with
| (bs, env) -> begin
(
# 554 "FStar.Tc.Normalize.fst"
let c2 = (snk tcenv (k_config k env cfg.steps))
in (
# 555 "FStar.Tc.Normalize.fst"
let _39_898 = (match (c2.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs', k) -> begin
((FStar_List.append bs bs'), k)
end
| _39_895 -> begin
(bs, c2.code)
end)
in (match (_39_898) with
| (bs, rhs) -> begin
(
# 558 "FStar.Tc.Normalize.fst"
let _39_899 = cfg
in (let _118_410 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (bs, rhs)))
in {code = _118_410; environment = _39_899.environment; stack = _39_899.stack; close = _39_899.close; steps = _39_899.steps}))
end)))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(FStar_All.failwith "Impossible")
end)))
and wne : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp config  ->  FStar_Absyn_Syntax.exp config = (fun tcenv cfg -> (
# 563 "FStar.Tc.Normalize.fst"
let e = (FStar_Absyn_Util.compress_exp cfg.code)
in (
# 564 "FStar.Tc.Normalize.fst"
let config = (
# 564 "FStar.Tc.Normalize.fst"
let _39_905 = cfg
in {code = e; environment = _39_905.environment; stack = _39_905.stack; close = _39_905.close; steps = _39_905.steps})
in (
# 565 "FStar.Tc.Normalize.fst"
let rebuild = (fun config -> if (is_stack_empty config) then begin
config
end else begin
(
# 567 "FStar.Tc.Normalize.fst"
let s' = if (FStar_List.contains EtaArgs config.steps) then begin
config.steps
end else begin
(no_eta config.steps)
end
in (
# 571 "FStar.Tc.Normalize.fst"
let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _39_9 -> (match (_39_9) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _118_419 = (let _118_418 = (let _118_417 = (sn tcenv (t_config t env s'))
in _118_417.code)
in (FStar_All.pipe_left (fun _118_416 -> FStar_Util.Inl (_118_416)) _118_418))
in (_118_419, imp))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _118_423 = (let _118_422 = (let _118_421 = (wne tcenv (e_config v env s'))
in _118_421.code)
in (FStar_All.pipe_left (fun _118_420 -> FStar_Util.Inr (_118_420)) _118_422))
in (_118_423, imp))
end))))
in (
# 575 "FStar.Tc.Normalize.fst"
let _39_925 = config
in (let _118_424 = (FStar_Absyn_Syntax.mk_Exp_app (config.code, args) None config.code.FStar_Absyn_Syntax.pos)
in {code = _118_424; environment = _39_925.environment; stack = empty_stack; close = _39_925.close; steps = _39_925.steps}))))
end)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_39_928) -> begin
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
| Some (V (_39_943, (vc, env))) -> begin
(wne tcenv (
# 587 "FStar.Tc.Normalize.fst"
let _39_950 = config
in {code = vc; environment = env; stack = _39_950.stack; close = _39_950.close; steps = _39_950.steps}))
end
| _39_953 -> begin
(FStar_All.failwith "Impossible: ill-typed term")
end)
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(
# 592 "FStar.Tc.Normalize.fst"
let args = (FStar_List.fold_right (fun a out -> ((a, config.environment))::out) args config.stack.args)
in (
# 593 "FStar.Tc.Normalize.fst"
let stack = (
# 593 "FStar.Tc.Normalize.fst"
let _39_961 = config.stack
in {args = args})
in (wne tcenv (
# 594 "FStar.Tc.Normalize.fst"
let _39_964 = config
in {code = head; environment = _39_964.environment; stack = stack; close = _39_964.close; steps = _39_964.steps}))))
end
| FStar_Absyn_Syntax.Exp_abs (binders, body) -> begin
(
# 597 "FStar.Tc.Normalize.fst"
let rec beta = (fun entries binders args -> (match ((binders, args)) with
| ([], _39_976) -> begin
(
# 599 "FStar.Tc.Normalize.fst"
let env = (extend_env config.environment entries)
in (wne tcenv (
# 600 "FStar.Tc.Normalize.fst"
let _39_979 = config
in {code = body; environment = env; stack = (
# 602 "FStar.Tc.Normalize.fst"
let _39_981 = config.stack
in {args = args}); close = _39_979.close; steps = _39_979.steps})))
end
| (_39_984, []) -> begin
(
# 605 "FStar.Tc.Normalize.fst"
let env = (extend_env config.environment entries)
in (
# 606 "FStar.Tc.Normalize.fst"
let _39_990 = (sn_binders tcenv binders env config.steps)
in (match (_39_990) with
| (binders, env) -> begin
(
# 607 "FStar.Tc.Normalize.fst"
let mk_abs = (fun t -> (FStar_Absyn_Syntax.mk_Exp_abs (binders, t) None body.FStar_Absyn_Syntax.pos))
in (
# 608 "FStar.Tc.Normalize.fst"
let c = (let _118_436 = (
# 608 "FStar.Tc.Normalize.fst"
let _39_993 = config
in (let _118_435 = (no_eta config.steps)
in {code = body; environment = env; stack = (
# 610 "FStar.Tc.Normalize.fst"
let _39_995 = config.stack
in {args = []}); close = _39_993.close; steps = _118_435}))
in (wne tcenv _118_436))
in (
# 612 "FStar.Tc.Normalize.fst"
let _39_998 = c
in (let _118_437 = (mk_abs c.code)
in {code = _118_437; environment = _39_998.environment; stack = _39_998.stack; close = _39_998.close; steps = _39_998.steps}))))
end)))
end
| (formal::rest, actual::rest') -> begin
(
# 615 "FStar.Tc.Normalize.fst"
let m = (match ((formal, actual)) with
| ((FStar_Util.Inl (a), _39_1010), ((FStar_Util.Inl (t), _39_1015), env)) -> begin
T ((a.FStar_Absyn_Syntax.v, (t, env)))
end
| ((FStar_Util.Inr (x), _39_1023), ((FStar_Util.Inr (v), _39_1028), env)) -> begin
V ((x.FStar_Absyn_Syntax.v, (v, env)))
end
| _39_1034 -> begin
(let _118_442 = (let _118_441 = (let _118_438 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _118_438))
in (let _118_440 = (FStar_Absyn_Print.binder_to_string formal)
in (let _118_439 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _118_441 _118_440 _118_439))))
in (FStar_All.failwith _118_442))
end)
in (beta ((m)::entries) rest rest'))
end))
in (beta [] binders config.stack.args))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(
# 627 "FStar.Tc.Normalize.fst"
let c_e1 = (wne tcenv (
# 627 "FStar.Tc.Normalize.fst"
let _39_1040 = config
in {code = e1; environment = _39_1040.environment; stack = empty_stack; close = _39_1040.close; steps = _39_1040.steps}))
in (
# 628 "FStar.Tc.Normalize.fst"
let wn_eqn = (fun _39_1047 -> (match (_39_1047) with
| (pat, w, body) -> begin
(
# 629 "FStar.Tc.Normalize.fst"
let rec pat_vars = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_disj (p::_39_1053) -> begin
(pat_vars p)
end
| FStar_Absyn_Syntax.Pat_cons (_39_1058, _39_1060, pats) -> begin
(FStar_List.collect (fun _39_1067 -> (match (_39_1067) with
| (x, _39_1066) -> begin
(pat_vars x)
end)) pats)
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _118_448 = (FStar_Absyn_Syntax.v_binder x)
in (_118_448)::[])
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _118_449 = (FStar_Absyn_Syntax.t_binder a)
in (_118_449)::[])
end
| (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_constant (_)) | (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
[]
end))
in (
# 641 "FStar.Tc.Normalize.fst"
let vars = (pat_vars pat)
in (
# 642 "FStar.Tc.Normalize.fst"
let norm_bvvar = (fun x -> (
# 643 "FStar.Tc.Normalize.fst"
let t = (sn tcenv (t_config x.FStar_Absyn_Syntax.sort config.environment config.steps))
in (
# 644 "FStar.Tc.Normalize.fst"
let _39_1091 = x
in {FStar_Absyn_Syntax.v = _39_1091.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t.code; FStar_Absyn_Syntax.p = _39_1091.FStar_Absyn_Syntax.p})))
in (
# 646 "FStar.Tc.Normalize.fst"
let norm_btvar = (fun a -> (
# 647 "FStar.Tc.Normalize.fst"
let k = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort config.environment config.steps))
in (
# 648 "FStar.Tc.Normalize.fst"
let _39_1096 = a
in {FStar_Absyn_Syntax.v = _39_1096.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k.code; FStar_Absyn_Syntax.p = _39_1096.FStar_Absyn_Syntax.p})))
in (
# 650 "FStar.Tc.Normalize.fst"
let rec norm_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (pats) -> begin
(let _118_457 = (let _118_456 = (FStar_List.map norm_pat pats)
in FStar_Absyn_Syntax.Pat_disj (_118_456))
in (FStar_Absyn_Util.withinfo _118_457 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _118_462 = (let _118_461 = (let _118_460 = (FStar_List.map (fun _39_1109 -> (match (_39_1109) with
| (x, i) -> begin
(let _118_459 = (norm_pat x)
in (_118_459, i))
end)) pats)
in (fv, q, _118_460))
in FStar_Absyn_Syntax.Pat_cons (_118_461))
in (FStar_Absyn_Util.withinfo _118_462 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _118_464 = (let _118_463 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_var (_118_463))
in (FStar_Absyn_Util.withinfo _118_464 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _118_466 = (let _118_465 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_tvar (_118_465))
in (FStar_Absyn_Util.withinfo _118_466 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let _118_468 = (let _118_467 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_wild (_118_467))
in (FStar_Absyn_Util.withinfo _118_468 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let _118_470 = (let _118_469 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_twild (_118_469))
in (FStar_Absyn_Util.withinfo _118_470 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_constant (_39_1119) -> begin
p
end
| FStar_Absyn_Syntax.Pat_dot_term (x, e) -> begin
(
# 670 "FStar.Tc.Normalize.fst"
let e = (wne tcenv (e_config e config.environment config.steps))
in (let _118_473 = (let _118_472 = (let _118_471 = (norm_bvvar x)
in (_118_471, e.code))
in FStar_Absyn_Syntax.Pat_dot_term (_118_472))
in (FStar_Absyn_Util.withinfo _118_473 None p.FStar_Absyn_Syntax.p)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
(
# 674 "FStar.Tc.Normalize.fst"
let t = (sn tcenv (t_config t config.environment config.steps))
in (let _118_476 = (let _118_475 = (let _118_474 = (norm_btvar a)
in (_118_474, t.code))
in FStar_Absyn_Syntax.Pat_dot_typ (_118_475))
in (FStar_Absyn_Util.withinfo _118_476 None p.FStar_Absyn_Syntax.p)))
end))
in (
# 677 "FStar.Tc.Normalize.fst"
let env_entries = (FStar_List.fold_left (fun entries b -> (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(
# 679 "FStar.Tc.Normalize.fst"
let atyp = (FStar_Absyn_Util.btvar_to_typ a)
in (T ((a.FStar_Absyn_Syntax.v, (atyp, empty_env))))::entries)
end
| FStar_Util.Inr (x) -> begin
(
# 683 "FStar.Tc.Normalize.fst"
let xexp = (FStar_Absyn_Util.bvar_to_exp x)
in (V ((x.FStar_Absyn_Syntax.v, (xexp, empty_env))))::entries)
end)) [] vars)
in (
# 685 "FStar.Tc.Normalize.fst"
let env = (extend_env config.environment env_entries)
in (
# 686 "FStar.Tc.Normalize.fst"
let w = (match (w) with
| None -> begin
None
end
| Some (w) -> begin
(
# 689 "FStar.Tc.Normalize.fst"
let c_w = (wne tcenv (
# 689 "FStar.Tc.Normalize.fst"
let _39_1144 = config
in {code = w; environment = env; stack = empty_stack; close = _39_1144.close; steps = _39_1144.steps}))
in Some (c_w.code))
end)
in (
# 691 "FStar.Tc.Normalize.fst"
let c_body = (wne tcenv (
# 691 "FStar.Tc.Normalize.fst"
let _39_1148 = config
in {code = body; environment = env; stack = empty_stack; close = _39_1148.close; steps = _39_1148.steps}))
in (let _118_479 = (norm_pat pat)
in (_118_479, w, c_body.code)))))))))))
end))
in (
# 693 "FStar.Tc.Normalize.fst"
let eqns = (FStar_List.map wn_eqn eqns)
in (
# 694 "FStar.Tc.Normalize.fst"
let e = (FStar_Absyn_Syntax.mk_Exp_match (c_e1.code, eqns) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (
# 695 "FStar.Tc.Normalize.fst"
let _39_1153 = config
in {code = e; environment = _39_1153.environment; stack = _39_1153.stack; close = _39_1153.close; steps = _39_1153.steps}) rebuild)))))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), body) -> begin
(
# 698 "FStar.Tc.Normalize.fst"
let _39_1185 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _39_1163 _39_1168 -> (match ((_39_1163, _39_1168)) with
| ((env, lbs), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = eff; FStar_Absyn_Syntax.lbdef = e}) -> begin
(
# 699 "FStar.Tc.Normalize.fst"
let c = (wne tcenv (
# 699 "FStar.Tc.Normalize.fst"
let _39_1169 = config
in {code = e; environment = _39_1169.environment; stack = empty_stack; close = _39_1169.close; steps = _39_1169.steps}))
in (
# 700 "FStar.Tc.Normalize.fst"
let t = (sn tcenv (t_config t config.environment config.steps))
in (
# 701 "FStar.Tc.Normalize.fst"
let _39_1182 = (match (x) with
| FStar_Util.Inl (x) -> begin
(
# 703 "FStar.Tc.Normalize.fst"
let y = (let _118_482 = if is_rec then begin
x
end else begin
(FStar_Absyn_Util.freshen_bvd x)
end
in (FStar_Absyn_Util.bvd_to_bvar_s _118_482 t.code))
in (
# 704 "FStar.Tc.Normalize.fst"
let yexp = (FStar_Absyn_Util.bvar_to_exp y)
in (
# 705 "FStar.Tc.Normalize.fst"
let y_for_x = V ((x, (yexp, empty_env)))
in (FStar_Util.Inl (y.FStar_Absyn_Syntax.v), (extend_env' env y_for_x)))))
end
| _39_1179 -> begin
(x, env)
end)
in (match (_39_1182) with
| (y, env) -> begin
(let _118_484 = (let _118_483 = (FStar_Absyn_Syntax.mk_lb (y, eff, t.code, c.code))
in (_118_483)::lbs)
in (env, _118_484))
end))))
end)) (config.environment, [])))
in (match (_39_1185) with
| (env, lbs) -> begin
(
# 709 "FStar.Tc.Normalize.fst"
let lbs = (FStar_List.rev lbs)
in (
# 710 "FStar.Tc.Normalize.fst"
let c_body = (wne tcenv (
# 710 "FStar.Tc.Normalize.fst"
let _39_1187 = config
in {code = body; environment = env; stack = empty_stack; close = _39_1187.close; steps = _39_1187.steps}))
in (
# 711 "FStar.Tc.Normalize.fst"
let e = (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), c_body.code) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (
# 712 "FStar.Tc.Normalize.fst"
let _39_1191 = config
in {code = e; environment = _39_1191.environment; stack = _39_1191.stack; close = _39_1191.close; steps = _39_1191.steps}) rebuild))))
end))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, l) -> begin
(
# 715 "FStar.Tc.Normalize.fst"
let c = (wne tcenv (
# 715 "FStar.Tc.Normalize.fst"
let _39_1198 = config
in {code = e; environment = _39_1198.environment; stack = _39_1198.stack; close = _39_1198.close; steps = _39_1198.steps}))
in if (is_stack_empty config) then begin
(
# 717 "FStar.Tc.Normalize.fst"
let t = (sn tcenv (t_config t config.environment config.steps))
in (let _118_486 = (
# 718 "FStar.Tc.Normalize.fst"
let _39_1202 = config
in (let _118_485 = (FStar_Absyn_Syntax.mk_Exp_ascribed (c.code, t.code, l) None e.FStar_Absyn_Syntax.pos)
in {code = _118_485; environment = _39_1202.environment; stack = _39_1202.stack; close = _39_1202.close; steps = _39_1202.steps}))
in (rebuild _118_486)))
end else begin
c
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, info)) -> begin
(
# 722 "FStar.Tc.Normalize.fst"
let c = (wne tcenv (
# 722 "FStar.Tc.Normalize.fst"
let _39_1209 = config
in {code = e; environment = _39_1209.environment; stack = _39_1209.stack; close = _39_1209.close; steps = _39_1209.steps}))
in if (is_stack_empty config) then begin
(let _118_488 = (
# 724 "FStar.Tc.Normalize.fst"
let _39_1212 = config
in (let _118_487 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((c.code, info))))
in {code = _118_487; environment = _39_1212.environment; stack = _39_1212.stack; close = _39_1212.close; steps = _39_1212.steps}))
in (rebuild _118_488))
end else begin
c
end)
end)))))

# 730 "FStar.Tc.Normalize.fst"
let norm_kind : steps  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun steps tcenv k -> (
# 731 "FStar.Tc.Normalize.fst"
let c = (snk tcenv (k_config k empty_env steps))
in (FStar_Absyn_Util.compress_kind c.code)))

# 734 "FStar.Tc.Normalize.fst"
let norm_typ : steps  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun steps tcenv t -> (
# 735 "FStar.Tc.Normalize.fst"
let c = (sn tcenv (t_config t empty_env steps))
in c.code))

# 738 "FStar.Tc.Normalize.fst"
let norm_exp : steps  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp = (fun steps tcenv e -> (
# 739 "FStar.Tc.Normalize.fst"
let c = (wne tcenv (e_config e empty_env steps))
in c.code))

# 742 "FStar.Tc.Normalize.fst"
let norm_sigelt : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt = (fun tcenv _39_10 -> (match (_39_10) with
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, b) -> begin
(
# 744 "FStar.Tc.Normalize.fst"
let e = (let _118_512 = (let _118_511 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None r)
in (lbs, _118_511))
in (FStar_Absyn_Syntax.mk_Exp_let _118_512 None r))
in (
# 745 "FStar.Tc.Normalize.fst"
let e = (norm_exp ((Beta)::[]) tcenv e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_let (lbs, _39_1238) -> begin
FStar_Absyn_Syntax.Sig_let ((lbs, r, l, b))
end
| _39_1242 -> begin
(FStar_All.failwith "Impossible")
end)))
end
| s -> begin
s
end))

# 752 "FStar.Tc.Normalize.fst"
let whnf : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun tcenv t -> (
# 753 "FStar.Tc.Normalize.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_refine (_)) -> begin
t
end
| (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _118_517 = (eta_expand tcenv t)
in (FStar_All.pipe_right _118_517 FStar_Absyn_Util.compress_typ))
end
| (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) | (_) -> begin
(norm_typ ((WHNF)::(Beta)::(Eta)::[]) tcenv t)
end)))

# 765 "FStar.Tc.Normalize.fst"
let norm_comp : steps  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp = (fun steps tcenv c -> (
# 766 "FStar.Tc.Normalize.fst"
let c = (sncomp tcenv (c_config c empty_env steps))
in c.code))

# 769 "FStar.Tc.Normalize.fst"
let normalize_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun tcenv k -> (
# 770 "FStar.Tc.Normalize.fst"
let steps = (Eta)::(Delta)::(Beta)::[]
in (norm_kind steps tcenv k)))

# 773 "FStar.Tc.Normalize.fst"
let normalize_comp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp = (fun tcenv c -> (
# 774 "FStar.Tc.Normalize.fst"
let steps = (Eta)::(Delta)::(Beta)::(SNComp)::(DeltaComp)::[]
in (norm_comp steps tcenv c)))

# 777 "FStar.Tc.Normalize.fst"
let normalize : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun tcenv t -> (norm_typ ((DeltaHard)::(Beta)::(Eta)::[]) tcenv t))

# 780 "FStar.Tc.Normalize.fst"
let exp_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  Prims.string = (fun tcenv e -> (let _118_540 = (norm_exp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv e)
in (FStar_Absyn_Print.exp_to_string _118_540)))

# 783 "FStar.Tc.Normalize.fst"
let typ_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun tcenv t -> (let _118_545 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv t)
in (FStar_Absyn_Print.typ_to_string _118_545)))

# 786 "FStar.Tc.Normalize.fst"
let kind_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun tcenv k -> (let _118_550 = (norm_kind ((Beta)::(SNComp)::(Unmeta)::[]) tcenv k)
in (FStar_Absyn_Print.kind_to_string _118_550)))

# 789 "FStar.Tc.Normalize.fst"
let formula_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun tcenv f -> (let _118_555 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv f)
in (FStar_Absyn_Print.formula_to_string _118_555)))

# 792 "FStar.Tc.Normalize.fst"
let comp_typ_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  Prims.string = (fun tcenv c -> (let _118_560 = (norm_comp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv c)
in (FStar_Absyn_Print.comp_typ_to_string _118_560)))

# 795 "FStar.Tc.Normalize.fst"
let normalize_refinement : steps  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun steps env t0 -> (
# 796 "FStar.Tc.Normalize.fst"
let t = (norm_typ (FStar_List.append ((Beta)::(WHNF)::(DeltaHard)::[]) steps) env t0)
in (
# 797 "FStar.Tc.Normalize.fst"
let rec aux = (fun t -> (
# 798 "FStar.Tc.Normalize.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(
# 801 "FStar.Tc.Normalize.fst"
let t0 = (aux x.FStar_Absyn_Syntax.sort)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (y, phi1) -> begin
(let _118_575 = (let _118_574 = (let _118_573 = (let _118_572 = (let _118_571 = (let _118_570 = (let _118_569 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _118_569))
in FStar_Util.Inr (_118_570))
in (_118_571)::[])
in (FStar_Absyn_Util.subst_typ _118_572 phi))
in (FStar_Absyn_Util.mk_conj phi1 _118_573))
in (y, _118_574))
in (FStar_Absyn_Syntax.mk_Typ_refine _118_575 (Some (FStar_Absyn_Syntax.ktype)) t0.FStar_Absyn_Syntax.pos))
end
| _39_1351 -> begin
t
end))
end
| _39_1353 -> begin
t
end)))
in (aux t))))




