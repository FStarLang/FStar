
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
| T (_38_26) -> begin
_38_26
end))

# 88 "FStar.Tc.Normalize.fst"
let ___V____0 : env_entry  ->  (FStar_Absyn_Syntax.bvvdef * vclos) = (fun projectee -> (match (projectee) with
| V (_38_29) -> begin
_38_29
end))

# 93 "FStar.Tc.Normalize.fst"
let empty_env : environment = {context = []; label_suffix = []}

# 97 "FStar.Tc.Normalize.fst"
let extend_env' : environment  ->  env_entry  ->  environment = (fun env b -> (
# 97 "FStar.Tc.Normalize.fst"
let _38_32 = env
in {context = (b)::env.context; label_suffix = _38_32.label_suffix}))

# 98 "FStar.Tc.Normalize.fst"
let extend_env : environment  ->  env_entry Prims.list  ->  environment = (fun env bindings -> (
# 98 "FStar.Tc.Normalize.fst"
let _38_36 = env
in {context = (FStar_List.append bindings env.context); label_suffix = _38_36.label_suffix}))

# 99 "FStar.Tc.Normalize.fst"
let lookup_env : environment  ->  Prims.string  ->  env_entry Prims.option = (fun env key -> (FStar_All.pipe_right env.context (FStar_Util.find_opt (fun _38_1 -> (match (_38_1) with
| T (a, _38_43) -> begin
(a.FStar_Absyn_Syntax.realname.FStar_Ident.idText = key)
end
| V (x, _38_48) -> begin
(x.FStar_Absyn_Syntax.realname.FStar_Ident.idText = key)
end)))))

# 102 "FStar.Tc.Normalize.fst"
let fold_env = (fun env f acc -> (FStar_List.fold_left (fun acc v -> (match (v) with
| T (a, _38_58) -> begin
(f a.FStar_Absyn_Syntax.realname.FStar_Ident.idText v acc)
end
| V (x, _38_63) -> begin
(f x.FStar_Absyn_Syntax.realname.FStar_Ident.idText v acc)
end)) acc env.context))

# 106 "FStar.Tc.Normalize.fst"
let empty_stack : stack = {args = []}

# 111 "FStar.Tc.Normalize.fst"
let rec subst_of_env' : environment  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list = (fun env -> (fold_env env (fun _38_67 v acc -> (match (v) with
| T (a, (t, env')) -> begin
(let _119_113 = (let _119_112 = (let _119_111 = (let _119_110 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_typ _119_110 t))
in (a, _119_111))
in FStar_Util.Inl (_119_112))
in (_119_113)::acc)
end
| V (x, (v, env')) -> begin
(let _119_117 = (let _119_116 = (let _119_115 = (let _119_114 = (subst_of_env' env')
in (FStar_Absyn_Util.subst_exp _119_114 v))
in (x, _119_115))
in FStar_Util.Inr (_119_116))
in (_119_117)::acc)
end)) []))

# 118 "FStar.Tc.Normalize.fst"
let subst_of_env = (fun tcenv env -> (subst_of_env' env))

# 120 "FStar.Tc.Normalize.fst"
let with_new_code = (fun c e -> {code = e; environment = c.environment; stack = empty_stack; close = None; steps = c.steps})

# 128 "FStar.Tc.Normalize.fst"
let rec eta_expand : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun tcenv t -> (
# 129 "FStar.Tc.Normalize.fst"
let k = (let _119_127 = (FStar_Tc_Recheck.recompute_kind t)
in (FStar_All.pipe_right _119_127 FStar_Absyn_Util.compress_kind))
in (
# 130 "FStar.Tc.Normalize.fst"
let rec aux = (fun t k -> (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
t
end
| FStar_Absyn_Syntax.Kind_abbrev (_38_99, k) -> begin
(aux t k)
end
| FStar_Absyn_Syntax.Kind_arrow (binders, k') -> begin
(match ((let _119_132 = (FStar_Absyn_Util.unascribe_typ t)
in _119_132.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam (real, body) -> begin
(
# 138 "FStar.Tc.Normalize.fst"
let rec aux = (fun real expected -> (match ((real, expected)) with
| (_38_116::real, _38_120::expected) -> begin
(aux real expected)
end
| ([], []) -> begin
t
end
| (_38_129::_38_127, []) -> begin
(FStar_All.failwith "Ill-kinded type")
end
| ([], more) -> begin
(
# 144 "FStar.Tc.Normalize.fst"
let _38_138 = (FStar_Absyn_Util.args_of_binders more)
in (match (_38_138) with
| (more, args) -> begin
(
# 145 "FStar.Tc.Normalize.fst"
let body = (FStar_Absyn_Syntax.mk_Typ_app (body, args) None body.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_lam ((FStar_List.append binders more), body) None body.FStar_Absyn_Syntax.pos))
end))
end))
in (aux real binders))
end
| _38_141 -> begin
(
# 151 "FStar.Tc.Normalize.fst"
let _38_144 = (FStar_Absyn_Util.args_of_binders binders)
in (match (_38_144) with
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
(let _119_140 = (let _119_139 = (let _119_137 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _119_137 FStar_Range.string_of_range))
in (let _119_138 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format2 "%s: Impossible: Kind_unknown: %s" _119_139 _119_138)))
in (FStar_All.failwith _119_140))
end))
in (aux t k))))

# 160 "FStar.Tc.Normalize.fst"
let is_var : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((FStar_Absyn_Util.compress_typ t)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (_38_163); FStar_Absyn_Syntax.tk = _38_161; FStar_Absyn_Syntax.pos = _38_159; FStar_Absyn_Syntax.fvs = _38_157; FStar_Absyn_Syntax.uvs = _38_155} -> begin
true
end
| _38_167 -> begin
false
end))

# 164 "FStar.Tc.Normalize.fst"
let rec eta_expand_exp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp = (fun tcenv e -> (
# 165 "FStar.Tc.Normalize.fst"
let t = (let _119_147 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_All.pipe_right _119_147 FStar_Absyn_Util.compress_typ))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((let _119_148 = (FStar_Absyn_Util.compress_exp e)
in _119_148.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (bs', body) -> begin
if ((FStar_List.length bs) = (FStar_List.length bs')) then begin
e
end else begin
(FStar_All.failwith "NYI")
end
end
| _38_180 -> begin
(
# 174 "FStar.Tc.Normalize.fst"
let _38_183 = (FStar_Absyn_Util.args_of_binders bs)
in (match (_38_183) with
| (bs, args) -> begin
(let _119_150 = (let _119_149 = (FStar_Absyn_Syntax.mk_Exp_app (e, args) None e.FStar_Absyn_Syntax.pos)
in (bs, _119_149))
in (FStar_Absyn_Syntax.mk_Exp_abs _119_150 (Some (t)) e.FStar_Absyn_Syntax.pos))
end))
end)
end
| _38_185 -> begin
e
end)))

# 179 "FStar.Tc.Normalize.fst"
let no_eta : step Prims.list  ->  step Prims.list = (fun s -> (FStar_All.pipe_right s (FStar_List.filter (fun _38_2 -> (match (_38_2) with
| Eta -> begin
false
end
| _38_190 -> begin
true
end)))))

# 180 "FStar.Tc.Normalize.fst"
let no_eta_cfg = (fun c -> (
# 180 "FStar.Tc.Normalize.fst"
let _38_192 = c
in (let _119_155 = (no_eta c.steps)
in {code = _38_192.code; environment = _38_192.environment; stack = _38_192.stack; close = _38_192.close; steps = _119_155})))

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
| _38_200 -> begin
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
let binders' = (FStar_List.map (fun _38_3 -> (match (_38_3) with
| (FStar_Util.Inl (b), imp) -> begin
(let _119_167 = (let _119_166 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inl (_119_166))
in (_119_167, imp))
end
| (FStar_Util.Inr (b), imp) -> begin
(let _119_169 = (let _119_168 = (FStar_Absyn_Util.freshen_bvar b)
in FStar_Util.Inr (_119_168))
in (_119_169, imp))
end)) binders)
in (
# 198 "FStar.Tc.Normalize.fst"
let subst = (let _119_171 = (let _119_170 = (FStar_Absyn_Util.args_of_binders binders')
in (FStar_All.pipe_right _119_170 Prims.snd))
in (FStar_Absyn_Util.subst_of_list binders _119_171))
in (
# 199 "FStar.Tc.Normalize.fst"
let cdef = (FStar_Absyn_Util.subst_comp subst cdef)
in (
# 200 "FStar.Tc.Normalize.fst"
let subst = (let _119_173 = (let _119_172 = (FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ)
in (_119_172)::c.FStar_Absyn_Syntax.effect_args)
in (FStar_Absyn_Util.subst_of_list binders' _119_173))
in (
# 201 "FStar.Tc.Normalize.fst"
let c1 = (FStar_Absyn_Util.subst_comp subst cdef)
in (
# 202 "FStar.Tc.Normalize.fst"
let c = (FStar_All.pipe_right (
# 202 "FStar.Tc.Normalize.fst"
let _38_224 = (FStar_Absyn_Util.comp_to_comp_typ c1)
in {FStar_Absyn_Syntax.effect_name = _38_224.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _38_224.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _38_224.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = c.FStar_Absyn_Syntax.flags}) FStar_Absyn_Syntax.mk_Comp)
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
let rec is_head_symbol : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _119_204 = (FStar_Absyn_Util.compress_typ t)
in _119_204.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _38_255, _38_257)) -> begin
(is_head_symbol t)
end
| _38_262 -> begin
false
end))

# 244 "FStar.Tc.Normalize.fst"
let simplify_then_apply : step Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.args  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.typ = (fun steps head args pos -> (
# 245 "FStar.Tc.Normalize.fst"
let fallback = (fun _38_268 -> (match (()) with
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
| _38_276 -> begin
None
end))
in (
# 250 "FStar.Tc.Normalize.fst"
let simplify = (fun arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (t) -> begin
((simp_t t), arg)
end
| _38_282 -> begin
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
| _38_329 -> begin
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
| _38_374 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
FStar_Absyn_Util.t_true
end
| (Some (true), _38_402)::(_38_392, (FStar_Util.Inl (arg), _38_396))::[] -> begin
arg
end
| _38_406 -> begin
(fallback ())
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (Some (true), _38_410)::[] -> begin
FStar_Absyn_Util.t_false
end
| (Some (false), _38_416)::[] -> begin
FStar_Absyn_Util.t_true
end
| _38_420 -> begin
(fallback ())
end)
end else begin
if ((((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.forall_lid) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid)) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exists_lid)) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) then begin
(match (args) with
| ((FStar_Util.Inl (t), _)::[]) | (_::(FStar_Util.Inl (t), _)::[]) -> begin
(match ((let _119_219 = (FStar_Absyn_Util.compress_typ t)
in _119_219.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_lam (_38_435::[], body) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
FStar_Absyn_Util.t_true
end
| Some (false) -> begin
FStar_Absyn_Util.t_false
end
| _38_445 -> begin
(fallback ())
end)
end
| _38_447 -> begin
(fallback ())
end)
end
| _38_449 -> begin
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
| _38_451 -> begin
(fallback ())
end)
end))))

# 301 "FStar.Tc.Normalize.fst"
let rec sn_delay : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ config  ->  FStar_Absyn_Syntax.typ config = (fun tcenv cfg -> (
# 302 "FStar.Tc.Normalize.fst"
let aux = (fun _38_455 -> (match (()) with
| () -> begin
(let _119_245 = (sn tcenv cfg)
in _119_245.code)
end))
in (
# 303 "FStar.Tc.Normalize.fst"
let t = (FStar_Absyn_Syntax.mk_Typ_delayed' (FStar_Util.Inr (aux)) None cfg.code.FStar_Absyn_Syntax.pos)
in (
# 304 "FStar.Tc.Normalize.fst"
let _38_457 = cfg
in {code = t; environment = _38_457.environment; stack = empty_stack; close = _38_457.close; steps = _38_457.steps}))))
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
let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _38_4 -> (match (_38_4) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _119_257 = (let _119_256 = (let _119_255 = (sn tcenv (t_config t env s'))
in _119_255.code)
in (FStar_All.pipe_left (fun _119_254 -> FStar_Util.Inl (_119_254)) _119_256))
in (_119_257, imp))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _119_261 = (let _119_260 = (let _119_259 = (wne tcenv (e_config v env s'))
in _119_259.code)
in (FStar_All.pipe_left (fun _119_258 -> FStar_Util.Inr (_119_258)) _119_260))
in (_119_261, imp))
end))))
in (
# 316 "FStar.Tc.Normalize.fst"
let t = (simplify_then_apply config.steps config.code args config.code.FStar_Absyn_Syntax.pos)
in (
# 317 "FStar.Tc.Normalize.fst"
let _38_481 = config
in {code = t; environment = _38_481.environment; stack = empty_stack; close = _38_481.close; steps = _38_481.steps}))))
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
let _38_488 = config
in (let _119_263 = (eta_expand tcenv t)
in {code = _119_263; environment = _38_488.environment; stack = _38_488.stack; close = _38_488.close; steps = _38_488.steps}))
end else begin
(
# 325 "FStar.Tc.Normalize.fst"
let _38_490 = config
in {code = t; environment = _38_490.environment; stack = _38_490.stack; close = _38_490.close; steps = _38_490.steps})
end))))
in (
# 328 "FStar.Tc.Normalize.fst"
let wk = (fun f -> (match ((FStar_ST.read cfg.code.FStar_Absyn_Syntax.tk)) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_type; FStar_Absyn_Syntax.tk = _38_501; FStar_Absyn_Syntax.pos = _38_499; FStar_Absyn_Syntax.fvs = _38_497; FStar_Absyn_Syntax.uvs = _38_495}) -> begin
(f (Some (FStar_Absyn_Syntax.ktype)) cfg.code.FStar_Absyn_Syntax.pos)
end
| _38_506 -> begin
(f None cfg.code.FStar_Absyn_Syntax.pos)
end))
in (
# 332 "FStar.Tc.Normalize.fst"
let config = (
# 332 "FStar.Tc.Normalize.fst"
let _38_507 = cfg
in (let _119_276 = (FStar_Absyn_Util.compress_typ cfg.code)
in {code = _119_276; environment = _38_507.environment; stack = _38_507.stack; close = _38_507.close; steps = _38_507.steps}))
in (match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_38_511) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_uvar (_38_514) -> begin
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
let _38_522 = config
in {code = t; environment = _38_522.environment; stack = _38_522.stack; close = _38_522.close; steps = _38_522.steps}))
end))
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(match ((lookup_env config.environment a.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname.FStar_Ident.idText)) with
| None -> begin
(rebuild config)
end
| Some (T (_38_528, (t, e))) -> begin
(sn tcenv (
# 355 "FStar.Tc.Normalize.fst"
let _38_535 = config
in {code = t; environment = e; stack = _38_535.stack; close = _38_535.close; steps = _38_535.steps}))
end
| _38_538 -> begin
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
let _38_546 = config.stack
in {args = args})
in (sn tcenv (
# 362 "FStar.Tc.Normalize.fst"
let _38_549 = config
in {code = head; environment = _38_549.environment; stack = stack; close = _38_549.close; steps = _38_549.steps}))))
end
| FStar_Absyn_Syntax.Typ_lam (binders, t2) -> begin
(match (config.stack.args) with
| [] -> begin
(
# 368 "FStar.Tc.Normalize.fst"
let _38_558 = (sn_binders tcenv binders config.environment config.steps)
in (match (_38_558) with
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
let t2_cfg = (let _119_289 = (let _119_288 = (no_eta config.steps)
in {code = t2; environment = environment; stack = empty_stack; close = None; steps = _119_288})
in (sn_delay tcenv _119_289))
in (
# 379 "FStar.Tc.Normalize.fst"
let _38_566 = t2_cfg
in (let _119_290 = (mk_lam t2_cfg.code)
in {code = _119_290; environment = _38_566.environment; stack = _38_566.stack; close = _38_566.close; steps = _38_566.steps}))))
end))
end
| args -> begin
(
# 382 "FStar.Tc.Normalize.fst"
let rec beta = (fun env_entries binders args -> (match ((binders, args)) with
| ([], _38_575) -> begin
(
# 384 "FStar.Tc.Normalize.fst"
let env = (extend_env config.environment env_entries)
in (sn tcenv (
# 385 "FStar.Tc.Normalize.fst"
let _38_578 = config
in {code = t2; environment = env; stack = (
# 385 "FStar.Tc.Normalize.fst"
let _38_580 = config.stack
in {args = args}); close = _38_578.close; steps = _38_578.steps})))
end
| (_38_583, []) -> begin
(
# 388 "FStar.Tc.Normalize.fst"
let t = (FStar_Absyn_Syntax.mk_Typ_lam (binders, t2) None t2.FStar_Absyn_Syntax.pos)
in (
# 389 "FStar.Tc.Normalize.fst"
let env = (extend_env config.environment env_entries)
in (sn tcenv (
# 390 "FStar.Tc.Normalize.fst"
let _38_588 = config
in {code = t; environment = env; stack = empty_stack; close = _38_588.close; steps = _38_588.steps}))))
end
| (formal::rest, actual::rest') -> begin
(
# 393 "FStar.Tc.Normalize.fst"
let m = (match ((formal, actual)) with
| ((FStar_Util.Inl (a), _38_600), ((FStar_Util.Inl (t), _38_605), env)) -> begin
T ((a.FStar_Absyn_Syntax.v, (t, env)))
end
| ((FStar_Util.Inr (x), _38_613), ((FStar_Util.Inr (v), _38_618), env)) -> begin
V ((x.FStar_Absyn_Syntax.v, (v, env)))
end
| _38_624 -> begin
(let _119_301 = (let _119_300 = (let _119_297 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _119_297))
in (let _119_299 = (FStar_Absyn_Print.binder_to_string formal)
in (let _119_298 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _119_300 _119_299 _119_298))))
in (FStar_All.failwith _119_301))
end)
in (beta ((m)::env_entries) rest rest'))
end))
in (beta [] binders args))
end)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _38_628) -> begin
(sn tcenv (
# 407 "FStar.Tc.Normalize.fst"
let _38_631 = config
in {code = t; environment = _38_631.environment; stack = _38_631.stack; close = _38_631.close; steps = _38_631.steps}))
end
| _38_634 -> begin
(match (config.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, comp) -> begin
(
# 413 "FStar.Tc.Normalize.fst"
let _38_641 = (sn_binders tcenv bs config.environment config.steps)
in (match (_38_641) with
| (binders, environment) -> begin
(
# 414 "FStar.Tc.Normalize.fst"
let c2 = (sncomp tcenv (c_config comp environment config.steps))
in (let _119_305 = (
# 415 "FStar.Tc.Normalize.fst"
let _38_643 = config
in (let _119_304 = (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_fun (binders, c2.code)))
in {code = _119_304; environment = _38_643.environment; stack = _38_643.stack; close = _38_643.close; steps = _38_643.steps}))
in (rebuild _119_305)))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((let _119_307 = (let _119_306 = (FStar_Absyn_Syntax.v_binder x)
in (_119_306)::[])
in (sn_binders tcenv _119_307 config.environment config.steps))) with
| ((FStar_Util.Inr (x), _38_652)::[], env) -> begin
(
# 420 "FStar.Tc.Normalize.fst"
let refine = (fun t -> (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_refine (x, t))))
in (let _119_314 = (let _119_313 = (FStar_All.pipe_right config.steps (FStar_List.filter (fun _38_5 -> (match (_38_5) with
| UnfoldOpaque -> begin
false
end
| _38_662 -> begin
true
end))))
in {code = t; environment = env; stack = empty_stack; close = (close_with_config config refine); steps = _119_313})
in (sn tcenv _119_314)))
end
| _38_664 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
if (unmeta config) then begin
(sn tcenv (
# 431 "FStar.Tc.Normalize.fst"
let _38_670 = config
in {code = t; environment = _38_670.environment; stack = _38_670.stack; close = _38_670.close; steps = _38_670.steps}))
end else begin
(
# 433 "FStar.Tc.Normalize.fst"
let pat = (fun t -> (
# 434 "FStar.Tc.Normalize.fst"
let ps = (FStar_All.pipe_right ps (FStar_List.map (sn_args true tcenv config.environment config.steps)))
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern ((t, ps)))))))
in (sn tcenv (
# 436 "FStar.Tc.Normalize.fst"
let _38_675 = config
in {code = t; environment = _38_675.environment; stack = _38_675.stack; close = (close_with_config config pat); steps = _38_675.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, b)) -> begin
if (unlabel config) then begin
(sn tcenv (
# 440 "FStar.Tc.Normalize.fst"
let _38_684 = config
in {code = t; environment = _38_684.environment; stack = _38_684.stack; close = _38_684.close; steps = _38_684.steps}))
end else begin
(
# 442 "FStar.Tc.Normalize.fst"
let lab = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when ((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) && (FStar_All.pipe_right config.steps (FStar_List.contains Simplify))) -> begin
t
end
| _38_691 -> begin
(match (config.environment.label_suffix) with
| (b', sfx)::_38_693 -> begin
if ((b' = None) || (Some (b) = b')) then begin
(
# 448 "FStar.Tc.Normalize.fst"
let _38_698 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _119_321 = (FStar_Range.string_of_range sfx)
in (FStar_Util.print2 "Stripping label %s because of enclosing refresh %s\n" l _119_321))
end else begin
()
end
in t)
end else begin
(
# 449 "FStar.Tc.Normalize.fst"
let _38_700 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _119_322 = (FStar_Range.string_of_range sfx)
in (FStar_Util.print1 "Normalizer refreshing label: %s\n" _119_322))
end else begin
()
end
in (FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, sfx, b))))))
end
end
| _38_703 -> begin
(FStar_All.pipe_left wk (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, b)))))
end)
end))
in (sn tcenv (
# 452 "FStar.Tc.Normalize.fst"
let _38_704 = config
in {code = t; environment = _38_704.environment; stack = _38_704.stack; close = (close_with_config config lab); steps = _38_704.steps})))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
if (unmeta config) then begin
(sn tcenv (
# 456 "FStar.Tc.Normalize.fst"
let _38_712 = config
in {code = t; environment = _38_712.environment; stack = _38_712.stack; close = _38_712.close; steps = _38_712.steps}))
end else begin
(
# 458 "FStar.Tc.Normalize.fst"
let sfx = (match (b) with
| Some (false) -> begin
r
end
| _38_717 -> begin
FStar_Absyn_Syntax.dummyRange
end)
in (
# 459 "FStar.Tc.Normalize.fst"
let config = (
# 459 "FStar.Tc.Normalize.fst"
let _38_719 = config
in {code = t; environment = (
# 459 "FStar.Tc.Normalize.fst"
let _38_721 = config.environment
in {context = _38_721.context; label_suffix = ((b, sfx))::config.environment.label_suffix}); stack = _38_719.stack; close = _38_719.close; steps = _38_719.steps})
in (sn tcenv config)))
end
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
if (FStar_ST.read flag) then begin
(let _119_328 = (
# 464 "FStar.Tc.Normalize.fst"
let _38_730 = config
in (let _119_327 = (FStar_Absyn_Util.mk_conj t1 t2)
in {code = _119_327; environment = _38_730.environment; stack = _38_730.stack; close = _38_730.close; steps = _38_730.steps}))
in (sn tcenv _119_328))
end else begin
(
# 465 "FStar.Tc.Normalize.fst"
let c1 = (sn tcenv (t_config t1 config.environment config.steps))
in (
# 466 "FStar.Tc.Normalize.fst"
let c2 = (sn tcenv (t_config t2 config.environment config.steps))
in (let _119_330 = (
# 467 "FStar.Tc.Normalize.fst"
let _38_734 = config
in (let _119_329 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula ((c1.code, c2.code, flag))))
in {code = _119_329; environment = _38_734.environment; stack = _38_734.stack; close = _38_734.close; steps = _38_734.steps}))
in (rebuild _119_330))))
end
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_))) | (FStar_Absyn_Syntax.Typ_unknown) | (_) -> begin
(let _119_335 = (let _119_334 = (let _119_331 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_right _119_331 FStar_Range.string_of_range))
in (let _119_333 = (FStar_Absyn_Print.tag_of_typ config.code)
in (let _119_332 = (FStar_Absyn_Print.typ_to_string config.code)
in (FStar_Util.format3 "(%s) Unexpected type (%s): %s" _119_334 _119_333 _119_332))))
in (FStar_All.failwith _119_335))
end)
end)))))
and sn_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  environment  ->  step Prims.list  ->  (FStar_Absyn_Syntax.binders * environment) = (fun tcenv binders env steps -> (
# 475 "FStar.Tc.Normalize.fst"
let rec aux = (fun out env _38_6 -> (match (_38_6) with
| (FStar_Util.Inl (a), imp)::rest -> begin
(
# 477 "FStar.Tc.Normalize.fst"
let c = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort env steps))
in (
# 478 "FStar.Tc.Normalize.fst"
let b = (let _119_346 = (FStar_Absyn_Util.freshen_bvd a.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _119_346 c.code))
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
let y = (let _119_347 = (FStar_Absyn_Util.freshen_bvd x.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.bvd_to_bvar_s _119_347 c.code))
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
let _38_778 = cfg
in (let _119_350 = (FStar_Absyn_Syntax.mk_Comp ctconf.code)
in {code = _119_350; environment = _38_778.environment; stack = _38_778.stack; close = _38_778.close; steps = _38_778.steps})))
end
| FStar_Absyn_Syntax.Total (t) -> begin
if (FStar_List.contains DeltaComp cfg.steps) then begin
(let _119_354 = (let _119_353 = (let _119_352 = (let _119_351 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_Absyn_Util.comp_to_comp_typ _119_351))
in (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp _119_352))
in (with_new_code cfg _119_353))
in (FStar_All.pipe_left (sncomp tcenv) _119_354))
end else begin
(
# 503 "FStar.Tc.Normalize.fst"
let t = (sn tcenv (with_new_code cfg t))
in (let _119_355 = (FStar_Absyn_Syntax.mk_Total t.code)
in (with_new_code cfg _119_355)))
end
end)))
and sncomp_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp_typ config  ->  FStar_Absyn_Syntax.comp_typ config = (fun tcenv cfg -> (
# 507 "FStar.Tc.Normalize.fst"
let m = cfg.code
in (
# 508 "FStar.Tc.Normalize.fst"
let norm = (fun _38_787 -> (match (()) with
| () -> begin
(
# 509 "FStar.Tc.Normalize.fst"
let remake = (fun l r eargs flags -> (
# 510 "FStar.Tc.Normalize.fst"
let c = {FStar_Absyn_Syntax.effect_name = l; FStar_Absyn_Syntax.result_typ = r; FStar_Absyn_Syntax.effect_args = eargs; FStar_Absyn_Syntax.flags = flags}
in (
# 511 "FStar.Tc.Normalize.fst"
let _38_794 = cfg
in {code = c; environment = _38_794.environment; stack = _38_794.stack; close = _38_794.close; steps = _38_794.steps})))
in (
# 512 "FStar.Tc.Normalize.fst"
let res = (let _119_368 = (sn tcenv (with_new_code cfg m.FStar_Absyn_Syntax.result_typ))
in _119_368.code)
in (
# 513 "FStar.Tc.Normalize.fst"
let sn_flags = (fun flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _38_7 -> (match (_38_7) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(
# 516 "FStar.Tc.Normalize.fst"
let e = (let _119_372 = (wne tcenv (e_config e cfg.environment cfg.steps))
in _119_372.code)
in FStar_Absyn_Syntax.DECREASES (e))
end
| f -> begin
f
end)))))
in (
# 519 "FStar.Tc.Normalize.fst"
let _38_806 = (let _119_374 = (sn_flags m.FStar_Absyn_Syntax.flags)
in (let _119_373 = (sn_args true tcenv cfg.environment cfg.steps m.FStar_Absyn_Syntax.effect_args)
in (_119_374, _119_373)))
in (match (_38_806) with
| (flags, args) -> begin
(remake m.FStar_Absyn_Syntax.effect_name res args flags)
end)))))
end))
in if (FStar_List.contains DeltaComp cfg.steps) then begin
(match ((FStar_Tc_Env.lookup_effect_abbrev tcenv m.FStar_Absyn_Syntax.effect_name)) with
| Some (_38_808) -> begin
(
# 525 "FStar.Tc.Normalize.fst"
let c = (let _119_375 = (FStar_Absyn_Syntax.mk_Comp m)
in (weak_norm_comp tcenv _119_375))
in (sncomp_typ tcenv (
# 526 "FStar.Tc.Normalize.fst"
let _38_811 = cfg
in {code = c; environment = _38_811.environment; stack = _38_811.stack; close = _38_811.close; steps = _38_811.steps})))
end
| _38_814 -> begin
(norm ())
end)
end else begin
(norm ())
end)))
and sn_args : Prims.bool  ->  FStar_Tc_Env.env  ->  environment  ->  step Prims.list  ->  FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.arg Prims.list = (fun delay tcenv env steps args -> (FStar_All.pipe_right args (FStar_List.map (fun _38_8 -> (match (_38_8) with
| (FStar_Util.Inl (t), imp) when delay -> begin
(let _119_385 = (let _119_384 = (let _119_383 = (sn_delay tcenv (t_config t env steps))
in _119_383.code)
in (FStar_All.pipe_left (fun _119_382 -> FStar_Util.Inl (_119_382)) _119_384))
in (_119_385, imp))
end
| (FStar_Util.Inl (t), imp) -> begin
(let _119_389 = (let _119_388 = (let _119_387 = (sn tcenv (t_config t env steps))
in _119_387.code)
in (FStar_All.pipe_left (fun _119_386 -> FStar_Util.Inl (_119_386)) _119_388))
in (_119_389, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _119_393 = (let _119_392 = (let _119_391 = (wne tcenv (e_config e env steps))
in _119_391.code)
in (FStar_All.pipe_left (fun _119_390 -> FStar_Util.Inr (_119_390)) _119_392))
in (_119_393, imp))
end)))))
and snk : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd config  ->  FStar_Absyn_Syntax.knd config = (fun tcenv cfg -> (
# 537 "FStar.Tc.Normalize.fst"
let w = (fun f -> (f cfg.code.FStar_Absyn_Syntax.pos))
in (match ((let _119_403 = (FStar_Absyn_Util.compress_kind cfg.code)
in _119_403.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Kind_delayed (_)) | (FStar_Absyn_Syntax.Kind_lam (_)) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
cfg
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(
# 544 "FStar.Tc.Normalize.fst"
let args = (let _119_404 = (no_eta cfg.steps)
in (sn_args false tcenv cfg.environment _119_404 args))
in (
# 545 "FStar.Tc.Normalize.fst"
let _38_850 = cfg
in (let _119_406 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar (uv, args)))
in {code = _119_406; environment = _38_850.environment; stack = _38_850.stack; close = _38_850.close; steps = _38_850.steps})))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _38_862; FStar_Absyn_Syntax.pos = _38_860; FStar_Absyn_Syntax.fvs = _38_858; FStar_Absyn_Syntax.uvs = _38_856}) -> begin
(
# 547 "FStar.Tc.Normalize.fst"
let _38_871 = (FStar_Tc_Env.lookup_kind_abbrev tcenv l)
in (match (_38_871) with
| (_38_868, binders, body) -> begin
(
# 548 "FStar.Tc.Normalize.fst"
let subst = (FStar_Absyn_Util.subst_of_list binders args)
in (let _119_408 = (
# 549 "FStar.Tc.Normalize.fst"
let _38_873 = cfg
in (let _119_407 = (FStar_Absyn_Util.subst_kind subst body)
in {code = _119_407; environment = _38_873.environment; stack = _38_873.stack; close = _38_873.close; steps = _38_873.steps}))
in (snk tcenv _119_408)))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_38_876, k) -> begin
(snk tcenv (
# 551 "FStar.Tc.Normalize.fst"
let _38_880 = cfg
in {code = k; environment = _38_880.environment; stack = _38_880.stack; close = _38_880.close; steps = _38_880.steps}))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(
# 553 "FStar.Tc.Normalize.fst"
let _38_888 = (sn_binders tcenv bs cfg.environment cfg.steps)
in (match (_38_888) with
| (bs, env) -> begin
(
# 554 "FStar.Tc.Normalize.fst"
let c2 = (snk tcenv (k_config k env cfg.steps))
in (
# 555 "FStar.Tc.Normalize.fst"
let _38_898 = (match (c2.code.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (bs', k) -> begin
((FStar_List.append bs bs'), k)
end
| _38_895 -> begin
(bs, c2.code)
end)
in (match (_38_898) with
| (bs, rhs) -> begin
(
# 558 "FStar.Tc.Normalize.fst"
let _38_899 = cfg
in (let _119_410 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (bs, rhs)))
in {code = _119_410; environment = _38_899.environment; stack = _38_899.stack; close = _38_899.close; steps = _38_899.steps}))
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
let _38_905 = cfg
in {code = e; environment = _38_905.environment; stack = _38_905.stack; close = _38_905.close; steps = _38_905.steps})
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
let args = (FStar_All.pipe_right config.stack.args (FStar_List.map (fun _38_9 -> (match (_38_9) with
| ((FStar_Util.Inl (t), imp), env) -> begin
(let _119_419 = (let _119_418 = (let _119_417 = (sn tcenv (t_config t env s'))
in _119_417.code)
in (FStar_All.pipe_left (fun _119_416 -> FStar_Util.Inl (_119_416)) _119_418))
in (_119_419, imp))
end
| ((FStar_Util.Inr (v), imp), env) -> begin
(let _119_423 = (let _119_422 = (let _119_421 = (wne tcenv (e_config v env s'))
in _119_421.code)
in (FStar_All.pipe_left (fun _119_420 -> FStar_Util.Inr (_119_420)) _119_422))
in (_119_423, imp))
end))))
in (
# 575 "FStar.Tc.Normalize.fst"
let _38_925 = config
in (let _119_424 = (FStar_Absyn_Syntax.mk_Exp_app (config.code, args) None config.code.FStar_Absyn_Syntax.pos)
in {code = _119_424; environment = _38_925.environment; stack = empty_stack; close = _38_925.close; steps = _38_925.steps}))))
end)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_38_928) -> begin
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
| Some (V (_38_943, (vc, env))) -> begin
(wne tcenv (
# 587 "FStar.Tc.Normalize.fst"
let _38_950 = config
in {code = vc; environment = env; stack = _38_950.stack; close = _38_950.close; steps = _38_950.steps}))
end
| _38_953 -> begin
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
let _38_961 = config.stack
in {args = args})
in (wne tcenv (
# 594 "FStar.Tc.Normalize.fst"
let _38_964 = config
in {code = head; environment = _38_964.environment; stack = stack; close = _38_964.close; steps = _38_964.steps}))))
end
| FStar_Absyn_Syntax.Exp_abs (binders, body) -> begin
(
# 597 "FStar.Tc.Normalize.fst"
let rec beta = (fun entries binders args -> (match ((binders, args)) with
| ([], _38_976) -> begin
(
# 599 "FStar.Tc.Normalize.fst"
let env = (extend_env config.environment entries)
in (wne tcenv (
# 600 "FStar.Tc.Normalize.fst"
let _38_979 = config
in {code = body; environment = env; stack = (
# 602 "FStar.Tc.Normalize.fst"
let _38_981 = config.stack
in {args = args}); close = _38_979.close; steps = _38_979.steps})))
end
| (_38_984, []) -> begin
(
# 605 "FStar.Tc.Normalize.fst"
let env = (extend_env config.environment entries)
in (
# 606 "FStar.Tc.Normalize.fst"
let _38_990 = (sn_binders tcenv binders env config.steps)
in (match (_38_990) with
| (binders, env) -> begin
(
# 607 "FStar.Tc.Normalize.fst"
let mk_abs = (fun t -> (FStar_Absyn_Syntax.mk_Exp_abs (binders, t) None body.FStar_Absyn_Syntax.pos))
in (
# 608 "FStar.Tc.Normalize.fst"
let c = (let _119_436 = (
# 608 "FStar.Tc.Normalize.fst"
let _38_993 = config
in (let _119_435 = (no_eta config.steps)
in {code = body; environment = env; stack = (
# 610 "FStar.Tc.Normalize.fst"
let _38_995 = config.stack
in {args = []}); close = _38_993.close; steps = _119_435}))
in (wne tcenv _119_436))
in (
# 612 "FStar.Tc.Normalize.fst"
let _38_998 = c
in (let _119_437 = (mk_abs c.code)
in {code = _119_437; environment = _38_998.environment; stack = _38_998.stack; close = _38_998.close; steps = _38_998.steps}))))
end)))
end
| (formal::rest, actual::rest') -> begin
(
# 615 "FStar.Tc.Normalize.fst"
let m = (match ((formal, actual)) with
| ((FStar_Util.Inl (a), _38_1010), ((FStar_Util.Inl (t), _38_1015), env)) -> begin
T ((a.FStar_Absyn_Syntax.v, (t, env)))
end
| ((FStar_Util.Inr (x), _38_1023), ((FStar_Util.Inr (v), _38_1028), env)) -> begin
V ((x.FStar_Absyn_Syntax.v, (v, env)))
end
| _38_1034 -> begin
(let _119_442 = (let _119_441 = (let _119_438 = (FStar_All.pipe_left FStar_Absyn_Syntax.argpos (Prims.fst actual))
in (FStar_Range.string_of_range _119_438))
in (let _119_440 = (FStar_Absyn_Print.binder_to_string formal)
in (let _119_439 = (FStar_All.pipe_left FStar_Absyn_Print.arg_to_string (Prims.fst actual))
in (FStar_Util.format3 "(%s) Impossible: ill-typed redex\n formal is %s\nactual is %s\n" _119_441 _119_440 _119_439))))
in (FStar_All.failwith _119_442))
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
let _38_1040 = config
in {code = e1; environment = _38_1040.environment; stack = empty_stack; close = _38_1040.close; steps = _38_1040.steps}))
in (
# 628 "FStar.Tc.Normalize.fst"
let wn_eqn = (fun _38_1047 -> (match (_38_1047) with
| (pat, w, body) -> begin
(
# 629 "FStar.Tc.Normalize.fst"
let rec pat_vars = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_disj (p::_38_1053) -> begin
(pat_vars p)
end
| FStar_Absyn_Syntax.Pat_cons (_38_1058, _38_1060, pats) -> begin
(FStar_List.collect (fun _38_1067 -> (match (_38_1067) with
| (x, _38_1066) -> begin
(pat_vars x)
end)) pats)
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _119_448 = (FStar_Absyn_Syntax.v_binder x)
in (_119_448)::[])
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _119_449 = (FStar_Absyn_Syntax.t_binder a)
in (_119_449)::[])
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
let _38_1091 = x
in {FStar_Absyn_Syntax.v = _38_1091.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t.code; FStar_Absyn_Syntax.p = _38_1091.FStar_Absyn_Syntax.p})))
in (
# 646 "FStar.Tc.Normalize.fst"
let norm_btvar = (fun a -> (
# 647 "FStar.Tc.Normalize.fst"
let k = (snk tcenv (k_config a.FStar_Absyn_Syntax.sort config.environment config.steps))
in (
# 648 "FStar.Tc.Normalize.fst"
let _38_1096 = a
in {FStar_Absyn_Syntax.v = _38_1096.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k.code; FStar_Absyn_Syntax.p = _38_1096.FStar_Absyn_Syntax.p})))
in (
# 650 "FStar.Tc.Normalize.fst"
let rec norm_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (pats) -> begin
(let _119_457 = (let _119_456 = (FStar_List.map norm_pat pats)
in FStar_Absyn_Syntax.Pat_disj (_119_456))
in (FStar_Absyn_Util.withinfo _119_457 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_cons (fv, q, pats) -> begin
(let _119_462 = (let _119_461 = (let _119_460 = (FStar_List.map (fun _38_1109 -> (match (_38_1109) with
| (x, i) -> begin
(let _119_459 = (norm_pat x)
in (_119_459, i))
end)) pats)
in (fv, q, _119_460))
in FStar_Absyn_Syntax.Pat_cons (_119_461))
in (FStar_Absyn_Util.withinfo _119_462 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(let _119_464 = (let _119_463 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_var (_119_463))
in (FStar_Absyn_Util.withinfo _119_464 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(let _119_466 = (let _119_465 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_tvar (_119_465))
in (FStar_Absyn_Util.withinfo _119_466 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_wild (x) -> begin
(let _119_468 = (let _119_467 = (norm_bvvar x)
in FStar_Absyn_Syntax.Pat_wild (_119_467))
in (FStar_Absyn_Util.withinfo _119_468 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_twild (a) -> begin
(let _119_470 = (let _119_469 = (norm_btvar a)
in FStar_Absyn_Syntax.Pat_twild (_119_469))
in (FStar_Absyn_Util.withinfo _119_470 None p.FStar_Absyn_Syntax.p))
end
| FStar_Absyn_Syntax.Pat_constant (_38_1119) -> begin
p
end
| FStar_Absyn_Syntax.Pat_dot_term (x, e) -> begin
(
# 670 "FStar.Tc.Normalize.fst"
let e = (wne tcenv (e_config e config.environment config.steps))
in (let _119_473 = (let _119_472 = (let _119_471 = (norm_bvvar x)
in (_119_471, e.code))
in FStar_Absyn_Syntax.Pat_dot_term (_119_472))
in (FStar_Absyn_Util.withinfo _119_473 None p.FStar_Absyn_Syntax.p)))
end
| FStar_Absyn_Syntax.Pat_dot_typ (a, t) -> begin
(
# 674 "FStar.Tc.Normalize.fst"
let t = (sn tcenv (t_config t config.environment config.steps))
in (let _119_476 = (let _119_475 = (let _119_474 = (norm_btvar a)
in (_119_474, t.code))
in FStar_Absyn_Syntax.Pat_dot_typ (_119_475))
in (FStar_Absyn_Util.withinfo _119_476 None p.FStar_Absyn_Syntax.p)))
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
let _38_1144 = config
in {code = w; environment = env; stack = empty_stack; close = _38_1144.close; steps = _38_1144.steps}))
in Some (c_w.code))
end)
in (
# 691 "FStar.Tc.Normalize.fst"
let c_body = (wne tcenv (
# 691 "FStar.Tc.Normalize.fst"
let _38_1148 = config
in {code = body; environment = env; stack = empty_stack; close = _38_1148.close; steps = _38_1148.steps}))
in (let _119_479 = (norm_pat pat)
in (_119_479, w, c_body.code)))))))))))
end))
in (
# 693 "FStar.Tc.Normalize.fst"
let eqns = (FStar_List.map wn_eqn eqns)
in (
# 694 "FStar.Tc.Normalize.fst"
let e = (FStar_Absyn_Syntax.mk_Exp_match (c_e1.code, eqns) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (
# 695 "FStar.Tc.Normalize.fst"
let _38_1153 = config
in {code = e; environment = _38_1153.environment; stack = _38_1153.stack; close = _38_1153.close; steps = _38_1153.steps}) rebuild)))))
end
| FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), body) -> begin
(
# 698 "FStar.Tc.Normalize.fst"
let _38_1185 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _38_1163 _38_1168 -> (match ((_38_1163, _38_1168)) with
| ((env, lbs), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = eff; FStar_Absyn_Syntax.lbdef = e}) -> begin
(
# 699 "FStar.Tc.Normalize.fst"
let c = (wne tcenv (
# 699 "FStar.Tc.Normalize.fst"
let _38_1169 = config
in {code = e; environment = _38_1169.environment; stack = empty_stack; close = _38_1169.close; steps = _38_1169.steps}))
in (
# 700 "FStar.Tc.Normalize.fst"
let t = (sn tcenv (t_config t config.environment config.steps))
in (
# 701 "FStar.Tc.Normalize.fst"
let _38_1182 = (match (x) with
| FStar_Util.Inl (x) -> begin
(
# 703 "FStar.Tc.Normalize.fst"
let y = (let _119_482 = if is_rec then begin
x
end else begin
(FStar_Absyn_Util.freshen_bvd x)
end
in (FStar_Absyn_Util.bvd_to_bvar_s _119_482 t.code))
in (
# 704 "FStar.Tc.Normalize.fst"
let yexp = (FStar_Absyn_Util.bvar_to_exp y)
in (
# 705 "FStar.Tc.Normalize.fst"
let y_for_x = V ((x, (yexp, empty_env)))
in (FStar_Util.Inl (y.FStar_Absyn_Syntax.v), (extend_env' env y_for_x)))))
end
| _38_1179 -> begin
(x, env)
end)
in (match (_38_1182) with
| (y, env) -> begin
(let _119_484 = (let _119_483 = (FStar_Absyn_Syntax.mk_lb (y, eff, t.code, c.code))
in (_119_483)::lbs)
in (env, _119_484))
end))))
end)) (config.environment, [])))
in (match (_38_1185) with
| (env, lbs) -> begin
(
# 709 "FStar.Tc.Normalize.fst"
let lbs = (FStar_List.rev lbs)
in (
# 710 "FStar.Tc.Normalize.fst"
let c_body = (wne tcenv (
# 710 "FStar.Tc.Normalize.fst"
let _38_1187 = config
in {code = body; environment = env; stack = empty_stack; close = _38_1187.close; steps = _38_1187.steps}))
in (
# 711 "FStar.Tc.Normalize.fst"
let e = (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), c_body.code) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right (
# 712 "FStar.Tc.Normalize.fst"
let _38_1191 = config
in {code = e; environment = _38_1191.environment; stack = _38_1191.stack; close = _38_1191.close; steps = _38_1191.steps}) rebuild))))
end))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, l) -> begin
(
# 715 "FStar.Tc.Normalize.fst"
let c = (wne tcenv (
# 715 "FStar.Tc.Normalize.fst"
let _38_1198 = config
in {code = e; environment = _38_1198.environment; stack = _38_1198.stack; close = _38_1198.close; steps = _38_1198.steps}))
in if (is_stack_empty config) then begin
(
# 717 "FStar.Tc.Normalize.fst"
let t = (sn tcenv (t_config t config.environment config.steps))
in (let _119_486 = (
# 718 "FStar.Tc.Normalize.fst"
let _38_1202 = config
in (let _119_485 = (FStar_Absyn_Syntax.mk_Exp_ascribed (c.code, t.code, l) None e.FStar_Absyn_Syntax.pos)
in {code = _119_485; environment = _38_1202.environment; stack = _38_1202.stack; close = _38_1202.close; steps = _38_1202.steps}))
in (rebuild _119_486)))
end else begin
c
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, info)) -> begin
(
# 722 "FStar.Tc.Normalize.fst"
let c = (wne tcenv (
# 722 "FStar.Tc.Normalize.fst"
let _38_1209 = config
in {code = e; environment = _38_1209.environment; stack = _38_1209.stack; close = _38_1209.close; steps = _38_1209.steps}))
in if (is_stack_empty config) then begin
(let _119_488 = (
# 724 "FStar.Tc.Normalize.fst"
let _38_1212 = config
in (let _119_487 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((c.code, info))))
in {code = _119_487; environment = _38_1212.environment; stack = _38_1212.stack; close = _38_1212.close; steps = _38_1212.steps}))
in (rebuild _119_488))
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
let norm_sigelt : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt = (fun tcenv _38_10 -> (match (_38_10) with
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, b) -> begin
(
# 744 "FStar.Tc.Normalize.fst"
let e = (let _119_512 = (let _119_511 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None r)
in (lbs, _119_511))
in (FStar_Absyn_Syntax.mk_Exp_let _119_512 None r))
in (
# 745 "FStar.Tc.Normalize.fst"
let e = (norm_exp ((Beta)::[]) tcenv e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_let (lbs, _38_1238) -> begin
FStar_Absyn_Syntax.Sig_let ((lbs, r, l, b))
end
| _38_1242 -> begin
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
(let _119_517 = (eta_expand tcenv t)
in (FStar_All.pipe_right _119_517 FStar_Absyn_Util.compress_typ))
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
let exp_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  Prims.string = (fun tcenv e -> (let _119_540 = (norm_exp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv e)
in (FStar_Absyn_Print.exp_to_string _119_540)))

# 783 "FStar.Tc.Normalize.fst"
let typ_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun tcenv t -> (let _119_545 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv t)
in (FStar_Absyn_Print.typ_to_string _119_545)))

# 786 "FStar.Tc.Normalize.fst"
let kind_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun tcenv k -> (let _119_550 = (norm_kind ((Beta)::(SNComp)::(Unmeta)::[]) tcenv k)
in (FStar_Absyn_Print.kind_to_string _119_550)))

# 789 "FStar.Tc.Normalize.fst"
let formula_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun tcenv f -> (let _119_555 = (norm_typ ((Beta)::(SNComp)::(Unmeta)::[]) tcenv f)
in (FStar_Absyn_Print.formula_to_string _119_555)))

# 792 "FStar.Tc.Normalize.fst"
let comp_typ_norm_to_string : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  Prims.string = (fun tcenv c -> (let _119_560 = (norm_comp ((Beta)::(SNComp)::(Unmeta)::[]) tcenv c)
in (FStar_Absyn_Print.comp_typ_to_string _119_560)))

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
(let _119_575 = (let _119_574 = (let _119_573 = (let _119_572 = (let _119_571 = (let _119_570 = (let _119_569 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _119_569))
in FStar_Util.Inr (_119_570))
in (_119_571)::[])
in (FStar_Absyn_Util.subst_typ _119_572 phi))
in (FStar_Absyn_Util.mk_conj phi1 _119_573))
in (y, _119_574))
in (FStar_Absyn_Syntax.mk_Typ_refine _119_575 (Some (FStar_Absyn_Syntax.ktype)) t0.FStar_Absyn_Syntax.pos))
end
| _38_1351 -> begin
t
end))
end
| _38_1353 -> begin
t
end)))
in (aux t))))




