
open Prims
# 26 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let log = (fun s -> ())

# 30 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let rec compress_typ_aux : Prims.bool  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun pos typ -> (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (typ) -> begin
(compress_typ_aux pos typ)
end
| _27_13 -> begin
typ
end)
end
| FStar_Absyn_Syntax.Typ_delayed (_27_15, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
typ
end
| Some (t) -> begin
(let t' = (compress_typ_aux pos t)
in (let _27_23 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) when pos -> begin
(compress_typ_aux pos t)
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _27_45); FStar_Absyn_Syntax.tk = _27_42; FStar_Absyn_Syntax.pos = _27_40; FStar_Absyn_Syntax.fvs = _27_38; FStar_Absyn_Syntax.uvs = _27_36}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (t') -> begin
(let _129_8 = (FStar_Absyn_Syntax.mk_Typ_app (t', args) None typ.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left (compress_typ_aux pos) _129_8))
end
| _27_55 -> begin
typ
end)
end
| _27_57 -> begin
typ
end))

# 50 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let compress_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun typ -> (compress_typ_aux true typ))

# 51 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let compress_typ_uvars : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun typ -> (compress_typ_aux false typ))

# 53 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let rec compress_exp_aux : Prims.bool  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun meta exp -> (match (exp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (uv, _27_64) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(compress_exp_aux meta e)
end
| _27_70 -> begin
exp
end)
end
| FStar_Absyn_Syntax.Exp_delayed (_27_72, _27_74, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
exp
end
| Some (e) -> begin
(let e' = (compress_exp_aux meta e)
in (let _27_82 = (FStar_ST.op_Colon_Equals m (Some (e')))
in e'))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _27_86)) when meta -> begin
(compress_exp_aux meta e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _27_100); FStar_Absyn_Syntax.tk = _27_97; FStar_Absyn_Syntax.pos = _27_95; FStar_Absyn_Syntax.fvs = _27_93; FStar_Absyn_Syntax.uvs = _27_91}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e') -> begin
(FStar_Absyn_Syntax.mk_Exp_app (e', args) None exp.FStar_Absyn_Syntax.pos)
end
| _27_110 -> begin
exp
end)
end
| _27_112 -> begin
exp
end))

# 72 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let compress_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (compress_exp_aux true e))

# 73 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let compress_exp_uvars : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (compress_exp_aux false e))

# 75 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let rec compress_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun knd -> (match (knd.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_27_117, _27_119, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
knd
end
| Some (k) -> begin
(let k' = (compress_kind k)
in (let _27_127 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k'))
end)
end
| _27_130 -> begin
knd
end))

# 82 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let left = (fun ext benv btv -> (match ((ext benv (FStar_Util.Inl (btv)))) with
| (benv, FStar_Util.Inl (bvd)) -> begin
(benv, bvd)
end
| _27_139 -> begin
(FStar_All.failwith "impossible")
end))

# 85 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let right = (fun ext benv bvv -> (match ((ext benv (FStar_Util.Inr (bvv)))) with
| (benv, FStar_Util.Inr (bvd)) -> begin
(benv, bvd)
end
| _27_148 -> begin
(FStar_All.failwith "impossible")
end))

# 92 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

type boundvar =
(FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either

# 93 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

type boundvars =
boundvar Prims.list

# 94 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

type ('env, 'm) imap =
'env  ->  boundvars  ->  'm  ->  ('m * 'env)

# 95 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

type ('env, 'm, 'n) mapper =
('env, FStar_Absyn_Syntax.knd) imap  ->  ('env, FStar_Absyn_Syntax.typ) imap  ->  ('env, FStar_Absyn_Syntax.exp) imap  ->  'env  ->  boundvars  ->  'm  ->  ('n * 'env)

# 101 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let push_tbinder = (fun binders _27_1 -> (match (_27_1) with
| None -> begin
binders
end
| Some (a) -> begin
(FStar_Util.Inl (a))::binders
end))

# 104 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let push_vbinder = (fun binders _27_2 -> (match (_27_2) with
| None -> begin
binders
end
| Some (a) -> begin
(FStar_Util.Inr (a))::binders
end))

# 107 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let bvd_to_bvar_s = (fun bvd sort -> {FStar_Absyn_Syntax.v = bvd; FStar_Absyn_Syntax.sort = sort; FStar_Absyn_Syntax.p = bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idRange})

# 108 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let tbinder_opt = (fun aopt k -> (match (aopt) with
| None -> begin
[]
end
| Some (a) -> begin
(FStar_Util.Inl ((bvd_to_bvar_s a k)))::[]
end))

# 111 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let vbinder_opt = (fun aopt t -> (match (aopt) with
| None -> begin
[]
end
| Some (a) -> begin
(FStar_Util.Inr ((bvd_to_bvar_s a t)))::[]
end))

# 116 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

type knd_components =
(FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd Prims.list * FStar_Absyn_Syntax.typ Prims.list * FStar_Absyn_Syntax.arg Prims.list)

# 117 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

type typ_components =
(FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd Prims.list * FStar_Absyn_Syntax.typ Prims.list * FStar_Absyn_Syntax.comp Prims.list * FStar_Absyn_Syntax.arg Prims.list Prims.list)

# 118 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

type exp_components =
(FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd Prims.list * FStar_Absyn_Syntax.typ Prims.list * FStar_Absyn_Syntax.exp Prims.list * FStar_Absyn_Syntax.arg Prims.list)

# 119 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let leaf_k = (fun _27_176 -> (match (()) with
| () -> begin
([], [], [], [])
end))

# 120 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let leaf_te = (fun _27_177 -> (match (()) with
| () -> begin
([], [], [], [], [])
end))

# 122 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let rec reduce_kind = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k -> (let rec visit_kind = (fun env binders k -> (let k = (compress_kind k)
in (let _27_236 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_27_197) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
((leaf_k ()), env)
end
| FStar_Absyn_Syntax.Kind_uvar (_27_206, args) -> begin
(let _27_212 = (map_args map_typ map_exp env binders args)
in (match (_27_212) with
| (args, env) -> begin
(([], [], [], args), env)
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(let _27_219 = (map_kind env binders k)
in (match (_27_219) with
| (k, env) -> begin
(let _27_222 = (map_args map_typ map_exp env binders (Prims.snd kabr))
in (match (_27_222) with
| (args, env) -> begin
(([], (k)::[], [], args), env)
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _27_230 = (map_binders map_kind map_typ env binders bs)
in (match (_27_230) with
| (bs, binders, env) -> begin
(let _27_233 = (map_kind env binders k)
in (match (_27_233) with
| (k, env) -> begin
((bs, (k)::[], [], []), env)
end))
end))
end)
in (match (_27_236) with
| (components, env) -> begin
(combine_kind k components env)
end))))
and map_kind = (fun env binders k -> (map_kind' visit_kind map_typ map_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_kind env binders k)))
and map_args = (fun map_typ map_exp env binders arguments -> (let _27_270 = (FStar_List.fold_left (fun _27_254 _27_257 -> (match ((_27_254, _27_257)) with
| ((out, env), (arg, imp)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(let _27_262 = (map_typ env binders t)
in (match (_27_262) with
| (t, env) -> begin
(((FStar_Util.Inl (t), imp))::out, env)
end))
end
| FStar_Util.Inr (e) -> begin
(let _27_267 = (map_exp env binders e)
in (match (_27_267) with
| (e, env) -> begin
(((FStar_Util.Inr (e), imp))::out, env)
end))
end)
end)) ([], env) arguments)
in (match (_27_270) with
| (args', env) -> begin
((FStar_List.rev args'), env)
end)))
and map_binders = (fun map_kind map_typ env binders bs -> (let _27_301 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _27_280 b -> (match (_27_280) with
| (bs, binders, env) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(let _27_288 = (map_kind env binders a.FStar_Absyn_Syntax.sort)
in (match (_27_288) with
| (k, env) -> begin
(let binders = (push_tbinder binders (Some (a.FStar_Absyn_Syntax.v)))
in (((FStar_Util.Inl ((bvd_to_bvar_s a.FStar_Absyn_Syntax.v k)), imp))::bs, binders, env))
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _27_296 = (map_typ env binders x.FStar_Absyn_Syntax.sort)
in (match (_27_296) with
| (t, env) -> begin
(let binders = (push_vbinder binders (Some (x.FStar_Absyn_Syntax.v)))
in (((FStar_Util.Inr ((bvd_to_bvar_s x.FStar_Absyn_Syntax.v t)), imp))::bs, binders, env))
end))
end)
end)) ([], binders, env)))
in (match (_27_301) with
| (bs, binders, env) -> begin
((FStar_List.rev bs), binders, env)
end)))
and reduce_typ = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t -> (let rec map_comp = (fun env binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _27_324 = (map_typ env binders t)
in (match (_27_324) with
| (t, env) -> begin
(let _129_292 = (FStar_Absyn_Syntax.mk_Total t)
in (_129_292, env))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _27_329 = (map_typ env binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_27_329) with
| (t, env) -> begin
(let _27_332 = (map_args map_typ map_exp env binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_27_332) with
| (args, env) -> begin
(let _27_343 = (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.fold_map (fun env flag -> (match (flag) with
| FStar_Absyn_Syntax.DECREASES (arg) -> begin
(let _27_339 = (map_exp env binders arg)
in (match (_27_339) with
| (arg, env) -> begin
(env, FStar_Absyn_Syntax.DECREASES (arg))
end))
end
| f -> begin
(env, f)
end)) env))
in (match (_27_343) with
| (env, flags) -> begin
(let _129_295 = (FStar_Absyn_Syntax.mk_Comp (let _27_344 = ct
in {FStar_Absyn_Syntax.effect_name = _27_344.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = flags}))
in (_129_295, env))
end))
end))
end))
end))
and visit_typ = (fun env binders t -> (let _27_507 = (match ((let _129_299 = (compress_typ t)
in _129_299.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_delayed (_27_350) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(let _27_362 = (map_typ env binders t)
in (match (_27_362) with
| (_27_360, env) -> begin
((leaf_te ()), env)
end))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(let _27_369 = (map_typ env binders t)
in (match (_27_369) with
| (t, env) -> begin
(let _27_372 = (map_args map_typ map_exp env binders args)
in (match (_27_372) with
| (args, env) -> begin
(([], [], (t)::[], [], (args)::[]), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (axs, t) -> begin
(let _27_380 = (map_binders map_kind map_typ env binders axs)
in (match (_27_380) with
| (axs, binders, env) -> begin
(let _27_383 = (map_typ env binders t)
in (match (_27_383) with
| (t, env) -> begin
((axs, [], (t)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t2) -> begin
(let _27_391 = (map_binders map_kind map_typ env binders (((FStar_Util.Inr (x), None))::[]))
in (match (_27_391) with
| (bs, binders, env) -> begin
(let _27_394 = (map_typ env binders t2)
in (match (_27_394) with
| (t2, env) -> begin
((bs, [], (t2)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let _27_402 = (map_binders map_kind map_typ env binders bs)
in (match (_27_402) with
| (bs, binders, env) -> begin
(let _27_405 = (map_comp env binders c)
in (match (_27_405) with
| (c, env) -> begin
((bs, [], [], (c)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
(let _27_412 = (map_typ env binders t)
in (match (_27_412) with
| (t, env) -> begin
(let _27_415 = (map_kind env binders k)
in (match (_27_415) with
| (k, env) -> begin
(([], (k)::[], (t)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_27_417, k) -> begin
(let _27_423 = (map_kind env binders k)
in (match (_27_423) with
| (k, env) -> begin
(([], (k)::[], [], [], []), env)
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
(let _27_432 = (map_typ env binders t1)
in (match (_27_432) with
| (t1, env) -> begin
(let _27_435 = (map_typ env binders t2)
in (match (_27_435) with
| (t2, env) -> begin
(([], [], (t1)::(t2)::[], [], []), env)
end))
end))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(let _27_460 = (map_typ env binders t)
in (match (_27_460) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
(let _27_468 = (map_typ env binders t)
in (match (_27_468) with
| (t, env) -> begin
(let map_pats = (fun env pats -> (let _27_494 = (FStar_List.fold_left (fun _27_474 arg -> (match (_27_474) with
| (pats, env) -> begin
(match (arg) with
| (FStar_Util.Inl (t), _27_479) -> begin
(let _27_483 = (map_typ env binders t)
in (match (_27_483) with
| (t, env) -> begin
(((FStar_Util.Inl (t), None))::pats, env)
end))
end
| (FStar_Util.Inr (e), _27_487) -> begin
(let _27_491 = (map_exp env binders e)
in (match (_27_491) with
| (e, env) -> begin
(((FStar_Util.Inr (e), None))::pats, env)
end))
end)
end)) ([], env) pats)
in (match (_27_494) with
| (pats, env) -> begin
((FStar_List.rev pats), env)
end)))
in (let _27_504 = (FStar_List.fold_left (fun _27_497 pats -> (match (_27_497) with
| (out, env) -> begin
(let _27_501 = (map_pats env pats)
in (match (_27_501) with
| (pats, env) -> begin
((pats)::out, env)
end))
end)) ([], env) ps)
in (match (_27_504) with
| (pats, env) -> begin
(([], [], (t)::[], [], (FStar_List.rev pats)), env)
end)))
end))
end)
in (match (_27_507) with
| (components, env) -> begin
(combine_typ t components env)
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (map_typ' map_kind visit_typ map_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_typ env binders t)))
and reduce_exp = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e -> (let rec map_exps = (fun env binders el -> (let _27_545 = (FStar_List.fold_left (fun _27_538 e -> (match (_27_538) with
| (out, env) -> begin
(let _27_542 = (map_exp env binders e)
in (match (_27_542) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_27_545) with
| (el, env) -> begin
((FStar_List.rev el), env)
end)))
and map_exps_with_binders = (fun env el -> (let _27_559 = (FStar_List.fold_left (fun _27_550 _27_553 -> (match ((_27_550, _27_553)) with
| ((out, env), (b, e)) -> begin
(let _27_556 = (map_exp env b e)
in (match (_27_556) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_27_559) with
| (el, env) -> begin
((FStar_List.rev el), env)
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (map_exp' map_kind map_typ visit_exp env binders e))
and visit_exp = (fun env binders e -> (let e = (compress_exp_uvars e)
in (let _27_746 = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_27_574) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _27_578)) -> begin
(let _27_584 = (map_exp env binders e)
in (match (_27_584) with
| (e, env) -> begin
(([], [], [], (e)::[], []), env)
end))
end
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
((leaf_te ()), env)
end
| FStar_Absyn_Syntax.Exp_uvar (_27_595, t) -> begin
(let _27_601 = (map_typ env binders t)
in (match (_27_601) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(let _27_609 = (map_binders map_kind map_typ env binders bs)
in (match (_27_609) with
| (bs, binders, env) -> begin
(let _27_612 = (map_exp env binders e)
in (match (_27_612) with
| (e, env) -> begin
((bs, [], [], (e)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(let _27_619 = (map_exp env binders e)
in (match (_27_619) with
| (e, env) -> begin
(let _27_622 = (map_args map_typ map_exp env binders args)
in (match (_27_622) with
| (args, env) -> begin
(([], [], [], (e)::[], args), env)
end))
end))
end
| FStar_Absyn_Syntax.Exp_match (e1, pl) -> begin
(let rec pat_binders = (fun b p -> (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_constant (_)) -> begin
b
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(push_vbinder b (Some (x.FStar_Absyn_Syntax.v)))
end
| FStar_Absyn_Syntax.Pat_tvar (t) -> begin
(push_tbinder b (Some (t.FStar_Absyn_Syntax.v)))
end
| FStar_Absyn_Syntax.Pat_cons (_27_650, _27_652, pats) -> begin
(FStar_List.fold_left (fun b _27_660 -> (match (_27_660) with
| (p, _27_659) -> begin
(pat_binders b p)
end)) b pats)
end
| FStar_Absyn_Syntax.Pat_disj (p::_27_662) -> begin
(pat_binders b p)
end
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end))
in (let branches = (FStar_All.pipe_right pl (FStar_List.collect (fun _27_671 -> (match (_27_671) with
| (p, w, e) -> begin
(let binders = (pat_binders binders p)
in (match (w) with
| None -> begin
((binders, e))::[]
end
| Some (w) -> begin
((binders, w))::((binders, e))::[]
end))
end))))
in (let _27_679 = (map_exps_with_binders env (((binders, e1))::branches))
in (match (_27_679) with
| (el, env) -> begin
(([], [], [], el, []), env)
end))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _27_683) -> begin
(let _27_688 = (map_typ env binders t)
in (match (_27_688) with
| (t, env) -> begin
(let _27_691 = (map_exp env binders e)
in (match (_27_691) with
| (e, env) -> begin
(([], [], (t)::[], (e)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, lb::[]), e2) -> begin
(let _27_701 = (map_typ env binders lb.FStar_Absyn_Syntax.lbtyp)
in (match (_27_701) with
| (t, env) -> begin
(let binders' = (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _27_705 -> begin
binders
end)
in (let _27_709 = (map_exps_with_binders env (((binders, lb.FStar_Absyn_Syntax.lbdef))::((binders', e2))::[]))
in (match (_27_709) with
| (el, env) -> begin
(([], [], (t)::[], el, []), env)
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((true, bvdt_tl), e) -> begin
(let tl = (FStar_List.map (fun lb -> lb.FStar_Absyn_Syntax.lbtyp) bvdt_tl)
in (let el = (FStar_List.map (fun lb -> lb.FStar_Absyn_Syntax.lbdef) bvdt_tl)
in (let _27_729 = (FStar_All.pipe_right tl (FStar_List.fold_left (fun _27_722 t -> (match (_27_722) with
| (tl, env) -> begin
(let _27_726 = (map_typ env binders t)
in (match (_27_726) with
| (t, env) -> begin
((t)::tl, env)
end))
end)) ([], env)))
in (match (_27_729) with
| (tl, env) -> begin
(let tl = (FStar_List.rev tl)
in (let binders = (FStar_List.fold_left (fun binders lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _27_736 -> begin
binders
end)) binders bvdt_tl)
in (let _27_740 = (map_exps env binders (FStar_List.append el ((e)::[])))
in (match (_27_740) with
| (el, env) -> begin
(([], [], tl, el, []), env)
end))))
end))))
end
| FStar_Absyn_Syntax.Exp_let (_27_742) -> begin
(FStar_All.failwith "impossible")
end)
in (match (_27_746) with
| (components, env) -> begin
(combine_exp e components env)
end))))
in (map_exp env binders e)))

# 372 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let combine_kind = (fun k kc env -> (let k' = (match ((k.FStar_Absyn_Syntax.n, kc)) with
| ((FStar_Absyn_Syntax.Kind_lam (_), _)) | ((FStar_Absyn_Syntax.Kind_type, _)) | ((FStar_Absyn_Syntax.Kind_effect, _)) | ((FStar_Absyn_Syntax.Kind_unknown, _)) -> begin
(fun p -> (FStar_Util.return_all k))
end
| (FStar_Absyn_Syntax.Kind_uvar (u, _27_771), (_27_775, _27_777, _27_779, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_uvar (u, args))
end
| (FStar_Absyn_Syntax.Kind_abbrev (kabr, _27_785), (_27_789, k::[], _27_793, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_abbrev (((Prims.fst kabr), args), k))
end
| (FStar_Absyn_Syntax.Kind_arrow (_27_798, _27_800), (bs, k'::[], _27_807, _27_809)) -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow (bs, k'))
end
| _27_813 -> begin
(FStar_All.failwith "impossible")
end)
in (let _129_388 = (k' k.FStar_Absyn_Syntax.pos)
in (_129_388, env))))

# 384 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let combine_typ = (fun t tc env -> (let t = (compress_typ t)
in (let w = (fun f -> (f None t.FStar_Absyn_Syntax.pos))
in (let t' = (match ((t.FStar_Absyn_Syntax.n, tc)) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((FStar_Absyn_Syntax.Typ_const (_), _)) -> begin
t
end
| (FStar_Absyn_Syntax.Typ_lam (_27_838), (bs, _27_842, t::[], _27_846, _27_848)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
end
| (FStar_Absyn_Syntax.Typ_app (_27_852), (_27_855, _27_857, t::[], _27_861, args::[])) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_app (t, args)))
end
| (FStar_Absyn_Syntax.Typ_refine (_27_867), ((FStar_Util.Inr (x), _27_872)::[], _27_876, t::[], _27_880, _27_882)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_refine (x, t)))
end
| (FStar_Absyn_Syntax.Typ_fun (_27_886), (bs, _27_890, _27_892, c::[], _27_896)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_fun (bs, c)))
end
| (FStar_Absyn_Syntax.Typ_uvar (x, _27_901), (_27_905, k::[], _27_909, _27_911, _27_913)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_uvar' (x, k)))
end
| (FStar_Absyn_Syntax.Typ_ascribed (_27_917), (_27_920, k::[], t::[], _27_926, _27_928)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_ascribed' (t, k)))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_27_932, l)), (_27_938, _27_940, t'::[], _27_944, _27_946)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_named ((t', l)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_27_950)), (_27_954, _27_956, t::[], _27_960, args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern ((t, args)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_27_965, l, r, p)), (_27_973, _27_975, t::[], _27_979, _27_981)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_27_985, b, r)), (_27_992, _27_994, t::[], _27_998, _27_1000)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_27_1004, _27_1006, _27_1008)), (_27_1013, _27_1015, t1::t2::[], _27_1020, _27_1022)) -> begin
(let _129_429 = (let _129_428 = (let _129_427 = (let _129_426 = (FStar_Util.mk_ref false)
in (t1, t2, _129_426))
in FStar_Absyn_Syntax.Meta_slack_formula (_129_427))
in (FStar_Absyn_Syntax.mk_Typ_meta' _129_428))
in (FStar_All.pipe_left w _129_429))
end
| _27_1026 -> begin
(FStar_All.failwith "impossible")
end)
in (t', env)))))

# 405 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let combine_exp = (fun e ec env -> (let e = (compress_exp e)
in (let w = (fun f -> (f None e.FStar_Absyn_Syntax.pos))
in (let e' = (match ((e.FStar_Absyn_Syntax.n, ec)) with
| ((FStar_Absyn_Syntax.Exp_bvar (_), _)) | ((FStar_Absyn_Syntax.Exp_fvar (_), _)) | ((FStar_Absyn_Syntax.Exp_constant (_), _)) -> begin
e
end
| (FStar_Absyn_Syntax.Exp_uvar (uv, _27_1054), (_27_1058, _27_1060, t::[], _27_1064, _27_1066)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t)))
end
| (FStar_Absyn_Syntax.Exp_abs (_27_1070), (bs, _27_1074, _27_1076, e::[], _27_1080)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_abs (bs, e)))
end
| (FStar_Absyn_Syntax.Exp_app (_27_1084), (_27_1087, _27_1089, _27_1091, e::[], args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_app (e, args)))
end
| (FStar_Absyn_Syntax.Exp_ascribed (_27_1098, _27_1100, l), (_27_1105, _27_1107, t::[], e::[], _27_1113)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, l)))
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_27_1117, tag)), (_27_1123, _27_1125, _27_1127, e::[], _27_1131)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_meta' (FStar_Absyn_Syntax.Meta_desugared ((e, tag)))))
end
| (FStar_Absyn_Syntax.Exp_match (_27_1135, eqns), (_27_1140, [], [], e1::el, _27_1147)) -> begin
(let rec mk_eqns = (fun eqns el -> (match ((eqns, el)) with
| ((p, None, _27_1157)::eqns', e::el') -> begin
(let _129_459 = (mk_eqns eqns' el')
in ((p, None, e))::_129_459)
end
| ((p, Some (_27_1167), _27_1170)::eqns', w::e::el') -> begin
(let _129_460 = (mk_eqns eqns' el')
in ((p, Some (w), e))::_129_460)
end
| ([], []) -> begin
[]
end
| _27_1183 -> begin
(FStar_All.failwith "impossible")
end))
in (let _129_465 = (let _129_464 = (let _129_463 = (mk_eqns eqns el)
in (e1, _129_463))
in (FStar_Absyn_Syntax.mk_Exp_match _129_464))
in (FStar_All.pipe_left w _129_465)))
end
| (FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), _27_1188), (_27_1192, _27_1194, tl, el, _27_1198)) -> begin
(match ((FStar_Util.first_N (FStar_List.length lbs) el)) with
| (el, e'::[]) -> begin
(let lbs' = (FStar_List.map3 (fun lb t e -> (let _27_1208 = lb
in {FStar_Absyn_Syntax.lbname = _27_1208.FStar_Absyn_Syntax.lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _27_1208.FStar_Absyn_Syntax.lbeff; FStar_Absyn_Syntax.lbdef = e})) lbs tl el)
in (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs'), e'))))
end
| _27_1212 -> begin
(FStar_All.failwith "impossible")
end)
end
| _27_1214 -> begin
(FStar_All.failwith "impossible")
end)
in (e', env)))))

# 435 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\visit.fs"

let collect_from_typ = (fun f env t -> (let _129_589 = (reduce_typ (fun _27_1260 _27_1262 _27_1264 env _27_1267 k -> (k, env)) (fun _27_1242 vt _27_1245 env bvs t -> (let env = (f env t)
in (match ((let _129_546 = (compress_typ t)
in _129_546.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(t, env)
end
| _27_1259 -> begin
(vt env bvs t)
end))) (fun _27_1232 _27_1234 _27_1236 env _27_1239 e -> (e, env)) (fun k _27_1229 env -> (k, env)) (fun t _27_1225 env -> (t, env)) (fun e _27_1221 env -> (e, env)) env [] t)
in (FStar_All.pipe_left Prims.snd _129_589)))




