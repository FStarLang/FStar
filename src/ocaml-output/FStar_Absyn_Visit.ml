
open Prims
# 26 "FStar.Absyn.Visit.fst"
let log = (fun s -> ())

# 30 "FStar.Absyn.Visit.fst"
let rec compress_typ_aux : Prims.bool  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun pos typ -> (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (typ) -> begin
(compress_typ_aux pos typ)
end
| _26_13 -> begin
typ
end)
end
| FStar_Absyn_Syntax.Typ_delayed (_26_15, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
typ
end
| Some (t) -> begin
(
# 40 "FStar.Absyn.Visit.fst"
let t' = (compress_typ_aux pos t)
in (
# 40 "FStar.Absyn.Visit.fst"
let _26_23 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) when pos -> begin
(compress_typ_aux pos t)
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _26_45); FStar_Absyn_Syntax.tk = _26_42; FStar_Absyn_Syntax.pos = _26_40; FStar_Absyn_Syntax.fvs = _26_38; FStar_Absyn_Syntax.uvs = _26_36}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (t') -> begin
(let _110_8 = (FStar_Absyn_Syntax.mk_Typ_app (t', args) None typ.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left (compress_typ_aux pos) _110_8))
end
| _26_55 -> begin
typ
end)
end
| _26_57 -> begin
typ
end))

# 50 "FStar.Absyn.Visit.fst"
let compress_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun typ -> (compress_typ_aux true typ))

# 51 "FStar.Absyn.Visit.fst"
let compress_typ_uvars : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun typ -> (compress_typ_aux false typ))

# 53 "FStar.Absyn.Visit.fst"
let rec compress_exp_aux : Prims.bool  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun meta exp -> (match (exp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (uv, _26_64) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(compress_exp_aux meta e)
end
| _26_70 -> begin
exp
end)
end
| FStar_Absyn_Syntax.Exp_delayed (_26_72, _26_74, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
exp
end
| Some (e) -> begin
(
# 63 "FStar.Absyn.Visit.fst"
let e' = (compress_exp_aux meta e)
in (
# 63 "FStar.Absyn.Visit.fst"
let _26_82 = (FStar_ST.op_Colon_Equals m (Some (e')))
in e'))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _26_86)) when meta -> begin
(compress_exp_aux meta e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _26_100); FStar_Absyn_Syntax.tk = _26_97; FStar_Absyn_Syntax.pos = _26_95; FStar_Absyn_Syntax.fvs = _26_93; FStar_Absyn_Syntax.uvs = _26_91}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e') -> begin
(FStar_Absyn_Syntax.mk_Exp_app (e', args) None exp.FStar_Absyn_Syntax.pos)
end
| _26_110 -> begin
exp
end)
end
| _26_112 -> begin
exp
end))

# 72 "FStar.Absyn.Visit.fst"
let compress_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (compress_exp_aux true e))

# 73 "FStar.Absyn.Visit.fst"
let compress_exp_uvars : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (compress_exp_aux false e))

# 75 "FStar.Absyn.Visit.fst"
let rec compress_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun knd -> (match (knd.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_26_117, _26_119, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
knd
end
| Some (k) -> begin
(
# 79 "FStar.Absyn.Visit.fst"
let k' = (compress_kind k)
in (
# 79 "FStar.Absyn.Visit.fst"
let _26_127 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k'))
end)
end
| _26_130 -> begin
knd
end))

# 82 "FStar.Absyn.Visit.fst"
let left = (fun ext benv btv -> (match ((ext benv (FStar_Util.Inl (btv)))) with
| (benv, FStar_Util.Inl (bvd)) -> begin
(benv, bvd)
end
| _26_139 -> begin
(FStar_All.failwith "impossible")
end))

# 85 "FStar.Absyn.Visit.fst"
let right = (fun ext benv bvv -> (match ((ext benv (FStar_Util.Inr (bvv)))) with
| (benv, FStar_Util.Inr (bvd)) -> begin
(benv, bvd)
end
| _26_148 -> begin
(FStar_All.failwith "impossible")
end))

# 92 "FStar.Absyn.Visit.fst"
type boundvar =
(FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either

# 93 "FStar.Absyn.Visit.fst"
type boundvars =
boundvar Prims.list

# 94 "FStar.Absyn.Visit.fst"
type ('env, 'm) imap =
'env  ->  boundvars  ->  'm  ->  ('m * 'env)

# 95 "FStar.Absyn.Visit.fst"
type ('env, 'm, 'n) mapper =
('env, FStar_Absyn_Syntax.knd) imap  ->  ('env, FStar_Absyn_Syntax.typ) imap  ->  ('env, FStar_Absyn_Syntax.exp) imap  ->  'env  ->  boundvars  ->  'm  ->  ('n * 'env)

# 101 "FStar.Absyn.Visit.fst"
let push_tbinder = (fun binders _26_1 -> (match (_26_1) with
| None -> begin
binders
end
| Some (a) -> begin
(FStar_Util.Inl (a))::binders
end))

# 104 "FStar.Absyn.Visit.fst"
let push_vbinder = (fun binders _26_2 -> (match (_26_2) with
| None -> begin
binders
end
| Some (a) -> begin
(FStar_Util.Inr (a))::binders
end))

# 107 "FStar.Absyn.Visit.fst"
let bvd_to_bvar_s = (fun bvd sort -> {FStar_Absyn_Syntax.v = bvd; FStar_Absyn_Syntax.sort = sort; FStar_Absyn_Syntax.p = bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idRange})

# 108 "FStar.Absyn.Visit.fst"
let tbinder_opt = (fun aopt k -> (match (aopt) with
| None -> begin
[]
end
| Some (a) -> begin
(FStar_Util.Inl ((bvd_to_bvar_s a k)))::[]
end))

# 111 "FStar.Absyn.Visit.fst"
let vbinder_opt = (fun aopt t -> (match (aopt) with
| None -> begin
[]
end
| Some (a) -> begin
(FStar_Util.Inr ((bvd_to_bvar_s a t)))::[]
end))

# 116 "FStar.Absyn.Visit.fst"
type knd_components =
(FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd Prims.list * FStar_Absyn_Syntax.typ Prims.list * FStar_Absyn_Syntax.arg Prims.list)

# 117 "FStar.Absyn.Visit.fst"
type typ_components =
(FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd Prims.list * FStar_Absyn_Syntax.typ Prims.list * FStar_Absyn_Syntax.comp Prims.list * FStar_Absyn_Syntax.arg Prims.list Prims.list)

# 118 "FStar.Absyn.Visit.fst"
type exp_components =
(FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd Prims.list * FStar_Absyn_Syntax.typ Prims.list * FStar_Absyn_Syntax.exp Prims.list * FStar_Absyn_Syntax.arg Prims.list)

# 119 "FStar.Absyn.Visit.fst"
let leaf_k = (fun _26_176 -> (match (()) with
| () -> begin
([], [], [], [])
end))

# 120 "FStar.Absyn.Visit.fst"
let leaf_te = (fun _26_177 -> (match (()) with
| () -> begin
([], [], [], [], [])
end))

# 122 "FStar.Absyn.Visit.fst"
let rec reduce_kind = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k -> (
# 130 "FStar.Absyn.Visit.fst"
let rec visit_kind = (fun env binders k -> (
# 131 "FStar.Absyn.Visit.fst"
let k = (compress_kind k)
in (
# 132 "FStar.Absyn.Visit.fst"
let _26_236 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_26_197) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
((leaf_k ()), env)
end
| FStar_Absyn_Syntax.Kind_uvar (_26_206, args) -> begin
(
# 141 "FStar.Absyn.Visit.fst"
let _26_212 = (map_args map_typ map_exp env binders args)
in (match (_26_212) with
| (args, env) -> begin
(([], [], [], args), env)
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(
# 144 "FStar.Absyn.Visit.fst"
let _26_219 = (map_kind env binders k)
in (match (_26_219) with
| (k, env) -> begin
(
# 145 "FStar.Absyn.Visit.fst"
let _26_222 = (map_args map_typ map_exp env binders (Prims.snd kabr))
in (match (_26_222) with
| (args, env) -> begin
(([], (k)::[], [], args), env)
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(
# 148 "FStar.Absyn.Visit.fst"
let _26_230 = (map_binders map_kind map_typ env binders bs)
in (match (_26_230) with
| (bs, binders, env) -> begin
(
# 149 "FStar.Absyn.Visit.fst"
let _26_233 = (map_kind env binders k)
in (match (_26_233) with
| (k, env) -> begin
((bs, (k)::[], [], []), env)
end))
end))
end)
in (match (_26_236) with
| (components, env) -> begin
(combine_kind k components env)
end))))
and map_kind = (fun env binders k -> (map_kind' visit_kind map_typ map_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_kind env binders k)))
and map_args = (fun map_typ map_exp env binders arguments -> (
# 160 "FStar.Absyn.Visit.fst"
let _26_270 = (FStar_List.fold_left (fun _26_254 _26_257 -> (match ((_26_254, _26_257)) with
| ((out, env), (arg, imp)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(
# 163 "FStar.Absyn.Visit.fst"
let _26_262 = (map_typ env binders t)
in (match (_26_262) with
| (t, env) -> begin
(((FStar_Util.Inl (t), imp))::out, env)
end))
end
| FStar_Util.Inr (e) -> begin
(
# 166 "FStar.Absyn.Visit.fst"
let _26_267 = (map_exp env binders e)
in (match (_26_267) with
| (e, env) -> begin
(((FStar_Util.Inr (e), imp))::out, env)
end))
end)
end)) ([], env) arguments)
in (match (_26_270) with
| (args', env) -> begin
((FStar_List.rev args'), env)
end)))
and map_binders = (fun map_kind map_typ env binders bs -> (
# 171 "FStar.Absyn.Visit.fst"
let _26_301 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _26_280 b -> (match (_26_280) with
| (bs, binders, env) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(
# 173 "FStar.Absyn.Visit.fst"
let _26_288 = (map_kind env binders a.FStar_Absyn_Syntax.sort)
in (match (_26_288) with
| (k, env) -> begin
(
# 174 "FStar.Absyn.Visit.fst"
let binders = (push_tbinder binders (Some (a.FStar_Absyn_Syntax.v)))
in (((FStar_Util.Inl ((bvd_to_bvar_s a.FStar_Absyn_Syntax.v k)), imp))::bs, binders, env))
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(
# 178 "FStar.Absyn.Visit.fst"
let _26_296 = (map_typ env binders x.FStar_Absyn_Syntax.sort)
in (match (_26_296) with
| (t, env) -> begin
(
# 179 "FStar.Absyn.Visit.fst"
let binders = (push_vbinder binders (Some (x.FStar_Absyn_Syntax.v)))
in (((FStar_Util.Inr ((bvd_to_bvar_s x.FStar_Absyn_Syntax.v t)), imp))::bs, binders, env))
end))
end)
end)) ([], binders, env)))
in (match (_26_301) with
| (bs, binders, env) -> begin
((FStar_List.rev bs), binders, env)
end)))
and reduce_typ = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t -> (
# 192 "FStar.Absyn.Visit.fst"
let rec map_comp = (fun env binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(
# 195 "FStar.Absyn.Visit.fst"
let _26_324 = (map_typ env binders t)
in (match (_26_324) with
| (t, env) -> begin
(let _110_292 = (FStar_Absyn_Syntax.mk_Total t)
in (_110_292, env))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(
# 198 "FStar.Absyn.Visit.fst"
let _26_329 = (map_typ env binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_26_329) with
| (t, env) -> begin
(
# 199 "FStar.Absyn.Visit.fst"
let _26_332 = (map_args map_typ map_exp env binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_26_332) with
| (args, env) -> begin
(
# 200 "FStar.Absyn.Visit.fst"
let _26_343 = (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.fold_map (fun env flag -> (match (flag) with
| FStar_Absyn_Syntax.DECREASES (arg) -> begin
(
# 201 "FStar.Absyn.Visit.fst"
let _26_339 = (map_exp env binders arg)
in (match (_26_339) with
| (arg, env) -> begin
(env, FStar_Absyn_Syntax.DECREASES (arg))
end))
end
| f -> begin
(env, f)
end)) env))
in (match (_26_343) with
| (env, flags) -> begin
(let _110_295 = (FStar_Absyn_Syntax.mk_Comp (
# 203 "FStar.Absyn.Visit.fst"
let _26_344 = ct
in {FStar_Absyn_Syntax.effect_name = _26_344.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = flags}))
in (_110_295, env))
end))
end))
end))
end))
and visit_typ = (fun env binders t -> (
# 206 "FStar.Absyn.Visit.fst"
let _26_507 = (match ((let _110_299 = (compress_typ t)
in _110_299.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_delayed (_26_350) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(
# 211 "FStar.Absyn.Visit.fst"
let _26_362 = (map_typ env binders t)
in (match (_26_362) with
| (_26_360, env) -> begin
((leaf_te ()), env)
end))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(
# 215 "FStar.Absyn.Visit.fst"
let _26_369 = (map_typ env binders t)
in (match (_26_369) with
| (t, env) -> begin
(
# 216 "FStar.Absyn.Visit.fst"
let _26_372 = (map_args map_typ map_exp env binders args)
in (match (_26_372) with
| (args, env) -> begin
(([], [], (t)::[], [], (args)::[]), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (axs, t) -> begin
(
# 220 "FStar.Absyn.Visit.fst"
let _26_380 = (map_binders map_kind map_typ env binders axs)
in (match (_26_380) with
| (axs, binders, env) -> begin
(
# 221 "FStar.Absyn.Visit.fst"
let _26_383 = (map_typ env binders t)
in (match (_26_383) with
| (t, env) -> begin
((axs, [], (t)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t2) -> begin
(
# 225 "FStar.Absyn.Visit.fst"
let _26_391 = (map_binders map_kind map_typ env binders (((FStar_Util.Inr (x), None))::[]))
in (match (_26_391) with
| (bs, binders, env) -> begin
(
# 226 "FStar.Absyn.Visit.fst"
let _26_394 = (map_typ env binders t2)
in (match (_26_394) with
| (t2, env) -> begin
((bs, [], (t2)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(
# 230 "FStar.Absyn.Visit.fst"
let _26_402 = (map_binders map_kind map_typ env binders bs)
in (match (_26_402) with
| (bs, binders, env) -> begin
(
# 231 "FStar.Absyn.Visit.fst"
let _26_405 = (map_comp env binders c)
in (match (_26_405) with
| (c, env) -> begin
((bs, [], [], (c)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
(
# 235 "FStar.Absyn.Visit.fst"
let _26_412 = (map_typ env binders t)
in (match (_26_412) with
| (t, env) -> begin
(
# 236 "FStar.Absyn.Visit.fst"
let _26_415 = (map_kind env binders k)
in (match (_26_415) with
| (k, env) -> begin
(([], (k)::[], (t)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_26_417, k) -> begin
(
# 240 "FStar.Absyn.Visit.fst"
let _26_423 = (map_kind env binders k)
in (match (_26_423) with
| (k, env) -> begin
(([], (k)::[], [], [], []), env)
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
(
# 244 "FStar.Absyn.Visit.fst"
let _26_432 = (map_typ env binders t1)
in (match (_26_432) with
| (t1, env) -> begin
(
# 245 "FStar.Absyn.Visit.fst"
let _26_435 = (map_typ env binders t2)
in (match (_26_435) with
| (t2, env) -> begin
(([], [], (t1)::(t2)::[], [], []), env)
end))
end))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(
# 251 "FStar.Absyn.Visit.fst"
let _26_460 = (map_typ env binders t)
in (match (_26_460) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
(
# 255 "FStar.Absyn.Visit.fst"
let _26_468 = (map_typ env binders t)
in (match (_26_468) with
| (t, env) -> begin
(
# 256 "FStar.Absyn.Visit.fst"
let map_pats = (fun env pats -> (
# 257 "FStar.Absyn.Visit.fst"
let _26_494 = (FStar_List.fold_left (fun _26_474 arg -> (match (_26_474) with
| (pats, env) -> begin
(match (arg) with
| (FStar_Util.Inl (t), _26_479) -> begin
(
# 258 "FStar.Absyn.Visit.fst"
let _26_483 = (map_typ env binders t)
in (match (_26_483) with
| (t, env) -> begin
(((FStar_Util.Inl (t), None))::pats, env)
end))
end
| (FStar_Util.Inr (e), _26_487) -> begin
(
# 259 "FStar.Absyn.Visit.fst"
let _26_491 = (map_exp env binders e)
in (match (_26_491) with
| (e, env) -> begin
(((FStar_Util.Inr (e), None))::pats, env)
end))
end)
end)) ([], env) pats)
in (match (_26_494) with
| (pats, env) -> begin
((FStar_List.rev pats), env)
end)))
in (
# 261 "FStar.Absyn.Visit.fst"
let _26_504 = (FStar_List.fold_left (fun _26_497 pats -> (match (_26_497) with
| (out, env) -> begin
(
# 261 "FStar.Absyn.Visit.fst"
let _26_501 = (map_pats env pats)
in (match (_26_501) with
| (pats, env) -> begin
((pats)::out, env)
end))
end)) ([], env) ps)
in (match (_26_504) with
| (pats, env) -> begin
(([], [], (t)::[], [], (FStar_List.rev pats)), env)
end)))
end))
end)
in (match (_26_507) with
| (components, env) -> begin
(combine_typ t components env)
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (map_typ' map_kind visit_typ map_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_typ env binders t)))
and reduce_exp = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e -> (
# 280 "FStar.Absyn.Visit.fst"
let rec map_exps = (fun env binders el -> (
# 281 "FStar.Absyn.Visit.fst"
let _26_545 = (FStar_List.fold_left (fun _26_538 e -> (match (_26_538) with
| (out, env) -> begin
(
# 282 "FStar.Absyn.Visit.fst"
let _26_542 = (map_exp env binders e)
in (match (_26_542) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_26_545) with
| (el, env) -> begin
((FStar_List.rev el), env)
end)))
and map_exps_with_binders = (fun env el -> (
# 286 "FStar.Absyn.Visit.fst"
let _26_559 = (FStar_List.fold_left (fun _26_550 _26_553 -> (match ((_26_550, _26_553)) with
| ((out, env), (b, e)) -> begin
(
# 287 "FStar.Absyn.Visit.fst"
let _26_556 = (map_exp env b e)
in (match (_26_556) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_26_559) with
| (el, env) -> begin
((FStar_List.rev el), env)
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (map_exp' map_kind map_typ visit_exp env binders e))
and visit_exp = (fun env binders e -> (
# 294 "FStar.Absyn.Visit.fst"
let e = (compress_exp_uvars e)
in (
# 295 "FStar.Absyn.Visit.fst"
let _26_746 = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_26_574) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _26_578)) -> begin
(
# 299 "FStar.Absyn.Visit.fst"
let _26_584 = (map_exp env binders e)
in (match (_26_584) with
| (e, env) -> begin
(([], [], [], (e)::[], []), env)
end))
end
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
((leaf_te ()), env)
end
| FStar_Absyn_Syntax.Exp_uvar (_26_595, t) -> begin
(
# 308 "FStar.Absyn.Visit.fst"
let _26_601 = (map_typ env binders t)
in (match (_26_601) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(
# 312 "FStar.Absyn.Visit.fst"
let _26_609 = (map_binders map_kind map_typ env binders bs)
in (match (_26_609) with
| (bs, binders, env) -> begin
(
# 313 "FStar.Absyn.Visit.fst"
let _26_612 = (map_exp env binders e)
in (match (_26_612) with
| (e, env) -> begin
((bs, [], [], (e)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(
# 317 "FStar.Absyn.Visit.fst"
let _26_619 = (map_exp env binders e)
in (match (_26_619) with
| (e, env) -> begin
(
# 318 "FStar.Absyn.Visit.fst"
let _26_622 = (map_args map_typ map_exp env binders args)
in (match (_26_622) with
| (args, env) -> begin
(([], [], [], (e)::[], args), env)
end))
end))
end
| FStar_Absyn_Syntax.Exp_match (e1, pl) -> begin
(
# 322 "FStar.Absyn.Visit.fst"
let rec pat_binders = (fun b p -> (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_constant (_)) -> begin
b
end
| FStar_Absyn_Syntax.Pat_var (x) -> begin
(push_vbinder b (Some (x.FStar_Absyn_Syntax.v)))
end
| FStar_Absyn_Syntax.Pat_tvar (t) -> begin
(push_tbinder b (Some (t.FStar_Absyn_Syntax.v)))
end
| FStar_Absyn_Syntax.Pat_cons (_26_650, _26_652, pats) -> begin
(FStar_List.fold_left (fun b _26_660 -> (match (_26_660) with
| (p, _26_659) -> begin
(pat_binders b p)
end)) b pats)
end
| FStar_Absyn_Syntax.Pat_disj (p::_26_662) -> begin
(pat_binders b p)
end
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end))
in (
# 333 "FStar.Absyn.Visit.fst"
let branches = (FStar_All.pipe_right pl (FStar_List.collect (fun _26_671 -> (match (_26_671) with
| (p, w, e) -> begin
(
# 334 "FStar.Absyn.Visit.fst"
let binders = (pat_binders binders p)
in (match (w) with
| None -> begin
((binders, e))::[]
end
| Some (w) -> begin
((binders, w))::((binders, e))::[]
end))
end))))
in (
# 338 "FStar.Absyn.Visit.fst"
let _26_679 = (map_exps_with_binders env (((binders, e1))::branches))
in (match (_26_679) with
| (el, env) -> begin
(([], [], [], el, []), env)
end))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _26_683) -> begin
(
# 342 "FStar.Absyn.Visit.fst"
let _26_688 = (map_typ env binders t)
in (match (_26_688) with
| (t, env) -> begin
(
# 343 "FStar.Absyn.Visit.fst"
let _26_691 = (map_exp env binders e)
in (match (_26_691) with
| (e, env) -> begin
(([], [], (t)::[], (e)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, lb::[]), e2) -> begin
(
# 347 "FStar.Absyn.Visit.fst"
let _26_701 = (map_typ env binders lb.FStar_Absyn_Syntax.lbtyp)
in (match (_26_701) with
| (t, env) -> begin
(
# 348 "FStar.Absyn.Visit.fst"
let binders' = (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _26_705 -> begin
binders
end)
in (
# 351 "FStar.Absyn.Visit.fst"
let _26_709 = (map_exps_with_binders env (((binders, lb.FStar_Absyn_Syntax.lbdef))::((binders', e2))::[]))
in (match (_26_709) with
| (el, env) -> begin
(([], [], (t)::[], el, []), env)
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((true, bvdt_tl), e) -> begin
(
# 355 "FStar.Absyn.Visit.fst"
let tl = (FStar_List.map (fun lb -> lb.FStar_Absyn_Syntax.lbtyp) bvdt_tl)
in (
# 356 "FStar.Absyn.Visit.fst"
let el = (FStar_List.map (fun lb -> lb.FStar_Absyn_Syntax.lbdef) bvdt_tl)
in (
# 357 "FStar.Absyn.Visit.fst"
let _26_729 = (FStar_All.pipe_right tl (FStar_List.fold_left (fun _26_722 t -> (match (_26_722) with
| (tl, env) -> begin
(
# 358 "FStar.Absyn.Visit.fst"
let _26_726 = (map_typ env binders t)
in (match (_26_726) with
| (t, env) -> begin
((t)::tl, env)
end))
end)) ([], env)))
in (match (_26_729) with
| (tl, env) -> begin
(
# 360 "FStar.Absyn.Visit.fst"
let tl = (FStar_List.rev tl)
in (
# 361 "FStar.Absyn.Visit.fst"
let binders = (FStar_List.fold_left (fun binders lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _26_736 -> begin
binders
end)) binders bvdt_tl)
in (
# 364 "FStar.Absyn.Visit.fst"
let _26_740 = (map_exps env binders (FStar_List.append el ((e)::[])))
in (match (_26_740) with
| (el, env) -> begin
(([], [], tl, el, []), env)
end))))
end))))
end
| FStar_Absyn_Syntax.Exp_let (_26_742) -> begin
(FStar_All.failwith "impossible")
end)
in (match (_26_746) with
| (components, env) -> begin
(combine_exp e components env)
end))))
in (map_exp env binders e)))

# 372 "FStar.Absyn.Visit.fst"
let combine_kind = (fun k kc env -> (
# 373 "FStar.Absyn.Visit.fst"
let k' = (match ((k.FStar_Absyn_Syntax.n, kc)) with
| ((FStar_Absyn_Syntax.Kind_lam (_), _)) | ((FStar_Absyn_Syntax.Kind_type, _)) | ((FStar_Absyn_Syntax.Kind_effect, _)) | ((FStar_Absyn_Syntax.Kind_unknown, _)) -> begin
(fun p -> (FStar_Util.return_all k))
end
| (FStar_Absyn_Syntax.Kind_uvar (u, _26_771), (_26_775, _26_777, _26_779, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_uvar (u, args))
end
| (FStar_Absyn_Syntax.Kind_abbrev (kabr, _26_785), (_26_789, k::[], _26_793, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_abbrev (((Prims.fst kabr), args), k))
end
| (FStar_Absyn_Syntax.Kind_arrow (_26_798, _26_800), (bs, k'::[], _26_807, _26_809)) -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow (bs, k'))
end
| _26_813 -> begin
(FStar_All.failwith "impossible")
end)
in (let _110_388 = (k' k.FStar_Absyn_Syntax.pos)
in (_110_388, env))))

# 384 "FStar.Absyn.Visit.fst"
let combine_typ = (fun t tc env -> (
# 385 "FStar.Absyn.Visit.fst"
let t = (compress_typ t)
in (
# 386 "FStar.Absyn.Visit.fst"
let w = (fun f -> (f None t.FStar_Absyn_Syntax.pos))
in (
# 387 "FStar.Absyn.Visit.fst"
let t' = (match ((t.FStar_Absyn_Syntax.n, tc)) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((FStar_Absyn_Syntax.Typ_const (_), _)) -> begin
t
end
| (FStar_Absyn_Syntax.Typ_lam (_26_838), (bs, _26_842, t::[], _26_846, _26_848)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
end
| (FStar_Absyn_Syntax.Typ_app (_26_852), (_26_855, _26_857, t::[], _26_861, args::[])) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_app (t, args)))
end
| (FStar_Absyn_Syntax.Typ_refine (_26_867), ((FStar_Util.Inr (x), _26_872)::[], _26_876, t::[], _26_880, _26_882)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_refine (x, t)))
end
| (FStar_Absyn_Syntax.Typ_fun (_26_886), (bs, _26_890, _26_892, c::[], _26_896)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_fun (bs, c)))
end
| (FStar_Absyn_Syntax.Typ_uvar (x, _26_901), (_26_905, k::[], _26_909, _26_911, _26_913)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_uvar' (x, k)))
end
| (FStar_Absyn_Syntax.Typ_ascribed (_26_917), (_26_920, k::[], t::[], _26_926, _26_928)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_ascribed' (t, k)))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_26_932, l)), (_26_938, _26_940, t'::[], _26_944, _26_946)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_named ((t', l)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_26_950)), (_26_954, _26_956, t::[], _26_960, args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern ((t, args)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_26_965, l, r, p)), (_26_973, _26_975, t::[], _26_979, _26_981)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_26_985, b, r)), (_26_992, _26_994, t::[], _26_998, _26_1000)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_26_1004, _26_1006, _26_1008)), (_26_1013, _26_1015, t1::t2::[], _26_1020, _26_1022)) -> begin
(let _110_429 = (let _110_428 = (let _110_427 = (let _110_426 = (FStar_Util.mk_ref false)
in (t1, t2, _110_426))
in FStar_Absyn_Syntax.Meta_slack_formula (_110_427))
in (FStar_Absyn_Syntax.mk_Typ_meta' _110_428))
in (FStar_All.pipe_left w _110_429))
end
| _26_1026 -> begin
(FStar_All.failwith "impossible")
end)
in (t', env)))))

# 405 "FStar.Absyn.Visit.fst"
let combine_exp = (fun e ec env -> (
# 406 "FStar.Absyn.Visit.fst"
let e = (compress_exp e)
in (
# 407 "FStar.Absyn.Visit.fst"
let w = (fun f -> (f None e.FStar_Absyn_Syntax.pos))
in (
# 408 "FStar.Absyn.Visit.fst"
let e' = (match ((e.FStar_Absyn_Syntax.n, ec)) with
| ((FStar_Absyn_Syntax.Exp_bvar (_), _)) | ((FStar_Absyn_Syntax.Exp_fvar (_), _)) | ((FStar_Absyn_Syntax.Exp_constant (_), _)) -> begin
e
end
| (FStar_Absyn_Syntax.Exp_uvar (uv, _26_1054), (_26_1058, _26_1060, t::[], _26_1064, _26_1066)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t)))
end
| (FStar_Absyn_Syntax.Exp_abs (_26_1070), (bs, _26_1074, _26_1076, e::[], _26_1080)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_abs (bs, e)))
end
| (FStar_Absyn_Syntax.Exp_app (_26_1084), (_26_1087, _26_1089, _26_1091, e::[], args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_app (e, args)))
end
| (FStar_Absyn_Syntax.Exp_ascribed (_26_1098, _26_1100, l), (_26_1105, _26_1107, t::[], e::[], _26_1113)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, l)))
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_26_1117, tag)), (_26_1123, _26_1125, _26_1127, e::[], _26_1131)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_meta' (FStar_Absyn_Syntax.Meta_desugared ((e, tag)))))
end
| (FStar_Absyn_Syntax.Exp_match (_26_1135, eqns), (_26_1140, [], [], e1::el, _26_1147)) -> begin
(
# 418 "FStar.Absyn.Visit.fst"
let rec mk_eqns = (fun eqns el -> (match ((eqns, el)) with
| ((p, None, _26_1157)::eqns', e::el') -> begin
(let _110_459 = (mk_eqns eqns' el')
in ((p, None, e))::_110_459)
end
| ((p, Some (_26_1167), _26_1170)::eqns', w::e::el') -> begin
(let _110_460 = (mk_eqns eqns' el')
in ((p, Some (w), e))::_110_460)
end
| ([], []) -> begin
[]
end
| _26_1183 -> begin
(FStar_All.failwith "impossible")
end))
in (let _110_465 = (let _110_464 = (let _110_463 = (mk_eqns eqns el)
in (e1, _110_463))
in (FStar_Absyn_Syntax.mk_Exp_match _110_464))
in (FStar_All.pipe_left w _110_465)))
end
| (FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), _26_1188), (_26_1192, _26_1194, tl, el, _26_1198)) -> begin
(match ((FStar_Util.first_N (FStar_List.length lbs) el)) with
| (el, e'::[]) -> begin
(
# 427 "FStar.Absyn.Visit.fst"
let lbs' = (FStar_List.map3 (fun lb t e -> (
# 427 "FStar.Absyn.Visit.fst"
let _26_1208 = lb
in {FStar_Absyn_Syntax.lbname = _26_1208.FStar_Absyn_Syntax.lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _26_1208.FStar_Absyn_Syntax.lbeff; FStar_Absyn_Syntax.lbdef = e})) lbs tl el)
in (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs'), e'))))
end
| _26_1212 -> begin
(FStar_All.failwith "impossible")
end)
end
| _26_1214 -> begin
(FStar_All.failwith "impossible")
end)
in (e', env)))))

# 435 "FStar.Absyn.Visit.fst"
let collect_from_typ = (fun f env t -> (let _110_589 = (reduce_typ (fun _26_1260 _26_1262 _26_1264 env _26_1267 k -> (k, env)) (fun _26_1242 vt _26_1245 env bvs t -> (
# 438 "FStar.Absyn.Visit.fst"
let env = (f env t)
in (match ((let _110_546 = (compress_typ t)
in _110_546.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(t, env)
end
| _26_1259 -> begin
(vt env bvs t)
end))) (fun _26_1232 _26_1234 _26_1236 env _26_1239 e -> (e, env)) (fun k _26_1229 env -> (k, env)) (fun t _26_1225 env -> (t, env)) (fun e _26_1221 env -> (e, env)) env [] t)
in (FStar_All.pipe_left Prims.snd _110_589)))




