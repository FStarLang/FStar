
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
| _20_13 -> begin
typ
end)
end
| FStar_Absyn_Syntax.Typ_delayed (_20_15, m) -> begin
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
let _20_23 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) when pos -> begin
(compress_typ_aux pos t)
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _20_45); FStar_Absyn_Syntax.tk = _20_42; FStar_Absyn_Syntax.pos = _20_40; FStar_Absyn_Syntax.fvs = _20_38; FStar_Absyn_Syntax.uvs = _20_36}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (t') -> begin
(let _99_8 = (FStar_Absyn_Syntax.mk_Typ_app (t', args) None typ.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left (compress_typ_aux pos) _99_8))
end
| _20_55 -> begin
typ
end)
end
| _20_57 -> begin
typ
end))

# 50 "FStar.Absyn.Visit.fst"
let compress_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun typ -> (compress_typ_aux true typ))

# 51 "FStar.Absyn.Visit.fst"
let compress_typ_uvars : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun typ -> (compress_typ_aux false typ))

# 53 "FStar.Absyn.Visit.fst"
let rec compress_exp_aux : Prims.bool  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun meta exp -> (match (exp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (uv, _20_64) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(compress_exp_aux meta e)
end
| _20_70 -> begin
exp
end)
end
| FStar_Absyn_Syntax.Exp_delayed (_20_72, _20_74, m) -> begin
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
let _20_82 = (FStar_ST.op_Colon_Equals m (Some (e')))
in e'))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _20_86)) when meta -> begin
(compress_exp_aux meta e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _20_100); FStar_Absyn_Syntax.tk = _20_97; FStar_Absyn_Syntax.pos = _20_95; FStar_Absyn_Syntax.fvs = _20_93; FStar_Absyn_Syntax.uvs = _20_91}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e') -> begin
(FStar_Absyn_Syntax.mk_Exp_app (e', args) None exp.FStar_Absyn_Syntax.pos)
end
| _20_110 -> begin
exp
end)
end
| _20_112 -> begin
exp
end))

# 72 "FStar.Absyn.Visit.fst"
let compress_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (compress_exp_aux true e))

# 73 "FStar.Absyn.Visit.fst"
let compress_exp_uvars : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (compress_exp_aux false e))

# 75 "FStar.Absyn.Visit.fst"
let rec compress_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun knd -> (match (knd.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_20_117, _20_119, m) -> begin
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
let _20_127 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k'))
end)
end
| _20_130 -> begin
knd
end))

# 82 "FStar.Absyn.Visit.fst"
let left = (fun ext benv btv -> (match ((ext benv (FStar_Util.Inl (btv)))) with
| (benv, FStar_Util.Inl (bvd)) -> begin
(benv, bvd)
end
| _20_139 -> begin
(FStar_All.failwith "impossible")
end))

# 85 "FStar.Absyn.Visit.fst"
let right = (fun ext benv bvv -> (match ((ext benv (FStar_Util.Inr (bvv)))) with
| (benv, FStar_Util.Inr (bvd)) -> begin
(benv, bvd)
end
| _20_148 -> begin
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
let push_tbinder = (fun binders _20_1 -> (match (_20_1) with
| None -> begin
binders
end
| Some (a) -> begin
(FStar_Util.Inl (a))::binders
end))

# 104 "FStar.Absyn.Visit.fst"
let push_vbinder = (fun binders _20_2 -> (match (_20_2) with
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
let leaf_k = (fun _20_176 -> (match (()) with
| () -> begin
([], [], [], [])
end))

# 120 "FStar.Absyn.Visit.fst"
let leaf_te = (fun _20_177 -> (match (()) with
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
let _20_236 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_20_197) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
((leaf_k ()), env)
end
| FStar_Absyn_Syntax.Kind_uvar (_20_206, args) -> begin
(
# 141 "FStar.Absyn.Visit.fst"
let _20_212 = (map_args map_typ map_exp env binders args)
in (match (_20_212) with
| (args, env) -> begin
(([], [], [], args), env)
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(
# 144 "FStar.Absyn.Visit.fst"
let _20_219 = (map_kind env binders k)
in (match (_20_219) with
| (k, env) -> begin
(
# 145 "FStar.Absyn.Visit.fst"
let _20_222 = (map_args map_typ map_exp env binders (Prims.snd kabr))
in (match (_20_222) with
| (args, env) -> begin
(([], (k)::[], [], args), env)
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(
# 148 "FStar.Absyn.Visit.fst"
let _20_230 = (map_binders map_kind map_typ env binders bs)
in (match (_20_230) with
| (bs, binders, env) -> begin
(
# 149 "FStar.Absyn.Visit.fst"
let _20_233 = (map_kind env binders k)
in (match (_20_233) with
| (k, env) -> begin
((bs, (k)::[], [], []), env)
end))
end))
end)
in (match (_20_236) with
| (components, env) -> begin
(combine_kind k components env)
end))))
and map_kind = (fun env binders k -> (map_kind' visit_kind map_typ map_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_kind env binders k)))
and map_args = (fun map_typ map_exp env binders arguments -> (
# 160 "FStar.Absyn.Visit.fst"
let _20_270 = (FStar_List.fold_left (fun _20_254 _20_257 -> (match ((_20_254, _20_257)) with
| ((out, env), (arg, imp)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(
# 163 "FStar.Absyn.Visit.fst"
let _20_262 = (map_typ env binders t)
in (match (_20_262) with
| (t, env) -> begin
(((FStar_Util.Inl (t), imp))::out, env)
end))
end
| FStar_Util.Inr (e) -> begin
(
# 166 "FStar.Absyn.Visit.fst"
let _20_267 = (map_exp env binders e)
in (match (_20_267) with
| (e, env) -> begin
(((FStar_Util.Inr (e), imp))::out, env)
end))
end)
end)) ([], env) arguments)
in (match (_20_270) with
| (args', env) -> begin
((FStar_List.rev args'), env)
end)))
and map_binders = (fun map_kind map_typ env binders bs -> (
# 171 "FStar.Absyn.Visit.fst"
let _20_301 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _20_280 b -> (match (_20_280) with
| (bs, binders, env) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(
# 173 "FStar.Absyn.Visit.fst"
let _20_288 = (map_kind env binders a.FStar_Absyn_Syntax.sort)
in (match (_20_288) with
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
let _20_296 = (map_typ env binders x.FStar_Absyn_Syntax.sort)
in (match (_20_296) with
| (t, env) -> begin
(
# 179 "FStar.Absyn.Visit.fst"
let binders = (push_vbinder binders (Some (x.FStar_Absyn_Syntax.v)))
in (((FStar_Util.Inr ((bvd_to_bvar_s x.FStar_Absyn_Syntax.v t)), imp))::bs, binders, env))
end))
end)
end)) ([], binders, env)))
in (match (_20_301) with
| (bs, binders, env) -> begin
((FStar_List.rev bs), binders, env)
end)))
and reduce_typ = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t -> (
# 192 "FStar.Absyn.Visit.fst"
let rec map_comp = (fun env binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(
# 195 "FStar.Absyn.Visit.fst"
let _20_324 = (map_typ env binders t)
in (match (_20_324) with
| (t, env) -> begin
(let _99_292 = (FStar_Absyn_Syntax.mk_Total t)
in (_99_292, env))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(
# 198 "FStar.Absyn.Visit.fst"
let _20_329 = (map_typ env binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_20_329) with
| (t, env) -> begin
(
# 199 "FStar.Absyn.Visit.fst"
let _20_332 = (map_args map_typ map_exp env binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_20_332) with
| (args, env) -> begin
(
# 200 "FStar.Absyn.Visit.fst"
let _20_343 = (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.fold_map (fun env flag -> (match (flag) with
| FStar_Absyn_Syntax.DECREASES (arg) -> begin
(
# 201 "FStar.Absyn.Visit.fst"
let _20_339 = (map_exp env binders arg)
in (match (_20_339) with
| (arg, env) -> begin
(env, FStar_Absyn_Syntax.DECREASES (arg))
end))
end
| f -> begin
(env, f)
end)) env))
in (match (_20_343) with
| (env, flags) -> begin
(let _99_295 = (FStar_Absyn_Syntax.mk_Comp (
# 203 "FStar.Absyn.Visit.fst"
let _20_344 = ct
in {FStar_Absyn_Syntax.effect_name = _20_344.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = flags}))
in (_99_295, env))
end))
end))
end))
end))
and visit_typ = (fun env binders t -> (
# 206 "FStar.Absyn.Visit.fst"
let _20_507 = (match ((let _99_299 = (compress_typ t)
in _99_299.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_delayed (_20_350) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(
# 211 "FStar.Absyn.Visit.fst"
let _20_362 = (map_typ env binders t)
in (match (_20_362) with
| (_20_360, env) -> begin
((leaf_te ()), env)
end))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(
# 215 "FStar.Absyn.Visit.fst"
let _20_369 = (map_typ env binders t)
in (match (_20_369) with
| (t, env) -> begin
(
# 216 "FStar.Absyn.Visit.fst"
let _20_372 = (map_args map_typ map_exp env binders args)
in (match (_20_372) with
| (args, env) -> begin
(([], [], (t)::[], [], (args)::[]), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (axs, t) -> begin
(
# 220 "FStar.Absyn.Visit.fst"
let _20_380 = (map_binders map_kind map_typ env binders axs)
in (match (_20_380) with
| (axs, binders, env) -> begin
(
# 221 "FStar.Absyn.Visit.fst"
let _20_383 = (map_typ env binders t)
in (match (_20_383) with
| (t, env) -> begin
((axs, [], (t)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t2) -> begin
(
# 225 "FStar.Absyn.Visit.fst"
let _20_391 = (map_binders map_kind map_typ env binders (((FStar_Util.Inr (x), None))::[]))
in (match (_20_391) with
| (bs, binders, env) -> begin
(
# 226 "FStar.Absyn.Visit.fst"
let _20_394 = (map_typ env binders t2)
in (match (_20_394) with
| (t2, env) -> begin
((bs, [], (t2)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(
# 230 "FStar.Absyn.Visit.fst"
let _20_402 = (map_binders map_kind map_typ env binders bs)
in (match (_20_402) with
| (bs, binders, env) -> begin
(
# 231 "FStar.Absyn.Visit.fst"
let _20_405 = (map_comp env binders c)
in (match (_20_405) with
| (c, env) -> begin
((bs, [], [], (c)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
(
# 235 "FStar.Absyn.Visit.fst"
let _20_412 = (map_typ env binders t)
in (match (_20_412) with
| (t, env) -> begin
(
# 236 "FStar.Absyn.Visit.fst"
let _20_415 = (map_kind env binders k)
in (match (_20_415) with
| (k, env) -> begin
(([], (k)::[], (t)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_20_417, k) -> begin
(
# 240 "FStar.Absyn.Visit.fst"
let _20_423 = (map_kind env binders k)
in (match (_20_423) with
| (k, env) -> begin
(([], (k)::[], [], [], []), env)
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
(
# 244 "FStar.Absyn.Visit.fst"
let _20_432 = (map_typ env binders t1)
in (match (_20_432) with
| (t1, env) -> begin
(
# 245 "FStar.Absyn.Visit.fst"
let _20_435 = (map_typ env binders t2)
in (match (_20_435) with
| (t2, env) -> begin
(([], [], (t1)::(t2)::[], [], []), env)
end))
end))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(
# 251 "FStar.Absyn.Visit.fst"
let _20_460 = (map_typ env binders t)
in (match (_20_460) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
(
# 255 "FStar.Absyn.Visit.fst"
let _20_468 = (map_typ env binders t)
in (match (_20_468) with
| (t, env) -> begin
(
# 256 "FStar.Absyn.Visit.fst"
let map_pats = (fun env pats -> (
# 257 "FStar.Absyn.Visit.fst"
let _20_494 = (FStar_List.fold_left (fun _20_474 arg -> (match (_20_474) with
| (pats, env) -> begin
(match (arg) with
| (FStar_Util.Inl (t), _20_479) -> begin
(
# 258 "FStar.Absyn.Visit.fst"
let _20_483 = (map_typ env binders t)
in (match (_20_483) with
| (t, env) -> begin
(((FStar_Util.Inl (t), None))::pats, env)
end))
end
| (FStar_Util.Inr (e), _20_487) -> begin
(
# 259 "FStar.Absyn.Visit.fst"
let _20_491 = (map_exp env binders e)
in (match (_20_491) with
| (e, env) -> begin
(((FStar_Util.Inr (e), None))::pats, env)
end))
end)
end)) ([], env) pats)
in (match (_20_494) with
| (pats, env) -> begin
((FStar_List.rev pats), env)
end)))
in (
# 261 "FStar.Absyn.Visit.fst"
let _20_504 = (FStar_List.fold_left (fun _20_497 pats -> (match (_20_497) with
| (out, env) -> begin
(
# 261 "FStar.Absyn.Visit.fst"
let _20_501 = (map_pats env pats)
in (match (_20_501) with
| (pats, env) -> begin
((pats)::out, env)
end))
end)) ([], env) ps)
in (match (_20_504) with
| (pats, env) -> begin
(([], [], (t)::[], [], (FStar_List.rev pats)), env)
end)))
end))
end)
in (match (_20_507) with
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
let _20_545 = (FStar_List.fold_left (fun _20_538 e -> (match (_20_538) with
| (out, env) -> begin
(
# 282 "FStar.Absyn.Visit.fst"
let _20_542 = (map_exp env binders e)
in (match (_20_542) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_20_545) with
| (el, env) -> begin
((FStar_List.rev el), env)
end)))
and map_exps_with_binders = (fun env el -> (
# 286 "FStar.Absyn.Visit.fst"
let _20_559 = (FStar_List.fold_left (fun _20_550 _20_553 -> (match ((_20_550, _20_553)) with
| ((out, env), (b, e)) -> begin
(
# 287 "FStar.Absyn.Visit.fst"
let _20_556 = (map_exp env b e)
in (match (_20_556) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_20_559) with
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
let _20_746 = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_20_574) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _20_578)) -> begin
(
# 299 "FStar.Absyn.Visit.fst"
let _20_584 = (map_exp env binders e)
in (match (_20_584) with
| (e, env) -> begin
(([], [], [], (e)::[], []), env)
end))
end
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
((leaf_te ()), env)
end
| FStar_Absyn_Syntax.Exp_uvar (_20_595, t) -> begin
(
# 308 "FStar.Absyn.Visit.fst"
let _20_601 = (map_typ env binders t)
in (match (_20_601) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(
# 312 "FStar.Absyn.Visit.fst"
let _20_609 = (map_binders map_kind map_typ env binders bs)
in (match (_20_609) with
| (bs, binders, env) -> begin
(
# 313 "FStar.Absyn.Visit.fst"
let _20_612 = (map_exp env binders e)
in (match (_20_612) with
| (e, env) -> begin
((bs, [], [], (e)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(
# 317 "FStar.Absyn.Visit.fst"
let _20_619 = (map_exp env binders e)
in (match (_20_619) with
| (e, env) -> begin
(
# 318 "FStar.Absyn.Visit.fst"
let _20_622 = (map_args map_typ map_exp env binders args)
in (match (_20_622) with
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
| FStar_Absyn_Syntax.Pat_cons (_20_650, _20_652, pats) -> begin
(FStar_List.fold_left (fun b _20_660 -> (match (_20_660) with
| (p, _20_659) -> begin
(pat_binders b p)
end)) b pats)
end
| FStar_Absyn_Syntax.Pat_disj (p::_20_662) -> begin
(pat_binders b p)
end
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end))
in (
# 333 "FStar.Absyn.Visit.fst"
let branches = (FStar_All.pipe_right pl (FStar_List.collect (fun _20_671 -> (match (_20_671) with
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
let _20_679 = (map_exps_with_binders env (((binders, e1))::branches))
in (match (_20_679) with
| (el, env) -> begin
(([], [], [], el, []), env)
end))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _20_683) -> begin
(
# 342 "FStar.Absyn.Visit.fst"
let _20_688 = (map_typ env binders t)
in (match (_20_688) with
| (t, env) -> begin
(
# 343 "FStar.Absyn.Visit.fst"
let _20_691 = (map_exp env binders e)
in (match (_20_691) with
| (e, env) -> begin
(([], [], (t)::[], (e)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, lb::[]), e2) -> begin
(
# 347 "FStar.Absyn.Visit.fst"
let _20_701 = (map_typ env binders lb.FStar_Absyn_Syntax.lbtyp)
in (match (_20_701) with
| (t, env) -> begin
(
# 348 "FStar.Absyn.Visit.fst"
let binders' = (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _20_705 -> begin
binders
end)
in (
# 351 "FStar.Absyn.Visit.fst"
let _20_709 = (map_exps_with_binders env (((binders, lb.FStar_Absyn_Syntax.lbdef))::((binders', e2))::[]))
in (match (_20_709) with
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
let _20_729 = (FStar_All.pipe_right tl (FStar_List.fold_left (fun _20_722 t -> (match (_20_722) with
| (tl, env) -> begin
(
# 358 "FStar.Absyn.Visit.fst"
let _20_726 = (map_typ env binders t)
in (match (_20_726) with
| (t, env) -> begin
((t)::tl, env)
end))
end)) ([], env)))
in (match (_20_729) with
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
| _20_736 -> begin
binders
end)) binders bvdt_tl)
in (
# 364 "FStar.Absyn.Visit.fst"
let _20_740 = (map_exps env binders (FStar_List.append el ((e)::[])))
in (match (_20_740) with
| (el, env) -> begin
(([], [], tl, el, []), env)
end))))
end))))
end
| FStar_Absyn_Syntax.Exp_let (_20_742) -> begin
(FStar_All.failwith "impossible")
end)
in (match (_20_746) with
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
| (FStar_Absyn_Syntax.Kind_uvar (u, _20_771), (_20_775, _20_777, _20_779, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_uvar (u, args))
end
| (FStar_Absyn_Syntax.Kind_abbrev (kabr, _20_785), (_20_789, k::[], _20_793, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_abbrev (((Prims.fst kabr), args), k))
end
| (FStar_Absyn_Syntax.Kind_arrow (_20_798, _20_800), (bs, k'::[], _20_807, _20_809)) -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow (bs, k'))
end
| _20_813 -> begin
(FStar_All.failwith "impossible")
end)
in (let _99_388 = (k' k.FStar_Absyn_Syntax.pos)
in (_99_388, env))))

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
| (FStar_Absyn_Syntax.Typ_lam (_20_838), (bs, _20_842, t::[], _20_846, _20_848)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
end
| (FStar_Absyn_Syntax.Typ_app (_20_852), (_20_855, _20_857, t::[], _20_861, args::[])) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_app (t, args)))
end
| (FStar_Absyn_Syntax.Typ_refine (_20_867), ((FStar_Util.Inr (x), _20_872)::[], _20_876, t::[], _20_880, _20_882)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_refine (x, t)))
end
| (FStar_Absyn_Syntax.Typ_fun (_20_886), (bs, _20_890, _20_892, c::[], _20_896)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_fun (bs, c)))
end
| (FStar_Absyn_Syntax.Typ_uvar (x, _20_901), (_20_905, k::[], _20_909, _20_911, _20_913)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_uvar' (x, k)))
end
| (FStar_Absyn_Syntax.Typ_ascribed (_20_917), (_20_920, k::[], t::[], _20_926, _20_928)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_ascribed' (t, k)))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_20_932, l)), (_20_938, _20_940, t'::[], _20_944, _20_946)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_named ((t', l)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_20_950)), (_20_954, _20_956, t::[], _20_960, args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern ((t, args)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_20_965, l, r, p)), (_20_973, _20_975, t::[], _20_979, _20_981)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_20_985, b, r)), (_20_992, _20_994, t::[], _20_998, _20_1000)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_20_1004, _20_1006, _20_1008)), (_20_1013, _20_1015, t1::t2::[], _20_1020, _20_1022)) -> begin
(let _99_429 = (let _99_428 = (let _99_427 = (let _99_426 = (FStar_Util.mk_ref false)
in (t1, t2, _99_426))
in FStar_Absyn_Syntax.Meta_slack_formula (_99_427))
in (FStar_Absyn_Syntax.mk_Typ_meta' _99_428))
in (FStar_All.pipe_left w _99_429))
end
| _20_1026 -> begin
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
| (FStar_Absyn_Syntax.Exp_uvar (uv, _20_1054), (_20_1058, _20_1060, t::[], _20_1064, _20_1066)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t)))
end
| (FStar_Absyn_Syntax.Exp_abs (_20_1070), (bs, _20_1074, _20_1076, e::[], _20_1080)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_abs (bs, e)))
end
| (FStar_Absyn_Syntax.Exp_app (_20_1084), (_20_1087, _20_1089, _20_1091, e::[], args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_app (e, args)))
end
| (FStar_Absyn_Syntax.Exp_ascribed (_20_1098, _20_1100, l), (_20_1105, _20_1107, t::[], e::[], _20_1113)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, l)))
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_20_1117, tag)), (_20_1123, _20_1125, _20_1127, e::[], _20_1131)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_meta' (FStar_Absyn_Syntax.Meta_desugared ((e, tag)))))
end
| (FStar_Absyn_Syntax.Exp_match (_20_1135, eqns), (_20_1140, [], [], e1::el, _20_1147)) -> begin
(
# 418 "FStar.Absyn.Visit.fst"
let rec mk_eqns = (fun eqns el -> (match ((eqns, el)) with
| ((p, None, _20_1157)::eqns', e::el') -> begin
(let _99_459 = (mk_eqns eqns' el')
in ((p, None, e))::_99_459)
end
| ((p, Some (_20_1167), _20_1170)::eqns', w::e::el') -> begin
(let _99_460 = (mk_eqns eqns' el')
in ((p, Some (w), e))::_99_460)
end
| ([], []) -> begin
[]
end
| _20_1183 -> begin
(FStar_All.failwith "impossible")
end))
in (let _99_465 = (let _99_464 = (let _99_463 = (mk_eqns eqns el)
in (e1, _99_463))
in (FStar_Absyn_Syntax.mk_Exp_match _99_464))
in (FStar_All.pipe_left w _99_465)))
end
| (FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), _20_1188), (_20_1192, _20_1194, tl, el, _20_1198)) -> begin
(match ((FStar_Util.first_N (FStar_List.length lbs) el)) with
| (el, e'::[]) -> begin
(
# 427 "FStar.Absyn.Visit.fst"
let lbs' = (FStar_List.map3 (fun lb t e -> (
# 427 "FStar.Absyn.Visit.fst"
let _20_1208 = lb
in {FStar_Absyn_Syntax.lbname = _20_1208.FStar_Absyn_Syntax.lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _20_1208.FStar_Absyn_Syntax.lbeff; FStar_Absyn_Syntax.lbdef = e})) lbs tl el)
in (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs'), e'))))
end
| _20_1212 -> begin
(FStar_All.failwith "impossible")
end)
end
| _20_1214 -> begin
(FStar_All.failwith "impossible")
end)
in (e', env)))))

# 435 "FStar.Absyn.Visit.fst"
let collect_from_typ = (fun f env t -> (let _99_589 = (reduce_typ (fun _20_1260 _20_1262 _20_1264 env _20_1267 k -> (k, env)) (fun _20_1242 vt _20_1245 env bvs t -> (
# 438 "FStar.Absyn.Visit.fst"
let env = (f env t)
in (match ((let _99_546 = (compress_typ t)
in _99_546.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(t, env)
end
| _20_1259 -> begin
(vt env bvs t)
end))) (fun _20_1232 _20_1234 _20_1236 env _20_1239 e -> (e, env)) (fun k _20_1229 env -> (k, env)) (fun t _20_1225 env -> (t, env)) (fun e _20_1221 env -> (e, env)) env [] t)
in (FStar_All.pipe_left Prims.snd _99_589)))




