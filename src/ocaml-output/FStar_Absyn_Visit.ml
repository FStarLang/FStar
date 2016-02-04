
open Prims
let log = (fun s -> ())

let rec compress_typ_aux : Prims.bool  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun pos typ -> (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (typ) -> begin
(compress_typ_aux pos typ)
end
| _28_13 -> begin
typ
end)
end
| FStar_Absyn_Syntax.Typ_delayed (_28_15, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
typ
end
| Some (t) -> begin
(let t' = (compress_typ_aux pos t)
in (let _28_23 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) when pos -> begin
(compress_typ_aux pos t)
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _28_45); FStar_Absyn_Syntax.tk = _28_42; FStar_Absyn_Syntax.pos = _28_40; FStar_Absyn_Syntax.fvs = _28_38; FStar_Absyn_Syntax.uvs = _28_36}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (t') -> begin
(let _131_8 = (FStar_Absyn_Syntax.mk_Typ_app (t', args) None typ.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left (compress_typ_aux pos) _131_8))
end
| _28_55 -> begin
typ
end)
end
| _28_57 -> begin
typ
end))

let compress_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun typ -> (compress_typ_aux true typ))

let compress_typ_uvars : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun typ -> (compress_typ_aux false typ))

let rec compress_exp_aux : Prims.bool  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun meta exp -> (match (exp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (uv, _28_64) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(compress_exp_aux meta e)
end
| _28_70 -> begin
exp
end)
end
| FStar_Absyn_Syntax.Exp_delayed (_28_72, _28_74, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
exp
end
| Some (e) -> begin
(let e' = (compress_exp_aux meta e)
in (let _28_82 = (FStar_ST.op_Colon_Equals m (Some (e')))
in e'))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _28_86)) when meta -> begin
(compress_exp_aux meta e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _28_100); FStar_Absyn_Syntax.tk = _28_97; FStar_Absyn_Syntax.pos = _28_95; FStar_Absyn_Syntax.fvs = _28_93; FStar_Absyn_Syntax.uvs = _28_91}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e') -> begin
(FStar_Absyn_Syntax.mk_Exp_app (e', args) None exp.FStar_Absyn_Syntax.pos)
end
| _28_110 -> begin
exp
end)
end
| _28_112 -> begin
exp
end))

let compress_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (compress_exp_aux true e))

let compress_exp_uvars : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (compress_exp_aux false e))

let rec compress_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun knd -> (match (knd.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_28_117, _28_119, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
knd
end
| Some (k) -> begin
(let k' = (compress_kind k)
in (let _28_127 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k'))
end)
end
| _28_130 -> begin
knd
end))

let left = (fun ext benv btv -> (match ((ext benv (FStar_Util.Inl (btv)))) with
| (benv, FStar_Util.Inl (bvd)) -> begin
(benv, bvd)
end
| _28_139 -> begin
(FStar_All.failwith "impossible")
end))

let right = (fun ext benv bvv -> (match ((ext benv (FStar_Util.Inr (bvv)))) with
| (benv, FStar_Util.Inr (bvd)) -> begin
(benv, bvd)
end
| _28_148 -> begin
(FStar_All.failwith "impossible")
end))

type boundvar =
(FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either

type boundvars =
boundvar Prims.list

type ('env, 'm) imap =
'env  ->  boundvars  ->  'm  ->  ('m * 'env)

type ('env, 'm, 'n) mapper =
('env, FStar_Absyn_Syntax.knd) imap  ->  ('env, FStar_Absyn_Syntax.typ) imap  ->  ('env, FStar_Absyn_Syntax.exp) imap  ->  'env  ->  boundvars  ->  'm  ->  ('n * 'env)

let push_tbinder = (fun binders _28_1 -> (match (_28_1) with
| None -> begin
binders
end
| Some (a) -> begin
(FStar_Util.Inl (a))::binders
end))

let push_vbinder = (fun binders _28_2 -> (match (_28_2) with
| None -> begin
binders
end
| Some (a) -> begin
(FStar_Util.Inr (a))::binders
end))

let bvd_to_bvar_s = (fun bvd sort -> {FStar_Absyn_Syntax.v = bvd; FStar_Absyn_Syntax.sort = sort; FStar_Absyn_Syntax.p = bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idRange})

let tbinder_opt = (fun aopt k -> (match (aopt) with
| None -> begin
[]
end
| Some (a) -> begin
(FStar_Util.Inl ((bvd_to_bvar_s a k)))::[]
end))

let vbinder_opt = (fun aopt t -> (match (aopt) with
| None -> begin
[]
end
| Some (a) -> begin
(FStar_Util.Inr ((bvd_to_bvar_s a t)))::[]
end))

type knd_components =
(FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd Prims.list * FStar_Absyn_Syntax.typ Prims.list * FStar_Absyn_Syntax.arg Prims.list)

type typ_components =
(FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd Prims.list * FStar_Absyn_Syntax.typ Prims.list * FStar_Absyn_Syntax.comp Prims.list * FStar_Absyn_Syntax.arg Prims.list Prims.list)

type exp_components =
(FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd Prims.list * FStar_Absyn_Syntax.typ Prims.list * FStar_Absyn_Syntax.exp Prims.list * FStar_Absyn_Syntax.arg Prims.list)

let leaf_k = (fun _28_176 -> (match (()) with
| () -> begin
([], [], [], [])
end))

let leaf_te = (fun _28_177 -> (match (()) with
| () -> begin
([], [], [], [], [])
end))

let rec reduce_kind = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k -> (let rec visit_kind = (fun env binders k -> (let k = (compress_kind k)
in (let _28_236 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_28_197) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
((leaf_k ()), env)
end
| FStar_Absyn_Syntax.Kind_uvar (_28_206, args) -> begin
(let _28_212 = (map_args map_typ map_exp env binders args)
in (match (_28_212) with
| (args, env) -> begin
(([], [], [], args), env)
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(let _28_219 = (map_kind env binders k)
in (match (_28_219) with
| (k, env) -> begin
(let _28_222 = (map_args map_typ map_exp env binders (Prims.snd kabr))
in (match (_28_222) with
| (args, env) -> begin
(([], (k)::[], [], args), env)
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _28_230 = (map_binders map_kind map_typ env binders bs)
in (match (_28_230) with
| (bs, binders, env) -> begin
(let _28_233 = (map_kind env binders k)
in (match (_28_233) with
| (k, env) -> begin
((bs, (k)::[], [], []), env)
end))
end))
end)
in (match (_28_236) with
| (components, env) -> begin
(combine_kind k components env)
end))))
and map_kind = (fun env binders k -> (map_kind' visit_kind map_typ map_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_kind env binders k)))
and map_args = (fun map_typ map_exp env binders arguments -> (let _28_270 = (FStar_List.fold_left (fun _28_254 _28_257 -> (match ((_28_254, _28_257)) with
| ((out, env), (arg, imp)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(let _28_262 = (map_typ env binders t)
in (match (_28_262) with
| (t, env) -> begin
(((FStar_Util.Inl (t), imp))::out, env)
end))
end
| FStar_Util.Inr (e) -> begin
(let _28_267 = (map_exp env binders e)
in (match (_28_267) with
| (e, env) -> begin
(((FStar_Util.Inr (e), imp))::out, env)
end))
end)
end)) ([], env) arguments)
in (match (_28_270) with
| (args', env) -> begin
((FStar_List.rev args'), env)
end)))
and map_binders = (fun map_kind map_typ env binders bs -> (let _28_301 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _28_280 b -> (match (_28_280) with
| (bs, binders, env) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(let _28_288 = (map_kind env binders a.FStar_Absyn_Syntax.sort)
in (match (_28_288) with
| (k, env) -> begin
(let binders = (push_tbinder binders (Some (a.FStar_Absyn_Syntax.v)))
in (((FStar_Util.Inl ((bvd_to_bvar_s a.FStar_Absyn_Syntax.v k)), imp))::bs, binders, env))
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _28_296 = (map_typ env binders x.FStar_Absyn_Syntax.sort)
in (match (_28_296) with
| (t, env) -> begin
(let binders = (push_vbinder binders (Some (x.FStar_Absyn_Syntax.v)))
in (((FStar_Util.Inr ((bvd_to_bvar_s x.FStar_Absyn_Syntax.v t)), imp))::bs, binders, env))
end))
end)
end)) ([], binders, env)))
in (match (_28_301) with
| (bs, binders, env) -> begin
((FStar_List.rev bs), binders, env)
end)))
and reduce_typ = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t -> (let rec map_comp = (fun env binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _28_324 = (map_typ env binders t)
in (match (_28_324) with
| (t, env) -> begin
(let _131_292 = (FStar_Absyn_Syntax.mk_Total t)
in (_131_292, env))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _28_329 = (map_typ env binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_28_329) with
| (t, env) -> begin
(let _28_332 = (map_args map_typ map_exp env binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_28_332) with
| (args, env) -> begin
(let _28_343 = (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.fold_map (fun env flag -> (match (flag) with
| FStar_Absyn_Syntax.DECREASES (arg) -> begin
(let _28_339 = (map_exp env binders arg)
in (match (_28_339) with
| (arg, env) -> begin
(env, FStar_Absyn_Syntax.DECREASES (arg))
end))
end
| f -> begin
(env, f)
end)) env))
in (match (_28_343) with
| (env, flags) -> begin
(let _131_295 = (FStar_Absyn_Syntax.mk_Comp (let _28_344 = ct
in {FStar_Absyn_Syntax.effect_name = _28_344.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = flags}))
in (_131_295, env))
end))
end))
end))
end))
and visit_typ = (fun env binders t -> (let _28_507 = (match ((let _131_299 = (compress_typ t)
in _131_299.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_delayed (_28_350) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(let _28_362 = (map_typ env binders t)
in (match (_28_362) with
| (_28_360, env) -> begin
((leaf_te ()), env)
end))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(let _28_369 = (map_typ env binders t)
in (match (_28_369) with
| (t, env) -> begin
(let _28_372 = (map_args map_typ map_exp env binders args)
in (match (_28_372) with
| (args, env) -> begin
(([], [], (t)::[], [], (args)::[]), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (axs, t) -> begin
(let _28_380 = (map_binders map_kind map_typ env binders axs)
in (match (_28_380) with
| (axs, binders, env) -> begin
(let _28_383 = (map_typ env binders t)
in (match (_28_383) with
| (t, env) -> begin
((axs, [], (t)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t2) -> begin
(let _28_391 = (map_binders map_kind map_typ env binders (((FStar_Util.Inr (x), None))::[]))
in (match (_28_391) with
| (bs, binders, env) -> begin
(let _28_394 = (map_typ env binders t2)
in (match (_28_394) with
| (t2, env) -> begin
((bs, [], (t2)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let _28_402 = (map_binders map_kind map_typ env binders bs)
in (match (_28_402) with
| (bs, binders, env) -> begin
(let _28_405 = (map_comp env binders c)
in (match (_28_405) with
| (c, env) -> begin
((bs, [], [], (c)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
(let _28_412 = (map_typ env binders t)
in (match (_28_412) with
| (t, env) -> begin
(let _28_415 = (map_kind env binders k)
in (match (_28_415) with
| (k, env) -> begin
(([], (k)::[], (t)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_28_417, k) -> begin
(let _28_423 = (map_kind env binders k)
in (match (_28_423) with
| (k, env) -> begin
(([], (k)::[], [], [], []), env)
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
(let _28_432 = (map_typ env binders t1)
in (match (_28_432) with
| (t1, env) -> begin
(let _28_435 = (map_typ env binders t2)
in (match (_28_435) with
| (t2, env) -> begin
(([], [], (t1)::(t2)::[], [], []), env)
end))
end))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(let _28_460 = (map_typ env binders t)
in (match (_28_460) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
(let _28_468 = (map_typ env binders t)
in (match (_28_468) with
| (t, env) -> begin
(let map_pats = (fun env pats -> (let _28_494 = (FStar_List.fold_left (fun _28_474 arg -> (match (_28_474) with
| (pats, env) -> begin
(match (arg) with
| (FStar_Util.Inl (t), _28_479) -> begin
(let _28_483 = (map_typ env binders t)
in (match (_28_483) with
| (t, env) -> begin
(((FStar_Util.Inl (t), None))::pats, env)
end))
end
| (FStar_Util.Inr (e), _28_487) -> begin
(let _28_491 = (map_exp env binders e)
in (match (_28_491) with
| (e, env) -> begin
(((FStar_Util.Inr (e), None))::pats, env)
end))
end)
end)) ([], env) pats)
in (match (_28_494) with
| (pats, env) -> begin
((FStar_List.rev pats), env)
end)))
in (let _28_504 = (FStar_List.fold_left (fun _28_497 pats -> (match (_28_497) with
| (out, env) -> begin
(let _28_501 = (map_pats env pats)
in (match (_28_501) with
| (pats, env) -> begin
((pats)::out, env)
end))
end)) ([], env) ps)
in (match (_28_504) with
| (pats, env) -> begin
(([], [], (t)::[], [], (FStar_List.rev pats)), env)
end)))
end))
end)
in (match (_28_507) with
| (components, env) -> begin
(combine_typ t components env)
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (map_typ' map_kind visit_typ map_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_typ env binders t)))
and reduce_exp = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e -> (let rec map_exps = (fun env binders el -> (let _28_545 = (FStar_List.fold_left (fun _28_538 e -> (match (_28_538) with
| (out, env) -> begin
(let _28_542 = (map_exp env binders e)
in (match (_28_542) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_28_545) with
| (el, env) -> begin
((FStar_List.rev el), env)
end)))
and map_exps_with_binders = (fun env el -> (let _28_559 = (FStar_List.fold_left (fun _28_550 _28_553 -> (match ((_28_550, _28_553)) with
| ((out, env), (b, e)) -> begin
(let _28_556 = (map_exp env b e)
in (match (_28_556) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_28_559) with
| (el, env) -> begin
((FStar_List.rev el), env)
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (map_exp' map_kind map_typ visit_exp env binders e))
and visit_exp = (fun env binders e -> (let e = (compress_exp_uvars e)
in (let _28_746 = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_28_574) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _28_578)) -> begin
(let _28_584 = (map_exp env binders e)
in (match (_28_584) with
| (e, env) -> begin
(([], [], [], (e)::[], []), env)
end))
end
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
((leaf_te ()), env)
end
| FStar_Absyn_Syntax.Exp_uvar (_28_595, t) -> begin
(let _28_601 = (map_typ env binders t)
in (match (_28_601) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(let _28_609 = (map_binders map_kind map_typ env binders bs)
in (match (_28_609) with
| (bs, binders, env) -> begin
(let _28_612 = (map_exp env binders e)
in (match (_28_612) with
| (e, env) -> begin
((bs, [], [], (e)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(let _28_619 = (map_exp env binders e)
in (match (_28_619) with
| (e, env) -> begin
(let _28_622 = (map_args map_typ map_exp env binders args)
in (match (_28_622) with
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
| FStar_Absyn_Syntax.Pat_cons (_28_650, _28_652, pats) -> begin
(FStar_List.fold_left (fun b _28_660 -> (match (_28_660) with
| (p, _28_659) -> begin
(pat_binders b p)
end)) b pats)
end
| FStar_Absyn_Syntax.Pat_disj (p::_28_662) -> begin
(pat_binders b p)
end
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end))
in (let branches = (FStar_All.pipe_right pl (FStar_List.collect (fun _28_671 -> (match (_28_671) with
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
in (let _28_679 = (map_exps_with_binders env (((binders, e1))::branches))
in (match (_28_679) with
| (el, env) -> begin
(([], [], [], el, []), env)
end))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _28_683) -> begin
(let _28_688 = (map_typ env binders t)
in (match (_28_688) with
| (t, env) -> begin
(let _28_691 = (map_exp env binders e)
in (match (_28_691) with
| (e, env) -> begin
(([], [], (t)::[], (e)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, lb::[]), e2) -> begin
(let _28_701 = (map_typ env binders lb.FStar_Absyn_Syntax.lbtyp)
in (match (_28_701) with
| (t, env) -> begin
(let binders' = (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _28_705 -> begin
binders
end)
in (let _28_709 = (map_exps_with_binders env (((binders, lb.FStar_Absyn_Syntax.lbdef))::((binders', e2))::[]))
in (match (_28_709) with
| (el, env) -> begin
(([], [], (t)::[], el, []), env)
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((true, bvdt_tl), e) -> begin
(let tl = (FStar_List.map (fun lb -> lb.FStar_Absyn_Syntax.lbtyp) bvdt_tl)
in (let el = (FStar_List.map (fun lb -> lb.FStar_Absyn_Syntax.lbdef) bvdt_tl)
in (let _28_729 = (FStar_All.pipe_right tl (FStar_List.fold_left (fun _28_722 t -> (match (_28_722) with
| (tl, env) -> begin
(let _28_726 = (map_typ env binders t)
in (match (_28_726) with
| (t, env) -> begin
((t)::tl, env)
end))
end)) ([], env)))
in (match (_28_729) with
| (tl, env) -> begin
(let tl = (FStar_List.rev tl)
in (let binders = (FStar_List.fold_left (fun binders lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _28_736 -> begin
binders
end)) binders bvdt_tl)
in (let _28_740 = (map_exps env binders (FStar_List.append el ((e)::[])))
in (match (_28_740) with
| (el, env) -> begin
(([], [], tl, el, []), env)
end))))
end))))
end
| FStar_Absyn_Syntax.Exp_let (_28_742) -> begin
(FStar_All.failwith "impossible")
end)
in (match (_28_746) with
| (components, env) -> begin
(combine_exp e components env)
end))))
in (map_exp env binders e)))

let combine_kind = (fun k kc env -> (let k' = (match ((k.FStar_Absyn_Syntax.n, kc)) with
| ((FStar_Absyn_Syntax.Kind_lam (_), _)) | ((FStar_Absyn_Syntax.Kind_type, _)) | ((FStar_Absyn_Syntax.Kind_effect, _)) | ((FStar_Absyn_Syntax.Kind_unknown, _)) -> begin
(fun p -> (FStar_Util.return_all k))
end
| (FStar_Absyn_Syntax.Kind_uvar (u, _28_771), (_28_775, _28_777, _28_779, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_uvar (u, args))
end
| (FStar_Absyn_Syntax.Kind_abbrev (kabr, _28_785), (_28_789, k::[], _28_793, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_abbrev (((Prims.fst kabr), args), k))
end
| (FStar_Absyn_Syntax.Kind_arrow (_28_798, _28_800), (bs, k'::[], _28_807, _28_809)) -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow (bs, k'))
end
| _28_813 -> begin
(FStar_All.failwith "impossible")
end)
in (let _131_388 = (k' k.FStar_Absyn_Syntax.pos)
in (_131_388, env))))

let combine_typ = (fun t tc env -> (let t = (compress_typ t)
in (let w = (fun f -> (f None t.FStar_Absyn_Syntax.pos))
in (let t' = (match ((t.FStar_Absyn_Syntax.n, tc)) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((FStar_Absyn_Syntax.Typ_const (_), _)) -> begin
t
end
| (FStar_Absyn_Syntax.Typ_lam (_28_838), (bs, _28_842, t::[], _28_846, _28_848)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
end
| (FStar_Absyn_Syntax.Typ_app (_28_852), (_28_855, _28_857, t::[], _28_861, args::[])) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_app (t, args)))
end
| (FStar_Absyn_Syntax.Typ_refine (_28_867), ((FStar_Util.Inr (x), _28_872)::[], _28_876, t::[], _28_880, _28_882)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_refine (x, t)))
end
| (FStar_Absyn_Syntax.Typ_fun (_28_886), (bs, _28_890, _28_892, c::[], _28_896)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_fun (bs, c)))
end
| (FStar_Absyn_Syntax.Typ_uvar (x, _28_901), (_28_905, k::[], _28_909, _28_911, _28_913)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_uvar' (x, k)))
end
| (FStar_Absyn_Syntax.Typ_ascribed (_28_917), (_28_920, k::[], t::[], _28_926, _28_928)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_ascribed' (t, k)))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_28_932, l)), (_28_938, _28_940, t'::[], _28_944, _28_946)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_named ((t', l)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_28_950)), (_28_954, _28_956, t::[], _28_960, args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern ((t, args)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_28_965, l, r, p)), (_28_973, _28_975, t::[], _28_979, _28_981)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_28_985, b, r)), (_28_992, _28_994, t::[], _28_998, _28_1000)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_28_1004, _28_1006, _28_1008)), (_28_1013, _28_1015, t1::t2::[], _28_1020, _28_1022)) -> begin
(let _131_429 = (let _131_428 = (let _131_427 = (let _131_426 = (FStar_Util.mk_ref false)
in (t1, t2, _131_426))
in FStar_Absyn_Syntax.Meta_slack_formula (_131_427))
in (FStar_Absyn_Syntax.mk_Typ_meta' _131_428))
in (FStar_All.pipe_left w _131_429))
end
| _28_1026 -> begin
(FStar_All.failwith "impossible")
end)
in (t', env)))))

let combine_exp = (fun e ec env -> (let e = (compress_exp e)
in (let w = (fun f -> (f None e.FStar_Absyn_Syntax.pos))
in (let e' = (match ((e.FStar_Absyn_Syntax.n, ec)) with
| ((FStar_Absyn_Syntax.Exp_bvar (_), _)) | ((FStar_Absyn_Syntax.Exp_fvar (_), _)) | ((FStar_Absyn_Syntax.Exp_constant (_), _)) -> begin
e
end
| (FStar_Absyn_Syntax.Exp_uvar (uv, _28_1054), (_28_1058, _28_1060, t::[], _28_1064, _28_1066)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t)))
end
| (FStar_Absyn_Syntax.Exp_abs (_28_1070), (bs, _28_1074, _28_1076, e::[], _28_1080)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_abs (bs, e)))
end
| (FStar_Absyn_Syntax.Exp_app (_28_1084), (_28_1087, _28_1089, _28_1091, e::[], args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_app (e, args)))
end
| (FStar_Absyn_Syntax.Exp_ascribed (_28_1098, _28_1100, l), (_28_1105, _28_1107, t::[], e::[], _28_1113)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, l)))
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_28_1117, tag)), (_28_1123, _28_1125, _28_1127, e::[], _28_1131)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_meta' (FStar_Absyn_Syntax.Meta_desugared ((e, tag)))))
end
| (FStar_Absyn_Syntax.Exp_match (_28_1135, eqns), (_28_1140, [], [], e1::el, _28_1147)) -> begin
(let rec mk_eqns = (fun eqns el -> (match ((eqns, el)) with
| ((p, None, _28_1157)::eqns', e::el') -> begin
(let _131_459 = (mk_eqns eqns' el')
in ((p, None, e))::_131_459)
end
| ((p, Some (_28_1167), _28_1170)::eqns', w::e::el') -> begin
(let _131_460 = (mk_eqns eqns' el')
in ((p, Some (w), e))::_131_460)
end
| ([], []) -> begin
[]
end
| _28_1183 -> begin
(FStar_All.failwith "impossible")
end))
in (let _131_465 = (let _131_464 = (let _131_463 = (mk_eqns eqns el)
in (e1, _131_463))
in (FStar_Absyn_Syntax.mk_Exp_match _131_464))
in (FStar_All.pipe_left w _131_465)))
end
| (FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), _28_1188), (_28_1192, _28_1194, tl, el, _28_1198)) -> begin
(match ((FStar_Util.first_N (FStar_List.length lbs) el)) with
| (el, e'::[]) -> begin
(let lbs' = (FStar_List.map3 (fun lb t e -> (let _28_1208 = lb
in {FStar_Absyn_Syntax.lbname = _28_1208.FStar_Absyn_Syntax.lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _28_1208.FStar_Absyn_Syntax.lbeff; FStar_Absyn_Syntax.lbdef = e})) lbs tl el)
in (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs'), e'))))
end
| _28_1212 -> begin
(FStar_All.failwith "impossible")
end)
end
| _28_1214 -> begin
(FStar_All.failwith "impossible")
end)
in (e', env)))))

let collect_from_typ = (fun f env t -> (let _131_589 = (reduce_typ (fun _28_1260 _28_1262 _28_1264 env _28_1267 k -> (k, env)) (fun _28_1242 vt _28_1245 env bvs t -> (let env = (f env t)
in (match ((let _131_546 = (compress_typ t)
in _131_546.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(t, env)
end
| _28_1259 -> begin
(vt env bvs t)
end))) (fun _28_1232 _28_1234 _28_1236 env _28_1239 e -> (e, env)) (fun k _28_1229 env -> (k, env)) (fun t _28_1225 env -> (t, env)) (fun e _28_1221 env -> (e, env)) env [] t)
in (FStar_All.pipe_left Prims.snd _131_589)))




