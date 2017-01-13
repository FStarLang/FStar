
open Prims

let log = (fun s -> ())


let rec compress_typ_aux : Prims.bool  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun pos typ -> (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (typ) -> begin
(compress_typ_aux pos typ)
end
| _32_13 -> begin
typ
end)
end
| FStar_Absyn_Syntax.Typ_delayed (_32_15, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
typ
end
| Some (t) -> begin
(

let t' = (compress_typ_aux pos t)
in (

let _32_23 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) when pos -> begin
(compress_typ_aux pos t)
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _32_45); FStar_Absyn_Syntax.tk = _32_42; FStar_Absyn_Syntax.pos = _32_40; FStar_Absyn_Syntax.fvs = _32_38; FStar_Absyn_Syntax.uvs = _32_36}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (t') -> begin
(let _133_8 = (FStar_Absyn_Syntax.mk_Typ_app ((t'), (args)) None typ.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left (compress_typ_aux pos) _133_8))
end
| _32_55 -> begin
typ
end)
end
| _32_57 -> begin
typ
end))


let compress_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun typ -> (compress_typ_aux true typ))


let compress_typ_uvars : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun typ -> (compress_typ_aux false typ))


let rec compress_exp_aux : Prims.bool  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun meta exp -> (match (exp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (uv, _32_64) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(compress_exp_aux meta e)
end
| _32_70 -> begin
exp
end)
end
| FStar_Absyn_Syntax.Exp_delayed (_32_72, _32_74, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
exp
end
| Some (e) -> begin
(

let e' = (compress_exp_aux meta e)
in (

let _32_82 = (FStar_ST.op_Colon_Equals m (Some (e')))
in e'))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _32_86)) when meta -> begin
(compress_exp_aux meta e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _32_100); FStar_Absyn_Syntax.tk = _32_97; FStar_Absyn_Syntax.pos = _32_95; FStar_Absyn_Syntax.fvs = _32_93; FStar_Absyn_Syntax.uvs = _32_91}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e') -> begin
(FStar_Absyn_Syntax.mk_Exp_app ((e'), (args)) None exp.FStar_Absyn_Syntax.pos)
end
| _32_110 -> begin
exp
end)
end
| _32_112 -> begin
exp
end))


let compress_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (compress_exp_aux true e))


let compress_exp_uvars : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (compress_exp_aux false e))


let rec compress_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun knd -> (match (knd.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_32_117, _32_119, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
knd
end
| Some (k) -> begin
(

let k' = (compress_kind k)
in (

let _32_127 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k'))
end)
end
| _32_130 -> begin
knd
end))


let left = (fun ext benv btv -> (match ((ext benv (FStar_Util.Inl (btv)))) with
| (benv, FStar_Util.Inl (bvd)) -> begin
((benv), (bvd))
end
| _32_139 -> begin
(failwith "impossible")
end))


let right = (fun ext benv bvv -> (match ((ext benv (FStar_Util.Inr (bvv)))) with
| (benv, FStar_Util.Inr (bvd)) -> begin
((benv), (bvd))
end
| _32_148 -> begin
(failwith "impossible")
end))


type boundvar =
(FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either


type boundvars =
boundvar Prims.list


type ('env, 'm) imap =
'env  ->  boundvars  ->  'm  ->  ('m * 'env)


type ('env, 'm, 'n) mapper =
('env, FStar_Absyn_Syntax.knd) imap  ->  ('env, FStar_Absyn_Syntax.typ) imap  ->  ('env, FStar_Absyn_Syntax.exp) imap  ->  'env  ->  boundvars  ->  'm  ->  ('n * 'env)


let push_tbinder = (fun binders _32_1 -> (match (_32_1) with
| None -> begin
binders
end
| Some (a) -> begin
(FStar_Util.Inl (a))::binders
end))


let push_vbinder = (fun binders _32_2 -> (match (_32_2) with
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


let leaf_k = (fun _32_176 -> (match (()) with
| () -> begin
(([]), ([]), ([]), ([]))
end))


let leaf_te = (fun _32_177 -> (match (()) with
| () -> begin
(([]), ([]), ([]), ([]), ([]))
end))


let rec reduce_kind = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k -> (

let rec visit_kind = (fun env binders k -> (

let k = (compress_kind k)
in (

let _32_236 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_32_197) -> begin
(failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
(((leaf_k ())), (env))
end
| FStar_Absyn_Syntax.Kind_uvar (_32_206, args) -> begin
(

let _32_212 = (map_args map_typ map_exp env binders args)
in (match (_32_212) with
| (args, env) -> begin
(((([]), ([]), ([]), (args))), (env))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(

let _32_219 = (map_kind env binders k)
in (match (_32_219) with
| (k, env) -> begin
(

let _32_222 = (map_args map_typ map_exp env binders (Prims.snd kabr))
in (match (_32_222) with
| (args, env) -> begin
(((([]), ((k)::[]), ([]), (args))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(

let _32_230 = (map_binders map_kind map_typ env binders bs)
in (match (_32_230) with
| (bs, binders, env) -> begin
(

let _32_233 = (map_kind env binders k)
in (match (_32_233) with
| (k, env) -> begin
((((bs), ((k)::[]), ([]), ([]))), (env))
end))
end))
end)
in (match (_32_236) with
| (components, env) -> begin
(combine_kind k components env)
end))))
and map_kind = (fun env binders k -> (map_kind' visit_kind map_typ map_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_kind env binders k)))
and map_args = (fun map_typ map_exp env binders arguments -> (

let _32_270 = (FStar_List.fold_left (fun _32_254 _32_257 -> (match (((_32_254), (_32_257))) with
| ((out, env), (arg, imp)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(

let _32_262 = (map_typ env binders t)
in (match (_32_262) with
| (t, env) -> begin
(((((FStar_Util.Inl (t)), (imp)))::out), (env))
end))
end
| FStar_Util.Inr (e) -> begin
(

let _32_267 = (map_exp env binders e)
in (match (_32_267) with
| (e, env) -> begin
(((((FStar_Util.Inr (e)), (imp)))::out), (env))
end))
end)
end)) (([]), (env)) arguments)
in (match (_32_270) with
| (args', env) -> begin
(((FStar_List.rev args')), (env))
end)))
and map_binders = (fun map_kind map_typ env binders bs -> (

let _32_301 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _32_280 b -> (match (_32_280) with
| (bs, binders, env) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(

let _32_288 = (map_kind env binders a.FStar_Absyn_Syntax.sort)
in (match (_32_288) with
| (k, env) -> begin
(

let binders = (push_tbinder binders (Some (a.FStar_Absyn_Syntax.v)))
in (((((FStar_Util.Inl ((bvd_to_bvar_s a.FStar_Absyn_Syntax.v k))), (imp)))::bs), (binders), (env)))
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(

let _32_296 = (map_typ env binders x.FStar_Absyn_Syntax.sort)
in (match (_32_296) with
| (t, env) -> begin
(

let binders = (push_vbinder binders (Some (x.FStar_Absyn_Syntax.v)))
in (((((FStar_Util.Inr ((bvd_to_bvar_s x.FStar_Absyn_Syntax.v t))), (imp)))::bs), (binders), (env)))
end))
end)
end)) (([]), (binders), (env))))
in (match (_32_301) with
| (bs, binders, env) -> begin
(((FStar_List.rev bs)), (binders), (env))
end)))
and reduce_typ = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t -> (

let rec map_comp = (fun env binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(

let _32_324 = (map_typ env binders t)
in (match (_32_324) with
| (t, env) -> begin
(let _133_292 = (FStar_Absyn_Syntax.mk_Total t)
in ((_133_292), (env)))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(

let _32_329 = (map_typ env binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_32_329) with
| (t, env) -> begin
(

let _32_332 = (map_args map_typ map_exp env binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_32_332) with
| (args, env) -> begin
(

let _32_343 = (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.fold_map (fun env flag -> (match (flag) with
| FStar_Absyn_Syntax.DECREASES (arg) -> begin
(

let _32_339 = (map_exp env binders arg)
in (match (_32_339) with
| (arg, env) -> begin
((env), (FStar_Absyn_Syntax.DECREASES (arg)))
end))
end
| f -> begin
((env), (f))
end)) env))
in (match (_32_343) with
| (env, flags) -> begin
(let _133_295 = (FStar_Absyn_Syntax.mk_Comp (

let _32_344 = ct
in {FStar_Absyn_Syntax.effect_name = _32_344.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = flags}))
in ((_133_295), (env)))
end))
end))
end))
end))
and visit_typ = (fun env binders t -> (

let _32_507 = (match ((let _133_299 = (compress_typ t)
in _133_299.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_delayed (_32_350) -> begin
(failwith "Impossible")
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(

let _32_362 = (map_typ env binders t)
in (match (_32_362) with
| (_32_360, env) -> begin
(((leaf_te ())), (env))
end))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(

let _32_369 = (map_typ env binders t)
in (match (_32_369) with
| (t, env) -> begin
(

let _32_372 = (map_args map_typ map_exp env binders args)
in (match (_32_372) with
| (args, env) -> begin
(((([]), ([]), ((t)::[]), ([]), ((args)::[]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (axs, t) -> begin
(

let _32_380 = (map_binders map_kind map_typ env binders axs)
in (match (_32_380) with
| (axs, binders, env) -> begin
(

let _32_383 = (map_typ env binders t)
in (match (_32_383) with
| (t, env) -> begin
((((axs), ([]), ((t)::[]), ([]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t2) -> begin
(

let _32_391 = (map_binders map_kind map_typ env binders ((((FStar_Util.Inr (x)), (None)))::[]))
in (match (_32_391) with
| (bs, binders, env) -> begin
(

let _32_394 = (map_typ env binders t2)
in (match (_32_394) with
| (t2, env) -> begin
((((bs), ([]), ((t2)::[]), ([]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(

let _32_402 = (map_binders map_kind map_typ env binders bs)
in (match (_32_402) with
| (bs, binders, env) -> begin
(

let _32_405 = (map_comp env binders c)
in (match (_32_405) with
| (c, env) -> begin
((((bs), ([]), ([]), ((c)::[]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
(

let _32_412 = (map_typ env binders t)
in (match (_32_412) with
| (t, env) -> begin
(

let _32_415 = (map_kind env binders k)
in (match (_32_415) with
| (k, env) -> begin
(((([]), ((k)::[]), ((t)::[]), ([]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_32_417, k) -> begin
(

let _32_423 = (map_kind env binders k)
in (match (_32_423) with
| (k, env) -> begin
(((([]), ((k)::[]), ([]), ([]), ([]))), (env))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
(

let _32_432 = (map_typ env binders t1)
in (match (_32_432) with
| (t1, env) -> begin
(

let _32_435 = (map_typ env binders t2)
in (match (_32_435) with
| (t2, env) -> begin
(((([]), ([]), ((t1)::(t2)::[]), ([]), ([]))), (env))
end))
end))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(

let _32_460 = (map_typ env binders t)
in (match (_32_460) with
| (t, env) -> begin
(((([]), ([]), ((t)::[]), ([]), ([]))), (env))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
(

let _32_468 = (map_typ env binders t)
in (match (_32_468) with
| (t, env) -> begin
(

let map_pats = (fun env pats -> (

let _32_494 = (FStar_List.fold_left (fun _32_474 arg -> (match (_32_474) with
| (pats, env) -> begin
(match (arg) with
| (FStar_Util.Inl (t), _32_479) -> begin
(

let _32_483 = (map_typ env binders t)
in (match (_32_483) with
| (t, env) -> begin
(((((FStar_Util.Inl (t)), (None)))::pats), (env))
end))
end
| (FStar_Util.Inr (e), _32_487) -> begin
(

let _32_491 = (map_exp env binders e)
in (match (_32_491) with
| (e, env) -> begin
(((((FStar_Util.Inr (e)), (None)))::pats), (env))
end))
end)
end)) (([]), (env)) pats)
in (match (_32_494) with
| (pats, env) -> begin
(((FStar_List.rev pats)), (env))
end)))
in (

let _32_504 = (FStar_List.fold_left (fun _32_497 pats -> (match (_32_497) with
| (out, env) -> begin
(

let _32_501 = (map_pats env pats)
in (match (_32_501) with
| (pats, env) -> begin
(((pats)::out), (env))
end))
end)) (([]), (env)) ps)
in (match (_32_504) with
| (pats, env) -> begin
(((([]), ([]), ((t)::[]), ([]), ((FStar_List.rev pats)))), (env))
end)))
end))
end)
in (match (_32_507) with
| (components, env) -> begin
(combine_typ t components env)
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (map_typ' map_kind visit_typ map_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_typ env binders t)))
and reduce_exp = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e -> (

let rec map_exps = (fun env binders el -> (

let _32_545 = (FStar_List.fold_left (fun _32_538 e -> (match (_32_538) with
| (out, env) -> begin
(

let _32_542 = (map_exp env binders e)
in (match (_32_542) with
| (e, env) -> begin
(((e)::out), (env))
end))
end)) (([]), (env)) el)
in (match (_32_545) with
| (el, env) -> begin
(((FStar_List.rev el)), (env))
end)))
and map_exps_with_binders = (fun env el -> (

let _32_559 = (FStar_List.fold_left (fun _32_550 _32_553 -> (match (((_32_550), (_32_553))) with
| ((out, env), (b, e)) -> begin
(

let _32_556 = (map_exp env b e)
in (match (_32_556) with
| (e, env) -> begin
(((e)::out), (env))
end))
end)) (([]), (env)) el)
in (match (_32_559) with
| (el, env) -> begin
(((FStar_List.rev el)), (env))
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (map_exp' map_kind map_typ visit_exp env binders e))
and visit_exp = (fun env binders e -> (

let e = (compress_exp_uvars e)
in (

let _32_746 = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_32_574) -> begin
(failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _32_578)) -> begin
(

let _32_584 = (map_exp env binders e)
in (match (_32_584) with
| (e, env) -> begin
(((([]), ([]), ([]), ((e)::[]), ([]))), (env))
end))
end
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(((leaf_te ())), (env))
end
| FStar_Absyn_Syntax.Exp_uvar (_32_595, t) -> begin
(

let _32_601 = (map_typ env binders t)
in (match (_32_601) with
| (t, env) -> begin
(((([]), ([]), ((t)::[]), ([]), ([]))), (env))
end))
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(

let _32_609 = (map_binders map_kind map_typ env binders bs)
in (match (_32_609) with
| (bs, binders, env) -> begin
(

let _32_612 = (map_exp env binders e)
in (match (_32_612) with
| (e, env) -> begin
((((bs), ([]), ([]), ((e)::[]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(

let _32_619 = (map_exp env binders e)
in (match (_32_619) with
| (e, env) -> begin
(

let _32_622 = (map_args map_typ map_exp env binders args)
in (match (_32_622) with
| (args, env) -> begin
(((([]), ([]), ([]), ((e)::[]), (args))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Exp_match (e1, pl) -> begin
(

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
| FStar_Absyn_Syntax.Pat_cons (_32_650, _32_652, pats) -> begin
(FStar_List.fold_left (fun b _32_660 -> (match (_32_660) with
| (p, _32_659) -> begin
(pat_binders b p)
end)) b pats)
end
| FStar_Absyn_Syntax.Pat_disj ((p)::_32_662) -> begin
(pat_binders b p)
end
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(failwith "impossible")
end))
in (

let branches = (FStar_All.pipe_right pl (FStar_List.collect (fun _32_671 -> (match (_32_671) with
| (p, w, e) -> begin
(

let binders = (pat_binders binders p)
in (match (w) with
| None -> begin
(((binders), (e)))::[]
end
| Some (w) -> begin
(((binders), (w)))::(((binders), (e)))::[]
end))
end))))
in (

let _32_679 = (map_exps_with_binders env ((((binders), (e1)))::branches))
in (match (_32_679) with
| (el, env) -> begin
(((([]), ([]), ([]), (el), ([]))), (env))
end))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _32_683) -> begin
(

let _32_688 = (map_typ env binders t)
in (match (_32_688) with
| (t, env) -> begin
(

let _32_691 = (map_exp env binders e)
in (match (_32_691) with
| (e, env) -> begin
(((([]), ([]), ((t)::[]), ((e)::[]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, (lb)::[]), e2) -> begin
(

let _32_701 = (map_typ env binders lb.FStar_Absyn_Syntax.lbtyp)
in (match (_32_701) with
| (t, env) -> begin
(

let binders' = (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _32_705 -> begin
binders
end)
in (

let _32_709 = (map_exps_with_binders env ((((binders), (lb.FStar_Absyn_Syntax.lbdef)))::(((binders'), (e2)))::[]))
in (match (_32_709) with
| (el, env) -> begin
(((([]), ([]), ((t)::[]), (el), ([]))), (env))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((true, bvdt_tl), e) -> begin
(

let tl = (FStar_List.map (fun lb -> lb.FStar_Absyn_Syntax.lbtyp) bvdt_tl)
in (

let el = (FStar_List.map (fun lb -> lb.FStar_Absyn_Syntax.lbdef) bvdt_tl)
in (

let _32_729 = (FStar_All.pipe_right tl (FStar_List.fold_left (fun _32_722 t -> (match (_32_722) with
| (tl, env) -> begin
(

let _32_726 = (map_typ env binders t)
in (match (_32_726) with
| (t, env) -> begin
(((t)::tl), (env))
end))
end)) (([]), (env))))
in (match (_32_729) with
| (tl, env) -> begin
(

let tl = (FStar_List.rev tl)
in (

let binders = (FStar_List.fold_left (fun binders lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _32_736 -> begin
binders
end)) binders bvdt_tl)
in (

let _32_740 = (map_exps env binders (FStar_List.append el ((e)::[])))
in (match (_32_740) with
| (el, env) -> begin
(((([]), ([]), (tl), (el), ([]))), (env))
end))))
end))))
end
| FStar_Absyn_Syntax.Exp_let (_32_742) -> begin
(failwith "impossible")
end)
in (match (_32_746) with
| (components, env) -> begin
(combine_exp e components env)
end))))
in (map_exp env binders e)))


let combine_kind = (fun k kc env -> (

let k' = (match (((k.FStar_Absyn_Syntax.n), (kc))) with
| ((FStar_Absyn_Syntax.Kind_lam (_), _)) | ((FStar_Absyn_Syntax.Kind_type, _)) | ((FStar_Absyn_Syntax.Kind_effect, _)) | ((FStar_Absyn_Syntax.Kind_unknown, _)) -> begin
(fun p -> (FStar_Util.return_all k))
end
| (FStar_Absyn_Syntax.Kind_uvar (u, _32_771), (_32_775, _32_777, _32_779, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_uvar ((u), (args)))
end
| (FStar_Absyn_Syntax.Kind_abbrev (kabr, _32_785), (_32_789, (k)::[], _32_793, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_abbrev (((((Prims.fst kabr)), (args))), (k)))
end
| (FStar_Absyn_Syntax.Kind_arrow (_32_798, _32_800), (bs, (k')::[], _32_807, _32_809)) -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (k')))
end
| _32_813 -> begin
(failwith "impossible")
end)
in (let _133_388 = (k' k.FStar_Absyn_Syntax.pos)
in ((_133_388), (env)))))


let combine_typ = (fun t tc env -> (

let t = (compress_typ t)
in (

let w = (fun f -> (f None t.FStar_Absyn_Syntax.pos))
in (

let t' = (match (((t.FStar_Absyn_Syntax.n), (tc))) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((FStar_Absyn_Syntax.Typ_const (_), _)) -> begin
t
end
| (FStar_Absyn_Syntax.Typ_lam (_32_838), (bs, _32_842, (t)::[], _32_846, _32_848)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (t))))
end
| (FStar_Absyn_Syntax.Typ_app (_32_852), (_32_855, _32_857, (t)::[], _32_861, (args)::[])) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_app ((t), (args))))
end
| (FStar_Absyn_Syntax.Typ_refine (_32_867), (((FStar_Util.Inr (x), _32_872))::[], _32_876, (t)::[], _32_880, _32_882)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_refine ((x), (t))))
end
| (FStar_Absyn_Syntax.Typ_fun (_32_886), (bs, _32_890, _32_892, (c)::[], _32_896)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c))))
end
| (FStar_Absyn_Syntax.Typ_uvar (x, _32_901), (_32_905, (k)::[], _32_909, _32_911, _32_913)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_uvar' ((x), (k))))
end
| (FStar_Absyn_Syntax.Typ_ascribed (_32_917), (_32_920, (k)::[], (t)::[], _32_926, _32_928)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_ascribed' ((t), (k))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_32_932, l)), (_32_938, _32_940, (t')::[], _32_944, _32_946)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_named (((t'), (l))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_32_950)), (_32_954, _32_956, (t)::[], _32_960, args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern (((t), (args))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_32_965, l, r, p)), (_32_973, _32_975, (t)::[], _32_979, _32_981)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled (((t), (l), (r), (p))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_32_985, b, r)), (_32_992, _32_994, (t)::[], _32_998, _32_1000)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_refresh_label (((t), (b), (r))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_32_1004, _32_1006, _32_1008)), (_32_1013, _32_1015, (t1)::(t2)::[], _32_1020, _32_1022)) -> begin
(let _133_429 = (let _133_428 = (let _133_427 = (let _133_426 = (FStar_Util.mk_ref false)
in ((t1), (t2), (_133_426)))
in FStar_Absyn_Syntax.Meta_slack_formula (_133_427))
in (FStar_Absyn_Syntax.mk_Typ_meta' _133_428))
in (FStar_All.pipe_left w _133_429))
end
| _32_1026 -> begin
(failwith "impossible")
end)
in ((t'), (env))))))


let combine_exp = (fun e ec env -> (

let e = (compress_exp e)
in (

let w = (fun f -> (f None e.FStar_Absyn_Syntax.pos))
in (

let e' = (match (((e.FStar_Absyn_Syntax.n), (ec))) with
| ((FStar_Absyn_Syntax.Exp_bvar (_), _)) | ((FStar_Absyn_Syntax.Exp_fvar (_), _)) | ((FStar_Absyn_Syntax.Exp_constant (_), _)) -> begin
e
end
| (FStar_Absyn_Syntax.Exp_uvar (uv, _32_1054), (_32_1058, _32_1060, (t)::[], _32_1064, _32_1066)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_uvar' ((uv), (t))))
end
| (FStar_Absyn_Syntax.Exp_abs (_32_1070), (bs, _32_1074, _32_1076, (e)::[], _32_1080)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_abs ((bs), (e))))
end
| (FStar_Absyn_Syntax.Exp_app (_32_1084), (_32_1087, _32_1089, _32_1091, (e)::[], args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_app ((e), (args))))
end
| (FStar_Absyn_Syntax.Exp_ascribed (_32_1098, _32_1100, l), (_32_1105, _32_1107, (t)::[], (e)::[], _32_1113)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_ascribed ((e), (t), (l))))
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_32_1117, tag)), (_32_1123, _32_1125, _32_1127, (e)::[], _32_1131)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_meta' (FStar_Absyn_Syntax.Meta_desugared (((e), (tag))))))
end
| (FStar_Absyn_Syntax.Exp_match (_32_1135, eqns), (_32_1140, [], [], (e1)::el, _32_1147)) -> begin
(

let rec mk_eqns = (fun eqns el -> (match (((eqns), (el))) with
| (((p, None, _32_1157))::eqns', (e)::el') -> begin
(let _133_459 = (mk_eqns eqns' el')
in (((p), (None), (e)))::_133_459)
end
| (((p, Some (_32_1167), _32_1170))::eqns', (w)::(e)::el') -> begin
(let _133_460 = (mk_eqns eqns' el')
in (((p), (Some (w)), (e)))::_133_460)
end
| ([], []) -> begin
[]
end
| _32_1183 -> begin
(failwith "impossible")
end))
in (let _133_465 = (let _133_464 = (let _133_463 = (mk_eqns eqns el)
in ((e1), (_133_463)))
in (FStar_Absyn_Syntax.mk_Exp_match _133_464))
in (FStar_All.pipe_left w _133_465)))
end
| (FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), _32_1188), (_32_1192, _32_1194, tl, el, _32_1198)) -> begin
(match ((FStar_Util.first_N (FStar_List.length lbs) el)) with
| (el, (e')::[]) -> begin
(

let lbs' = (FStar_List.map3 (fun lb t e -> (

let _32_1208 = lb
in {FStar_Absyn_Syntax.lbname = _32_1208.FStar_Absyn_Syntax.lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _32_1208.FStar_Absyn_Syntax.lbeff; FStar_Absyn_Syntax.lbdef = e})) lbs tl el)
in (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_let ((((is_rec), (lbs'))), (e')))))
end
| _32_1212 -> begin
(failwith "impossible")
end)
end
| _32_1214 -> begin
(failwith "impossible")
end)
in ((e'), (env))))))


let collect_from_typ = (fun f env t -> (let _133_589 = (reduce_typ (fun _32_1260 _32_1262 _32_1264 env _32_1267 k -> ((k), (env))) (fun _32_1242 vt _32_1245 env bvs t -> (

let env = (f env t)
in (match ((let _133_546 = (compress_typ t)
in _133_546.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
((t), (env))
end
| _32_1259 -> begin
(vt env bvs t)
end))) (fun _32_1232 _32_1234 _32_1236 env _32_1239 e -> ((e), (env))) (fun k _32_1229 env -> ((k), (env))) (fun t _32_1225 env -> ((t), (env))) (fun e _32_1221 env -> ((e), (env))) env [] t)
in (FStar_All.pipe_left Prims.snd _133_589)))




