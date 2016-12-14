
open Prims

let log = (fun s -> ())


let rec compress_typ_aux : Prims.bool  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun pos typ -> (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (typ) -> begin
(compress_typ_aux pos typ)
end
| _31_13 -> begin
typ
end)
end
| FStar_Absyn_Syntax.Typ_delayed (_31_15, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
typ
end
| Some (t) -> begin
(

let t' = (compress_typ_aux pos t)
in (

let _31_23 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) when pos -> begin
(compress_typ_aux pos t)
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _31_45); FStar_Absyn_Syntax.tk = _31_42; FStar_Absyn_Syntax.pos = _31_40; FStar_Absyn_Syntax.fvs = _31_38; FStar_Absyn_Syntax.uvs = _31_36}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (t') -> begin
(let _128_8 = (FStar_Absyn_Syntax.mk_Typ_app ((t'), (args)) None typ.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left (compress_typ_aux pos) _128_8))
end
| _31_55 -> begin
typ
end)
end
| _31_57 -> begin
typ
end))


let compress_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun typ -> (compress_typ_aux true typ))


let compress_typ_uvars : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun typ -> (compress_typ_aux false typ))


let rec compress_exp_aux : Prims.bool  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun meta exp -> (match (exp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (uv, _31_64) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(compress_exp_aux meta e)
end
| _31_70 -> begin
exp
end)
end
| FStar_Absyn_Syntax.Exp_delayed (_31_72, _31_74, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
exp
end
| Some (e) -> begin
(

let e' = (compress_exp_aux meta e)
in (

let _31_82 = (FStar_ST.op_Colon_Equals m (Some (e')))
in e'))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _31_86)) when meta -> begin
(compress_exp_aux meta e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _31_100); FStar_Absyn_Syntax.tk = _31_97; FStar_Absyn_Syntax.pos = _31_95; FStar_Absyn_Syntax.fvs = _31_93; FStar_Absyn_Syntax.uvs = _31_91}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e') -> begin
(FStar_Absyn_Syntax.mk_Exp_app ((e'), (args)) None exp.FStar_Absyn_Syntax.pos)
end
| _31_110 -> begin
exp
end)
end
| _31_112 -> begin
exp
end))


let compress_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (compress_exp_aux true e))


let compress_exp_uvars : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (compress_exp_aux false e))


let rec compress_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun knd -> (match (knd.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_31_117, _31_119, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
knd
end
| Some (k) -> begin
(

let k' = (compress_kind k)
in (

let _31_127 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k'))
end)
end
| _31_130 -> begin
knd
end))


let left = (fun ext benv btv -> (match ((ext benv (FStar_Util.Inl (btv)))) with
| (benv, FStar_Util.Inl (bvd)) -> begin
((benv), (bvd))
end
| _31_139 -> begin
(FStar_All.failwith "impossible")
end))


let right = (fun ext benv bvv -> (match ((ext benv (FStar_Util.Inr (bvv)))) with
| (benv, FStar_Util.Inr (bvd)) -> begin
((benv), (bvd))
end
| _31_148 -> begin
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


let push_tbinder = (fun binders _31_1 -> (match (_31_1) with
| None -> begin
binders
end
| Some (a) -> begin
(FStar_Util.Inl (a))::binders
end))


let push_vbinder = (fun binders _31_2 -> (match (_31_2) with
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


let leaf_k = (fun _31_176 -> (match (()) with
| () -> begin
(([]), ([]), ([]), ([]))
end))


let leaf_te = (fun _31_177 -> (match (()) with
| () -> begin
(([]), ([]), ([]), ([]), ([]))
end))


let rec reduce_kind = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k -> (

let rec visit_kind = (fun env binders k -> (

let k = (compress_kind k)
in (

let _31_236 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_31_197) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
(((leaf_k ())), (env))
end
| FStar_Absyn_Syntax.Kind_uvar (_31_206, args) -> begin
(

let _31_212 = (map_args map_typ map_exp env binders args)
in (match (_31_212) with
| (args, env) -> begin
(((([]), ([]), ([]), (args))), (env))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(

let _31_219 = (map_kind env binders k)
in (match (_31_219) with
| (k, env) -> begin
(

let _31_222 = (map_args map_typ map_exp env binders (Prims.snd kabr))
in (match (_31_222) with
| (args, env) -> begin
(((([]), ((k)::[]), ([]), (args))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(

let _31_230 = (map_binders map_kind map_typ env binders bs)
in (match (_31_230) with
| (bs, binders, env) -> begin
(

let _31_233 = (map_kind env binders k)
in (match (_31_233) with
| (k, env) -> begin
((((bs), ((k)::[]), ([]), ([]))), (env))
end))
end))
end)
in (match (_31_236) with
| (components, env) -> begin
(combine_kind k components env)
end))))
and map_kind = (fun env binders k -> (map_kind' visit_kind map_typ map_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_kind env binders k)))
and map_args = (fun map_typ map_exp env binders arguments -> (

let _31_270 = (FStar_List.fold_left (fun _31_254 _31_257 -> (match (((_31_254), (_31_257))) with
| ((out, env), (arg, imp)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(

let _31_262 = (map_typ env binders t)
in (match (_31_262) with
| (t, env) -> begin
(((((FStar_Util.Inl (t)), (imp)))::out), (env))
end))
end
| FStar_Util.Inr (e) -> begin
(

let _31_267 = (map_exp env binders e)
in (match (_31_267) with
| (e, env) -> begin
(((((FStar_Util.Inr (e)), (imp)))::out), (env))
end))
end)
end)) (([]), (env)) arguments)
in (match (_31_270) with
| (args', env) -> begin
(((FStar_List.rev args')), (env))
end)))
and map_binders = (fun map_kind map_typ env binders bs -> (

let _31_301 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _31_280 b -> (match (_31_280) with
| (bs, binders, env) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(

let _31_288 = (map_kind env binders a.FStar_Absyn_Syntax.sort)
in (match (_31_288) with
| (k, env) -> begin
(

let binders = (push_tbinder binders (Some (a.FStar_Absyn_Syntax.v)))
in (((((FStar_Util.Inl ((bvd_to_bvar_s a.FStar_Absyn_Syntax.v k))), (imp)))::bs), (binders), (env)))
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(

let _31_296 = (map_typ env binders x.FStar_Absyn_Syntax.sort)
in (match (_31_296) with
| (t, env) -> begin
(

let binders = (push_vbinder binders (Some (x.FStar_Absyn_Syntax.v)))
in (((((FStar_Util.Inr ((bvd_to_bvar_s x.FStar_Absyn_Syntax.v t))), (imp)))::bs), (binders), (env)))
end))
end)
end)) (([]), (binders), (env))))
in (match (_31_301) with
| (bs, binders, env) -> begin
(((FStar_List.rev bs)), (binders), (env))
end)))
and reduce_typ = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t -> (

let rec map_comp = (fun env binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(

let _31_324 = (map_typ env binders t)
in (match (_31_324) with
| (t, env) -> begin
(let _128_292 = (FStar_Absyn_Syntax.mk_Total t)
in ((_128_292), (env)))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(

let _31_329 = (map_typ env binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_31_329) with
| (t, env) -> begin
(

let _31_332 = (map_args map_typ map_exp env binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_31_332) with
| (args, env) -> begin
(

let _31_343 = (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.fold_map (fun env flag -> (match (flag) with
| FStar_Absyn_Syntax.DECREASES (arg) -> begin
(

let _31_339 = (map_exp env binders arg)
in (match (_31_339) with
| (arg, env) -> begin
((env), (FStar_Absyn_Syntax.DECREASES (arg)))
end))
end
| f -> begin
((env), (f))
end)) env))
in (match (_31_343) with
| (env, flags) -> begin
(let _128_295 = (FStar_Absyn_Syntax.mk_Comp (

let _31_344 = ct
in {FStar_Absyn_Syntax.effect_name = _31_344.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = flags}))
in ((_128_295), (env)))
end))
end))
end))
end))
and visit_typ = (fun env binders t -> (

let _31_507 = (match ((let _128_299 = (compress_typ t)
in _128_299.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_delayed (_31_350) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(

let _31_362 = (map_typ env binders t)
in (match (_31_362) with
| (_31_360, env) -> begin
(((leaf_te ())), (env))
end))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(

let _31_369 = (map_typ env binders t)
in (match (_31_369) with
| (t, env) -> begin
(

let _31_372 = (map_args map_typ map_exp env binders args)
in (match (_31_372) with
| (args, env) -> begin
(((([]), ([]), ((t)::[]), ([]), ((args)::[]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (axs, t) -> begin
(

let _31_380 = (map_binders map_kind map_typ env binders axs)
in (match (_31_380) with
| (axs, binders, env) -> begin
(

let _31_383 = (map_typ env binders t)
in (match (_31_383) with
| (t, env) -> begin
((((axs), ([]), ((t)::[]), ([]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t2) -> begin
(

let _31_391 = (map_binders map_kind map_typ env binders ((((FStar_Util.Inr (x)), (None)))::[]))
in (match (_31_391) with
| (bs, binders, env) -> begin
(

let _31_394 = (map_typ env binders t2)
in (match (_31_394) with
| (t2, env) -> begin
((((bs), ([]), ((t2)::[]), ([]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(

let _31_402 = (map_binders map_kind map_typ env binders bs)
in (match (_31_402) with
| (bs, binders, env) -> begin
(

let _31_405 = (map_comp env binders c)
in (match (_31_405) with
| (c, env) -> begin
((((bs), ([]), ([]), ((c)::[]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
(

let _31_412 = (map_typ env binders t)
in (match (_31_412) with
| (t, env) -> begin
(

let _31_415 = (map_kind env binders k)
in (match (_31_415) with
| (k, env) -> begin
(((([]), ((k)::[]), ((t)::[]), ([]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_31_417, k) -> begin
(

let _31_423 = (map_kind env binders k)
in (match (_31_423) with
| (k, env) -> begin
(((([]), ((k)::[]), ([]), ([]), ([]))), (env))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
(

let _31_432 = (map_typ env binders t1)
in (match (_31_432) with
| (t1, env) -> begin
(

let _31_435 = (map_typ env binders t2)
in (match (_31_435) with
| (t2, env) -> begin
(((([]), ([]), ((t1)::(t2)::[]), ([]), ([]))), (env))
end))
end))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(

let _31_460 = (map_typ env binders t)
in (match (_31_460) with
| (t, env) -> begin
(((([]), ([]), ((t)::[]), ([]), ([]))), (env))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
(

let _31_468 = (map_typ env binders t)
in (match (_31_468) with
| (t, env) -> begin
(

let map_pats = (fun env pats -> (

let _31_494 = (FStar_List.fold_left (fun _31_474 arg -> (match (_31_474) with
| (pats, env) -> begin
(match (arg) with
| (FStar_Util.Inl (t), _31_479) -> begin
(

let _31_483 = (map_typ env binders t)
in (match (_31_483) with
| (t, env) -> begin
(((((FStar_Util.Inl (t)), (None)))::pats), (env))
end))
end
| (FStar_Util.Inr (e), _31_487) -> begin
(

let _31_491 = (map_exp env binders e)
in (match (_31_491) with
| (e, env) -> begin
(((((FStar_Util.Inr (e)), (None)))::pats), (env))
end))
end)
end)) (([]), (env)) pats)
in (match (_31_494) with
| (pats, env) -> begin
(((FStar_List.rev pats)), (env))
end)))
in (

let _31_504 = (FStar_List.fold_left (fun _31_497 pats -> (match (_31_497) with
| (out, env) -> begin
(

let _31_501 = (map_pats env pats)
in (match (_31_501) with
| (pats, env) -> begin
(((pats)::out), (env))
end))
end)) (([]), (env)) ps)
in (match (_31_504) with
| (pats, env) -> begin
(((([]), ([]), ((t)::[]), ([]), ((FStar_List.rev pats)))), (env))
end)))
end))
end)
in (match (_31_507) with
| (components, env) -> begin
(combine_typ t components env)
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (map_typ' map_kind visit_typ map_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_typ env binders t)))
and reduce_exp = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e -> (

let rec map_exps = (fun env binders el -> (

let _31_545 = (FStar_List.fold_left (fun _31_538 e -> (match (_31_538) with
| (out, env) -> begin
(

let _31_542 = (map_exp env binders e)
in (match (_31_542) with
| (e, env) -> begin
(((e)::out), (env))
end))
end)) (([]), (env)) el)
in (match (_31_545) with
| (el, env) -> begin
(((FStar_List.rev el)), (env))
end)))
and map_exps_with_binders = (fun env el -> (

let _31_559 = (FStar_List.fold_left (fun _31_550 _31_553 -> (match (((_31_550), (_31_553))) with
| ((out, env), (b, e)) -> begin
(

let _31_556 = (map_exp env b e)
in (match (_31_556) with
| (e, env) -> begin
(((e)::out), (env))
end))
end)) (([]), (env)) el)
in (match (_31_559) with
| (el, env) -> begin
(((FStar_List.rev el)), (env))
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (map_exp' map_kind map_typ visit_exp env binders e))
and visit_exp = (fun env binders e -> (

let e = (compress_exp_uvars e)
in (

let _31_746 = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_31_574) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _31_578)) -> begin
(

let _31_584 = (map_exp env binders e)
in (match (_31_584) with
| (e, env) -> begin
(((([]), ([]), ([]), ((e)::[]), ([]))), (env))
end))
end
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(((leaf_te ())), (env))
end
| FStar_Absyn_Syntax.Exp_uvar (_31_595, t) -> begin
(

let _31_601 = (map_typ env binders t)
in (match (_31_601) with
| (t, env) -> begin
(((([]), ([]), ((t)::[]), ([]), ([]))), (env))
end))
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(

let _31_609 = (map_binders map_kind map_typ env binders bs)
in (match (_31_609) with
| (bs, binders, env) -> begin
(

let _31_612 = (map_exp env binders e)
in (match (_31_612) with
| (e, env) -> begin
((((bs), ([]), ([]), ((e)::[]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(

let _31_619 = (map_exp env binders e)
in (match (_31_619) with
| (e, env) -> begin
(

let _31_622 = (map_args map_typ map_exp env binders args)
in (match (_31_622) with
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
| FStar_Absyn_Syntax.Pat_cons (_31_650, _31_652, pats) -> begin
(FStar_List.fold_left (fun b _31_660 -> (match (_31_660) with
| (p, _31_659) -> begin
(pat_binders b p)
end)) b pats)
end
| FStar_Absyn_Syntax.Pat_disj ((p)::_31_662) -> begin
(pat_binders b p)
end
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end))
in (

let branches = (FStar_All.pipe_right pl (FStar_List.collect (fun _31_671 -> (match (_31_671) with
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

let _31_679 = (map_exps_with_binders env ((((binders), (e1)))::branches))
in (match (_31_679) with
| (el, env) -> begin
(((([]), ([]), ([]), (el), ([]))), (env))
end))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _31_683) -> begin
(

let _31_688 = (map_typ env binders t)
in (match (_31_688) with
| (t, env) -> begin
(

let _31_691 = (map_exp env binders e)
in (match (_31_691) with
| (e, env) -> begin
(((([]), ([]), ((t)::[]), ((e)::[]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, (lb)::[]), e2) -> begin
(

let _31_701 = (map_typ env binders lb.FStar_Absyn_Syntax.lbtyp)
in (match (_31_701) with
| (t, env) -> begin
(

let binders' = (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _31_705 -> begin
binders
end)
in (

let _31_709 = (map_exps_with_binders env ((((binders), (lb.FStar_Absyn_Syntax.lbdef)))::(((binders'), (e2)))::[]))
in (match (_31_709) with
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

let _31_729 = (FStar_All.pipe_right tl (FStar_List.fold_left (fun _31_722 t -> (match (_31_722) with
| (tl, env) -> begin
(

let _31_726 = (map_typ env binders t)
in (match (_31_726) with
| (t, env) -> begin
(((t)::tl), (env))
end))
end)) (([]), (env))))
in (match (_31_729) with
| (tl, env) -> begin
(

let tl = (FStar_List.rev tl)
in (

let binders = (FStar_List.fold_left (fun binders lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _31_736 -> begin
binders
end)) binders bvdt_tl)
in (

let _31_740 = (map_exps env binders (FStar_List.append el ((e)::[])))
in (match (_31_740) with
| (el, env) -> begin
(((([]), ([]), (tl), (el), ([]))), (env))
end))))
end))))
end
| FStar_Absyn_Syntax.Exp_let (_31_742) -> begin
(FStar_All.failwith "impossible")
end)
in (match (_31_746) with
| (components, env) -> begin
(combine_exp e components env)
end))))
in (map_exp env binders e)))


let combine_kind = (fun k kc env -> (

let k' = (match (((k.FStar_Absyn_Syntax.n), (kc))) with
| ((FStar_Absyn_Syntax.Kind_lam (_), _)) | ((FStar_Absyn_Syntax.Kind_type, _)) | ((FStar_Absyn_Syntax.Kind_effect, _)) | ((FStar_Absyn_Syntax.Kind_unknown, _)) -> begin
(fun p -> (FStar_Util.return_all k))
end
| (FStar_Absyn_Syntax.Kind_uvar (u, _31_771), (_31_775, _31_777, _31_779, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_uvar ((u), (args)))
end
| (FStar_Absyn_Syntax.Kind_abbrev (kabr, _31_785), (_31_789, (k)::[], _31_793, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_abbrev (((((Prims.fst kabr)), (args))), (k)))
end
| (FStar_Absyn_Syntax.Kind_arrow (_31_798, _31_800), (bs, (k')::[], _31_807, _31_809)) -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (k')))
end
| _31_813 -> begin
(FStar_All.failwith "impossible")
end)
in (let _128_388 = (k' k.FStar_Absyn_Syntax.pos)
in ((_128_388), (env)))))


let combine_typ = (fun t tc env -> (

let t = (compress_typ t)
in (

let w = (fun f -> (f None t.FStar_Absyn_Syntax.pos))
in (

let t' = (match (((t.FStar_Absyn_Syntax.n), (tc))) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((FStar_Absyn_Syntax.Typ_const (_), _)) -> begin
t
end
| (FStar_Absyn_Syntax.Typ_lam (_31_838), (bs, _31_842, (t)::[], _31_846, _31_848)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (t))))
end
| (FStar_Absyn_Syntax.Typ_app (_31_852), (_31_855, _31_857, (t)::[], _31_861, (args)::[])) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_app ((t), (args))))
end
| (FStar_Absyn_Syntax.Typ_refine (_31_867), (((FStar_Util.Inr (x), _31_872))::[], _31_876, (t)::[], _31_880, _31_882)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_refine ((x), (t))))
end
| (FStar_Absyn_Syntax.Typ_fun (_31_886), (bs, _31_890, _31_892, (c)::[], _31_896)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c))))
end
| (FStar_Absyn_Syntax.Typ_uvar (x, _31_901), (_31_905, (k)::[], _31_909, _31_911, _31_913)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_uvar' ((x), (k))))
end
| (FStar_Absyn_Syntax.Typ_ascribed (_31_917), (_31_920, (k)::[], (t)::[], _31_926, _31_928)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_ascribed' ((t), (k))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_31_932, l)), (_31_938, _31_940, (t')::[], _31_944, _31_946)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_named (((t'), (l))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_31_950)), (_31_954, _31_956, (t)::[], _31_960, args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern (((t), (args))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_31_965, l, r, p)), (_31_973, _31_975, (t)::[], _31_979, _31_981)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled (((t), (l), (r), (p))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_31_985, b, r)), (_31_992, _31_994, (t)::[], _31_998, _31_1000)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_refresh_label (((t), (b), (r))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_31_1004, _31_1006, _31_1008)), (_31_1013, _31_1015, (t1)::(t2)::[], _31_1020, _31_1022)) -> begin
(let _128_429 = (let _128_428 = (let _128_427 = (let _128_426 = (FStar_Util.mk_ref false)
in ((t1), (t2), (_128_426)))
in FStar_Absyn_Syntax.Meta_slack_formula (_128_427))
in (FStar_Absyn_Syntax.mk_Typ_meta' _128_428))
in (FStar_All.pipe_left w _128_429))
end
| _31_1026 -> begin
(FStar_All.failwith "impossible")
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
| (FStar_Absyn_Syntax.Exp_uvar (uv, _31_1054), (_31_1058, _31_1060, (t)::[], _31_1064, _31_1066)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_uvar' ((uv), (t))))
end
| (FStar_Absyn_Syntax.Exp_abs (_31_1070), (bs, _31_1074, _31_1076, (e)::[], _31_1080)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_abs ((bs), (e))))
end
| (FStar_Absyn_Syntax.Exp_app (_31_1084), (_31_1087, _31_1089, _31_1091, (e)::[], args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_app ((e), (args))))
end
| (FStar_Absyn_Syntax.Exp_ascribed (_31_1098, _31_1100, l), (_31_1105, _31_1107, (t)::[], (e)::[], _31_1113)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_ascribed ((e), (t), (l))))
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_31_1117, tag)), (_31_1123, _31_1125, _31_1127, (e)::[], _31_1131)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_meta' (FStar_Absyn_Syntax.Meta_desugared (((e), (tag))))))
end
| (FStar_Absyn_Syntax.Exp_match (_31_1135, eqns), (_31_1140, [], [], (e1)::el, _31_1147)) -> begin
(

let rec mk_eqns = (fun eqns el -> (match (((eqns), (el))) with
| (((p, None, _31_1157))::eqns', (e)::el') -> begin
(let _128_459 = (mk_eqns eqns' el')
in (((p), (None), (e)))::_128_459)
end
| (((p, Some (_31_1167), _31_1170))::eqns', (w)::(e)::el') -> begin
(let _128_460 = (mk_eqns eqns' el')
in (((p), (Some (w)), (e)))::_128_460)
end
| ([], []) -> begin
[]
end
| _31_1183 -> begin
(FStar_All.failwith "impossible")
end))
in (let _128_465 = (let _128_464 = (let _128_463 = (mk_eqns eqns el)
in ((e1), (_128_463)))
in (FStar_Absyn_Syntax.mk_Exp_match _128_464))
in (FStar_All.pipe_left w _128_465)))
end
| (FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), _31_1188), (_31_1192, _31_1194, tl, el, _31_1198)) -> begin
(match ((FStar_Util.first_N (FStar_List.length lbs) el)) with
| (el, (e')::[]) -> begin
(

let lbs' = (FStar_List.map3 (fun lb t e -> (

let _31_1208 = lb
in {FStar_Absyn_Syntax.lbname = _31_1208.FStar_Absyn_Syntax.lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _31_1208.FStar_Absyn_Syntax.lbeff; FStar_Absyn_Syntax.lbdef = e})) lbs tl el)
in (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_let ((((is_rec), (lbs'))), (e')))))
end
| _31_1212 -> begin
(FStar_All.failwith "impossible")
end)
end
| _31_1214 -> begin
(FStar_All.failwith "impossible")
end)
in ((e'), (env))))))


let collect_from_typ = (fun f env t -> (let _128_589 = (reduce_typ (fun _31_1260 _31_1262 _31_1264 env _31_1267 k -> ((k), (env))) (fun _31_1242 vt _31_1245 env bvs t -> (

let env = (f env t)
in (match ((let _128_546 = (compress_typ t)
in _128_546.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
((t), (env))
end
| _31_1259 -> begin
(vt env bvs t)
end))) (fun _31_1232 _31_1234 _31_1236 env _31_1239 e -> ((e), (env))) (fun k _31_1229 env -> ((k), (env))) (fun t _31_1225 env -> ((t), (env))) (fun e _31_1221 env -> ((e), (env))) env [] t)
in (FStar_All.pipe_left Prims.snd _128_589)))




