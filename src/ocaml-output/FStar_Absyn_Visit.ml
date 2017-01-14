
open Prims

let log = (fun s -> ())


let rec compress_typ_aux : Prims.bool  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun pos typ -> (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (typ) -> begin
(compress_typ_aux pos typ)
end
| _32_11 -> begin
typ
end)
end
| FStar_Absyn_Syntax.Typ_delayed (_32_13, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
typ
end
| Some (t) -> begin
(

let t' = (compress_typ_aux pos t)
in (

let _32_21 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) when pos -> begin
(compress_typ_aux pos t)
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _32_43); FStar_Absyn_Syntax.tk = _32_40; FStar_Absyn_Syntax.pos = _32_38; FStar_Absyn_Syntax.fvs = _32_36; FStar_Absyn_Syntax.uvs = _32_34}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (t') -> begin
(let _133_8 = (FStar_Absyn_Syntax.mk_Typ_app ((t'), (args)) None typ.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left (compress_typ_aux pos) _133_8))
end
| _32_53 -> begin
typ
end)
end
| _32_55 -> begin
typ
end))


let compress_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun typ -> (compress_typ_aux true typ))


let compress_typ_uvars : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun typ -> (compress_typ_aux false typ))


let rec compress_exp_aux : Prims.bool  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun meta exp -> (match (exp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (uv, _32_62) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(compress_exp_aux meta e)
end
| _32_68 -> begin
exp
end)
end
| FStar_Absyn_Syntax.Exp_delayed (_32_70, _32_72, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
exp
end
| Some (e) -> begin
(

let e' = (compress_exp_aux meta e)
in (

let _32_80 = (FStar_ST.op_Colon_Equals m (Some (e')))
in e'))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _32_84)) when meta -> begin
(compress_exp_aux meta e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _32_98); FStar_Absyn_Syntax.tk = _32_95; FStar_Absyn_Syntax.pos = _32_93; FStar_Absyn_Syntax.fvs = _32_91; FStar_Absyn_Syntax.uvs = _32_89}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e') -> begin
(FStar_Absyn_Syntax.mk_Exp_app ((e'), (args)) None exp.FStar_Absyn_Syntax.pos)
end
| _32_108 -> begin
exp
end)
end
| _32_110 -> begin
exp
end))


let compress_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (compress_exp_aux true e))


let compress_exp_uvars : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (compress_exp_aux false e))


let rec compress_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun knd -> (match (knd.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_32_115, _32_117, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
knd
end
| Some (k) -> begin
(

let k' = (compress_kind k)
in (

let _32_125 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k'))
end)
end
| _32_128 -> begin
knd
end))


let left = (fun ext benv btv -> (match ((ext benv (FStar_Util.Inl (btv)))) with
| (benv, FStar_Util.Inl (bvd)) -> begin
((benv), (bvd))
end
| _32_137 -> begin
(failwith "impossible")
end))


let right = (fun ext benv bvv -> (match ((ext benv (FStar_Util.Inr (bvv)))) with
| (benv, FStar_Util.Inr (bvd)) -> begin
((benv), (bvd))
end
| _32_146 -> begin
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


let push_tbinder = (fun binders uu___14 -> (match (uu___14) with
| None -> begin
binders
end
| Some (a) -> begin
(FStar_Util.Inl (a))::binders
end))


let push_vbinder = (fun binders uu___15 -> (match (uu___15) with
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


let leaf_k = (fun _32_174 -> (match (()) with
| () -> begin
(([]), ([]), ([]), ([]))
end))


let leaf_te = (fun _32_175 -> (match (()) with
| () -> begin
(([]), ([]), ([]), ([]), ([]))
end))


let rec reduce_kind = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k -> (

let rec visit_kind = (fun env binders k -> (

let k = (compress_kind k)
in (

let _32_234 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_32_195) -> begin
(failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
(((leaf_k ())), (env))
end
| FStar_Absyn_Syntax.Kind_uvar (_32_204, args) -> begin
(

let _32_210 = (map_args map_typ map_exp env binders args)
in (match (_32_210) with
| (args, env) -> begin
(((([]), ([]), ([]), (args))), (env))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(

let _32_217 = (map_kind env binders k)
in (match (_32_217) with
| (k, env) -> begin
(

let _32_220 = (map_args map_typ map_exp env binders (Prims.snd kabr))
in (match (_32_220) with
| (args, env) -> begin
(((([]), ((k)::[]), ([]), (args))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(

let _32_228 = (map_binders map_kind map_typ env binders bs)
in (match (_32_228) with
| (bs, binders, env) -> begin
(

let _32_231 = (map_kind env binders k)
in (match (_32_231) with
| (k, env) -> begin
((((bs), ((k)::[]), ([]), ([]))), (env))
end))
end))
end)
in (match (_32_234) with
| (components, env) -> begin
(combine_kind k components env)
end))))
and map_kind = (fun env binders k -> (map_kind' visit_kind map_typ map_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_kind env binders k)))
and map_args = (fun map_typ map_exp env binders arguments -> (

let _32_268 = (FStar_List.fold_left (fun _32_252 _32_255 -> (match (((_32_252), (_32_255))) with
| ((out, env), (arg, imp)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(

let _32_260 = (map_typ env binders t)
in (match (_32_260) with
| (t, env) -> begin
(((((FStar_Util.Inl (t)), (imp)))::out), (env))
end))
end
| FStar_Util.Inr (e) -> begin
(

let _32_265 = (map_exp env binders e)
in (match (_32_265) with
| (e, env) -> begin
(((((FStar_Util.Inr (e)), (imp)))::out), (env))
end))
end)
end)) (([]), (env)) arguments)
in (match (_32_268) with
| (args', env) -> begin
(((FStar_List.rev args')), (env))
end)))
and map_binders = (fun map_kind map_typ env binders bs -> (

let _32_299 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _32_278 b -> (match (_32_278) with
| (bs, binders, env) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(

let _32_286 = (map_kind env binders a.FStar_Absyn_Syntax.sort)
in (match (_32_286) with
| (k, env) -> begin
(

let binders = (push_tbinder binders (Some (a.FStar_Absyn_Syntax.v)))
in (((((FStar_Util.Inl ((bvd_to_bvar_s a.FStar_Absyn_Syntax.v k))), (imp)))::bs), (binders), (env)))
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(

let _32_294 = (map_typ env binders x.FStar_Absyn_Syntax.sort)
in (match (_32_294) with
| (t, env) -> begin
(

let binders = (push_vbinder binders (Some (x.FStar_Absyn_Syntax.v)))
in (((((FStar_Util.Inr ((bvd_to_bvar_s x.FStar_Absyn_Syntax.v t))), (imp)))::bs), (binders), (env)))
end))
end)
end)) (([]), (binders), (env))))
in (match (_32_299) with
| (bs, binders, env) -> begin
(((FStar_List.rev bs)), (binders), (env))
end)))
and reduce_typ = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t -> (

let rec map_comp = (fun env binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(

let _32_322 = (map_typ env binders t)
in (match (_32_322) with
| (t, env) -> begin
(let _133_292 = (FStar_Absyn_Syntax.mk_Total t)
in ((_133_292), (env)))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(

let _32_327 = (map_typ env binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_32_327) with
| (t, env) -> begin
(

let _32_330 = (map_args map_typ map_exp env binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_32_330) with
| (args, env) -> begin
(

let _32_341 = (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.fold_map (fun env flag -> (match (flag) with
| FStar_Absyn_Syntax.DECREASES (arg) -> begin
(

let _32_337 = (map_exp env binders arg)
in (match (_32_337) with
| (arg, env) -> begin
((env), (FStar_Absyn_Syntax.DECREASES (arg)))
end))
end
| f -> begin
((env), (f))
end)) env))
in (match (_32_341) with
| (env, flags) -> begin
(let _133_295 = (FStar_Absyn_Syntax.mk_Comp (

let _32_342 = ct
in {FStar_Absyn_Syntax.effect_name = _32_342.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = flags}))
in ((_133_295), (env)))
end))
end))
end))
end))
and visit_typ = (fun env binders t -> (

let _32_505 = (match ((let _133_299 = (compress_typ t)
in _133_299.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_delayed (_32_348) -> begin
(failwith "Impossible")
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(

let _32_360 = (map_typ env binders t)
in (match (_32_360) with
| (_32_358, env) -> begin
(((leaf_te ())), (env))
end))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(

let _32_367 = (map_typ env binders t)
in (match (_32_367) with
| (t, env) -> begin
(

let _32_370 = (map_args map_typ map_exp env binders args)
in (match (_32_370) with
| (args, env) -> begin
(((([]), ([]), ((t)::[]), ([]), ((args)::[]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (axs, t) -> begin
(

let _32_378 = (map_binders map_kind map_typ env binders axs)
in (match (_32_378) with
| (axs, binders, env) -> begin
(

let _32_381 = (map_typ env binders t)
in (match (_32_381) with
| (t, env) -> begin
((((axs), ([]), ((t)::[]), ([]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t2) -> begin
(

let _32_389 = (map_binders map_kind map_typ env binders ((((FStar_Util.Inr (x)), (None)))::[]))
in (match (_32_389) with
| (bs, binders, env) -> begin
(

let _32_392 = (map_typ env binders t2)
in (match (_32_392) with
| (t2, env) -> begin
((((bs), ([]), ((t2)::[]), ([]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(

let _32_400 = (map_binders map_kind map_typ env binders bs)
in (match (_32_400) with
| (bs, binders, env) -> begin
(

let _32_403 = (map_comp env binders c)
in (match (_32_403) with
| (c, env) -> begin
((((bs), ([]), ([]), ((c)::[]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
(

let _32_410 = (map_typ env binders t)
in (match (_32_410) with
| (t, env) -> begin
(

let _32_413 = (map_kind env binders k)
in (match (_32_413) with
| (k, env) -> begin
(((([]), ((k)::[]), ((t)::[]), ([]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_32_415, k) -> begin
(

let _32_421 = (map_kind env binders k)
in (match (_32_421) with
| (k, env) -> begin
(((([]), ((k)::[]), ([]), ([]), ([]))), (env))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
(

let _32_430 = (map_typ env binders t1)
in (match (_32_430) with
| (t1, env) -> begin
(

let _32_433 = (map_typ env binders t2)
in (match (_32_433) with
| (t2, env) -> begin
(((([]), ([]), ((t1)::(t2)::[]), ([]), ([]))), (env))
end))
end))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(

let _32_458 = (map_typ env binders t)
in (match (_32_458) with
| (t, env) -> begin
(((([]), ([]), ((t)::[]), ([]), ([]))), (env))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
(

let _32_466 = (map_typ env binders t)
in (match (_32_466) with
| (t, env) -> begin
(

let map_pats = (fun env pats -> (

let _32_492 = (FStar_List.fold_left (fun _32_472 arg -> (match (_32_472) with
| (pats, env) -> begin
(match (arg) with
| (FStar_Util.Inl (t), _32_477) -> begin
(

let _32_481 = (map_typ env binders t)
in (match (_32_481) with
| (t, env) -> begin
(((((FStar_Util.Inl (t)), (None)))::pats), (env))
end))
end
| (FStar_Util.Inr (e), _32_485) -> begin
(

let _32_489 = (map_exp env binders e)
in (match (_32_489) with
| (e, env) -> begin
(((((FStar_Util.Inr (e)), (None)))::pats), (env))
end))
end)
end)) (([]), (env)) pats)
in (match (_32_492) with
| (pats, env) -> begin
(((FStar_List.rev pats)), (env))
end)))
in (

let _32_502 = (FStar_List.fold_left (fun _32_495 pats -> (match (_32_495) with
| (out, env) -> begin
(

let _32_499 = (map_pats env pats)
in (match (_32_499) with
| (pats, env) -> begin
(((pats)::out), (env))
end))
end)) (([]), (env)) ps)
in (match (_32_502) with
| (pats, env) -> begin
(((([]), ([]), ((t)::[]), ([]), ((FStar_List.rev pats)))), (env))
end)))
end))
end)
in (match (_32_505) with
| (components, env) -> begin
(combine_typ t components env)
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (map_typ' map_kind visit_typ map_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_typ env binders t)))
and reduce_exp = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e -> (

let rec map_exps = (fun env binders el -> (

let _32_543 = (FStar_List.fold_left (fun _32_536 e -> (match (_32_536) with
| (out, env) -> begin
(

let _32_540 = (map_exp env binders e)
in (match (_32_540) with
| (e, env) -> begin
(((e)::out), (env))
end))
end)) (([]), (env)) el)
in (match (_32_543) with
| (el, env) -> begin
(((FStar_List.rev el)), (env))
end)))
and map_exps_with_binders = (fun env el -> (

let _32_557 = (FStar_List.fold_left (fun _32_548 _32_551 -> (match (((_32_548), (_32_551))) with
| ((out, env), (b, e)) -> begin
(

let _32_554 = (map_exp env b e)
in (match (_32_554) with
| (e, env) -> begin
(((e)::out), (env))
end))
end)) (([]), (env)) el)
in (match (_32_557) with
| (el, env) -> begin
(((FStar_List.rev el)), (env))
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (map_exp' map_kind map_typ visit_exp env binders e))
and visit_exp = (fun env binders e -> (

let e = (compress_exp_uvars e)
in (

let _32_744 = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_32_572) -> begin
(failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _32_576)) -> begin
(

let _32_582 = (map_exp env binders e)
in (match (_32_582) with
| (e, env) -> begin
(((([]), ([]), ([]), ((e)::[]), ([]))), (env))
end))
end
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(((leaf_te ())), (env))
end
| FStar_Absyn_Syntax.Exp_uvar (_32_593, t) -> begin
(

let _32_599 = (map_typ env binders t)
in (match (_32_599) with
| (t, env) -> begin
(((([]), ([]), ((t)::[]), ([]), ([]))), (env))
end))
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(

let _32_607 = (map_binders map_kind map_typ env binders bs)
in (match (_32_607) with
| (bs, binders, env) -> begin
(

let _32_610 = (map_exp env binders e)
in (match (_32_610) with
| (e, env) -> begin
((((bs), ([]), ([]), ((e)::[]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(

let _32_617 = (map_exp env binders e)
in (match (_32_617) with
| (e, env) -> begin
(

let _32_620 = (map_args map_typ map_exp env binders args)
in (match (_32_620) with
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
| FStar_Absyn_Syntax.Pat_cons (_32_648, _32_650, pats) -> begin
(FStar_List.fold_left (fun b _32_658 -> (match (_32_658) with
| (p, _32_657) -> begin
(pat_binders b p)
end)) b pats)
end
| FStar_Absyn_Syntax.Pat_disj ((p)::_32_660) -> begin
(pat_binders b p)
end
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(failwith "impossible")
end))
in (

let branches = (FStar_All.pipe_right pl (FStar_List.collect (fun _32_669 -> (match (_32_669) with
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

let _32_677 = (map_exps_with_binders env ((((binders), (e1)))::branches))
in (match (_32_677) with
| (el, env) -> begin
(((([]), ([]), ([]), (el), ([]))), (env))
end))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _32_681) -> begin
(

let _32_686 = (map_typ env binders t)
in (match (_32_686) with
| (t, env) -> begin
(

let _32_689 = (map_exp env binders e)
in (match (_32_689) with
| (e, env) -> begin
(((([]), ([]), ((t)::[]), ((e)::[]), ([]))), (env))
end))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, (lb)::[]), e2) -> begin
(

let _32_699 = (map_typ env binders lb.FStar_Absyn_Syntax.lbtyp)
in (match (_32_699) with
| (t, env) -> begin
(

let binders' = (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _32_703 -> begin
binders
end)
in (

let _32_707 = (map_exps_with_binders env ((((binders), (lb.FStar_Absyn_Syntax.lbdef)))::(((binders'), (e2)))::[]))
in (match (_32_707) with
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

let _32_727 = (FStar_All.pipe_right tl (FStar_List.fold_left (fun _32_720 t -> (match (_32_720) with
| (tl, env) -> begin
(

let _32_724 = (map_typ env binders t)
in (match (_32_724) with
| (t, env) -> begin
(((t)::tl), (env))
end))
end)) (([]), (env))))
in (match (_32_727) with
| (tl, env) -> begin
(

let tl = (FStar_List.rev tl)
in (

let binders = (FStar_List.fold_left (fun binders lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _32_734 -> begin
binders
end)) binders bvdt_tl)
in (

let _32_738 = (map_exps env binders (FStar_List.append el ((e)::[])))
in (match (_32_738) with
| (el, env) -> begin
(((([]), ([]), (tl), (el), ([]))), (env))
end))))
end))))
end
| FStar_Absyn_Syntax.Exp_let (_32_740) -> begin
(failwith "impossible")
end)
in (match (_32_744) with
| (components, env) -> begin
(combine_exp e components env)
end))))
in (map_exp env binders e)))


let combine_kind = (fun k kc env -> (

let k' = (match (((k.FStar_Absyn_Syntax.n), (kc))) with
| ((FStar_Absyn_Syntax.Kind_lam (_), _)) | ((FStar_Absyn_Syntax.Kind_type, _)) | ((FStar_Absyn_Syntax.Kind_effect, _)) | ((FStar_Absyn_Syntax.Kind_unknown, _)) -> begin
(fun p -> (FStar_Util.return_all k))
end
| (FStar_Absyn_Syntax.Kind_uvar (u, _32_769), (_32_773, _32_775, _32_777, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_uvar ((u), (args)))
end
| (FStar_Absyn_Syntax.Kind_abbrev (kabr, _32_783), (_32_787, (k)::[], _32_791, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_abbrev (((((Prims.fst kabr)), (args))), (k)))
end
| (FStar_Absyn_Syntax.Kind_arrow (_32_796, _32_798), (bs, (k')::[], _32_805, _32_807)) -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (k')))
end
| _32_811 -> begin
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
| (FStar_Absyn_Syntax.Typ_lam (_32_836), (bs, _32_840, (t)::[], _32_844, _32_846)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (t))))
end
| (FStar_Absyn_Syntax.Typ_app (_32_850), (_32_853, _32_855, (t)::[], _32_859, (args)::[])) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_app ((t), (args))))
end
| (FStar_Absyn_Syntax.Typ_refine (_32_865), (((FStar_Util.Inr (x), _32_870))::[], _32_874, (t)::[], _32_878, _32_880)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_refine ((x), (t))))
end
| (FStar_Absyn_Syntax.Typ_fun (_32_884), (bs, _32_888, _32_890, (c)::[], _32_894)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c))))
end
| (FStar_Absyn_Syntax.Typ_uvar (x, _32_899), (_32_903, (k)::[], _32_907, _32_909, _32_911)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_uvar' ((x), (k))))
end
| (FStar_Absyn_Syntax.Typ_ascribed (_32_915), (_32_918, (k)::[], (t)::[], _32_924, _32_926)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_ascribed' ((t), (k))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_32_930, l)), (_32_936, _32_938, (t')::[], _32_942, _32_944)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_named (((t'), (l))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_32_948)), (_32_952, _32_954, (t)::[], _32_958, args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern (((t), (args))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_32_963, l, r, p)), (_32_971, _32_973, (t)::[], _32_977, _32_979)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled (((t), (l), (r), (p))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_32_983, b, r)), (_32_990, _32_992, (t)::[], _32_996, _32_998)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_refresh_label (((t), (b), (r))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_32_1002, _32_1004, _32_1006)), (_32_1011, _32_1013, (t1)::(t2)::[], _32_1018, _32_1020)) -> begin
(let _133_429 = (let _133_428 = (let _133_427 = (let _133_426 = (FStar_Util.mk_ref false)
in ((t1), (t2), (_133_426)))
in FStar_Absyn_Syntax.Meta_slack_formula (_133_427))
in (FStar_Absyn_Syntax.mk_Typ_meta' _133_428))
in (FStar_All.pipe_left w _133_429))
end
| _32_1024 -> begin
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
| (FStar_Absyn_Syntax.Exp_uvar (uv, _32_1052), (_32_1056, _32_1058, (t)::[], _32_1062, _32_1064)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_uvar' ((uv), (t))))
end
| (FStar_Absyn_Syntax.Exp_abs (_32_1068), (bs, _32_1072, _32_1074, (e)::[], _32_1078)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_abs ((bs), (e))))
end
| (FStar_Absyn_Syntax.Exp_app (_32_1082), (_32_1085, _32_1087, _32_1089, (e)::[], args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_app ((e), (args))))
end
| (FStar_Absyn_Syntax.Exp_ascribed (_32_1096, _32_1098, l), (_32_1103, _32_1105, (t)::[], (e)::[], _32_1111)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_ascribed ((e), (t), (l))))
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_32_1115, tag)), (_32_1121, _32_1123, _32_1125, (e)::[], _32_1129)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_meta' (FStar_Absyn_Syntax.Meta_desugared (((e), (tag))))))
end
| (FStar_Absyn_Syntax.Exp_match (_32_1133, eqns), (_32_1138, [], [], (e1)::el, _32_1145)) -> begin
(

let rec mk_eqns = (fun eqns el -> (match (((eqns), (el))) with
| (((p, None, _32_1155))::eqns', (e)::el') -> begin
(let _133_459 = (mk_eqns eqns' el')
in (((p), (None), (e)))::_133_459)
end
| (((p, Some (_32_1165), _32_1168))::eqns', (w)::(e)::el') -> begin
(let _133_460 = (mk_eqns eqns' el')
in (((p), (Some (w)), (e)))::_133_460)
end
| ([], []) -> begin
[]
end
| _32_1181 -> begin
(failwith "impossible")
end))
in (let _133_465 = (let _133_464 = (let _133_463 = (mk_eqns eqns el)
in ((e1), (_133_463)))
in (FStar_Absyn_Syntax.mk_Exp_match _133_464))
in (FStar_All.pipe_left w _133_465)))
end
| (FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), _32_1186), (_32_1190, _32_1192, tl, el, _32_1196)) -> begin
(match ((FStar_Util.first_N (FStar_List.length lbs) el)) with
| (el, (e')::[]) -> begin
(

let lbs' = (FStar_List.map3 (fun lb t e -> (

let _32_1206 = lb
in {FStar_Absyn_Syntax.lbname = _32_1206.FStar_Absyn_Syntax.lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _32_1206.FStar_Absyn_Syntax.lbeff; FStar_Absyn_Syntax.lbdef = e})) lbs tl el)
in (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_let ((((is_rec), (lbs'))), (e')))))
end
| _32_1210 -> begin
(failwith "impossible")
end)
end
| _32_1212 -> begin
(failwith "impossible")
end)
in ((e'), (env))))))


let collect_from_typ = (fun f env t -> (let _133_589 = (reduce_typ (fun _32_1258 _32_1260 _32_1262 env _32_1265 k -> ((k), (env))) (fun _32_1240 vt _32_1243 env bvs t -> (

let env = (f env t)
in (match ((let _133_546 = (compress_typ t)
in _133_546.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
((t), (env))
end
| _32_1257 -> begin
(vt env bvs t)
end))) (fun _32_1230 _32_1232 _32_1234 env _32_1237 e -> ((e), (env))) (fun k _32_1227 env -> ((k), (env))) (fun t _32_1223 env -> ((t), (env))) (fun e _32_1219 env -> ((e), (env))) env [] t)
in (FStar_All.pipe_left Prims.snd _133_589)))




