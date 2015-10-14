
open Prims
let log = (fun s -> ())

let rec compress_typ_aux = (fun pos typ -> (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (typ) -> begin
(compress_typ_aux pos typ)
end
| _25_13 -> begin
typ
end)
end
| FStar_Absyn_Syntax.Typ_delayed (_25_15, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
typ
end
| Some (t) -> begin
(let t' = (compress_typ_aux pos t)
in (let _25_23 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) when pos -> begin
(compress_typ_aux pos t)
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _25_45); FStar_Absyn_Syntax.tk = _25_42; FStar_Absyn_Syntax.pos = _25_40; FStar_Absyn_Syntax.fvs = _25_38; FStar_Absyn_Syntax.uvs = _25_36}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (t') -> begin
(let _90_8 = (FStar_Absyn_Syntax.mk_Typ_app (t', args) None typ.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left (compress_typ_aux pos) _90_8))
end
| _25_55 -> begin
typ
end)
end
| _25_57 -> begin
typ
end))

let compress_typ = (fun typ -> (compress_typ_aux true typ))

let compress_typ_uvars = (fun typ -> (compress_typ_aux false typ))

let rec compress_exp_aux = (fun meta exp -> (match (exp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (uv, _25_64) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(compress_exp_aux meta e)
end
| _25_70 -> begin
exp
end)
end
| FStar_Absyn_Syntax.Exp_delayed (_25_72, _25_74, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
exp
end
| Some (e) -> begin
(let e' = (compress_exp_aux meta e)
in (let _25_82 = (FStar_ST.op_Colon_Equals m (Some (e')))
in e'))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _25_86)) when meta -> begin
(compress_exp_aux meta e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _25_100); FStar_Absyn_Syntax.tk = _25_97; FStar_Absyn_Syntax.pos = _25_95; FStar_Absyn_Syntax.fvs = _25_93; FStar_Absyn_Syntax.uvs = _25_91}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e') -> begin
(FStar_Absyn_Syntax.mk_Exp_app (e', args) None exp.FStar_Absyn_Syntax.pos)
end
| _25_110 -> begin
exp
end)
end
| _25_112 -> begin
exp
end))

let compress_exp = (fun e -> (compress_exp_aux true e))

let compress_exp_uvars = (fun e -> (compress_exp_aux false e))

let rec compress_kind = (fun knd -> (match (knd.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_25_117, _25_119, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
knd
end
| Some (k) -> begin
(let k' = (compress_kind k)
in (let _25_127 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k'))
end)
end
| _25_130 -> begin
knd
end))

let left = (fun ext benv btv -> (match ((ext benv (FStar_Util.Inl (btv)))) with
| (benv, FStar_Util.Inl (bvd)) -> begin
(benv, bvd)
end
| _25_139 -> begin
(FStar_All.failwith "impossible")
end))

let right = (fun ext benv bvv -> (match ((ext benv (FStar_Util.Inr (bvv)))) with
| (benv, FStar_Util.Inr (bvd)) -> begin
(benv, bvd)
end
| _25_148 -> begin
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

let push_tbinder = (fun binders _25_1 -> (match (_25_1) with
| None -> begin
binders
end
| Some (a) -> begin
(FStar_Util.Inl (a))::binders
end))

let push_vbinder = (fun binders _25_2 -> (match (_25_2) with
| None -> begin
binders
end
| Some (a) -> begin
(FStar_Util.Inr (a))::binders
end))

let bvd_to_bvar_s = (fun bvd sort -> {FStar_Absyn_Syntax.v = bvd; FStar_Absyn_Syntax.sort = sort; FStar_Absyn_Syntax.p = bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idRange})

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
(FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd Prims.list * FStar_Absyn_Syntax.typ Prims.list * FStar_Absyn_Syntax.comp Prims.list * FStar_Absyn_Syntax.arg Prims.list)

type exp_components =
(FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd Prims.list * FStar_Absyn_Syntax.typ Prims.list * FStar_Absyn_Syntax.exp Prims.list * FStar_Absyn_Syntax.arg Prims.list)

let leaf_k = (fun _25_176 -> (match (()) with
| () -> begin
([], [], [], [])
end))

let leaf_te = (fun _25_177 -> (match (()) with
| () -> begin
([], [], [], [], [])
end))

let rec reduce_kind = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k -> (let rec visit_kind = (fun env binders k -> (let k = (compress_kind k)
in (let _25_236 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_25_197) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
((leaf_k ()), env)
end
| FStar_Absyn_Syntax.Kind_uvar (_25_206, args) -> begin
(let _25_212 = (map_args map_typ map_exp env binders args)
in (match (_25_212) with
| (args, env) -> begin
(([], [], [], args), env)
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(let _25_219 = (map_kind env binders k)
in (match (_25_219) with
| (k, env) -> begin
(let _25_222 = (map_args map_typ map_exp env binders (Prims.snd kabr))
in (match (_25_222) with
| (args, env) -> begin
(([], (k)::[], [], args), env)
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _25_230 = (map_binders map_kind map_typ env binders bs)
in (match (_25_230) with
| (bs, binders, env) -> begin
(let _25_233 = (map_kind env binders k)
in (match (_25_233) with
| (k, env) -> begin
((bs, (k)::[], [], []), env)
end))
end))
end)
in (match (_25_236) with
| (components, env) -> begin
(combine_kind k components env)
end))))
and map_kind = (fun env binders k -> (map_kind' visit_kind map_typ map_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_kind env binders k)))
and map_args = (fun map_typ map_exp env binders arguments -> (let _25_270 = (FStar_List.fold_left (fun _25_254 _25_257 -> (match ((_25_254, _25_257)) with
| ((out, env), (arg, imp)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(let _25_262 = (map_typ env binders t)
in (match (_25_262) with
| (t, env) -> begin
(((FStar_Util.Inl (t), imp))::out, env)
end))
end
| FStar_Util.Inr (e) -> begin
(let _25_267 = (map_exp env binders e)
in (match (_25_267) with
| (e, env) -> begin
(((FStar_Util.Inr (e), imp))::out, env)
end))
end)
end)) ([], env) arguments)
in (match (_25_270) with
| (args', env) -> begin
((FStar_List.rev args'), env)
end)))
and map_binders = (fun map_kind map_typ env binders bs -> (let _25_301 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _25_280 b -> (match (_25_280) with
| (bs, binders, env) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(let _25_288 = (map_kind env binders a.FStar_Absyn_Syntax.sort)
in (match (_25_288) with
| (k, env) -> begin
(let binders = (push_tbinder binders (Some (a.FStar_Absyn_Syntax.v)))
in (((FStar_Util.Inl ((bvd_to_bvar_s a.FStar_Absyn_Syntax.v k)), imp))::bs, binders, env))
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _25_296 = (map_typ env binders x.FStar_Absyn_Syntax.sort)
in (match (_25_296) with
| (t, env) -> begin
(let binders = (push_vbinder binders (Some (x.FStar_Absyn_Syntax.v)))
in (((FStar_Util.Inr ((bvd_to_bvar_s x.FStar_Absyn_Syntax.v t)), imp))::bs, binders, env))
end))
end)
end)) ([], binders, env)))
in (match (_25_301) with
| (bs, binders, env) -> begin
((FStar_List.rev bs), binders, env)
end)))
and reduce_typ = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t -> (let rec map_comp = (fun env binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _25_324 = (map_typ env binders t)
in (match (_25_324) with
| (t, env) -> begin
(let _90_292 = (FStar_Absyn_Syntax.mk_Total t)
in (_90_292, env))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _25_329 = (map_typ env binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_25_329) with
| (t, env) -> begin
(let _25_332 = (map_args map_typ map_exp env binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_25_332) with
| (args, env) -> begin
(let _25_343 = (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.fold_map (fun env flag -> (match (flag) with
| FStar_Absyn_Syntax.DECREASES (arg) -> begin
(let _25_339 = (map_exp env binders arg)
in (match (_25_339) with
| (arg, env) -> begin
(env, FStar_Absyn_Syntax.DECREASES (arg))
end))
end
| f -> begin
(env, f)
end)) env))
in (match (_25_343) with
| (env, flags) -> begin
(let _90_295 = (FStar_Absyn_Syntax.mk_Comp (let _25_344 = ct
in {FStar_Absyn_Syntax.effect_name = _25_344.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = flags}))
in (_90_295, env))
end))
end))
end))
end))
and visit_typ = (fun env binders t -> (let _25_494 = (match ((let _90_299 = (compress_typ t)
in _90_299.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_delayed (_25_350) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(let _25_362 = (map_typ env binders t)
in (match (_25_362) with
| (_25_360, env) -> begin
((leaf_te ()), env)
end))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(let _25_369 = (map_typ env binders t)
in (match (_25_369) with
| (t, env) -> begin
(let _25_372 = (map_args map_typ map_exp env binders args)
in (match (_25_372) with
| (args, env) -> begin
(([], [], (t)::[], [], args), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (axs, t) -> begin
(let _25_380 = (map_binders map_kind map_typ env binders axs)
in (match (_25_380) with
| (axs, binders, env) -> begin
(let _25_383 = (map_typ env binders t)
in (match (_25_383) with
| (t, env) -> begin
((axs, [], (t)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t2) -> begin
(let _25_391 = (map_binders map_kind map_typ env binders (((FStar_Util.Inr (x), None))::[]))
in (match (_25_391) with
| (bs, binders, env) -> begin
(let _25_394 = (map_typ env binders t2)
in (match (_25_394) with
| (t2, env) -> begin
((bs, [], (t2)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let _25_402 = (map_binders map_kind map_typ env binders bs)
in (match (_25_402) with
| (bs, binders, env) -> begin
(let _25_405 = (map_comp env binders c)
in (match (_25_405) with
| (c, env) -> begin
((bs, [], [], (c)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
(let _25_412 = (map_typ env binders t)
in (match (_25_412) with
| (t, env) -> begin
(let _25_415 = (map_kind env binders k)
in (match (_25_415) with
| (k, env) -> begin
(([], (k)::[], (t)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_25_417, k) -> begin
(let _25_423 = (map_kind env binders k)
in (match (_25_423) with
| (k, env) -> begin
(([], (k)::[], [], [], []), env)
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
(let _25_432 = (map_typ env binders t1)
in (match (_25_432) with
| (t1, env) -> begin
(let _25_435 = (map_typ env binders t2)
in (match (_25_435) with
| (t2, env) -> begin
(([], [], (t1)::(t2)::[], [], []), env)
end))
end))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(let _25_460 = (map_typ env binders t)
in (match (_25_460) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
(let _25_468 = (map_typ env binders t)
in (match (_25_468) with
| (t, env) -> begin
(let _25_491 = (FStar_List.fold_left (fun _25_471 arg -> (match (_25_471) with
| (pats, env) -> begin
(match (arg) with
| (FStar_Util.Inl (t), _25_476) -> begin
(let _25_480 = (map_typ env binders t)
in (match (_25_480) with
| (t, env) -> begin
(((FStar_Util.Inl (t), None))::pats, env)
end))
end
| (FStar_Util.Inr (e), _25_484) -> begin
(let _25_488 = (map_exp env binders e)
in (match (_25_488) with
| (e, env) -> begin
(((FStar_Util.Inr (e), None))::pats, env)
end))
end)
end)) ([], env) ps)
in (match (_25_491) with
| (pats, env) -> begin
(([], [], (t)::[], [], (FStar_List.rev pats)), env)
end))
end))
end)
in (match (_25_494) with
| (components, env) -> begin
(combine_typ t components env)
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (map_typ' map_kind visit_typ map_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_typ env binders t)))
and reduce_exp = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e -> (let rec map_exps = (fun env binders el -> (let _25_532 = (FStar_List.fold_left (fun _25_525 e -> (match (_25_525) with
| (out, env) -> begin
(let _25_529 = (map_exp env binders e)
in (match (_25_529) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_25_532) with
| (el, env) -> begin
((FStar_List.rev el), env)
end)))
and map_exps_with_binders = (fun env el -> (let _25_546 = (FStar_List.fold_left (fun _25_537 _25_540 -> (match ((_25_537, _25_540)) with
| ((out, env), (b, e)) -> begin
(let _25_543 = (map_exp env b e)
in (match (_25_543) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_25_546) with
| (el, env) -> begin
((FStar_List.rev el), env)
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (map_exp' map_kind map_typ visit_exp env binders e))
and visit_exp = (fun env binders e -> (let e = (compress_exp_uvars e)
in (let _25_733 = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_25_561) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _25_565)) -> begin
(let _25_571 = (map_exp env binders e)
in (match (_25_571) with
| (e, env) -> begin
(([], [], [], (e)::[], []), env)
end))
end
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
((leaf_te ()), env)
end
| FStar_Absyn_Syntax.Exp_uvar (_25_582, t) -> begin
(let _25_588 = (map_typ env binders t)
in (match (_25_588) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(let _25_596 = (map_binders map_kind map_typ env binders bs)
in (match (_25_596) with
| (bs, binders, env) -> begin
(let _25_599 = (map_exp env binders e)
in (match (_25_599) with
| (e, env) -> begin
((bs, [], [], (e)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(let _25_606 = (map_exp env binders e)
in (match (_25_606) with
| (e, env) -> begin
(let _25_609 = (map_args map_typ map_exp env binders args)
in (match (_25_609) with
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
| FStar_Absyn_Syntax.Pat_cons (_25_637, _25_639, pats) -> begin
(FStar_List.fold_left (fun b _25_647 -> (match (_25_647) with
| (p, _25_646) -> begin
(pat_binders b p)
end)) b pats)
end
| FStar_Absyn_Syntax.Pat_disj (p::_25_649) -> begin
(pat_binders b p)
end
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end))
in (let branches = (FStar_All.pipe_right pl (FStar_List.collect (fun _25_658 -> (match (_25_658) with
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
in (let _25_666 = (map_exps_with_binders env (((binders, e1))::branches))
in (match (_25_666) with
| (el, env) -> begin
(([], [], [], el, []), env)
end))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _25_670) -> begin
(let _25_675 = (map_typ env binders t)
in (match (_25_675) with
| (t, env) -> begin
(let _25_678 = (map_exp env binders e)
in (match (_25_678) with
| (e, env) -> begin
(([], [], (t)::[], (e)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, lb::[]), e2) -> begin
(let _25_688 = (map_typ env binders lb.FStar_Absyn_Syntax.lbtyp)
in (match (_25_688) with
| (t, env) -> begin
(let binders' = (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _25_692 -> begin
binders
end)
in (let _25_696 = (map_exps_with_binders env (((binders, lb.FStar_Absyn_Syntax.lbdef))::((binders', e2))::[]))
in (match (_25_696) with
| (el, env) -> begin
(([], [], (t)::[], el, []), env)
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((true, bvdt_tl), e) -> begin
(let tl = (FStar_List.map (fun lb -> lb.FStar_Absyn_Syntax.lbtyp) bvdt_tl)
in (let el = (FStar_List.map (fun lb -> lb.FStar_Absyn_Syntax.lbdef) bvdt_tl)
in (let _25_716 = (FStar_All.pipe_right tl (FStar_List.fold_left (fun _25_709 t -> (match (_25_709) with
| (tl, env) -> begin
(let _25_713 = (map_typ env binders t)
in (match (_25_713) with
| (t, env) -> begin
((t)::tl, env)
end))
end)) ([], env)))
in (match (_25_716) with
| (tl, env) -> begin
(let tl = (FStar_List.rev tl)
in (let binders = (FStar_List.fold_left (fun binders lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _25_723 -> begin
binders
end)) binders bvdt_tl)
in (let _25_727 = (map_exps env binders (FStar_List.append el ((e)::[])))
in (match (_25_727) with
| (el, env) -> begin
(([], [], tl, el, []), env)
end))))
end))))
end
| FStar_Absyn_Syntax.Exp_let (_25_729) -> begin
(FStar_All.failwith "impossible")
end)
in (match (_25_733) with
| (components, env) -> begin
(combine_exp e components env)
end))))
in (map_exp env binders e)))

let combine_kind = (fun k kc env -> (let k' = (match ((k.FStar_Absyn_Syntax.n, kc)) with
| ((FStar_Absyn_Syntax.Kind_lam (_), _)) | ((FStar_Absyn_Syntax.Kind_type, _)) | ((FStar_Absyn_Syntax.Kind_effect, _)) | ((FStar_Absyn_Syntax.Kind_unknown, _)) -> begin
(fun p -> (FStar_Util.return_all k))
end
| (FStar_Absyn_Syntax.Kind_uvar (u, _25_758), (_25_762, _25_764, _25_766, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_uvar (u, args))
end
| (FStar_Absyn_Syntax.Kind_abbrev (kabr, _25_772), (_25_776, k::[], _25_780, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_abbrev (((Prims.fst kabr), args), k))
end
| (FStar_Absyn_Syntax.Kind_arrow (_25_785, _25_787), (bs, k'::[], _25_794, _25_796)) -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow (bs, k'))
end
| _25_800 -> begin
(FStar_All.failwith "impossible")
end)
in (let _90_382 = (k' k.FStar_Absyn_Syntax.pos)
in (_90_382, env))))

let combine_typ = (fun t tc env -> (let t = (compress_typ t)
in (let w = (fun f -> (f None t.FStar_Absyn_Syntax.pos))
in (let t' = (match ((t.FStar_Absyn_Syntax.n, tc)) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((FStar_Absyn_Syntax.Typ_const (_), _)) -> begin
t
end
| (FStar_Absyn_Syntax.Typ_lam (_25_825), (bs, _25_829, t::[], _25_833, _25_835)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
end
| (FStar_Absyn_Syntax.Typ_app (_25_839), (_25_842, _25_844, t::[], _25_848, args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_app (t, args)))
end
| (FStar_Absyn_Syntax.Typ_refine (_25_853), ((FStar_Util.Inr (x), _25_858)::[], _25_862, t::[], _25_866, _25_868)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_refine (x, t)))
end
| (FStar_Absyn_Syntax.Typ_fun (_25_872), (bs, _25_876, _25_878, c::[], _25_882)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_fun (bs, c)))
end
| (FStar_Absyn_Syntax.Typ_uvar (x, _25_887), (_25_891, k::[], _25_895, _25_897, _25_899)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_uvar' (x, k)))
end
| (FStar_Absyn_Syntax.Typ_ascribed (_25_903), (_25_906, k::[], t::[], _25_912, _25_914)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_ascribed' (t, k)))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_25_918, l)), (_25_924, _25_926, t'::[], _25_930, _25_932)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_named ((t', l)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_25_936)), (_25_940, _25_942, t::[], _25_946, args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern ((t, args)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_25_951, l, r, p)), (_25_959, _25_961, t::[], _25_965, _25_967)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_25_971, b, r)), (_25_978, _25_980, t::[], _25_984, _25_986)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_25_990, _25_992, _25_994)), (_25_999, _25_1001, t1::t2::[], _25_1006, _25_1008)) -> begin
(let _90_423 = (let _90_422 = (let _90_421 = (let _90_420 = (FStar_Util.mk_ref false)
in (t1, t2, _90_420))
in FStar_Absyn_Syntax.Meta_slack_formula (_90_421))
in (FStar_Absyn_Syntax.mk_Typ_meta' _90_422))
in (FStar_All.pipe_left w _90_423))
end
| _25_1012 -> begin
(FStar_All.failwith "impossible")
end)
in (t', env)))))

let combine_exp = (fun e ec env -> (let e = (compress_exp e)
in (let w = (fun f -> (f None e.FStar_Absyn_Syntax.pos))
in (let e' = (match ((e.FStar_Absyn_Syntax.n, ec)) with
| ((FStar_Absyn_Syntax.Exp_bvar (_), _)) | ((FStar_Absyn_Syntax.Exp_fvar (_), _)) | ((FStar_Absyn_Syntax.Exp_constant (_), _)) -> begin
e
end
| (FStar_Absyn_Syntax.Exp_uvar (uv, _25_1040), (_25_1044, _25_1046, t::[], _25_1050, _25_1052)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t)))
end
| (FStar_Absyn_Syntax.Exp_abs (_25_1056), (bs, _25_1060, _25_1062, e::[], _25_1066)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_abs (bs, e)))
end
| (FStar_Absyn_Syntax.Exp_app (_25_1070), (_25_1073, _25_1075, _25_1077, e::[], args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_app (e, args)))
end
| (FStar_Absyn_Syntax.Exp_ascribed (_25_1084, _25_1086, l), (_25_1091, _25_1093, t::[], e::[], _25_1099)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, l)))
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_25_1103, tag)), (_25_1109, _25_1111, _25_1113, e::[], _25_1117)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_meta' (FStar_Absyn_Syntax.Meta_desugared ((e, tag)))))
end
| (FStar_Absyn_Syntax.Exp_match (_25_1121, eqns), (_25_1126, [], [], e1::el, _25_1133)) -> begin
(let rec mk_eqns = (fun eqns el -> (match ((eqns, el)) with
| ((p, None, _25_1143)::eqns', e::el') -> begin
(let _90_453 = (mk_eqns eqns' el')
in ((p, None, e))::_90_453)
end
| ((p, Some (_25_1153), _25_1156)::eqns', w::e::el') -> begin
(let _90_454 = (mk_eqns eqns' el')
in ((p, Some (w), e))::_90_454)
end
| ([], []) -> begin
[]
end
| _25_1169 -> begin
(FStar_All.failwith "impossible")
end))
in (let _90_459 = (let _90_458 = (let _90_457 = (mk_eqns eqns el)
in (e1, _90_457))
in (FStar_Absyn_Syntax.mk_Exp_match _90_458))
in (FStar_All.pipe_left w _90_459)))
end
| (FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), _25_1174), (_25_1178, _25_1180, tl, el, _25_1184)) -> begin
(match ((FStar_Util.first_N (FStar_List.length lbs) el)) with
| (el, e'::[]) -> begin
(let lbs' = (FStar_List.map3 (fun lb t e -> (let _25_1194 = lb
in {FStar_Absyn_Syntax.lbname = _25_1194.FStar_Absyn_Syntax.lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _25_1194.FStar_Absyn_Syntax.lbeff; FStar_Absyn_Syntax.lbdef = e})) lbs tl el)
in (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs'), e'))))
end
| _25_1198 -> begin
(FStar_All.failwith "impossible")
end)
end
| _25_1200 -> begin
(FStar_All.failwith "impossible")
end)
in (e', env)))))

let collect_from_typ = (fun f env t -> (let _90_583 = (reduce_typ (fun _25_1246 _25_1248 _25_1250 env _25_1253 k -> (k, env)) (fun _25_1228 vt _25_1231 env bvs t -> (let env = (f env t)
in (match ((let _90_540 = (compress_typ t)
in _90_540.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(t, env)
end
| _25_1245 -> begin
(vt env bvs t)
end))) (fun _25_1218 _25_1220 _25_1222 env _25_1225 e -> (e, env)) (fun k _25_1215 env -> (k, env)) (fun t _25_1211 env -> (t, env)) (fun e _25_1207 env -> (e, env)) env [] t)
in (FStar_All.pipe_left Prims.snd _90_583)))
