
let log = (fun s -> ())

let rec compress_typ_aux = (fun pos typ -> (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (typ) -> begin
(compress_typ_aux pos typ)
end
| _24_13 -> begin
typ
end)
end
| FStar_Absyn_Syntax.Typ_delayed (_24_15, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
typ
end
| Some (t) -> begin
(let t' = (compress_typ_aux pos t)
in (let _24_23 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) when pos -> begin
(compress_typ_aux pos t)
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _24_45); FStar_Absyn_Syntax.tk = _24_42; FStar_Absyn_Syntax.pos = _24_40; FStar_Absyn_Syntax.fvs = _24_38; FStar_Absyn_Syntax.uvs = _24_36}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (t') -> begin
(let _90_8 = (FStar_Absyn_Syntax.mk_Typ_app (t', args) None typ.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left (compress_typ_aux pos) _90_8))
end
| _24_55 -> begin
typ
end)
end
| _24_57 -> begin
typ
end))

let compress_typ = (fun typ -> (compress_typ_aux true typ))

let compress_typ_uvars = (fun typ -> (compress_typ_aux false typ))

let rec compress_exp_aux = (fun meta exp -> (match (exp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (uv, _24_64) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(compress_exp_aux meta e)
end
| _24_70 -> begin
exp
end)
end
| FStar_Absyn_Syntax.Exp_delayed (_24_72, _24_74, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
exp
end
| Some (e) -> begin
(let e' = (compress_exp_aux meta e)
in (let _24_82 = (FStar_ST.op_Colon_Equals m (Some (e')))
in e'))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _24_86)) when meta -> begin
(compress_exp_aux meta e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _24_100); FStar_Absyn_Syntax.tk = _24_97; FStar_Absyn_Syntax.pos = _24_95; FStar_Absyn_Syntax.fvs = _24_93; FStar_Absyn_Syntax.uvs = _24_91}, args) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (e') -> begin
(FStar_Absyn_Syntax.mk_Exp_app (e', args) None exp.FStar_Absyn_Syntax.pos)
end
| _24_110 -> begin
exp
end)
end
| _24_112 -> begin
exp
end))

let compress_exp = (fun e -> (compress_exp_aux true e))

let compress_exp_uvars = (fun e -> (compress_exp_aux false e))

let rec compress_kind = (fun knd -> (match (knd.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_24_117, _24_119, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
knd
end
| Some (k) -> begin
(let k' = (compress_kind k)
in (let _24_127 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k'))
end)
end
| _24_130 -> begin
knd
end))

let left = (fun ext benv btv -> (match ((ext benv (FStar_Util.Inl (btv)))) with
| (benv, FStar_Util.Inl (bvd)) -> begin
(benv, bvd)
end
| _24_139 -> begin
(FStar_All.failwith "impossible")
end))

let right = (fun ext benv bvv -> (match ((ext benv (FStar_Util.Inr (bvv)))) with
| (benv, FStar_Util.Inr (bvd)) -> begin
(benv, bvd)
end
| _24_148 -> begin
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

let push_tbinder = (fun binders _24_1 -> (match (_24_1) with
| None -> begin
binders
end
| Some (a) -> begin
(FStar_Util.Inl (a))::binders
end))

let push_vbinder = (fun binders _24_2 -> (match (_24_2) with
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

let leaf_k = (fun _24_176 -> (match (()) with
| () -> begin
([], [], [], [])
end))

let leaf_te = (fun _24_177 -> (match (()) with
| () -> begin
([], [], [], [], [])
end))

let rec reduce_kind = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k -> (let rec visit_kind = (fun env binders k -> (let k = (compress_kind k)
in (let _24_236 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (_24_197) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
((leaf_k ()), env)
end
| FStar_Absyn_Syntax.Kind_uvar (_24_206, args) -> begin
(let _24_212 = (map_args map_typ map_exp env binders args)
in (match (_24_212) with
| (args, env) -> begin
(([], [], [], args), env)
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(let _24_219 = (map_kind env binders k)
in (match (_24_219) with
| (k, env) -> begin
(let _24_222 = (map_args map_typ map_exp env binders (Prims.snd kabr))
in (match (_24_222) with
| (args, env) -> begin
(([], (k)::[], [], args), env)
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _24_230 = (map_binders map_kind map_typ env binders bs)
in (match (_24_230) with
| (bs, binders, env) -> begin
(let _24_233 = (map_kind env binders k)
in (match (_24_233) with
| (k, env) -> begin
((bs, (k)::[], [], []), env)
end))
end))
end)
in (match (_24_236) with
| (components, env) -> begin
(combine_kind k components env)
end))))
and map_kind = (fun env binders k -> (map_kind' visit_kind map_typ map_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_kind env binders k)))
and map_args = (fun map_typ map_exp env binders arguments -> (let _24_270 = (FStar_List.fold_left (fun _24_254 _24_257 -> (match ((_24_254, _24_257)) with
| ((out, env), (arg, imp)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(let _24_262 = (map_typ env binders t)
in (match (_24_262) with
| (t, env) -> begin
(((FStar_Util.Inl (t), imp))::out, env)
end))
end
| FStar_Util.Inr (e) -> begin
(let _24_267 = (map_exp env binders e)
in (match (_24_267) with
| (e, env) -> begin
(((FStar_Util.Inr (e), imp))::out, env)
end))
end)
end)) ([], env) arguments)
in (match (_24_270) with
| (args', env) -> begin
((FStar_List.rev args'), env)
end)))
and map_binders = (fun map_kind map_typ env binders bs -> (let _24_301 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _24_280 b -> (match (_24_280) with
| (bs, binders, env) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(let _24_288 = (map_kind env binders a.FStar_Absyn_Syntax.sort)
in (match (_24_288) with
| (k, env) -> begin
(let binders = (push_tbinder binders (Some (a.FStar_Absyn_Syntax.v)))
in (((FStar_Util.Inl ((bvd_to_bvar_s a.FStar_Absyn_Syntax.v k)), imp))::bs, binders, env))
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _24_296 = (map_typ env binders x.FStar_Absyn_Syntax.sort)
in (match (_24_296) with
| (t, env) -> begin
(let binders = (push_vbinder binders (Some (x.FStar_Absyn_Syntax.v)))
in (((FStar_Util.Inr ((bvd_to_bvar_s x.FStar_Absyn_Syntax.v t)), imp))::bs, binders, env))
end))
end)
end)) ([], binders, env)))
in (match (_24_301) with
| (bs, binders, env) -> begin
((FStar_List.rev bs), binders, env)
end)))
and reduce_typ = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t -> (let rec map_comp = (fun env binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _24_324 = (map_typ env binders t)
in (match (_24_324) with
| (t, env) -> begin
(let _90_292 = (FStar_Absyn_Syntax.mk_Total t)
in (_90_292, env))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _24_329 = (map_typ env binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_24_329) with
| (t, env) -> begin
(let _24_332 = (map_args map_typ map_exp env binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_24_332) with
| (args, env) -> begin
(let _24_343 = (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.fold_map (fun env flag -> (match (flag) with
| FStar_Absyn_Syntax.DECREASES (arg) -> begin
(let _24_339 = (map_exp env binders arg)
in (match (_24_339) with
| (arg, env) -> begin
(env, FStar_Absyn_Syntax.DECREASES (arg))
end))
end
| f -> begin
(env, f)
end)) env))
in (match (_24_343) with
| (env, flags) -> begin
(let _90_295 = (FStar_Absyn_Syntax.mk_Comp (let _24_344 = ct
in {FStar_Absyn_Syntax.effect_name = _24_344.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = flags}))
in (_90_295, env))
end))
end))
end))
end))
and visit_typ = (fun env binders t -> (let _24_494 = (match ((let _90_299 = (compress_typ t)
in _90_299.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_delayed (_24_350) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(let _24_362 = (map_typ env binders t)
in (match (_24_362) with
| (_24_360, env) -> begin
((leaf_te ()), env)
end))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(let _24_369 = (map_typ env binders t)
in (match (_24_369) with
| (t, env) -> begin
(let _24_372 = (map_args map_typ map_exp env binders args)
in (match (_24_372) with
| (args, env) -> begin
(([], [], (t)::[], [], args), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (axs, t) -> begin
(let _24_380 = (map_binders map_kind map_typ env binders axs)
in (match (_24_380) with
| (axs, binders, env) -> begin
(let _24_383 = (map_typ env binders t)
in (match (_24_383) with
| (t, env) -> begin
((axs, [], (t)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, t2) -> begin
(let _24_391 = (map_binders map_kind map_typ env binders (((FStar_Util.Inr (x), None))::[]))
in (match (_24_391) with
| (bs, binders, env) -> begin
(let _24_394 = (map_typ env binders t2)
in (match (_24_394) with
| (t2, env) -> begin
((bs, [], (t2)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let _24_402 = (map_binders map_kind map_typ env binders bs)
in (match (_24_402) with
| (bs, binders, env) -> begin
(let _24_405 = (map_comp env binders c)
in (match (_24_405) with
| (c, env) -> begin
((bs, [], [], (c)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, k) -> begin
(let _24_412 = (map_typ env binders t)
in (match (_24_412) with
| (t, env) -> begin
(let _24_415 = (map_kind env binders k)
in (match (_24_415) with
| (k, env) -> begin
(([], (k)::[], (t)::[], [], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_24_417, k) -> begin
(let _24_423 = (map_kind env binders k)
in (match (_24_423) with
| (k, env) -> begin
(([], (k)::[], [], [], []), env)
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, flag)) -> begin
(let _24_432 = (map_typ env binders t1)
in (match (_24_432) with
| (t1, env) -> begin
(let _24_435 = (map_typ env binders t2)
in (match (_24_435) with
| (t2, env) -> begin
(([], [], (t1)::(t2)::[], [], []), env)
end))
end))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(let _24_460 = (map_typ env binders t)
in (match (_24_460) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, ps)) -> begin
(let _24_468 = (map_typ env binders t)
in (match (_24_468) with
| (t, env) -> begin
(let _24_491 = (FStar_List.fold_left (fun _24_471 arg -> (match (_24_471) with
| (pats, env) -> begin
(match (arg) with
| (FStar_Util.Inl (t), _24_476) -> begin
(let _24_480 = (map_typ env binders t)
in (match (_24_480) with
| (t, env) -> begin
(((FStar_Util.Inl (t), None))::pats, env)
end))
end
| (FStar_Util.Inr (e), _24_484) -> begin
(let _24_488 = (map_exp env binders e)
in (match (_24_488) with
| (e, env) -> begin
(((FStar_Util.Inr (e), None))::pats, env)
end))
end)
end)) ([], env) ps)
in (match (_24_491) with
| (pats, env) -> begin
(([], [], (t)::[], [], (FStar_List.rev pats)), env)
end))
end))
end)
in (match (_24_494) with
| (components, env) -> begin
(combine_typ t components env)
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (map_typ' map_kind visit_typ map_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_typ env binders t)))
and reduce_exp = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e -> (let rec map_exps = (fun env binders el -> (let _24_532 = (FStar_List.fold_left (fun _24_525 e -> (match (_24_525) with
| (out, env) -> begin
(let _24_529 = (map_exp env binders e)
in (match (_24_529) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_24_532) with
| (el, env) -> begin
((FStar_List.rev el), env)
end)))
and map_exps_with_binders = (fun env el -> (let _24_546 = (FStar_List.fold_left (fun _24_537 _24_540 -> (match ((_24_537, _24_540)) with
| ((out, env), (b, e)) -> begin
(let _24_543 = (map_exp env b e)
in (match (_24_543) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_24_546) with
| (el, env) -> begin
((FStar_List.rev el), env)
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (map_exp' map_kind map_typ visit_exp env binders e))
and visit_exp = (fun env binders e -> (let e = (compress_exp_uvars e)
in (let _24_733 = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_24_561) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _24_565)) -> begin
(let _24_571 = (map_exp env binders e)
in (match (_24_571) with
| (e, env) -> begin
(([], [], [], (e)::[], []), env)
end))
end
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
((leaf_te ()), env)
end
| FStar_Absyn_Syntax.Exp_uvar (_24_582, t) -> begin
(let _24_588 = (map_typ env binders t)
in (match (_24_588) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(let _24_596 = (map_binders map_kind map_typ env binders bs)
in (match (_24_596) with
| (bs, binders, env) -> begin
(let _24_599 = (map_exp env binders e)
in (match (_24_599) with
| (e, env) -> begin
((bs, [], [], (e)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(let _24_606 = (map_exp env binders e)
in (match (_24_606) with
| (e, env) -> begin
(let _24_609 = (map_args map_typ map_exp env binders args)
in (match (_24_609) with
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
| FStar_Absyn_Syntax.Pat_cons (_24_637, _24_639, pats) -> begin
(FStar_List.fold_left (fun b _24_647 -> (match (_24_647) with
| (p, _24_646) -> begin
(pat_binders b p)
end)) b pats)
end
| FStar_Absyn_Syntax.Pat_disj (p::_24_649) -> begin
(pat_binders b p)
end
| FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end))
in (let branches = (FStar_All.pipe_right pl (FStar_List.collect (fun _24_658 -> (match (_24_658) with
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
in (let _24_666 = (map_exps_with_binders env (((binders, e1))::branches))
in (match (_24_666) with
| (el, env) -> begin
(([], [], [], el, []), env)
end))))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _24_670) -> begin
(let _24_675 = (map_typ env binders t)
in (match (_24_675) with
| (t, env) -> begin
(let _24_678 = (map_exp env binders e)
in (match (_24_678) with
| (e, env) -> begin
(([], [], (t)::[], (e)::[], []), env)
end))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, lb::[]), e2) -> begin
(let _24_688 = (map_typ env binders lb.FStar_Absyn_Syntax.lbtyp)
in (match (_24_688) with
| (t, env) -> begin
(let binders' = (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _24_692 -> begin
binders
end)
in (let _24_696 = (map_exps_with_binders env (((binders, lb.FStar_Absyn_Syntax.lbdef))::((binders', e2))::[]))
in (match (_24_696) with
| (el, env) -> begin
(([], [], (t)::[], el, []), env)
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((true, bvdt_tl), e) -> begin
(let tl = (FStar_List.map (fun lb -> lb.FStar_Absyn_Syntax.lbtyp) bvdt_tl)
in (let el = (FStar_List.map (fun lb -> lb.FStar_Absyn_Syntax.lbdef) bvdt_tl)
in (let _24_716 = (FStar_All.pipe_right tl (FStar_List.fold_left (fun _24_709 t -> (match (_24_709) with
| (tl, env) -> begin
(let _24_713 = (map_typ env binders t)
in (match (_24_713) with
| (t, env) -> begin
((t)::tl, env)
end))
end)) ([], env)))
in (match (_24_716) with
| (tl, env) -> begin
(let tl = (FStar_List.rev tl)
in (let binders = (FStar_List.fold_left (fun binders lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _24_723 -> begin
binders
end)) binders bvdt_tl)
in (let _24_727 = (map_exps env binders (FStar_List.append el ((e)::[])))
in (match (_24_727) with
| (el, env) -> begin
(([], [], tl, el, []), env)
end))))
end))))
end
| FStar_Absyn_Syntax.Exp_let (_24_729) -> begin
(FStar_All.failwith "impossible")
end)
in (match (_24_733) with
| (components, env) -> begin
(combine_exp e components env)
end))))
in (map_exp env binders e)))

let combine_kind = (fun k kc env -> (let k' = (match ((k.FStar_Absyn_Syntax.n, kc)) with
| ((FStar_Absyn_Syntax.Kind_lam (_), _)) | ((FStar_Absyn_Syntax.Kind_type, _)) | ((FStar_Absyn_Syntax.Kind_effect, _)) | ((FStar_Absyn_Syntax.Kind_unknown, _)) -> begin
(fun p -> (FStar_Util.return_all k))
end
| (FStar_Absyn_Syntax.Kind_uvar (u, _24_758), (_24_762, _24_764, _24_766, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_uvar (u, args))
end
| (FStar_Absyn_Syntax.Kind_abbrev (kabr, _24_772), (_24_776, k::[], _24_780, args)) -> begin
(FStar_Absyn_Syntax.mk_Kind_abbrev (((Prims.fst kabr), args), k))
end
| (FStar_Absyn_Syntax.Kind_arrow (_24_785, _24_787), (bs, k'::[], _24_794, _24_796)) -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow (bs, k'))
end
| _24_800 -> begin
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
| (FStar_Absyn_Syntax.Typ_lam (_24_825), (bs, _24_829, t::[], _24_833, _24_835)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
end
| (FStar_Absyn_Syntax.Typ_app (_24_839), (_24_842, _24_844, t::[], _24_848, args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_app (t, args)))
end
| (FStar_Absyn_Syntax.Typ_refine (_24_853), ((FStar_Util.Inr (x), _24_858)::[], _24_862, t::[], _24_866, _24_868)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_refine (x, t)))
end
| (FStar_Absyn_Syntax.Typ_fun (_24_872), (bs, _24_876, _24_878, c::[], _24_882)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_fun (bs, c)))
end
| (FStar_Absyn_Syntax.Typ_uvar (x, _24_887), (_24_891, k::[], _24_895, _24_897, _24_899)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_uvar' (x, k)))
end
| (FStar_Absyn_Syntax.Typ_ascribed (_24_903), (_24_906, k::[], t::[], _24_912, _24_914)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_ascribed' (t, k)))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (_24_918, l)), (_24_924, _24_926, t'::[], _24_930, _24_932)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_named ((t', l)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_24_936)), (_24_940, _24_942, t::[], _24_946, args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_pattern ((t, args)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_24_951, l, r, p)), (_24_959, _24_961, t::[], _24_965, _24_967)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (_24_971, b, r)), (_24_978, _24_980, t::[], _24_984, _24_986)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Typ_meta' (FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r)))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_24_990, _24_992, _24_994)), (_24_999, _24_1001, t1::t2::[], _24_1006, _24_1008)) -> begin
(let _90_423 = (let _90_422 = (let _90_421 = (let _90_420 = (FStar_Util.mk_ref false)
in (t1, t2, _90_420))
in FStar_Absyn_Syntax.Meta_slack_formula (_90_421))
in (FStar_Absyn_Syntax.mk_Typ_meta' _90_422))
in (FStar_All.pipe_left w _90_423))
end
| _24_1012 -> begin
(FStar_All.failwith "impossible")
end)
in (t', env)))))

let combine_exp = (fun e ec env -> (let e = (compress_exp e)
in (let w = (fun f -> (f None e.FStar_Absyn_Syntax.pos))
in (let e' = (match ((e.FStar_Absyn_Syntax.n, ec)) with
| ((FStar_Absyn_Syntax.Exp_bvar (_), _)) | ((FStar_Absyn_Syntax.Exp_fvar (_), _)) | ((FStar_Absyn_Syntax.Exp_constant (_), _)) -> begin
e
end
| (FStar_Absyn_Syntax.Exp_uvar (uv, _24_1040), (_24_1044, _24_1046, t::[], _24_1050, _24_1052)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t)))
end
| (FStar_Absyn_Syntax.Exp_abs (_24_1056), (bs, _24_1060, _24_1062, e::[], _24_1066)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_abs (bs, e)))
end
| (FStar_Absyn_Syntax.Exp_app (_24_1070), (_24_1073, _24_1075, _24_1077, e::[], args)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_app (e, args)))
end
| (FStar_Absyn_Syntax.Exp_ascribed (_24_1084, _24_1086, l), (_24_1091, _24_1093, t::[], e::[], _24_1099)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, l)))
end
| (FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_24_1103, tag)), (_24_1109, _24_1111, _24_1113, e::[], _24_1117)) -> begin
(FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_meta' (FStar_Absyn_Syntax.Meta_desugared ((e, tag)))))
end
| (FStar_Absyn_Syntax.Exp_match (_24_1121, eqns), (_24_1126, [], [], e1::el, _24_1133)) -> begin
(let rec mk_eqns = (fun eqns el -> (match ((eqns, el)) with
| ((p, None, _24_1143)::eqns', e::el') -> begin
(let _90_453 = (mk_eqns eqns' el')
in ((p, None, e))::_90_453)
end
| ((p, Some (_24_1153), _24_1156)::eqns', w::e::el') -> begin
(let _90_454 = (mk_eqns eqns' el')
in ((p, Some (w), e))::_90_454)
end
| ([], []) -> begin
[]
end
| _24_1169 -> begin
(FStar_All.failwith "impossible")
end))
in (let _90_459 = (let _90_458 = (let _90_457 = (mk_eqns eqns el)
in (e1, _90_457))
in (FStar_Absyn_Syntax.mk_Exp_match _90_458))
in (FStar_All.pipe_left w _90_459)))
end
| (FStar_Absyn_Syntax.Exp_let ((is_rec, lbs), _24_1174), (_24_1178, _24_1180, tl, el, _24_1184)) -> begin
(match ((FStar_Util.first_N (FStar_List.length lbs) el)) with
| (el, e'::[]) -> begin
(let lbs' = (FStar_List.map3 (fun lb t e -> (let _24_1194 = lb
in {FStar_Absyn_Syntax.lbname = _24_1194.FStar_Absyn_Syntax.lbname; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _24_1194.FStar_Absyn_Syntax.lbeff; FStar_Absyn_Syntax.lbdef = e})) lbs tl el)
in (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs'), e'))))
end
| _24_1198 -> begin
(FStar_All.failwith "impossible")
end)
end
| _24_1200 -> begin
(FStar_All.failwith "impossible")
end)
in (e', env)))))

let collect_from_typ = (fun f env t -> (let _90_583 = (reduce_typ (fun _24_1246 _24_1248 _24_1250 env _24_1253 k -> (k, env)) (fun _24_1228 vt _24_1231 env bvs t -> (let env = (f env t)
in (match ((let _90_540 = (compress_typ t)
in _90_540.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(t, env)
end
| _24_1245 -> begin
(vt env bvs t)
end))) (fun _24_1218 _24_1220 _24_1222 env _24_1225 e -> (e, env)) (fun k _24_1215 env -> (k, env)) (fun t _24_1211 env -> (t, env)) (fun e _24_1207 env -> (e, env)) env [] t)
in (FStar_All.pipe_left Prims.snd _90_583)))




