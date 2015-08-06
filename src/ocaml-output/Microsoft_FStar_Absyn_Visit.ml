
let log = (fun ( s ) -> ())

let rec compress_typ_aux = (fun ( pos ) ( typ ) -> (match (typ.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (typ) -> begin
(compress_typ_aux pos typ)
end
| _24_13 -> begin
typ
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((_24_15, m)) -> begin
(match ((Support.ST.read m)) with
| None -> begin
typ
end
| Some (t) -> begin
(let t' = (compress_typ_aux pos t)
in (let _24_23 = (Support.ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) when pos -> begin
(compress_typ_aux pos t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _24_45)); Microsoft_FStar_Absyn_Syntax.tk = _24_42; Microsoft_FStar_Absyn_Syntax.pos = _24_40; Microsoft_FStar_Absyn_Syntax.fvs = _24_38; Microsoft_FStar_Absyn_Syntax.uvs = _24_36}, args)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (t') -> begin
(let _70_7962 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t', args) None typ.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_left (compress_typ_aux pos) _70_7962))
end
| _24_55 -> begin
typ
end)
end
| _24_57 -> begin
typ
end))

let compress_typ = (fun ( typ ) -> (compress_typ_aux true typ))

let compress_typ_uvars = (fun ( typ ) -> (compress_typ_aux false typ))

let rec compress_exp_aux = (fun ( meta ) ( exp ) -> (match (exp.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _24_64)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (e) -> begin
(compress_exp_aux meta e)
end
| _24_70 -> begin
exp
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_delayed ((_24_72, _24_74, m)) -> begin
(match ((Support.ST.read m)) with
| None -> begin
exp
end
| Some (e) -> begin
(let e' = (compress_exp_aux meta e)
in (let _24_82 = (Support.ST.op_Colon_Equals m (Some (e')))
in e'))
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _24_86))) when meta -> begin
(compress_exp_aux meta e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _24_100)); Microsoft_FStar_Absyn_Syntax.tk = _24_97; Microsoft_FStar_Absyn_Syntax.pos = _24_95; Microsoft_FStar_Absyn_Syntax.fvs = _24_93; Microsoft_FStar_Absyn_Syntax.uvs = _24_91}, args)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (e') -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e', args) None exp.Microsoft_FStar_Absyn_Syntax.pos)
end
| _24_110 -> begin
exp
end)
end
| _24_112 -> begin
exp
end))

let compress_exp = (fun ( e ) -> (compress_exp_aux true e))

let compress_exp_uvars = (fun ( e ) -> (compress_exp_aux false e))

let rec compress_kind = (fun ( knd ) -> (match (knd.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_delayed ((_24_117, _24_119, m)) -> begin
(match ((Support.ST.read m)) with
| None -> begin
knd
end
| Some (k) -> begin
(let k' = (compress_kind k)
in (let _24_127 = (Support.ST.op_Colon_Equals m (Some (k')))
in k'))
end)
end
| _24_130 -> begin
knd
end))

let left = (fun ( ext ) ( benv ) ( btv ) -> (match ((ext benv (Support.Microsoft.FStar.Util.Inl (btv)))) with
| (benv, Support.Microsoft.FStar.Util.Inl (bvd)) -> begin
(benv, bvd)
end
| _24_139 -> begin
(Support.All.failwith "impossible")
end))

let right = (fun ( ext ) ( benv ) ( bvv ) -> (match ((ext benv (Support.Microsoft.FStar.Util.Inr (bvv)))) with
| (benv, Support.Microsoft.FStar.Util.Inr (bvd)) -> begin
(benv, bvd)
end
| _24_148 -> begin
(Support.All.failwith "impossible")
end))

type boundvar =
(Microsoft_FStar_Absyn_Syntax.btvdef, Microsoft_FStar_Absyn_Syntax.bvvdef) Support.Microsoft.FStar.Util.either

type boundvars =
boundvar list

type ('env, 'm) imap =
'env  ->  boundvars  ->  'm  ->  ('m * 'env)

type ('env, 'm, 'n) mapper =
('env, Microsoft_FStar_Absyn_Syntax.knd) imap  ->  ('env, Microsoft_FStar_Absyn_Syntax.typ) imap  ->  ('env, Microsoft_FStar_Absyn_Syntax.exp) imap  ->  'env  ->  boundvars  ->  'm  ->  ('n * 'env)

let push_tbinder = (fun ( binders ) ( _24_1 ) -> (match (_24_1) with
| None -> begin
binders
end
| Some (a) -> begin
(Support.Microsoft.FStar.Util.Inl (a))::binders
end))

let push_vbinder = (fun ( binders ) ( _24_2 ) -> (match (_24_2) with
| None -> begin
binders
end
| Some (a) -> begin
(Support.Microsoft.FStar.Util.Inr (a))::binders
end))

let bvd_to_bvar_s = (fun ( bvd ) ( sort ) -> {Microsoft_FStar_Absyn_Syntax.v = bvd; Microsoft_FStar_Absyn_Syntax.sort = sort; Microsoft_FStar_Absyn_Syntax.p = bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idRange})

let tbinder_opt = (fun ( aopt ) ( k ) -> (match (aopt) with
| None -> begin
[]
end
| Some (a) -> begin
(Support.Microsoft.FStar.Util.Inl ((bvd_to_bvar_s a k)))::[]
end))

let vbinder_opt = (fun ( aopt ) ( t ) -> (match (aopt) with
| None -> begin
[]
end
| Some (a) -> begin
(Support.Microsoft.FStar.Util.Inr ((bvd_to_bvar_s a t)))::[]
end))

type knd_components =
(Microsoft_FStar_Absyn_Syntax.binders * Microsoft_FStar_Absyn_Syntax.knd list * Microsoft_FStar_Absyn_Syntax.typ list * Microsoft_FStar_Absyn_Syntax.arg list)

type typ_components =
(Microsoft_FStar_Absyn_Syntax.binders * Microsoft_FStar_Absyn_Syntax.knd list * Microsoft_FStar_Absyn_Syntax.typ list * Microsoft_FStar_Absyn_Syntax.comp list * Microsoft_FStar_Absyn_Syntax.arg list)

type exp_components =
(Microsoft_FStar_Absyn_Syntax.binders * Microsoft_FStar_Absyn_Syntax.knd list * Microsoft_FStar_Absyn_Syntax.typ list * Microsoft_FStar_Absyn_Syntax.exp list * Microsoft_FStar_Absyn_Syntax.arg list)

let leaf_k = (fun ( _24_176 ) -> (match (()) with
| () -> begin
([], [], [], [])
end))

let leaf_te = (fun ( _24_177 ) -> (match (()) with
| () -> begin
([], [], [], [], [])
end))

let rec reduce_kind = (fun ( map_kind' ) ( map_typ' ) ( map_exp' ) ( combine_kind ) ( combine_typ ) ( combine_exp ) ( env ) ( binders ) ( k ) -> (let rec visit_kind = (fun ( env ) ( binders ) ( k ) -> (let k = (compress_kind k)
in (let _24_236 = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_24_197) -> begin
(Support.All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Kind_lam (_)) | (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) | (Microsoft_FStar_Absyn_Syntax.Kind_unknown) -> begin
((leaf_k ()), env)
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((_24_206, args)) -> begin
(let _24_212 = (map_args map_typ map_exp env binders args)
in (match (_24_212) with
| (args, env) -> begin
(([], [], [], args), env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((kabr, k)) -> begin
(let _24_219 = (map_kind env binders k)
in (match (_24_219) with
| (k, env) -> begin
(let _24_222 = (map_args map_typ map_exp env binders (Support.Prims.snd kabr))
in (match (_24_222) with
| (args, env) -> begin
(([], (k)::[], [], args), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
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
and map_kind = (fun ( env ) ( binders ) ( k ) -> (map_kind' visit_kind map_typ map_exp env binders k))
and map_typ = (fun ( env ) ( binders ) ( t ) -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun ( env ) ( binders ) ( e ) -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_kind env binders k)))
and map_args = (fun ( map_typ ) ( map_exp ) ( env ) ( binders ) ( arguments ) -> (let _24_270 = (Support.List.fold_left (fun ( _24_254 ) ( _24_257 ) -> (match ((_24_254, _24_257)) with
| ((out, env), (arg, imp)) -> begin
(match (arg) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _24_262 = (map_typ env binders t)
in (match (_24_262) with
| (t, env) -> begin
(((Support.Microsoft.FStar.Util.Inl (t), imp))::out, env)
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _24_267 = (map_exp env binders e)
in (match (_24_267) with
| (e, env) -> begin
(((Support.Microsoft.FStar.Util.Inr (e), imp))::out, env)
end))
end)
end)) ([], env) arguments)
in (match (_24_270) with
| (args', env) -> begin
((Support.List.rev args'), env)
end)))
and map_binders = (fun ( map_kind ) ( map_typ ) ( env ) ( binders ) ( bs ) -> (let _24_301 = (Support.All.pipe_right bs (Support.List.fold_left (fun ( _24_280 ) ( b ) -> (match (_24_280) with
| (bs, binders, env) -> begin
(match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _24_288 = (map_kind env binders a.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_24_288) with
| (k, env) -> begin
(let binders = (push_tbinder binders (Some (a.Microsoft_FStar_Absyn_Syntax.v)))
in (((Support.Microsoft.FStar.Util.Inl ((bvd_to_bvar_s a.Microsoft_FStar_Absyn_Syntax.v k)), imp))::bs, binders, env))
end))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _24_296 = (map_typ env binders x.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_24_296) with
| (t, env) -> begin
(let binders = (push_vbinder binders (Some (x.Microsoft_FStar_Absyn_Syntax.v)))
in (((Support.Microsoft.FStar.Util.Inr ((bvd_to_bvar_s x.Microsoft_FStar_Absyn_Syntax.v t)), imp))::bs, binders, env))
end))
end)
end)) ([], binders, env)))
in (match (_24_301) with
| (bs, binders, env) -> begin
((Support.List.rev bs), binders, env)
end)))
and reduce_typ = (fun ( map_kind' ) ( map_typ' ) ( map_exp' ) ( combine_kind ) ( combine_typ ) ( combine_exp ) ( env ) ( binders ) ( t ) -> (let rec map_comp = (fun ( env ) ( binders ) ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _24_324 = (map_typ env binders t)
in (match (_24_324) with
| (t, env) -> begin
(let _70_8246 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (_70_8246, env))
end))
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _24_329 = (map_typ env binders ct.Microsoft_FStar_Absyn_Syntax.result_typ)
in (match (_24_329) with
| (t, env) -> begin
(let _24_332 = (map_args map_typ map_exp env binders ct.Microsoft_FStar_Absyn_Syntax.effect_args)
in (match (_24_332) with
| (args, env) -> begin
(let _24_343 = (Support.All.pipe_right ct.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.fold_map (fun ( env ) ( flag ) -> (match (flag) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (arg) -> begin
(let _24_339 = (map_exp env binders arg)
in (match (_24_339) with
| (arg, env) -> begin
(env, Microsoft_FStar_Absyn_Syntax.DECREASES (arg))
end))
end
| f -> begin
(env, f)
end)) env))
in (match (_24_343) with
| (env, flags) -> begin
(let _70_8249 = (Microsoft_FStar_Absyn_Syntax.mk_Comp (let _24_344 = ct
in {Microsoft_FStar_Absyn_Syntax.effect_name = _24_344.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = args; Microsoft_FStar_Absyn_Syntax.flags = flags}))
in (_70_8249, env))
end))
end))
end))
end))
and visit_typ = (fun ( env ) ( binders ) ( t ) -> (let _24_494 = (match ((let _70_8253 = (compress_typ t)
in _70_8253.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_24_350) -> begin
(Support.All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) -> begin
(let _24_362 = (map_typ env binders t)
in (match (_24_362) with
| (_24_360, env) -> begin
((leaf_te ()), env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, args)) -> begin
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
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((axs, t)) -> begin
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
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, t2)) -> begin
(let _24_391 = (map_binders map_kind map_typ env binders (((Support.Microsoft.FStar.Util.Inr (x), None))::[]))
in (match (_24_391) with
| (bs, binders, env) -> begin
(let _24_394 = (map_typ env binders t2)
in (match (_24_394) with
| (t2, env) -> begin
((bs, [], (t2)::[], [], []), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
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
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, k)) -> begin
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
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((_24_417, k)) -> begin
(let _24_423 = (map_kind env binders k)
in (match (_24_423) with
| (k, env) -> begin
(([], (k)::[], [], [], []), env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, flag))) -> begin
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
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, _, _, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _, _)))) -> begin
(let _24_460 = (map_typ env binders t)
in (match (_24_460) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps))) -> begin
(let _24_468 = (map_typ env binders t)
in (match (_24_468) with
| (t, env) -> begin
(let _24_491 = (Support.List.fold_left (fun ( _24_471 ) ( arg ) -> (match (_24_471) with
| (pats, env) -> begin
(match (arg) with
| (Support.Microsoft.FStar.Util.Inl (t), _24_476) -> begin
(let _24_480 = (map_typ env binders t)
in (match (_24_480) with
| (t, env) -> begin
(((Support.Microsoft.FStar.Util.Inl (t), None))::pats, env)
end))
end
| (Support.Microsoft.FStar.Util.Inr (e), _24_484) -> begin
(let _24_488 = (map_exp env binders e)
in (match (_24_488) with
| (e, env) -> begin
(((Support.Microsoft.FStar.Util.Inr (e), None))::pats, env)
end))
end)
end)) ([], env) ps)
in (match (_24_491) with
| (pats, env) -> begin
(([], [], (t)::[], [], (Support.List.rev pats)), env)
end))
end))
end)
in (match (_24_494) with
| (components, env) -> begin
(combine_typ t components env)
end)))
and map_kind = (fun ( env ) ( binders ) ( k ) -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun ( env ) ( binders ) ( t ) -> (map_typ' map_kind visit_typ map_exp env binders t))
and map_exp = (fun ( env ) ( binders ) ( e ) -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_typ env binders t)))
and reduce_exp = (fun ( map_kind' ) ( map_typ' ) ( map_exp' ) ( combine_kind ) ( combine_typ ) ( combine_exp ) ( env ) ( binders ) ( e ) -> (let rec map_exps = (fun ( env ) ( binders ) ( el ) -> (let _24_532 = (Support.List.fold_left (fun ( _24_525 ) ( e ) -> (match (_24_525) with
| (out, env) -> begin
(let _24_529 = (map_exp env binders e)
in (match (_24_529) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_24_532) with
| (el, env) -> begin
((Support.List.rev el), env)
end)))
and map_exps_with_binders = (fun ( env ) ( el ) -> (let _24_546 = (Support.List.fold_left (fun ( _24_537 ) ( _24_540 ) -> (match ((_24_537, _24_540)) with
| ((out, env), (b, e)) -> begin
(let _24_543 = (map_exp env b e)
in (match (_24_543) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_24_546) with
| (el, env) -> begin
((Support.List.rev el), env)
end)))
and map_kind = (fun ( env ) ( binders ) ( k ) -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun ( env ) ( binders ) ( t ) -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun ( env ) ( binders ) ( e ) -> (map_exp' map_kind map_typ visit_exp env binders e))
and visit_exp = (fun ( env ) ( binders ) ( e ) -> (let e = (compress_exp_uvars e)
in (let _24_731 = (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_24_561) -> begin
(Support.All.failwith "impossible")
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _24_565))) -> begin
(let _24_571 = (map_exp env binders e)
in (match (_24_571) with
| (e, env) -> begin
(([], [], [], (e)::[], []), env)
end))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) -> begin
((leaf_te ()), env)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((_24_582, t)) -> begin
(let _24_588 = (map_typ env binders t)
in (match (_24_588) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, e)) -> begin
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
| Microsoft_FStar_Absyn_Syntax.Exp_app ((e, args)) -> begin
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
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e1, pl)) -> begin
(let rec pat_binders = (fun ( b ) ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_constant (_)) -> begin
b
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _24_634)) -> begin
(push_vbinder b (Some (x.Microsoft_FStar_Absyn_Syntax.v)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (t) -> begin
(push_tbinder b (Some (t.Microsoft_FStar_Absyn_Syntax.v)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((_24_640, _24_642, pats)) -> begin
(Support.List.fold_left pat_binders b pats)
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (p::_24_647) -> begin
(pat_binders b p)
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(Support.All.failwith "impossible")
end))
in (let branches = (Support.All.pipe_right pl (Support.List.collect (fun ( _24_656 ) -> (match (_24_656) with
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
in (let _24_664 = (map_exps_with_binders env (((binders, e1))::branches))
in (match (_24_664) with
| (el, env) -> begin
(([], [], [], el, []), env)
end))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _24_668)) -> begin
(let _24_673 = (map_typ env binders t)
in (match (_24_673) with
| (t, env) -> begin
(let _24_676 = (map_exp env binders e)
in (match (_24_676) with
| (e, env) -> begin
(([], [], (t)::[], (e)::[], []), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, lb::[]), e2)) -> begin
(let _24_686 = (map_typ env binders lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (match (_24_686) with
| (t, env) -> begin
(let binders' = (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _24_690 -> begin
binders
end)
in (let _24_694 = (map_exps_with_binders env (((binders, lb.Microsoft_FStar_Absyn_Syntax.lbdef))::((binders', e2))::[]))
in (match (_24_694) with
| (el, env) -> begin
(([], [], (t)::[], el, []), env)
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((true, bvdt_tl), e)) -> begin
(let tl = (Support.List.map (fun ( lb ) -> lb.Microsoft_FStar_Absyn_Syntax.lbtyp) bvdt_tl)
in (let el = (Support.List.map (fun ( lb ) -> lb.Microsoft_FStar_Absyn_Syntax.lbdef) bvdt_tl)
in (let _24_714 = (Support.All.pipe_right tl (Support.List.fold_left (fun ( _24_707 ) ( t ) -> (match (_24_707) with
| (tl, env) -> begin
(let _24_711 = (map_typ env binders t)
in (match (_24_711) with
| (t, env) -> begin
((t)::tl, env)
end))
end)) ([], env)))
in (match (_24_714) with
| (tl, env) -> begin
(let tl = (Support.List.rev tl)
in (let binders = (Support.List.fold_left (fun ( binders ) ( lb ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _24_721 -> begin
binders
end)) binders bvdt_tl)
in (let _24_725 = (map_exps env binders (Support.List.append el ((e)::[])))
in (match (_24_725) with
| (el, env) -> begin
(([], [], tl, el, []), env)
end))))
end))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (_24_727) -> begin
(Support.All.failwith "impossible")
end)
in (match (_24_731) with
| (components, env) -> begin
(combine_exp e components env)
end))))
in (map_exp env binders e)))

let combine_kind = (fun ( k ) ( kc ) ( env ) -> (let k' = (match ((k.Microsoft_FStar_Absyn_Syntax.n, kc)) with
| ((Microsoft_FStar_Absyn_Syntax.Kind_lam (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Kind_type, _)) | ((Microsoft_FStar_Absyn_Syntax.Kind_effect, _)) | ((Microsoft_FStar_Absyn_Syntax.Kind_unknown, _)) -> begin
(fun ( p ) -> (Support.Microsoft.FStar.Util.return_all k))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_uvar ((u, _24_756)), (_24_760, _24_762, _24_764, args)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (u, args))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((kabr, _24_770)), (_24_774, k::[], _24_778, args)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev (((Support.Prims.fst kabr), args), k))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_arrow ((_24_783, _24_785)), (bs, k'::[], _24_792, _24_794)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, k'))
end
| _24_798 -> begin
(Support.All.failwith "impossible")
end)
in (let _70_8334 = (k' k.Microsoft_FStar_Absyn_Syntax.pos)
in (_70_8334, env))))

let combine_typ = (fun ( t ) ( tc ) ( env ) -> (let t = (compress_typ t)
in (let w = (fun ( f ) -> (f None t.Microsoft_FStar_Absyn_Syntax.pos))
in (let t' = (match ((t.Microsoft_FStar_Absyn_Syntax.n, tc)) with
| ((Microsoft_FStar_Absyn_Syntax.Typ_unknown, _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_const (_), _)) -> begin
t
end
| (Microsoft_FStar_Absyn_Syntax.Typ_lam (_24_823), (bs, _24_827, t::[], _24_831, _24_833)) -> begin
(Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app (_24_837), (_24_840, _24_842, t::[], _24_846, args)) -> begin
(Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t, args)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine (_24_851), ((Support.Microsoft.FStar.Util.Inr (x), _24_856)::[], _24_860, t::[], _24_864, _24_866)) -> begin
(Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, t)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_24_870), (bs, _24_874, _24_876, c::[], _24_880)) -> begin
(Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar ((x, _24_885)), (_24_889, k::[], _24_893, _24_895, _24_897)) -> begin
(Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_uvar' (x, k)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_24_901), (_24_904, k::[], t::[], _24_910, _24_912)) -> begin
(Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed' (t, k)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((_24_916, l))), (_24_922, _24_924, t'::[], _24_928, _24_930)) -> begin
(Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_named ((t', l)))))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern (_24_934)), (_24_938, _24_940, t::[], _24_944, args)) -> begin
(Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, args)))))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((_24_949, l, r, p))), (_24_957, _24_959, t::[], _24_963, _24_965)) -> begin
(Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p)))))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((_24_969, b, r))), (_24_976, _24_978, t::[], _24_982, _24_984)) -> begin
(Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r)))))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((_24_988, _24_990, _24_992))), (_24_997, _24_999, t1::t2::[], _24_1004, _24_1006)) -> begin
(let _70_8375 = (let _70_8374 = (let _70_8373 = (let _70_8372 = (Support.Microsoft.FStar.Util.mk_ref false)
in (t1, t2, _70_8372))
in Microsoft_FStar_Absyn_Syntax.Meta_slack_formula (_70_8373))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' _70_8374))
in (Support.All.pipe_left w _70_8375))
end
| _24_1010 -> begin
(Support.All.failwith "impossible")
end)
in (t', env)))))

let combine_exp = (fun ( e ) ( ec ) ( env ) -> (let e = (compress_exp e)
in (let w = (fun ( f ) -> (f None e.Microsoft_FStar_Absyn_Syntax.pos))
in (let e' = (match ((e.Microsoft_FStar_Absyn_Syntax.n, ec)) with
| ((Microsoft_FStar_Absyn_Syntax.Exp_bvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Exp_fvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Exp_constant (_), _)) -> begin
e
end
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _24_1038)), (_24_1042, _24_1044, t::[], _24_1048, _24_1050)) -> begin
(Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t)))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_abs (_24_1054), (bs, _24_1058, _24_1060, e::[], _24_1064)) -> begin
(Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, e)))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app (_24_1068), (_24_1071, _24_1073, _24_1075, e::[], args)) -> begin
(Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e, args)))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((_24_1082, _24_1084, l)), (_24_1089, _24_1091, t::[], e::[], _24_1097)) -> begin
(Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, l)))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((_24_1101, tag))), (_24_1107, _24_1109, _24_1111, e::[], _24_1115)) -> begin
(Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta' (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, tag)))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_match ((_24_1119, eqns)), (_24_1124, [], [], e1::el, _24_1131)) -> begin
(let rec mk_eqns = (fun ( eqns ) ( el ) -> (match ((eqns, el)) with
| ((p, None, _24_1141)::eqns', e::el') -> begin
(let _70_8405 = (mk_eqns eqns' el')
in ((p, None, e))::_70_8405)
end
| ((p, Some (_24_1151), _24_1154)::eqns', w::e::el') -> begin
(let _70_8406 = (mk_eqns eqns' el')
in ((p, Some (w), e))::_70_8406)
end
| ([], []) -> begin
[]
end
| _24_1167 -> begin
(Support.All.failwith "impossible")
end))
in (let _70_8411 = (let _70_8410 = (let _70_8409 = (mk_eqns eqns el)
in (e1, _70_8409))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _70_8410))
in (Support.All.pipe_left w _70_8411)))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_let (((is_rec, lbs), _24_1172)), (_24_1176, _24_1178, tl, el, _24_1182)) -> begin
(match ((Support.Microsoft.FStar.Util.first_N (Support.List.length lbs) el)) with
| (el, e'::[]) -> begin
(let lbs' = (Support.List.map3 (fun ( lb ) ( t ) ( e ) -> (let _24_1192 = lb
in {Microsoft_FStar_Absyn_Syntax.lbname = _24_1192.Microsoft_FStar_Absyn_Syntax.lbname; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _24_1192.Microsoft_FStar_Absyn_Syntax.lbeff; Microsoft_FStar_Absyn_Syntax.lbdef = e})) lbs tl el)
in (Support.All.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs'), e'))))
end
| _24_1196 -> begin
(Support.All.failwith "impossible")
end)
end
| _24_1198 -> begin
(Support.All.failwith "impossible")
end)
in (e', env)))))

let collect_from_typ = (fun ( f ) ( env ) ( t ) -> (let _70_8535 = (reduce_typ (fun ( _24_1244 ) ( _24_1246 ) ( _24_1248 ) ( env ) ( _24_1251 ) ( k ) -> (k, env)) (fun ( _24_1226 ) ( vt ) ( _24_1229 ) ( env ) ( bvs ) ( t ) -> (let env = (f env t)
in (match ((let _70_8492 = (compress_typ t)
in _70_8492.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) -> begin
(t, env)
end
| _24_1243 -> begin
(vt env bvs t)
end))) (fun ( _24_1216 ) ( _24_1218 ) ( _24_1220 ) ( env ) ( _24_1223 ) ( e ) -> (e, env)) (fun ( k ) ( _24_1213 ) ( env ) -> (k, env)) (fun ( t ) ( _24_1209 ) ( env ) -> (t, env)) (fun ( e ) ( _24_1205 ) ( env ) -> (e, env)) env [] t)
in (Support.All.pipe_left Support.Prims.snd _70_8535)))




