
let log = (fun ( s ) -> ())

let rec compress_typ_aux = (fun ( pos ) ( typ ) -> (match (typ.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (typ) -> begin
(compress_typ_aux pos typ)
end
| _ -> begin
typ
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((_, m)) -> begin
(match ((Support.ST.read m)) with
| None -> begin
typ
end
| Some (t) -> begin
(let t' = (compress_typ_aux pos t)
in (let _22_23 = (Support.ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) when pos -> begin
(compress_typ_aux pos t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (t') -> begin
(let _68_7839 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t', args) None typ.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Prims.pipe_left (compress_typ_aux pos) _68_7839))
end
| _ -> begin
typ
end)
end
| _ -> begin
typ
end))

let compress_typ = (fun ( typ ) -> (compress_typ_aux true typ))

let compress_typ_uvars = (fun ( typ ) -> (compress_typ_aux false typ))

let rec compress_exp_aux = (fun ( meta ) ( exp ) -> (match (exp.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (e) -> begin
(compress_exp_aux meta e)
end
| _ -> begin
exp
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_delayed ((_, _, m)) -> begin
(match ((Support.ST.read m)) with
| None -> begin
exp
end
| Some (e) -> begin
(let e' = (compress_exp_aux meta e)
in (let _22_82 = (Support.ST.op_Colon_Equals m (Some (e')))
in e'))
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) when meta -> begin
(compress_exp_aux meta e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (e') -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e', args) None exp.Microsoft_FStar_Absyn_Syntax.pos)
end
| _ -> begin
exp
end)
end
| _ -> begin
exp
end))

let compress_exp = (fun ( e ) -> (compress_exp_aux true e))

let compress_exp_uvars = (fun ( e ) -> (compress_exp_aux false e))

let rec compress_kind = (fun ( knd ) -> (match (knd.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_delayed ((_, _, m)) -> begin
(match ((Support.ST.read m)) with
| None -> begin
knd
end
| Some (k) -> begin
(let k' = (compress_kind k)
in (let _22_127 = (Support.ST.op_Colon_Equals m (Some (k')))
in k'))
end)
end
| _ -> begin
knd
end))

let left = (fun ( ext ) ( benv ) ( btv ) -> (match ((ext benv (Support.Microsoft.FStar.Util.Inl (btv)))) with
| (benv, Support.Microsoft.FStar.Util.Inl (bvd)) -> begin
(benv, bvd)
end
| _ -> begin
(failwith ("impossible"))
end))

let right = (fun ( ext ) ( benv ) ( bvv ) -> (match ((ext benv (Support.Microsoft.FStar.Util.Inr (bvv)))) with
| (benv, Support.Microsoft.FStar.Util.Inr (bvd)) -> begin
(benv, bvd)
end
| _ -> begin
(failwith ("impossible"))
end))

type boundvar =
(Microsoft_FStar_Absyn_Syntax.btvdef, Microsoft_FStar_Absyn_Syntax.bvvdef) Support.Microsoft.FStar.Util.either

type boundvars =
boundvar list

type ('env, 'm) imap =
'env  ->  boundvars  ->  'm  ->  ('m * 'env)

type ('env, 'm, 'n) mapper =
('env, Microsoft_FStar_Absyn_Syntax.knd) imap  ->  ('env, Microsoft_FStar_Absyn_Syntax.typ) imap  ->  ('env, Microsoft_FStar_Absyn_Syntax.exp) imap  ->  'env  ->  boundvars  ->  'm  ->  ('n * 'env)

let push_tbinder = (fun ( binders ) ( _22_1 ) -> (match (_22_1) with
| None -> begin
binders
end
| Some (a) -> begin
(Support.Microsoft.FStar.Util.Inl (a))::binders
end))

let push_vbinder = (fun ( binders ) ( _22_2 ) -> (match (_22_2) with
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

let leaf_k = (fun ( _22_176 ) -> (match (()) with
| () -> begin
([], [], [], [])
end))

let leaf_te = (fun ( _22_177 ) -> (match (()) with
| () -> begin
([], [], [], [], [])
end))

let rec reduce_kind = (fun ( map_kind' ) ( map_typ' ) ( map_exp' ) ( combine_kind ) ( combine_typ ) ( combine_exp ) ( env ) ( binders ) ( k ) -> (let rec visit_kind = (fun ( env ) ( binders ) ( k ) -> (let k = (compress_kind k)
in (let _22_236 = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_) -> begin
(failwith ("Impossible"))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_lam (_)) | (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) | (Microsoft_FStar_Absyn_Syntax.Kind_unknown) -> begin
((leaf_k ()), env)
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((_, args)) -> begin
(let _22_212 = (map_args map_typ map_exp env binders args)
in (match (_22_212) with
| (args, env) -> begin
(([], [], [], args), env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((kabr, k)) -> begin
(let _22_219 = (map_kind env binders k)
in (match (_22_219) with
| (k, env) -> begin
(let _22_222 = (map_args map_typ map_exp env binders (Support.Prims.snd kabr))
in (match (_22_222) with
| (args, env) -> begin
(([], (k)::[], [], args), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _22_230 = (map_binders map_kind map_typ env binders bs)
in (match (_22_230) with
| (bs, binders, env) -> begin
(let _22_233 = (map_kind env binders k)
in (match (_22_233) with
| (k, env) -> begin
((bs, (k)::[], [], []), env)
end))
end))
end)
in (match (_22_236) with
| (components, env) -> begin
(combine_kind k components env)
end))))
and map_kind = (fun ( env ) ( binders ) ( k ) -> (map_kind' visit_kind map_typ map_exp env binders k))
and map_typ = (fun ( env ) ( binders ) ( t ) -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun ( env ) ( binders ) ( e ) -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_kind env binders k)))
and map_args = (fun ( map_typ ) ( map_exp ) ( env ) ( binders ) ( arguments ) -> (let _22_270 = (Support.List.fold_left (fun ( _22_254 ) ( _22_257 ) -> (match ((_22_254, _22_257)) with
| ((out, env), (arg, imp)) -> begin
(match (arg) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _22_262 = (map_typ env binders t)
in (match (_22_262) with
| (t, env) -> begin
(((Support.Microsoft.FStar.Util.Inl (t), imp))::out, env)
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _22_267 = (map_exp env binders e)
in (match (_22_267) with
| (e, env) -> begin
(((Support.Microsoft.FStar.Util.Inr (e), imp))::out, env)
end))
end)
end)) ([], env) arguments)
in (match (_22_270) with
| (args', env) -> begin
((Support.List.rev args'), env)
end)))
and map_binders = (fun ( map_kind ) ( map_typ ) ( env ) ( binders ) ( bs ) -> (let _22_301 = (Support.Prims.pipe_right bs (Support.List.fold_left (fun ( _22_280 ) ( b ) -> (match (_22_280) with
| (bs, binders, env) -> begin
(match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _22_288 = (map_kind env binders a.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_22_288) with
| (k, env) -> begin
(let binders = (push_tbinder binders (Some (a.Microsoft_FStar_Absyn_Syntax.v)))
in (((Support.Microsoft.FStar.Util.Inl ((bvd_to_bvar_s a.Microsoft_FStar_Absyn_Syntax.v k)), imp))::bs, binders, env))
end))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _22_296 = (map_typ env binders x.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_22_296) with
| (t, env) -> begin
(let binders = (push_vbinder binders (Some (x.Microsoft_FStar_Absyn_Syntax.v)))
in (((Support.Microsoft.FStar.Util.Inr ((bvd_to_bvar_s x.Microsoft_FStar_Absyn_Syntax.v t)), imp))::bs, binders, env))
end))
end)
end)) ([], binders, env)))
in (match (_22_301) with
| (bs, binders, env) -> begin
((Support.List.rev bs), binders, env)
end)))
and reduce_typ = (fun ( map_kind' ) ( map_typ' ) ( map_exp' ) ( combine_kind ) ( combine_typ ) ( combine_exp ) ( env ) ( binders ) ( t ) -> (let rec map_comp = (fun ( env ) ( binders ) ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _22_324 = (map_typ env binders t)
in (match (_22_324) with
| (t, env) -> begin
(let _68_8123 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (_68_8123, env))
end))
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _22_329 = (map_typ env binders ct.Microsoft_FStar_Absyn_Syntax.result_typ)
in (match (_22_329) with
| (t, env) -> begin
(let _22_332 = (map_args map_typ map_exp env binders ct.Microsoft_FStar_Absyn_Syntax.effect_args)
in (match (_22_332) with
| (args, env) -> begin
(let _22_343 = (Support.Prims.pipe_right ct.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.fold_map (fun ( env ) ( flag ) -> (match (flag) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (arg) -> begin
(let _22_339 = (map_exp env binders arg)
in (match (_22_339) with
| (arg, env) -> begin
(env, Microsoft_FStar_Absyn_Syntax.DECREASES (arg))
end))
end
| f -> begin
(env, f)
end)) env))
in (match (_22_343) with
| (env, flags) -> begin
(let _68_8126 = (Microsoft_FStar_Absyn_Syntax.mk_Comp (let _22_344 = ct
in {Microsoft_FStar_Absyn_Syntax.effect_name = _22_344.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = args; Microsoft_FStar_Absyn_Syntax.flags = flags}))
in (_68_8126, env))
end))
end))
end))
end))
and visit_typ = (fun ( env ) ( binders ) ( t ) -> (let _22_494 = (match ((let _68_8130 = (compress_typ t)
in _68_8130.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_) -> begin
(failwith ("Impossible"))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) -> begin
(let _22_362 = (map_typ env binders t)
in (match (_22_362) with
| (_, env) -> begin
((leaf_te ()), env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, args)) -> begin
(let _22_369 = (map_typ env binders t)
in (match (_22_369) with
| (t, env) -> begin
(let _22_372 = (map_args map_typ map_exp env binders args)
in (match (_22_372) with
| (args, env) -> begin
(([], [], (t)::[], [], args), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((axs, t)) -> begin
(let _22_380 = (map_binders map_kind map_typ env binders axs)
in (match (_22_380) with
| (axs, binders, env) -> begin
(let _22_383 = (map_typ env binders t)
in (match (_22_383) with
| (t, env) -> begin
((axs, [], (t)::[], [], []), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, t2)) -> begin
(let _22_391 = (map_binders map_kind map_typ env binders (((Support.Microsoft.FStar.Util.Inr (x), None))::[]))
in (match (_22_391) with
| (bs, binders, env) -> begin
(let _22_394 = (map_typ env binders t2)
in (match (_22_394) with
| (t2, env) -> begin
((bs, [], (t2)::[], [], []), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let _22_402 = (map_binders map_kind map_typ env binders bs)
in (match (_22_402) with
| (bs, binders, env) -> begin
(let _22_405 = (map_comp env binders c)
in (match (_22_405) with
| (c, env) -> begin
((bs, [], [], (c)::[], []), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, k)) -> begin
(let _22_412 = (map_typ env binders t)
in (match (_22_412) with
| (t, env) -> begin
(let _22_415 = (map_kind env binders k)
in (match (_22_415) with
| (k, env) -> begin
(([], (k)::[], (t)::[], [], []), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((_, k)) -> begin
(let _22_423 = (map_kind env binders k)
in (match (_22_423) with
| (k, env) -> begin
(([], (k)::[], [], [], []), env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, flag))) -> begin
(let _22_432 = (map_typ env binders t1)
in (match (_22_432) with
| (t1, env) -> begin
(let _22_435 = (map_typ env binders t2)
in (match (_22_435) with
| (t2, env) -> begin
(([], [], (t1)::(t2)::[], [], []), env)
end))
end))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, _, _, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _, _)))) -> begin
(let _22_460 = (map_typ env binders t)
in (match (_22_460) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps))) -> begin
(let _22_468 = (map_typ env binders t)
in (match (_22_468) with
| (t, env) -> begin
(let _22_491 = (Support.List.fold_left (fun ( _22_471 ) ( arg ) -> (match (_22_471) with
| (pats, env) -> begin
(match (arg) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(let _22_480 = (map_typ env binders t)
in (match (_22_480) with
| (t, env) -> begin
(((Support.Microsoft.FStar.Util.Inl (t), None))::pats, env)
end))
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(let _22_488 = (map_exp env binders e)
in (match (_22_488) with
| (e, env) -> begin
(((Support.Microsoft.FStar.Util.Inr (e), None))::pats, env)
end))
end)
end)) ([], env) ps)
in (match (_22_491) with
| (pats, env) -> begin
(([], [], (t)::[], [], (Support.List.rev pats)), env)
end))
end))
end)
in (match (_22_494) with
| (components, env) -> begin
(combine_typ t components env)
end)))
and map_kind = (fun ( env ) ( binders ) ( k ) -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun ( env ) ( binders ) ( t ) -> (map_typ' map_kind visit_typ map_exp env binders t))
and map_exp = (fun ( env ) ( binders ) ( e ) -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_typ env binders t)))
and reduce_exp = (fun ( map_kind' ) ( map_typ' ) ( map_exp' ) ( combine_kind ) ( combine_typ ) ( combine_exp ) ( env ) ( binders ) ( e ) -> (let rec map_exps = (fun ( env ) ( binders ) ( el ) -> (let _22_532 = (Support.List.fold_left (fun ( _22_525 ) ( e ) -> (match (_22_525) with
| (out, env) -> begin
(let _22_529 = (map_exp env binders e)
in (match (_22_529) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_22_532) with
| (el, env) -> begin
((Support.List.rev el), env)
end)))
and map_exps_with_binders = (fun ( env ) ( el ) -> (let _22_546 = (Support.List.fold_left (fun ( _22_537 ) ( _22_540 ) -> (match ((_22_537, _22_540)) with
| ((out, env), (b, e)) -> begin
(let _22_543 = (map_exp env b e)
in (match (_22_543) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_22_546) with
| (el, env) -> begin
((Support.List.rev el), env)
end)))
and map_kind = (fun ( env ) ( binders ) ( k ) -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun ( env ) ( binders ) ( t ) -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun ( env ) ( binders ) ( e ) -> (map_exp' map_kind map_typ visit_exp env binders e))
and visit_exp = (fun ( env ) ( binders ) ( e ) -> (let e = (compress_exp_uvars e)
in (let _22_731 = (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_) -> begin
(failwith ("impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(let _22_571 = (map_exp env binders e)
in (match (_22_571) with
| (e, env) -> begin
(([], [], [], (e)::[], []), env)
end))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) -> begin
((leaf_te ()), env)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((_, t)) -> begin
(let _22_588 = (map_typ env binders t)
in (match (_22_588) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, e)) -> begin
(let _22_596 = (map_binders map_kind map_typ env binders bs)
in (match (_22_596) with
| (bs, binders, env) -> begin
(let _22_599 = (map_exp env binders e)
in (match (_22_599) with
| (e, env) -> begin
((bs, [], [], (e)::[], []), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((e, args)) -> begin
(let _22_606 = (map_exp env binders e)
in (match (_22_606) with
| (e, env) -> begin
(let _22_609 = (map_args map_typ map_exp env binders args)
in (match (_22_609) with
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
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _)) -> begin
(push_vbinder b (Some (x.Microsoft_FStar_Absyn_Syntax.v)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (t) -> begin
(push_tbinder b (Some (t.Microsoft_FStar_Absyn_Syntax.v)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((_, _, pats)) -> begin
(Support.List.fold_left pat_binders b pats)
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (p::_) -> begin
(pat_binders b p)
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(failwith ("impossible"))
end))
in (let branches = (Support.Prims.pipe_right pl (Support.List.collect (fun ( _22_656 ) -> (match (_22_656) with
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
in (let _22_664 = (map_exps_with_binders env (((binders, e1))::branches))
in (match (_22_664) with
| (el, env) -> begin
(([], [], [], el, []), env)
end))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _)) -> begin
(let _22_673 = (map_typ env binders t)
in (match (_22_673) with
| (t, env) -> begin
(let _22_676 = (map_exp env binders e)
in (match (_22_676) with
| (e, env) -> begin
(([], [], (t)::[], (e)::[], []), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, lb::[]), e2)) -> begin
(let _22_686 = (map_typ env binders lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (match (_22_686) with
| (t, env) -> begin
(let binders' = (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _ -> begin
binders
end)
in (let _22_694 = (map_exps_with_binders env (((binders, lb.Microsoft_FStar_Absyn_Syntax.lbdef))::((binders', e2))::[]))
in (match (_22_694) with
| (el, env) -> begin
(([], [], (t)::[], el, []), env)
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((true, bvdt_tl), e)) -> begin
(let tl = (Support.List.map (fun ( lb ) -> lb.Microsoft_FStar_Absyn_Syntax.lbtyp) bvdt_tl)
in (let el = (Support.List.map (fun ( lb ) -> lb.Microsoft_FStar_Absyn_Syntax.lbdef) bvdt_tl)
in (let _22_714 = (Support.Prims.pipe_right tl (Support.List.fold_left (fun ( _22_707 ) ( t ) -> (match (_22_707) with
| (tl, env) -> begin
(let _22_711 = (map_typ env binders t)
in (match (_22_711) with
| (t, env) -> begin
((t)::tl, env)
end))
end)) ([], env)))
in (match (_22_714) with
| (tl, env) -> begin
(let tl = (Support.List.rev tl)
in (let binders = (Support.List.fold_left (fun ( binders ) ( lb ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _ -> begin
binders
end)) binders bvdt_tl)
in (let _22_725 = (map_exps env binders (Support.List.append el ((e)::[])))
in (match (_22_725) with
| (el, env) -> begin
(([], [], tl, el, []), env)
end))))
end))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (_) -> begin
(failwith ("impossible"))
end)
in (match (_22_731) with
| (components, env) -> begin
(combine_exp e components env)
end))))
in (map_exp env binders e)))

let combine_kind = (fun ( k ) ( kc ) ( env ) -> (let k' = (match ((k.Microsoft_FStar_Absyn_Syntax.n, kc)) with
| ((Microsoft_FStar_Absyn_Syntax.Kind_lam (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Kind_type, _)) | ((Microsoft_FStar_Absyn_Syntax.Kind_effect, _)) | ((Microsoft_FStar_Absyn_Syntax.Kind_unknown, _)) -> begin
(fun ( p ) -> (Support.Microsoft.FStar.Util.return_all k))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_uvar ((u, _)), (_, _, _, args)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_uvar (u, args))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((kabr, _)), (_, k::[], _, args)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_abbrev (((Support.Prims.fst kabr), args), k))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_arrow ((_, _)), (bs, k'::[], _, _)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, k'))
end
| _ -> begin
(failwith ("impossible"))
end)
in (let _68_8208 = (k' k.Microsoft_FStar_Absyn_Syntax.pos)
in (_68_8208, env))))

let combine_typ = (fun ( t ) ( tc ) ( env ) -> (let t = (compress_typ t)
in (let w = (fun ( f ) -> (f None t.Microsoft_FStar_Absyn_Syntax.pos))
in (let t' = (match ((t.Microsoft_FStar_Absyn_Syntax.n, tc)) with
| ((Microsoft_FStar_Absyn_Syntax.Typ_unknown, _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_const (_), _)) -> begin
t
end
| (Microsoft_FStar_Absyn_Syntax.Typ_lam (_), (bs, _, t::[], _, _)) -> begin
(Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app (_), (_, _, t::[], _, args)) -> begin
(Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t, args)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine (_), ((Support.Microsoft.FStar.Util.Inr (x), _)::[], _, t::[], _, _)) -> begin
(Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, t)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_), (bs, _, _, c::[], _)) -> begin
(Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar ((x, _)), (_, k::[], _, _, _)) -> begin
(Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_uvar' (x, k)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_), (_, k::[], t::[], _, _)) -> begin
(Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed' (t, k)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((_, l))), (_, _, t'::[], _, _)) -> begin
(Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_named ((t', l)))))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern (_)), (_, _, t::[], _, args)) -> begin
(Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, args)))))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((_, l, r, p))), (_, _, t::[], _, _)) -> begin
(Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p)))))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((_, b, r))), (_, _, t::[], _, _)) -> begin
(Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r)))))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((_, _, _))), (_, _, t1::t2::[], _, _)) -> begin
(let _68_8249 = (let _68_8248 = (let _68_8247 = (let _68_8246 = (Support.Microsoft.FStar.Util.mk_ref false)
in (t1, t2, _68_8246))
in Microsoft_FStar_Absyn_Syntax.Meta_slack_formula (_68_8247))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' _68_8248))
in (Support.Prims.pipe_left w _68_8249))
end
| _ -> begin
(failwith ("impossible"))
end)
in (t', env)))))

let combine_exp = (fun ( e ) ( ec ) ( env ) -> (let e = (compress_exp e)
in (let w = (fun ( f ) -> (f None e.Microsoft_FStar_Absyn_Syntax.pos))
in (let e' = (match ((e.Microsoft_FStar_Absyn_Syntax.n, ec)) with
| ((Microsoft_FStar_Absyn_Syntax.Exp_bvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Exp_fvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Exp_constant (_), _)) -> begin
e
end
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _)), (_, _, t::[], _, _)) -> begin
(Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t)))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_abs (_), (bs, _, _, e::[], _)) -> begin
(Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, e)))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app (_), (_, _, _, e::[], args)) -> begin
(Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e, args)))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((_, _, l)), (_, _, t::[], e::[], _)) -> begin
(Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, l)))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((_, tag))), (_, _, _, e::[], _)) -> begin
(Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta' (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, tag)))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_match ((_, eqns)), (_, [], [], e1::el, _)) -> begin
(let rec mk_eqns = (fun ( eqns ) ( el ) -> (match ((eqns, el)) with
| ((p, None, _)::eqns', e::el') -> begin
(let _68_8279 = (mk_eqns eqns' el')
in ((p, None, e))::_68_8279)
end
| ((p, Some (_), _)::eqns', w::e::el') -> begin
(let _68_8280 = (mk_eqns eqns' el')
in ((p, Some (w), e))::_68_8280)
end
| ([], []) -> begin
[]
end
| _ -> begin
(failwith ("impossible"))
end))
in (let _68_8285 = (let _68_8284 = (let _68_8283 = (mk_eqns eqns el)
in (e1, _68_8283))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_match _68_8284))
in (Support.Prims.pipe_left w _68_8285)))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_let (((is_rec, lbs), _)), (_, _, tl, el, _)) -> begin
(match ((Support.Microsoft.FStar.Util.first_N (Support.List.length lbs) el)) with
| (el, e'::[]) -> begin
(let lbs' = (Support.List.map3 (fun ( lb ) ( t ) ( e ) -> (let _22_1192 = lb
in {Microsoft_FStar_Absyn_Syntax.lbname = _22_1192.Microsoft_FStar_Absyn_Syntax.lbname; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _22_1192.Microsoft_FStar_Absyn_Syntax.lbeff; Microsoft_FStar_Absyn_Syntax.lbdef = e})) lbs tl el)
in (Support.Prims.pipe_left w (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs'), e'))))
end
| _ -> begin
(failwith ("impossible"))
end)
end
| _ -> begin
(failwith ("impossible"))
end)
in (e', env)))))

let collect_from_typ = (fun ( f ) ( env ) ( t ) -> (let _68_8409 = (reduce_typ (fun ( _22_1244 ) ( _22_1246 ) ( _22_1248 ) ( env ) ( _22_1251 ) ( k ) -> (k, env)) (fun ( _22_1226 ) ( vt ) ( _22_1229 ) ( env ) ( bvs ) ( t ) -> (let env = (f env t)
in (match ((let _68_8366 = (compress_typ t)
in _68_8366.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) -> begin
(t, env)
end
| _ -> begin
(vt env bvs t)
end))) (fun ( _22_1216 ) ( _22_1218 ) ( _22_1220 ) ( env ) ( _22_1223 ) ( e ) -> (e, env)) (fun ( k ) ( _22_1213 ) ( env ) -> (k, env)) (fun ( t ) ( _22_1209 ) ( env ) -> (t, env)) (fun ( e ) ( _22_1205 ) ( env ) -> (e, env)) env [] t)
in (Support.Prims.pipe_left Support.Prims.snd _68_8409)))




