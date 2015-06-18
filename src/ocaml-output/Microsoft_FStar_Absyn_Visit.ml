
let log = (fun s -> ())

let rec compress_typ_aux = (fun pos typ -> (match (typ.Microsoft_FStar_Absyn_Syntax.n) with
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
(match ((! (m))) with
| None -> begin
typ
end
| Some (t) -> begin
(let t' = (compress_typ_aux pos t)
in (let _36490 = (m := Some (t'))
in t'))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) when pos -> begin
(compress_typ_aux pos t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (t') -> begin
((compress_typ_aux pos) (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t', args) None typ.Microsoft_FStar_Absyn_Syntax.pos))
end
| _ -> begin
typ
end)
end
| _ -> begin
typ
end))

let compress_typ = (fun typ -> (compress_typ_aux true typ))

let compress_typ_uvars = (fun typ -> (compress_typ_aux false typ))

let rec compress_exp_aux = (fun meta exp -> (match (exp.Microsoft_FStar_Absyn_Syntax.n) with
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
(match ((! (m))) with
| None -> begin
exp
end
| Some (e) -> begin
(let e' = (compress_exp_aux meta e)
in (let _36549 = (m := Some (e'))
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

let compress_exp = (fun e -> (compress_exp_aux true e))

let compress_exp_uvars = (fun e -> (compress_exp_aux false e))

let rec compress_kind = (fun knd -> (match (knd.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_delayed ((_, _, m)) -> begin
(match ((! (m))) with
| None -> begin
knd
end
| Some (k) -> begin
(let k' = (compress_kind k)
in (let _36594 = (m := Some (k'))
in k'))
end)
end
| _ -> begin
knd
end))

let left = (fun ext benv btv -> (match ((ext benv (Support.Microsoft.FStar.Util.Inl (btv)))) with
| (benv, Support.Microsoft.FStar.Util.Inl (bvd)) -> begin
(benv, bvd)
end
| _ -> begin
(failwith "impossible")
end))

let right = (fun ext benv bvv -> (match ((ext benv (Support.Microsoft.FStar.Util.Inr (bvv)))) with
| (benv, Support.Microsoft.FStar.Util.Inr (bvd)) -> begin
(benv, bvd)
end
| _ -> begin
(failwith "impossible")
end))

type boundvar =
(Microsoft_FStar_Absyn_Syntax.btvdef, Microsoft_FStar_Absyn_Syntax.bvvdef) Support.Microsoft.FStar.Util.either

type boundvars =
boundvar list

type ('env, 'm) imap =
'env  ->  boundvars  ->  'm  ->  ('m * 'env)

type ('env, 'm, 'n) mapper =
('env, Microsoft_FStar_Absyn_Syntax.knd) imap  ->  ('env, Microsoft_FStar_Absyn_Syntax.typ) imap  ->  ('env, Microsoft_FStar_Absyn_Syntax.exp) imap  ->  'env  ->  boundvars  ->  'm  ->  ('n * 'env)

let push_tbinder = (fun binders _36468 -> (match (_36468) with
| None -> begin
binders
end
| Some (a) -> begin
(Support.Microsoft.FStar.Util.Inl (a))::binders
end))

let push_vbinder = (fun binders _36469 -> (match (_36469) with
| None -> begin
binders
end
| Some (a) -> begin
(Support.Microsoft.FStar.Util.Inr (a))::binders
end))

let bvd_to_bvar_s = (fun bvd sort -> {Microsoft_FStar_Absyn_Syntax.v = bvd; Microsoft_FStar_Absyn_Syntax.sort = sort; Microsoft_FStar_Absyn_Syntax.p = bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idRange})

let tbinder_opt = (fun aopt k -> (match (aopt) with
| None -> begin
[]
end
| Some (a) -> begin
(Support.Microsoft.FStar.Util.Inl ((bvd_to_bvar_s a k)))::[]
end))

let vbinder_opt = (fun aopt t -> (match (aopt) with
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

let leaf_k = (fun _36643 -> (match (_36643) with
| () -> begin
([], [], [], [])
end))

let leaf_te = (fun _36644 -> (match (_36644) with
| () -> begin
([], [], [], [], [])
end))

let rec reduce_kind = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k -> (let rec visit_kind = (fun env binders k -> (let k = (compress_kind k)
in (let _36703 = (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_) -> begin
(failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Kind_lam (_)) | (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) | (Microsoft_FStar_Absyn_Syntax.Kind_unknown) -> begin
((leaf_k ()), env)
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((_, args)) -> begin
(let _36679 = (map_args map_typ map_exp env binders args)
in (match (_36679) with
| (args, env) -> begin
(([], [], [], args), env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((kabr, k)) -> begin
(let _36686 = (map_kind env binders k)
in (match (_36686) with
| (k, env) -> begin
(let _36689 = (map_args map_typ map_exp env binders (Support.Prims.snd kabr))
in (match (_36689) with
| (args, env) -> begin
(([], (k)::[], [], args), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _36697 = (map_binders map_kind map_typ env binders bs)
in (match (_36697) with
| (bs, binders, env) -> begin
(let _36700 = (map_kind env binders k)
in (match (_36700) with
| (k, env) -> begin
((bs, (k)::[], [], []), env)
end))
end))
end)
in (match (_36703) with
| (components, env) -> begin
(combine_kind k components env)
end))))
and map_kind = (fun env binders k -> (map_kind' visit_kind map_typ map_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_kind env binders k)))
and map_args = (fun map_typ map_exp env binders arguments -> (let _36737 = (Support.List.fold_left (fun _36721 _36724 -> (match ((_36721, _36724)) with
| ((out, env), (arg, imp)) -> begin
(match (arg) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _36729 = (map_typ env binders t)
in (match (_36729) with
| (t, env) -> begin
(((Support.Microsoft.FStar.Util.Inl (t), imp))::out, env)
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _36734 = (map_exp env binders e)
in (match (_36734) with
| (e, env) -> begin
(((Support.Microsoft.FStar.Util.Inr (e), imp))::out, env)
end))
end)
end)) ([], env) arguments)
in (match (_36737) with
| (args', env) -> begin
((Support.List.rev args'), env)
end)))
and map_binders = (fun map_kind map_typ env binders bs -> (let _36768 = ((Support.List.fold_left (fun _36747 b -> (match (_36747) with
| (bs, binders, env) -> begin
(match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _36755 = (map_kind env binders a.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_36755) with
| (k, env) -> begin
(let binders = (push_tbinder binders (Some (a.Microsoft_FStar_Absyn_Syntax.v)))
in (((Support.Microsoft.FStar.Util.Inl ((bvd_to_bvar_s a.Microsoft_FStar_Absyn_Syntax.v k)), imp))::bs, binders, env))
end))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _36763 = (map_typ env binders x.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_36763) with
| (t, env) -> begin
(let binders = (push_vbinder binders (Some (x.Microsoft_FStar_Absyn_Syntax.v)))
in (((Support.Microsoft.FStar.Util.Inr ((bvd_to_bvar_s x.Microsoft_FStar_Absyn_Syntax.v t)), imp))::bs, binders, env))
end))
end)
end)) ([], binders, env)) bs)
in (match (_36768) with
| (bs, binders, env) -> begin
((Support.List.rev bs), binders, env)
end)))
and reduce_typ = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t -> (let rec map_comp = (fun env binders c -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _36791 = (map_typ env binders t)
in (match (_36791) with
| (t, env) -> begin
((Microsoft_FStar_Absyn_Syntax.mk_Total t), env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _36796 = (map_typ env binders ct.Microsoft_FStar_Absyn_Syntax.result_typ)
in (match (_36796) with
| (t, env) -> begin
(let _36799 = (map_args map_typ map_exp env binders ct.Microsoft_FStar_Absyn_Syntax.effect_args)
in (match (_36799) with
| (args, env) -> begin
(let _36810 = ((Support.Microsoft.FStar.Util.fold_map (fun env flag -> (match (flag) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (arg) -> begin
(let _36806 = (map_exp env binders arg)
in (match (_36806) with
| (arg, env) -> begin
(env, Microsoft_FStar_Absyn_Syntax.DECREASES (arg))
end))
end
| f -> begin
(env, f)
end)) env) ct.Microsoft_FStar_Absyn_Syntax.flags)
in (match (_36810) with
| (env, flags) -> begin
((Microsoft_FStar_Absyn_Syntax.mk_Comp (let _36811 = ct
in {Microsoft_FStar_Absyn_Syntax.effect_name = _36811.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = args; Microsoft_FStar_Absyn_Syntax.flags = flags})), env)
end))
end))
end))
end))
and visit_typ = (fun env binders t -> (let _36961 = (match ((compress_typ t).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_) -> begin
(failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) -> begin
(let _36829 = (map_typ env binders t)
in (match (_36829) with
| (_, env) -> begin
((leaf_te ()), env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, args)) -> begin
(let _36836 = (map_typ env binders t)
in (match (_36836) with
| (t, env) -> begin
(let _36839 = (map_args map_typ map_exp env binders args)
in (match (_36839) with
| (args, env) -> begin
(([], [], (t)::[], [], args), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((axs, t)) -> begin
(let _36847 = (map_binders map_kind map_typ env binders axs)
in (match (_36847) with
| (axs, binders, env) -> begin
(let _36850 = (map_typ env binders t)
in (match (_36850) with
| (t, env) -> begin
((axs, [], (t)::[], [], []), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, t2)) -> begin
(let _36858 = (map_binders map_kind map_typ env binders (((Support.Microsoft.FStar.Util.Inr (x), None))::[]))
in (match (_36858) with
| (bs, binders, env) -> begin
(let _36861 = (map_typ env binders t2)
in (match (_36861) with
| (t2, env) -> begin
((bs, [], (t2)::[], [], []), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(let _36869 = (map_binders map_kind map_typ env binders bs)
in (match (_36869) with
| (bs, binders, env) -> begin
(let _36872 = (map_comp env binders c)
in (match (_36872) with
| (c, env) -> begin
((bs, [], [], (c)::[], []), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, k)) -> begin
(let _36879 = (map_typ env binders t)
in (match (_36879) with
| (t, env) -> begin
(let _36882 = (map_kind env binders k)
in (match (_36882) with
| (k, env) -> begin
(([], (k)::[], (t)::[], [], []), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((_, k)) -> begin
(let _36890 = (map_kind env binders k)
in (match (_36890) with
| (k, env) -> begin
(([], (k)::[], [], [], []), env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, flag))) -> begin
(let _36899 = (map_typ env binders t1)
in (match (_36899) with
| (t1, env) -> begin
(let _36902 = (map_typ env binders t2)
in (match (_36902) with
| (t2, env) -> begin
(([], [], (t1)::(t2)::[], [], []), env)
end))
end))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, _, _, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _, _)))) -> begin
(let _36927 = (map_typ env binders t)
in (match (_36927) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps))) -> begin
(let _36935 = (map_typ env binders t)
in (match (_36935) with
| (t, env) -> begin
(let _36958 = (Support.List.fold_left (fun _36938 arg -> (match (_36938) with
| (pats, env) -> begin
(match (arg) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(let _36947 = (map_typ env binders t)
in (match (_36947) with
| (t, env) -> begin
(((Support.Microsoft.FStar.Util.Inl (t), None))::pats, env)
end))
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(let _36955 = (map_exp env binders e)
in (match (_36955) with
| (e, env) -> begin
(((Support.Microsoft.FStar.Util.Inr (e), None))::pats, env)
end))
end)
end)) ([], env) ps)
in (match (_36958) with
| (pats, env) -> begin
(([], [], (t)::[], [], (Support.List.rev pats)), env)
end))
end))
end)
in (match (_36961) with
| (components, env) -> begin
(combine_typ t components env)
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (map_typ' map_kind visit_typ map_exp env binders t))
and map_exp = (fun env binders e -> (reduce_exp map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e))
in (map_typ env binders t)))
and reduce_exp = (fun map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders e -> (let rec map_exps = (fun env binders el -> (let _36999 = (Support.List.fold_left (fun _36992 e -> (match (_36992) with
| (out, env) -> begin
(let _36996 = (map_exp env binders e)
in (match (_36996) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_36999) with
| (el, env) -> begin
((Support.List.rev el), env)
end)))
and map_exps_with_binders = (fun env el -> (let _37013 = (Support.List.fold_left (fun _37004 _37007 -> (match ((_37004, _37007)) with
| ((out, env), (b, e)) -> begin
(let _37010 = (map_exp env b e)
in (match (_37010) with
| (e, env) -> begin
((e)::out, env)
end))
end)) ([], env) el)
in (match (_37013) with
| (el, env) -> begin
((Support.List.rev el), env)
end)))
and map_kind = (fun env binders k -> (reduce_kind map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders k))
and map_typ = (fun env binders t -> (reduce_typ map_kind' map_typ' map_exp' combine_kind combine_typ combine_exp env binders t))
and map_exp = (fun env binders e -> (map_exp' map_kind map_typ visit_exp env binders e))
and visit_exp = (fun env binders e -> (let e = (compress_exp_uvars e)
in (let _37212 = (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_) -> begin
(failwith "impossible")
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(let _37038 = (map_exp env binders e)
in (match (_37038) with
| (e, env) -> begin
(([], [], [], (e)::[], []), env)
end))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) -> begin
((leaf_te ()), env)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((_, t)) -> begin
(let _37055 = (map_typ env binders t)
in (match (_37055) with
| (t, env) -> begin
(([], [], (t)::[], [], []), env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, e)) -> begin
(let _37063 = (map_binders map_kind map_typ env binders bs)
in (match (_37063) with
| (bs, binders, env) -> begin
(let _37066 = (map_exp env binders e)
in (match (_37066) with
| (e, env) -> begin
((bs, [], [], (e)::[], []), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((e, args)) -> begin
(let _37073 = (map_exp env binders e)
in (match (_37073) with
| (e, env) -> begin
(let _37076 = (map_args map_typ map_exp env binders args)
in (match (_37076) with
| (args, env) -> begin
(([], [], [], (e)::[], args), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e1, pl)) -> begin
(let rec pat_binders = (fun b p -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_constant (_)) -> begin
b
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _)) -> begin
(push_vbinder b (Some (x.Microsoft_FStar_Absyn_Syntax.v)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (t) -> begin
(push_tbinder b (Some (t.Microsoft_FStar_Absyn_Syntax.v)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((_, pats)) -> begin
(Support.List.fold_left pat_binders b pats)
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (p::_) -> begin
(pat_binders b p)
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj ([]) -> begin
(failwith "impossible")
end))
in (let branches = ((Support.List.collect (fun _37121 -> (match (_37121) with
| (p, w, e) -> begin
(let binders = (pat_binders binders p)
in (match (w) with
| None -> begin
((binders, e))::[]
end
| Some (w) -> begin
((binders, w))::((binders, e))::[]
end))
end))) pl)
in (let _37129 = (map_exps_with_binders env (((binders, e1))::branches))
in (match (_37129) with
| (el, env) -> begin
(([], [], [], el, []), env)
end))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t)) -> begin
(let _37136 = (map_typ env binders t)
in (match (_37136) with
| (t, env) -> begin
(let _37139 = (map_exp env binders e)
in (match (_37139) with
| (e, env) -> begin
(([], [], (t)::[], (e)::[], []), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, (x, t, e1)::[]), e2)) -> begin
(let _37152 = (map_typ env binders t)
in (match (_37152) with
| (t, env) -> begin
(let binders' = (match (x) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _ -> begin
binders
end)
in (let _37160 = (map_exps_with_binders env (((binders, e1))::((binders', e2))::[]))
in (match (_37160) with
| (el, env) -> begin
(([], [], (t)::[], el, []), env)
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((true, bvdt_tl), e)) -> begin
(let tl = (Support.List.map (fun _37172 -> (match (_37172) with
| (_, t, _) -> begin
t
end)) bvdt_tl)
in (let el = (Support.List.map (fun _37179 -> (match (_37179) with
| (_, _, e) -> begin
e
end)) bvdt_tl)
in (let _37190 = ((Support.List.fold_left (fun _37183 t -> (match (_37183) with
| (tl, env) -> begin
(let _37187 = (map_typ env binders t)
in (match (_37187) with
| (t, env) -> begin
((t)::tl, env)
end))
end)) ([], env)) tl)
in (match (_37190) with
| (tl, env) -> begin
(let tl = (Support.List.rev tl)
in (let binders = (Support.List.fold_left (fun binders _37198 -> (match (_37198) with
| (x, _, _) -> begin
(match (x) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(push_vbinder binders (Some (x)))
end
| _ -> begin
binders
end)
end)) binders bvdt_tl)
in (let _37206 = (map_exps env binders (Support.List.append el ((e)::[])))
in (match (_37206) with
| (el, env) -> begin
(([], [], tl, el, []), env)
end))))
end))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (_) -> begin
(failwith "impossible")
end)
in (match (_37212) with
| (components, env) -> begin
(combine_exp e components env)
end))))
in (map_exp env binders e)))

let combine_kind = (fun k kc env -> (let k' = (match ((k.Microsoft_FStar_Absyn_Syntax.n, kc)) with
| ((Microsoft_FStar_Absyn_Syntax.Kind_lam (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Kind_type, _)) | ((Microsoft_FStar_Absyn_Syntax.Kind_effect, _)) | ((Microsoft_FStar_Absyn_Syntax.Kind_unknown, _)) -> begin
(fun p -> (Support.Microsoft.FStar.Util.return_all k))
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
(failwith "impossible")
end)
in ((k' k.Microsoft_FStar_Absyn_Syntax.pos), env)))

let combine_typ = (fun t tc env -> (let t = (compress_typ t)
in (let w = (fun f -> (f None t.Microsoft_FStar_Absyn_Syntax.pos))
in (let t' = (match ((t.Microsoft_FStar_Absyn_Syntax.n, tc)) with
| ((Microsoft_FStar_Absyn_Syntax.Typ_unknown, _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Typ_const (_), _)) -> begin
t
end
| (Microsoft_FStar_Absyn_Syntax.Typ_lam (_), (bs, _, t::[], _, _)) -> begin
(w (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_app (_), (_, _, t::[], _, args)) -> begin
(w (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (t, args)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_refine (_), ((Support.Microsoft.FStar.Util.Inr (x), _)::[], _, t::[], _, _)) -> begin
(w (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, t)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_), (bs, _, _, c::[], _)) -> begin
(w (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_uvar ((x, _)), (_, k::[], _, _, _)) -> begin
(w (Microsoft_FStar_Absyn_Syntax.mk_Typ_uvar' (x, k)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_), (_, k::[], t::[], _, _)) -> begin
(w (Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed' (t, k)))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((_, l))), (_, _, t'::[], _, _)) -> begin
(w (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_named ((t', l)))))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern (_)), (_, _, t::[], _, args)) -> begin
(w (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, args)))))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((_, l, r, p))), (_, _, t::[], _, _)) -> begin
(w (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p)))))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((_, b, r))), (_, _, t::[], _, _)) -> begin
(w (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r)))))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((_, _, _))), (_, _, t1::t2::[], _, _)) -> begin
(w (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta' (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, (Support.Microsoft.FStar.Util.mk_ref false))))))
end
| _ -> begin
(failwith "impossible")
end)
in (t', env)))))

let combine_exp = (fun e ec env -> (let e = (compress_exp e)
in (let w = (fun f -> (f None e.Microsoft_FStar_Absyn_Syntax.pos))
in (let e' = (match ((e.Microsoft_FStar_Absyn_Syntax.n, ec)) with
| ((Microsoft_FStar_Absyn_Syntax.Exp_bvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Exp_fvar (_), _)) | ((Microsoft_FStar_Absyn_Syntax.Exp_constant (_), _)) -> begin
e
end
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _)), (_, _, t::[], _, _)) -> begin
(w (Microsoft_FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t)))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_abs (_), (bs, _, _, e::[], _)) -> begin
(w (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs, e)))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_app (_), (_, _, _, e::[], args)) -> begin
(w (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (e, args)))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed (_), (_, _, t::[], e::[], _)) -> begin
(w (Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed' (e, t)))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((_, tag))), (_, _, _, e::[], _)) -> begin
(w (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta' (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, tag)))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_match ((_, eqns)), (_, [], [], e1::el, _)) -> begin
(let rec mk_eqns = (fun eqns el -> (match ((eqns, el)) with
| ((p, None, _)::eqns', e::el') -> begin
((p, None, e))::(mk_eqns eqns' el')
end
| ((p, Some (_), _)::eqns', w::e::el') -> begin
((p, Some (w), e))::(mk_eqns eqns' el')
end
| ([], []) -> begin
[]
end
| _ -> begin
(failwith "impossible")
end))
in (w (Microsoft_FStar_Absyn_Syntax.mk_Exp_match (e1, (mk_eqns eqns el)))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_let (((is_rec, lbs), _)), (_, _, tl, el, _)) -> begin
(match ((Support.Microsoft.FStar.Util.first_N (Support.List.length lbs) el)) with
| (el, e'::[]) -> begin
(let lbs' = (Support.List.map3 (fun _37671 t e -> (match (_37671) with
| (lbname, _, _) -> begin
(lbname, t, e)
end)) lbs tl el)
in (w (Microsoft_FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs'), e'))))
end
| _ -> begin
(failwith "impossible")
end)
end
| _ -> begin
(failwith "impossible")
end)
in (e', env)))))

let collect_from_typ = (fun f env t -> ((Support.Prims.snd) (reduce_typ (fun _37724 _37726 _37728 env _37731 k -> (k, env)) (fun _37706 vt _37709 env bvs t -> (let env = (f env t)
in (match ((compress_typ t).Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) -> begin
(t, env)
end
| _ -> begin
(vt env bvs t)
end))) (fun _37696 _37698 _37700 env _37703 e -> (e, env)) (fun k _37693 env -> (k, env)) (fun t _37689 env -> (t, env)) (fun e _37685 env -> (e, env)) env [] t)))




