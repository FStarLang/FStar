
let handle_err = (fun warning ret e -> (match (e) with
| Microsoft_FStar_Absyn_Syntax.Error ((msg, r)) -> begin
(let _68800 = (Support.Microsoft.FStar.Util.print_string (Support.Microsoft.FStar.Util.format3 "%s : %s\n%s\n" (Support.Microsoft.FStar.Range.string_of_range r) (if warning then begin
"Warning"
end else begin
"Error"
end) msg))
in ret)
end
| Support.Microsoft.FStar.Util.NYI (s) -> begin
(let _68804 = (Support.Microsoft.FStar.Util.print_string (Support.Microsoft.FStar.Util.format1 "Feature not yet implemented: %s" s))
in ret)
end
| Microsoft_FStar_Absyn_Syntax.Err (s) -> begin
(Support.Microsoft.FStar.Util.print_string (Support.Microsoft.FStar.Util.format1 "Error: %s" s))
end
| _ -> begin
(raise (e))
end))

let handleable = (fun _68768 -> (match (_68768) with
| (Microsoft_FStar_Absyn_Syntax.Error (_)) | (Support.Microsoft.FStar.Util.NYI (_)) | (Microsoft_FStar_Absyn_Syntax.Err (_)) -> begin
true
end
| _ -> begin
false
end))

let gensym = (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun _68823 -> (match (_68823) with
| () -> begin
(Support.String.strcat "_" (Support.Microsoft.FStar.Util.string_of_int (let _68824 = (Support.Microsoft.FStar.Util.incr ctr)
in (! (ctr)))))
end)))

let rec gensyms = (fun x -> (match (x) with
| 0 -> begin
[]
end
| n -> begin
((gensym ()))::(gensyms (n - 1))
end))

let genident = (fun r -> (let sym = (gensym ())
in (match (r) with
| None -> begin
(Microsoft_FStar_Absyn_Syntax.mk_ident (sym, Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| Some (r) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_ident (sym, r))
end)))

let bvd_eq = (fun bvd1 bvd2 -> (bvd1.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText = bvd2.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText))

let range_of_bvd = (fun x -> x.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idRange)

let mkbvd = (fun _68839 -> (match (_68839) with
| (x, y) -> begin
{Microsoft_FStar_Absyn_Syntax.ppname = x; Microsoft_FStar_Absyn_Syntax.realname = y}
end))

let setsort = (fun w t -> {Microsoft_FStar_Absyn_Syntax.v = w.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = w.Microsoft_FStar_Absyn_Syntax.p})

let withinfo = (fun e s r -> {Microsoft_FStar_Absyn_Syntax.v = e; Microsoft_FStar_Absyn_Syntax.sort = s; Microsoft_FStar_Absyn_Syntax.p = r})

let withsort = (fun e s -> (withinfo e s Microsoft_FStar_Absyn_Syntax.dummyRange))

let bvar_ppname = (fun bv -> bv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)

let bvar_realname = (fun bv -> bv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname)

let bvar_eq = (fun bv1 bv2 -> (bvd_eq bv1.Microsoft_FStar_Absyn_Syntax.v bv2.Microsoft_FStar_Absyn_Syntax.v))

let lbname_eq = (fun l1 l2 -> (match ((l1, l2)) with
| (Support.Microsoft.FStar.Util.Inl (x), Support.Microsoft.FStar.Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (Support.Microsoft.FStar.Util.Inr (l), Support.Microsoft.FStar.Util.Inr (m)) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l m)
end
| _ -> begin
false
end))

let fvar_eq = (fun fv1 fv2 -> (Microsoft_FStar_Absyn_Syntax.lid_equals fv1.Microsoft_FStar_Absyn_Syntax.v fv2.Microsoft_FStar_Absyn_Syntax.v))

let bvd_to_bvar_s = (fun bvd sort -> {Microsoft_FStar_Absyn_Syntax.v = bvd; Microsoft_FStar_Absyn_Syntax.sort = sort; Microsoft_FStar_Absyn_Syntax.p = bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idRange})

let bvar_to_bvd = (fun bv -> bv.Microsoft_FStar_Absyn_Syntax.v)

let btvar_to_typ = (fun bv -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar bv None bv.Microsoft_FStar_Absyn_Syntax.p))

let bvd_to_typ = (fun bvd k -> (btvar_to_typ (bvd_to_bvar_s bvd k)))

let bvar_to_exp = (fun bv -> (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar bv None bv.Microsoft_FStar_Absyn_Syntax.p))

let bvd_to_exp = (fun bvd t -> (bvar_to_exp (bvd_to_bvar_s bvd t)))

let new_bvd = (fun ropt -> (let f = (fun ropt -> (let id = (genident ropt)
in (mkbvd (id, id))))
in (f ropt)))

let freshen_bvd = (fun bvd' -> (mkbvd (bvd'.Microsoft_FStar_Absyn_Syntax.ppname, (genident (Some ((range_of_bvd bvd')))))))

let freshen_bvar = (fun b -> (bvd_to_bvar_s (freshen_bvd b.Microsoft_FStar_Absyn_Syntax.v) b.Microsoft_FStar_Absyn_Syntax.sort))

let gen_bvar = (fun sort -> (let bvd = (new_bvd None)
in (bvd_to_bvar_s bvd sort)))

let gen_bvar_p = (fun r sort -> (let bvd = (new_bvd (Some (r)))
in (bvd_to_bvar_s bvd sort)))

let bvdef_of_str = (fun s -> (let f = (fun s -> (let id = (Microsoft_FStar_Absyn_Syntax.id_of_text s)
in (mkbvd (id, id))))
in (f s)))

let set_bvd_range = (fun bvd r -> {Microsoft_FStar_Absyn_Syntax.ppname = (Microsoft_FStar_Absyn_Syntax.mk_ident (bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText, r)); Microsoft_FStar_Absyn_Syntax.realname = (Microsoft_FStar_Absyn_Syntax.mk_ident (bvd.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText, r))})

let set_lid_range = (fun l r -> (let ids = ((Support.List.map (fun i -> (Microsoft_FStar_Absyn_Syntax.mk_ident (i.Microsoft_FStar_Absyn_Syntax.idText, r)))) (Support.List.append l.Microsoft_FStar_Absyn_Syntax.ns ((l.Microsoft_FStar_Absyn_Syntax.ident)::[])))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids ids)))

let fv = (fun l -> (withinfo l Microsoft_FStar_Absyn_Syntax.tun (Microsoft_FStar_Absyn_Syntax.range_of_lid l)))

let fvar = (fun dc l r -> (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar ((fv (set_lid_range l r)), dc) None r))

let ftv = (fun l k -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (withinfo l k (Microsoft_FStar_Absyn_Syntax.range_of_lid l)) None (Microsoft_FStar_Absyn_Syntax.range_of_lid l)))

let order_bvd = (fun x y -> (match ((x, y)) with
| (Support.Microsoft.FStar.Util.Inl (_), Support.Microsoft.FStar.Util.Inr (_)) -> begin
(- (1))
end
| (Support.Microsoft.FStar.Util.Inr (_), Support.Microsoft.FStar.Util.Inl (_)) -> begin
1
end
| (Support.Microsoft.FStar.Util.Inl (x), Support.Microsoft.FStar.Util.Inl (y)) -> begin
(Support.String.compare x.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText y.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Support.String.compare x.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText y.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText)
end))

let arg_of_non_null_binder = (fun _68935 -> (match (_68935) with
| (b, imp) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(Support.Microsoft.FStar.Util.Inl ((btvar_to_typ a)), imp)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(Support.Microsoft.FStar.Util.Inr ((bvar_to_exp x)), imp)
end)
end))

let args_of_non_null_binders = (fun binders -> ((Support.List.collect (fun b -> if (Microsoft_FStar_Absyn_Syntax.is_null_binder b) then begin
[]
end else begin
((arg_of_non_null_binder b))::[]
end)) binders))

let args_of_binders = (fun binders -> ((Support.List.unzip) ((Support.List.map (fun b -> if (Microsoft_FStar_Absyn_Syntax.is_null_binder b) then begin
(let b = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(Support.Microsoft.FStar.Util.Inl ((gen_bvar a.Microsoft_FStar_Absyn_Syntax.sort)), (Support.Prims.snd b))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(Support.Microsoft.FStar.Util.Inr ((gen_bvar x.Microsoft_FStar_Absyn_Syntax.sort)), (Support.Prims.snd b))
end)
in (b, (arg_of_non_null_binder b)))
end else begin
(b, (arg_of_non_null_binder b))
end)) binders)))

let name_binders = (fun binders -> ((Support.List.mapi (fun i b -> if (Microsoft_FStar_Absyn_Syntax.is_null_binder b) then begin
(match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let b = (Microsoft_FStar_Absyn_Syntax.id_of_text (Support.String.strcat "_" (Support.Microsoft.FStar.Util.string_of_int i)))
in (let b = (bvd_to_bvar_s (mkbvd (b, b)) a.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.Inl (b), imp)))
end
| (Support.Microsoft.FStar.Util.Inr (y), imp) -> begin
(let x = (Microsoft_FStar_Absyn_Syntax.id_of_text (Support.String.strcat "_" (Support.Microsoft.FStar.Util.string_of_int i)))
in (let x = (bvd_to_bvar_s (mkbvd (x, x)) y.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.Inr (x), imp)))
end)
end else begin
b
end)) binders))

let name_function_binders = (fun t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, comp)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun ((name_binders binders), comp) None t.Microsoft_FStar_Absyn_Syntax.pos)
end
| _ -> begin
t
end))

let null_binders_of_tks = (fun tks -> ((Support.List.map (fun _68769 -> (match (_68769) with
| (Support.Microsoft.FStar.Util.Inl (k), imp) -> begin
(((Support.Prims.fst) (Microsoft_FStar_Absyn_Syntax.null_t_binder k)), imp)
end
| (Support.Microsoft.FStar.Util.Inr (t), imp) -> begin
(((Support.Prims.fst) (Microsoft_FStar_Absyn_Syntax.null_v_binder t)), imp)
end))) tks))

let binders_of_tks = (fun tks -> ((Support.List.map (fun _68770 -> (match (_68770) with
| (Support.Microsoft.FStar.Util.Inl (k), imp) -> begin
(Support.Microsoft.FStar.Util.Inl ((gen_bvar_p k.Microsoft_FStar_Absyn_Syntax.pos k)), imp)
end
| (Support.Microsoft.FStar.Util.Inr (t), imp) -> begin
(Support.Microsoft.FStar.Util.Inr ((gen_bvar_p t.Microsoft_FStar_Absyn_Syntax.pos t)), imp)
end))) tks))

let binders_of_freevars = (fun fvs -> (Support.List.append ((Support.List.map Microsoft_FStar_Absyn_Syntax.t_binder) (Support.Microsoft.FStar.Util.set_elements fvs.Microsoft_FStar_Absyn_Syntax.ftvs)) ((Support.List.map Microsoft_FStar_Absyn_Syntax.v_binder) (Support.Microsoft.FStar.Util.set_elements fvs.Microsoft_FStar_Absyn_Syntax.fxvs))))

let subst_to_string = (fun s -> ((Support.String.concat ", ") ((Support.List.map (fun _68771 -> (match (_68771) with
| Support.Microsoft.FStar.Util.Inl ((b, _)) -> begin
b.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText
end
| Support.Microsoft.FStar.Util.Inr ((x, _)) -> begin
x.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText
end))) s)))

let subst_tvar = (fun s a -> (Support.Microsoft.FStar.Util.find_map s (fun _68772 -> (match (_68772) with
| Support.Microsoft.FStar.Util.Inl ((b, t)) when (bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _ -> begin
None
end))))

let subst_xvar = (fun s a -> (Support.Microsoft.FStar.Util.find_map s (fun _68773 -> (match (_68773) with
| Support.Microsoft.FStar.Util.Inr ((b, t)) when (bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _ -> begin
None
end))))

let rec subst_typ' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
(Microsoft_FStar_Absyn_Visit.compress_typ t)
end
| _ -> begin
(let t0 = (Microsoft_FStar_Absyn_Visit.compress_typ t)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((Support.Microsoft.FStar.Util.Inl ((t', s')), m)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_delayed (t', (compose_subst s' s), (Support.Microsoft.FStar.Util.mk_ref None)) None t.Microsoft_FStar_Absyn_Syntax.pos)
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((Support.Microsoft.FStar.Util.Inr (mk_t), m)) -> begin
(let t = (mk_t ())
in (let _69043 = (m := Some (t))
in (subst_typ' s t)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let rec aux = (fun s' -> (match (s') with
| s0::rest -> begin
(match ((subst_tvar s0 a)) with
| Some (t) -> begin
(subst_typ' rest t)
end
| _ -> begin
(aux rest)
end)
end
| _ -> begin
t0
end))
in (aux s))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
t0
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_delayed (t0, s, (Support.Microsoft.FStar.Util.mk_ref None)) None t.Microsoft_FStar_Absyn_Syntax.pos)
end))
end))
and subst_exp' = (fun s e -> (match (s) with
| ([]) | ([]::[]) -> begin
(Microsoft_FStar_Absyn_Visit.compress_exp e)
end
| _ -> begin
(let e0 = (Microsoft_FStar_Absyn_Visit.compress_exp e)
in (match (e0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed ((e, s', m)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_delayed (e, (compose_subst s' s), (Support.Microsoft.FStar.Util.mk_ref None)) None e.Microsoft_FStar_Absyn_Syntax.pos)
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let rec aux = (fun s -> (match (s) with
| s0::rest -> begin
(match ((subst_xvar s0 x)) with
| Some (e) -> begin
(subst_exp' rest e)
end
| _ -> begin
(aux rest)
end)
end
| _ -> begin
e0
end))
in (aux s))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
e0
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_delayed (e0, s, (Support.Microsoft.FStar.Util.mk_ref None)) None e0.Microsoft_FStar_Absyn_Syntax.pos)
end))
end))
and subst_kind' = (fun s k -> (match (s) with
| ([]) | ([]::[]) -> begin
(Microsoft_FStar_Absyn_Visit.compress_kind k)
end
| _ -> begin
(let k0 = (Microsoft_FStar_Absyn_Visit.compress_kind k)
in (match (k0.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) | (Microsoft_FStar_Absyn_Syntax.Kind_unknown) -> begin
k0
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed ((k, s', m)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_delayed (k, (compose_subst s' s), (Support.Microsoft.FStar.Util.mk_ref None)) k0.Microsoft_FStar_Absyn_Syntax.pos)
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_delayed (k0, s, (Support.Microsoft.FStar.Util.mk_ref None)) k0.Microsoft_FStar_Absyn_Syntax.pos)
end))
end))
and subst_flags' = (fun s flags -> ((Support.List.map (fun _68774 -> (match (_68774) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (a) -> begin
Microsoft_FStar_Absyn_Syntax.DECREASES ((subst_exp' s a))
end
| f -> begin
f
end))) flags))
and subst_comp_typ' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _ -> begin
(let _69132 = t
in {Microsoft_FStar_Absyn_Syntax.effect_name = _69132.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = (subst_typ' s t.Microsoft_FStar_Absyn_Syntax.result_typ); Microsoft_FStar_Absyn_Syntax.effect_args = (Support.List.map (fun _68775 -> (match (_68775) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(Support.Microsoft.FStar.Util.Inl ((subst_typ' s t)), imp)
end
| (Support.Microsoft.FStar.Util.Inr (e), imp) -> begin
(Support.Microsoft.FStar.Util.Inr ((subst_exp' s e)), imp)
end)) t.Microsoft_FStar_Absyn_Syntax.effect_args); Microsoft_FStar_Absyn_Syntax.flags = (subst_flags' s t.Microsoft_FStar_Absyn_Syntax.flags)})
end))
and subst_comp' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _ -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total (subst_typ' s t))
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Comp (subst_comp_typ' s ct))
end)
end))
and compose_subst = (fun s1 s2 -> (Support.List.append s1 s2))

let mk_subst = (fun s -> (s)::[])

let subst_kind = (fun s t -> (subst_kind' (mk_subst s) t))

let subst_typ = (fun s t -> (subst_typ' (mk_subst s) t))

let subst_exp = (fun s t -> (subst_exp' (mk_subst s) t))

let subst_flags = (fun s t -> (subst_flags' (mk_subst s) t))

let subst_comp = (fun s t -> (subst_comp' (mk_subst s) t))

let subst_binder = (fun s _68776 -> (match (_68776) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(Support.Microsoft.FStar.Util.Inl ((let _69173 = a
in {Microsoft_FStar_Absyn_Syntax.v = _69173.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = (subst_kind s a.Microsoft_FStar_Absyn_Syntax.sort); Microsoft_FStar_Absyn_Syntax.p = _69173.Microsoft_FStar_Absyn_Syntax.p})), imp)
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(Support.Microsoft.FStar.Util.Inr ((let _69179 = x
in {Microsoft_FStar_Absyn_Syntax.v = _69179.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = (subst_typ s x.Microsoft_FStar_Absyn_Syntax.sort); Microsoft_FStar_Absyn_Syntax.p = _69179.Microsoft_FStar_Absyn_Syntax.p})), imp)
end))

let subst_arg = (fun s _68777 -> (match (_68777) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(Support.Microsoft.FStar.Util.Inl ((subst_typ s t)), imp)
end
| (Support.Microsoft.FStar.Util.Inr (e), imp) -> begin
(Support.Microsoft.FStar.Util.Inr ((subst_exp s e)), imp)
end))

let subst_binders = (fun s bs -> (match (s) with
| [] -> begin
bs
end
| _ -> begin
(Support.List.map (subst_binder s) bs)
end))

let subst_args = (fun s args -> (match (s) with
| [] -> begin
args
end
| _ -> begin
(Support.List.map (subst_arg s) args)
end))

let subst_formal = (fun f a -> (match ((f, a)) with
| ((Support.Microsoft.FStar.Util.Inl (a), _), (Support.Microsoft.FStar.Util.Inl (t), _)) -> begin
Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t))
end
| ((Support.Microsoft.FStar.Util.Inr (x), _), (Support.Microsoft.FStar.Util.Inr (v), _)) -> begin
Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, v))
end
| _ -> begin
(failwith "Ill-formed substitution")
end))

let mk_subst_one_binder = (fun b1 b2 -> if ((Microsoft_FStar_Absyn_Syntax.is_null_binder b1) || (Microsoft_FStar_Absyn_Syntax.is_null_binder b2)) then begin
[]
end else begin
(match (((Support.Prims.fst b1), (Support.Prims.fst b2))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
if (bvar_eq a b) then begin
[]
end else begin
(Support.Microsoft.FStar.Util.Inl ((b.Microsoft_FStar_Absyn_Syntax.v, (btvar_to_typ a))))::[]
end
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
if (bvar_eq x y) then begin
[]
end else begin
(Support.Microsoft.FStar.Util.Inr ((y.Microsoft_FStar_Absyn_Syntax.v, (bvar_to_exp x))))::[]
end
end
| _ -> begin
[]
end)
end)

let mk_subst_binder = (fun bs1 bs2 -> (let rec aux = (fun out bs1 bs2 -> (match ((bs1, bs2)) with
| ([], []) -> begin
Some (out)
end
| (b1::bs1, b2::bs2) -> begin
(aux (Support.List.append (mk_subst_one_binder b1 b2) out) bs1 bs2)
end
| _ -> begin
None
end))
in (aux [] bs1 bs2)))

let subst_of_list = (fun formals actuals -> if ((Support.List.length formals) = (Support.List.length actuals)) then begin
(Support.List.map2 subst_formal formals actuals)
end else begin
(failwith "Ill-formed substitution")
end)

type red_ctrl =
{stop_if_empty_subst : bool; descend : bool}

let alpha_ctrl = {stop_if_empty_subst = false; descend = true}

let subst_ctrl = {stop_if_empty_subst = true; descend = true}

let null_ctrl = {stop_if_empty_subst = true; descend = false}

let extend_subst = (fun e s -> (Support.List.append (((mk_subst e))::[]) s))

let map_knd = (fun s vk mt me descend binders k -> ((subst_kind' s k), descend))

let map_typ = (fun s mk vt me descend binders t -> ((subst_typ' s t), descend))

let map_exp = (fun s mk me ve descend binders e -> ((subst_exp' s e), descend))

let map_flags = (fun s map_exp descend binders flags -> ((Support.List.map (fun _68778 -> (match (_68778) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
Microsoft_FStar_Absyn_Syntax.DECREASES (((Support.Prims.fst) (map_exp descend binders e)))
end
| f -> begin
f
end))) flags))

let map_comp = (fun s mk map_typ map_exp descend binders c -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _69307 = (map_typ descend binders t)
in (match (_69307) with
| (t, descend) -> begin
((Microsoft_FStar_Absyn_Syntax.mk_Total t), descend)
end))
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _69312 = (map_typ descend binders ct.Microsoft_FStar_Absyn_Syntax.result_typ)
in (match (_69312) with
| (t, descend) -> begin
(let _69315 = (Microsoft_FStar_Absyn_Visit.map_args map_typ map_exp descend binders ct.Microsoft_FStar_Absyn_Syntax.effect_args)
in (match (_69315) with
| (args, descend) -> begin
((Microsoft_FStar_Absyn_Syntax.mk_Comp (let _69316 = ct
in {Microsoft_FStar_Absyn_Syntax.effect_name = _69316.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = args; Microsoft_FStar_Absyn_Syntax.flags = (map_flags s map_exp descend binders ct.Microsoft_FStar_Absyn_Syntax.flags)})), descend)
end))
end))
end))

let visit_knd = (fun s vk mt me ctrl binders k -> (let k = (Microsoft_FStar_Absyn_Visit.compress_kind k)
in if ctrl.descend then begin
(let _69329 = (vk null_ctrl binders k)
in (match (_69329) with
| (k, _) -> begin
(k, ctrl)
end))
end else begin
(map_knd s vk mt me null_ctrl binders k)
end))

let rec compress_kind = (fun k -> (let k = (Microsoft_FStar_Absyn_Visit.compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_delayed ((k', s, m)) -> begin
(let k' = ((Support.Prims.fst) (Microsoft_FStar_Absyn_Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) (Microsoft_FStar_Absyn_Visit.combine_kind) (Microsoft_FStar_Absyn_Visit.combine_typ) (Microsoft_FStar_Absyn_Visit.combine_exp) subst_ctrl [] k'))
in (let k' = (compress_kind k')
in (let _69339 = (m := Some (k'))
in k')))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, actuals)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (k) -> begin
(match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam ((formals, k')) -> begin
(compress_kind (subst_kind (subst_of_list formals actuals) k'))
end
| _ -> begin
if ((Support.List.length actuals) = 0) then begin
k
end else begin
(failwith "Wrong arity for kind unifier")
end
end)
end
| _ -> begin
k
end)
end
| _ -> begin
k
end)))

let rec visit_typ = (fun s mk vt me ctrl boundvars t -> (let visit_prod = (fun bs tc -> (let _69417 = ((Support.List.fold_left (fun _69370 b -> (match (_69370) with
| (bs, boundvars, s) -> begin
(match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _69379 = (map_knd s mk vt me null_ctrl boundvars a.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_69379) with
| (k, _) -> begin
(let a = (let _69380 = a
in {Microsoft_FStar_Absyn_Syntax.v = _69380.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _69380.Microsoft_FStar_Absyn_Syntax.p})
in if (Microsoft_FStar_Absyn_Syntax.is_null_binder b) then begin
(((Support.Microsoft.FStar.Util.Inl (a), imp))::bs, boundvars, s)
end else begin
(let boundvars' = (Support.Microsoft.FStar.Util.Inl (a.Microsoft_FStar_Absyn_Syntax.v))::boundvars
in (let _69392 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(Support.Microsoft.FStar.Util.Inl (a), s, boundvars')
end
| _ -> begin
(let b = (bvd_to_bvar_s (freshen_bvd a.Microsoft_FStar_Absyn_Syntax.v) k)
in (let s = (extend_subst (Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, (btvar_to_typ b)))) s)
in (Support.Microsoft.FStar.Util.Inl (b), s, (Support.Microsoft.FStar.Util.Inl (b.Microsoft_FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_69392) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end)
end))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _69400 = (map_typ s mk vt me null_ctrl boundvars x.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_69400) with
| (t, _) -> begin
(let x = (let _69401 = x
in {Microsoft_FStar_Absyn_Syntax.v = _69401.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _69401.Microsoft_FStar_Absyn_Syntax.p})
in if (Microsoft_FStar_Absyn_Syntax.is_null_binder b) then begin
(((Support.Microsoft.FStar.Util.Inr (x), imp))::bs, boundvars, s)
end else begin
(let boundvars' = (Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.v))::boundvars
in (let _69413 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(Support.Microsoft.FStar.Util.Inr (x), s, boundvars')
end
| _ -> begin
(let y = (bvd_to_bvar_s (freshen_bvd x.Microsoft_FStar_Absyn_Syntax.v) t)
in (let s = (extend_subst (Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, (bvar_to_exp y)))) s)
in (Support.Microsoft.FStar.Util.Inr (y), s, (Support.Microsoft.FStar.Util.Inr (y.Microsoft_FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_69413) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end)
end))
end)
end)) ([], boundvars, s)) bs)
in (match (_69417) with
| (bs, boundvars, s) -> begin
(let tc = (match ((s, tc)) with
| ([], _) -> begin
tc
end
| (_, Support.Microsoft.FStar.Util.Inl (t)) -> begin
Support.Microsoft.FStar.Util.Inl (((Support.Prims.fst) (map_typ s mk vt me null_ctrl boundvars t)))
end
| (_, Support.Microsoft.FStar.Util.Inr (c)) -> begin
Support.Microsoft.FStar.Util.Inr (((Support.Prims.fst) (map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl boundvars c)))
end)
in ((Support.List.rev bs), tc))
end)))
in (let t0 = t
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (_) -> begin
((compress_typ (subst_typ' s t0)), ctrl)
end
| _ when (not (ctrl.descend)) -> begin
(map_typ s mk vt me null_ctrl boundvars t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(match ((visit_prod bs (Support.Microsoft.FStar.Util.Inr (c)))) with
| (bs, Support.Microsoft.FStar.Util.Inr (c)) -> begin
((Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t0.Microsoft_FStar_Absyn_Syntax.pos), ctrl)
end
| _ -> begin
(failwith "Impossible")
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, t)) -> begin
(match ((visit_prod (((Support.Microsoft.FStar.Util.Inr (x), None))::[]) (Support.Microsoft.FStar.Util.Inl (t)))) with
| ((Support.Microsoft.FStar.Util.Inr (x), _)::[], Support.Microsoft.FStar.Util.Inl (t)) -> begin
((Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, t) None t0.Microsoft_FStar_Absyn_Syntax.pos), ctrl)
end
| _ -> begin
(failwith "Impossible")
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(match ((visit_prod bs (Support.Microsoft.FStar.Util.Inl (t)))) with
| (bs, Support.Microsoft.FStar.Util.Inl (t)) -> begin
((Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t0.Microsoft_FStar_Absyn_Syntax.pos), ctrl)
end
| _ -> begin
(failwith "Impossible")
end)
end
| _ -> begin
(let _69479 = (vt null_ctrl boundvars t)
in (match (_69479) with
| (t, _) -> begin
(t, ctrl)
end))
end))))
and compress_typ' = (fun t -> (let t = (Microsoft_FStar_Absyn_Visit.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((Support.Microsoft.FStar.Util.Inl ((t', s)), m)) -> begin
(let res = ((Support.Prims.fst) (Microsoft_FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) (Microsoft_FStar_Absyn_Visit.combine_kind) (Microsoft_FStar_Absyn_Visit.combine_typ) (Microsoft_FStar_Absyn_Visit.combine_exp) subst_ctrl [] t'))
in (let res = (compress_typ' res)
in (let _69491 = (m := Some (res))
in res)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((Support.Microsoft.FStar.Util.Inr (mk_t), m)) -> begin
(let t = (compress_typ' (mk_t ()))
in (let _69499 = (m := Some (t))
in t))
end
| _ -> begin
t
end)))
and compress_typ = (fun t -> (let t = (compress_typ' t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_) -> begin
(failwith "Impossible: compress returned a delayed type")
end
| _ -> begin
t
end)))

let rec visit_exp = (fun s mk me ve ctrl binders e -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (_) -> begin
((compress_exp (subst_exp' s e)), ctrl)
end
| _ when (not (ctrl.descend)) -> begin
(map_exp s mk me ve ctrl binders e)
end
| _ -> begin
(let _69528 = (ve null_ctrl binders e)
in (match (_69528) with
| (e, _) -> begin
(e, ctrl)
end))
end)))
and compress_exp = (fun e -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed ((e', s, m)) -> begin
(let e = ((Support.Prims.fst) (Microsoft_FStar_Absyn_Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) (Microsoft_FStar_Absyn_Visit.combine_kind) (Microsoft_FStar_Absyn_Visit.combine_typ) (Microsoft_FStar_Absyn_Visit.combine_exp) subst_ctrl [] e'))
in (let res = (compress_exp e)
in (let _69538 = (m := Some (res))
in res)))
end
| _ -> begin
e
end)))

let rec unmeta_exp = (fun e -> (let e = (compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(unmeta_exp e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _)) -> begin
(unmeta_exp e)
end
| _ -> begin
e
end)))

let alpha_typ = (fun t -> (let t = (compress_typ t)
in (let s = (mk_subst [])
in (let doit = (fun t -> ((Support.Prims.fst) (Microsoft_FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) (Microsoft_FStar_Absyn_Visit.combine_kind) (Microsoft_FStar_Absyn_Visit.combine_typ) (Microsoft_FStar_Absyn_Visit.combine_exp) alpha_ctrl [] t)))
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, _))) -> begin
if (Support.Microsoft.FStar.Util.for_all Microsoft_FStar_Absyn_Syntax.is_null_binder bs) then begin
t
end else begin
(doit t)
end
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_) -> begin
(doit t)
end
| _ -> begin
t
end)))))

let formals_for_actuals = (fun formals actuals -> (Support.List.map2 (fun formal actual -> (match (((Support.Prims.fst formal), (Support.Prims.fst actual))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, b))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, y))
end
| _ -> begin
(failwith "Ill-typed substitution")
end)) formals actuals))

let compress_typ_opt = (fun _68779 -> (match (_68779) with
| None -> begin
None
end
| Some (t) -> begin
Some ((compress_typ t))
end))

let mk_discriminator = (fun lid -> (Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append lid.Microsoft_FStar_Absyn_Syntax.ns (((Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.String.strcat "is_" lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText), lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idRange)))::[]))))

let is_name = (fun lid -> (let c = (Support.Microsoft.FStar.Util.char_at lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText 0)
in (Support.Microsoft.FStar.Util.is_upper c)))

let ml_comp = (fun t r -> (Microsoft_FStar_Absyn_Syntax.mk_Comp {Microsoft_FStar_Absyn_Syntax.effect_name = (set_lid_range Microsoft_FStar_Absyn_Const.ml_effect_lid r); Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = []; Microsoft_FStar_Absyn_Syntax.flags = (Microsoft_FStar_Absyn_Syntax.MLEFFECT)::[]}))

let total_comp = (fun t r -> (Microsoft_FStar_Absyn_Syntax.mk_Total t))

let gtotal_comp = (fun t -> (Microsoft_FStar_Absyn_Syntax.mk_Comp {Microsoft_FStar_Absyn_Syntax.effect_name = Microsoft_FStar_Absyn_Const.effect_GTot_lid; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = []; Microsoft_FStar_Absyn_Syntax.flags = (Microsoft_FStar_Absyn_Syntax.SOMETRIVIAL)::[]}))

let comp_set_flags = (fun c f -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_) -> begin
c
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _69611 = c
in {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp ((let _69613 = ct
in {Microsoft_FStar_Absyn_Syntax.effect_name = _69613.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _69613.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _69613.Microsoft_FStar_Absyn_Syntax.effect_args; Microsoft_FStar_Absyn_Syntax.flags = f})); Microsoft_FStar_Absyn_Syntax.tk = _69611.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = _69611.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _69611.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _69611.Microsoft_FStar_Absyn_Syntax.uvs})
end))

let comp_flags = (fun c -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_) -> begin
(Microsoft_FStar_Absyn_Syntax.TOTAL)::[]
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
ct.Microsoft_FStar_Absyn_Syntax.flags
end))

let comp_effect_name = (fun c -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
c.Microsoft_FStar_Absyn_Syntax.effect_name
end
| Microsoft_FStar_Absyn_Syntax.Total (_) -> begin
Microsoft_FStar_Absyn_Const.tot_effect_lid
end))

let comp_to_comp_typ = (fun c -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
c
end
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
{Microsoft_FStar_Absyn_Syntax.effect_name = Microsoft_FStar_Absyn_Const.tot_effect_lid; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = []; Microsoft_FStar_Absyn_Syntax.flags = (Microsoft_FStar_Absyn_Syntax.TOTAL)::[]}
end))

let is_total_comp = (fun c -> ((Support.Microsoft.FStar.Util.for_some (fun _68780 -> (match (_68780) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _ -> begin
false
end))) (comp_flags c)))

let is_total_lcomp = (fun c -> ((Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.tot_effect_lid) || ((Support.Microsoft.FStar.Util.for_some (fun _68781 -> (match (_68781) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _ -> begin
false
end))) c.Microsoft_FStar_Absyn_Syntax.cflags)))

let is_partial_return = (fun c -> ((Support.Microsoft.FStar.Util.for_some (fun _68782 -> (match (_68782) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _ -> begin
false
end))) (comp_flags c)))

let is_lcomp_partial_return = (fun c -> ((Support.Microsoft.FStar.Util.for_some (fun _68783 -> (match (_68783) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _ -> begin
false
end))) c.Microsoft_FStar_Absyn_Syntax.cflags))

let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.effect_GTot_lid (comp_effect_name c))))

let is_pure_comp = (fun c -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
((((is_tot_or_gtot_comp c) || (Support.Microsoft.FStar.Util.starts_with ct.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str "Prims.PURE")) || (Support.Microsoft.FStar.Util.starts_with ct.Microsoft_FStar_Absyn_Syntax.effect_name.Microsoft_FStar_Absyn_Syntax.str "Prims.Pure")) || ((Support.Microsoft.FStar.Util.for_some (fun _68784 -> (match (_68784) with
| Microsoft_FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _ -> begin
false
end))) ct.Microsoft_FStar_Absyn_Syntax.flags))
end))

let is_ghost_effect = (fun l -> (((Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.effect_GTot_lid l) || (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.effect_GHOST_lid l)) || (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.effect_Ghost_lid l)))

let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))

let is_pure_lcomp = (fun lc -> ((((is_total_lcomp lc) || (Support.Microsoft.FStar.Util.starts_with lc.Microsoft_FStar_Absyn_Syntax.eff_name.Microsoft_FStar_Absyn_Syntax.str "Prims.Pure")) || (Support.Microsoft.FStar.Util.starts_with lc.Microsoft_FStar_Absyn_Syntax.eff_name.Microsoft_FStar_Absyn_Syntax.str "Prims.PURE")) || ((Support.Microsoft.FStar.Util.for_some (fun _68785 -> (match (_68785) with
| Microsoft_FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _ -> begin
false
end))) lc.Microsoft_FStar_Absyn_Syntax.cflags)))

let is_pure_or_ghost_lcomp = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.Microsoft_FStar_Absyn_Syntax.eff_name)))

let is_pure_or_ghost_function = (fun t -> (match ((compress_typ t).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((_, c)) -> begin
(is_pure_or_ghost_comp c)
end
| _ -> begin
true
end))

let is_lemma = (fun t -> (match ((compress_typ t).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((_, c)) -> begin
(match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.lemma_lid)
end
| _ -> begin
false
end)
end
| _ -> begin
false
end))

let is_smt_lemma = (fun t -> (match ((compress_typ t).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((_, c)) -> begin
(match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (ct) when (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.lemma_lid) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| _req::_ens::(Support.Microsoft.FStar.Util.Inr (pats), _)::_ -> begin
(match ((unmeta_exp pats).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.cons_lid)
end
| _ -> begin
false
end)
end
| _ -> begin
false
end)
end
| _ -> begin
false
end)
end
| _ -> begin
false
end))

let is_ml_comp = (fun c -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
((Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.ml_effect_lid) || ((Support.Microsoft.FStar.Util.for_some (fun _68786 -> (match (_68786) with
| Microsoft_FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _ -> begin
false
end))) c.Microsoft_FStar_Absyn_Syntax.flags))
end
| _ -> begin
false
end))

let comp_result = (fun c -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
ct.Microsoft_FStar_Absyn_Syntax.result_typ
end))

let set_result_typ = (fun c t -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total t)
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Comp (let _69762 = ct
in {Microsoft_FStar_Absyn_Syntax.effect_name = _69762.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = _69762.Microsoft_FStar_Absyn_Syntax.effect_args; Microsoft_FStar_Absyn_Syntax.flags = _69762.Microsoft_FStar_Absyn_Syntax.flags}))
end))

let is_trivial_wp = (fun c -> ((Support.Microsoft.FStar.Util.for_some (fun _68787 -> (match (_68787) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _ -> begin
false
end))) (comp_flags c)))

let rec is_atom = (fun e -> (match ((compress_exp e).Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(is_atom e)
end
| _ -> begin
false
end))

let primops = (Microsoft_FStar_Absyn_Const.op_Eq)::(Microsoft_FStar_Absyn_Const.op_notEq)::(Microsoft_FStar_Absyn_Const.op_LT)::(Microsoft_FStar_Absyn_Const.op_LTE)::(Microsoft_FStar_Absyn_Const.op_GT)::(Microsoft_FStar_Absyn_Const.op_GTE)::(Microsoft_FStar_Absyn_Const.op_Subtraction)::(Microsoft_FStar_Absyn_Const.op_Minus)::(Microsoft_FStar_Absyn_Const.op_Addition)::(Microsoft_FStar_Absyn_Const.op_Multiply)::(Microsoft_FStar_Absyn_Const.op_Division)::(Microsoft_FStar_Absyn_Const.op_Modulus)::(Microsoft_FStar_Absyn_Const.op_And)::(Microsoft_FStar_Absyn_Const.op_Or)::(Microsoft_FStar_Absyn_Const.op_Negation)::[]

let is_primop = (fun f -> (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)) -> begin
((Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v)) primops)
end
| _ -> begin
false
end))

let rec ascribe = (fun e t -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _)) -> begin
(ascribe e t)
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_ascribed (e, t) e.Microsoft_FStar_Absyn_Syntax.pos)
end))

let rec unascribe = (fun e -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _)) -> begin
(unascribe e)
end
| _ -> begin
e
end))

let rec ascribe_typ = (fun t k -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t', _)) -> begin
(ascribe_typ t' k)
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.Microsoft_FStar_Absyn_Syntax.pos)
end))

let rec unascribe_typ = (fun t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _)) -> begin
(unascribe_typ t)
end
| _ -> begin
t
end))

let rec unrefine = (fun t -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _)) -> begin
(unrefine x.Microsoft_FStar_Absyn_Syntax.sort)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _)) -> begin
(unrefine t)
end
| _ -> begin
t
end)))

let is_fun = (fun e -> (match ((compress_exp e).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_abs (_) -> begin
true
end
| _ -> begin
false
end))

let is_function_typ = (fun t -> (match ((compress_typ t).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_) -> begin
true
end
| _ -> begin
false
end))

let rec pre_typ = (fun t -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _)) -> begin
(pre_typ x.Microsoft_FStar_Absyn_Syntax.sort)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _)) -> begin
(pre_typ t)
end
| _ -> begin
t
end)))

let destruct = (fun typ lid -> (let typ = (compress_typ typ)
in (match (typ.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, args)) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v lid) -> begin
Some (args)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v lid) -> begin
Some ([])
end
| _ -> begin
None
end)))

let rec lids_of_sigelt = (fun se -> (match (se) with
| (Microsoft_FStar_Absyn_Syntax.Sig_let ((_, _, lids, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_bundle ((_, _, lids, _))) -> begin
lids
end
| (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, _, _, _, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, _, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, _, _, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, _, _, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((lid, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, _, _, _))) -> begin
(lid)::[]
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((n, _)) -> begin
(n.Microsoft_FStar_Absyn_Syntax.mname)::[]
end
| (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_main (_)) -> begin
[]
end))

let lid_of_sigelt = (fun se -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _ -> begin
None
end))

let range_of_sigelt = (fun x -> (match (x) with
| (Microsoft_FStar_Absyn_Syntax.Sig_bundle ((_, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_, _, _, _, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((_, _, _, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((_, _, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_, _, _, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_assume ((_, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_let ((_, r, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_main ((_, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_pragma ((_, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((_, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((_, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect ((_, r))) -> begin
r
end))

let range_of_lb = (fun _68788 -> (match (_68788) with
| (Support.Microsoft.FStar.Util.Inl (x), _, _) -> begin
(range_of_bvd x)
end
| (Support.Microsoft.FStar.Util.Inr (l), _, _) -> begin
(Microsoft_FStar_Absyn_Syntax.range_of_lid l)
end))

let range_of_arg = (fun _68789 -> (match (_68789) with
| (Support.Microsoft.FStar.Util.Inl (hd), _) -> begin
hd.Microsoft_FStar_Absyn_Syntax.pos
end
| (Support.Microsoft.FStar.Util.Inr (hd), _) -> begin
hd.Microsoft_FStar_Absyn_Syntax.pos
end))

let range_of_args = (fun args r -> ((Support.List.fold_left (fun r a -> (Support.Microsoft.FStar.Range.union_ranges r (range_of_arg a))) r) args))

let mk_typ_app = (fun f args -> (let r = (range_of_args args f.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (f, args) None r)))

let mk_exp_app = (fun f args -> (let r = (range_of_args args f.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (f, args) None r)))

let mk_data = (fun l args -> (match (args) with
| [] -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared (((fvar true l (Microsoft_FStar_Absyn_Syntax.range_of_lid l)), Microsoft_FStar_Absyn_Syntax.Data_app))))
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared (((mk_exp_app (fvar true l (Microsoft_FStar_Absyn_Syntax.range_of_lid l)) args), Microsoft_FStar_Absyn_Syntax.Data_app))))
end))

let mangle_field_name = (fun x -> (Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.String.strcat "^fname^" x.Microsoft_FStar_Absyn_Syntax.idText), x.Microsoft_FStar_Absyn_Syntax.idRange)))

let unmangle_field_name = (fun x -> if (Support.Microsoft.FStar.Util.starts_with x.Microsoft_FStar_Absyn_Syntax.idText "^fname^") then begin
(Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.Microsoft.FStar.Util.substring_from x.Microsoft_FStar_Absyn_Syntax.idText 7), x.Microsoft_FStar_Absyn_Syntax.idRange))
end else begin
x
end)

let mk_field_projector_name = (fun lid x i -> (let nm = if (Microsoft_FStar_Absyn_Syntax.is_null_bvar x) then begin
(Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.String.strcat "_" (Support.Microsoft.FStar.Util.string_of_int i)), x.Microsoft_FStar_Absyn_Syntax.p))
end else begin
x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname
end
in (let y = (let _70156 = x.Microsoft_FStar_Absyn_Syntax.v
in {Microsoft_FStar_Absyn_Syntax.ppname = nm; Microsoft_FStar_Absyn_Syntax.realname = _70156.Microsoft_FStar_Absyn_Syntax.realname})
in ((Microsoft_FStar_Absyn_Syntax.lid_of_ids (Support.List.append (Microsoft_FStar_Absyn_Syntax.ids_of_lid lid) (((unmangle_field_name nm))::[]))), y))))

let unchecked_unify = (fun uv t -> (match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (_) -> begin
(failwith (Support.Microsoft.FStar.Util.format1 "Changing a fixed uvar! U%s\n" (Support.Microsoft.FStar.Util.string_of_int (Support.Microsoft.FStar.Unionfind.uvar_id uv))))
end
| _ -> begin
(Support.Microsoft.FStar.Unionfind.change uv (Microsoft_FStar_Absyn_Syntax.Fixed (t)))
end))

type bvars =
(Microsoft_FStar_Absyn_Syntax.btvar Support.Microsoft.FStar.Util.set * Microsoft_FStar_Absyn_Syntax.bvvar Support.Microsoft.FStar.Util.set)

let no_bvars = (Microsoft_FStar_Absyn_Syntax.no_fvs.Microsoft_FStar_Absyn_Syntax.ftvs, Microsoft_FStar_Absyn_Syntax.no_fvs.Microsoft_FStar_Absyn_Syntax.fxvs)

let fvs_included = (fun fvs1 fvs2 -> ((Support.Microsoft.FStar.Util.set_is_subset_of fvs1.Microsoft_FStar_Absyn_Syntax.ftvs fvs2.Microsoft_FStar_Absyn_Syntax.ftvs) && (Support.Microsoft.FStar.Util.set_is_subset_of fvs1.Microsoft_FStar_Absyn_Syntax.fxvs fvs2.Microsoft_FStar_Absyn_Syntax.fxvs)))

let eq_fvars = (fun v1 v2 -> (match ((v1, v2)) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq a b)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| _ -> begin
false
end))

let eq_binder = (fun b1 b2 -> (match (((Support.Prims.fst b1), (Support.Prims.fst b2))) with
| (Support.Microsoft.FStar.Util.Inl (x), Support.Microsoft.FStar.Util.Inl (y)) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
false
end))

let uv_eq = (fun _70199 _70203 -> (match ((_70199, _70203)) with
| ((uv1, _), (uv2, _)) -> begin
(Support.Microsoft.FStar.Unionfind.equivalent uv1 uv2)
end))

let union_uvs = (fun uvs1 uvs2 -> {Microsoft_FStar_Absyn_Syntax.uvars_k = (Support.Microsoft.FStar.Util.set_union uvs1.Microsoft_FStar_Absyn_Syntax.uvars_k uvs2.Microsoft_FStar_Absyn_Syntax.uvars_k); Microsoft_FStar_Absyn_Syntax.uvars_t = (Support.Microsoft.FStar.Util.set_union uvs1.Microsoft_FStar_Absyn_Syntax.uvars_t uvs2.Microsoft_FStar_Absyn_Syntax.uvars_t); Microsoft_FStar_Absyn_Syntax.uvars_e = (Support.Microsoft.FStar.Util.set_union uvs1.Microsoft_FStar_Absyn_Syntax.uvars_e uvs2.Microsoft_FStar_Absyn_Syntax.uvars_e)})

let union_fvs = (fun fvs1 fvs2 -> {Microsoft_FStar_Absyn_Syntax.ftvs = (Support.Microsoft.FStar.Util.set_union fvs1.Microsoft_FStar_Absyn_Syntax.ftvs fvs2.Microsoft_FStar_Absyn_Syntax.ftvs); Microsoft_FStar_Absyn_Syntax.fxvs = (Support.Microsoft.FStar.Util.set_union fvs1.Microsoft_FStar_Absyn_Syntax.fxvs fvs2.Microsoft_FStar_Absyn_Syntax.fxvs)})

let union_fvs_uvs = (fun _70210 _70213 -> (match ((_70210, _70213)) with
| ((fvs1, uvs1), (fvs2, uvs2)) -> begin
((union_fvs fvs1 fvs2), (union_uvs uvs1 uvs2))
end))

let sub_fv = (fun _70216 _70219 -> (match ((_70216, _70219)) with
| ((fvs, uvs), (tvars, vvars)) -> begin
((let _70220 = fvs
in {Microsoft_FStar_Absyn_Syntax.ftvs = (Support.Microsoft.FStar.Util.set_difference fvs.Microsoft_FStar_Absyn_Syntax.ftvs tvars); Microsoft_FStar_Absyn_Syntax.fxvs = (Support.Microsoft.FStar.Util.set_difference fvs.Microsoft_FStar_Absyn_Syntax.fxvs vvars)}), uvs)
end))

let stash = (fun uvonly s _70228 -> (match (_70228) with
| (fvs, uvs) -> begin
(let _70229 = (s.Microsoft_FStar_Absyn_Syntax.uvs := Some (uvs))
in if uvonly then begin
()
end else begin
(s.Microsoft_FStar_Absyn_Syntax.fvs := Some (fvs))
end)
end))

let single_fv = (fun x -> (Support.Microsoft.FStar.Util.set_add x (Microsoft_FStar_Absyn_Syntax.new_ftv_set ())))

let single_uv = (fun u -> (Support.Microsoft.FStar.Util.set_add u (Microsoft_FStar_Absyn_Syntax.new_uv_set ())))

let single_uvt = (fun u -> (Support.Microsoft.FStar.Util.set_add u (Microsoft_FStar_Absyn_Syntax.new_uvt_set ())))

let rec vs_typ' = (fun t uvonly cont -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_) -> begin
(failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
if uvonly then begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end else begin
(cont ((let _70244 = Microsoft_FStar_Absyn_Syntax.no_fvs
in {Microsoft_FStar_Absyn_Syntax.ftvs = (single_fv a); Microsoft_FStar_Absyn_Syntax.fxvs = _70244.Microsoft_FStar_Absyn_Syntax.fxvs}), Microsoft_FStar_Absyn_Syntax.no_uvs))
end
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, (let _70250 = Microsoft_FStar_Absyn_Syntax.no_uvs
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _70250.Microsoft_FStar_Absyn_Syntax.uvars_k; Microsoft_FStar_Absyn_Syntax.uvars_t = (single_uvt (uv, k)); Microsoft_FStar_Absyn_Syntax.uvars_e = _70250.Microsoft_FStar_Absyn_Syntax.uvars_e})))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(vs_binders bs uvonly (fun _70262 -> (match (_70262) with
| (bvs, vs1) -> begin
(vs_comp c uvonly (fun vs2 -> (cont (sub_fv (union_fvs_uvs vs1 vs2) bvs))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(vs_binders bs uvonly (fun _70270 -> (match (_70270) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (cont (sub_fv (union_fvs_uvs vs1 vs2) bvs))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, t)) -> begin
(vs_binders (((Support.Microsoft.FStar.Util.Inr (x), None))::[]) uvonly (fun _70278 -> (match (_70278) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (cont (sub_fv (union_fvs_uvs vs1 vs2) bvs))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, args)) -> begin
(vs_typ t uvonly (fun vs1 -> (vs_args args uvonly (fun vs2 -> (cont (union_fvs_uvs vs1 vs2))))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _)) -> begin
(vs_typ t uvonly cont)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, _))) -> begin
(vs_typ t1 uvonly (fun vs1 -> (vs_typ t2 uvonly (fun vs2 -> (cont (union_fvs_uvs vs1 vs2))))))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, _, _, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, _)))) -> begin
(vs_typ t uvonly cont)
end)))
and vs_binders = (fun bs uvonly cont -> (match (bs) with
| [] -> begin
(cont (no_bvars, (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs)))
end
| (Support.Microsoft.FStar.Util.Inl (a), _)::rest -> begin
(vs_kind a.Microsoft_FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _70344 -> (match (_70344) with
| ((tvars, vvars), vs2) -> begin
(cont (((Support.Microsoft.FStar.Util.set_add a tvars), vvars), (union_fvs_uvs vs vs2)))
end)))))
end
| (Support.Microsoft.FStar.Util.Inr (x), _)::rest -> begin
(vs_typ x.Microsoft_FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _70357 -> (match (_70357) with
| ((tvars, vvars), vs2) -> begin
(cont ((tvars, (Support.Microsoft.FStar.Util.set_add x vvars)), (union_fvs_uvs vs vs2)))
end)))))
end))
and vs_args = (fun args uvonly cont -> (match (args) with
| [] -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| (Support.Microsoft.FStar.Util.Inl (t), _)::tl -> begin
(vs_typ t uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (cont (union_fvs_uvs ft1 ft2))))))
end
| (Support.Microsoft.FStar.Util.Inr (e), _)::tl -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (cont (union_fvs_uvs ft1 ft2))))))
end))
and vs_typ = (fun t uvonly cont -> (match (((! (t.Microsoft_FStar_Absyn_Syntax.fvs)), (! (t.Microsoft_FStar_Absyn_Syntax.uvs)))) with
| (Some (_), None) -> begin
(failwith "Impossible")
end
| (None, None) -> begin
(vs_typ' t uvonly (fun fvs -> (let _70394 = (stash uvonly t fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_typ' t uvonly (fun fvs -> (let _70401 = (stash uvonly t fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_kind' = (fun k uvonly cont -> (let k = (compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam ((_, k)) -> begin
(failwith (Support.Microsoft.FStar.Util.format1 "%s: Impossible ... found a Kind_lam bare" (Support.Microsoft.FStar.Range.string_of_range k.Microsoft_FStar_Absyn_Syntax.pos)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_) -> begin
(failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Kind_unknown) | (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, args)) -> begin
(vs_args args uvonly (fun _70430 -> (match (_70430) with
| (fvs, uvs) -> begin
(cont (fvs, (let _70431 = uvs
in {Microsoft_FStar_Absyn_Syntax.uvars_k = (Support.Microsoft.FStar.Util.set_add uv uvs.Microsoft_FStar_Absyn_Syntax.uvars_k); Microsoft_FStar_Absyn_Syntax.uvars_t = _70431.Microsoft_FStar_Absyn_Syntax.uvars_t; Microsoft_FStar_Absyn_Syntax.uvars_e = _70431.Microsoft_FStar_Absyn_Syntax.uvars_e})))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(vs_kind k uvonly cont)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(vs_binders bs uvonly (fun _70444 -> (match (_70444) with
| (bvs, vs1) -> begin
(vs_kind k uvonly (fun vs2 -> (cont (sub_fv (union_fvs_uvs vs1 vs2) bvs))))
end)))
end)))
and vs_kind = (fun k uvonly cont -> (match (((! (k.Microsoft_FStar_Absyn_Syntax.fvs)), (! (k.Microsoft_FStar_Absyn_Syntax.uvs)))) with
| (Some (_), None) -> begin
(failwith "Impossible")
end
| (None, None) -> begin
(vs_kind' k uvonly (fun fvs -> (let _70459 = (stash uvonly k fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_kind' k uvonly (fun fvs -> (let _70466 = (stash uvonly k fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_exp' = (fun e uvonly cont -> (let e = (compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_) -> begin
(failwith "impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, t)) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, (let _70491 = Microsoft_FStar_Absyn_Syntax.no_uvs
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _70491.Microsoft_FStar_Absyn_Syntax.uvars_k; Microsoft_FStar_Absyn_Syntax.uvars_t = _70491.Microsoft_FStar_Absyn_Syntax.uvars_t; Microsoft_FStar_Absyn_Syntax.uvars_e = (single_uvt (uv, t))})))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
if uvonly then begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end else begin
(cont ((let _70495 = Microsoft_FStar_Absyn_Syntax.no_fvs
in {Microsoft_FStar_Absyn_Syntax.ftvs = _70495.Microsoft_FStar_Absyn_Syntax.ftvs; Microsoft_FStar_Absyn_Syntax.fxvs = (single_fv x)}), Microsoft_FStar_Absyn_Syntax.no_uvs))
end
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _)) -> begin
(vs_exp e uvonly cont)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, e)) -> begin
(vs_binders bs uvonly (fun _70508 -> (match (_70508) with
| (bvs, vs1) -> begin
(vs_exp e uvonly (fun vs2 -> (cont (sub_fv (union_fvs_uvs vs1 vs2) bvs))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((e, args)) -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args args uvonly (fun ft2 -> (cont (union_fvs_uvs ft1 ft2))))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_match (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_let (_)) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(vs_exp e uvonly cont)
end)))
and vs_exp = (fun e uvonly cont -> (match (((! (e.Microsoft_FStar_Absyn_Syntax.fvs)), (! (e.Microsoft_FStar_Absyn_Syntax.uvs)))) with
| (Some (_), None) -> begin
(failwith "Impossible")
end
| (None, None) -> begin
(vs_exp' e uvonly (fun fvs -> (let _70541 = (stash uvonly e fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_exp' e uvonly (fun fvs -> (let _70548 = (stash uvonly e fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_comp' = (fun c uvonly k -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(vs_typ t uvonly k)
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
if uvonly then begin
(vs_typ ct.Microsoft_FStar_Absyn_Syntax.result_typ uvonly k)
end else begin
(vs_typ ct.Microsoft_FStar_Absyn_Syntax.result_typ uvonly (fun vs1 -> (vs_args ct.Microsoft_FStar_Absyn_Syntax.effect_args uvonly (fun vs2 -> (k (union_fvs_uvs vs1 vs2))))))
end
end))
and vs_comp = (fun c uvonly cont -> (match (((! (c.Microsoft_FStar_Absyn_Syntax.fvs)), (! (c.Microsoft_FStar_Absyn_Syntax.uvs)))) with
| (Some (_), None) -> begin
(failwith "Impossible")
end
| (None, None) -> begin
(vs_comp' c uvonly (fun fvs -> (let _70578 = (stash uvonly c fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_comp' c uvonly (fun fvs -> (let _70585 = (stash uvonly c fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_either = (fun te uvonly cont -> (match (te) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(vs_typ t uvonly cont)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(vs_exp e uvonly cont)
end))
and vs_either_l = (fun tes uvonly cont -> (match (tes) with
| [] -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| hd::tl -> begin
(vs_either hd uvonly (fun ft1 -> (vs_either_l tl uvonly (fun ft2 -> (cont (union_fvs_uvs ft1 ft2))))))
end))

let freevars_kind = (fun k -> (vs_kind k false (fun _70614 -> (match (_70614) with
| (x, _) -> begin
x
end))))

let freevars_typ = (fun t -> (vs_typ t false (fun _70619 -> (match (_70619) with
| (x, _) -> begin
x
end))))

let freevars_exp = (fun e -> (vs_exp e false (fun _70624 -> (match (_70624) with
| (x, _) -> begin
x
end))))

let freevars_comp = (fun c -> (vs_comp c false (fun _70629 -> (match (_70629) with
| (x, _) -> begin
x
end))))

let freevars_args = (fun args -> ((Support.List.fold_left (fun out a -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
((union_fvs out) (freevars_typ t))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
((union_fvs out) (freevars_exp e))
end)) Microsoft_FStar_Absyn_Syntax.no_fvs) args))

let is_free = (fun axs fvs -> ((Support.Microsoft.FStar.Util.for_some (fun _68790 -> (match (_68790) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(Support.Microsoft.FStar.Util.set_mem a fvs.Microsoft_FStar_Absyn_Syntax.ftvs)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(Support.Microsoft.FStar.Util.set_mem x fvs.Microsoft_FStar_Absyn_Syntax.fxvs)
end))) axs))

type syntax_sum =
| SynSumKind of Microsoft_FStar_Absyn_Syntax.knd
| SynSumType of Microsoft_FStar_Absyn_Syntax.typ
| SynSumExp of Microsoft_FStar_Absyn_Syntax.exp
| SynSumComp of (Microsoft_FStar_Absyn_Syntax.comp', unit) Microsoft_FStar_Absyn_Syntax.syntax

let rec update_uvars = (fun s uvs -> (let out = ((Support.List.fold_left (fun out u -> (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (k) -> begin
(union_uvs (uvars_in_kind k) out)
end
| _ -> begin
(let _70660 = out
in {Microsoft_FStar_Absyn_Syntax.uvars_k = (Support.Microsoft.FStar.Util.set_add u out.Microsoft_FStar_Absyn_Syntax.uvars_k); Microsoft_FStar_Absyn_Syntax.uvars_t = _70660.Microsoft_FStar_Absyn_Syntax.uvars_t; Microsoft_FStar_Absyn_Syntax.uvars_e = _70660.Microsoft_FStar_Absyn_Syntax.uvars_e})
end)) Microsoft_FStar_Absyn_Syntax.no_uvs) (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_k))
in (let out = ((Support.List.fold_left (fun out _70666 -> (match (_70666) with
| (u, t) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (t) -> begin
(union_uvs (uvars_in_typ t) out)
end
| _ -> begin
(let _70671 = out
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _70671.Microsoft_FStar_Absyn_Syntax.uvars_k; Microsoft_FStar_Absyn_Syntax.uvars_t = (Support.Microsoft.FStar.Util.set_add (u, t) out.Microsoft_FStar_Absyn_Syntax.uvars_t); Microsoft_FStar_Absyn_Syntax.uvars_e = _70671.Microsoft_FStar_Absyn_Syntax.uvars_e})
end)
end)) out) (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_t))
in (let out = ((Support.List.fold_left (fun out _70677 -> (match (_70677) with
| (u, t) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (e) -> begin
(union_uvs (uvars_in_exp e) out)
end
| _ -> begin
(let _70682 = out
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _70682.Microsoft_FStar_Absyn_Syntax.uvars_k; Microsoft_FStar_Absyn_Syntax.uvars_t = _70682.Microsoft_FStar_Absyn_Syntax.uvars_t; Microsoft_FStar_Absyn_Syntax.uvars_e = (Support.Microsoft.FStar.Util.set_add (u, t) out.Microsoft_FStar_Absyn_Syntax.uvars_e)})
end)
end)) out) (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_e))
in (let _70693 = (match (s) with
| SynSumKind (k) -> begin
(k.Microsoft_FStar_Absyn_Syntax.uvs := Some (out))
end
| SynSumType (t) -> begin
(t.Microsoft_FStar_Absyn_Syntax.uvs := Some (out))
end
| SynSumExp (e) -> begin
(e.Microsoft_FStar_Absyn_Syntax.uvs := Some (out))
end
| SynSumComp (c) -> begin
(c.Microsoft_FStar_Absyn_Syntax.uvs := Some (out))
end)
in out)))))
and uvars_in_kind = (fun k -> ((update_uvars (SynSumKind (k))) (vs_kind k true (fun _70699 -> (match (_70699) with
| (_, x) -> begin
x
end)))))
and uvars_in_typ = (fun t -> ((update_uvars (SynSumType (t))) (vs_typ t true (fun _70704 -> (match (_70704) with
| (_, x) -> begin
x
end)))))
and uvars_in_exp = (fun e -> ((update_uvars (SynSumExp (e))) (vs_exp e true (fun _70709 -> (match (_70709) with
| (_, x) -> begin
x
end)))))
and uvars_in_comp = (fun c -> ((update_uvars (SynSumComp (c))) (vs_comp c true (fun _70714 -> (match (_70714) with
| (_, x) -> begin
x
end)))))

let uvars_included_in = (fun u1 u2 -> (((Support.Microsoft.FStar.Util.set_is_subset_of u1.Microsoft_FStar_Absyn_Syntax.uvars_k u2.Microsoft_FStar_Absyn_Syntax.uvars_k) && (Support.Microsoft.FStar.Util.set_is_subset_of u1.Microsoft_FStar_Absyn_Syntax.uvars_t u2.Microsoft_FStar_Absyn_Syntax.uvars_t)) && (Support.Microsoft.FStar.Util.set_is_subset_of u1.Microsoft_FStar_Absyn_Syntax.uvars_e u2.Microsoft_FStar_Absyn_Syntax.uvars_e)))

let rec kind_formals = (fun k -> (let k = (compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam (_) -> begin
(failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Kind_unknown) | (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) | (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
([], k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _70734 = (kind_formals k)
in (match (_70734) with
| (bs', k) -> begin
((Support.List.append bs bs'), k)
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(kind_formals k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_) -> begin
(failwith "Impossible")
end)))

let close_for_kind = (fun t k -> (let _70748 = (kind_formals k)
in (match (_70748) with
| (bs, _) -> begin
(match (bs) with
| [] -> begin
t
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.Microsoft_FStar_Absyn_Syntax.pos)
end)
end)))

let rec unabbreviate_kind = (fun k -> (let k = (compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(unabbreviate_kind k)
end
| _ -> begin
k
end)))

let close_with_lam = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (tps, t) None t.Microsoft_FStar_Absyn_Syntax.pos)
end))

let close_with_arrow = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _ -> begin
(let _70779 = (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs', c)) -> begin
((Support.List.append tps bs'), c)
end
| _ -> begin
(tps, (Microsoft_FStar_Absyn_Syntax.mk_Total t))
end)
in (match (_70779) with
| (bs, c) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.Microsoft_FStar_Absyn_Syntax.pos)
end))
end))

let close_typ = close_with_arrow

let close_kind = (fun tps k -> (match (tps) with
| [] -> begin
k
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow' (tps, k) k.Microsoft_FStar_Absyn_Syntax.pos)
end))

let is_tuple_constructor = (fun t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (l) -> begin
(Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str "Prims.Tuple")
end
| _ -> begin
false
end))

let mk_tuple_lid = (fun n r -> (let t = (Support.Microsoft.FStar.Util.format1 "Tuple%s" (Support.Microsoft.FStar.Util.string_of_int n))
in (set_lid_range (Microsoft_FStar_Absyn_Const.pconst t) r)))

let mk_tuple_data_lid = (fun n r -> (let t = (Support.Microsoft.FStar.Util.format1 "MkTuple%s" (Support.Microsoft.FStar.Util.string_of_int n))
in (set_lid_range (Microsoft_FStar_Absyn_Const.pconst t) r)))

let is_tuple_data_lid = (fun f n -> (Microsoft_FStar_Absyn_Syntax.lid_equals f (mk_tuple_data_lid n Microsoft_FStar_Absyn_Syntax.dummyRange)))

let is_dtuple_constructor = (fun t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (l) -> begin
(Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str "Prims.DTuple")
end
| _ -> begin
false
end))

let mk_dtuple_lid = (fun n r -> (let t = (Support.Microsoft.FStar.Util.format1 "DTuple%s" (Support.Microsoft.FStar.Util.string_of_int n))
in (set_lid_range (Microsoft_FStar_Absyn_Const.pconst t) r)))

let mk_dtuple_data_lid = (fun n r -> (let t = (Support.Microsoft.FStar.Util.format1 "MkDTuple%s" (Support.Microsoft.FStar.Util.string_of_int n))
in (set_lid_range (Microsoft_FStar_Absyn_Const.pconst t) r)))

let is_lid_equality = (fun x -> ((((Microsoft_FStar_Absyn_Syntax.lid_equals x Microsoft_FStar_Absyn_Const.eq_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals x Microsoft_FStar_Absyn_Const.eq2_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals x Microsoft_FStar_Absyn_Const.eqA_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals x Microsoft_FStar_Absyn_Const.eqT_lid)))

let is_forall = (fun lid -> ((Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.forall_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.allTyp_lid)))

let is_exists = (fun lid -> ((Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.exists_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.exTyp_lid)))

let is_qlid = (fun lid -> ((is_forall lid) || (is_exists lid)))

let is_equality = (fun x -> (is_lid_equality x.Microsoft_FStar_Absyn_Syntax.v))

let lid_is_connective = (let lst = (Microsoft_FStar_Absyn_Const.and_lid)::(Microsoft_FStar_Absyn_Const.or_lid)::(Microsoft_FStar_Absyn_Const.not_lid)::(Microsoft_FStar_Absyn_Const.iff_lid)::(Microsoft_FStar_Absyn_Const.imp_lid)::[]
in (fun lid -> (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals lid) lst)))

let is_constructor = (fun t lid -> (match ((pre_typ t).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v lid)
end
| _ -> begin
false
end))

let rec is_constructed_typ = (fun t lid -> (match ((pre_typ t).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (_) -> begin
(is_constructor t lid)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, _)) -> begin
(is_constructed_typ t lid)
end
| _ -> begin
false
end))

let rec get_tycon = (fun t -> (let t = (pre_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) -> begin
Some (t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, _)) -> begin
(get_tycon t)
end
| _ -> begin
None
end)))

let base_kind = (fun _68791 -> (match (_68791) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
true
end
| _ -> begin
false
end))

let sortByFieldName = (fun fn_a_l -> ((Support.List.sortWith (fun _70858 _70862 -> (match ((_70858, _70862)) with
| ((fn1, _), (fn2, _)) -> begin
(Support.String.compare (Microsoft_FStar_Absyn_Syntax.text_of_lid fn1) (Microsoft_FStar_Absyn_Syntax.text_of_lid fn2))
end))) fn_a_l))

let kt_kt = (Microsoft_FStar_Absyn_Const.kunary Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype)

let kt_kt_kt = (Microsoft_FStar_Absyn_Const.kbin Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype)

let tand = (ftv Microsoft_FStar_Absyn_Const.and_lid kt_kt_kt)

let tor = (ftv Microsoft_FStar_Absyn_Const.or_lid kt_kt_kt)

let timp = (ftv Microsoft_FStar_Absyn_Const.imp_lid kt_kt_kt)

let tiff = (ftv Microsoft_FStar_Absyn_Const.iff_lid kt_kt_kt)

let t_bool = (ftv Microsoft_FStar_Absyn_Const.bool_lid Microsoft_FStar_Absyn_Syntax.ktype)

let t_false = (ftv Microsoft_FStar_Absyn_Const.false_lid Microsoft_FStar_Absyn_Syntax.ktype)

let t_true = (ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)

let b2t_v = (ftv Microsoft_FStar_Absyn_Const.b2t_lid (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (((Microsoft_FStar_Absyn_Syntax.null_v_binder t_bool))::[], Microsoft_FStar_Absyn_Syntax.ktype) Microsoft_FStar_Absyn_Syntax.dummyRange))

let mk_conj_opt = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
Some ((Microsoft_FStar_Absyn_Syntax.mk_Typ_app (tand, ((Microsoft_FStar_Absyn_Syntax.targ phi1))::((Microsoft_FStar_Absyn_Syntax.targ phi2))::[]) None (Support.Microsoft.FStar.Range.union_ranges phi1.Microsoft_FStar_Absyn_Syntax.pos phi2.Microsoft_FStar_Absyn_Syntax.pos)))
end))

let mk_binop = (fun op_t phi1 phi2 -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (op_t, ((Microsoft_FStar_Absyn_Syntax.targ phi1))::((Microsoft_FStar_Absyn_Syntax.targ phi2))::[]) None (Support.Microsoft.FStar.Range.union_ranges phi1.Microsoft_FStar_Absyn_Syntax.pos phi2.Microsoft_FStar_Absyn_Syntax.pos)))

let mk_neg = (fun phi -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_app ((ftv Microsoft_FStar_Absyn_Const.not_lid kt_kt), ((Microsoft_FStar_Absyn_Syntax.targ phi))::[]) None phi.Microsoft_FStar_Absyn_Syntax.pos))

let mk_conj = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))

let mk_conj_l = (fun phi -> (match (phi) with
| [] -> begin
(ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
end
| hd::tl -> begin
(Support.List.fold_right mk_conj tl hd)
end))

let mk_disj = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))

let mk_disj_l = (fun phi -> (match (phi) with
| [] -> begin
(ftv Microsoft_FStar_Absyn_Const.false_lid Microsoft_FStar_Absyn_Syntax.ktype)
end
| hd::tl -> begin
(Support.List.fold_right mk_disj tl hd)
end))

let mk_imp = (fun phi1 phi2 -> (match ((compress_typ phi1).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.false_lid) -> begin
t_true
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
phi2
end
| _ -> begin
(match ((compress_typ phi2).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when ((Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.false_lid)) -> begin
phi2
end
| _ -> begin
(mk_binop timp phi1 phi2)
end)
end))

let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))

let b2t = (fun e -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (b2t_v, ((Microsoft_FStar_Absyn_Syntax.varg e))::[]) None e.Microsoft_FStar_Absyn_Syntax.pos))

let rec unmeta_typ = (fun t -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, _, _, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _, _)))) -> begin
(unmeta_typ t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, _))) -> begin
(mk_conj t1 t2)
end
| _ -> begin
t
end)))

let eq_k = (let a = (bvd_to_bvar_s (new_bvd None) Microsoft_FStar_Absyn_Syntax.ktype)
in (let atyp = (btvar_to_typ a)
in (let b = (bvd_to_bvar_s (new_bvd None) Microsoft_FStar_Absyn_Syntax.ktype)
in (let btyp = (btvar_to_typ b)
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::((Support.Microsoft.FStar.Util.Inl (b), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::((Microsoft_FStar_Absyn_Syntax.null_v_binder atyp))::((Microsoft_FStar_Absyn_Syntax.null_v_binder btyp))::[], Microsoft_FStar_Absyn_Syntax.ktype) Microsoft_FStar_Absyn_Syntax.dummyRange)))))

let teq = (ftv Microsoft_FStar_Absyn_Const.eq2_lid eq_k)

let mk_eq = (fun t1 t2 e1 e2 -> (match ((t1.Microsoft_FStar_Absyn_Syntax.n, t2.Microsoft_FStar_Absyn_Syntax.n)) with
| ((Microsoft_FStar_Absyn_Syntax.Typ_unknown, _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_unknown)) -> begin
(failwith "DIE! mk_eq with tun")
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (teq, ((Microsoft_FStar_Absyn_Syntax.itarg t1))::((Microsoft_FStar_Absyn_Syntax.itarg t2))::((Microsoft_FStar_Absyn_Syntax.varg e1))::((Microsoft_FStar_Absyn_Syntax.varg e2))::[]) None (Support.Microsoft.FStar.Range.union_ranges e1.Microsoft_FStar_Absyn_Syntax.pos e2.Microsoft_FStar_Absyn_Syntax.pos))
end))

let eq_typ = (ftv Microsoft_FStar_Absyn_Const.eqT_lid Microsoft_FStar_Absyn_Syntax.kun)

let mk_eq_typ = (fun t1 t2 -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (eq_typ, ((Microsoft_FStar_Absyn_Syntax.targ t1))::((Microsoft_FStar_Absyn_Syntax.targ t2))::[]) None (Support.Microsoft.FStar.Range.union_ranges t1.Microsoft_FStar_Absyn_Syntax.pos t2.Microsoft_FStar_Absyn_Syntax.pos)))

let lex_t = (ftv Microsoft_FStar_Absyn_Const.lex_t_lid Microsoft_FStar_Absyn_Syntax.ktype)

let lex_top = (let lexnil = (withinfo Microsoft_FStar_Absyn_Const.lextop_lid lex_t Microsoft_FStar_Absyn_Syntax.dummyRange)
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar (lexnil, true) None Microsoft_FStar_Absyn_Syntax.dummyRange))

let lex_pair = (let a = (gen_bvar Microsoft_FStar_Absyn_Syntax.ktype)
in (let lexcons = (withinfo Microsoft_FStar_Absyn_Const.lexcons_lid (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (((Microsoft_FStar_Absyn_Syntax.t_binder a))::((Microsoft_FStar_Absyn_Syntax.null_v_binder (btvar_to_typ a)))::((Microsoft_FStar_Absyn_Syntax.null_v_binder lex_t))::[], (Microsoft_FStar_Absyn_Syntax.mk_Total lex_t)) None Microsoft_FStar_Absyn_Syntax.dummyRange) Microsoft_FStar_Absyn_Syntax.dummyRange)
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar (lexcons, true) None Microsoft_FStar_Absyn_Syntax.dummyRange)))

let forall_kind = (let a = (bvd_to_bvar_s (new_bvd None) Microsoft_FStar_Absyn_Syntax.ktype)
in (let atyp = (btvar_to_typ a)
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::((Microsoft_FStar_Absyn_Syntax.null_t_binder (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (((Microsoft_FStar_Absyn_Syntax.null_v_binder atyp))::[], Microsoft_FStar_Absyn_Syntax.ktype) Microsoft_FStar_Absyn_Syntax.dummyRange)))::[], Microsoft_FStar_Absyn_Syntax.ktype) Microsoft_FStar_Absyn_Syntax.dummyRange)))

let tforall = (ftv Microsoft_FStar_Absyn_Const.forall_lid forall_kind)

let allT_k = (fun k -> (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (((Microsoft_FStar_Absyn_Syntax.null_t_binder (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (((Microsoft_FStar_Absyn_Syntax.null_t_binder k))::[], Microsoft_FStar_Absyn_Syntax.ktype) Microsoft_FStar_Absyn_Syntax.dummyRange)))::[], Microsoft_FStar_Absyn_Syntax.ktype) Microsoft_FStar_Absyn_Syntax.dummyRange))

let eqT_k = (fun k -> (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (((Microsoft_FStar_Absyn_Syntax.null_t_binder k))::((Microsoft_FStar_Absyn_Syntax.null_t_binder k))::[], Microsoft_FStar_Absyn_Syntax.ktype) Microsoft_FStar_Absyn_Syntax.dummyRange))

let tforall_typ = (fun k -> (ftv Microsoft_FStar_Absyn_Const.allTyp_lid (allT_k k)))

let mk_forallT = (fun a b -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_app ((tforall_typ a.Microsoft_FStar_Absyn_Syntax.sort), ((Microsoft_FStar_Absyn_Syntax.targ (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (((Microsoft_FStar_Absyn_Syntax.t_binder a))::[], b) None b.Microsoft_FStar_Absyn_Syntax.pos)))::[]) None b.Microsoft_FStar_Absyn_Syntax.pos))

let mk_forall = (fun x body -> (let r = Microsoft_FStar_Absyn_Syntax.dummyRange
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (tforall, ((Microsoft_FStar_Absyn_Syntax.targ (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (((Microsoft_FStar_Absyn_Syntax.v_binder x))::[], body) None r)))::[]) None r)))

let rec close_forall = (fun bs f -> (Support.List.fold_right (fun b f -> if (Microsoft_FStar_Absyn_Syntax.is_null_binder b) then begin
f
end else begin
(let body = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam ((b)::[], f) None f.Microsoft_FStar_Absyn_Syntax.pos)
in (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app ((tforall_typ a.Microsoft_FStar_Absyn_Syntax.sort), ((Microsoft_FStar_Absyn_Syntax.targ body))::[]) None f.Microsoft_FStar_Absyn_Syntax.pos)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_app (tforall, ((Support.Microsoft.FStar.Util.Inl (x.Microsoft_FStar_Absyn_Syntax.sort), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::((Microsoft_FStar_Absyn_Syntax.targ body))::[]) None f.Microsoft_FStar_Absyn_Syntax.pos)
end))
end) bs f))

let rec is_wild_pat = (fun p -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_wild (_) -> begin
true
end
| _ -> begin
false
end))

let head_and_args = (fun t -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(head, args)
end
| _ -> begin
(t, [])
end)))

let head_and_args_e = (fun e -> (let e = (compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(head, args)
end
| _ -> begin
(e, [])
end)))

let function_formals = (fun t -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
Some ((bs, c))
end
| _ -> begin
None
end)))

let is_interpreted = (fun l -> (let theory_syms = (Microsoft_FStar_Absyn_Const.op_Eq)::(Microsoft_FStar_Absyn_Const.op_notEq)::(Microsoft_FStar_Absyn_Const.op_LT)::(Microsoft_FStar_Absyn_Const.op_LTE)::(Microsoft_FStar_Absyn_Const.op_GT)::(Microsoft_FStar_Absyn_Const.op_GTE)::(Microsoft_FStar_Absyn_Const.op_Subtraction)::(Microsoft_FStar_Absyn_Const.op_Minus)::(Microsoft_FStar_Absyn_Const.op_Addition)::(Microsoft_FStar_Absyn_Const.op_Multiply)::(Microsoft_FStar_Absyn_Const.op_Division)::(Microsoft_FStar_Absyn_Const.op_Modulus)::(Microsoft_FStar_Absyn_Const.op_And)::(Microsoft_FStar_Absyn_Const.op_Or)::(Microsoft_FStar_Absyn_Const.op_Negation)::[]
in (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals l) theory_syms)))

type qpats =
Microsoft_FStar_Absyn_Syntax.args

type connective =
| QAll of (Microsoft_FStar_Absyn_Syntax.binders * qpats * Microsoft_FStar_Absyn_Syntax.typ)
| QEx of (Microsoft_FStar_Absyn_Syntax.binders * qpats * Microsoft_FStar_Absyn_Syntax.typ)
| BaseConn of (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.args)

let destruct_typ_as_formula = (fun f -> (let destruct_base_conn = (fun f -> (let _71028 = (true, false)
in (match (_71028) with
| (type_sort, term_sort) -> begin
(let oneType = (type_sort)::[]
in (let twoTypes = (type_sort)::(type_sort)::[]
in (let threeTys = (type_sort)::(type_sort)::(type_sort)::[]
in (let twoTerms = (term_sort)::(term_sort)::[]
in (let connectives = ((Microsoft_FStar_Absyn_Const.true_lid, []))::((Microsoft_FStar_Absyn_Const.false_lid, []))::((Microsoft_FStar_Absyn_Const.and_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.or_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.imp_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.iff_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.ite_lid, threeTys))::((Microsoft_FStar_Absyn_Const.not_lid, oneType))::((Microsoft_FStar_Absyn_Const.eqT_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.eq2_lid, twoTerms))::((Microsoft_FStar_Absyn_Const.eq2_lid, (Support.List.append twoTypes twoTerms)))::[]
in (let rec aux = (fun f _71038 -> (match (_71038) with
| (lid, arity) -> begin
(let _71041 = (head_and_args f)
in (match (_71041) with
| (t, args) -> begin
if (((is_constructor t lid) && ((Support.List.length args) = (Support.List.length arity))) && (Support.List.forall2 (fun arg flag -> (match (arg) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
(flag = type_sort)
end
| (Support.Microsoft.FStar.Util.Inr (_), _) -> begin
(flag = term_sort)
end)) args arity)) then begin
Some (BaseConn ((lid, args)))
end else begin
None
end
end))
end))
in (Support.Microsoft.FStar.Util.find_map connectives (aux f))))))))
end)))
in (let patterns = (fun t -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, pats))) -> begin
(pats, (compress_typ t))
end
| _ -> begin
([], (compress_typ t))
end)))
in (let destruct_q_conn = (fun t -> (let is_q = (fun fa l -> if fa then begin
(is_forall l)
end else begin
(is_exists l)
end)
in (let flat = (fun t -> (let _71075 = (head_and_args t)
in (match (_71075) with
| (t, args) -> begin
(t, ((Support.List.map (fun _68792 -> (match (_68792) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(Support.Microsoft.FStar.Util.Inl ((compress_typ t)), imp)
end
| (Support.Microsoft.FStar.Util.Inr (e), imp) -> begin
(Support.Microsoft.FStar.Util.Inr ((compress_exp e)), imp)
end))) args))
end)))
in (let rec aux = (fun qopt out t -> (match ((qopt, (flat t))) with
| ((Some (fa), ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, (Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t2)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((Some (fa), ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _::(Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t2)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_q fa tc.Microsoft_FStar_Absyn_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, (Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t2)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((None, ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _::(Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t2)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_qlid tc.Microsoft_FStar_Absyn_Syntax.v) -> begin
(aux (Some ((is_forall tc.Microsoft_FStar_Absyn_Syntax.v))) ((b)::out) t2)
end
| (Some (true), _) -> begin
(let _71227 = (patterns t)
in (match (_71227) with
| (pats, body) -> begin
Some (QAll (((Support.List.rev out), pats, body)))
end))
end
| (Some (false), _) -> begin
(let _71235 = (patterns t)
in (match (_71235) with
| (pats, body) -> begin
Some (QEx (((Support.List.rev out), pats, body)))
end))
end
| _ -> begin
None
end))
in (aux None [] t)))))
in (let phi = (compress_typ f)
in (match ((destruct_base_conn phi)) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end))))))




