
let handle_err = (fun ( warning ) ( ret ) ( e ) -> (match (e) with
| Microsoft_FStar_Absyn_Syntax.Error ((msg, r)) -> begin
()
end
| Support.Microsoft.FStar.Util.NYI (s) -> begin
()
end
| Microsoft_FStar_Absyn_Syntax.Err (s) -> begin
(let _52_4938 = (Support.Microsoft.FStar.Util.format1 "Error: %s" s)
in (Support.Microsoft.FStar.Util.print_string _52_4938))
end
| _ -> begin
(raise (e))
end))

let handleable = (fun ( _23_1 ) -> (match (_23_1) with
| (Microsoft_FStar_Absyn_Syntax.Error (_)) | (Support.Microsoft.FStar.Util.NYI (_)) | (Microsoft_FStar_Absyn_Syntax.Err (_)) -> begin
true
end
| _ -> begin
false
end))

type gensym_t =
{gensym : unit  ->  string; reset : unit  ->  unit}

let is_Mkgensym_t = (fun ( _ ) -> (failwith ("Not yet implemented")))

let gs = (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (let n_resets = (Support.Microsoft.FStar.Util.mk_ref 0)
in {gensym = (fun ( _23_60 ) -> (match (()) with
| () -> begin
(let _52_4966 = (let _52_4963 = (let _52_4962 = (let _52_4961 = (Support.ST.read n_resets)
in (Support.Microsoft.FStar.Util.string_of_int _52_4961))
in (Support.String.strcat "_" _52_4962))
in (Support.String.strcat _52_4963 "_"))
in (let _52_4965 = (let _52_4964 = (let _23_61 = (Support.Microsoft.FStar.Util.incr ctr)
in (Support.ST.read ctr))
in (Support.Microsoft.FStar.Util.string_of_int _52_4964))
in (Support.String.strcat _52_4966 _52_4965)))
end)); reset = (fun ( _23_63 ) -> (match (()) with
| () -> begin
(let _23_64 = (Support.ST.op_Colon_Equals ctr 0)
in (Support.Microsoft.FStar.Util.incr n_resets))
end))}))

let gensym = (fun ( _23_66 ) -> (match (()) with
| () -> begin
(gs.gensym ())
end))

let reset_gensym = (fun ( _23_67 ) -> (match (()) with
| () -> begin
(gs.reset ())
end))

let rec gensyms = (fun ( x ) -> (match (x) with
| 0 -> begin
[]
end
| n -> begin
(let _52_4975 = (gensym ())
in (let _52_4974 = (gensyms (n - 1))
in (_52_4975)::_52_4974))
end))

let genident = (fun ( r ) -> (let sym = (gensym ())
in (match (r) with
| None -> begin
(Microsoft_FStar_Absyn_Syntax.mk_ident (sym, Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| Some (r) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_ident (sym, r))
end)))

let bvd_eq = (fun ( bvd1 ) ( bvd2 ) -> (bvd1.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText = bvd2.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText))

let range_of_bvd = (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idRange)

let mkbvd = (fun ( _23_81 ) -> (match (_23_81) with
| (x, y) -> begin
{Microsoft_FStar_Absyn_Syntax.ppname = x; Microsoft_FStar_Absyn_Syntax.realname = y}
end))

let setsort = (fun ( w ) ( t ) -> {Microsoft_FStar_Absyn_Syntax.v = w.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = w.Microsoft_FStar_Absyn_Syntax.p})

let withinfo = (fun ( e ) ( s ) ( r ) -> {Microsoft_FStar_Absyn_Syntax.v = e; Microsoft_FStar_Absyn_Syntax.sort = s; Microsoft_FStar_Absyn_Syntax.p = r})

let withsort = (fun ( e ) ( s ) -> (withinfo e s Microsoft_FStar_Absyn_Syntax.dummyRange))

let bvar_ppname = (fun ( bv ) -> bv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)

let bvar_realname = (fun ( bv ) -> bv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname)

let bvar_eq = (fun ( bv1 ) ( bv2 ) -> (bvd_eq bv1.Microsoft_FStar_Absyn_Syntax.v bv2.Microsoft_FStar_Absyn_Syntax.v))

let lbname_eq = (fun ( l1 ) ( l2 ) -> (match ((l1, l2)) with
| (Support.Microsoft.FStar.Util.Inl (x), Support.Microsoft.FStar.Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (Support.Microsoft.FStar.Util.Inr (l), Support.Microsoft.FStar.Util.Inr (m)) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l m)
end
| _ -> begin
false
end))

let fvar_eq = (fun ( fv1 ) ( fv2 ) -> (Microsoft_FStar_Absyn_Syntax.lid_equals fv1.Microsoft_FStar_Absyn_Syntax.v fv2.Microsoft_FStar_Absyn_Syntax.v))

let bvd_to_bvar_s = (fun ( bvd ) ( sort ) -> {Microsoft_FStar_Absyn_Syntax.v = bvd; Microsoft_FStar_Absyn_Syntax.sort = sort; Microsoft_FStar_Absyn_Syntax.p = bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idRange})

let bvar_to_bvd = (fun ( bv ) -> bv.Microsoft_FStar_Absyn_Syntax.v)

let btvar_to_typ = (fun ( bv ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar bv None bv.Microsoft_FStar_Absyn_Syntax.p))

let bvd_to_typ = (fun ( bvd ) ( k ) -> (btvar_to_typ (bvd_to_bvar_s bvd k)))

let bvar_to_exp = (fun ( bv ) -> (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar bv None bv.Microsoft_FStar_Absyn_Syntax.p))

let bvd_to_exp = (fun ( bvd ) ( t ) -> (bvar_to_exp (bvd_to_bvar_s bvd t)))

let new_bvd = (fun ( ropt ) -> (let f = (fun ( ropt ) -> (let id = (genident ropt)
in (mkbvd (id, id))))
in (f ropt)))

let freshen_bvd = (fun ( bvd' ) -> (let _52_5016 = (let _52_5015 = (genident (Some ((range_of_bvd bvd'))))
in (bvd'.Microsoft_FStar_Absyn_Syntax.ppname, _52_5015))
in (mkbvd _52_5016)))

let freshen_bvar = (fun ( b ) -> (let _52_5018 = (freshen_bvd b.Microsoft_FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _52_5018 b.Microsoft_FStar_Absyn_Syntax.sort)))

let gen_bvar = (fun ( sort ) -> (let bvd = (new_bvd None)
in (bvd_to_bvar_s bvd sort)))

let gen_bvar_p = (fun ( r ) ( sort ) -> (let bvd = (new_bvd (Some (r)))
in (bvd_to_bvar_s bvd sort)))

let bvdef_of_str = (fun ( s ) -> (let f = (fun ( s ) -> (let id = (Microsoft_FStar_Absyn_Syntax.id_of_text s)
in (mkbvd (id, id))))
in (f s)))

let set_bvd_range = (fun ( bvd ) ( r ) -> (let _52_5027 = (Microsoft_FStar_Absyn_Syntax.mk_ident (bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText, r))
in (let _52_5026 = (Microsoft_FStar_Absyn_Syntax.mk_ident (bvd.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText, r))
in {Microsoft_FStar_Absyn_Syntax.ppname = _52_5027; Microsoft_FStar_Absyn_Syntax.realname = _52_5026})))

let set_lid_range = (fun ( l ) ( r ) -> (let ids = (Support.Prims.pipe_right (Support.List.append l.Microsoft_FStar_Absyn_Syntax.ns ((l.Microsoft_FStar_Absyn_Syntax.ident)::[])) (Support.List.map (fun ( i ) -> (Microsoft_FStar_Absyn_Syntax.mk_ident (i.Microsoft_FStar_Absyn_Syntax.idText, r)))))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids ids)))

let fv = (fun ( l ) -> (let _52_5035 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l Microsoft_FStar_Absyn_Syntax.tun _52_5035)))

let fvvar_of_lid = (fun ( l ) ( t ) -> (let _52_5038 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l t _52_5038)))

let fvar = (fun ( dc ) ( l ) ( r ) -> (let _52_5047 = (let _52_5046 = (let _52_5045 = (set_lid_range l r)
in (fv _52_5045))
in (_52_5046, dc))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _52_5047 None r)))

let ftv = (fun ( l ) ( k ) -> (let _52_5054 = (let _52_5052 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l k _52_5052))
in (let _52_5053 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_const _52_5054 None _52_5053))))

let order_bvd = (fun ( x ) ( y ) -> (match ((x, y)) with
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

let arg_of_non_null_binder = (fun ( _23_179 ) -> (match (_23_179) with
| (b, imp) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _52_5059 = (let _52_5058 = (btvar_to_typ a)
in Support.Microsoft.FStar.Util.Inl (_52_5058))
in (_52_5059, imp))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _52_5061 = (let _52_5060 = (bvar_to_exp x)
in Support.Microsoft.FStar.Util.Inr (_52_5060))
in (_52_5061, imp))
end)
end))

let args_of_non_null_binders = (fun ( binders ) -> (Support.Prims.pipe_right binders (Support.List.collect (fun ( b ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
[]
end
| false -> begin
(let _52_5065 = (arg_of_non_null_binder b)
in (_52_5065)::[])
end)))))

let args_of_binders = (fun ( binders ) -> (let _52_5075 = (Support.Prims.pipe_right binders (Support.List.map (fun ( b ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
(let b = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _52_5070 = (let _52_5069 = (gen_bvar a.Microsoft_FStar_Absyn_Syntax.sort)
in Support.Microsoft.FStar.Util.Inl (_52_5069))
in (_52_5070, (Support.Prims.snd b)))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _52_5072 = (let _52_5071 = (gen_bvar x.Microsoft_FStar_Absyn_Syntax.sort)
in Support.Microsoft.FStar.Util.Inr (_52_5071))
in (_52_5072, (Support.Prims.snd b)))
end)
in (let _52_5073 = (arg_of_non_null_binder b)
in (b, _52_5073)))
end
| false -> begin
(let _52_5074 = (arg_of_non_null_binder b)
in (b, _52_5074))
end))))
in (Support.Prims.pipe_right _52_5075 Support.List.unzip)))

let name_binders = (fun ( binders ) -> (Support.Prims.pipe_right binders (Support.List.mapi (fun ( i ) ( b ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
(match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let b = (let _52_5081 = (let _52_5080 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.String.strcat "_" _52_5080))
in (Microsoft_FStar_Absyn_Syntax.id_of_text _52_5081))
in (let b = (bvd_to_bvar_s (mkbvd (b, b)) a.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.Inl (b), imp)))
end
| (Support.Microsoft.FStar.Util.Inr (y), imp) -> begin
(let x = (let _52_5083 = (let _52_5082 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.String.strcat "_" _52_5082))
in (Microsoft_FStar_Absyn_Syntax.id_of_text _52_5083))
in (let x = (bvd_to_bvar_s (mkbvd (x, x)) y.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.Inr (x), imp)))
end)
end
| false -> begin
b
end)))))

let name_function_binders = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, comp)) -> begin
(let _52_5087 = (let _52_5086 = (name_binders binders)
in (_52_5086, comp))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _52_5087 None t.Microsoft_FStar_Absyn_Syntax.pos))
end
| _ -> begin
t
end))

let null_binders_of_tks = (fun ( tks ) -> (Support.Prims.pipe_right tks (Support.List.map (fun ( _23_2 ) -> (match (_23_2) with
| (Support.Microsoft.FStar.Util.Inl (k), imp) -> begin
(let _52_5092 = (let _52_5091 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (Support.Prims.pipe_left Support.Prims.fst _52_5091))
in (_52_5092, imp))
end
| (Support.Microsoft.FStar.Util.Inr (t), imp) -> begin
(let _52_5094 = (let _52_5093 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (Support.Prims.pipe_left Support.Prims.fst _52_5093))
in (_52_5094, imp))
end)))))

let binders_of_tks = (fun ( tks ) -> (Support.Prims.pipe_right tks (Support.List.map (fun ( _23_3 ) -> (match (_23_3) with
| (Support.Microsoft.FStar.Util.Inl (k), imp) -> begin
(let _52_5099 = (let _52_5098 = (gen_bvar_p k.Microsoft_FStar_Absyn_Syntax.pos k)
in Support.Microsoft.FStar.Util.Inl (_52_5098))
in (_52_5099, imp))
end
| (Support.Microsoft.FStar.Util.Inr (t), imp) -> begin
(let _52_5101 = (let _52_5100 = (gen_bvar_p t.Microsoft_FStar_Absyn_Syntax.pos t)
in Support.Microsoft.FStar.Util.Inr (_52_5100))
in (_52_5101, imp))
end)))))

let binders_of_freevars = (fun ( fvs ) -> (let _52_5107 = (let _52_5104 = (Support.Microsoft.FStar.Util.set_elements fvs.Microsoft_FStar_Absyn_Syntax.ftvs)
in (Support.Prims.pipe_right _52_5104 (Support.List.map Microsoft_FStar_Absyn_Syntax.t_binder)))
in (let _52_5106 = (let _52_5105 = (Support.Microsoft.FStar.Util.set_elements fvs.Microsoft_FStar_Absyn_Syntax.fxvs)
in (Support.Prims.pipe_right _52_5105 (Support.List.map Microsoft_FStar_Absyn_Syntax.v_binder)))
in (Support.List.append _52_5107 _52_5106))))

let subst_to_string = (fun ( s ) -> (let _52_5110 = (Support.Prims.pipe_right s (Support.List.map (fun ( _23_4 ) -> (match (_23_4) with
| Support.Microsoft.FStar.Util.Inl ((b, _)) -> begin
b.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText
end
| Support.Microsoft.FStar.Util.Inr ((x, _)) -> begin
x.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText
end))))
in (Support.Prims.pipe_right _52_5110 (Support.String.concat ", "))))

let subst_tvar = (fun ( s ) ( a ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _23_5 ) -> (match (_23_5) with
| Support.Microsoft.FStar.Util.Inl ((b, t)) when (bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _ -> begin
None
end))))

let subst_xvar = (fun ( s ) ( a ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _23_6 ) -> (match (_23_6) with
| Support.Microsoft.FStar.Util.Inr ((b, t)) when (bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _ -> begin
None
end))))

let rec subst_typ' = (fun ( s ) ( t ) -> (match (s) with
| ([]) | ([]::[]) -> begin
(Microsoft_FStar_Absyn_Visit.compress_typ t)
end
| _ -> begin
(let t0 = (Microsoft_FStar_Absyn_Visit.compress_typ t)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((Support.Microsoft.FStar.Util.Inl ((t', s')), m)) -> begin
(let _52_5135 = (let _52_5134 = (compose_subst s' s)
in (let _52_5133 = (Support.Microsoft.FStar.Util.mk_ref None)
in (t', _52_5134, _52_5133)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_delayed _52_5135 None t.Microsoft_FStar_Absyn_Syntax.pos))
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((Support.Microsoft.FStar.Util.Inr (mk_t), m)) -> begin
(let t = (mk_t ())
in (let _23_287 = (Support.ST.op_Colon_Equals m (Some (t)))
in (subst_typ' s t)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let rec aux = (fun ( s' ) -> (match (s') with
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
(let _52_5140 = (let _52_5139 = (Support.Microsoft.FStar.Util.mk_ref None)
in (t0, s, _52_5139))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_delayed _52_5140 None t.Microsoft_FStar_Absyn_Syntax.pos))
end))
end))
and subst_exp' = (fun ( s ) ( e ) -> (match (s) with
| ([]) | ([]::[]) -> begin
(Microsoft_FStar_Absyn_Visit.compress_exp e)
end
| _ -> begin
(let e0 = (Microsoft_FStar_Absyn_Visit.compress_exp e)
in (match (e0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed ((e, s', m)) -> begin
(let _52_5145 = (let _52_5144 = (compose_subst s' s)
in (let _52_5143 = (Support.Microsoft.FStar.Util.mk_ref None)
in (e, _52_5144, _52_5143)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_delayed _52_5145 None e.Microsoft_FStar_Absyn_Syntax.pos))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let rec aux = (fun ( s ) -> (match (s) with
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
(let _52_5149 = (let _52_5148 = (Support.Microsoft.FStar.Util.mk_ref None)
in (e0, s, _52_5148))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_delayed _52_5149 None e0.Microsoft_FStar_Absyn_Syntax.pos))
end))
end))
and subst_kind' = (fun ( s ) ( k ) -> (match (s) with
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
(let _52_5154 = (let _52_5153 = (compose_subst s' s)
in (let _52_5152 = (Support.Microsoft.FStar.Util.mk_ref None)
in (k, _52_5153, _52_5152)))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_delayed _52_5154 k0.Microsoft_FStar_Absyn_Syntax.pos))
end
| _ -> begin
(let _52_5156 = (let _52_5155 = (Support.Microsoft.FStar.Util.mk_ref None)
in (k0, s, _52_5155))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_delayed _52_5156 k0.Microsoft_FStar_Absyn_Syntax.pos))
end))
end))
and subst_flags' = (fun ( s ) ( flags ) -> (Support.Prims.pipe_right flags (Support.List.map (fun ( _23_7 ) -> (match (_23_7) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (a) -> begin
(let _52_5160 = (subst_exp' s a)
in Microsoft_FStar_Absyn_Syntax.DECREASES (_52_5160))
end
| f -> begin
f
end)))))
and subst_comp_typ' = (fun ( s ) ( t ) -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _ -> begin
(let _23_376 = t
in (let _52_5170 = (subst_typ' s t.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _52_5169 = (Support.List.map (fun ( _23_8 ) -> (match (_23_8) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _52_5165 = (let _52_5164 = (subst_typ' s t)
in Support.Microsoft.FStar.Util.Inl (_52_5164))
in (_52_5165, imp))
end
| (Support.Microsoft.FStar.Util.Inr (e), imp) -> begin
(let _52_5167 = (let _52_5166 = (subst_exp' s e)
in Support.Microsoft.FStar.Util.Inr (_52_5166))
in (_52_5167, imp))
end)) t.Microsoft_FStar_Absyn_Syntax.effect_args)
in (let _52_5168 = (subst_flags' s t.Microsoft_FStar_Absyn_Syntax.flags)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _23_376.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _52_5170; Microsoft_FStar_Absyn_Syntax.effect_args = _52_5169; Microsoft_FStar_Absyn_Syntax.flags = _52_5168}))))
end))
and subst_comp' = (fun ( s ) ( t ) -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _ -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _52_5173 = (subst_typ' s t)
in (Microsoft_FStar_Absyn_Syntax.mk_Total _52_5173))
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _52_5174 = (subst_comp_typ' s ct)
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _52_5174))
end)
end))
and compose_subst = (fun ( s1 ) ( s2 ) -> (Support.List.append s1 s2))

let mk_subst = (fun ( s ) -> (s)::[])

let subst_kind = (fun ( s ) ( t ) -> (subst_kind' (mk_subst s) t))

let subst_typ = (fun ( s ) ( t ) -> (subst_typ' (mk_subst s) t))

let subst_exp = (fun ( s ) ( t ) -> (subst_exp' (mk_subst s) t))

let subst_flags = (fun ( s ) ( t ) -> (subst_flags' (mk_subst s) t))

let subst_comp = (fun ( s ) ( t ) -> (subst_comp' (mk_subst s) t))

let subst_binder = (fun ( s ) ( _23_9 ) -> (match (_23_9) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _52_5202 = (let _52_5201 = (let _23_417 = a
in (let _52_5200 = (subst_kind s a.Microsoft_FStar_Absyn_Syntax.sort)
in {Microsoft_FStar_Absyn_Syntax.v = _23_417.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _52_5200; Microsoft_FStar_Absyn_Syntax.p = _23_417.Microsoft_FStar_Absyn_Syntax.p}))
in Support.Microsoft.FStar.Util.Inl (_52_5201))
in (_52_5202, imp))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _52_5205 = (let _52_5204 = (let _23_423 = x
in (let _52_5203 = (subst_typ s x.Microsoft_FStar_Absyn_Syntax.sort)
in {Microsoft_FStar_Absyn_Syntax.v = _23_423.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _52_5203; Microsoft_FStar_Absyn_Syntax.p = _23_423.Microsoft_FStar_Absyn_Syntax.p}))
in Support.Microsoft.FStar.Util.Inr (_52_5204))
in (_52_5205, imp))
end))

let subst_arg = (fun ( s ) ( _23_10 ) -> (match (_23_10) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _52_5209 = (let _52_5208 = (subst_typ s t)
in Support.Microsoft.FStar.Util.Inl (_52_5208))
in (_52_5209, imp))
end
| (Support.Microsoft.FStar.Util.Inr (e), imp) -> begin
(let _52_5211 = (let _52_5210 = (subst_exp s e)
in Support.Microsoft.FStar.Util.Inr (_52_5210))
in (_52_5211, imp))
end))

let subst_binders = (fun ( s ) ( bs ) -> (match (s) with
| [] -> begin
bs
end
| _ -> begin
(Support.List.map (subst_binder s) bs)
end))

let subst_args = (fun ( s ) ( args ) -> (match (s) with
| [] -> begin
args
end
| _ -> begin
(Support.List.map (subst_arg s) args)
end))

let subst_formal = (fun ( f ) ( a ) -> (match ((f, a)) with
| ((Support.Microsoft.FStar.Util.Inl (a), _), (Support.Microsoft.FStar.Util.Inl (t), _)) -> begin
Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t))
end
| ((Support.Microsoft.FStar.Util.Inr (x), _), (Support.Microsoft.FStar.Util.Inr (v), _)) -> begin
Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, v))
end
| _ -> begin
(failwith ("Ill-formed substitution"))
end))

let mk_subst_one_binder = (fun ( b1 ) ( b2 ) -> (match ((let _52_5225 = (Microsoft_FStar_Absyn_Syntax.is_null_binder b1)
in (let _52_5224 = (Microsoft_FStar_Absyn_Syntax.is_null_binder b2)
in (_52_5225 || _52_5224)))) with
| true -> begin
[]
end
| false -> begin
(match (((Support.Prims.fst b1), (Support.Prims.fst b2))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(match ((bvar_eq a b)) with
| true -> begin
[]
end
| false -> begin
(let _52_5228 = (let _52_5227 = (let _52_5226 = (btvar_to_typ a)
in (b.Microsoft_FStar_Absyn_Syntax.v, _52_5226))
in Support.Microsoft.FStar.Util.Inl (_52_5227))
in (_52_5228)::[])
end)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(match ((bvar_eq x y)) with
| true -> begin
[]
end
| false -> begin
(let _52_5231 = (let _52_5230 = (let _52_5229 = (bvar_to_exp x)
in (y.Microsoft_FStar_Absyn_Syntax.v, _52_5229))
in Support.Microsoft.FStar.Util.Inr (_52_5230))
in (_52_5231)::[])
end)
end
| _ -> begin
[]
end)
end))

let mk_subst_binder = (fun ( bs1 ) ( bs2 ) -> (let rec aux = (fun ( out ) ( bs1 ) ( bs2 ) -> (match ((bs1, bs2)) with
| ([], []) -> begin
Some (out)
end
| (b1::bs1, b2::bs2) -> begin
(let _52_5243 = (let _52_5242 = (mk_subst_one_binder b1 b2)
in (Support.List.append _52_5242 out))
in (aux _52_5243 bs1 bs2))
end
| _ -> begin
None
end))
in (aux [] bs1 bs2)))

let subst_of_list = (fun ( formals ) ( actuals ) -> (match (((Support.List.length formals) = (Support.List.length actuals))) with
| true -> begin
(Support.List.map2 subst_formal formals actuals)
end
| false -> begin
(failwith ("Ill-formed substitution"))
end))

type red_ctrl =
{stop_if_empty_subst : bool; descend : bool}

let is_Mkred_ctrl = (fun ( _ ) -> (failwith ("Not yet implemented")))

let alpha_ctrl = {stop_if_empty_subst = false; descend = true}

let subst_ctrl = {stop_if_empty_subst = true; descend = true}

let null_ctrl = {stop_if_empty_subst = true; descend = false}

let extend_subst = (fun ( e ) ( s ) -> (Support.List.append (((mk_subst e))::[]) s))

let map_knd = (fun ( s ) ( vk ) ( mt ) ( me ) ( descend ) ( binders ) ( k ) -> (let _52_5264 = (subst_kind' s k)
in (_52_5264, descend)))

let map_typ = (fun ( s ) ( mk ) ( vt ) ( me ) ( descend ) ( binders ) ( t ) -> (let _52_5272 = (subst_typ' s t)
in (_52_5272, descend)))

let map_exp = (fun ( s ) ( mk ) ( me ) ( ve ) ( descend ) ( binders ) ( e ) -> (let _52_5280 = (subst_exp' s e)
in (_52_5280, descend)))

let map_flags = (fun ( s ) ( map_exp ) ( descend ) ( binders ) ( flags ) -> (Support.Prims.pipe_right flags (Support.List.map (fun ( _23_11 ) -> (match (_23_11) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _52_5297 = (let _52_5296 = (map_exp descend binders e)
in (Support.Prims.pipe_right _52_5296 Support.Prims.fst))
in Microsoft_FStar_Absyn_Syntax.DECREASES (_52_5297))
end
| f -> begin
f
end)))))

let map_comp = (fun ( s ) ( mk ) ( map_typ ) ( map_exp ) ( descend ) ( binders ) ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _23_551 = (map_typ descend binders t)
in (match (_23_551) with
| (t, descend) -> begin
(let _52_5320 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (_52_5320, descend))
end))
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _23_556 = (map_typ descend binders ct.Microsoft_FStar_Absyn_Syntax.result_typ)
in (match (_23_556) with
| (t, descend) -> begin
(let _23_559 = (Microsoft_FStar_Absyn_Visit.map_args map_typ map_exp descend binders ct.Microsoft_FStar_Absyn_Syntax.effect_args)
in (match (_23_559) with
| (args, descend) -> begin
(let _52_5323 = (let _52_5322 = (let _23_560 = ct
in (let _52_5321 = (map_flags s map_exp descend binders ct.Microsoft_FStar_Absyn_Syntax.flags)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _23_560.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = args; Microsoft_FStar_Absyn_Syntax.flags = _52_5321}))
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _52_5322))
in (_52_5323, descend))
end))
end))
end))

let visit_knd = (fun ( s ) ( vk ) ( mt ) ( me ) ( ctrl ) ( binders ) ( k ) -> (let k = (Microsoft_FStar_Absyn_Visit.compress_kind k)
in (match (ctrl.descend) with
| true -> begin
(let _23_573 = (vk null_ctrl binders k)
in (match (_23_573) with
| (k, _) -> begin
(k, ctrl)
end))
end
| false -> begin
(map_knd s vk mt me null_ctrl binders k)
end)))

let rec compress_kind = (fun ( k ) -> (let k = (Microsoft_FStar_Absyn_Visit.compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_delayed ((k', s, m)) -> begin
(let k' = (let _52_5369 = (Microsoft_FStar_Absyn_Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) Microsoft_FStar_Absyn_Visit.combine_kind Microsoft_FStar_Absyn_Visit.combine_typ Microsoft_FStar_Absyn_Visit.combine_exp subst_ctrl [] k')
in (Support.Prims.pipe_left Support.Prims.fst _52_5369))
in (let k' = (compress_kind k')
in (let _23_583 = (Support.ST.op_Colon_Equals m (Some (k')))
in k')))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, actuals)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (k) -> begin
(match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam ((formals, k')) -> begin
(let _52_5371 = (let _52_5370 = (subst_of_list formals actuals)
in (subst_kind _52_5370 k'))
in (compress_kind _52_5371))
end
| _ -> begin
(match (((Support.List.length actuals) = 0)) with
| true -> begin
k
end
| false -> begin
(failwith ("Wrong arity for kind unifier"))
end)
end)
end
| _ -> begin
k
end)
end
| _ -> begin
k
end)))

let rec visit_typ = (fun ( s ) ( mk ) ( vt ) ( me ) ( ctrl ) ( boundvars ) ( t ) -> (let visit_prod = (fun ( bs ) ( tc ) -> (let _23_661 = (Support.Prims.pipe_right bs (Support.List.fold_left (fun ( _23_614 ) ( b ) -> (match (_23_614) with
| (bs, boundvars, s) -> begin
(match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _23_623 = (map_knd s mk vt me null_ctrl boundvars a.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_23_623) with
| (k, _) -> begin
(let a = (let _23_624 = a
in {Microsoft_FStar_Absyn_Syntax.v = _23_624.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _23_624.Microsoft_FStar_Absyn_Syntax.p})
in (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
(((Support.Microsoft.FStar.Util.Inl (a), imp))::bs, boundvars, s)
end
| false -> begin
(let boundvars' = (Support.Microsoft.FStar.Util.Inl (a.Microsoft_FStar_Absyn_Syntax.v))::boundvars
in (let _23_636 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(Support.Microsoft.FStar.Util.Inl (a), s, boundvars')
end
| _ -> begin
(let b = (let _52_5448 = (freshen_bvd a.Microsoft_FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _52_5448 k))
in (let s = (let _52_5451 = (let _52_5450 = (let _52_5449 = (btvar_to_typ b)
in (a.Microsoft_FStar_Absyn_Syntax.v, _52_5449))
in Support.Microsoft.FStar.Util.Inl (_52_5450))
in (extend_subst _52_5451 s))
in (Support.Microsoft.FStar.Util.Inl (b), s, (Support.Microsoft.FStar.Util.Inl (b.Microsoft_FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_23_636) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end))
end))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _23_644 = (map_typ s mk vt me null_ctrl boundvars x.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_23_644) with
| (t, _) -> begin
(let x = (let _23_645 = x
in {Microsoft_FStar_Absyn_Syntax.v = _23_645.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _23_645.Microsoft_FStar_Absyn_Syntax.p})
in (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
(((Support.Microsoft.FStar.Util.Inr (x), imp))::bs, boundvars, s)
end
| false -> begin
(let boundvars' = (Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.v))::boundvars
in (let _23_657 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(Support.Microsoft.FStar.Util.Inr (x), s, boundvars')
end
| _ -> begin
(let y = (let _52_5461 = (freshen_bvd x.Microsoft_FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _52_5461 t))
in (let s = (let _52_5464 = (let _52_5463 = (let _52_5462 = (bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _52_5462))
in Support.Microsoft.FStar.Util.Inr (_52_5463))
in (extend_subst _52_5464 s))
in (Support.Microsoft.FStar.Util.Inr (y), s, (Support.Microsoft.FStar.Util.Inr (y.Microsoft_FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_23_657) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end))
end))
end)
end)) ([], boundvars, s)))
in (match (_23_661) with
| (bs, boundvars, s) -> begin
(let tc = (match ((s, tc)) with
| ([], _) -> begin
tc
end
| (_, Support.Microsoft.FStar.Util.Inl (t)) -> begin
(let _52_5475 = (let _52_5474 = (map_typ s mk vt me null_ctrl boundvars t)
in (Support.Prims.pipe_left Support.Prims.fst _52_5474))
in Support.Microsoft.FStar.Util.Inl (_52_5475))
end
| (_, Support.Microsoft.FStar.Util.Inr (c)) -> begin
(let _52_5498 = (let _52_5497 = (map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl boundvars c)
in (Support.Prims.pipe_left Support.Prims.fst _52_5497))
in Support.Microsoft.FStar.Util.Inr (_52_5498))
end)
in ((Support.List.rev bs), tc))
end)))
in (let t0 = t
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (_) -> begin
(let _52_5500 = (let _52_5499 = (subst_typ' s t0)
in (Support.Prims.pipe_left compress_typ _52_5499))
in (_52_5500, ctrl))
end
| _ when (not (ctrl.descend)) -> begin
(map_typ s mk vt me null_ctrl boundvars t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(match ((visit_prod bs (Support.Microsoft.FStar.Util.Inr (c)))) with
| (bs, Support.Microsoft.FStar.Util.Inr (c)) -> begin
(let _52_5510 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t0.Microsoft_FStar_Absyn_Syntax.pos)
in (_52_5510, ctrl))
end
| _ -> begin
(failwith ("Impossible"))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, t)) -> begin
(match ((visit_prod (((Support.Microsoft.FStar.Util.Inr (x), None))::[]) (Support.Microsoft.FStar.Util.Inl (t)))) with
| ((Support.Microsoft.FStar.Util.Inr (x), _)::[], Support.Microsoft.FStar.Util.Inl (t)) -> begin
(let _52_5511 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, t) None t0.Microsoft_FStar_Absyn_Syntax.pos)
in (_52_5511, ctrl))
end
| _ -> begin
(failwith ("Impossible"))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(match ((visit_prod bs (Support.Microsoft.FStar.Util.Inl (t)))) with
| (bs, Support.Microsoft.FStar.Util.Inl (t)) -> begin
(let _52_5512 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t0.Microsoft_FStar_Absyn_Syntax.pos)
in (_52_5512, ctrl))
end
| _ -> begin
(failwith ("Impossible"))
end)
end
| _ -> begin
(let _23_723 = (vt null_ctrl boundvars t)
in (match (_23_723) with
| (t, _) -> begin
(t, ctrl)
end))
end))))
and compress_typ' = (fun ( t ) -> (let t = (Microsoft_FStar_Absyn_Visit.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((Support.Microsoft.FStar.Util.Inl ((t', s)), m)) -> begin
(let res = (let _52_5532 = (Microsoft_FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) Microsoft_FStar_Absyn_Visit.combine_kind Microsoft_FStar_Absyn_Visit.combine_typ Microsoft_FStar_Absyn_Visit.combine_exp subst_ctrl [] t')
in (Support.Prims.pipe_left Support.Prims.fst _52_5532))
in (let res = (compress_typ' res)
in (let _23_735 = (Support.ST.op_Colon_Equals m (Some (res)))
in res)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((Support.Microsoft.FStar.Util.Inr (mk_t), m)) -> begin
(let t = (let _52_5534 = (mk_t ())
in (compress_typ' _52_5534))
in (let _23_743 = (Support.ST.op_Colon_Equals m (Some (t)))
in t))
end
| _ -> begin
t
end)))
and compress_typ = (fun ( t ) -> (let t = (compress_typ' t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_) -> begin
(failwith ("Impossible: compress returned a delayed type"))
end
| _ -> begin
t
end)))

let rec visit_exp = (fun ( s ) ( mk ) ( me ) ( ve ) ( ctrl ) ( binders ) ( e ) -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (_) -> begin
(let _52_5597 = (let _52_5596 = (subst_exp' s e)
in (Support.Prims.pipe_left compress_exp _52_5596))
in (_52_5597, ctrl))
end
| _ when (not (ctrl.descend)) -> begin
(map_exp s mk me ve ctrl binders e)
end
| _ -> begin
(let _23_772 = (ve null_ctrl binders e)
in (match (_23_772) with
| (e, _) -> begin
(e, ctrl)
end))
end)))
and compress_exp = (fun ( e ) -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed ((e', s, m)) -> begin
(let e = (let _52_5626 = (Microsoft_FStar_Absyn_Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) Microsoft_FStar_Absyn_Visit.combine_kind Microsoft_FStar_Absyn_Visit.combine_typ Microsoft_FStar_Absyn_Visit.combine_exp subst_ctrl [] e')
in (Support.Prims.pipe_left Support.Prims.fst _52_5626))
in (let res = (compress_exp e)
in (let _23_782 = (Support.ST.op_Colon_Equals m (Some (res)))
in res)))
end
| _ -> begin
e
end)))

let rec unmeta_exp = (fun ( e ) -> (let e = (compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(unmeta_exp e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _, _)) -> begin
(unmeta_exp e)
end
| _ -> begin
e
end)))

let alpha_typ = (fun ( t ) -> (let t = (compress_typ t)
in (let s = (mk_subst [])
in (let doit = (fun ( t ) -> (let _52_5651 = (Microsoft_FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) Microsoft_FStar_Absyn_Visit.combine_kind Microsoft_FStar_Absyn_Visit.combine_typ Microsoft_FStar_Absyn_Visit.combine_exp alpha_ctrl [] t)
in (Support.Prims.pipe_left Support.Prims.fst _52_5651)))
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, _))) -> begin
(match ((Support.Microsoft.FStar.Util.for_all Microsoft_FStar_Absyn_Syntax.is_null_binder bs)) with
| true -> begin
t
end
| false -> begin
(doit t)
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_) -> begin
(doit t)
end
| _ -> begin
t
end)))))

let formals_for_actuals = (fun ( formals ) ( actuals ) -> (Support.List.map2 (fun ( formal ) ( actual ) -> (match (((Support.Prims.fst formal), (Support.Prims.fst actual))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, b))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, y))
end
| _ -> begin
(failwith ("Ill-typed substitution"))
end)) formals actuals))

let compress_typ_opt = (fun ( _23_12 ) -> (match (_23_12) with
| None -> begin
None
end
| Some (t) -> begin
(let _52_5658 = (compress_typ t)
in Some (_52_5658))
end))

let mk_discriminator = (fun ( lid ) -> (let _52_5663 = (let _52_5662 = (let _52_5661 = (Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.String.strcat "is_" lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText), lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idRange))
in (_52_5661)::[])
in (Support.List.append lid.Microsoft_FStar_Absyn_Syntax.ns _52_5662))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _52_5663)))

let is_name = (fun ( lid ) -> (let c = (Support.Microsoft.FStar.Util.char_at lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText 0)
in (Support.Microsoft.FStar.Util.is_upper c)))

let ml_comp = (fun ( t ) ( r ) -> (let _52_5671 = (let _52_5670 = (set_lid_range Microsoft_FStar_Absyn_Const.effect_ML_lid r)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _52_5670; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = []; Microsoft_FStar_Absyn_Syntax.flags = (Microsoft_FStar_Absyn_Syntax.MLEFFECT)::[]})
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _52_5671)))

let total_comp = (fun ( t ) ( r ) -> (Microsoft_FStar_Absyn_Syntax.mk_Total t))

let gtotal_comp = (fun ( t ) -> (Microsoft_FStar_Absyn_Syntax.mk_Comp {Microsoft_FStar_Absyn_Syntax.effect_name = Microsoft_FStar_Absyn_Const.effect_GTot_lid; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = []; Microsoft_FStar_Absyn_Syntax.flags = (Microsoft_FStar_Absyn_Syntax.SOMETRIVIAL)::[]}))

let comp_set_flags = (fun ( c ) ( f ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_) -> begin
c
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _23_857 = c
in {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp ((let _23_859 = ct
in {Microsoft_FStar_Absyn_Syntax.effect_name = _23_859.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _23_859.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _23_859.Microsoft_FStar_Absyn_Syntax.effect_args; Microsoft_FStar_Absyn_Syntax.flags = f})); Microsoft_FStar_Absyn_Syntax.tk = _23_857.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = _23_857.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _23_857.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _23_857.Microsoft_FStar_Absyn_Syntax.uvs})
end))

let comp_flags = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_) -> begin
(Microsoft_FStar_Absyn_Syntax.TOTAL)::[]
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
ct.Microsoft_FStar_Absyn_Syntax.flags
end))

let comp_effect_name = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
c.Microsoft_FStar_Absyn_Syntax.effect_name
end
| Microsoft_FStar_Absyn_Syntax.Total (_) -> begin
Microsoft_FStar_Absyn_Const.effect_Tot_lid
end))

let comp_to_comp_typ = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
c
end
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
{Microsoft_FStar_Absyn_Syntax.effect_name = Microsoft_FStar_Absyn_Const.effect_Tot_lid; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = []; Microsoft_FStar_Absyn_Syntax.flags = (Microsoft_FStar_Absyn_Syntax.TOTAL)::[]}
end))

let is_total_comp = (fun ( c ) -> (Support.Prims.pipe_right (comp_flags c) (Support.Microsoft.FStar.Util.for_some (fun ( _23_13 ) -> (match (_23_13) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _ -> begin
false
end)))))

let is_total_lcomp = (fun ( c ) -> (let _52_5689 = (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.cflags (Support.Microsoft.FStar.Util.for_some (fun ( _23_14 ) -> (match (_23_14) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _ -> begin
false
end))))
in ((Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_Tot_lid) || _52_5689)))

let is_partial_return = (fun ( c ) -> (Support.Prims.pipe_right (comp_flags c) (Support.Microsoft.FStar.Util.for_some (fun ( _23_15 ) -> (match (_23_15) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _ -> begin
false
end)))))

let is_lcomp_partial_return = (fun ( c ) -> (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.cflags (Support.Microsoft.FStar.Util.for_some (fun ( _23_16 ) -> (match (_23_16) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _ -> begin
false
end)))))

let is_tot_or_gtot_comp = (fun ( c ) -> (let _52_5696 = (is_total_comp c)
in (_52_5696 || (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.effect_GTot_lid (comp_effect_name c)))))

let is_pure_comp = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _52_5702 = (let _52_5699 = (let _52_5698 = (is_tot_or_gtot_comp c)
in (_52_5698 || (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_PURE_lid)))
in (_52_5699 || (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Pure_lid)))
in (let _52_5701 = (Support.Prims.pipe_right ct.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _23_17 ) -> (match (_23_17) with
| Microsoft_FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _ -> begin
false
end))))
in (_52_5702 || _52_5701)))
end))

let is_ghost_effect = (fun ( l ) -> (((Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.effect_GTot_lid l) || (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.effect_GHOST_lid l)) || (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.effect_Ghost_lid l)))

let is_pure_or_ghost_comp = (fun ( c ) -> (let _52_5706 = (is_pure_comp c)
in (_52_5706 || (is_ghost_effect (comp_effect_name c)))))

let is_pure_lcomp = (fun ( lc ) -> (let _52_5713 = (let _52_5710 = (let _52_5709 = (is_total_lcomp lc)
in (_52_5709 || (Microsoft_FStar_Absyn_Syntax.lid_equals lc.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_PURE_lid)))
in (_52_5710 || (Microsoft_FStar_Absyn_Syntax.lid_equals lc.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_Pure_lid)))
in (let _52_5712 = (Support.Prims.pipe_right lc.Microsoft_FStar_Absyn_Syntax.cflags (Support.Microsoft.FStar.Util.for_some (fun ( _23_18 ) -> (match (_23_18) with
| Microsoft_FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _ -> begin
false
end))))
in (_52_5713 || _52_5712))))

let is_pure_or_ghost_lcomp = (fun ( lc ) -> (let _52_5716 = (is_pure_lcomp lc)
in (_52_5716 || (is_ghost_effect lc.Microsoft_FStar_Absyn_Syntax.eff_name))))

let is_pure_or_ghost_function = (fun ( t ) -> (match ((let _52_5719 = (compress_typ t)
in _52_5719.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((_, c)) -> begin
(is_pure_or_ghost_comp c)
end
| _ -> begin
true
end))

let is_lemma = (fun ( t ) -> (match ((let _52_5722 = (compress_typ t)
in _52_5722.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((_, c)) -> begin
(match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Lemma_lid)
end
| _ -> begin
false
end)
end
| _ -> begin
false
end))

let is_smt_lemma = (fun ( t ) -> (match ((let _52_5725 = (compress_typ t)
in _52_5725.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((_, c)) -> begin
(match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (ct) when (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Lemma_lid) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| _req::_ens::(Support.Microsoft.FStar.Util.Inr (pats), _)::_ -> begin
(match ((let _52_5726 = (unmeta_exp pats)
in _52_5726.Microsoft_FStar_Absyn_Syntax.n)) with
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

let is_ml_comp = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
(let _52_5729 = (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _23_19 ) -> (match (_23_19) with
| Microsoft_FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _ -> begin
false
end))))
in ((Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_ML_lid) || _52_5729))
end
| _ -> begin
false
end))

let comp_result = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
ct.Microsoft_FStar_Absyn_Syntax.result_typ
end))

let set_result_typ = (fun ( c ) ( t ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total t)
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Comp (let _23_1008 = ct
in {Microsoft_FStar_Absyn_Syntax.effect_name = _23_1008.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = _23_1008.Microsoft_FStar_Absyn_Syntax.effect_args; Microsoft_FStar_Absyn_Syntax.flags = _23_1008.Microsoft_FStar_Absyn_Syntax.flags}))
end))

let is_trivial_wp = (fun ( c ) -> (Support.Prims.pipe_right (comp_flags c) (Support.Microsoft.FStar.Util.for_some (fun ( _23_20 ) -> (match (_23_20) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _ -> begin
false
end)))))

let rec is_atom = (fun ( e ) -> (match ((let _52_5737 = (compress_exp e)
in _52_5737.Microsoft_FStar_Absyn_Syntax.n)) with
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

let is_primop = (fun ( f ) -> (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)) -> begin
(Support.Prims.pipe_right primops (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v)))
end
| _ -> begin
false
end))

let rec unascribe = (fun ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _, _)) -> begin
(unascribe e)
end
| _ -> begin
e
end))

let rec ascribe_typ = (fun ( t ) ( k ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t', _)) -> begin
(ascribe_typ t' k)
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.Microsoft_FStar_Absyn_Syntax.pos)
end))

let rec unascribe_typ = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _)) -> begin
(unascribe_typ t)
end
| _ -> begin
t
end))

let rec unrefine = (fun ( t ) -> (let t = (compress_typ t)
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

let is_fun = (fun ( e ) -> (match ((let _52_5751 = (compress_exp e)
in _52_5751.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_abs (_) -> begin
true
end
| _ -> begin
false
end))

let is_function_typ = (fun ( t ) -> (match ((let _52_5754 = (compress_typ t)
in _52_5754.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_) -> begin
true
end
| _ -> begin
false
end))

let rec pre_typ = (fun ( t ) -> (let t = (compress_typ t)
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

let destruct = (fun ( typ ) ( lid ) -> (let typ = (compress_typ typ)
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

let rec lids_of_sigelt = (fun ( se ) -> (match (se) with
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

let lid_of_sigelt = (fun ( se ) -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _ -> begin
None
end))

let range_of_sigelt = (fun ( x ) -> (match (x) with
| (Microsoft_FStar_Absyn_Syntax.Sig_bundle ((_, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_, _, _, _, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((_, _, _, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((_, _, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_, _, _, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_assume ((_, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_let ((_, r, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_main ((_, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_pragma ((_, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((_, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((_, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect ((_, r))) -> begin
r
end))

let range_of_lb = (fun ( _23_21 ) -> (match (_23_21) with
| (Support.Microsoft.FStar.Util.Inl (x), _, _) -> begin
(range_of_bvd x)
end
| (Support.Microsoft.FStar.Util.Inr (l), _, _) -> begin
(Microsoft_FStar_Absyn_Syntax.range_of_lid l)
end))

let range_of_arg = (fun ( _23_22 ) -> (match (_23_22) with
| (Support.Microsoft.FStar.Util.Inl (hd), _) -> begin
hd.Microsoft_FStar_Absyn_Syntax.pos
end
| (Support.Microsoft.FStar.Util.Inr (hd), _) -> begin
hd.Microsoft_FStar_Absyn_Syntax.pos
end))

let range_of_args = (fun ( args ) ( r ) -> (Support.Prims.pipe_right args (Support.List.fold_left (fun ( r ) ( a ) -> (Support.Microsoft.FStar.Range.union_ranges r (range_of_arg a))) r)))

let mk_typ_app = (fun ( f ) ( args ) -> (let r = (range_of_args args f.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (f, args) None r)))

let mk_exp_app = (fun ( f ) ( args ) -> (let r = (range_of_args args f.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (f, args) None r)))

let mk_data = (fun ( l ) ( args ) -> (match (args) with
| [] -> begin
(let _52_5788 = (let _52_5787 = (let _52_5786 = (let _52_5785 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) l _52_5785))
in (_52_5786, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_52_5787))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _52_5788))
end
| _ -> begin
(let _52_5793 = (let _52_5792 = (let _52_5791 = (let _52_5790 = (let _52_5789 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) l _52_5789))
in (mk_exp_app _52_5790 args))
in (_52_5791, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_52_5792))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _52_5793))
end))

let mangle_field_name = (fun ( x ) -> (Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.String.strcat "^fname^" x.Microsoft_FStar_Absyn_Syntax.idText), x.Microsoft_FStar_Absyn_Syntax.idRange)))

let unmangle_field_name = (fun ( x ) -> (match ((Support.Microsoft.FStar.Util.starts_with x.Microsoft_FStar_Absyn_Syntax.idText "^fname^")) with
| true -> begin
(let _52_5799 = (let _52_5798 = (Support.Microsoft.FStar.Util.substring_from x.Microsoft_FStar_Absyn_Syntax.idText 7)
in (_52_5798, x.Microsoft_FStar_Absyn_Syntax.idRange))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _52_5799))
end
| false -> begin
x
end))

let mk_field_projector_name = (fun ( lid ) ( x ) ( i ) -> (let nm = (match ((Microsoft_FStar_Absyn_Syntax.is_null_bvar x)) with
| true -> begin
(let _52_5805 = (let _52_5804 = (let _52_5803 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.String.strcat "_" _52_5803))
in (_52_5804, x.Microsoft_FStar_Absyn_Syntax.p))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _52_5805))
end
| false -> begin
x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname
end)
in (let y = (let _23_1395 = x.Microsoft_FStar_Absyn_Syntax.v
in {Microsoft_FStar_Absyn_Syntax.ppname = nm; Microsoft_FStar_Absyn_Syntax.realname = _23_1395.Microsoft_FStar_Absyn_Syntax.realname})
in (let _52_5810 = (let _52_5809 = (let _52_5808 = (Microsoft_FStar_Absyn_Syntax.ids_of_lid lid)
in (let _52_5807 = (let _52_5806 = (unmangle_field_name nm)
in (_52_5806)::[])
in (Support.List.append _52_5808 _52_5807)))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _52_5809))
in (_52_5810, y)))))

let unchecked_unify = (fun ( uv ) ( t ) -> (match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (_) -> begin
(let _52_5815 = (let _52_5814 = (let _52_5813 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_int _52_5813))
in (Support.Microsoft.FStar.Util.format1 "Changing a fixed uvar! U%s\n" _52_5814))
in (failwith (_52_5815)))
end
| _ -> begin
(Support.Microsoft.FStar.Unionfind.change uv (Microsoft_FStar_Absyn_Syntax.Fixed (t)))
end))

type bvars =
(Microsoft_FStar_Absyn_Syntax.btvar Support.Microsoft.FStar.Util.set * Microsoft_FStar_Absyn_Syntax.bvvar Support.Microsoft.FStar.Util.set)

let no_bvars = (Microsoft_FStar_Absyn_Syntax.no_fvs.Microsoft_FStar_Absyn_Syntax.ftvs, Microsoft_FStar_Absyn_Syntax.no_fvs.Microsoft_FStar_Absyn_Syntax.fxvs)

let fvs_included = (fun ( fvs1 ) ( fvs2 ) -> (let _52_5833 = (Support.Microsoft.FStar.Util.set_is_subset_of fvs1.Microsoft_FStar_Absyn_Syntax.ftvs fvs2.Microsoft_FStar_Absyn_Syntax.ftvs)
in (let _52_5832 = (Support.Microsoft.FStar.Util.set_is_subset_of fvs1.Microsoft_FStar_Absyn_Syntax.fxvs fvs2.Microsoft_FStar_Absyn_Syntax.fxvs)
in (_52_5833 && _52_5832))))

let eq_fvars = (fun ( v1 ) ( v2 ) -> (match ((v1, v2)) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq a b)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| _ -> begin
false
end))

let eq_binder = (fun ( b1 ) ( b2 ) -> (match (((Support.Prims.fst b1), (Support.Prims.fst b2))) with
| (Support.Microsoft.FStar.Util.Inl (x), Support.Microsoft.FStar.Util.Inl (y)) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| _ -> begin
false
end))

let uv_eq = (fun ( _23_1438 ) ( _23_1442 ) -> (match ((_23_1438, _23_1442)) with
| ((uv1, _), (uv2, _)) -> begin
(Support.Microsoft.FStar.Unionfind.equivalent uv1 uv2)
end))

let union_uvs = (fun ( uvs1 ) ( uvs2 ) -> (let _52_5846 = (Support.Microsoft.FStar.Util.set_union uvs1.Microsoft_FStar_Absyn_Syntax.uvars_k uvs2.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (let _52_5845 = (Support.Microsoft.FStar.Util.set_union uvs1.Microsoft_FStar_Absyn_Syntax.uvars_t uvs2.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (let _52_5844 = (Support.Microsoft.FStar.Util.set_union uvs1.Microsoft_FStar_Absyn_Syntax.uvars_e uvs2.Microsoft_FStar_Absyn_Syntax.uvars_e)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _52_5846; Microsoft_FStar_Absyn_Syntax.uvars_t = _52_5845; Microsoft_FStar_Absyn_Syntax.uvars_e = _52_5844}))))

let union_fvs = (fun ( fvs1 ) ( fvs2 ) -> (let _52_5852 = (Support.Microsoft.FStar.Util.set_union fvs1.Microsoft_FStar_Absyn_Syntax.ftvs fvs2.Microsoft_FStar_Absyn_Syntax.ftvs)
in (let _52_5851 = (Support.Microsoft.FStar.Util.set_union fvs1.Microsoft_FStar_Absyn_Syntax.fxvs fvs2.Microsoft_FStar_Absyn_Syntax.fxvs)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _52_5852; Microsoft_FStar_Absyn_Syntax.fxvs = _52_5851})))

let union_fvs_uvs = (fun ( _23_1449 ) ( _23_1452 ) -> (match ((_23_1449, _23_1452)) with
| ((fvs1, uvs1), (fvs2, uvs2)) -> begin
(let _52_5858 = (union_fvs fvs1 fvs2)
in (let _52_5857 = (union_uvs uvs1 uvs2)
in (_52_5858, _52_5857)))
end))

let sub_fv = (fun ( _23_1455 ) ( _23_1458 ) -> (match ((_23_1455, _23_1458)) with
| ((fvs, uvs), (tvars, vvars)) -> begin
(let _52_5879 = (let _23_1459 = fvs
in (let _52_5878 = (Support.Microsoft.FStar.Util.set_difference fvs.Microsoft_FStar_Absyn_Syntax.ftvs tvars)
in (let _52_5877 = (Support.Microsoft.FStar.Util.set_difference fvs.Microsoft_FStar_Absyn_Syntax.fxvs vvars)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _52_5878; Microsoft_FStar_Absyn_Syntax.fxvs = _52_5877})))
in (_52_5879, uvs))
end))

let stash = (fun ( uvonly ) ( s ) ( _23_1467 ) -> (match (_23_1467) with
| (fvs, uvs) -> begin
(let _23_1468 = (Support.ST.op_Colon_Equals s.Microsoft_FStar_Absyn_Syntax.uvs (Some (uvs)))
in (match (uvonly) with
| true -> begin
()
end
| false -> begin
(Support.ST.op_Colon_Equals s.Microsoft_FStar_Absyn_Syntax.fvs (Some (fvs)))
end))
end))

let single_fv = (fun ( x ) -> (let _52_5890 = (Microsoft_FStar_Absyn_Syntax.new_ftv_set ())
in (Support.Microsoft.FStar.Util.set_add x _52_5890)))

let single_uv = (fun ( u ) -> (let _52_5898 = (Microsoft_FStar_Absyn_Syntax.new_uv_set ())
in (Support.Microsoft.FStar.Util.set_add u _52_5898)))

let single_uvt = (fun ( u ) -> (let _52_5906 = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ())
in (Support.Microsoft.FStar.Util.set_add u _52_5906)))

let rec vs_typ' = (fun ( t ) ( uvonly ) ( cont ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| false -> begin
(let _52_6018 = (let _52_6017 = (let _23_1483 = Microsoft_FStar_Absyn_Syntax.no_fvs
in (let _52_6016 = (single_fv a)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _52_6016; Microsoft_FStar_Absyn_Syntax.fxvs = _23_1483.Microsoft_FStar_Absyn_Syntax.fxvs}))
in (_52_6017, Microsoft_FStar_Absyn_Syntax.no_uvs))
in (cont _52_6018))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(let _52_6021 = (let _52_6020 = (let _23_1489 = Microsoft_FStar_Absyn_Syntax.no_uvs
in (let _52_6019 = (single_uvt (uv, k))
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _23_1489.Microsoft_FStar_Absyn_Syntax.uvars_k; Microsoft_FStar_Absyn_Syntax.uvars_t = _52_6019; Microsoft_FStar_Absyn_Syntax.uvars_e = _23_1489.Microsoft_FStar_Absyn_Syntax.uvars_e}))
in (Microsoft_FStar_Absyn_Syntax.no_fvs, _52_6020))
in (cont _52_6021))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(vs_binders bs uvonly (fun ( _23_1501 ) -> (match (_23_1501) with
| (bvs, vs1) -> begin
(vs_comp c uvonly (fun ( vs2 ) -> (let _52_6025 = (let _52_6024 = (union_fvs_uvs vs1 vs2)
in (sub_fv _52_6024 bvs))
in (cont _52_6025))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(vs_binders bs uvonly (fun ( _23_1509 ) -> (match (_23_1509) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun ( vs2 ) -> (let _52_6029 = (let _52_6028 = (union_fvs_uvs vs1 vs2)
in (sub_fv _52_6028 bvs))
in (cont _52_6029))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, t)) -> begin
(vs_binders (((Support.Microsoft.FStar.Util.Inr (x), None))::[]) uvonly (fun ( _23_1517 ) -> (match (_23_1517) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun ( vs2 ) -> (let _52_6033 = (let _52_6032 = (union_fvs_uvs vs1 vs2)
in (sub_fv _52_6032 bvs))
in (cont _52_6033))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, args)) -> begin
(vs_typ t uvonly (fun ( vs1 ) -> (vs_args args uvonly (fun ( vs2 ) -> (let _52_6036 = (union_fvs_uvs vs1 vs2)
in (cont _52_6036))))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _)) -> begin
(vs_typ t uvonly cont)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, _))) -> begin
(vs_typ t1 uvonly (fun ( vs1 ) -> (vs_typ t2 uvonly (fun ( vs2 ) -> (let _52_6039 = (union_fvs_uvs vs1 vs2)
in (cont _52_6039))))))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, _, _, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, _)))) -> begin
(vs_typ t uvonly cont)
end)))
and vs_binders = (fun ( bs ) ( uvonly ) ( cont ) -> (match (bs) with
| [] -> begin
(cont (no_bvars, (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs)))
end
| (Support.Microsoft.FStar.Util.Inl (a), _)::rest -> begin
(vs_kind a.Microsoft_FStar_Absyn_Syntax.sort uvonly (fun ( vs ) -> (vs_binders rest uvonly (fun ( _23_1583 ) -> (match (_23_1583) with
| ((tvars, vvars), vs2) -> begin
(let _52_6076 = (let _52_6075 = (let _52_6073 = (Support.Microsoft.FStar.Util.set_add a tvars)
in (_52_6073, vvars))
in (let _52_6074 = (union_fvs_uvs vs vs2)
in (_52_6075, _52_6074)))
in (cont _52_6076))
end)))))
end
| (Support.Microsoft.FStar.Util.Inr (x), _)::rest -> begin
(vs_typ x.Microsoft_FStar_Absyn_Syntax.sort uvonly (fun ( vs ) -> (vs_binders rest uvonly (fun ( _23_1596 ) -> (match (_23_1596) with
| ((tvars, vvars), vs2) -> begin
(let _52_6100 = (let _52_6099 = (let _52_6097 = (Support.Microsoft.FStar.Util.set_add x vvars)
in (tvars, _52_6097))
in (let _52_6098 = (union_fvs_uvs vs vs2)
in (_52_6099, _52_6098)))
in (cont _52_6100))
end)))))
end))
and vs_args = (fun ( args ) ( uvonly ) ( cont ) -> (match (args) with
| [] -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| (Support.Microsoft.FStar.Util.Inl (t), _)::tl -> begin
(vs_typ t uvonly (fun ( ft1 ) -> (vs_args tl uvonly (fun ( ft2 ) -> (let _52_6104 = (union_fvs_uvs ft1 ft2)
in (cont _52_6104))))))
end
| (Support.Microsoft.FStar.Util.Inr (e), _)::tl -> begin
(vs_exp e uvonly (fun ( ft1 ) -> (vs_args tl uvonly (fun ( ft2 ) -> (let _52_6107 = (union_fvs_uvs ft1 ft2)
in (cont _52_6107))))))
end))
and vs_typ = (fun ( t ) ( uvonly ) ( cont ) -> (match ((let _52_6110 = (Support.ST.read t.Microsoft_FStar_Absyn_Syntax.fvs)
in (let _52_6109 = (Support.ST.read t.Microsoft_FStar_Absyn_Syntax.uvs)
in (_52_6110, _52_6109)))) with
| (Some (_), None) -> begin
(failwith ("Impossible"))
end
| (None, None) -> begin
(vs_typ' t uvonly (fun ( fvs ) -> (let _23_1633 = (stash uvonly t fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, uvs))
end
| false -> begin
(vs_typ' t uvonly (fun ( fvs ) -> (let _23_1640 = (stash uvonly t fvs)
in (cont fvs))))
end)
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_kind' = (fun ( k ) ( uvonly ) ( cont ) -> (let k = (compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam ((_, k)) -> begin
(let _52_6115 = (let _52_6114 = (Support.Microsoft.FStar.Range.string_of_range k.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Microsoft.FStar.Util.format1 "%s: Impossible ... found a Kind_lam bare" _52_6114))
in (failwith (_52_6115)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_) -> begin
(failwith ("Impossible"))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_unknown) | (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, args)) -> begin
(vs_args args uvonly (fun ( _23_1669 ) -> (match (_23_1669) with
| (fvs, uvs) -> begin
(let _52_6119 = (let _52_6118 = (let _23_1670 = uvs
in (let _52_6117 = (Support.Microsoft.FStar.Util.set_add uv uvs.Microsoft_FStar_Absyn_Syntax.uvars_k)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _52_6117; Microsoft_FStar_Absyn_Syntax.uvars_t = _23_1670.Microsoft_FStar_Absyn_Syntax.uvars_t; Microsoft_FStar_Absyn_Syntax.uvars_e = _23_1670.Microsoft_FStar_Absyn_Syntax.uvars_e}))
in (fvs, _52_6118))
in (cont _52_6119))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(vs_kind k uvonly cont)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(vs_binders bs uvonly (fun ( _23_1683 ) -> (match (_23_1683) with
| (bvs, vs1) -> begin
(vs_kind k uvonly (fun ( vs2 ) -> (let _52_6123 = (let _52_6122 = (union_fvs_uvs vs1 vs2)
in (sub_fv _52_6122 bvs))
in (cont _52_6123))))
end)))
end)))
and vs_kind = (fun ( k ) ( uvonly ) ( cont ) -> (match ((let _52_6126 = (Support.ST.read k.Microsoft_FStar_Absyn_Syntax.fvs)
in (let _52_6125 = (Support.ST.read k.Microsoft_FStar_Absyn_Syntax.uvs)
in (_52_6126, _52_6125)))) with
| (Some (_), None) -> begin
(failwith ("Impossible"))
end
| (None, None) -> begin
(vs_kind' k uvonly (fun ( fvs ) -> (let _23_1698 = (stash uvonly k fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, uvs))
end
| false -> begin
(vs_kind' k uvonly (fun ( fvs ) -> (let _23_1705 = (stash uvonly k fvs)
in (cont fvs))))
end)
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_exp' = (fun ( e ) ( uvonly ) ( cont ) -> (let e = (compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_) -> begin
(failwith ("impossible"))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, t)) -> begin
(let _52_6132 = (let _52_6131 = (let _23_1730 = Microsoft_FStar_Absyn_Syntax.no_uvs
in (let _52_6130 = (single_uvt (uv, t))
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _23_1730.Microsoft_FStar_Absyn_Syntax.uvars_k; Microsoft_FStar_Absyn_Syntax.uvars_t = _23_1730.Microsoft_FStar_Absyn_Syntax.uvars_t; Microsoft_FStar_Absyn_Syntax.uvars_e = _52_6130}))
in (Microsoft_FStar_Absyn_Syntax.no_fvs, _52_6131))
in (cont _52_6132))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| false -> begin
(let _52_6135 = (let _52_6134 = (let _23_1734 = Microsoft_FStar_Absyn_Syntax.no_fvs
in (let _52_6133 = (single_fv x)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _23_1734.Microsoft_FStar_Absyn_Syntax.ftvs; Microsoft_FStar_Absyn_Syntax.fxvs = _52_6133}))
in (_52_6134, Microsoft_FStar_Absyn_Syntax.no_uvs))
in (cont _52_6135))
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _, _)) -> begin
(vs_exp e uvonly cont)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, e)) -> begin
(vs_binders bs uvonly (fun ( _23_1749 ) -> (match (_23_1749) with
| (bvs, vs1) -> begin
(vs_exp e uvonly (fun ( vs2 ) -> (let _52_6139 = (let _52_6138 = (union_fvs_uvs vs1 vs2)
in (sub_fv _52_6138 bvs))
in (cont _52_6139))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((e, args)) -> begin
(vs_exp e uvonly (fun ( ft1 ) -> (vs_args args uvonly (fun ( ft2 ) -> (let _52_6142 = (union_fvs_uvs ft1 ft2)
in (cont _52_6142))))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_match (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_let (_)) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(vs_exp e uvonly cont)
end)))
and vs_exp = (fun ( e ) ( uvonly ) ( cont ) -> (match ((let _52_6145 = (Support.ST.read e.Microsoft_FStar_Absyn_Syntax.fvs)
in (let _52_6144 = (Support.ST.read e.Microsoft_FStar_Absyn_Syntax.uvs)
in (_52_6145, _52_6144)))) with
| (Some (_), None) -> begin
(failwith ("Impossible"))
end
| (None, None) -> begin
(vs_exp' e uvonly (fun ( fvs ) -> (let _23_1782 = (stash uvonly e fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, uvs))
end
| false -> begin
(vs_exp' e uvonly (fun ( fvs ) -> (let _23_1789 = (stash uvonly e fvs)
in (cont fvs))))
end)
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_comp' = (fun ( c ) ( uvonly ) ( k ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(vs_typ t uvonly k)
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(match (uvonly) with
| true -> begin
(vs_typ ct.Microsoft_FStar_Absyn_Syntax.result_typ uvonly k)
end
| false -> begin
(vs_typ ct.Microsoft_FStar_Absyn_Syntax.result_typ uvonly (fun ( vs1 ) -> (vs_args ct.Microsoft_FStar_Absyn_Syntax.effect_args uvonly (fun ( vs2 ) -> (let _52_6151 = (union_fvs_uvs vs1 vs2)
in (k _52_6151))))))
end)
end))
and vs_comp = (fun ( c ) ( uvonly ) ( cont ) -> (match ((let _52_6154 = (Support.ST.read c.Microsoft_FStar_Absyn_Syntax.fvs)
in (let _52_6153 = (Support.ST.read c.Microsoft_FStar_Absyn_Syntax.uvs)
in (_52_6154, _52_6153)))) with
| (Some (_), None) -> begin
(failwith ("Impossible"))
end
| (None, None) -> begin
(vs_comp' c uvonly (fun ( fvs ) -> (let _23_1819 = (stash uvonly c fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, uvs))
end
| false -> begin
(vs_comp' c uvonly (fun ( fvs ) -> (let _23_1826 = (stash uvonly c fvs)
in (cont fvs))))
end)
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_either = (fun ( te ) ( uvonly ) ( cont ) -> (match (te) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(vs_typ t uvonly cont)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(vs_exp e uvonly cont)
end))
and vs_either_l = (fun ( tes ) ( uvonly ) ( cont ) -> (match (tes) with
| [] -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| hd::tl -> begin
(vs_either hd uvonly (fun ( ft1 ) -> (vs_either_l tl uvonly (fun ( ft2 ) -> (let _52_6161 = (union_fvs_uvs ft1 ft2)
in (cont _52_6161))))))
end))

let freevars_kind = (fun ( k ) -> (vs_kind k false (fun ( _23_1855 ) -> (match (_23_1855) with
| (x, _) -> begin
x
end))))

let freevars_typ = (fun ( t ) -> (vs_typ t false (fun ( _23_1860 ) -> (match (_23_1860) with
| (x, _) -> begin
x
end))))

let freevars_exp = (fun ( e ) -> (vs_exp e false (fun ( _23_1865 ) -> (match (_23_1865) with
| (x, _) -> begin
x
end))))

let freevars_comp = (fun ( c ) -> (vs_comp c false (fun ( _23_1870 ) -> (match (_23_1870) with
| (x, _) -> begin
x
end))))

let freevars_args = (fun ( args ) -> (Support.Prims.pipe_right args (Support.List.fold_left (fun ( out ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _52_6177 = (freevars_typ t)
in (Support.Prims.pipe_left (union_fvs out) _52_6177))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _52_6178 = (freevars_exp e)
in (Support.Prims.pipe_left (union_fvs out) _52_6178))
end)) Microsoft_FStar_Absyn_Syntax.no_fvs)))

let is_free = (fun ( axs ) ( fvs ) -> (Support.Prims.pipe_right axs (Support.Microsoft.FStar.Util.for_some (fun ( _23_23 ) -> (match (_23_23) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(Support.Microsoft.FStar.Util.set_mem a fvs.Microsoft_FStar_Absyn_Syntax.ftvs)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(Support.Microsoft.FStar.Util.set_mem x fvs.Microsoft_FStar_Absyn_Syntax.fxvs)
end)))))

type syntax_sum =
| SynSumKind of Microsoft_FStar_Absyn_Syntax.knd
| SynSumType of Microsoft_FStar_Absyn_Syntax.typ
| SynSumExp of Microsoft_FStar_Absyn_Syntax.exp
| SynSumComp of (Microsoft_FStar_Absyn_Syntax.comp', unit) Microsoft_FStar_Absyn_Syntax.syntax

let is_SynSumKind = (fun ( _discr_ ) -> (match (_discr_) with
| SynSumKind (_) -> begin
true
end
| _ -> begin
false
end))

let is_SynSumType = (fun ( _discr_ ) -> (match (_discr_) with
| SynSumType (_) -> begin
true
end
| _ -> begin
false
end))

let is_SynSumExp = (fun ( _discr_ ) -> (match (_discr_) with
| SynSumExp (_) -> begin
true
end
| _ -> begin
false
end))

let is_SynSumComp = (fun ( _discr_ ) -> (match (_discr_) with
| SynSumComp (_) -> begin
true
end
| _ -> begin
false
end))

let rec update_uvars = (fun ( s ) ( uvs ) -> (let out = (let _52_6224 = (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (Support.Prims.pipe_right _52_6224 (Support.List.fold_left (fun ( out ) ( u ) -> (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (k) -> begin
(let _52_6222 = (uvars_in_kind k)
in (union_uvs _52_6222 out))
end
| _ -> begin
(let _23_1901 = out
in (let _52_6223 = (Support.Microsoft.FStar.Util.set_add u out.Microsoft_FStar_Absyn_Syntax.uvars_k)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _52_6223; Microsoft_FStar_Absyn_Syntax.uvars_t = _23_1901.Microsoft_FStar_Absyn_Syntax.uvars_t; Microsoft_FStar_Absyn_Syntax.uvars_e = _23_1901.Microsoft_FStar_Absyn_Syntax.uvars_e}))
end)) Microsoft_FStar_Absyn_Syntax.no_uvs)))
in (let out = (let _52_6229 = (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.Prims.pipe_right _52_6229 (Support.List.fold_left (fun ( out ) ( _23_1907 ) -> (match (_23_1907) with
| (u, t) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (t) -> begin
(let _52_6227 = (uvars_in_typ t)
in (union_uvs _52_6227 out))
end
| _ -> begin
(let _23_1912 = out
in (let _52_6228 = (Support.Microsoft.FStar.Util.set_add (u, t) out.Microsoft_FStar_Absyn_Syntax.uvars_t)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _23_1912.Microsoft_FStar_Absyn_Syntax.uvars_k; Microsoft_FStar_Absyn_Syntax.uvars_t = _52_6228; Microsoft_FStar_Absyn_Syntax.uvars_e = _23_1912.Microsoft_FStar_Absyn_Syntax.uvars_e}))
end)
end)) out)))
in (let out = (let _52_6234 = (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (Support.Prims.pipe_right _52_6234 (Support.List.fold_left (fun ( out ) ( _23_1918 ) -> (match (_23_1918) with
| (u, t) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (e) -> begin
(let _52_6232 = (uvars_in_exp e)
in (union_uvs _52_6232 out))
end
| _ -> begin
(let _23_1923 = out
in (let _52_6233 = (Support.Microsoft.FStar.Util.set_add (u, t) out.Microsoft_FStar_Absyn_Syntax.uvars_e)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _23_1923.Microsoft_FStar_Absyn_Syntax.uvars_k; Microsoft_FStar_Absyn_Syntax.uvars_t = _23_1923.Microsoft_FStar_Absyn_Syntax.uvars_t; Microsoft_FStar_Absyn_Syntax.uvars_e = _52_6233}))
end)
end)) out)))
in (let _23_1934 = (match (s) with
| SynSumKind (k) -> begin
(Support.ST.op_Colon_Equals k.Microsoft_FStar_Absyn_Syntax.uvs (Some (out)))
end
| SynSumType (t) -> begin
(Support.ST.op_Colon_Equals t.Microsoft_FStar_Absyn_Syntax.uvs (Some (out)))
end
| SynSumExp (e) -> begin
(Support.ST.op_Colon_Equals e.Microsoft_FStar_Absyn_Syntax.uvs (Some (out)))
end
| SynSumComp (c) -> begin
(Support.ST.op_Colon_Equals c.Microsoft_FStar_Absyn_Syntax.uvs (Some (out)))
end)
in out)))))
and uvars_in_kind = (fun ( k ) -> (let _52_6237 = (vs_kind k true (fun ( _23_1940 ) -> (match (_23_1940) with
| (_, x) -> begin
x
end)))
in (Support.Prims.pipe_left (update_uvars (SynSumKind (k))) _52_6237)))
and uvars_in_typ = (fun ( t ) -> (let _52_6240 = (vs_typ t true (fun ( _23_1945 ) -> (match (_23_1945) with
| (_, x) -> begin
x
end)))
in (Support.Prims.pipe_left (update_uvars (SynSumType (t))) _52_6240)))
and uvars_in_exp = (fun ( e ) -> (let _52_6243 = (vs_exp e true (fun ( _23_1950 ) -> (match (_23_1950) with
| (_, x) -> begin
x
end)))
in (Support.Prims.pipe_left (update_uvars (SynSumExp (e))) _52_6243)))
and uvars_in_comp = (fun ( c ) -> (let _52_6246 = (vs_comp c true (fun ( _23_1955 ) -> (match (_23_1955) with
| (_, x) -> begin
x
end)))
in (Support.Prims.pipe_left (update_uvars (SynSumComp (c))) _52_6246)))

let uvars_included_in = (fun ( u1 ) ( u2 ) -> (let _52_6254 = (let _52_6252 = (Support.Microsoft.FStar.Util.set_is_subset_of u1.Microsoft_FStar_Absyn_Syntax.uvars_k u2.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (let _52_6251 = (Support.Microsoft.FStar.Util.set_is_subset_of u1.Microsoft_FStar_Absyn_Syntax.uvars_t u2.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (_52_6252 && _52_6251)))
in (let _52_6253 = (Support.Microsoft.FStar.Util.set_is_subset_of u1.Microsoft_FStar_Absyn_Syntax.uvars_e u2.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (_52_6254 && _52_6253))))

let rec kind_formals = (fun ( k ) -> (let k = (compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam (_) -> begin
(failwith ("Impossible"))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_unknown) | (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) | (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
([], k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _23_1975 = (kind_formals k)
in (match (_23_1975) with
| (bs', k) -> begin
((Support.List.append bs bs'), k)
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(kind_formals k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_) -> begin
(failwith ("Impossible"))
end)))

let close_for_kind = (fun ( t ) ( k ) -> (let _23_1989 = (kind_formals k)
in (match (_23_1989) with
| (bs, _) -> begin
(match (bs) with
| [] -> begin
t
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.Microsoft_FStar_Absyn_Syntax.pos)
end)
end)))

let rec unabbreviate_kind = (fun ( k ) -> (let k = (compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(unabbreviate_kind k)
end
| _ -> begin
k
end)))

let close_with_lam = (fun ( tps ) ( t ) -> (match (tps) with
| [] -> begin
t
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (tps, t) None t.Microsoft_FStar_Absyn_Syntax.pos)
end))

let close_with_arrow = (fun ( tps ) ( t ) -> (match (tps) with
| [] -> begin
t
end
| _ -> begin
(let _23_2020 = (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs', c)) -> begin
((Support.List.append tps bs'), c)
end
| _ -> begin
(let _52_6271 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (tps, _52_6271))
end)
in (match (_23_2020) with
| (bs, c) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.Microsoft_FStar_Absyn_Syntax.pos)
end))
end))

let close_typ = close_with_arrow

let close_kind = (fun ( tps ) ( k ) -> (match (tps) with
| [] -> begin
k
end
| _ -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow' (tps, k) k.Microsoft_FStar_Absyn_Syntax.pos)
end))

let is_tuple_constructor = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (l) -> begin
(Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str "Prims.Tuple")
end
| _ -> begin
false
end))

let mk_tuple_lid = (fun ( n ) ( r ) -> (let t = (let _52_6284 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "Tuple%s" _52_6284))
in (let _52_6285 = (Microsoft_FStar_Absyn_Const.pconst t)
in (set_lid_range _52_6285 r))))

let mk_tuple_data_lid = (fun ( n ) ( r ) -> (let t = (let _52_6290 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "MkTuple%s" _52_6290))
in (let _52_6291 = (Microsoft_FStar_Absyn_Const.pconst t)
in (set_lid_range _52_6291 r))))

let is_tuple_data_lid = (fun ( f ) ( n ) -> (let _52_6296 = (mk_tuple_data_lid n Microsoft_FStar_Absyn_Syntax.dummyRange)
in (Microsoft_FStar_Absyn_Syntax.lid_equals f _52_6296)))

let is_dtuple_constructor = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (l) -> begin
(Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str "Prims.DTuple")
end
| _ -> begin
false
end))

let mk_dtuple_lid = (fun ( n ) ( r ) -> (let t = (let _52_6303 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "DTuple%s" _52_6303))
in (let _52_6304 = (Microsoft_FStar_Absyn_Const.pconst t)
in (set_lid_range _52_6304 r))))

let mk_dtuple_data_lid = (fun ( n ) ( r ) -> (let t = (let _52_6309 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "MkDTuple%s" _52_6309))
in (let _52_6310 = (Microsoft_FStar_Absyn_Const.pconst t)
in (set_lid_range _52_6310 r))))

let is_lid_equality = (fun ( x ) -> ((((Microsoft_FStar_Absyn_Syntax.lid_equals x Microsoft_FStar_Absyn_Const.eq_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals x Microsoft_FStar_Absyn_Const.eq2_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals x Microsoft_FStar_Absyn_Const.eqA_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals x Microsoft_FStar_Absyn_Const.eqT_lid)))

let is_forall = (fun ( lid ) -> ((Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.forall_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.allTyp_lid)))

let is_exists = (fun ( lid ) -> ((Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.exists_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.exTyp_lid)))

let is_qlid = (fun ( lid ) -> ((is_forall lid) || (is_exists lid)))

let is_equality = (fun ( x ) -> (is_lid_equality x.Microsoft_FStar_Absyn_Syntax.v))

let lid_is_connective = (let lst = (Microsoft_FStar_Absyn_Const.and_lid)::(Microsoft_FStar_Absyn_Const.or_lid)::(Microsoft_FStar_Absyn_Const.not_lid)::(Microsoft_FStar_Absyn_Const.iff_lid)::(Microsoft_FStar_Absyn_Const.imp_lid)::[]
in (fun ( lid ) -> (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals lid) lst)))

let is_constructor = (fun ( t ) ( lid ) -> (match ((let _52_6326 = (pre_typ t)
in _52_6326.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v lid)
end
| _ -> begin
false
end))

let rec is_constructed_typ = (fun ( t ) ( lid ) -> (match ((let _52_6331 = (pre_typ t)
in _52_6331.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (_) -> begin
(is_constructor t lid)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, _)) -> begin
(is_constructed_typ t lid)
end
| _ -> begin
false
end))

let rec get_tycon = (fun ( t ) -> (let t = (pre_typ t)
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

let base_kind = (fun ( _23_24 ) -> (match (_23_24) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
true
end
| _ -> begin
false
end))

let sortByFieldName = (fun ( fn_a_l ) -> (Support.Prims.pipe_right fn_a_l (Support.List.sortWith (fun ( _23_2099 ) ( _23_2103 ) -> (match ((_23_2099, _23_2103)) with
| ((fn1, _), (fn2, _)) -> begin
(let _52_6340 = (Microsoft_FStar_Absyn_Syntax.text_of_lid fn1)
in (let _52_6339 = (Microsoft_FStar_Absyn_Syntax.text_of_lid fn2)
in (Support.String.compare _52_6340 _52_6339)))
end)))))

let kt_kt = (Microsoft_FStar_Absyn_Const.kunary Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype)

let kt_kt_kt = (Microsoft_FStar_Absyn_Const.kbin Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype)

let tand = (ftv Microsoft_FStar_Absyn_Const.and_lid kt_kt_kt)

let tor = (ftv Microsoft_FStar_Absyn_Const.or_lid kt_kt_kt)

let timp = (ftv Microsoft_FStar_Absyn_Const.imp_lid kt_kt_kt)

let tiff = (ftv Microsoft_FStar_Absyn_Const.iff_lid kt_kt_kt)

let t_bool = (ftv Microsoft_FStar_Absyn_Const.bool_lid Microsoft_FStar_Absyn_Syntax.ktype)

let t_false = (ftv Microsoft_FStar_Absyn_Const.false_lid Microsoft_FStar_Absyn_Syntax.ktype)

let t_true = (ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)

let b2t_v = (let _52_6344 = (let _52_6343 = (let _52_6342 = (let _52_6341 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.null_v_binder t_bool)
in (_52_6341)::[])
in (_52_6342, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_6343 Microsoft_FStar_Absyn_Syntax.dummyRange))
in (ftv Microsoft_FStar_Absyn_Const.b2t_lid _52_6344))

let mk_conj_opt = (fun ( phi1 ) ( phi2 ) -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _52_6355 = (let _52_6354 = (let _52_6352 = (let _52_6351 = (Microsoft_FStar_Absyn_Syntax.targ phi1)
in (let _52_6350 = (let _52_6349 = (Microsoft_FStar_Absyn_Syntax.targ phi2)
in (_52_6349)::[])
in (_52_6351)::_52_6350))
in (tand, _52_6352))
in (let _52_6353 = (Support.Microsoft.FStar.Range.union_ranges phi1.Microsoft_FStar_Absyn_Syntax.pos phi2.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_6354 None _52_6353)))
in Some (_52_6355))
end))

let mk_binop = (fun ( op_t ) ( phi1 ) ( phi2 ) -> (let _52_6367 = (let _52_6365 = (let _52_6364 = (Microsoft_FStar_Absyn_Syntax.targ phi1)
in (let _52_6363 = (let _52_6362 = (Microsoft_FStar_Absyn_Syntax.targ phi2)
in (_52_6362)::[])
in (_52_6364)::_52_6363))
in (op_t, _52_6365))
in (let _52_6366 = (Support.Microsoft.FStar.Range.union_ranges phi1.Microsoft_FStar_Absyn_Syntax.pos phi2.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_6367 None _52_6366))))

let mk_neg = (fun ( phi ) -> (let _52_6373 = (let _52_6372 = (ftv Microsoft_FStar_Absyn_Const.not_lid kt_kt)
in (let _52_6371 = (let _52_6370 = (Microsoft_FStar_Absyn_Syntax.targ phi)
in (_52_6370)::[])
in (_52_6372, _52_6371)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_6373 None phi.Microsoft_FStar_Absyn_Syntax.pos)))

let mk_conj = (fun ( phi1 ) ( phi2 ) -> (mk_binop tand phi1 phi2))

let mk_conj_l = (fun ( phi ) -> (match (phi) with
| [] -> begin
(ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
end
| hd::tl -> begin
(Support.List.fold_right mk_conj tl hd)
end))

let mk_disj = (fun ( phi1 ) ( phi2 ) -> (mk_binop tor phi1 phi2))

let mk_disj_l = (fun ( phi ) -> (match (phi) with
| [] -> begin
(ftv Microsoft_FStar_Absyn_Const.false_lid Microsoft_FStar_Absyn_Syntax.ktype)
end
| hd::tl -> begin
(Support.List.fold_right mk_disj tl hd)
end))

let mk_imp = (fun ( phi1 ) ( phi2 ) -> (match ((let _52_6390 = (compress_typ phi1)
in _52_6390.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.false_lid) -> begin
t_true
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
phi2
end
| _ -> begin
(match ((let _52_6391 = (compress_typ phi2)
in _52_6391.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when ((Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.false_lid)) -> begin
phi2
end
| _ -> begin
(mk_binop timp phi1 phi2)
end)
end))

let mk_iff = (fun ( phi1 ) ( phi2 ) -> (mk_binop tiff phi1 phi2))

let b2t = (fun ( e ) -> (let _52_6400 = (let _52_6399 = (let _52_6398 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg e)
in (_52_6398)::[])
in (b2t_v, _52_6399))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_6400 None e.Microsoft_FStar_Absyn_Syntax.pos)))

let rec unmeta_typ = (fun ( t ) -> (let t = (compress_typ t)
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

let eq_k = (let a = (let _52_6403 = (new_bvd None)
in (bvd_to_bvar_s _52_6403 Microsoft_FStar_Absyn_Syntax.ktype))
in (let atyp = (btvar_to_typ a)
in (let b = (let _52_6404 = (new_bvd None)
in (bvd_to_bvar_s _52_6404 Microsoft_FStar_Absyn_Syntax.ktype))
in (let btyp = (btvar_to_typ b)
in (let _52_6411 = (let _52_6410 = (let _52_6409 = (let _52_6408 = (let _52_6407 = (Microsoft_FStar_Absyn_Syntax.null_v_binder atyp)
in (let _52_6406 = (let _52_6405 = (Microsoft_FStar_Absyn_Syntax.null_v_binder btyp)
in (_52_6405)::[])
in (_52_6407)::_52_6406))
in ((Support.Microsoft.FStar.Util.Inl (b), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_52_6408)
in ((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_52_6409)
in (_52_6410, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_6411 Microsoft_FStar_Absyn_Syntax.dummyRange))))))

let teq = (ftv Microsoft_FStar_Absyn_Const.eq2_lid eq_k)

let mk_eq = (fun ( t1 ) ( t2 ) ( e1 ) ( e2 ) -> (match ((t1.Microsoft_FStar_Absyn_Syntax.n, t2.Microsoft_FStar_Absyn_Syntax.n)) with
| ((Microsoft_FStar_Absyn_Syntax.Typ_unknown, _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_unknown)) -> begin
(failwith ("DIE! mk_eq with tun"))
end
| _ -> begin
(let _52_6429 = (let _52_6427 = (let _52_6426 = (Microsoft_FStar_Absyn_Syntax.itarg t1)
in (let _52_6425 = (let _52_6424 = (Microsoft_FStar_Absyn_Syntax.itarg t2)
in (let _52_6423 = (let _52_6422 = (Microsoft_FStar_Absyn_Syntax.varg e1)
in (let _52_6421 = (let _52_6420 = (Microsoft_FStar_Absyn_Syntax.varg e2)
in (_52_6420)::[])
in (_52_6422)::_52_6421))
in (_52_6424)::_52_6423))
in (_52_6426)::_52_6425))
in (teq, _52_6427))
in (let _52_6428 = (Support.Microsoft.FStar.Range.union_ranges e1.Microsoft_FStar_Absyn_Syntax.pos e2.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_6429 None _52_6428)))
end))

let eq_typ = (ftv Microsoft_FStar_Absyn_Const.eqT_lid Microsoft_FStar_Absyn_Syntax.kun)

let mk_eq_typ = (fun ( t1 ) ( t2 ) -> (let _52_6439 = (let _52_6437 = (let _52_6436 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _52_6435 = (let _52_6434 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (_52_6434)::[])
in (_52_6436)::_52_6435))
in (eq_typ, _52_6437))
in (let _52_6438 = (Support.Microsoft.FStar.Range.union_ranges t1.Microsoft_FStar_Absyn_Syntax.pos t2.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_6439 None _52_6438))))

let lex_t = (ftv Microsoft_FStar_Absyn_Const.lex_t_lid Microsoft_FStar_Absyn_Syntax.ktype)

let lex_top = (let lexnil = (withinfo Microsoft_FStar_Absyn_Const.lextop_lid lex_t Microsoft_FStar_Absyn_Syntax.dummyRange)
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar (lexnil, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) None Microsoft_FStar_Absyn_Syntax.dummyRange))

let lex_pair = (let a = (gen_bvar Microsoft_FStar_Absyn_Syntax.ktype)
in (let lexcons = (let _52_6449 = (let _52_6448 = (let _52_6447 = (let _52_6445 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _52_6444 = (let _52_6443 = (let _52_6440 = (btvar_to_typ a)
in (Microsoft_FStar_Absyn_Syntax.null_v_binder _52_6440))
in (let _52_6442 = (let _52_6441 = (Microsoft_FStar_Absyn_Syntax.null_v_binder lex_t)
in (_52_6441)::[])
in (_52_6443)::_52_6442))
in (_52_6445)::_52_6444))
in (let _52_6446 = (Microsoft_FStar_Absyn_Syntax.mk_Total lex_t)
in (_52_6447, _52_6446)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _52_6448 None Microsoft_FStar_Absyn_Syntax.dummyRange))
in (withinfo Microsoft_FStar_Absyn_Const.lexcons_lid _52_6449 Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar (lexcons, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) None Microsoft_FStar_Absyn_Syntax.dummyRange)))

let forall_kind = (let a = (let _52_6450 = (new_bvd None)
in (bvd_to_bvar_s _52_6450 Microsoft_FStar_Absyn_Syntax.ktype))
in (let atyp = (btvar_to_typ a)
in (let _52_6458 = (let _52_6457 = (let _52_6456 = (let _52_6455 = (let _52_6454 = (let _52_6453 = (let _52_6452 = (let _52_6451 = (Microsoft_FStar_Absyn_Syntax.null_v_binder atyp)
in (_52_6451)::[])
in (_52_6452, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_6453 Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.null_t_binder _52_6454))
in (_52_6455)::[])
in ((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_52_6456)
in (_52_6457, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_6458 Microsoft_FStar_Absyn_Syntax.dummyRange))))

let tforall = (ftv Microsoft_FStar_Absyn_Const.forall_lid forall_kind)

let allT_k = (fun ( k ) -> (let _52_6467 = (let _52_6466 = (let _52_6465 = (let _52_6464 = (let _52_6463 = (let _52_6462 = (let _52_6461 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (_52_6461)::[])
in (_52_6462, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_6463 Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.null_t_binder _52_6464))
in (_52_6465)::[])
in (_52_6466, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_6467 Microsoft_FStar_Absyn_Syntax.dummyRange)))

let eqT_k = (fun ( k ) -> (let _52_6474 = (let _52_6473 = (let _52_6472 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (let _52_6471 = (let _52_6470 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (_52_6470)::[])
in (_52_6472)::_52_6471))
in (_52_6473, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_6474 Microsoft_FStar_Absyn_Syntax.dummyRange)))

let tforall_typ = (fun ( k ) -> (let _52_6477 = (allT_k k)
in (ftv Microsoft_FStar_Absyn_Const.allTyp_lid _52_6477)))

let mk_forallT = (fun ( a ) ( b ) -> (let _52_6489 = (let _52_6488 = (tforall_typ a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _52_6487 = (let _52_6486 = (let _52_6485 = (let _52_6484 = (let _52_6483 = (let _52_6482 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (_52_6482)::[])
in (_52_6483, b))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _52_6484 None b.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _52_6485))
in (_52_6486)::[])
in (_52_6488, _52_6487)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_6489 None b.Microsoft_FStar_Absyn_Syntax.pos)))

let mk_forall = (fun ( x ) ( body ) -> (let r = Microsoft_FStar_Absyn_Syntax.dummyRange
in (let _52_6500 = (let _52_6499 = (let _52_6498 = (let _52_6497 = (let _52_6496 = (let _52_6495 = (let _52_6494 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_52_6494)::[])
in (_52_6495, body))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _52_6496 None r))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _52_6497))
in (_52_6498)::[])
in (tforall, _52_6499))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_6500 None r))))

let rec close_forall = (fun ( bs ) ( f ) -> (Support.List.fold_right (fun ( b ) ( f ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
f
end
| false -> begin
(let body = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam ((b)::[], f) None f.Microsoft_FStar_Absyn_Syntax.pos)
in (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _52_6510 = (let _52_6509 = (tforall_typ a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _52_6508 = (let _52_6507 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_52_6507)::[])
in (_52_6509, _52_6508)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_6510 None f.Microsoft_FStar_Absyn_Syntax.pos))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _52_6514 = (let _52_6513 = (let _52_6512 = (let _52_6511 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_52_6511)::[])
in ((Support.Microsoft.FStar.Util.Inl (x.Microsoft_FStar_Absyn_Syntax.sort), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_52_6512)
in (tforall, _52_6513))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _52_6514 None f.Microsoft_FStar_Absyn_Syntax.pos))
end))
end)) bs f))

let rec is_wild_pat = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_wild (_) -> begin
true
end
| _ -> begin
false
end))

let head_and_args = (fun ( t ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(head, args)
end
| _ -> begin
(t, [])
end)))

let head_and_args_e = (fun ( e ) -> (let e = (compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(head, args)
end
| _ -> begin
(e, [])
end)))

let function_formals = (fun ( t ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
Some ((bs, c))
end
| _ -> begin
None
end)))

let is_interpreted = (fun ( l ) -> (let theory_syms = (Microsoft_FStar_Absyn_Const.op_Eq)::(Microsoft_FStar_Absyn_Const.op_notEq)::(Microsoft_FStar_Absyn_Const.op_LT)::(Microsoft_FStar_Absyn_Const.op_LTE)::(Microsoft_FStar_Absyn_Const.op_GT)::(Microsoft_FStar_Absyn_Const.op_GTE)::(Microsoft_FStar_Absyn_Const.op_Subtraction)::(Microsoft_FStar_Absyn_Const.op_Minus)::(Microsoft_FStar_Absyn_Const.op_Addition)::(Microsoft_FStar_Absyn_Const.op_Multiply)::(Microsoft_FStar_Absyn_Const.op_Division)::(Microsoft_FStar_Absyn_Const.op_Modulus)::(Microsoft_FStar_Absyn_Const.op_And)::(Microsoft_FStar_Absyn_Const.op_Or)::(Microsoft_FStar_Absyn_Const.op_Negation)::[]
in (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals l) theory_syms)))

type qpats =
Microsoft_FStar_Absyn_Syntax.args

type connective =
| QAll of (Microsoft_FStar_Absyn_Syntax.binders * qpats * Microsoft_FStar_Absyn_Syntax.typ)
| QEx of (Microsoft_FStar_Absyn_Syntax.binders * qpats * Microsoft_FStar_Absyn_Syntax.typ)
| BaseConn of (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.args)

let is_QAll = (fun ( _discr_ ) -> (match (_discr_) with
| QAll (_) -> begin
true
end
| _ -> begin
false
end))

let is_QEx = (fun ( _discr_ ) -> (match (_discr_) with
| QEx (_) -> begin
true
end
| _ -> begin
false
end))

let is_BaseConn = (fun ( _discr_ ) -> (match (_discr_) with
| BaseConn (_) -> begin
true
end
| _ -> begin
false
end))

let destruct_typ_as_formula = (fun ( f ) -> (let destruct_base_conn = (fun ( f ) -> (let _23_2269 = (true, false)
in (match (_23_2269) with
| (type_sort, term_sort) -> begin
(let oneType = (type_sort)::[]
in (let twoTypes = (type_sort)::(type_sort)::[]
in (let threeTys = (type_sort)::(type_sort)::(type_sort)::[]
in (let twoTerms = (term_sort)::(term_sort)::[]
in (let connectives = ((Microsoft_FStar_Absyn_Const.true_lid, []))::((Microsoft_FStar_Absyn_Const.false_lid, []))::((Microsoft_FStar_Absyn_Const.and_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.or_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.imp_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.iff_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.ite_lid, threeTys))::((Microsoft_FStar_Absyn_Const.not_lid, oneType))::((Microsoft_FStar_Absyn_Const.eqT_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.eq2_lid, twoTerms))::((Microsoft_FStar_Absyn_Const.eq2_lid, (Support.List.append twoTypes twoTerms)))::[]
in (let rec aux = (fun ( f ) ( _23_2279 ) -> (match (_23_2279) with
| (lid, arity) -> begin
(let _23_2282 = (head_and_args f)
in (match (_23_2282) with
| (t, args) -> begin
(match ((let _52_6557 = (let _52_6553 = (is_constructor t lid)
in (_52_6553 && ((Support.List.length args) = (Support.List.length arity))))
in (let _52_6556 = (Support.List.forall2 (fun ( arg ) ( flag ) -> (match (arg) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
(flag = type_sort)
end
| (Support.Microsoft.FStar.Util.Inr (_), _) -> begin
(flag = term_sort)
end)) args arity)
in (_52_6557 && _52_6556)))) with
| true -> begin
Some (BaseConn ((lid, args)))
end
| false -> begin
None
end)
end))
end))
in (Support.Microsoft.FStar.Util.find_map connectives (aux f))))))))
end)))
in (let patterns = (fun ( t ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, pats))) -> begin
(let _52_6560 = (compress_typ t)
in (pats, _52_6560))
end
| _ -> begin
(let _52_6561 = (compress_typ t)
in ([], _52_6561))
end)))
in (let destruct_q_conn = (fun ( t ) -> (let is_q = (fun ( fa ) ( l ) -> (match (fa) with
| true -> begin
(is_forall l)
end
| false -> begin
(is_exists l)
end))
in (let flat = (fun ( t ) -> (let _23_2316 = (head_and_args t)
in (match (_23_2316) with
| (t, args) -> begin
(let _52_6575 = (Support.Prims.pipe_right args (Support.List.map (fun ( _23_25 ) -> (match (_23_25) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _52_6572 = (let _52_6571 = (compress_typ t)
in Support.Microsoft.FStar.Util.Inl (_52_6571))
in (_52_6572, imp))
end
| (Support.Microsoft.FStar.Util.Inr (e), imp) -> begin
(let _52_6574 = (let _52_6573 = (compress_exp e)
in Support.Microsoft.FStar.Util.Inr (_52_6573))
in (_52_6574, imp))
end))))
in (t, _52_6575))
end)))
in (let rec aux = (fun ( qopt ) ( out ) ( t ) -> (match ((let _52_6582 = (flat t)
in (qopt, _52_6582))) with
| ((Some (fa), ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, (Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t2)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((Some (fa), ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _::(Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t2)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_q fa tc.Microsoft_FStar_Absyn_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, (Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t2)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((None, ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _::(Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t2)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_qlid tc.Microsoft_FStar_Absyn_Syntax.v) -> begin
(aux (Some ((is_forall tc.Microsoft_FStar_Absyn_Syntax.v))) ((b)::out) t2)
end
| (Some (true), _) -> begin
(let _23_2468 = (patterns t)
in (match (_23_2468) with
| (pats, body) -> begin
Some (QAll (((Support.List.rev out), pats, body)))
end))
end
| (Some (false), _) -> begin
(let _23_2476 = (patterns t)
in (match (_23_2476) with
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




