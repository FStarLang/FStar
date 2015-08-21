
let handle_err = (fun ( warning ) ( ret ) ( e ) -> (match (e) with
| Microsoft_FStar_Absyn_Syntax.Error ((msg, r)) -> begin
(let _25_34 = (let _89_8 = (let _89_7 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format3 "%s : %s\n%s\n" _89_7 (match (warning) with
| true -> begin
"Warning"
end
| false -> begin
"Error"
end) msg))
in (Support.Microsoft.FStar.Util.print_string _89_8))
in ())
end
| Support.Microsoft.FStar.Util.NYI (s) -> begin
(let _25_38 = (let _89_9 = (Support.Microsoft.FStar.Util.format1 "Feature not yet implemented: %s" s)
in (Support.Microsoft.FStar.Util.print_string _89_9))
in ())
end
| Microsoft_FStar_Absyn_Syntax.Err (s) -> begin
(let _89_10 = (Support.Microsoft.FStar.Util.format1 "Error: %s" s)
in (Support.Microsoft.FStar.Util.print_string _89_10))
end
| _25_43 -> begin
(raise (e))
end))

let handleable = (fun ( _25_1 ) -> (match (_25_1) with
| (Microsoft_FStar_Absyn_Syntax.Error (_)) | (Support.Microsoft.FStar.Util.NYI (_)) | (Microsoft_FStar_Absyn_Syntax.Err (_)) -> begin
true
end
| _25_55 -> begin
false
end))

type gensym_t =
{gensym : unit  ->  string; reset : unit  ->  unit}

let is_Mkgensym_t = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkgensym_t"))

let gs = (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (let n_resets = (Support.Microsoft.FStar.Util.mk_ref 0)
in {gensym = (fun ( _25_61 ) -> (match (()) with
| () -> begin
(let _89_38 = (let _89_35 = (let _89_34 = (let _89_33 = (Support.ST.read n_resets)
in (Support.Microsoft.FStar.Util.string_of_int _89_33))
in (Support.String.strcat "_" _89_34))
in (Support.String.strcat _89_35 "_"))
in (let _89_37 = (let _89_36 = (let _25_62 = (Support.Microsoft.FStar.Util.incr ctr)
in (Support.ST.read ctr))
in (Support.Microsoft.FStar.Util.string_of_int _89_36))
in (Support.String.strcat _89_38 _89_37)))
end)); reset = (fun ( _25_64 ) -> (match (()) with
| () -> begin
(let _25_65 = (Support.ST.op_Colon_Equals ctr 0)
in (Support.Microsoft.FStar.Util.incr n_resets))
end))}))

let gensym = (fun ( _25_67 ) -> (match (()) with
| () -> begin
(gs.gensym ())
end))

let reset_gensym = (fun ( _25_68 ) -> (match (()) with
| () -> begin
(gs.reset ())
end))

let rec gensyms = (fun ( x ) -> (match (x) with
| 0 -> begin
[]
end
| n -> begin
(let _89_47 = (gensym ())
in (let _89_46 = (gensyms (n - 1))
in (_89_47)::_89_46))
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

let mkbvd = (fun ( _25_82 ) -> (match (_25_82) with
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
| _25_109 -> begin
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

let freshen_bvd = (fun ( bvd' ) -> (let _89_88 = (let _89_87 = (genident (Some ((range_of_bvd bvd'))))
in (bvd'.Microsoft_FStar_Absyn_Syntax.ppname, _89_87))
in (mkbvd _89_88)))

let freshen_bvar = (fun ( b ) -> (let _89_90 = (freshen_bvd b.Microsoft_FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _89_90 b.Microsoft_FStar_Absyn_Syntax.sort)))

let gen_bvar = (fun ( sort ) -> (let bvd = (new_bvd None)
in (bvd_to_bvar_s bvd sort)))

let gen_bvar_p = (fun ( r ) ( sort ) -> (let bvd = (new_bvd (Some (r)))
in (bvd_to_bvar_s bvd sort)))

let bvdef_of_str = (fun ( s ) -> (let f = (fun ( s ) -> (let id = (Microsoft_FStar_Absyn_Syntax.id_of_text s)
in (mkbvd (id, id))))
in (f s)))

let set_bvd_range = (fun ( bvd ) ( r ) -> (let _89_99 = (Microsoft_FStar_Absyn_Syntax.mk_ident (bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText, r))
in (let _89_98 = (Microsoft_FStar_Absyn_Syntax.mk_ident (bvd.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText, r))
in {Microsoft_FStar_Absyn_Syntax.ppname = _89_99; Microsoft_FStar_Absyn_Syntax.realname = _89_98})))

let set_lid_range = (fun ( l ) ( r ) -> (let ids = (Support.All.pipe_right (Support.List.append l.Microsoft_FStar_Absyn_Syntax.ns ((l.Microsoft_FStar_Absyn_Syntax.ident)::[])) (Support.List.map (fun ( i ) -> (Microsoft_FStar_Absyn_Syntax.mk_ident (i.Microsoft_FStar_Absyn_Syntax.idText, r)))))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids ids)))

let fv = (fun ( l ) -> (let _89_107 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l Microsoft_FStar_Absyn_Syntax.tun _89_107)))

let fvvar_of_lid = (fun ( l ) ( t ) -> (let _89_110 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l t _89_110)))

let fvar = (fun ( dc ) ( l ) ( r ) -> (let _89_119 = (let _89_118 = (let _89_117 = (set_lid_range l r)
in (fv _89_117))
in (_89_118, dc))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _89_119 None r)))

let ftv = (fun ( l ) ( k ) -> (let _89_126 = (let _89_124 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l k _89_124))
in (let _89_125 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_const _89_126 None _89_125))))

let order_bvd = (fun ( x ) ( y ) -> (match ((x, y)) with
| (Support.Microsoft.FStar.Util.Inl (_25_155), Support.Microsoft.FStar.Util.Inr (_25_158)) -> begin
(- (1))
end
| (Support.Microsoft.FStar.Util.Inr (_25_162), Support.Microsoft.FStar.Util.Inl (_25_165)) -> begin
1
end
| (Support.Microsoft.FStar.Util.Inl (x), Support.Microsoft.FStar.Util.Inl (y)) -> begin
(Support.String.compare x.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText y.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Support.String.compare x.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText y.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText)
end))

let arg_of_non_null_binder = (fun ( _25_180 ) -> (match (_25_180) with
| (b, imp) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _89_131 = (let _89_130 = (btvar_to_typ a)
in Support.Microsoft.FStar.Util.Inl (_89_130))
in (_89_131, imp))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _89_133 = (let _89_132 = (bvar_to_exp x)
in Support.Microsoft.FStar.Util.Inr (_89_132))
in (_89_133, imp))
end)
end))

let args_of_non_null_binders = (fun ( binders ) -> (Support.All.pipe_right binders (Support.List.collect (fun ( b ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
[]
end
| false -> begin
(let _89_137 = (arg_of_non_null_binder b)
in (_89_137)::[])
end)))))

let args_of_binders = (fun ( binders ) -> (let _89_147 = (Support.All.pipe_right binders (Support.List.map (fun ( b ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
(let b = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _89_142 = (let _89_141 = (gen_bvar a.Microsoft_FStar_Absyn_Syntax.sort)
in Support.Microsoft.FStar.Util.Inl (_89_141))
in (_89_142, (Support.Prims.snd b)))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _89_144 = (let _89_143 = (gen_bvar x.Microsoft_FStar_Absyn_Syntax.sort)
in Support.Microsoft.FStar.Util.Inr (_89_143))
in (_89_144, (Support.Prims.snd b)))
end)
in (let _89_145 = (arg_of_non_null_binder b)
in (b, _89_145)))
end
| false -> begin
(let _89_146 = (arg_of_non_null_binder b)
in (b, _89_146))
end))))
in (Support.All.pipe_right _89_147 Support.List.unzip)))

let name_binders = (fun ( binders ) -> (Support.All.pipe_right binders (Support.List.mapi (fun ( i ) ( b ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
(match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let b = (let _89_153 = (let _89_152 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.String.strcat "_" _89_152))
in (Microsoft_FStar_Absyn_Syntax.id_of_text _89_153))
in (let b = (bvd_to_bvar_s (mkbvd (b, b)) a.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.Inl (b), imp)))
end
| (Support.Microsoft.FStar.Util.Inr (y), imp) -> begin
(let x = (let _89_155 = (let _89_154 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.String.strcat "_" _89_154))
in (Microsoft_FStar_Absyn_Syntax.id_of_text _89_155))
in (let x = (bvd_to_bvar_s (mkbvd (x, x)) y.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.Inr (x), imp)))
end)
end
| false -> begin
b
end)))))

let name_function_binders = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, comp)) -> begin
(let _89_159 = (let _89_158 = (name_binders binders)
in (_89_158, comp))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _89_159 None t.Microsoft_FStar_Absyn_Syntax.pos))
end
| _25_215 -> begin
t
end))

let null_binders_of_tks = (fun ( tks ) -> (Support.All.pipe_right tks (Support.List.map (fun ( _25_2 ) -> (match (_25_2) with
| (Support.Microsoft.FStar.Util.Inl (k), imp) -> begin
(let _89_164 = (let _89_163 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (Support.All.pipe_left Support.Prims.fst _89_163))
in (_89_164, imp))
end
| (Support.Microsoft.FStar.Util.Inr (t), imp) -> begin
(let _89_166 = (let _89_165 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (Support.All.pipe_left Support.Prims.fst _89_165))
in (_89_166, imp))
end)))))

let binders_of_tks = (fun ( tks ) -> (Support.All.pipe_right tks (Support.List.map (fun ( _25_3 ) -> (match (_25_3) with
| (Support.Microsoft.FStar.Util.Inl (k), imp) -> begin
(let _89_171 = (let _89_170 = (gen_bvar_p k.Microsoft_FStar_Absyn_Syntax.pos k)
in Support.Microsoft.FStar.Util.Inl (_89_170))
in (_89_171, imp))
end
| (Support.Microsoft.FStar.Util.Inr (t), imp) -> begin
(let _89_173 = (let _89_172 = (gen_bvar_p t.Microsoft_FStar_Absyn_Syntax.pos t)
in Support.Microsoft.FStar.Util.Inr (_89_172))
in (_89_173, imp))
end)))))

let binders_of_freevars = (fun ( fvs ) -> (let _89_179 = (let _89_176 = (Support.Microsoft.FStar.Util.set_elements fvs.Microsoft_FStar_Absyn_Syntax.ftvs)
in (Support.All.pipe_right _89_176 (Support.List.map Microsoft_FStar_Absyn_Syntax.t_binder)))
in (let _89_178 = (let _89_177 = (Support.Microsoft.FStar.Util.set_elements fvs.Microsoft_FStar_Absyn_Syntax.fxvs)
in (Support.All.pipe_right _89_177 (Support.List.map Microsoft_FStar_Absyn_Syntax.v_binder)))
in (Support.List.append _89_179 _89_178))))

let subst_to_string = (fun ( s ) -> (let _89_182 = (Support.All.pipe_right s (Support.List.map (fun ( _25_4 ) -> (match (_25_4) with
| Support.Microsoft.FStar.Util.Inl ((b, _25_241)) -> begin
b.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText
end
| Support.Microsoft.FStar.Util.Inr ((x, _25_246)) -> begin
x.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText
end))))
in (Support.All.pipe_right _89_182 (Support.String.concat ", "))))

let subst_tvar = (fun ( s ) ( a ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _25_5 ) -> (match (_25_5) with
| Support.Microsoft.FStar.Util.Inl ((b, t)) when (bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _25_257 -> begin
None
end))))

let subst_xvar = (fun ( s ) ( a ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _25_6 ) -> (match (_25_6) with
| Support.Microsoft.FStar.Util.Inr ((b, t)) when (bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _25_266 -> begin
None
end))))

let rec subst_typ' = (fun ( s ) ( t ) -> (match (s) with
| ([]) | ([]::[]) -> begin
(Microsoft_FStar_Absyn_Visit.compress_typ t)
end
| _25_273 -> begin
(let t0 = (Microsoft_FStar_Absyn_Visit.compress_typ t)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((Support.Microsoft.FStar.Util.Inl ((t', s')), m)) -> begin
(let _89_207 = (let _89_206 = (compose_subst s' s)
in (let _89_205 = (Support.Microsoft.FStar.Util.mk_ref None)
in (t', _89_206, _89_205)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_delayed _89_207 None t.Microsoft_FStar_Absyn_Syntax.pos))
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((Support.Microsoft.FStar.Util.Inr (mk_t), m)) -> begin
(let t = (mk_t ())
in (let _25_288 = (Support.ST.op_Colon_Equals m (Some (t)))
in (subst_typ' s t)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let rec aux = (fun ( s' ) -> (match (s') with
| s0::rest -> begin
(match ((subst_tvar s0 a)) with
| Some (t) -> begin
(subst_typ' rest t)
end
| _25_300 -> begin
(aux rest)
end)
end
| _25_302 -> begin
t0
end))
in (aux s))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
t0
end
| _25_311 -> begin
(let _89_212 = (let _89_211 = (Support.Microsoft.FStar.Util.mk_ref None)
in (t0, s, _89_211))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_delayed _89_212 None t.Microsoft_FStar_Absyn_Syntax.pos))
end))
end))
and subst_exp' = (fun ( s ) ( e ) -> (match (s) with
| ([]) | ([]::[]) -> begin
(Microsoft_FStar_Absyn_Visit.compress_exp e)
end
| _25_318 -> begin
(let e0 = (Microsoft_FStar_Absyn_Visit.compress_exp e)
in (match (e0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed ((e, s', m)) -> begin
(let _89_217 = (let _89_216 = (compose_subst s' s)
in (let _89_215 = (Support.Microsoft.FStar.Util.mk_ref None)
in (e, _89_216, _89_215)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_delayed _89_217 None e.Microsoft_FStar_Absyn_Syntax.pos))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let rec aux = (fun ( s ) -> (match (s) with
| s0::rest -> begin
(match ((subst_xvar s0 x)) with
| Some (e) -> begin
(subst_exp' rest e)
end
| _25_335 -> begin
(aux rest)
end)
end
| _25_337 -> begin
e0
end))
in (aux s))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
e0
end
| _25_345 -> begin
(let _89_221 = (let _89_220 = (Support.Microsoft.FStar.Util.mk_ref None)
in (e0, s, _89_220))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_delayed _89_221 None e0.Microsoft_FStar_Absyn_Syntax.pos))
end))
end))
and subst_kind' = (fun ( s ) ( k ) -> (match (s) with
| ([]) | ([]::[]) -> begin
(Microsoft_FStar_Absyn_Visit.compress_kind k)
end
| _25_352 -> begin
(let k0 = (Microsoft_FStar_Absyn_Visit.compress_kind k)
in (match (k0.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) | (Microsoft_FStar_Absyn_Syntax.Kind_unknown) -> begin
k0
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed ((k, s', m)) -> begin
(let _89_226 = (let _89_225 = (compose_subst s' s)
in (let _89_224 = (Support.Microsoft.FStar.Util.mk_ref None)
in (k, _89_225, _89_224)))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_delayed _89_226 k0.Microsoft_FStar_Absyn_Syntax.pos))
end
| _25_363 -> begin
(let _89_228 = (let _89_227 = (Support.Microsoft.FStar.Util.mk_ref None)
in (k0, s, _89_227))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_delayed _89_228 k0.Microsoft_FStar_Absyn_Syntax.pos))
end))
end))
and subst_flags' = (fun ( s ) ( flags ) -> (Support.All.pipe_right flags (Support.List.map (fun ( _25_7 ) -> (match (_25_7) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (a) -> begin
(let _89_232 = (subst_exp' s a)
in Microsoft_FStar_Absyn_Syntax.DECREASES (_89_232))
end
| f -> begin
f
end)))))
and subst_comp_typ' = (fun ( s ) ( t ) -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _25_376 -> begin
(let _25_377 = t
in (let _89_242 = (subst_typ' s t.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _89_241 = (Support.List.map (fun ( _25_8 ) -> (match (_25_8) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _89_237 = (let _89_236 = (subst_typ' s t)
in Support.Microsoft.FStar.Util.Inl (_89_236))
in (_89_237, imp))
end
| (Support.Microsoft.FStar.Util.Inr (e), imp) -> begin
(let _89_239 = (let _89_238 = (subst_exp' s e)
in Support.Microsoft.FStar.Util.Inr (_89_238))
in (_89_239, imp))
end)) t.Microsoft_FStar_Absyn_Syntax.effect_args)
in (let _89_240 = (subst_flags' s t.Microsoft_FStar_Absyn_Syntax.flags)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _25_377.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _89_242; Microsoft_FStar_Absyn_Syntax.effect_args = _89_241; Microsoft_FStar_Absyn_Syntax.flags = _89_240}))))
end))
and subst_comp' = (fun ( s ) ( t ) -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _25_394 -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _89_245 = (subst_typ' s t)
in (Microsoft_FStar_Absyn_Syntax.mk_Total _89_245))
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _89_246 = (subst_comp_typ' s ct)
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _89_246))
end)
end))
and compose_subst = (fun ( s1 ) ( s2 ) -> (Support.List.append s1 s2))

let mk_subst = (fun ( s ) -> (s)::[])

let subst_kind = (fun ( s ) ( t ) -> (subst_kind' (mk_subst s) t))

let subst_typ = (fun ( s ) ( t ) -> (subst_typ' (mk_subst s) t))

let subst_exp = (fun ( s ) ( t ) -> (subst_exp' (mk_subst s) t))

let subst_flags = (fun ( s ) ( t ) -> (subst_flags' (mk_subst s) t))

let subst_comp = (fun ( s ) ( t ) -> (subst_comp' (mk_subst s) t))

let subst_binder = (fun ( s ) ( _25_9 ) -> (match (_25_9) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _89_274 = (let _89_273 = (let _25_418 = a
in (let _89_272 = (subst_kind s a.Microsoft_FStar_Absyn_Syntax.sort)
in {Microsoft_FStar_Absyn_Syntax.v = _25_418.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _89_272; Microsoft_FStar_Absyn_Syntax.p = _25_418.Microsoft_FStar_Absyn_Syntax.p}))
in Support.Microsoft.FStar.Util.Inl (_89_273))
in (_89_274, imp))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _89_277 = (let _89_276 = (let _25_424 = x
in (let _89_275 = (subst_typ s x.Microsoft_FStar_Absyn_Syntax.sort)
in {Microsoft_FStar_Absyn_Syntax.v = _25_424.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _89_275; Microsoft_FStar_Absyn_Syntax.p = _25_424.Microsoft_FStar_Absyn_Syntax.p}))
in Support.Microsoft.FStar.Util.Inr (_89_276))
in (_89_277, imp))
end))

let subst_arg = (fun ( s ) ( _25_10 ) -> (match (_25_10) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _89_281 = (let _89_280 = (subst_typ s t)
in Support.Microsoft.FStar.Util.Inl (_89_280))
in (_89_281, imp))
end
| (Support.Microsoft.FStar.Util.Inr (e), imp) -> begin
(let _89_283 = (let _89_282 = (subst_exp s e)
in Support.Microsoft.FStar.Util.Inr (_89_282))
in (_89_283, imp))
end))

let subst_binders = (fun ( s ) ( bs ) -> (match (s) with
| [] -> begin
bs
end
| _25_440 -> begin
(Support.List.map (subst_binder s) bs)
end))

let subst_args = (fun ( s ) ( args ) -> (match (s) with
| [] -> begin
args
end
| _25_445 -> begin
(Support.List.map (subst_arg s) args)
end))

let subst_formal = (fun ( f ) ( a ) -> (match ((f, a)) with
| ((Support.Microsoft.FStar.Util.Inl (a), _25_451), (Support.Microsoft.FStar.Util.Inl (t), _25_456)) -> begin
Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t))
end
| ((Support.Microsoft.FStar.Util.Inr (x), _25_462), (Support.Microsoft.FStar.Util.Inr (v), _25_467)) -> begin
Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, v))
end
| _25_471 -> begin
(Support.All.failwith "Ill-formed substitution")
end))

let mk_subst_one_binder = (fun ( b1 ) ( b2 ) -> (match (((Microsoft_FStar_Absyn_Syntax.is_null_binder b1) || (Microsoft_FStar_Absyn_Syntax.is_null_binder b2))) with
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
(let _89_298 = (let _89_297 = (let _89_296 = (btvar_to_typ a)
in (b.Microsoft_FStar_Absyn_Syntax.v, _89_296))
in Support.Microsoft.FStar.Util.Inl (_89_297))
in (_89_298)::[])
end)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(match ((bvar_eq x y)) with
| true -> begin
[]
end
| false -> begin
(let _89_301 = (let _89_300 = (let _89_299 = (bvar_to_exp x)
in (y.Microsoft_FStar_Absyn_Syntax.v, _89_299))
in Support.Microsoft.FStar.Util.Inr (_89_300))
in (_89_301)::[])
end)
end
| _25_485 -> begin
[]
end)
end))

let mk_subst_binder = (fun ( bs1 ) ( bs2 ) -> (let rec aux = (fun ( out ) ( bs1 ) ( bs2 ) -> (match ((bs1, bs2)) with
| ([], []) -> begin
Some (out)
end
| (b1::bs1, b2::bs2) -> begin
(let _89_313 = (let _89_312 = (mk_subst_one_binder b1 b2)
in (Support.List.append _89_312 out))
in (aux _89_313 bs1 bs2))
end
| _25_503 -> begin
None
end))
in (aux [] bs1 bs2)))

let subst_of_list = (fun ( formals ) ( actuals ) -> (match (((Support.List.length formals) = (Support.List.length actuals))) with
| true -> begin
(Support.List.map2 subst_formal formals actuals)
end
| false -> begin
(Support.All.failwith "Ill-formed substitution")
end))

type red_ctrl =
{stop_if_empty_subst : bool; descend : bool}

let is_Mkred_ctrl = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkred_ctrl"))

let alpha_ctrl = {stop_if_empty_subst = false; descend = true}

let subst_ctrl = {stop_if_empty_subst = true; descend = true}

let null_ctrl = {stop_if_empty_subst = true; descend = false}

let extend_subst = (fun ( e ) ( s ) -> (Support.List.append (((mk_subst e))::[]) s))

let map_knd = (fun ( s ) ( vk ) ( mt ) ( me ) ( descend ) ( binders ) ( k ) -> (let _89_334 = (subst_kind' s k)
in (_89_334, descend)))

let map_typ = (fun ( s ) ( mk ) ( vt ) ( me ) ( descend ) ( binders ) ( t ) -> (let _89_342 = (subst_typ' s t)
in (_89_342, descend)))

let map_exp = (fun ( s ) ( mk ) ( me ) ( ve ) ( descend ) ( binders ) ( e ) -> (let _89_350 = (subst_exp' s e)
in (_89_350, descend)))

let map_flags = (fun ( s ) ( map_exp ) ( descend ) ( binders ) ( flags ) -> (Support.All.pipe_right flags (Support.List.map (fun ( _25_11 ) -> (match (_25_11) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _89_367 = (let _89_366 = (map_exp descend binders e)
in (Support.All.pipe_right _89_366 Support.Prims.fst))
in Microsoft_FStar_Absyn_Syntax.DECREASES (_89_367))
end
| f -> begin
f
end)))))

let map_comp = (fun ( s ) ( mk ) ( map_typ ) ( map_exp ) ( descend ) ( binders ) ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _25_552 = (map_typ descend binders t)
in (match (_25_552) with
| (t, descend) -> begin
(let _89_390 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (_89_390, descend))
end))
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _25_557 = (map_typ descend binders ct.Microsoft_FStar_Absyn_Syntax.result_typ)
in (match (_25_557) with
| (t, descend) -> begin
(let _25_560 = (Microsoft_FStar_Absyn_Visit.map_args map_typ map_exp descend binders ct.Microsoft_FStar_Absyn_Syntax.effect_args)
in (match (_25_560) with
| (args, descend) -> begin
(let _89_393 = (let _89_392 = (let _25_561 = ct
in (let _89_391 = (map_flags s map_exp descend binders ct.Microsoft_FStar_Absyn_Syntax.flags)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _25_561.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = args; Microsoft_FStar_Absyn_Syntax.flags = _89_391}))
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _89_392))
in (_89_393, descend))
end))
end))
end))

let visit_knd = (fun ( s ) ( vk ) ( mt ) ( me ) ( ctrl ) ( binders ) ( k ) -> (let k = (Microsoft_FStar_Absyn_Visit.compress_kind k)
in (match (ctrl.descend) with
| true -> begin
(let _25_574 = (vk null_ctrl binders k)
in (match (_25_574) with
| (k, _25_573) -> begin
(k, ctrl)
end))
end
| false -> begin
(map_knd s vk mt me null_ctrl binders k)
end)))

let rec compress_kind = (fun ( k ) -> (let k = (Microsoft_FStar_Absyn_Visit.compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_delayed ((k', s, m)) -> begin
(let k' = (let _89_439 = (Microsoft_FStar_Absyn_Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) Microsoft_FStar_Absyn_Visit.combine_kind Microsoft_FStar_Absyn_Visit.combine_typ Microsoft_FStar_Absyn_Visit.combine_exp subst_ctrl [] k')
in (Support.All.pipe_left Support.Prims.fst _89_439))
in (let k' = (compress_kind k')
in (let _25_584 = (Support.ST.op_Colon_Equals m (Some (k')))
in k')))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, actuals)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (k) -> begin
(match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam ((formals, k')) -> begin
(let _89_441 = (let _89_440 = (subst_of_list formals actuals)
in (subst_kind _89_440 k'))
in (compress_kind _89_441))
end
| _25_597 -> begin
(match (((Support.List.length actuals) = 0)) with
| true -> begin
k
end
| false -> begin
(Support.All.failwith "Wrong arity for kind unifier")
end)
end)
end
| _25_599 -> begin
k
end)
end
| _25_601 -> begin
k
end)))

let rec visit_typ = (fun ( s ) ( mk ) ( vt ) ( me ) ( ctrl ) ( boundvars ) ( t ) -> (let visit_prod = (fun ( bs ) ( tc ) -> (let _25_662 = (Support.All.pipe_right bs (Support.List.fold_left (fun ( _25_615 ) ( b ) -> (match (_25_615) with
| (bs, boundvars, s) -> begin
(match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _25_624 = (map_knd s mk vt me null_ctrl boundvars a.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_25_624) with
| (k, _25_623) -> begin
(let a = (let _25_625 = a
in {Microsoft_FStar_Absyn_Syntax.v = _25_625.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _25_625.Microsoft_FStar_Absyn_Syntax.p})
in (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
(((Support.Microsoft.FStar.Util.Inl (a), imp))::bs, boundvars, s)
end
| false -> begin
(let boundvars' = (Support.Microsoft.FStar.Util.Inl (a.Microsoft_FStar_Absyn_Syntax.v))::boundvars
in (let _25_637 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(Support.Microsoft.FStar.Util.Inl (a), s, boundvars')
end
| _25_631 -> begin
(let b = (let _89_518 = (freshen_bvd a.Microsoft_FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _89_518 k))
in (let s = (let _89_521 = (let _89_520 = (let _89_519 = (btvar_to_typ b)
in (a.Microsoft_FStar_Absyn_Syntax.v, _89_519))
in Support.Microsoft.FStar.Util.Inl (_89_520))
in (extend_subst _89_521 s))
in (Support.Microsoft.FStar.Util.Inl (b), s, (Support.Microsoft.FStar.Util.Inl (b.Microsoft_FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_25_637) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end))
end))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _25_645 = (map_typ s mk vt me null_ctrl boundvars x.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_25_645) with
| (t, _25_644) -> begin
(let x = (let _25_646 = x
in {Microsoft_FStar_Absyn_Syntax.v = _25_646.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _25_646.Microsoft_FStar_Absyn_Syntax.p})
in (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
(((Support.Microsoft.FStar.Util.Inr (x), imp))::bs, boundvars, s)
end
| false -> begin
(let boundvars' = (Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.v))::boundvars
in (let _25_658 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(Support.Microsoft.FStar.Util.Inr (x), s, boundvars')
end
| _25_652 -> begin
(let y = (let _89_531 = (freshen_bvd x.Microsoft_FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _89_531 t))
in (let s = (let _89_534 = (let _89_533 = (let _89_532 = (bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _89_532))
in Support.Microsoft.FStar.Util.Inr (_89_533))
in (extend_subst _89_534 s))
in (Support.Microsoft.FStar.Util.Inr (y), s, (Support.Microsoft.FStar.Util.Inr (y.Microsoft_FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_25_658) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end))
end))
end)
end)) ([], boundvars, s)))
in (match (_25_662) with
| (bs, boundvars, s) -> begin
(let tc = (match ((s, tc)) with
| ([], _25_665) -> begin
tc
end
| (_25_668, Support.Microsoft.FStar.Util.Inl (t)) -> begin
(let _89_545 = (let _89_544 = (map_typ s mk vt me null_ctrl boundvars t)
in (Support.All.pipe_left Support.Prims.fst _89_544))
in Support.Microsoft.FStar.Util.Inl (_89_545))
end
| (_25_673, Support.Microsoft.FStar.Util.Inr (c)) -> begin
(let _89_568 = (let _89_567 = (map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl boundvars c)
in (Support.All.pipe_left Support.Prims.fst _89_567))
in Support.Microsoft.FStar.Util.Inr (_89_568))
end)
in ((Support.List.rev bs), tc))
end)))
in (let t0 = t
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (_25_680) -> begin
(let _89_570 = (let _89_569 = (subst_typ' s t0)
in (Support.All.pipe_left compress_typ _89_569))
in (_89_570, ctrl))
end
| _25_683 when (not (ctrl.descend)) -> begin
(map_typ s mk vt me null_ctrl boundvars t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(match ((visit_prod bs (Support.Microsoft.FStar.Util.Inr (c)))) with
| (bs, Support.Microsoft.FStar.Util.Inr (c)) -> begin
(let _89_580 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t0.Microsoft_FStar_Absyn_Syntax.pos)
in (_89_580, ctrl))
end
| _25_693 -> begin
(Support.All.failwith "Impossible")
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, t)) -> begin
(match ((visit_prod (((Support.Microsoft.FStar.Util.Inr (x), None))::[]) (Support.Microsoft.FStar.Util.Inl (t)))) with
| ((Support.Microsoft.FStar.Util.Inr (x), _25_701)::[], Support.Microsoft.FStar.Util.Inl (t)) -> begin
(let _89_581 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, t) None t0.Microsoft_FStar_Absyn_Syntax.pos)
in (_89_581, ctrl))
end
| _25_708 -> begin
(Support.All.failwith "Impossible")
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(match ((visit_prod bs (Support.Microsoft.FStar.Util.Inl (t)))) with
| (bs, Support.Microsoft.FStar.Util.Inl (t)) -> begin
(let _89_582 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t0.Microsoft_FStar_Absyn_Syntax.pos)
in (_89_582, ctrl))
end
| _25_718 -> begin
(Support.All.failwith "Impossible")
end)
end
| _25_720 -> begin
(let _25_724 = (vt null_ctrl boundvars t)
in (match (_25_724) with
| (t, _25_723) -> begin
(t, ctrl)
end))
end))))
and compress_typ' = (fun ( t ) -> (let t = (Microsoft_FStar_Absyn_Visit.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((Support.Microsoft.FStar.Util.Inl ((t', s)), m)) -> begin
(let res = (let _89_602 = (Microsoft_FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) Microsoft_FStar_Absyn_Visit.combine_kind Microsoft_FStar_Absyn_Visit.combine_typ Microsoft_FStar_Absyn_Visit.combine_exp subst_ctrl [] t')
in (Support.All.pipe_left Support.Prims.fst _89_602))
in (let res = (compress_typ' res)
in (let _25_736 = (Support.ST.op_Colon_Equals m (Some (res)))
in res)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((Support.Microsoft.FStar.Util.Inr (mk_t), m)) -> begin
(let t = (let _89_604 = (mk_t ())
in (compress_typ' _89_604))
in (let _25_744 = (Support.ST.op_Colon_Equals m (Some (t)))
in t))
end
| _25_747 -> begin
t
end)))
and compress_typ = (fun ( t ) -> (let t = (compress_typ' t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_25_751) -> begin
(Support.All.failwith "Impossible: compress returned a delayed type")
end
| _25_754 -> begin
t
end)))

let rec visit_exp = (fun ( s ) ( mk ) ( me ) ( ve ) ( ctrl ) ( binders ) ( e ) -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (_25_764) -> begin
(let _89_670 = (let _89_669 = (subst_exp' s e)
in (Support.All.pipe_left compress_exp _89_669))
in (_89_670, ctrl))
end
| _25_767 when (not (ctrl.descend)) -> begin
(map_exp s mk me ve ctrl binders e)
end
| _25_769 -> begin
(let _25_773 = (ve null_ctrl binders e)
in (match (_25_773) with
| (e, _25_772) -> begin
(e, ctrl)
end))
end)))
and compress_exp = (fun ( e ) -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed ((e', s, m)) -> begin
(let e = (let _89_699 = (Microsoft_FStar_Absyn_Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) Microsoft_FStar_Absyn_Visit.combine_kind Microsoft_FStar_Absyn_Visit.combine_typ Microsoft_FStar_Absyn_Visit.combine_exp subst_ctrl [] e')
in (Support.All.pipe_left Support.Prims.fst _89_699))
in (let res = (compress_exp e)
in (let _25_783 = (Support.ST.op_Colon_Equals m (Some (res)))
in res)))
end
| _25_786 -> begin
e
end)))

let rec unmeta_exp = (fun ( e ) -> (let e = (compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _25_791))) -> begin
(unmeta_exp e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _25_797, _25_799)) -> begin
(unmeta_exp e)
end
| _25_803 -> begin
e
end)))

let alpha_typ = (fun ( t ) -> (let t = (compress_typ t)
in (let s = (mk_subst [])
in (let doit = (fun ( t ) -> (let _89_724 = (Microsoft_FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) Microsoft_FStar_Absyn_Visit.combine_kind Microsoft_FStar_Absyn_Visit.combine_typ Microsoft_FStar_Absyn_Visit.combine_exp alpha_ctrl [] t)
in (Support.All.pipe_left Support.Prims.fst _89_724)))
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
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_25_819) -> begin
(doit t)
end
| _25_822 -> begin
t
end)))))

let formals_for_actuals = (fun ( formals ) ( actuals ) -> (Support.List.map2 (fun ( formal ) ( actual ) -> (match (((Support.Prims.fst formal), (Support.Prims.fst actual))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, b))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, y))
end
| _25_838 -> begin
(Support.All.failwith "Ill-typed substitution")
end)) formals actuals))

let compress_typ_opt = (fun ( _25_12 ) -> (match (_25_12) with
| None -> begin
None
end
| Some (t) -> begin
(let _89_731 = (compress_typ t)
in Some (_89_731))
end))

let mk_discriminator = (fun ( lid ) -> (let _89_736 = (let _89_735 = (let _89_734 = (Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.String.strcat "is_" lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText), lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idRange))
in (_89_734)::[])
in (Support.List.append lid.Microsoft_FStar_Absyn_Syntax.ns _89_735))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _89_736)))

let is_name = (fun ( lid ) -> (let c = (Support.Microsoft.FStar.Util.char_at lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText 0)
in (Support.Microsoft.FStar.Util.is_upper c)))

let ml_comp = (fun ( t ) ( r ) -> (let _89_744 = (let _89_743 = (set_lid_range Microsoft_FStar_Absyn_Const.effect_ML_lid r)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _89_743; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = []; Microsoft_FStar_Absyn_Syntax.flags = (Microsoft_FStar_Absyn_Syntax.MLEFFECT)::[]})
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _89_744)))

let total_comp = (fun ( t ) ( r ) -> (Microsoft_FStar_Absyn_Syntax.mk_Total t))

let gtotal_comp = (fun ( t ) -> (Microsoft_FStar_Absyn_Syntax.mk_Comp {Microsoft_FStar_Absyn_Syntax.effect_name = Microsoft_FStar_Absyn_Const.effect_GTot_lid; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = []; Microsoft_FStar_Absyn_Syntax.flags = (Microsoft_FStar_Absyn_Syntax.SOMETRIVIAL)::[]}))

let comp_set_flags = (fun ( c ) ( f ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_25_854) -> begin
c
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _25_858 = c
in {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp ((let _25_860 = ct
in {Microsoft_FStar_Absyn_Syntax.effect_name = _25_860.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _25_860.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _25_860.Microsoft_FStar_Absyn_Syntax.effect_args; Microsoft_FStar_Absyn_Syntax.flags = f})); Microsoft_FStar_Absyn_Syntax.tk = _25_858.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = _25_858.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _25_858.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _25_858.Microsoft_FStar_Absyn_Syntax.uvs})
end))

let comp_flags = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_25_864) -> begin
(Microsoft_FStar_Absyn_Syntax.TOTAL)::[]
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
ct.Microsoft_FStar_Absyn_Syntax.flags
end))

let comp_effect_name = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
c.Microsoft_FStar_Absyn_Syntax.effect_name
end
| Microsoft_FStar_Absyn_Syntax.Total (_25_872) -> begin
Microsoft_FStar_Absyn_Const.effect_Tot_lid
end))

let comp_to_comp_typ = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
c
end
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
{Microsoft_FStar_Absyn_Syntax.effect_name = Microsoft_FStar_Absyn_Const.effect_Tot_lid; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = []; Microsoft_FStar_Absyn_Syntax.flags = (Microsoft_FStar_Absyn_Syntax.TOTAL)::[]}
end))

let is_total_comp = (fun ( c ) -> (Support.All.pipe_right (comp_flags c) (Support.Microsoft.FStar.Util.for_some (fun ( _25_13 ) -> (match (_25_13) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _25_884 -> begin
false
end)))))

let is_total_lcomp = (fun ( c ) -> ((Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_Tot_lid) || (Support.All.pipe_right c.Microsoft_FStar_Absyn_Syntax.cflags (Support.Microsoft.FStar.Util.for_some (fun ( _25_14 ) -> (match (_25_14) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _25_890 -> begin
false
end))))))

let is_tot_or_gtot_lcomp = (fun ( c ) -> (((Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_Tot_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_GTot_lid)) || (Support.All.pipe_right c.Microsoft_FStar_Absyn_Syntax.cflags (Support.Microsoft.FStar.Util.for_some (fun ( _25_15 ) -> (match (_25_15) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _25_896 -> begin
false
end))))))

let is_partial_return = (fun ( c ) -> (Support.All.pipe_right (comp_flags c) (Support.Microsoft.FStar.Util.for_some (fun ( _25_16 ) -> (match (_25_16) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _25_902 -> begin
false
end)))))

let is_lcomp_partial_return = (fun ( c ) -> (Support.All.pipe_right c.Microsoft_FStar_Absyn_Syntax.cflags (Support.Microsoft.FStar.Util.for_some (fun ( _25_17 ) -> (match (_25_17) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _25_908 -> begin
false
end)))))

let is_tot_or_gtot_comp = (fun ( c ) -> ((is_total_comp c) || (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.effect_GTot_lid (comp_effect_name c))))

let is_pure_comp = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_25_912) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
((((is_tot_or_gtot_comp c) || (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_PURE_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Pure_lid)) || (Support.All.pipe_right ct.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _25_18 ) -> (match (_25_18) with
| Microsoft_FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _25_919 -> begin
false
end)))))
end))

let is_ghost_effect = (fun ( l ) -> (((Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.effect_GTot_lid l) || (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.effect_GHOST_lid l)) || (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.effect_Ghost_lid l)))

let is_pure_or_ghost_comp = (fun ( c ) -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))

let is_pure_lcomp = (fun ( lc ) -> ((((is_total_lcomp lc) || (Microsoft_FStar_Absyn_Syntax.lid_equals lc.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_PURE_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals lc.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_Pure_lid)) || (Support.All.pipe_right lc.Microsoft_FStar_Absyn_Syntax.cflags (Support.Microsoft.FStar.Util.for_some (fun ( _25_19 ) -> (match (_25_19) with
| Microsoft_FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _25_926 -> begin
false
end))))))

let is_pure_or_ghost_lcomp = (fun ( lc ) -> ((is_pure_lcomp lc) || (is_ghost_effect lc.Microsoft_FStar_Absyn_Syntax.eff_name)))

let is_pure_or_ghost_function = (fun ( t ) -> (match ((let _89_783 = (compress_typ t)
in _89_783.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((_25_930, c)) -> begin
(is_pure_or_ghost_comp c)
end
| _25_935 -> begin
true
end))

let is_lemma = (fun ( t ) -> (match ((let _89_786 = (compress_typ t)
in _89_786.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((_25_938, c)) -> begin
(match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Lemma_lid)
end
| _25_945 -> begin
false
end)
end
| _25_947 -> begin
false
end))

let is_smt_lemma = (fun ( t ) -> (match ((let _89_789 = (compress_typ t)
in _89_789.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((_25_950, c)) -> begin
(match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (ct) when (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Lemma_lid) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| _req::_ens::(Support.Microsoft.FStar.Util.Inr (pats), _25_961)::_25_957 -> begin
(match ((let _89_790 = (unmeta_exp pats)
in _89_790.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _25_978)); Microsoft_FStar_Absyn_Syntax.tk = _25_975; Microsoft_FStar_Absyn_Syntax.pos = _25_973; Microsoft_FStar_Absyn_Syntax.fvs = _25_971; Microsoft_FStar_Absyn_Syntax.uvs = _25_969}, _25_983)) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.cons_lid)
end
| _25_987 -> begin
false
end)
end
| _25_989 -> begin
false
end)
end
| _25_991 -> begin
false
end)
end
| _25_993 -> begin
false
end))

let is_ml_comp = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
((Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_ML_lid) || (Support.All.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _25_20 ) -> (match (_25_20) with
| Microsoft_FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _25_1000 -> begin
false
end)))))
end
| _25_1002 -> begin
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
| Microsoft_FStar_Absyn_Syntax.Total (_25_1011) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total t)
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Comp (let _25_1015 = ct
in {Microsoft_FStar_Absyn_Syntax.effect_name = _25_1015.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = _25_1015.Microsoft_FStar_Absyn_Syntax.effect_args; Microsoft_FStar_Absyn_Syntax.flags = _25_1015.Microsoft_FStar_Absyn_Syntax.flags}))
end))

let is_trivial_wp = (fun ( c ) -> (Support.All.pipe_right (comp_flags c) (Support.Microsoft.FStar.Util.for_some (fun ( _25_21 ) -> (match (_25_21) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _25_1022 -> begin
false
end)))))

let rec is_atom = (fun ( e ) -> (match ((let _89_800 = (compress_exp e)
in _89_800.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _25_1035))) -> begin
(is_atom e)
end
| _25_1040 -> begin
false
end))

let primops = (Microsoft_FStar_Absyn_Const.op_Eq)::(Microsoft_FStar_Absyn_Const.op_notEq)::(Microsoft_FStar_Absyn_Const.op_LT)::(Microsoft_FStar_Absyn_Const.op_LTE)::(Microsoft_FStar_Absyn_Const.op_GT)::(Microsoft_FStar_Absyn_Const.op_GTE)::(Microsoft_FStar_Absyn_Const.op_Subtraction)::(Microsoft_FStar_Absyn_Const.op_Minus)::(Microsoft_FStar_Absyn_Const.op_Addition)::(Microsoft_FStar_Absyn_Const.op_Multiply)::(Microsoft_FStar_Absyn_Const.op_Division)::(Microsoft_FStar_Absyn_Const.op_Modulus)::(Microsoft_FStar_Absyn_Const.op_And)::(Microsoft_FStar_Absyn_Const.op_Or)::(Microsoft_FStar_Absyn_Const.op_Negation)::[]

let is_primop = (fun ( f ) -> (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _25_1044)) -> begin
(Support.All.pipe_right primops (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v)))
end
| _25_1048 -> begin
false
end))

let rec unascribe = (fun ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _25_1052, _25_1054)) -> begin
(unascribe e)
end
| _25_1058 -> begin
e
end))

let rec ascribe_typ = (fun ( t ) ( k ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t', _25_1063)) -> begin
(ascribe_typ t' k)
end
| _25_1067 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.Microsoft_FStar_Absyn_Syntax.pos)
end))

let rec unascribe_typ = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _25_1071)) -> begin
(unascribe_typ t)
end
| _25_1075 -> begin
t
end))

let rec unrefine = (fun ( t ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _25_1080)) -> begin
(unrefine x.Microsoft_FStar_Absyn_Syntax.sort)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _25_1085)) -> begin
(unrefine t)
end
| _25_1089 -> begin
t
end)))

let is_fun = (fun ( e ) -> (match ((let _89_814 = (compress_exp e)
in _89_814.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_abs (_25_1092) -> begin
true
end
| _25_1095 -> begin
false
end))

let is_function_typ = (fun ( t ) -> (match ((let _89_817 = (compress_typ t)
in _89_817.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_25_1098) -> begin
true
end
| _25_1101 -> begin
false
end))

let rec pre_typ = (fun ( t ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _25_1106)) -> begin
(pre_typ x.Microsoft_FStar_Absyn_Syntax.sort)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _25_1111)) -> begin
(pre_typ t)
end
| _25_1115 -> begin
t
end)))

let destruct = (fun ( typ ) ( lid ) -> (let typ = (compress_typ typ)
in (match (typ.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _25_1126; Microsoft_FStar_Absyn_Syntax.pos = _25_1124; Microsoft_FStar_Absyn_Syntax.fvs = _25_1122; Microsoft_FStar_Absyn_Syntax.uvs = _25_1120}, args)) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v lid) -> begin
Some (args)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v lid) -> begin
Some ([])
end
| _25_1136 -> begin
None
end)))

let rec lids_of_sigelt = (fun ( se ) -> (match (se) with
| (Microsoft_FStar_Absyn_Syntax.Sig_let ((_, _, lids, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_bundle ((_, _, lids, _))) -> begin
lids
end
| (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, _, _, _, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, _, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, _, _, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, _, _, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((lid, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, _, _, _))) -> begin
(lid)::[]
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((n, _25_1230)) -> begin
(n.Microsoft_FStar_Absyn_Syntax.mname)::[]
end
| (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_main (_)) -> begin
[]
end))

let lid_of_sigelt = (fun ( se ) -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _25_1246 -> begin
None
end))

let range_of_sigelt = (fun ( x ) -> (match (x) with
| (Microsoft_FStar_Absyn_Syntax.Sig_bundle ((_, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_, _, _, _, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((_, _, _, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((_, _, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_, _, _, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_assume ((_, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_let ((_, r, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_main ((_, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_pragma ((_, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((_, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((_, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect ((_, r))) -> begin
r
end))

let range_of_lb = (fun ( _25_22 ) -> (match (_25_22) with
| (Support.Microsoft.FStar.Util.Inl (x), _25_1357, _25_1359) -> begin
(range_of_bvd x)
end
| (Support.Microsoft.FStar.Util.Inr (l), _25_1364, _25_1366) -> begin
(Microsoft_FStar_Absyn_Syntax.range_of_lid l)
end))

let range_of_arg = (fun ( _25_23 ) -> (match (_25_23) with
| (Support.Microsoft.FStar.Util.Inl (hd), _25_1372) -> begin
hd.Microsoft_FStar_Absyn_Syntax.pos
end
| (Support.Microsoft.FStar.Util.Inr (hd), _25_1377) -> begin
hd.Microsoft_FStar_Absyn_Syntax.pos
end))

let range_of_args = (fun ( args ) ( r ) -> (Support.All.pipe_right args (Support.List.fold_left (fun ( r ) ( a ) -> (Support.Microsoft.FStar.Range.union_ranges r (range_of_arg a))) r)))

let mk_typ_app = (fun ( f ) ( args ) -> (let r = (range_of_args args f.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (f, args) None r)))

let mk_exp_app = (fun ( f ) ( args ) -> (let r = (range_of_args args f.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (f, args) None r)))

let mk_data = (fun ( l ) ( args ) -> (match (args) with
| [] -> begin
(let _89_851 = (let _89_850 = (let _89_849 = (let _89_848 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) l _89_848))
in (_89_849, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_89_850))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _89_851))
end
| _25_1393 -> begin
(let _89_856 = (let _89_855 = (let _89_854 = (let _89_853 = (let _89_852 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) l _89_852))
in (mk_exp_app _89_853 args))
in (_89_854, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_89_855))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _89_856))
end))

let mangle_field_name = (fun ( x ) -> (Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.String.strcat "^fname^" x.Microsoft_FStar_Absyn_Syntax.idText), x.Microsoft_FStar_Absyn_Syntax.idRange)))

let unmangle_field_name = (fun ( x ) -> (match ((Support.Microsoft.FStar.Util.starts_with x.Microsoft_FStar_Absyn_Syntax.idText "^fname^")) with
| true -> begin
(let _89_862 = (let _89_861 = (Support.Microsoft.FStar.Util.substring_from x.Microsoft_FStar_Absyn_Syntax.idText 7)
in (_89_861, x.Microsoft_FStar_Absyn_Syntax.idRange))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _89_862))
end
| false -> begin
x
end))

let mk_field_projector_name = (fun ( lid ) ( x ) ( i ) -> (let nm = (match ((Microsoft_FStar_Absyn_Syntax.is_null_bvar x)) with
| true -> begin
(let _89_868 = (let _89_867 = (let _89_866 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.String.strcat "_" _89_866))
in (_89_867, x.Microsoft_FStar_Absyn_Syntax.p))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _89_868))
end
| false -> begin
x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname
end)
in (let y = (let _25_1402 = x.Microsoft_FStar_Absyn_Syntax.v
in {Microsoft_FStar_Absyn_Syntax.ppname = nm; Microsoft_FStar_Absyn_Syntax.realname = _25_1402.Microsoft_FStar_Absyn_Syntax.realname})
in (let _89_873 = (let _89_872 = (let _89_871 = (Microsoft_FStar_Absyn_Syntax.ids_of_lid lid)
in (let _89_870 = (let _89_869 = (unmangle_field_name nm)
in (_89_869)::[])
in (Support.List.append _89_871 _89_870)))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _89_872))
in (_89_873, y)))))

let unchecked_unify = (fun ( uv ) ( t ) -> (match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (_25_1408) -> begin
(let _89_878 = (let _89_877 = (let _89_876 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.All.pipe_left Support.Microsoft.FStar.Util.string_of_int _89_876))
in (Support.Microsoft.FStar.Util.format1 "Changing a fixed uvar! U%s\n" _89_877))
in (Support.All.failwith _89_878))
end
| _25_1411 -> begin
(Support.Microsoft.FStar.Unionfind.change uv (Microsoft_FStar_Absyn_Syntax.Fixed (t)))
end))

type bvars =
(Microsoft_FStar_Absyn_Syntax.btvar Support.Microsoft.FStar.Util.set * Microsoft_FStar_Absyn_Syntax.bvvar Support.Microsoft.FStar.Util.set)

let no_bvars = (Microsoft_FStar_Absyn_Syntax.no_fvs.Microsoft_FStar_Absyn_Syntax.ftvs, Microsoft_FStar_Absyn_Syntax.no_fvs.Microsoft_FStar_Absyn_Syntax.fxvs)

let fvs_included = (fun ( fvs1 ) ( fvs2 ) -> ((Support.Microsoft.FStar.Util.set_is_subset_of fvs1.Microsoft_FStar_Absyn_Syntax.ftvs fvs2.Microsoft_FStar_Absyn_Syntax.ftvs) && (Support.Microsoft.FStar.Util.set_is_subset_of fvs1.Microsoft_FStar_Absyn_Syntax.fxvs fvs2.Microsoft_FStar_Absyn_Syntax.fxvs)))

let eq_fvars = (fun ( v1 ) ( v2 ) -> (match ((v1, v2)) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq a b)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| _25_1427 -> begin
false
end))

let eq_binder = (fun ( b1 ) ( b2 ) -> (match (((Support.Prims.fst b1), (Support.Prims.fst b2))) with
| (Support.Microsoft.FStar.Util.Inl (x), Support.Microsoft.FStar.Util.Inl (y)) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| _25_1441 -> begin
false
end))

let uv_eq = (fun ( _25_1445 ) ( _25_1449 ) -> (match ((_25_1445, _25_1449)) with
| ((uv1, _25_1444), (uv2, _25_1448)) -> begin
(Support.Microsoft.FStar.Unionfind.equivalent uv1 uv2)
end))

let union_uvs = (fun ( uvs1 ) ( uvs2 ) -> (let _89_907 = (Support.Microsoft.FStar.Util.set_union uvs1.Microsoft_FStar_Absyn_Syntax.uvars_k uvs2.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (let _89_906 = (Support.Microsoft.FStar.Util.set_union uvs1.Microsoft_FStar_Absyn_Syntax.uvars_t uvs2.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (let _89_905 = (Support.Microsoft.FStar.Util.set_union uvs1.Microsoft_FStar_Absyn_Syntax.uvars_e uvs2.Microsoft_FStar_Absyn_Syntax.uvars_e)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _89_907; Microsoft_FStar_Absyn_Syntax.uvars_t = _89_906; Microsoft_FStar_Absyn_Syntax.uvars_e = _89_905}))))

let union_fvs = (fun ( fvs1 ) ( fvs2 ) -> (let _89_913 = (Support.Microsoft.FStar.Util.set_union fvs1.Microsoft_FStar_Absyn_Syntax.ftvs fvs2.Microsoft_FStar_Absyn_Syntax.ftvs)
in (let _89_912 = (Support.Microsoft.FStar.Util.set_union fvs1.Microsoft_FStar_Absyn_Syntax.fxvs fvs2.Microsoft_FStar_Absyn_Syntax.fxvs)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _89_913; Microsoft_FStar_Absyn_Syntax.fxvs = _89_912})))

let union_fvs_uvs = (fun ( _25_1456 ) ( _25_1459 ) -> (match ((_25_1456, _25_1459)) with
| ((fvs1, uvs1), (fvs2, uvs2)) -> begin
(let _89_919 = (union_fvs fvs1 fvs2)
in (let _89_918 = (union_uvs uvs1 uvs2)
in (_89_919, _89_918)))
end))

let sub_fv = (fun ( _25_1462 ) ( _25_1465 ) -> (match ((_25_1462, _25_1465)) with
| ((fvs, uvs), (tvars, vvars)) -> begin
(let _89_940 = (let _25_1466 = fvs
in (let _89_939 = (Support.Microsoft.FStar.Util.set_difference fvs.Microsoft_FStar_Absyn_Syntax.ftvs tvars)
in (let _89_938 = (Support.Microsoft.FStar.Util.set_difference fvs.Microsoft_FStar_Absyn_Syntax.fxvs vvars)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _89_939; Microsoft_FStar_Absyn_Syntax.fxvs = _89_938})))
in (_89_940, uvs))
end))

let stash = (fun ( uvonly ) ( s ) ( _25_1474 ) -> (match (_25_1474) with
| (fvs, uvs) -> begin
(let _25_1475 = (Support.ST.op_Colon_Equals s.Microsoft_FStar_Absyn_Syntax.uvs (Some (uvs)))
in (match (uvonly) with
| true -> begin
()
end
| false -> begin
(Support.ST.op_Colon_Equals s.Microsoft_FStar_Absyn_Syntax.fvs (Some (fvs)))
end))
end))

let single_fv = (fun ( x ) -> (let _89_951 = (Microsoft_FStar_Absyn_Syntax.new_ftv_set ())
in (Support.Microsoft.FStar.Util.set_add x _89_951)))

let single_uv = (fun ( u ) -> (let _89_959 = (Microsoft_FStar_Absyn_Syntax.new_uv_set ())
in (Support.Microsoft.FStar.Util.set_add u _89_959)))

let single_uvt = (fun ( u ) -> (let _89_967 = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ())
in (Support.Microsoft.FStar.Util.set_add u _89_967)))

let rec vs_typ' = (fun ( t ) ( uvonly ) ( cont ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_25_1486) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| false -> begin
(let _89_1082 = (let _89_1081 = (let _25_1490 = Microsoft_FStar_Absyn_Syntax.no_fvs
in (let _89_1080 = (single_fv a)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _89_1080; Microsoft_FStar_Absyn_Syntax.fxvs = _25_1490.Microsoft_FStar_Absyn_Syntax.fxvs}))
in (_89_1081, Microsoft_FStar_Absyn_Syntax.no_uvs))
in (cont _89_1082))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(let _89_1085 = (let _89_1084 = (let _25_1496 = Microsoft_FStar_Absyn_Syntax.no_uvs
in (let _89_1083 = (single_uvt (uv, k))
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _25_1496.Microsoft_FStar_Absyn_Syntax.uvars_k; Microsoft_FStar_Absyn_Syntax.uvars_t = _89_1083; Microsoft_FStar_Absyn_Syntax.uvars_e = _25_1496.Microsoft_FStar_Absyn_Syntax.uvars_e}))
in (Microsoft_FStar_Absyn_Syntax.no_fvs, _89_1084))
in (cont _89_1085))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(vs_binders bs uvonly (fun ( _25_1508 ) -> (match (_25_1508) with
| (bvs, vs1) -> begin
(vs_comp c uvonly (fun ( vs2 ) -> (let _89_1089 = (let _89_1088 = (union_fvs_uvs vs1 vs2)
in (sub_fv _89_1088 bvs))
in (cont _89_1089))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(vs_binders bs uvonly (fun ( _25_1516 ) -> (match (_25_1516) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun ( vs2 ) -> (let _89_1093 = (let _89_1092 = (union_fvs_uvs vs1 vs2)
in (sub_fv _89_1092 bvs))
in (cont _89_1093))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, t)) -> begin
(vs_binders (((Support.Microsoft.FStar.Util.Inr (x), None))::[]) uvonly (fun ( _25_1524 ) -> (match (_25_1524) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun ( vs2 ) -> (let _89_1097 = (let _89_1096 = (union_fvs_uvs vs1 vs2)
in (sub_fv _89_1096 bvs))
in (cont _89_1097))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, args)) -> begin
(vs_typ t uvonly (fun ( vs1 ) -> (vs_args args uvonly (fun ( vs2 ) -> (let _89_1100 = (union_fvs_uvs vs1 vs2)
in (cont _89_1100))))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _25_1534)) -> begin
(vs_typ t uvonly cont)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, _25_1540))) -> begin
(vs_typ t1 uvonly (fun ( vs1 ) -> (vs_typ t2 uvonly (fun ( vs2 ) -> (let _89_1103 = (union_fvs_uvs vs1 vs2)
in (cont _89_1103))))))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, _, _, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, _)))) -> begin
(vs_typ t uvonly cont)
end)))
and vs_binders = (fun ( bs ) ( uvonly ) ( cont ) -> (match (bs) with
| [] -> begin
(cont (no_bvars, (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs)))
end
| (Support.Microsoft.FStar.Util.Inl (a), _25_1582)::rest -> begin
(vs_kind a.Microsoft_FStar_Absyn_Syntax.sort uvonly (fun ( vs ) -> (vs_binders rest uvonly (fun ( _25_1590 ) -> (match (_25_1590) with
| ((tvars, vvars), vs2) -> begin
(let _89_1140 = (let _89_1139 = (let _89_1137 = (Support.Microsoft.FStar.Util.set_add a tvars)
in (_89_1137, vvars))
in (let _89_1138 = (union_fvs_uvs vs vs2)
in (_89_1139, _89_1138)))
in (cont _89_1140))
end)))))
end
| (Support.Microsoft.FStar.Util.Inr (x), _25_1595)::rest -> begin
(vs_typ x.Microsoft_FStar_Absyn_Syntax.sort uvonly (fun ( vs ) -> (vs_binders rest uvonly (fun ( _25_1603 ) -> (match (_25_1603) with
| ((tvars, vvars), vs2) -> begin
(let _89_1164 = (let _89_1163 = (let _89_1161 = (Support.Microsoft.FStar.Util.set_add x vvars)
in (tvars, _89_1161))
in (let _89_1162 = (union_fvs_uvs vs vs2)
in (_89_1163, _89_1162)))
in (cont _89_1164))
end)))))
end))
and vs_args = (fun ( args ) ( uvonly ) ( cont ) -> (match (args) with
| [] -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| (Support.Microsoft.FStar.Util.Inl (t), _25_1613)::tl -> begin
(vs_typ t uvonly (fun ( ft1 ) -> (vs_args tl uvonly (fun ( ft2 ) -> (let _89_1168 = (union_fvs_uvs ft1 ft2)
in (cont _89_1168))))))
end
| (Support.Microsoft.FStar.Util.Inr (e), _25_1622)::tl -> begin
(vs_exp e uvonly (fun ( ft1 ) -> (vs_args tl uvonly (fun ( ft2 ) -> (let _89_1171 = (union_fvs_uvs ft1 ft2)
in (cont _89_1171))))))
end))
and vs_typ = (fun ( t ) ( uvonly ) ( cont ) -> (match ((let _89_1174 = (Support.ST.read t.Microsoft_FStar_Absyn_Syntax.fvs)
in (let _89_1173 = (Support.ST.read t.Microsoft_FStar_Absyn_Syntax.uvs)
in (_89_1174, _89_1173)))) with
| (Some (_25_1632), None) -> begin
(Support.All.failwith "Impossible")
end
| (None, None) -> begin
(vs_typ' t uvonly (fun ( fvs ) -> (let _25_1640 = (stash uvonly t fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, uvs))
end
| false -> begin
(vs_typ' t uvonly (fun ( fvs ) -> (let _25_1647 = (stash uvonly t fvs)
in (cont fvs))))
end)
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_kind' = (fun ( k ) ( uvonly ) ( cont ) -> (let k = (compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam ((_25_1660, k)) -> begin
(let _89_1179 = (let _89_1178 = (Support.Microsoft.FStar.Range.string_of_range k.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Microsoft.FStar.Util.format1 "%s: Impossible ... found a Kind_lam bare" _89_1178))
in (Support.All.failwith _89_1179))
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_25_1665) -> begin
(Support.All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Kind_unknown) | (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, args)) -> begin
(vs_args args uvonly (fun ( _25_1676 ) -> (match (_25_1676) with
| (fvs, uvs) -> begin
(let _89_1183 = (let _89_1182 = (let _25_1677 = uvs
in (let _89_1181 = (Support.Microsoft.FStar.Util.set_add uv uvs.Microsoft_FStar_Absyn_Syntax.uvars_k)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _89_1181; Microsoft_FStar_Absyn_Syntax.uvars_t = _25_1677.Microsoft_FStar_Absyn_Syntax.uvars_t; Microsoft_FStar_Absyn_Syntax.uvars_e = _25_1677.Microsoft_FStar_Absyn_Syntax.uvars_e}))
in (fvs, _89_1182))
in (cont _89_1183))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_25_1680, k)) -> begin
(vs_kind k uvonly cont)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(vs_binders bs uvonly (fun ( _25_1690 ) -> (match (_25_1690) with
| (bvs, vs1) -> begin
(vs_kind k uvonly (fun ( vs2 ) -> (let _89_1187 = (let _89_1186 = (union_fvs_uvs vs1 vs2)
in (sub_fv _89_1186 bvs))
in (cont _89_1187))))
end)))
end)))
and vs_kind = (fun ( k ) ( uvonly ) ( cont ) -> (match ((let _89_1190 = (Support.ST.read k.Microsoft_FStar_Absyn_Syntax.fvs)
in (let _89_1189 = (Support.ST.read k.Microsoft_FStar_Absyn_Syntax.uvs)
in (_89_1190, _89_1189)))) with
| (Some (_25_1697), None) -> begin
(Support.All.failwith "Impossible")
end
| (None, None) -> begin
(vs_kind' k uvonly (fun ( fvs ) -> (let _25_1705 = (stash uvonly k fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, uvs))
end
| false -> begin
(vs_kind' k uvonly (fun ( fvs ) -> (let _25_1712 = (stash uvonly k fvs)
in (cont fvs))))
end)
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_exp' = (fun ( e ) ( uvonly ) ( cont ) -> (let e = (compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_25_1725) -> begin
(Support.All.failwith "impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, t)) -> begin
(let _89_1196 = (let _89_1195 = (let _25_1737 = Microsoft_FStar_Absyn_Syntax.no_uvs
in (let _89_1194 = (single_uvt (uv, t))
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _25_1737.Microsoft_FStar_Absyn_Syntax.uvars_k; Microsoft_FStar_Absyn_Syntax.uvars_t = _25_1737.Microsoft_FStar_Absyn_Syntax.uvars_t; Microsoft_FStar_Absyn_Syntax.uvars_e = _89_1194}))
in (Microsoft_FStar_Absyn_Syntax.no_fvs, _89_1195))
in (cont _89_1196))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| false -> begin
(let _89_1199 = (let _89_1198 = (let _25_1741 = Microsoft_FStar_Absyn_Syntax.no_fvs
in (let _89_1197 = (single_fv x)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _25_1741.Microsoft_FStar_Absyn_Syntax.ftvs; Microsoft_FStar_Absyn_Syntax.fxvs = _89_1197}))
in (_89_1198, Microsoft_FStar_Absyn_Syntax.no_uvs))
in (cont _89_1199))
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _25_1745, _25_1747)) -> begin
(vs_exp e uvonly cont)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, e)) -> begin
(vs_binders bs uvonly (fun ( _25_1756 ) -> (match (_25_1756) with
| (bvs, vs1) -> begin
(vs_exp e uvonly (fun ( vs2 ) -> (let _89_1203 = (let _89_1202 = (union_fvs_uvs vs1 vs2)
in (sub_fv _89_1202 bvs))
in (cont _89_1203))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((e, args)) -> begin
(vs_exp e uvonly (fun ( ft1 ) -> (vs_args args uvonly (fun ( ft2 ) -> (let _89_1206 = (union_fvs_uvs ft1 ft2)
in (cont _89_1206))))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_match (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_let (_)) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _25_1772))) -> begin
(vs_exp e uvonly cont)
end)))
and vs_exp = (fun ( e ) ( uvonly ) ( cont ) -> (match ((let _89_1209 = (Support.ST.read e.Microsoft_FStar_Absyn_Syntax.fvs)
in (let _89_1208 = (Support.ST.read e.Microsoft_FStar_Absyn_Syntax.uvs)
in (_89_1209, _89_1208)))) with
| (Some (_25_1781), None) -> begin
(Support.All.failwith "Impossible")
end
| (None, None) -> begin
(vs_exp' e uvonly (fun ( fvs ) -> (let _25_1789 = (stash uvonly e fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, uvs))
end
| false -> begin
(vs_exp' e uvonly (fun ( fvs ) -> (let _25_1796 = (stash uvonly e fvs)
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
(vs_typ ct.Microsoft_FStar_Absyn_Syntax.result_typ uvonly (fun ( vs1 ) -> (vs_args ct.Microsoft_FStar_Absyn_Syntax.effect_args uvonly (fun ( vs2 ) -> (let _89_1215 = (union_fvs_uvs vs1 vs2)
in (k _89_1215))))))
end)
end))
and vs_comp = (fun ( c ) ( uvonly ) ( cont ) -> (match ((let _89_1218 = (Support.ST.read c.Microsoft_FStar_Absyn_Syntax.fvs)
in (let _89_1217 = (Support.ST.read c.Microsoft_FStar_Absyn_Syntax.uvs)
in (_89_1218, _89_1217)))) with
| (Some (_25_1818), None) -> begin
(Support.All.failwith "Impossible")
end
| (None, None) -> begin
(vs_comp' c uvonly (fun ( fvs ) -> (let _25_1826 = (stash uvonly c fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, uvs))
end
| false -> begin
(vs_comp' c uvonly (fun ( fvs ) -> (let _25_1833 = (stash uvonly c fvs)
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
(vs_either hd uvonly (fun ( ft1 ) -> (vs_either_l tl uvonly (fun ( ft2 ) -> (let _89_1225 = (union_fvs_uvs ft1 ft2)
in (cont _89_1225))))))
end))

let freevars_kind = (fun ( k ) -> (vs_kind k false (fun ( _25_1862 ) -> (match (_25_1862) with
| (x, _25_1861) -> begin
x
end))))

let freevars_typ = (fun ( t ) -> (vs_typ t false (fun ( _25_1867 ) -> (match (_25_1867) with
| (x, _25_1866) -> begin
x
end))))

let freevars_exp = (fun ( e ) -> (vs_exp e false (fun ( _25_1872 ) -> (match (_25_1872) with
| (x, _25_1871) -> begin
x
end))))

let freevars_comp = (fun ( c ) -> (vs_comp c false (fun ( _25_1877 ) -> (match (_25_1877) with
| (x, _25_1876) -> begin
x
end))))

let freevars_args = (fun ( args ) -> (Support.All.pipe_right args (Support.List.fold_left (fun ( out ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _89_1241 = (freevars_typ t)
in (Support.All.pipe_left (union_fvs out) _89_1241))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _89_1242 = (freevars_exp e)
in (Support.All.pipe_left (union_fvs out) _89_1242))
end)) Microsoft_FStar_Absyn_Syntax.no_fvs)))

let is_free = (fun ( axs ) ( fvs ) -> (Support.All.pipe_right axs (Support.Microsoft.FStar.Util.for_some (fun ( _25_24 ) -> (match (_25_24) with
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

let ___SynSumKind____0 = (fun ( projectee ) -> (match (projectee) with
| SynSumKind (_25_1894) -> begin
_25_1894
end))

let ___SynSumType____0 = (fun ( projectee ) -> (match (projectee) with
| SynSumType (_25_1897) -> begin
_25_1897
end))

let ___SynSumExp____0 = (fun ( projectee ) -> (match (projectee) with
| SynSumExp (_25_1900) -> begin
_25_1900
end))

let ___SynSumComp____0 = (fun ( projectee ) -> (match (projectee) with
| SynSumComp (_25_1903) -> begin
_25_1903
end))

let rec update_uvars = (fun ( s ) ( uvs ) -> (let out = (let _89_1316 = (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (Support.All.pipe_right _89_1316 (Support.List.fold_left (fun ( out ) ( u ) -> (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (k) -> begin
(let _89_1314 = (uvars_in_kind k)
in (union_uvs _89_1314 out))
end
| _25_1911 -> begin
(let _25_1912 = out
in (let _89_1315 = (Support.Microsoft.FStar.Util.set_add u out.Microsoft_FStar_Absyn_Syntax.uvars_k)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _89_1315; Microsoft_FStar_Absyn_Syntax.uvars_t = _25_1912.Microsoft_FStar_Absyn_Syntax.uvars_t; Microsoft_FStar_Absyn_Syntax.uvars_e = _25_1912.Microsoft_FStar_Absyn_Syntax.uvars_e}))
end)) Microsoft_FStar_Absyn_Syntax.no_uvs)))
in (let out = (let _89_1321 = (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.All.pipe_right _89_1321 (Support.List.fold_left (fun ( out ) ( _25_1918 ) -> (match (_25_1918) with
| (u, t) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (t) -> begin
(let _89_1319 = (uvars_in_typ t)
in (union_uvs _89_1319 out))
end
| _25_1922 -> begin
(let _25_1923 = out
in (let _89_1320 = (Support.Microsoft.FStar.Util.set_add (u, t) out.Microsoft_FStar_Absyn_Syntax.uvars_t)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _25_1923.Microsoft_FStar_Absyn_Syntax.uvars_k; Microsoft_FStar_Absyn_Syntax.uvars_t = _89_1320; Microsoft_FStar_Absyn_Syntax.uvars_e = _25_1923.Microsoft_FStar_Absyn_Syntax.uvars_e}))
end)
end)) out)))
in (let out = (let _89_1326 = (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (Support.All.pipe_right _89_1326 (Support.List.fold_left (fun ( out ) ( _25_1929 ) -> (match (_25_1929) with
| (u, t) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (e) -> begin
(let _89_1324 = (uvars_in_exp e)
in (union_uvs _89_1324 out))
end
| _25_1933 -> begin
(let _25_1934 = out
in (let _89_1325 = (Support.Microsoft.FStar.Util.set_add (u, t) out.Microsoft_FStar_Absyn_Syntax.uvars_e)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _25_1934.Microsoft_FStar_Absyn_Syntax.uvars_k; Microsoft_FStar_Absyn_Syntax.uvars_t = _25_1934.Microsoft_FStar_Absyn_Syntax.uvars_t; Microsoft_FStar_Absyn_Syntax.uvars_e = _89_1325}))
end)
end)) out)))
in (let _25_1945 = (match (s) with
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
and uvars_in_kind = (fun ( k ) -> (let _89_1329 = (vs_kind k true (fun ( _25_1951 ) -> (match (_25_1951) with
| (_25_1949, x) -> begin
x
end)))
in (Support.All.pipe_left (update_uvars (SynSumKind (k))) _89_1329)))
and uvars_in_typ = (fun ( t ) -> (let _89_1332 = (vs_typ t true (fun ( _25_1956 ) -> (match (_25_1956) with
| (_25_1954, x) -> begin
x
end)))
in (Support.All.pipe_left (update_uvars (SynSumType (t))) _89_1332)))
and uvars_in_exp = (fun ( e ) -> (let _89_1335 = (vs_exp e true (fun ( _25_1961 ) -> (match (_25_1961) with
| (_25_1959, x) -> begin
x
end)))
in (Support.All.pipe_left (update_uvars (SynSumExp (e))) _89_1335)))
and uvars_in_comp = (fun ( c ) -> (let _89_1338 = (vs_comp c true (fun ( _25_1966 ) -> (match (_25_1966) with
| (_25_1964, x) -> begin
x
end)))
in (Support.All.pipe_left (update_uvars (SynSumComp (c))) _89_1338)))

let uvars_included_in = (fun ( u1 ) ( u2 ) -> (((Support.Microsoft.FStar.Util.set_is_subset_of u1.Microsoft_FStar_Absyn_Syntax.uvars_k u2.Microsoft_FStar_Absyn_Syntax.uvars_k) && (Support.Microsoft.FStar.Util.set_is_subset_of u1.Microsoft_FStar_Absyn_Syntax.uvars_t u2.Microsoft_FStar_Absyn_Syntax.uvars_t)) && (Support.Microsoft.FStar.Util.set_is_subset_of u1.Microsoft_FStar_Absyn_Syntax.uvars_e u2.Microsoft_FStar_Absyn_Syntax.uvars_e)))

let rec kind_formals = (fun ( k ) -> (let k = (compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam (_25_1972) -> begin
(Support.All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Kind_unknown) | (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) | (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
([], k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _25_1986 = (kind_formals k)
in (match (_25_1986) with
| (bs', k) -> begin
((Support.List.append bs bs'), k)
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_25_1988, k)) -> begin
(kind_formals k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_25_1993) -> begin
(Support.All.failwith "Impossible")
end)))

let close_for_kind = (fun ( t ) ( k ) -> (let _25_2000 = (kind_formals k)
in (match (_25_2000) with
| (bs, _25_1999) -> begin
(match (bs) with
| [] -> begin
t
end
| _25_2003 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.Microsoft_FStar_Absyn_Syntax.pos)
end)
end)))

let rec unabbreviate_kind = (fun ( k ) -> (let k = (compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_25_2007, k)) -> begin
(unabbreviate_kind k)
end
| _25_2012 -> begin
k
end)))

let close_with_lam = (fun ( tps ) ( t ) -> (match (tps) with
| [] -> begin
t
end
| _25_2017 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (tps, t) None t.Microsoft_FStar_Absyn_Syntax.pos)
end))

let close_with_arrow = (fun ( tps ) ( t ) -> (match (tps) with
| [] -> begin
t
end
| _25_2022 -> begin
(let _25_2031 = (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs', c)) -> begin
((Support.List.append tps bs'), c)
end
| _25_2028 -> begin
(let _89_1359 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (tps, _89_1359))
end)
in (match (_25_2031) with
| (bs, c) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.Microsoft_FStar_Absyn_Syntax.pos)
end))
end))

let close_typ = close_with_arrow

let close_kind = (fun ( tps ) ( k ) -> (match (tps) with
| [] -> begin
k
end
| _25_2036 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow' (tps, k) k.Microsoft_FStar_Absyn_Syntax.pos)
end))

let is_tuple_constructor = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (l) -> begin
(Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str "Prims.Tuple")
end
| _25_2041 -> begin
false
end))

let mk_tuple_lid = (fun ( n ) ( r ) -> (let t = (let _89_1372 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "Tuple%s" _89_1372))
in (let _89_1373 = (Microsoft_FStar_Absyn_Const.pconst t)
in (set_lid_range _89_1373 r))))

let mk_tuple_data_lid = (fun ( n ) ( r ) -> (let t = (let _89_1378 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "MkTuple%s" _89_1378))
in (let _89_1379 = (Microsoft_FStar_Absyn_Const.pconst t)
in (set_lid_range _89_1379 r))))

let is_tuple_data_lid = (fun ( f ) ( n ) -> (let _89_1384 = (mk_tuple_data_lid n Microsoft_FStar_Absyn_Syntax.dummyRange)
in (Microsoft_FStar_Absyn_Syntax.lid_equals f _89_1384)))

let is_dtuple_constructor = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (l) -> begin
(Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str "Prims.DTuple")
end
| _25_2054 -> begin
false
end))

let mk_dtuple_lid = (fun ( n ) ( r ) -> (let t = (let _89_1391 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "DTuple%s" _89_1391))
in (let _89_1392 = (Microsoft_FStar_Absyn_Const.pconst t)
in (set_lid_range _89_1392 r))))

let mk_dtuple_data_lid = (fun ( n ) ( r ) -> (let t = (let _89_1397 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "MkDTuple%s" _89_1397))
in (let _89_1398 = (Microsoft_FStar_Absyn_Const.pconst t)
in (set_lid_range _89_1398 r))))

let is_lid_equality = (fun ( x ) -> ((((Microsoft_FStar_Absyn_Syntax.lid_equals x Microsoft_FStar_Absyn_Const.eq_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals x Microsoft_FStar_Absyn_Const.eq2_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals x Microsoft_FStar_Absyn_Const.eqA_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals x Microsoft_FStar_Absyn_Const.eqT_lid)))

let is_forall = (fun ( lid ) -> ((Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.forall_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.allTyp_lid)))

let is_exists = (fun ( lid ) -> ((Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.exists_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.exTyp_lid)))

let is_qlid = (fun ( lid ) -> ((is_forall lid) || (is_exists lid)))

let is_equality = (fun ( x ) -> (is_lid_equality x.Microsoft_FStar_Absyn_Syntax.v))

let lid_is_connective = (let lst = (Microsoft_FStar_Absyn_Const.and_lid)::(Microsoft_FStar_Absyn_Const.or_lid)::(Microsoft_FStar_Absyn_Const.not_lid)::(Microsoft_FStar_Absyn_Const.iff_lid)::(Microsoft_FStar_Absyn_Const.imp_lid)::[]
in (fun ( lid ) -> (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals lid) lst)))

let is_constructor = (fun ( t ) ( lid ) -> (match ((let _89_1414 = (pre_typ t)
in _89_1414.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v lid)
end
| _25_2073 -> begin
false
end))

let rec is_constructed_typ = (fun ( t ) ( lid ) -> (match ((let _89_1419 = (pre_typ t)
in _89_1419.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (_25_2077) -> begin
(is_constructor t lid)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, _25_2081)) -> begin
(is_constructed_typ t lid)
end
| _25_2085 -> begin
false
end))

let rec get_tycon = (fun ( t ) -> (let t = (pre_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) -> begin
Some (t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, _25_2096)) -> begin
(get_tycon t)
end
| _25_2100 -> begin
None
end)))

let base_kind = (fun ( _25_25 ) -> (match (_25_25) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
true
end
| _25_2104 -> begin
false
end))

let sortByFieldName = (fun ( fn_a_l ) -> (Support.All.pipe_right fn_a_l (Support.List.sortWith (fun ( _25_2110 ) ( _25_2114 ) -> (match ((_25_2110, _25_2114)) with
| ((fn1, _25_2109), (fn2, _25_2113)) -> begin
(let _89_1428 = (Microsoft_FStar_Absyn_Syntax.text_of_lid fn1)
in (let _89_1427 = (Microsoft_FStar_Absyn_Syntax.text_of_lid fn2)
in (Support.String.compare _89_1428 _89_1427)))
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

let b2t_v = (let _89_1432 = (let _89_1431 = (let _89_1430 = (let _89_1429 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.null_v_binder t_bool)
in (_89_1429)::[])
in (_89_1430, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _89_1431 Microsoft_FStar_Absyn_Syntax.dummyRange))
in (ftv Microsoft_FStar_Absyn_Const.b2t_lid _89_1432))

let mk_conj_opt = (fun ( phi1 ) ( phi2 ) -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _89_1443 = (let _89_1442 = (let _89_1440 = (let _89_1439 = (Microsoft_FStar_Absyn_Syntax.targ phi1)
in (let _89_1438 = (let _89_1437 = (Microsoft_FStar_Absyn_Syntax.targ phi2)
in (_89_1437)::[])
in (_89_1439)::_89_1438))
in (tand, _89_1440))
in (let _89_1441 = (Support.Microsoft.FStar.Range.union_ranges phi1.Microsoft_FStar_Absyn_Syntax.pos phi2.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _89_1442 None _89_1441)))
in Some (_89_1443))
end))

let mk_binop = (fun ( op_t ) ( phi1 ) ( phi2 ) -> (let _89_1455 = (let _89_1453 = (let _89_1452 = (Microsoft_FStar_Absyn_Syntax.targ phi1)
in (let _89_1451 = (let _89_1450 = (Microsoft_FStar_Absyn_Syntax.targ phi2)
in (_89_1450)::[])
in (_89_1452)::_89_1451))
in (op_t, _89_1453))
in (let _89_1454 = (Support.Microsoft.FStar.Range.union_ranges phi1.Microsoft_FStar_Absyn_Syntax.pos phi2.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _89_1455 None _89_1454))))

let mk_neg = (fun ( phi ) -> (let _89_1461 = (let _89_1460 = (ftv Microsoft_FStar_Absyn_Const.not_lid kt_kt)
in (let _89_1459 = (let _89_1458 = (Microsoft_FStar_Absyn_Syntax.targ phi)
in (_89_1458)::[])
in (_89_1460, _89_1459)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _89_1461 None phi.Microsoft_FStar_Absyn_Syntax.pos)))

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

let mk_imp = (fun ( phi1 ) ( phi2 ) -> (match ((let _89_1478 = (compress_typ phi1)
in _89_1478.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.false_lid) -> begin
t_true
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
phi2
end
| _25_2145 -> begin
(match ((let _89_1479 = (compress_typ phi2)
in _89_1479.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when ((Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.false_lid)) -> begin
phi2
end
| _25_2149 -> begin
(mk_binop timp phi1 phi2)
end)
end))

let mk_iff = (fun ( phi1 ) ( phi2 ) -> (mk_binop tiff phi1 phi2))

let b2t = (fun ( e ) -> (let _89_1488 = (let _89_1487 = (let _89_1486 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.varg e)
in (_89_1486)::[])
in (b2t_v, _89_1487))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _89_1488 None e.Microsoft_FStar_Absyn_Syntax.pos)))

let rec unmeta_typ = (fun ( t ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, _, _, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _, _)))) -> begin
(unmeta_typ t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, _25_2189))) -> begin
(mk_conj t1 t2)
end
| _25_2194 -> begin
t
end)))

let eq_k = (let a = (let _89_1491 = (new_bvd None)
in (bvd_to_bvar_s _89_1491 Microsoft_FStar_Absyn_Syntax.ktype))
in (let atyp = (btvar_to_typ a)
in (let b = (let _89_1492 = (new_bvd None)
in (bvd_to_bvar_s _89_1492 Microsoft_FStar_Absyn_Syntax.ktype))
in (let btyp = (btvar_to_typ b)
in (let _89_1499 = (let _89_1498 = (let _89_1497 = (let _89_1496 = (let _89_1495 = (Microsoft_FStar_Absyn_Syntax.null_v_binder atyp)
in (let _89_1494 = (let _89_1493 = (Microsoft_FStar_Absyn_Syntax.null_v_binder btyp)
in (_89_1493)::[])
in (_89_1495)::_89_1494))
in ((Support.Microsoft.FStar.Util.Inl (b), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_89_1496)
in ((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_89_1497)
in (_89_1498, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _89_1499 Microsoft_FStar_Absyn_Syntax.dummyRange))))))

let teq = (ftv Microsoft_FStar_Absyn_Const.eq2_lid eq_k)

let mk_eq = (fun ( t1 ) ( t2 ) ( e1 ) ( e2 ) -> (match ((t1.Microsoft_FStar_Absyn_Syntax.n, t2.Microsoft_FStar_Absyn_Syntax.n)) with
| ((Microsoft_FStar_Absyn_Syntax.Typ_unknown, _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_unknown)) -> begin
(Support.All.failwith "DIE! mk_eq with tun")
end
| _25_2212 -> begin
(let _89_1517 = (let _89_1515 = (let _89_1514 = (Microsoft_FStar_Absyn_Syntax.itarg t1)
in (let _89_1513 = (let _89_1512 = (Microsoft_FStar_Absyn_Syntax.itarg t2)
in (let _89_1511 = (let _89_1510 = (Microsoft_FStar_Absyn_Syntax.varg e1)
in (let _89_1509 = (let _89_1508 = (Microsoft_FStar_Absyn_Syntax.varg e2)
in (_89_1508)::[])
in (_89_1510)::_89_1509))
in (_89_1512)::_89_1511))
in (_89_1514)::_89_1513))
in (teq, _89_1515))
in (let _89_1516 = (Support.Microsoft.FStar.Range.union_ranges e1.Microsoft_FStar_Absyn_Syntax.pos e2.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _89_1517 None _89_1516)))
end))

let eq_typ = (ftv Microsoft_FStar_Absyn_Const.eqT_lid Microsoft_FStar_Absyn_Syntax.kun)

let mk_eq_typ = (fun ( t1 ) ( t2 ) -> (let _89_1527 = (let _89_1525 = (let _89_1524 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _89_1523 = (let _89_1522 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (_89_1522)::[])
in (_89_1524)::_89_1523))
in (eq_typ, _89_1525))
in (let _89_1526 = (Support.Microsoft.FStar.Range.union_ranges t1.Microsoft_FStar_Absyn_Syntax.pos t2.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _89_1527 None _89_1526))))

let lex_t = (ftv Microsoft_FStar_Absyn_Const.lex_t_lid Microsoft_FStar_Absyn_Syntax.ktype)

let lex_top = (let lexnil = (withinfo Microsoft_FStar_Absyn_Const.lextop_lid lex_t Microsoft_FStar_Absyn_Syntax.dummyRange)
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar (lexnil, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) None Microsoft_FStar_Absyn_Syntax.dummyRange))

let lex_pair = (let a = (gen_bvar Microsoft_FStar_Absyn_Syntax.ktype)
in (let lexcons = (let _89_1537 = (let _89_1536 = (let _89_1535 = (let _89_1533 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _89_1532 = (let _89_1531 = (let _89_1528 = (btvar_to_typ a)
in (Microsoft_FStar_Absyn_Syntax.null_v_binder _89_1528))
in (let _89_1530 = (let _89_1529 = (Microsoft_FStar_Absyn_Syntax.null_v_binder lex_t)
in (_89_1529)::[])
in (_89_1531)::_89_1530))
in (_89_1533)::_89_1532))
in (let _89_1534 = (Microsoft_FStar_Absyn_Syntax.mk_Total lex_t)
in (_89_1535, _89_1534)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _89_1536 None Microsoft_FStar_Absyn_Syntax.dummyRange))
in (withinfo Microsoft_FStar_Absyn_Const.lexcons_lid _89_1537 Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar (lexcons, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) None Microsoft_FStar_Absyn_Syntax.dummyRange)))

let forall_kind = (let a = (let _89_1538 = (new_bvd None)
in (bvd_to_bvar_s _89_1538 Microsoft_FStar_Absyn_Syntax.ktype))
in (let atyp = (btvar_to_typ a)
in (let _89_1546 = (let _89_1545 = (let _89_1544 = (let _89_1543 = (let _89_1542 = (let _89_1541 = (let _89_1540 = (let _89_1539 = (Microsoft_FStar_Absyn_Syntax.null_v_binder atyp)
in (_89_1539)::[])
in (_89_1540, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _89_1541 Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.null_t_binder _89_1542))
in (_89_1543)::[])
in ((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_89_1544)
in (_89_1545, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _89_1546 Microsoft_FStar_Absyn_Syntax.dummyRange))))

let tforall = (ftv Microsoft_FStar_Absyn_Const.forall_lid forall_kind)

let allT_k = (fun ( k ) -> (let _89_1555 = (let _89_1554 = (let _89_1553 = (let _89_1552 = (let _89_1551 = (let _89_1550 = (let _89_1549 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (_89_1549)::[])
in (_89_1550, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _89_1551 Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.null_t_binder _89_1552))
in (_89_1553)::[])
in (_89_1554, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _89_1555 Microsoft_FStar_Absyn_Syntax.dummyRange)))

let eqT_k = (fun ( k ) -> (let _89_1562 = (let _89_1561 = (let _89_1560 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (let _89_1559 = (let _89_1558 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (_89_1558)::[])
in (_89_1560)::_89_1559))
in (_89_1561, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _89_1562 Microsoft_FStar_Absyn_Syntax.dummyRange)))

let tforall_typ = (fun ( k ) -> (let _89_1565 = (allT_k k)
in (ftv Microsoft_FStar_Absyn_Const.allTyp_lid _89_1565)))

let mk_forallT = (fun ( a ) ( b ) -> (let _89_1577 = (let _89_1576 = (tforall_typ a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _89_1575 = (let _89_1574 = (let _89_1573 = (let _89_1572 = (let _89_1571 = (let _89_1570 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (_89_1570)::[])
in (_89_1571, b))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _89_1572 None b.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _89_1573))
in (_89_1574)::[])
in (_89_1576, _89_1575)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _89_1577 None b.Microsoft_FStar_Absyn_Syntax.pos)))

let mk_forall = (fun ( x ) ( body ) -> (let r = Microsoft_FStar_Absyn_Syntax.dummyRange
in (let _89_1588 = (let _89_1587 = (let _89_1586 = (let _89_1585 = (let _89_1584 = (let _89_1583 = (let _89_1582 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_89_1582)::[])
in (_89_1583, body))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _89_1584 None r))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.targ _89_1585))
in (_89_1586)::[])
in (tforall, _89_1587))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _89_1588 None r))))

let rec close_forall = (fun ( bs ) ( f ) -> (Support.List.fold_right (fun ( b ) ( f ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
f
end
| false -> begin
(let body = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam ((b)::[], f) None f.Microsoft_FStar_Absyn_Syntax.pos)
in (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _89_1598 = (let _89_1597 = (tforall_typ a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _89_1596 = (let _89_1595 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_89_1595)::[])
in (_89_1597, _89_1596)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _89_1598 None f.Microsoft_FStar_Absyn_Syntax.pos))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _89_1602 = (let _89_1601 = (let _89_1600 = (let _89_1599 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_89_1599)::[])
in ((Support.Microsoft.FStar.Util.Inl (x.Microsoft_FStar_Absyn_Syntax.sort), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_89_1600)
in (tforall, _89_1601))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _89_1602 None f.Microsoft_FStar_Absyn_Syntax.pos))
end))
end)) bs f))

let rec is_wild_pat = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_wild (_25_2239) -> begin
true
end
| _25_2242 -> begin
false
end))

let head_and_args = (fun ( t ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(head, args)
end
| _25_2250 -> begin
(t, [])
end)))

let head_and_args_e = (fun ( e ) -> (let e = (compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(head, args)
end
| _25_2258 -> begin
(e, [])
end)))

let function_formals = (fun ( t ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
Some ((bs, c))
end
| _25_2266 -> begin
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

let ___QAll____0 = (fun ( projectee ) -> (match (projectee) with
| QAll (_25_2271) -> begin
_25_2271
end))

let ___QEx____0 = (fun ( projectee ) -> (match (projectee) with
| QEx (_25_2274) -> begin
_25_2274
end))

let ___BaseConn____0 = (fun ( projectee ) -> (match (projectee) with
| BaseConn (_25_2277) -> begin
_25_2277
end))

let destruct_typ_as_formula = (fun ( f ) -> (let destruct_base_conn = (fun ( f ) -> (let _25_2283 = (true, false)
in (match (_25_2283) with
| (type_sort, term_sort) -> begin
(let oneType = (type_sort)::[]
in (let twoTypes = (type_sort)::(type_sort)::[]
in (let threeTys = (type_sort)::(type_sort)::(type_sort)::[]
in (let twoTerms = (term_sort)::(term_sort)::[]
in (let connectives = ((Microsoft_FStar_Absyn_Const.true_lid, []))::((Microsoft_FStar_Absyn_Const.false_lid, []))::((Microsoft_FStar_Absyn_Const.and_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.or_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.imp_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.iff_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.ite_lid, threeTys))::((Microsoft_FStar_Absyn_Const.not_lid, oneType))::((Microsoft_FStar_Absyn_Const.eqT_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.eq2_lid, twoTerms))::((Microsoft_FStar_Absyn_Const.eq2_lid, (Support.List.append twoTypes twoTerms)))::[]
in (let rec aux = (fun ( f ) ( _25_2293 ) -> (match (_25_2293) with
| (lid, arity) -> begin
(let _25_2296 = (head_and_args f)
in (match (_25_2296) with
| (t, args) -> begin
(match ((((is_constructor t lid) && ((Support.List.length args) = (Support.List.length arity))) && (Support.List.forall2 (fun ( arg ) ( flag ) -> (match (arg) with
| (Support.Microsoft.FStar.Util.Inl (_25_2300), _25_2303) -> begin
(flag = type_sort)
end
| (Support.Microsoft.FStar.Util.Inr (_25_2306), _25_2309) -> begin
(flag = term_sort)
end)) args arity))) with
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
(let _89_1666 = (compress_typ t)
in (pats, _89_1666))
end
| _25_2320 -> begin
(let _89_1667 = (compress_typ t)
in ([], _89_1667))
end)))
in (let destruct_q_conn = (fun ( t ) -> (let is_q = (fun ( fa ) ( l ) -> (match (fa) with
| true -> begin
(is_forall l)
end
| false -> begin
(is_exists l)
end))
in (let flat = (fun ( t ) -> (let _25_2330 = (head_and_args t)
in (match (_25_2330) with
| (t, args) -> begin
(let _89_1681 = (Support.All.pipe_right args (Support.List.map (fun ( _25_26 ) -> (match (_25_26) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _89_1678 = (let _89_1677 = (compress_typ t)
in Support.Microsoft.FStar.Util.Inl (_89_1677))
in (_89_1678, imp))
end
| (Support.Microsoft.FStar.Util.Inr (e), imp) -> begin
(let _89_1680 = (let _89_1679 = (compress_exp e)
in Support.Microsoft.FStar.Util.Inr (_89_1679))
in (_89_1680, imp))
end))))
in (t, _89_1681))
end)))
in (let rec aux = (fun ( qopt ) ( out ) ( t ) -> (match ((let _89_1688 = (flat t)
in (qopt, _89_1688))) with
| ((Some (fa), ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, (Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t2)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((Some (fa), ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _::(Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t2)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_q fa tc.Microsoft_FStar_Absyn_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, (Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t2)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((None, ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _::(Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t2)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_qlid tc.Microsoft_FStar_Absyn_Syntax.v) -> begin
(aux (Some ((is_forall tc.Microsoft_FStar_Absyn_Syntax.v))) ((b)::out) t2)
end
| (Some (true), _25_2478) -> begin
(let _25_2482 = (patterns t)
in (match (_25_2482) with
| (pats, body) -> begin
Some (QAll (((Support.List.rev out), pats, body)))
end))
end
| (Some (false), _25_2486) -> begin
(let _25_2490 = (patterns t)
in (match (_25_2490) with
| (pats, body) -> begin
Some (QEx (((Support.List.rev out), pats, body)))
end))
end
| _25_2492 -> begin
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




