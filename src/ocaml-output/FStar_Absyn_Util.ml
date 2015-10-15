
open Prims
let handle_err = (fun warning ret e -> (match (e) with
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(let _26_34 = (let _91_8 = (let _91_7 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s : %s\n%s\n" _91_7 (match (warning) with
| true -> begin
"Warning"
end
| false -> begin
"Error"
end) msg))
in (FStar_Util.print_string _91_8))
in ())
end
| FStar_Util.NYI (s) -> begin
(let _26_38 = (let _91_9 = (FStar_Util.format1 "Feature not yet implemented: %s" s)
in (FStar_Util.print_string _91_9))
in ())
end
| FStar_Absyn_Syntax.Err (s) -> begin
(let _91_10 = (FStar_Util.format1 "Error: %s" s)
in (FStar_Util.print_string _91_10))
end
| _26_43 -> begin
(Prims.raise e)
end))

let handleable = (fun _26_1 -> (match (_26_1) with
| (FStar_Absyn_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Absyn_Syntax.Err (_)) -> begin
true
end
| _26_55 -> begin
false
end))

type gensym_t =
{gensym : Prims.unit  ->  Prims.string; reset : Prims.unit  ->  Prims.unit}

let is_Mkgensym_t = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkgensym_t")))

let gs = (let ctr = (FStar_Util.mk_ref 0)
in (let n_resets = (FStar_Util.mk_ref 0)
in {gensym = (fun _26_61 -> (match (()) with
| () -> begin
(let _91_38 = (let _91_35 = (let _91_34 = (let _91_33 = (FStar_ST.read n_resets)
in (FStar_Util.string_of_int _91_33))
in (Prims.strcat "_" _91_34))
in (Prims.strcat _91_35 "_"))
in (let _91_37 = (let _91_36 = (let _26_62 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
in (FStar_Util.string_of_int _91_36))
in (Prims.strcat _91_38 _91_37)))
end)); reset = (fun _26_64 -> (match (()) with
| () -> begin
(let _26_65 = (FStar_ST.op_Colon_Equals ctr 0)
in (FStar_Util.incr n_resets))
end))}))

let gensym = (fun _26_67 -> (match (()) with
| () -> begin
(gs.gensym ())
end))

let reset_gensym = (fun _26_68 -> (match (()) with
| () -> begin
(gs.reset ())
end))

let rec gensyms = (fun x -> (match (x) with
| 0 -> begin
[]
end
| n -> begin
(let _91_47 = (gensym ())
in (let _91_46 = (gensyms (n - 1))
in (_91_47)::_91_46))
end))

let genident = (fun r -> (let sym = (gensym ())
in (match (r) with
| None -> begin
(FStar_Absyn_Syntax.mk_ident (sym, FStar_Absyn_Syntax.dummyRange))
end
| Some (r) -> begin
(FStar_Absyn_Syntax.mk_ident (sym, r))
end)))

let bvd_eq = (fun bvd1 bvd2 -> (bvd1.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText = bvd2.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText))

let range_of_bvd = (fun x -> x.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idRange)

let mkbvd = (fun _26_82 -> (match (_26_82) with
| (x, y) -> begin
{FStar_Absyn_Syntax.ppname = x; FStar_Absyn_Syntax.realname = y}
end))

let setsort = (fun w t -> {FStar_Absyn_Syntax.v = w.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = w.FStar_Absyn_Syntax.p})

let withinfo = (fun e s r -> {FStar_Absyn_Syntax.v = e; FStar_Absyn_Syntax.sort = s; FStar_Absyn_Syntax.p = r})

let withsort = (fun e s -> (withinfo e s FStar_Absyn_Syntax.dummyRange))

let bvar_ppname = (fun bv -> bv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)

let bvar_realname = (fun bv -> bv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname)

let bvar_eq = (fun bv1 bv2 -> (bvd_eq bv1.FStar_Absyn_Syntax.v bv2.FStar_Absyn_Syntax.v))

let lbname_eq = (fun l1 l2 -> (match ((l1, l2)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (FStar_Util.Inr (l), FStar_Util.Inr (m)) -> begin
(FStar_Absyn_Syntax.lid_equals l m)
end
| _26_109 -> begin
false
end))

let fvar_eq = (fun fv1 fv2 -> (FStar_Absyn_Syntax.lid_equals fv1.FStar_Absyn_Syntax.v fv2.FStar_Absyn_Syntax.v))

let bvd_to_bvar_s = (fun bvd sort -> {FStar_Absyn_Syntax.v = bvd; FStar_Absyn_Syntax.sort = sort; FStar_Absyn_Syntax.p = bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idRange})

let bvar_to_bvd = (fun bv -> bv.FStar_Absyn_Syntax.v)

let btvar_to_typ = (fun bv -> (FStar_Absyn_Syntax.mk_Typ_btvar bv None bv.FStar_Absyn_Syntax.p))

let bvd_to_typ = (fun bvd k -> (btvar_to_typ (bvd_to_bvar_s bvd k)))

let bvar_to_exp = (fun bv -> (FStar_Absyn_Syntax.mk_Exp_bvar bv None bv.FStar_Absyn_Syntax.p))

let bvd_to_exp = (fun bvd t -> (bvar_to_exp (bvd_to_bvar_s bvd t)))

let new_bvd = (fun ropt -> (let f = (fun ropt -> (let id = (genident ropt)
in (mkbvd (id, id))))
in (f ropt)))

let freshen_bvd = (fun bvd' -> (let _91_88 = (let _91_87 = (genident (Some ((range_of_bvd bvd'))))
in (bvd'.FStar_Absyn_Syntax.ppname, _91_87))
in (mkbvd _91_88)))

let freshen_bvar = (fun b -> (let _91_90 = (freshen_bvd b.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _91_90 b.FStar_Absyn_Syntax.sort)))

let gen_bvar = (fun sort -> (let bvd = (new_bvd None)
in (bvd_to_bvar_s bvd sort)))

let gen_bvar_p = (fun r sort -> (let bvd = (new_bvd (Some (r)))
in (bvd_to_bvar_s bvd sort)))

let bvdef_of_str = (fun s -> (let f = (fun s -> (let id = (FStar_Absyn_Syntax.id_of_text s)
in (mkbvd (id, id))))
in (f s)))

let set_bvd_range = (fun bvd r -> (let _91_99 = (FStar_Absyn_Syntax.mk_ident (bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText, r))
in (let _91_98 = (FStar_Absyn_Syntax.mk_ident (bvd.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText, r))
in {FStar_Absyn_Syntax.ppname = _91_99; FStar_Absyn_Syntax.realname = _91_98})))

let set_lid_range = (fun l r -> (let ids = (FStar_All.pipe_right (FStar_List.append l.FStar_Absyn_Syntax.ns ((l.FStar_Absyn_Syntax.ident)::[])) (FStar_List.map (fun i -> (FStar_Absyn_Syntax.mk_ident (i.FStar_Absyn_Syntax.idText, r)))))
in (FStar_Absyn_Syntax.lid_of_ids ids)))

let fv = (fun l -> (let _91_107 = (FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l FStar_Absyn_Syntax.tun _91_107)))

let fvvar_of_lid = (fun l t -> (let _91_110 = (FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l t _91_110)))

let fvar = (fun dc l r -> (let _91_119 = (let _91_118 = (let _91_117 = (set_lid_range l r)
in (fv _91_117))
in (_91_118, dc))
in (FStar_Absyn_Syntax.mk_Exp_fvar _91_119 None r)))

let ftv = (fun l k -> (let _91_126 = (let _91_124 = (FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l k _91_124))
in (let _91_125 = (FStar_Absyn_Syntax.range_of_lid l)
in (FStar_Absyn_Syntax.mk_Typ_const _91_126 None _91_125))))

let order_bvd = (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (_26_155), FStar_Util.Inr (_26_158)) -> begin
(- (1))
end
| (FStar_Util.Inr (_26_162), FStar_Util.Inl (_26_165)) -> begin
1
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText y.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText y.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText)
end))

let arg_of_non_null_binder = (fun _26_180 -> (match (_26_180) with
| (b, imp) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let _91_131 = (let _91_130 = (btvar_to_typ a)
in FStar_Util.Inl (_91_130))
in (_91_131, imp))
end
| FStar_Util.Inr (x) -> begin
(let _91_133 = (let _91_132 = (bvar_to_exp x)
in FStar_Util.Inr (_91_132))
in (_91_133, imp))
end)
end))

let args_of_non_null_binders = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> (match ((FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
[]
end
| false -> begin
(let _91_137 = (arg_of_non_null_binder b)
in (_91_137)::[])
end)))))

let args_of_binders = (fun binders -> (let _91_147 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> (match ((FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
(let b = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _91_142 = (let _91_141 = (gen_bvar a.FStar_Absyn_Syntax.sort)
in FStar_Util.Inl (_91_141))
in (_91_142, (Prims.snd b)))
end
| FStar_Util.Inr (x) -> begin
(let _91_144 = (let _91_143 = (gen_bvar x.FStar_Absyn_Syntax.sort)
in FStar_Util.Inr (_91_143))
in (_91_144, (Prims.snd b)))
end)
in (let _91_145 = (arg_of_non_null_binder b)
in (b, _91_145)))
end
| false -> begin
(let _91_146 = (arg_of_non_null_binder b)
in (b, _91_146))
end))))
in (FStar_All.pipe_right _91_147 FStar_List.unzip)))

let name_binders = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> (match ((FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(let b = (let _91_153 = (let _91_152 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _91_152))
in (FStar_Absyn_Syntax.id_of_text _91_153))
in (let b = (bvd_to_bvar_s (mkbvd (b, b)) a.FStar_Absyn_Syntax.sort)
in (FStar_Util.Inl (b), imp)))
end
| (FStar_Util.Inr (y), imp) -> begin
(let x = (let _91_155 = (let _91_154 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _91_154))
in (FStar_Absyn_Syntax.id_of_text _91_155))
in (let x = (bvd_to_bvar_s (mkbvd (x, x)) y.FStar_Absyn_Syntax.sort)
in (FStar_Util.Inr (x), imp)))
end)
end
| false -> begin
b
end)))))

let name_function_binders = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, comp) -> begin
(let _91_159 = (let _91_158 = (name_binders binders)
in (_91_158, comp))
in (FStar_Absyn_Syntax.mk_Typ_fun _91_159 None t.FStar_Absyn_Syntax.pos))
end
| _26_215 -> begin
t
end))

let null_binders_of_tks = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _26_2 -> (match (_26_2) with
| (FStar_Util.Inl (k), imp) -> begin
(let _91_164 = (let _91_163 = (FStar_Absyn_Syntax.null_t_binder k)
in (FStar_All.pipe_left Prims.fst _91_163))
in (_91_164, imp))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _91_166 = (let _91_165 = (FStar_Absyn_Syntax.null_v_binder t)
in (FStar_All.pipe_left Prims.fst _91_165))
in (_91_166, imp))
end)))))

let binders_of_tks = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _26_3 -> (match (_26_3) with
| (FStar_Util.Inl (k), imp) -> begin
(let _91_171 = (let _91_170 = (gen_bvar_p k.FStar_Absyn_Syntax.pos k)
in FStar_Util.Inl (_91_170))
in (_91_171, imp))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _91_173 = (let _91_172 = (gen_bvar_p t.FStar_Absyn_Syntax.pos t)
in FStar_Util.Inr (_91_172))
in (_91_173, imp))
end)))))

let binders_of_freevars = (fun fvs -> (let _91_179 = (let _91_176 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.ftvs)
in (FStar_All.pipe_right _91_176 (FStar_List.map FStar_Absyn_Syntax.t_binder)))
in (let _91_178 = (let _91_177 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_All.pipe_right _91_177 (FStar_List.map FStar_Absyn_Syntax.v_binder)))
in (FStar_List.append _91_179 _91_178))))

let subst_to_string = (fun s -> (let _91_182 = (FStar_All.pipe_right s (FStar_List.map (fun _26_4 -> (match (_26_4) with
| FStar_Util.Inl (b, _26_241) -> begin
b.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText
end
| FStar_Util.Inr (x, _26_246) -> begin
x.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText
end))))
in (FStar_All.pipe_right _91_182 (FStar_String.concat ", "))))

let subst_tvar = (fun s a -> (FStar_Util.find_map s (fun _26_5 -> (match (_26_5) with
| FStar_Util.Inl (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _26_257 -> begin
None
end))))

let subst_xvar = (fun s a -> (FStar_Util.find_map s (fun _26_6 -> (match (_26_6) with
| FStar_Util.Inr (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _26_266 -> begin
None
end))))

let rec subst_typ' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_typ t)
end
| _26_273 -> begin
(let t0 = (FStar_Absyn_Visit.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s'), m) -> begin
(let _91_207 = (let _91_206 = (compose_subst s' s)
in (let _91_205 = (FStar_Util.mk_ref None)
in (t', _91_206, _91_205)))
in (FStar_Absyn_Syntax.mk_Typ_delayed _91_207 None t.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(let t = (mk_t ())
in (let _26_288 = (FStar_ST.op_Colon_Equals m (Some (t)))
in (subst_typ' s t)))
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let rec aux = (fun s' -> (match (s') with
| s0::rest -> begin
(match ((subst_tvar s0 a)) with
| Some (t) -> begin
(subst_typ' rest t)
end
| _26_300 -> begin
(aux rest)
end)
end
| _26_302 -> begin
t0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
t0
end
| _26_311 -> begin
(let _91_212 = (let _91_211 = (FStar_Util.mk_ref None)
in (t0, s, _91_211))
in (FStar_Absyn_Syntax.mk_Typ_delayed _91_212 None t.FStar_Absyn_Syntax.pos))
end))
end))
and subst_exp' = (fun s e -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_exp e)
end
| _26_318 -> begin
(let e0 = (FStar_Absyn_Visit.compress_exp e)
in (match (e0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e, s', m) -> begin
(let _91_217 = (let _91_216 = (compose_subst s' s)
in (let _91_215 = (FStar_Util.mk_ref None)
in (e, _91_216, _91_215)))
in (FStar_Absyn_Syntax.mk_Exp_delayed _91_217 None e.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let rec aux = (fun s -> (match (s) with
| s0::rest -> begin
(match ((subst_xvar s0 x)) with
| Some (e) -> begin
(subst_exp' rest e)
end
| _26_335 -> begin
(aux rest)
end)
end
| _26_337 -> begin
e0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
e0
end
| _26_345 -> begin
(let _91_221 = (let _91_220 = (FStar_Util.mk_ref None)
in (e0, s, _91_220))
in (FStar_Absyn_Syntax.mk_Exp_delayed _91_221 None e0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_kind' = (fun s k -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_kind k)
end
| _26_352 -> begin
(let k0 = (FStar_Absyn_Visit.compress_kind k)
in (match (k0.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
k0
end
| FStar_Absyn_Syntax.Kind_delayed (k, s', m) -> begin
(let _91_226 = (let _91_225 = (compose_subst s' s)
in (let _91_224 = (FStar_Util.mk_ref None)
in (k, _91_225, _91_224)))
in (FStar_Absyn_Syntax.mk_Kind_delayed _91_226 k0.FStar_Absyn_Syntax.pos))
end
| _26_363 -> begin
(let _91_228 = (let _91_227 = (FStar_Util.mk_ref None)
in (k0, s, _91_227))
in (FStar_Absyn_Syntax.mk_Kind_delayed _91_228 k0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_flags' = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _26_7 -> (match (_26_7) with
| FStar_Absyn_Syntax.DECREASES (a) -> begin
(let _91_232 = (subst_exp' s a)
in FStar_Absyn_Syntax.DECREASES (_91_232))
end
| f -> begin
f
end)))))
and subst_comp_typ' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _26_376 -> begin
(let _26_377 = t
in (let _91_242 = (subst_typ' s t.FStar_Absyn_Syntax.result_typ)
in (let _91_241 = (FStar_List.map (fun _26_8 -> (match (_26_8) with
| (FStar_Util.Inl (t), imp) -> begin
(let _91_237 = (let _91_236 = (subst_typ' s t)
in FStar_Util.Inl (_91_236))
in (_91_237, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _91_239 = (let _91_238 = (subst_exp' s e)
in FStar_Util.Inr (_91_238))
in (_91_239, imp))
end)) t.FStar_Absyn_Syntax.effect_args)
in (let _91_240 = (subst_flags' s t.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _26_377.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _91_242; FStar_Absyn_Syntax.effect_args = _91_241; FStar_Absyn_Syntax.flags = _91_240}))))
end))
and subst_comp' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _26_394 -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _91_245 = (subst_typ' s t)
in (FStar_Absyn_Syntax.mk_Total _91_245))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _91_246 = (subst_comp_typ' s ct)
in (FStar_Absyn_Syntax.mk_Comp _91_246))
end)
end))
and compose_subst = (fun s1 s2 -> (FStar_List.append s1 s2))

let mk_subst = (fun s -> (s)::[])

let subst_kind = (fun s t -> (subst_kind' (mk_subst s) t))

let subst_typ = (fun s t -> (subst_typ' (mk_subst s) t))

let subst_exp = (fun s t -> (subst_exp' (mk_subst s) t))

let subst_flags = (fun s t -> (subst_flags' (mk_subst s) t))

let subst_comp = (fun s t -> (subst_comp' (mk_subst s) t))

let subst_binder = (fun s _26_9 -> (match (_26_9) with
| (FStar_Util.Inl (a), imp) -> begin
(let _91_274 = (let _91_273 = (let _26_418 = a
in (let _91_272 = (subst_kind s a.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _26_418.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _91_272; FStar_Absyn_Syntax.p = _26_418.FStar_Absyn_Syntax.p}))
in FStar_Util.Inl (_91_273))
in (_91_274, imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _91_277 = (let _91_276 = (let _26_424 = x
in (let _91_275 = (subst_typ s x.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _26_424.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _91_275; FStar_Absyn_Syntax.p = _26_424.FStar_Absyn_Syntax.p}))
in FStar_Util.Inr (_91_276))
in (_91_277, imp))
end))

let subst_arg = (fun s _26_10 -> (match (_26_10) with
| (FStar_Util.Inl (t), imp) -> begin
(let _91_281 = (let _91_280 = (subst_typ s t)
in FStar_Util.Inl (_91_280))
in (_91_281, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _91_283 = (let _91_282 = (subst_exp s e)
in FStar_Util.Inr (_91_282))
in (_91_283, imp))
end))

let subst_binders = (fun s bs -> (match (s) with
| [] -> begin
bs
end
| _26_440 -> begin
(FStar_List.map (subst_binder s) bs)
end))

let subst_args = (fun s args -> (match (s) with
| [] -> begin
args
end
| _26_445 -> begin
(FStar_List.map (subst_arg s) args)
end))

let subst_formal = (fun f a -> (match ((f, a)) with
| ((FStar_Util.Inl (a), _26_451), (FStar_Util.Inl (t), _26_456)) -> begin
FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t))
end
| ((FStar_Util.Inr (x), _26_462), (FStar_Util.Inr (v), _26_467)) -> begin
FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v))
end
| _26_471 -> begin
(FStar_All.failwith "Ill-formed substitution")
end))

let mk_subst_one_binder = (fun b1 b2 -> (match (((FStar_Absyn_Syntax.is_null_binder b1) || (FStar_Absyn_Syntax.is_null_binder b2))) with
| true -> begin
[]
end
| false -> begin
(match (((Prims.fst b1), (Prims.fst b2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(match ((bvar_eq a b)) with
| true -> begin
[]
end
| false -> begin
(let _91_298 = (let _91_297 = (let _91_296 = (btvar_to_typ a)
in (b.FStar_Absyn_Syntax.v, _91_296))
in FStar_Util.Inl (_91_297))
in (_91_298)::[])
end)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(match ((bvar_eq x y)) with
| true -> begin
[]
end
| false -> begin
(let _91_301 = (let _91_300 = (let _91_299 = (bvar_to_exp x)
in (y.FStar_Absyn_Syntax.v, _91_299))
in FStar_Util.Inr (_91_300))
in (_91_301)::[])
end)
end
| _26_485 -> begin
[]
end)
end))

let mk_subst_binder = (fun bs1 bs2 -> (let rec aux = (fun out bs1 bs2 -> (match ((bs1, bs2)) with
| ([], []) -> begin
Some (out)
end
| (b1::bs1, b2::bs2) -> begin
(let _91_313 = (let _91_312 = (mk_subst_one_binder b1 b2)
in (FStar_List.append _91_312 out))
in (aux _91_313 bs1 bs2))
end
| _26_503 -> begin
None
end))
in (aux [] bs1 bs2)))

let subst_of_list = (fun formals actuals -> (match (((FStar_List.length formals) = (FStar_List.length actuals))) with
| true -> begin
(FStar_List.map2 subst_formal formals actuals)
end
| false -> begin
(FStar_All.failwith "Ill-formed substitution")
end))

type red_ctrl =
{stop_if_empty_subst : Prims.bool; descend : Prims.bool}

let is_Mkred_ctrl = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkred_ctrl")))

let alpha_ctrl = {stop_if_empty_subst = false; descend = true}

let subst_ctrl = {stop_if_empty_subst = true; descend = true}

let null_ctrl = {stop_if_empty_subst = true; descend = false}

let extend_subst = (fun e s -> (FStar_List.append (((mk_subst e))::[]) s))

let map_knd = (fun s vk mt me descend binders k -> (let _91_334 = (subst_kind' s k)
in (_91_334, descend)))

let map_typ = (fun s mk vt me descend binders t -> (let _91_342 = (subst_typ' s t)
in (_91_342, descend)))

let map_exp = (fun s mk me ve descend binders e -> (let _91_350 = (subst_exp' s e)
in (_91_350, descend)))

let map_flags = (fun s map_exp descend binders flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _26_11 -> (match (_26_11) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _91_367 = (let _91_366 = (map_exp descend binders e)
in (FStar_All.pipe_right _91_366 Prims.fst))
in FStar_Absyn_Syntax.DECREASES (_91_367))
end
| f -> begin
f
end)))))

let map_comp = (fun s mk map_typ map_exp descend binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _26_552 = (map_typ descend binders t)
in (match (_26_552) with
| (t, descend) -> begin
(let _91_390 = (FStar_Absyn_Syntax.mk_Total t)
in (_91_390, descend))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _26_557 = (map_typ descend binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_26_557) with
| (t, descend) -> begin
(let _26_560 = (FStar_Absyn_Visit.map_args map_typ map_exp descend binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_26_560) with
| (args, descend) -> begin
(let _91_393 = (let _91_392 = (let _26_561 = ct
in (let _91_391 = (map_flags s map_exp descend binders ct.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _26_561.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _91_391}))
in (FStar_Absyn_Syntax.mk_Comp _91_392))
in (_91_393, descend))
end))
end))
end))

let visit_knd = (fun s vk mt me ctrl binders k -> (let k = (FStar_Absyn_Visit.compress_kind k)
in (match (ctrl.descend) with
| true -> begin
(let _26_574 = (vk null_ctrl binders k)
in (match (_26_574) with
| (k, _26_573) -> begin
(k, ctrl)
end))
end
| false -> begin
(map_knd s vk mt me null_ctrl binders k)
end)))

let rec compress_kind = (fun k -> (let k = (FStar_Absyn_Visit.compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (k', s, m) -> begin
(let k' = (let _91_439 = (FStar_Absyn_Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] k')
in (FStar_All.pipe_left Prims.fst _91_439))
in (let k' = (compress_kind k')
in (let _26_584 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k')))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, actuals) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (formals, k') -> begin
(let _91_441 = (let _91_440 = (subst_of_list formals actuals)
in (subst_kind _91_440 k'))
in (compress_kind _91_441))
end
| _26_597 -> begin
(match (((FStar_List.length actuals) = 0)) with
| true -> begin
k
end
| false -> begin
(FStar_All.failwith "Wrong arity for kind unifier")
end)
end)
end
| _26_599 -> begin
k
end)
end
| _26_601 -> begin
k
end)))

let rec visit_typ = (fun s mk vt me ctrl boundvars t -> (let visit_prod = (fun bs tc -> (let _26_662 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _26_615 b -> (match (_26_615) with
| (bs, boundvars, s) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(let _26_624 = (map_knd s mk vt me null_ctrl boundvars a.FStar_Absyn_Syntax.sort)
in (match (_26_624) with
| (k, _26_623) -> begin
(let a = (let _26_625 = a
in {FStar_Absyn_Syntax.v = _26_625.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _26_625.FStar_Absyn_Syntax.p})
in (match ((FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
(((FStar_Util.Inl (a), imp))::bs, boundvars, s)
end
| false -> begin
(let boundvars' = (FStar_Util.Inl (a.FStar_Absyn_Syntax.v))::boundvars
in (let _26_637 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(FStar_Util.Inl (a), s, boundvars')
end
| _26_631 -> begin
(let b = (let _91_518 = (freshen_bvd a.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _91_518 k))
in (let s = (let _91_521 = (let _91_520 = (let _91_519 = (btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _91_519))
in FStar_Util.Inl (_91_520))
in (extend_subst _91_521 s))
in (FStar_Util.Inl (b), s, (FStar_Util.Inl (b.FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_26_637) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end))
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _26_645 = (map_typ s mk vt me null_ctrl boundvars x.FStar_Absyn_Syntax.sort)
in (match (_26_645) with
| (t, _26_644) -> begin
(let x = (let _26_646 = x
in {FStar_Absyn_Syntax.v = _26_646.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _26_646.FStar_Absyn_Syntax.p})
in (match ((FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
(((FStar_Util.Inr (x), imp))::bs, boundvars, s)
end
| false -> begin
(let boundvars' = (FStar_Util.Inr (x.FStar_Absyn_Syntax.v))::boundvars
in (let _26_658 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(FStar_Util.Inr (x), s, boundvars')
end
| _26_652 -> begin
(let y = (let _91_531 = (freshen_bvd x.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _91_531 t))
in (let s = (let _91_534 = (let _91_533 = (let _91_532 = (bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _91_532))
in FStar_Util.Inr (_91_533))
in (extend_subst _91_534 s))
in (FStar_Util.Inr (y), s, (FStar_Util.Inr (y.FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_26_658) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end))
end))
end)
end)) ([], boundvars, s)))
in (match (_26_662) with
| (bs, boundvars, s) -> begin
(let tc = (match ((s, tc)) with
| ([], _26_665) -> begin
tc
end
| (_26_668, FStar_Util.Inl (t)) -> begin
(let _91_545 = (let _91_544 = (map_typ s mk vt me null_ctrl boundvars t)
in (FStar_All.pipe_left Prims.fst _91_544))
in FStar_Util.Inl (_91_545))
end
| (_26_673, FStar_Util.Inr (c)) -> begin
(let _91_568 = (let _91_567 = (map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl boundvars c)
in (FStar_All.pipe_left Prims.fst _91_567))
in FStar_Util.Inr (_91_568))
end)
in ((FStar_List.rev bs), tc))
end)))
in (let t0 = t
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_26_680) -> begin
(let _91_570 = (let _91_569 = (subst_typ' s t0)
in (FStar_All.pipe_left compress_typ _91_569))
in (_91_570, ctrl))
end
| _26_683 when (not (ctrl.descend)) -> begin
(map_typ s mk vt me null_ctrl boundvars t)
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((visit_prod bs (FStar_Util.Inr (c)))) with
| (bs, FStar_Util.Inr (c)) -> begin
(let _91_580 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t0.FStar_Absyn_Syntax.pos)
in (_91_580, ctrl))
end
| _26_693 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((visit_prod (((FStar_Util.Inr (x), None))::[]) (FStar_Util.Inl (t)))) with
| ((FStar_Util.Inr (x), _26_701)::[], FStar_Util.Inl (t)) -> begin
(let _91_581 = (FStar_Absyn_Syntax.mk_Typ_refine (x, t) None t0.FStar_Absyn_Syntax.pos)
in (_91_581, ctrl))
end
| _26_708 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(match ((visit_prod bs (FStar_Util.Inl (t)))) with
| (bs, FStar_Util.Inl (t)) -> begin
(let _91_582 = (FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t0.FStar_Absyn_Syntax.pos)
in (_91_582, ctrl))
end
| _26_718 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _26_720 -> begin
(let _26_724 = (vt null_ctrl boundvars t)
in (match (_26_724) with
| (t, _26_723) -> begin
(t, ctrl)
end))
end))))
and compress_typ' = (fun t -> (let t = (FStar_Absyn_Visit.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s), m) -> begin
(let res = (let _91_602 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] t')
in (FStar_All.pipe_left Prims.fst _91_602))
in (let res = (compress_typ' res)
in (let _26_736 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(let t = (let _91_604 = (mk_t ())
in (compress_typ' _91_604))
in (let _26_744 = (FStar_ST.op_Colon_Equals m (Some (t)))
in t))
end
| _26_747 -> begin
t
end)))
and compress_typ = (fun t -> (let t = (compress_typ' t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_26_751) -> begin
(FStar_All.failwith "Impossible: compress returned a delayed type")
end
| _26_754 -> begin
t
end)))

let rec visit_exp = (fun s mk me ve ctrl binders e -> (let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_26_764) -> begin
(let _91_670 = (let _91_669 = (subst_exp' s e)
in (FStar_All.pipe_left compress_exp _91_669))
in (_91_670, ctrl))
end
| _26_767 when (not (ctrl.descend)) -> begin
(map_exp s mk me ve ctrl binders e)
end
| _26_769 -> begin
(let _26_773 = (ve null_ctrl binders e)
in (match (_26_773) with
| (e, _26_772) -> begin
(e, ctrl)
end))
end)))
and compress_exp = (fun e -> (let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e', s, m) -> begin
(let e = (let _91_699 = (FStar_Absyn_Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] e')
in (FStar_All.pipe_left Prims.fst _91_699))
in (let res = (compress_exp e)
in (let _26_783 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| _26_786 -> begin
e
end)))

let rec unmeta_exp = (fun e -> (let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _26_791)) -> begin
(unmeta_exp e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _26_797, _26_799) -> begin
(unmeta_exp e)
end
| _26_803 -> begin
e
end)))

let alpha_typ = (fun t -> (let t = (compress_typ t)
in (let s = (mk_subst [])
in (let doit = (fun t -> (let _91_724 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp alpha_ctrl [] t)
in (FStar_All.pipe_left Prims.fst _91_724)))
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_lam (bs, _)) | (FStar_Absyn_Syntax.Typ_fun (bs, _)) -> begin
(match ((FStar_Util.for_all FStar_Absyn_Syntax.is_null_binder bs)) with
| true -> begin
t
end
| false -> begin
(doit t)
end)
end
| FStar_Absyn_Syntax.Typ_refine (_26_819) -> begin
(doit t)
end
| _26_822 -> begin
t
end)))))

let formals_for_actuals = (fun formals actuals -> (FStar_List.map2 (fun formal actual -> (match (((Prims.fst formal), (Prims.fst actual))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, b))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, y))
end
| _26_838 -> begin
(FStar_All.failwith "Ill-typed substitution")
end)) formals actuals))

let compress_typ_opt = (fun _26_12 -> (match (_26_12) with
| None -> begin
None
end
| Some (t) -> begin
(let _91_731 = (compress_typ t)
in Some (_91_731))
end))

let mk_discriminator = (fun lid -> (let _91_736 = (let _91_735 = (let _91_734 = (FStar_Absyn_Syntax.mk_ident ((Prims.strcat "is_" lid.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText), lid.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idRange))
in (_91_734)::[])
in (FStar_List.append lid.FStar_Absyn_Syntax.ns _91_735))
in (FStar_Absyn_Syntax.lid_of_ids _91_736)))

let is_name = (fun lid -> (let c = (FStar_Util.char_at lid.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText 0)
in (FStar_Util.is_upper c)))

let ml_comp = (fun t r -> (let _91_744 = (let _91_743 = (set_lid_range FStar_Absyn_Const.effect_ML_lid r)
in {FStar_Absyn_Syntax.effect_name = _91_743; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.MLEFFECT)::[]})
in (FStar_Absyn_Syntax.mk_Comp _91_744)))

let total_comp = (fun t r -> (FStar_Absyn_Syntax.mk_Total t))

let gtotal_comp = (fun t -> (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_GTot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.SOMETRIVIAL)::[]}))

let comp_set_flags = (fun c f -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_26_854) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _26_858 = c
in {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp ((let _26_860 = ct
in {FStar_Absyn_Syntax.effect_name = _26_860.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _26_860.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _26_860.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = f})); FStar_Absyn_Syntax.tk = _26_858.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _26_858.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _26_858.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _26_858.FStar_Absyn_Syntax.uvs})
end))

let comp_flags = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_26_864) -> begin
(FStar_Absyn_Syntax.TOTAL)::[]
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
ct.FStar_Absyn_Syntax.flags
end))

let comp_effect_name = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c.FStar_Absyn_Syntax.effect_name
end
| FStar_Absyn_Syntax.Total (_26_872) -> begin
FStar_Absyn_Const.effect_Tot_lid
end))

let comp_to_comp_typ = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c
end
| FStar_Absyn_Syntax.Total (t) -> begin
{FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.TOTAL)::[]}
end))

let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _26_13 -> (match (_26_13) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _26_884 -> begin
false
end)))))

let is_total_lcomp = (fun c -> ((FStar_Absyn_Syntax.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _26_14 -> (match (_26_14) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _26_890 -> begin
false
end))))))

let is_tot_or_gtot_lcomp = (fun c -> (((FStar_Absyn_Syntax.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_Absyn_Syntax.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _26_15 -> (match (_26_15) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _26_896 -> begin
false
end))))))

let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _26_16 -> (match (_26_16) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _26_902 -> begin
false
end)))))

let is_lcomp_partial_return = (fun c -> (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _26_17 -> (match (_26_17) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _26_908 -> begin
false
end)))))

let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Absyn_Syntax.lid_equals FStar_Absyn_Const.effect_GTot_lid (comp_effect_name c))))

let is_pure_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_26_912) -> begin
true
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
((((is_tot_or_gtot_comp c) || (FStar_Absyn_Syntax.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Absyn_Syntax.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _26_18 -> (match (_26_18) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _26_919 -> begin
false
end)))))
end))

let is_ghost_effect = (fun l -> (((FStar_Absyn_Syntax.lid_equals FStar_Absyn_Const.effect_GTot_lid l) || (FStar_Absyn_Syntax.lid_equals FStar_Absyn_Const.effect_GHOST_lid l)) || (FStar_Absyn_Syntax.lid_equals FStar_Absyn_Const.effect_Ghost_lid l)))

let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))

let is_pure_lcomp = (fun lc -> ((((is_total_lcomp lc) || (FStar_Absyn_Syntax.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Absyn_Syntax.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _26_19 -> (match (_26_19) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _26_926 -> begin
false
end))))))

let is_pure_or_ghost_lcomp = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Absyn_Syntax.eff_name)))

let is_pure_or_ghost_function = (fun t -> (match ((let _91_783 = (compress_typ t)
in _91_783.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_26_930, c) -> begin
(is_pure_or_ghost_comp c)
end
| _26_935 -> begin
true
end))

let is_lemma = (fun t -> (match ((let _91_786 = (compress_typ t)
in _91_786.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_26_938, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Absyn_Syntax.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid)
end
| _26_945 -> begin
false
end)
end
| _26_947 -> begin
false
end))

let is_smt_lemma = (fun t -> (match ((let _91_789 = (compress_typ t)
in _91_789.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_26_950, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) when (FStar_Absyn_Syntax.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| _req::_ens::(FStar_Util.Inr (pats), _26_961)::_26_957 -> begin
(match ((let _91_790 = (unmeta_exp pats)
in _91_790.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _26_978); FStar_Absyn_Syntax.tk = _26_975; FStar_Absyn_Syntax.pos = _26_973; FStar_Absyn_Syntax.fvs = _26_971; FStar_Absyn_Syntax.uvs = _26_969}, _26_983) -> begin
(FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid)
end
| _26_987 -> begin
false
end)
end
| _26_989 -> begin
false
end)
end
| _26_991 -> begin
false
end)
end
| _26_993 -> begin
false
end))

let is_ml_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
((FStar_Absyn_Syntax.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _26_20 -> (match (_26_20) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _26_1000 -> begin
false
end)))))
end
| _26_1002 -> begin
false
end))

let comp_result = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
t
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
ct.FStar_Absyn_Syntax.result_typ
end))

let set_result_typ = (fun c t -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_26_1011) -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Absyn_Syntax.mk_Comp (let _26_1015 = ct
in {FStar_Absyn_Syntax.effect_name = _26_1015.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = _26_1015.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = _26_1015.FStar_Absyn_Syntax.flags}))
end))

let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _26_21 -> (match (_26_21) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _26_1022 -> begin
false
end)))))

let rec is_atom = (fun e -> (match ((let _91_800 = (compress_exp e)
in _91_800.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _26_1035)) -> begin
(is_atom e)
end
| _26_1040 -> begin
false
end))

let primops = (FStar_Absyn_Const.op_Eq)::(FStar_Absyn_Const.op_notEq)::(FStar_Absyn_Const.op_LT)::(FStar_Absyn_Const.op_LTE)::(FStar_Absyn_Const.op_GT)::(FStar_Absyn_Const.op_GTE)::(FStar_Absyn_Const.op_Subtraction)::(FStar_Absyn_Const.op_Minus)::(FStar_Absyn_Const.op_Addition)::(FStar_Absyn_Const.op_Multiply)::(FStar_Absyn_Const.op_Division)::(FStar_Absyn_Const.op_Modulus)::(FStar_Absyn_Const.op_And)::(FStar_Absyn_Const.op_Or)::(FStar_Absyn_Const.op_Negation)::[]

let is_primop = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _26_1044) -> begin
(FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _26_1048 -> begin
false
end))

let rec unascribe = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_ascribed (e, _26_1052, _26_1054) -> begin
(unascribe e)
end
| _26_1058 -> begin
e
end))

let rec ascribe_typ = (fun t k -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t', _26_1063) -> begin
(ascribe_typ t' k)
end
| _26_1067 -> begin
(FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.FStar_Absyn_Syntax.pos)
end))

let rec unascribe_typ = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t, _26_1071) -> begin
(unascribe_typ t)
end
| _26_1075 -> begin
t
end))

let rec unrefine = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _26_1080) -> begin
(unrefine x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _26_1085) -> begin
(unrefine t)
end
| _26_1089 -> begin
t
end)))

let is_fun = (fun e -> (match ((let _91_814 = (compress_exp e)
in _91_814.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (_26_1092) -> begin
true
end
| _26_1095 -> begin
false
end))

let is_function_typ = (fun t -> (match ((let _91_817 = (compress_typ t)
in _91_817.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_26_1098) -> begin
true
end
| _26_1101 -> begin
false
end))

let rec pre_typ = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _26_1106) -> begin
(pre_typ x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _26_1111) -> begin
(pre_typ t)
end
| _26_1115 -> begin
t
end)))

let destruct = (fun typ lid -> (let typ = (compress_typ typ)
in (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _26_1126; FStar_Absyn_Syntax.pos = _26_1124; FStar_Absyn_Syntax.fvs = _26_1122; FStar_Absyn_Syntax.uvs = _26_1120}, args) when (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some (args)
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some ([])
end
| _26_1136 -> begin
None
end)))

let rec lids_of_sigelt = (fun se -> (match (se) with
| (FStar_Absyn_Syntax.Sig_let (_, _, lids, _)) | (FStar_Absyn_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Absyn_Syntax.Sig_tycon (lid, _, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_datacon (lid, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_val_decl (lid, _, _, _)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (lid, _, _, _)) | (FStar_Absyn_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| FStar_Absyn_Syntax.Sig_new_effect (n, _26_1230) -> begin
(n.FStar_Absyn_Syntax.mname)::[]
end
| (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) -> begin
[]
end))

let lid_of_sigelt = (fun se -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _26_1246 -> begin
None
end))

let range_of_sigelt = (fun x -> (match (x) with
| (FStar_Absyn_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_datacon (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_val_decl (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_assume (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_let (_, r, _, _)) | (FStar_Absyn_Syntax.Sig_main (_, r)) | (FStar_Absyn_Syntax.Sig_pragma (_, r)) | (FStar_Absyn_Syntax.Sig_new_effect (_, r)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))

let range_of_lb = (fun _26_22 -> (match (_26_22) with
| (FStar_Util.Inl (x), _26_1357, _26_1359) -> begin
(range_of_bvd x)
end
| (FStar_Util.Inr (l), _26_1364, _26_1366) -> begin
(FStar_Absyn_Syntax.range_of_lid l)
end))

let range_of_arg = (fun _26_23 -> (match (_26_23) with
| (FStar_Util.Inl (hd), _26_1372) -> begin
hd.FStar_Absyn_Syntax.pos
end
| (FStar_Util.Inr (hd), _26_1377) -> begin
hd.FStar_Absyn_Syntax.pos
end))

let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))

let mk_typ_app = (fun f args -> (let r = (range_of_args args f.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (f, args) None r)))

let mk_exp_app = (fun f args -> (let r = (range_of_args args f.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Exp_app (f, args) None r)))

let mk_data = (fun l args -> (match (args) with
| [] -> begin
(let _91_851 = (let _91_850 = (let _91_849 = (let _91_848 = (FStar_Absyn_Syntax.range_of_lid l)
in (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l _91_848))
in (_91_849, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_91_850))
in (FStar_Absyn_Syntax.mk_Exp_meta _91_851))
end
| _26_1393 -> begin
(let _91_856 = (let _91_855 = (let _91_854 = (let _91_853 = (let _91_852 = (FStar_Absyn_Syntax.range_of_lid l)
in (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l _91_852))
in (mk_exp_app _91_853 args))
in (_91_854, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_91_855))
in (FStar_Absyn_Syntax.mk_Exp_meta _91_856))
end))

let mangle_field_name = (fun x -> (FStar_Absyn_Syntax.mk_ident ((Prims.strcat "^fname^" x.FStar_Absyn_Syntax.idText), x.FStar_Absyn_Syntax.idRange)))

let unmangle_field_name = (fun x -> (match ((FStar_Util.starts_with x.FStar_Absyn_Syntax.idText "^fname^")) with
| true -> begin
(let _91_862 = (let _91_861 = (FStar_Util.substring_from x.FStar_Absyn_Syntax.idText 7)
in (_91_861, x.FStar_Absyn_Syntax.idRange))
in (FStar_Absyn_Syntax.mk_ident _91_862))
end
| false -> begin
x
end))

let mk_field_projector_name = (fun lid x i -> (let nm = (match ((FStar_Absyn_Syntax.is_null_bvar x)) with
| true -> begin
(let _91_868 = (let _91_867 = (let _91_866 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _91_866))
in (_91_867, x.FStar_Absyn_Syntax.p))
in (FStar_Absyn_Syntax.mk_ident _91_868))
end
| false -> begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end)
in (let y = (let _26_1402 = x.FStar_Absyn_Syntax.v
in {FStar_Absyn_Syntax.ppname = nm; FStar_Absyn_Syntax.realname = _26_1402.FStar_Absyn_Syntax.realname})
in (let _91_873 = (let _91_872 = (let _91_871 = (FStar_Absyn_Syntax.ids_of_lid lid)
in (let _91_870 = (let _91_869 = (unmangle_field_name nm)
in (_91_869)::[])
in (FStar_List.append _91_871 _91_870)))
in (FStar_Absyn_Syntax.lid_of_ids _91_872))
in (_91_873, y)))))

let unchecked_unify = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (_26_1408) -> begin
(let _91_878 = (let _91_877 = (let _91_876 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _91_876))
in (FStar_Util.format1 "Changing a fixed uvar! U%s\n" _91_877))
in (FStar_All.failwith _91_878))
end
| _26_1411 -> begin
(FStar_Unionfind.change uv (FStar_Absyn_Syntax.Fixed (t)))
end))

type bvars =
(FStar_Absyn_Syntax.btvar FStar_Util.set * FStar_Absyn_Syntax.bvvar FStar_Util.set)

let no_bvars = (FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.ftvs, FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.fxvs)

let fvs_included = (fun fvs1 fvs2 -> ((FStar_Util.set_is_subset_of fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs) && (FStar_Util.set_is_subset_of fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)))

let eq_fvars = (fun v1 v2 -> (match ((v1, v2)) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(FStar_Absyn_Syntax.bvd_eq a b)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| _26_1427 -> begin
false
end))

let eq_binder = (fun b1 b2 -> (match (((Prims.fst b1), (Prims.fst b2))) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| _26_1441 -> begin
false
end))

let uv_eq = (fun _26_1445 _26_1449 -> (match ((_26_1445, _26_1449)) with
| ((uv1, _26_1444), (uv2, _26_1448)) -> begin
(FStar_Unionfind.equivalent uv1 uv2)
end))

let union_uvs = (fun uvs1 uvs2 -> (let _91_907 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_k uvs2.FStar_Absyn_Syntax.uvars_k)
in (let _91_906 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_t uvs2.FStar_Absyn_Syntax.uvars_t)
in (let _91_905 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_e uvs2.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _91_907; FStar_Absyn_Syntax.uvars_t = _91_906; FStar_Absyn_Syntax.uvars_e = _91_905}))))

let union_fvs = (fun fvs1 fvs2 -> (let _91_913 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs)
in (let _91_912 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)
in {FStar_Absyn_Syntax.ftvs = _91_913; FStar_Absyn_Syntax.fxvs = _91_912})))

let union_fvs_uvs = (fun _26_1456 _26_1459 -> (match ((_26_1456, _26_1459)) with
| ((fvs1, uvs1), (fvs2, uvs2)) -> begin
(let _91_919 = (union_fvs fvs1 fvs2)
in (let _91_918 = (union_uvs uvs1 uvs2)
in (_91_919, _91_918)))
end))

let sub_fv = (fun _26_1462 _26_1465 -> (match ((_26_1462, _26_1465)) with
| ((fvs, uvs), (tvars, vvars)) -> begin
(let _91_940 = (let _26_1466 = fvs
in (let _91_939 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.ftvs tvars)
in (let _91_938 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.fxvs vvars)
in {FStar_Absyn_Syntax.ftvs = _91_939; FStar_Absyn_Syntax.fxvs = _91_938})))
in (_91_940, uvs))
end))

let stash = (fun uvonly s _26_1474 -> (match (_26_1474) with
| (fvs, uvs) -> begin
(let _26_1475 = (FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.uvs (Some (uvs)))
in (match (uvonly) with
| true -> begin
()
end
| false -> begin
(FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.fvs (Some (fvs)))
end))
end))

let single_fv = (fun x -> (let _91_951 = (FStar_Absyn_Syntax.new_ftv_set ())
in (FStar_Util.set_add x _91_951)))

let single_uv = (fun u -> (let _91_959 = (FStar_Absyn_Syntax.new_uv_set ())
in (FStar_Util.set_add u _91_959)))

let single_uvt = (fun u -> (let _91_967 = (FStar_Absyn_Syntax.new_uvt_set ())
in (FStar_Util.set_add u _91_967)))

let rec vs_typ' = (fun t uvonly cont -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_26_1486) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(match (uvonly) with
| true -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| false -> begin
(let _91_1082 = (let _91_1081 = (let _26_1490 = FStar_Absyn_Syntax.no_fvs
in (let _91_1080 = (single_fv a)
in {FStar_Absyn_Syntax.ftvs = _91_1080; FStar_Absyn_Syntax.fxvs = _26_1490.FStar_Absyn_Syntax.fxvs}))
in (_91_1081, FStar_Absyn_Syntax.no_uvs))
in (cont _91_1082))
end)
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let _91_1085 = (let _91_1084 = (let _26_1496 = FStar_Absyn_Syntax.no_uvs
in (let _91_1083 = (single_uvt (uv, k))
in {FStar_Absyn_Syntax.uvars_k = _26_1496.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _91_1083; FStar_Absyn_Syntax.uvars_e = _26_1496.FStar_Absyn_Syntax.uvars_e}))
in (FStar_Absyn_Syntax.no_fvs, _91_1084))
in (cont _91_1085))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(vs_binders bs uvonly (fun _26_1508 -> (match (_26_1508) with
| (bvs, vs1) -> begin
(vs_comp c uvonly (fun vs2 -> (let _91_1089 = (let _91_1088 = (union_fvs_uvs vs1 vs2)
in (sub_fv _91_1088 bvs))
in (cont _91_1089))))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(vs_binders bs uvonly (fun _26_1516 -> (match (_26_1516) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _91_1093 = (let _91_1092 = (union_fvs_uvs vs1 vs2)
in (sub_fv _91_1092 bvs))
in (cont _91_1093))))
end)))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(vs_binders (((FStar_Util.Inr (x), None))::[]) uvonly (fun _26_1524 -> (match (_26_1524) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _91_1097 = (let _91_1096 = (union_fvs_uvs vs1 vs2)
in (sub_fv _91_1096 bvs))
in (cont _91_1097))))
end)))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(vs_typ t uvonly (fun vs1 -> (vs_args args uvonly (fun vs2 -> (let _91_1100 = (union_fvs_uvs vs1 vs2)
in (cont _91_1100))))))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _26_1534) -> begin
(vs_typ t uvonly cont)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _26_1540)) -> begin
(vs_typ t1 uvonly (fun vs1 -> (vs_typ t2 uvonly (fun vs2 -> (let _91_1103 = (union_fvs_uvs vs1 vs2)
in (cont _91_1103))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) -> begin
(vs_typ t uvonly cont)
end)))
and vs_binders = (fun bs uvonly cont -> (match (bs) with
| [] -> begin
(cont (no_bvars, (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs)))
end
| (FStar_Util.Inl (a), _26_1582)::rest -> begin
(vs_kind a.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _26_1590 -> (match (_26_1590) with
| ((tvars, vvars), vs2) -> begin
(let _91_1140 = (let _91_1139 = (let _91_1137 = (FStar_Util.set_add a tvars)
in (_91_1137, vvars))
in (let _91_1138 = (union_fvs_uvs vs vs2)
in (_91_1139, _91_1138)))
in (cont _91_1140))
end)))))
end
| (FStar_Util.Inr (x), _26_1595)::rest -> begin
(vs_typ x.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _26_1603 -> (match (_26_1603) with
| ((tvars, vvars), vs2) -> begin
(let _91_1164 = (let _91_1163 = (let _91_1161 = (FStar_Util.set_add x vvars)
in (tvars, _91_1161))
in (let _91_1162 = (union_fvs_uvs vs vs2)
in (_91_1163, _91_1162)))
in (cont _91_1164))
end)))))
end))
and vs_args = (fun args uvonly cont -> (match (args) with
| [] -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| (FStar_Util.Inl (t), _26_1613)::tl -> begin
(vs_typ t uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _91_1168 = (union_fvs_uvs ft1 ft2)
in (cont _91_1168))))))
end
| (FStar_Util.Inr (e), _26_1622)::tl -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _91_1171 = (union_fvs_uvs ft1 ft2)
in (cont _91_1171))))))
end))
and vs_typ = (fun t uvonly cont -> (match ((let _91_1174 = (FStar_ST.read t.FStar_Absyn_Syntax.fvs)
in (let _91_1173 = (FStar_ST.read t.FStar_Absyn_Syntax.uvs)
in (_91_1174, _91_1173)))) with
| (Some (_26_1632), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_typ' t uvonly (fun fvs -> (let _26_1640 = (stash uvonly t fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
(match (uvonly) with
| true -> begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end
| false -> begin
(vs_typ' t uvonly (fun fvs -> (let _26_1647 = (stash uvonly t fvs)
in (cont fvs))))
end)
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_kind' = (fun k uvonly cont -> (let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_26_1660, k) -> begin
(let _91_1179 = (let _91_1178 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "%s: Impossible ... found a Kind_lam bare" _91_1178))
in (FStar_All.failwith _91_1179))
end
| FStar_Absyn_Syntax.Kind_delayed (_26_1665) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(vs_args args uvonly (fun _26_1676 -> (match (_26_1676) with
| (fvs, uvs) -> begin
(let _91_1183 = (let _91_1182 = (let _26_1677 = uvs
in (let _91_1181 = (FStar_Util.set_add uv uvs.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _91_1181; FStar_Absyn_Syntax.uvars_t = _26_1677.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _26_1677.FStar_Absyn_Syntax.uvars_e}))
in (fvs, _91_1182))
in (cont _91_1183))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev (_26_1680, k) -> begin
(vs_kind k uvonly cont)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(vs_binders bs uvonly (fun _26_1690 -> (match (_26_1690) with
| (bvs, vs1) -> begin
(vs_kind k uvonly (fun vs2 -> (let _91_1187 = (let _91_1186 = (union_fvs_uvs vs1 vs2)
in (sub_fv _91_1186 bvs))
in (cont _91_1187))))
end)))
end)))
and vs_kind = (fun k uvonly cont -> (match ((let _91_1190 = (FStar_ST.read k.FStar_Absyn_Syntax.fvs)
in (let _91_1189 = (FStar_ST.read k.FStar_Absyn_Syntax.uvs)
in (_91_1190, _91_1189)))) with
| (Some (_26_1697), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_kind' k uvonly (fun fvs -> (let _26_1705 = (stash uvonly k fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
(match (uvonly) with
| true -> begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end
| false -> begin
(vs_kind' k uvonly (fun fvs -> (let _26_1712 = (stash uvonly k fvs)
in (cont fvs))))
end)
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_exp' = (fun e uvonly cont -> (let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_26_1725) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(let _91_1196 = (let _91_1195 = (let _26_1737 = FStar_Absyn_Syntax.no_uvs
in (let _91_1194 = (single_uvt (uv, t))
in {FStar_Absyn_Syntax.uvars_k = _26_1737.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _26_1737.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _91_1194}))
in (FStar_Absyn_Syntax.no_fvs, _91_1195))
in (cont _91_1196))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(match (uvonly) with
| true -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| false -> begin
(let _91_1199 = (let _91_1198 = (let _26_1741 = FStar_Absyn_Syntax.no_fvs
in (let _91_1197 = (single_fv x)
in {FStar_Absyn_Syntax.ftvs = _26_1741.FStar_Absyn_Syntax.ftvs; FStar_Absyn_Syntax.fxvs = _91_1197}))
in (_91_1198, FStar_Absyn_Syntax.no_uvs))
in (cont _91_1199))
end)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _26_1745, _26_1747) -> begin
(vs_exp e uvonly cont)
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(vs_binders bs uvonly (fun _26_1756 -> (match (_26_1756) with
| (bvs, vs1) -> begin
(vs_exp e uvonly (fun vs2 -> (let _91_1203 = (let _91_1202 = (union_fvs_uvs vs1 vs2)
in (sub_fv _91_1202 bvs))
in (cont _91_1203))))
end)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args args uvonly (fun ft2 -> (let _91_1206 = (union_fvs_uvs ft1 ft2)
in (cont _91_1206))))))
end
| (FStar_Absyn_Syntax.Exp_match (_)) | (FStar_Absyn_Syntax.Exp_let (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _26_1772)) -> begin
(vs_exp e uvonly cont)
end)))
and vs_exp = (fun e uvonly cont -> (match ((let _91_1209 = (FStar_ST.read e.FStar_Absyn_Syntax.fvs)
in (let _91_1208 = (FStar_ST.read e.FStar_Absyn_Syntax.uvs)
in (_91_1209, _91_1208)))) with
| (Some (_26_1781), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_exp' e uvonly (fun fvs -> (let _26_1789 = (stash uvonly e fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
(match (uvonly) with
| true -> begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end
| false -> begin
(vs_exp' e uvonly (fun fvs -> (let _26_1796 = (stash uvonly e fvs)
in (cont fvs))))
end)
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_comp' = (fun c uvonly k -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(vs_typ t uvonly k)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(match (uvonly) with
| true -> begin
(vs_typ ct.FStar_Absyn_Syntax.result_typ uvonly k)
end
| false -> begin
(vs_typ ct.FStar_Absyn_Syntax.result_typ uvonly (fun vs1 -> (vs_args ct.FStar_Absyn_Syntax.effect_args uvonly (fun vs2 -> (let _91_1215 = (union_fvs_uvs vs1 vs2)
in (k _91_1215))))))
end)
end))
and vs_comp = (fun c uvonly cont -> (match ((let _91_1218 = (FStar_ST.read c.FStar_Absyn_Syntax.fvs)
in (let _91_1217 = (FStar_ST.read c.FStar_Absyn_Syntax.uvs)
in (_91_1218, _91_1217)))) with
| (Some (_26_1818), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_comp' c uvonly (fun fvs -> (let _26_1826 = (stash uvonly c fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
(match (uvonly) with
| true -> begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end
| false -> begin
(vs_comp' c uvonly (fun fvs -> (let _26_1833 = (stash uvonly c fvs)
in (cont fvs))))
end)
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_either = (fun te uvonly cont -> (match (te) with
| FStar_Util.Inl (t) -> begin
(vs_typ t uvonly cont)
end
| FStar_Util.Inr (e) -> begin
(vs_exp e uvonly cont)
end))
and vs_either_l = (fun tes uvonly cont -> (match (tes) with
| [] -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| hd::tl -> begin
(vs_either hd uvonly (fun ft1 -> (vs_either_l tl uvonly (fun ft2 -> (let _91_1225 = (union_fvs_uvs ft1 ft2)
in (cont _91_1225))))))
end))

let freevars_kind = (fun k -> (vs_kind k false (fun _26_1862 -> (match (_26_1862) with
| (x, _26_1861) -> begin
x
end))))

let freevars_typ = (fun t -> (vs_typ t false (fun _26_1867 -> (match (_26_1867) with
| (x, _26_1866) -> begin
x
end))))

let freevars_exp = (fun e -> (vs_exp e false (fun _26_1872 -> (match (_26_1872) with
| (x, _26_1871) -> begin
x
end))))

let freevars_comp = (fun c -> (vs_comp c false (fun _26_1877 -> (match (_26_1877) with
| (x, _26_1876) -> begin
x
end))))

let freevars_args = (fun args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(let _91_1241 = (freevars_typ t)
in (FStar_All.pipe_left (union_fvs out) _91_1241))
end
| FStar_Util.Inr (e) -> begin
(let _91_1242 = (freevars_exp e)
in (FStar_All.pipe_left (union_fvs out) _91_1242))
end)) FStar_Absyn_Syntax.no_fvs)))

let is_free = (fun axs fvs -> (FStar_All.pipe_right axs (FStar_Util.for_some (fun _26_24 -> (match (_26_24) with
| FStar_Util.Inl (a) -> begin
(FStar_Util.set_mem a fvs.FStar_Absyn_Syntax.ftvs)
end
| FStar_Util.Inr (x) -> begin
(FStar_Util.set_mem x fvs.FStar_Absyn_Syntax.fxvs)
end)))))

type syntax_sum =
| SynSumKind of FStar_Absyn_Syntax.knd
| SynSumType of FStar_Absyn_Syntax.typ
| SynSumExp of FStar_Absyn_Syntax.exp
| SynSumComp of (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax

let is_SynSumKind = (fun _discr_ -> (match (_discr_) with
| SynSumKind (_) -> begin
true
end
| _ -> begin
false
end))

let is_SynSumType = (fun _discr_ -> (match (_discr_) with
| SynSumType (_) -> begin
true
end
| _ -> begin
false
end))

let is_SynSumExp = (fun _discr_ -> (match (_discr_) with
| SynSumExp (_) -> begin
true
end
| _ -> begin
false
end))

let is_SynSumComp = (fun _discr_ -> (match (_discr_) with
| SynSumComp (_) -> begin
true
end
| _ -> begin
false
end))

let ___SynSumKind____0 = (fun projectee -> (match (projectee) with
| SynSumKind (_26_1894) -> begin
_26_1894
end))

let ___SynSumType____0 = (fun projectee -> (match (projectee) with
| SynSumType (_26_1897) -> begin
_26_1897
end))

let ___SynSumExp____0 = (fun projectee -> (match (projectee) with
| SynSumExp (_26_1900) -> begin
_26_1900
end))

let ___SynSumComp____0 = (fun projectee -> (match (projectee) with
| SynSumComp (_26_1903) -> begin
_26_1903
end))

let rec update_uvars = (fun s uvs -> (let out = (let _91_1316 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_k)
in (FStar_All.pipe_right _91_1316 (FStar_List.fold_left (fun out u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(let _91_1314 = (uvars_in_kind k)
in (union_uvs _91_1314 out))
end
| _26_1911 -> begin
(let _26_1912 = out
in (let _91_1315 = (FStar_Util.set_add u out.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _91_1315; FStar_Absyn_Syntax.uvars_t = _26_1912.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _26_1912.FStar_Absyn_Syntax.uvars_e}))
end)) FStar_Absyn_Syntax.no_uvs)))
in (let out = (let _91_1321 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _91_1321 (FStar_List.fold_left (fun out _26_1918 -> (match (_26_1918) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (t) -> begin
(let _91_1319 = (uvars_in_typ t)
in (union_uvs _91_1319 out))
end
| _26_1922 -> begin
(let _26_1923 = out
in (let _91_1320 = (FStar_Util.set_add (u, t) out.FStar_Absyn_Syntax.uvars_t)
in {FStar_Absyn_Syntax.uvars_k = _26_1923.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _91_1320; FStar_Absyn_Syntax.uvars_e = _26_1923.FStar_Absyn_Syntax.uvars_e}))
end)
end)) out)))
in (let out = (let _91_1326 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_e)
in (FStar_All.pipe_right _91_1326 (FStar_List.fold_left (fun out _26_1929 -> (match (_26_1929) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(let _91_1324 = (uvars_in_exp e)
in (union_uvs _91_1324 out))
end
| _26_1933 -> begin
(let _26_1934 = out
in (let _91_1325 = (FStar_Util.set_add (u, t) out.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _26_1934.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _26_1934.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _91_1325}))
end)
end)) out)))
in (let _26_1945 = (match (s) with
| SynSumKind (k) -> begin
(FStar_ST.op_Colon_Equals k.FStar_Absyn_Syntax.uvs (Some (out)))
end
| SynSumType (t) -> begin
(FStar_ST.op_Colon_Equals t.FStar_Absyn_Syntax.uvs (Some (out)))
end
| SynSumExp (e) -> begin
(FStar_ST.op_Colon_Equals e.FStar_Absyn_Syntax.uvs (Some (out)))
end
| SynSumComp (c) -> begin
(FStar_ST.op_Colon_Equals c.FStar_Absyn_Syntax.uvs (Some (out)))
end)
in out)))))
and uvars_in_kind = (fun k -> (let _91_1329 = (vs_kind k true (fun _26_1951 -> (match (_26_1951) with
| (_26_1949, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumKind (k))) _91_1329)))
and uvars_in_typ = (fun t -> (let _91_1332 = (vs_typ t true (fun _26_1956 -> (match (_26_1956) with
| (_26_1954, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumType (t))) _91_1332)))
and uvars_in_exp = (fun e -> (let _91_1335 = (vs_exp e true (fun _26_1961 -> (match (_26_1961) with
| (_26_1959, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumExp (e))) _91_1335)))
and uvars_in_comp = (fun c -> (let _91_1338 = (vs_comp c true (fun _26_1966 -> (match (_26_1966) with
| (_26_1964, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumComp (c))) _91_1338)))

let uvars_included_in = (fun u1 u2 -> (((FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_k u2.FStar_Absyn_Syntax.uvars_k) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_t u2.FStar_Absyn_Syntax.uvars_t)) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_e u2.FStar_Absyn_Syntax.uvars_e)))

let rec kind_formals = (fun k -> (let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_26_1972) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
([], k)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _26_1986 = (kind_formals k)
in (match (_26_1986) with
| (bs', k) -> begin
((FStar_List.append bs bs'), k)
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_26_1988, k) -> begin
(kind_formals k)
end
| FStar_Absyn_Syntax.Kind_delayed (_26_1993) -> begin
(FStar_All.failwith "Impossible")
end)))

let close_for_kind = (fun t k -> (let _26_2000 = (kind_formals k)
in (match (_26_2000) with
| (bs, _26_1999) -> begin
(match (bs) with
| [] -> begin
t
end
| _26_2003 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.FStar_Absyn_Syntax.pos)
end)
end)))

let rec unabbreviate_kind = (fun k -> (let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_abbrev (_26_2007, k) -> begin
(unabbreviate_kind k)
end
| _26_2012 -> begin
k
end)))

let close_with_lam = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _26_2017 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (tps, t) None t.FStar_Absyn_Syntax.pos)
end))

let close_with_arrow = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _26_2022 -> begin
(let _26_2031 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
((FStar_List.append tps bs'), c)
end
| _26_2028 -> begin
(let _91_1359 = (FStar_Absyn_Syntax.mk_Total t)
in (tps, _91_1359))
end)
in (match (_26_2031) with
| (bs, c) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.FStar_Absyn_Syntax.pos)
end))
end))

let close_typ = close_with_arrow

let close_kind = (fun tps k -> (match (tps) with
| [] -> begin
k
end
| _26_2036 -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow' (tps, k) k.FStar_Absyn_Syntax.pos)
end))

let is_tuple_constructor = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str "Prims.Tuple")
end
| _26_2041 -> begin
false
end))

let mk_tuple_lid = (fun n r -> (let t = (let _91_1372 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Tuple%s" _91_1372))
in (let _91_1373 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _91_1373 r))))

let mk_tuple_data_lid = (fun n r -> (let t = (let _91_1378 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkTuple%s" _91_1378))
in (let _91_1379 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _91_1379 r))))

let is_tuple_data_lid = (fun f n -> (let _91_1384 = (mk_tuple_data_lid n FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.lid_equals f _91_1384)))

let is_dtuple_constructor = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str "Prims.DTuple")
end
| _26_2054 -> begin
false
end))

let mk_dtuple_lid = (fun n r -> (let t = (let _91_1391 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "DTuple%s" _91_1391))
in (let _91_1392 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _91_1392 r))))

let mk_dtuple_data_lid = (fun n r -> (let t = (let _91_1397 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkDTuple%s" _91_1397))
in (let _91_1398 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _91_1398 r))))

let is_lid_equality = (fun x -> ((((FStar_Absyn_Syntax.lid_equals x FStar_Absyn_Const.eq_lid) || (FStar_Absyn_Syntax.lid_equals x FStar_Absyn_Const.eq2_lid)) || (FStar_Absyn_Syntax.lid_equals x FStar_Absyn_Const.eqA_lid)) || (FStar_Absyn_Syntax.lid_equals x FStar_Absyn_Const.eqT_lid)))

let is_forall = (fun lid -> ((FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.forall_lid) || (FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.allTyp_lid)))

let is_exists = (fun lid -> ((FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.exists_lid) || (FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.exTyp_lid)))

let is_qlid = (fun lid -> ((is_forall lid) || (is_exists lid)))

let is_equality = (fun x -> (is_lid_equality x.FStar_Absyn_Syntax.v))

let lid_is_connective = (let lst = (FStar_Absyn_Const.and_lid)::(FStar_Absyn_Const.or_lid)::(FStar_Absyn_Const.not_lid)::(FStar_Absyn_Const.iff_lid)::(FStar_Absyn_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Absyn_Syntax.lid_equals lid) lst)))

let is_constructor = (fun t lid -> (match ((let _91_1414 = (pre_typ t)
in _91_1414.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
(FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v lid)
end
| _26_2073 -> begin
false
end))

let rec is_constructed_typ = (fun t lid -> (match ((let _91_1419 = (pre_typ t)
in _91_1419.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (_26_2077) -> begin
(is_constructor t lid)
end
| FStar_Absyn_Syntax.Typ_app (t, _26_2081) -> begin
(is_constructed_typ t lid)
end
| _26_2085 -> begin
false
end))

let rec get_tycon = (fun t -> (let t = (pre_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
Some (t)
end
| FStar_Absyn_Syntax.Typ_app (t, _26_2096) -> begin
(get_tycon t)
end
| _26_2100 -> begin
None
end)))

let base_kind = (fun _26_25 -> (match (_26_25) with
| FStar_Absyn_Syntax.Kind_type -> begin
true
end
| _26_2104 -> begin
false
end))

let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _26_2110 _26_2114 -> (match ((_26_2110, _26_2114)) with
| ((fn1, _26_2109), (fn2, _26_2113)) -> begin
(let _91_1428 = (FStar_Absyn_Syntax.text_of_lid fn1)
in (let _91_1427 = (FStar_Absyn_Syntax.text_of_lid fn2)
in (FStar_String.compare _91_1428 _91_1427)))
end)))))

let kt_kt = (FStar_Absyn_Const.kunary FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)

let kt_kt_kt = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)

let tand = (ftv FStar_Absyn_Const.and_lid kt_kt_kt)

let tor = (ftv FStar_Absyn_Const.or_lid kt_kt_kt)

let timp = (ftv FStar_Absyn_Const.imp_lid kt_kt_kt)

let tiff = (ftv FStar_Absyn_Const.iff_lid kt_kt_kt)

let t_bool = (ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)

let t_false = (ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)

let t_true = (ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)

let b2t_v = (let _91_1432 = (let _91_1431 = (let _91_1430 = (let _91_1429 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder t_bool)
in (_91_1429)::[])
in (_91_1430, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _91_1431 FStar_Absyn_Syntax.dummyRange))
in (ftv FStar_Absyn_Const.b2t_lid _91_1432))

let mk_conj_opt = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _91_1443 = (let _91_1442 = (let _91_1440 = (let _91_1439 = (FStar_Absyn_Syntax.targ phi1)
in (let _91_1438 = (let _91_1437 = (FStar_Absyn_Syntax.targ phi2)
in (_91_1437)::[])
in (_91_1439)::_91_1438))
in (tand, _91_1440))
in (let _91_1441 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _91_1442 None _91_1441)))
in Some (_91_1443))
end))

let mk_binop = (fun op_t phi1 phi2 -> (let _91_1455 = (let _91_1453 = (let _91_1452 = (FStar_Absyn_Syntax.targ phi1)
in (let _91_1451 = (let _91_1450 = (FStar_Absyn_Syntax.targ phi2)
in (_91_1450)::[])
in (_91_1452)::_91_1451))
in (op_t, _91_1453))
in (let _91_1454 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _91_1455 None _91_1454))))

let mk_neg = (fun phi -> (let _91_1461 = (let _91_1460 = (ftv FStar_Absyn_Const.not_lid kt_kt)
in (let _91_1459 = (let _91_1458 = (FStar_Absyn_Syntax.targ phi)
in (_91_1458)::[])
in (_91_1460, _91_1459)))
in (FStar_Absyn_Syntax.mk_Typ_app _91_1461 None phi.FStar_Absyn_Syntax.pos)))

let mk_conj = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))

let mk_conj_l = (fun phi -> (match (phi) with
| [] -> begin
(ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end
| hd::tl -> begin
(FStar_List.fold_right mk_conj tl hd)
end))

let mk_disj = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))

let mk_disj_l = (fun phi -> (match (phi) with
| [] -> begin
(ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)
end
| hd::tl -> begin
(FStar_List.fold_right mk_disj tl hd)
end))

let mk_imp = (fun phi1 phi2 -> (match ((let _91_1478 = (compress_typ phi1)
in _91_1478.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid) -> begin
t_true
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
phi2
end
| _26_2145 -> begin
(match ((let _91_1479 = (compress_typ phi2)
in _91_1479.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when ((FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) || (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid)) -> begin
phi2
end
| _26_2149 -> begin
(mk_binop timp phi1 phi2)
end)
end))

let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))

let b2t = (fun e -> (let _91_1488 = (let _91_1487 = (let _91_1486 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg e)
in (_91_1486)::[])
in (b2t_v, _91_1487))
in (FStar_Absyn_Syntax.mk_Typ_app _91_1488 None e.FStar_Absyn_Syntax.pos)))

let rec unmeta_typ = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(unmeta_typ t)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _26_2189)) -> begin
(mk_conj t1 t2)
end
| _26_2194 -> begin
t
end)))

let eq_k = (let a = (let _91_1491 = (new_bvd None)
in (bvd_to_bvar_s _91_1491 FStar_Absyn_Syntax.ktype))
in (let atyp = (btvar_to_typ a)
in (let b = (let _91_1492 = (new_bvd None)
in (bvd_to_bvar_s _91_1492 FStar_Absyn_Syntax.ktype))
in (let btyp = (btvar_to_typ b)
in (let _91_1499 = (let _91_1498 = (let _91_1497 = (let _91_1496 = (let _91_1495 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (let _91_1494 = (let _91_1493 = (FStar_Absyn_Syntax.null_v_binder btyp)
in (_91_1493)::[])
in (_91_1495)::_91_1494))
in ((FStar_Util.Inl (b), Some (FStar_Absyn_Syntax.Implicit)))::_91_1496)
in ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit)))::_91_1497)
in (_91_1498, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _91_1499 FStar_Absyn_Syntax.dummyRange))))))

let teq = (ftv FStar_Absyn_Const.eq2_lid eq_k)

let mk_eq = (fun t1 t2 e1 e2 -> (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((_, FStar_Absyn_Syntax.Typ_unknown)) -> begin
(FStar_All.failwith "DIE! mk_eq with tun")
end
| _26_2212 -> begin
(let _91_1517 = (let _91_1515 = (let _91_1514 = (FStar_Absyn_Syntax.itarg t1)
in (let _91_1513 = (let _91_1512 = (FStar_Absyn_Syntax.itarg t2)
in (let _91_1511 = (let _91_1510 = (FStar_Absyn_Syntax.varg e1)
in (let _91_1509 = (let _91_1508 = (FStar_Absyn_Syntax.varg e2)
in (_91_1508)::[])
in (_91_1510)::_91_1509))
in (_91_1512)::_91_1511))
in (_91_1514)::_91_1513))
in (teq, _91_1515))
in (let _91_1516 = (FStar_Range.union_ranges e1.FStar_Absyn_Syntax.pos e2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _91_1517 None _91_1516)))
end))

let eq_typ = (ftv FStar_Absyn_Const.eqT_lid FStar_Absyn_Syntax.kun)

let mk_eq_typ = (fun t1 t2 -> (let _91_1527 = (let _91_1525 = (let _91_1524 = (FStar_Absyn_Syntax.targ t1)
in (let _91_1523 = (let _91_1522 = (FStar_Absyn_Syntax.targ t2)
in (_91_1522)::[])
in (_91_1524)::_91_1523))
in (eq_typ, _91_1525))
in (let _91_1526 = (FStar_Range.union_ranges t1.FStar_Absyn_Syntax.pos t2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _91_1527 None _91_1526))))

let lex_t = (ftv FStar_Absyn_Const.lex_t_lid FStar_Absyn_Syntax.ktype)

let lex_top = (let lexnil = (withinfo FStar_Absyn_Const.lextop_lid lex_t FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.mk_Exp_fvar (lexnil, Some (FStar_Absyn_Syntax.Data_ctor)) None FStar_Absyn_Syntax.dummyRange))

let lex_pair = (let a = (gen_bvar FStar_Absyn_Syntax.ktype)
in (let lexcons = (let _91_1537 = (let _91_1536 = (let _91_1535 = (let _91_1533 = (FStar_Absyn_Syntax.t_binder a)
in (let _91_1532 = (let _91_1531 = (let _91_1528 = (btvar_to_typ a)
in (FStar_Absyn_Syntax.null_v_binder _91_1528))
in (let _91_1530 = (let _91_1529 = (FStar_Absyn_Syntax.null_v_binder lex_t)
in (_91_1529)::[])
in (_91_1531)::_91_1530))
in (_91_1533)::_91_1532))
in (let _91_1534 = (FStar_Absyn_Syntax.mk_Total lex_t)
in (_91_1535, _91_1534)))
in (FStar_Absyn_Syntax.mk_Typ_fun _91_1536 None FStar_Absyn_Syntax.dummyRange))
in (withinfo FStar_Absyn_Const.lexcons_lid _91_1537 FStar_Absyn_Syntax.dummyRange))
in (FStar_Absyn_Syntax.mk_Exp_fvar (lexcons, Some (FStar_Absyn_Syntax.Data_ctor)) None FStar_Absyn_Syntax.dummyRange)))

let forall_kind = (let a = (let _91_1538 = (new_bvd None)
in (bvd_to_bvar_s _91_1538 FStar_Absyn_Syntax.ktype))
in (let atyp = (btvar_to_typ a)
in (let _91_1546 = (let _91_1545 = (let _91_1544 = (let _91_1543 = (let _91_1542 = (let _91_1541 = (let _91_1540 = (let _91_1539 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (_91_1539)::[])
in (_91_1540, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _91_1541 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _91_1542))
in (_91_1543)::[])
in ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit)))::_91_1544)
in (_91_1545, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _91_1546 FStar_Absyn_Syntax.dummyRange))))

let tforall = (ftv FStar_Absyn_Const.forall_lid forall_kind)

let allT_k = (fun k -> (let _91_1555 = (let _91_1554 = (let _91_1553 = (let _91_1552 = (let _91_1551 = (let _91_1550 = (let _91_1549 = (FStar_Absyn_Syntax.null_t_binder k)
in (_91_1549)::[])
in (_91_1550, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _91_1551 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _91_1552))
in (_91_1553)::[])
in (_91_1554, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _91_1555 FStar_Absyn_Syntax.dummyRange)))

let eqT_k = (fun k -> (let _91_1562 = (let _91_1561 = (let _91_1560 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder k)
in (let _91_1559 = (let _91_1558 = (FStar_Absyn_Syntax.null_t_binder k)
in (_91_1558)::[])
in (_91_1560)::_91_1559))
in (_91_1561, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _91_1562 FStar_Absyn_Syntax.dummyRange)))

let tforall_typ = (fun k -> (let _91_1565 = (allT_k k)
in (ftv FStar_Absyn_Const.allTyp_lid _91_1565)))

let mk_forallT = (fun a b -> (let _91_1577 = (let _91_1576 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _91_1575 = (let _91_1574 = (let _91_1573 = (let _91_1572 = (let _91_1571 = (let _91_1570 = (FStar_Absyn_Syntax.t_binder a)
in (_91_1570)::[])
in (_91_1571, b))
in (FStar_Absyn_Syntax.mk_Typ_lam _91_1572 None b.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _91_1573))
in (_91_1574)::[])
in (_91_1576, _91_1575)))
in (FStar_Absyn_Syntax.mk_Typ_app _91_1577 None b.FStar_Absyn_Syntax.pos)))

let mk_forall = (fun x body -> (let r = FStar_Absyn_Syntax.dummyRange
in (let _91_1588 = (let _91_1587 = (let _91_1586 = (let _91_1585 = (let _91_1584 = (let _91_1583 = (let _91_1582 = (FStar_Absyn_Syntax.v_binder x)
in (_91_1582)::[])
in (_91_1583, body))
in (FStar_Absyn_Syntax.mk_Typ_lam _91_1584 None r))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _91_1585))
in (_91_1586)::[])
in (tforall, _91_1587))
in (FStar_Absyn_Syntax.mk_Typ_app _91_1588 None r))))

let rec close_forall = (fun bs f -> (FStar_List.fold_right (fun b f -> (match ((FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
f
end
| false -> begin
(let body = (FStar_Absyn_Syntax.mk_Typ_lam ((b)::[], f) None f.FStar_Absyn_Syntax.pos)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _91_1598 = (let _91_1597 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _91_1596 = (let _91_1595 = (FStar_Absyn_Syntax.targ body)
in (_91_1595)::[])
in (_91_1597, _91_1596)))
in (FStar_Absyn_Syntax.mk_Typ_app _91_1598 None f.FStar_Absyn_Syntax.pos))
end
| FStar_Util.Inr (x) -> begin
(let _91_1602 = (let _91_1601 = (let _91_1600 = (let _91_1599 = (FStar_Absyn_Syntax.targ body)
in (_91_1599)::[])
in ((FStar_Util.Inl (x.FStar_Absyn_Syntax.sort), Some (FStar_Absyn_Syntax.Implicit)))::_91_1600)
in (tforall, _91_1601))
in (FStar_Absyn_Syntax.mk_Typ_app _91_1602 None f.FStar_Absyn_Syntax.pos))
end))
end)) bs f))

let rec is_wild_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_wild (_26_2239) -> begin
true
end
| _26_2242 -> begin
false
end))

let head_and_args = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(head, args)
end
| _26_2250 -> begin
(t, [])
end)))

let head_and_args_e = (fun e -> (let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(head, args)
end
| _26_2258 -> begin
(e, [])
end)))

let function_formals = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
Some ((bs, c))
end
| _26_2266 -> begin
None
end)))

let is_interpreted = (fun l -> (let theory_syms = (FStar_Absyn_Const.op_Eq)::(FStar_Absyn_Const.op_notEq)::(FStar_Absyn_Const.op_LT)::(FStar_Absyn_Const.op_LTE)::(FStar_Absyn_Const.op_GT)::(FStar_Absyn_Const.op_GTE)::(FStar_Absyn_Const.op_Subtraction)::(FStar_Absyn_Const.op_Minus)::(FStar_Absyn_Const.op_Addition)::(FStar_Absyn_Const.op_Multiply)::(FStar_Absyn_Const.op_Division)::(FStar_Absyn_Const.op_Modulus)::(FStar_Absyn_Const.op_And)::(FStar_Absyn_Const.op_Or)::(FStar_Absyn_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Absyn_Syntax.lid_equals l) theory_syms)))

type qpats =
FStar_Absyn_Syntax.args

type connective =
| QAll of (FStar_Absyn_Syntax.binders * qpats * FStar_Absyn_Syntax.typ)
| QEx of (FStar_Absyn_Syntax.binders * qpats * FStar_Absyn_Syntax.typ)
| BaseConn of (FStar_Absyn_Syntax.lident * FStar_Absyn_Syntax.args)

let is_QAll = (fun _discr_ -> (match (_discr_) with
| QAll (_) -> begin
true
end
| _ -> begin
false
end))

let is_QEx = (fun _discr_ -> (match (_discr_) with
| QEx (_) -> begin
true
end
| _ -> begin
false
end))

let is_BaseConn = (fun _discr_ -> (match (_discr_) with
| BaseConn (_) -> begin
true
end
| _ -> begin
false
end))

let ___QAll____0 = (fun projectee -> (match (projectee) with
| QAll (_26_2271) -> begin
_26_2271
end))

let ___QEx____0 = (fun projectee -> (match (projectee) with
| QEx (_26_2274) -> begin
_26_2274
end))

let ___BaseConn____0 = (fun projectee -> (match (projectee) with
| BaseConn (_26_2277) -> begin
_26_2277
end))

let destruct_typ_as_formula = (fun f -> (let destruct_base_conn = (fun f -> (let _26_2283 = (true, false)
in (match (_26_2283) with
| (type_sort, term_sort) -> begin
(let oneType = (type_sort)::[]
in (let twoTypes = (type_sort)::(type_sort)::[]
in (let threeTys = (type_sort)::(type_sort)::(type_sort)::[]
in (let twoTerms = (term_sort)::(term_sort)::[]
in (let connectives = ((FStar_Absyn_Const.true_lid, []))::((FStar_Absyn_Const.false_lid, []))::((FStar_Absyn_Const.and_lid, twoTypes))::((FStar_Absyn_Const.or_lid, twoTypes))::((FStar_Absyn_Const.imp_lid, twoTypes))::((FStar_Absyn_Const.iff_lid, twoTypes))::((FStar_Absyn_Const.ite_lid, threeTys))::((FStar_Absyn_Const.not_lid, oneType))::((FStar_Absyn_Const.eqT_lid, twoTypes))::((FStar_Absyn_Const.eq2_lid, twoTerms))::((FStar_Absyn_Const.eq2_lid, (FStar_List.append twoTypes twoTerms)))::[]
in (let rec aux = (fun f _26_2293 -> (match (_26_2293) with
| (lid, arity) -> begin
(let _26_2296 = (head_and_args f)
in (match (_26_2296) with
| (t, args) -> begin
(match ((((is_constructor t lid) && ((FStar_List.length args) = (FStar_List.length arity))) && (FStar_List.forall2 (fun arg flag -> (match (arg) with
| (FStar_Util.Inl (_26_2300), _26_2303) -> begin
(flag = type_sort)
end
| (FStar_Util.Inr (_26_2306), _26_2309) -> begin
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
in (FStar_Util.find_map connectives (aux f))))))))
end)))
in (let patterns = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, pats)) -> begin
(let _91_1666 = (compress_typ t)
in (pats, _91_1666))
end
| _26_2320 -> begin
(let _91_1667 = (compress_typ t)
in ([], _91_1667))
end)))
in (let destruct_q_conn = (fun t -> (let is_q = (fun fa l -> (match (fa) with
| true -> begin
(is_forall l)
end
| false -> begin
(is_exists l)
end))
in (let flat = (fun t -> (let _26_2330 = (head_and_args t)
in (match (_26_2330) with
| (t, args) -> begin
(let _91_1681 = (FStar_All.pipe_right args (FStar_List.map (fun _26_26 -> (match (_26_26) with
| (FStar_Util.Inl (t), imp) -> begin
(let _91_1678 = (let _91_1677 = (compress_typ t)
in FStar_Util.Inl (_91_1677))
in (_91_1678, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _91_1680 = (let _91_1679 = (compress_exp e)
in FStar_Util.Inr (_91_1679))
in (_91_1680, imp))
end))))
in (t, _91_1681))
end)))
in (let rec aux = (fun qopt out t -> (match ((let _91_1688 = (flat t)
in (qopt, _91_1688))) with
| ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _::(FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_q fa tc.FStar_Absyn_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _::(FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_qlid tc.FStar_Absyn_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Absyn_Syntax.v))) ((b)::out) t2)
end
| (Some (true), _26_2478) -> begin
(let _26_2482 = (patterns t)
in (match (_26_2482) with
| (pats, body) -> begin
Some (QAll (((FStar_List.rev out), pats, body)))
end))
end
| (Some (false), _26_2486) -> begin
(let _26_2490 = (patterns t)
in (match (_26_2490) with
| (pats, body) -> begin
Some (QEx (((FStar_List.rev out), pats, body)))
end))
end
| _26_2492 -> begin
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
