
open Prims
let handle_err = (fun warning ret e -> (match (e) with
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(let _26_34 = (let _93_8 = (let _93_7 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s : %s\n%s\n" _93_7 (if warning then begin
"Warning"
end else begin
"Error"
end) msg))
in (FStar_Util.print_string _93_8))
in ())
end
| FStar_Util.NYI (s) -> begin
(let _26_38 = (let _93_9 = (FStar_Util.format1 "Feature not yet implemented: %s" s)
in (FStar_Util.print_string _93_9))
in ())
end
| FStar_Absyn_Syntax.Err (s) -> begin
(let _93_10 = (FStar_Util.format1 "Error: %s" s)
in (FStar_Util.print_string _93_10))
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

let is_Mkgensym_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkgensym_t"))))

let gs = (let ctr = (FStar_Util.mk_ref 0)
in (let n_resets = (FStar_Util.mk_ref 0)
in {gensym = (fun _26_61 -> (match (()) with
| () -> begin
(let _93_38 = (let _93_35 = (let _93_34 = (let _93_33 = (FStar_ST.read n_resets)
in (FStar_Util.string_of_int _93_33))
in (Prims.strcat "_" _93_34))
in (Prims.strcat _93_35 "_"))
in (let _93_37 = (let _93_36 = (let _26_62 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
in (FStar_Util.string_of_int _93_36))
in (Prims.strcat _93_38 _93_37)))
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
(let _93_47 = (gensym ())
in (let _93_46 = (gensyms (n - 1))
in (_93_47)::_93_46))
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

let freshen_bvd = (fun bvd' -> (let _93_88 = (let _93_87 = (genident (Some ((range_of_bvd bvd'))))
in (bvd'.FStar_Absyn_Syntax.ppname, _93_87))
in (mkbvd _93_88)))

let freshen_bvar = (fun b -> (let _93_90 = (freshen_bvd b.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _93_90 b.FStar_Absyn_Syntax.sort)))

let gen_bvar = (fun sort -> (let bvd = (new_bvd None)
in (bvd_to_bvar_s bvd sort)))

let gen_bvar_p = (fun r sort -> (let bvd = (new_bvd (Some (r)))
in (bvd_to_bvar_s bvd sort)))

let bvdef_of_str = (fun s -> (let f = (fun s -> (let id = (FStar_Absyn_Syntax.id_of_text s)
in (mkbvd (id, id))))
in (f s)))

let set_bvd_range = (fun bvd r -> (let _93_99 = (FStar_Absyn_Syntax.mk_ident (bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText, r))
in (let _93_98 = (FStar_Absyn_Syntax.mk_ident (bvd.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText, r))
in {FStar_Absyn_Syntax.ppname = _93_99; FStar_Absyn_Syntax.realname = _93_98})))

let set_lid_range = (fun l r -> (let ids = (FStar_All.pipe_right (FStar_List.append l.FStar_Absyn_Syntax.ns ((l.FStar_Absyn_Syntax.ident)::[])) (FStar_List.map (fun i -> (FStar_Absyn_Syntax.mk_ident (i.FStar_Absyn_Syntax.idText, r)))))
in (FStar_Absyn_Syntax.lid_of_ids ids)))

let fv = (fun l -> (let _93_107 = (FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l FStar_Absyn_Syntax.tun _93_107)))

let fvvar_of_lid = (fun l t -> (let _93_110 = (FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l t _93_110)))

let fvar = (fun dc l r -> (let _93_119 = (let _93_118 = (let _93_117 = (set_lid_range l r)
in (fv _93_117))
in (_93_118, dc))
in (FStar_Absyn_Syntax.mk_Exp_fvar _93_119 None r)))

let ftv = (fun l k -> (let _93_126 = (let _93_124 = (FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l k _93_124))
in (let _93_125 = (FStar_Absyn_Syntax.range_of_lid l)
in (FStar_Absyn_Syntax.mk_Typ_const _93_126 None _93_125))))

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
(let _93_131 = (let _93_130 = (btvar_to_typ a)
in FStar_Util.Inl (_93_130))
in (_93_131, imp))
end
| FStar_Util.Inr (x) -> begin
(let _93_133 = (let _93_132 = (bvar_to_exp x)
in FStar_Util.Inr (_93_132))
in (_93_133, imp))
end)
end))

let args_of_non_null_binders = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
[]
end else begin
(let _93_137 = (arg_of_non_null_binder b)
in (_93_137)::[])
end))))

let args_of_binders = (fun binders -> (let _93_147 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(let b = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _93_142 = (let _93_141 = (gen_bvar a.FStar_Absyn_Syntax.sort)
in FStar_Util.Inl (_93_141))
in (_93_142, (Prims.snd b)))
end
| FStar_Util.Inr (x) -> begin
(let _93_144 = (let _93_143 = (gen_bvar x.FStar_Absyn_Syntax.sort)
in FStar_Util.Inr (_93_143))
in (_93_144, (Prims.snd b)))
end)
in (let _93_145 = (arg_of_non_null_binder b)
in (b, _93_145)))
end else begin
(let _93_146 = (arg_of_non_null_binder b)
in (b, _93_146))
end)))
in (FStar_All.pipe_right _93_147 FStar_List.unzip)))

let name_binders = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(let b = (let _93_153 = (let _93_152 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _93_152))
in (FStar_Absyn_Syntax.id_of_text _93_153))
in (let b = (bvd_to_bvar_s (mkbvd (b, b)) a.FStar_Absyn_Syntax.sort)
in (FStar_Util.Inl (b), imp)))
end
| (FStar_Util.Inr (y), imp) -> begin
(let x = (let _93_155 = (let _93_154 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _93_154))
in (FStar_Absyn_Syntax.id_of_text _93_155))
in (let x = (bvd_to_bvar_s (mkbvd (x, x)) y.FStar_Absyn_Syntax.sort)
in (FStar_Util.Inr (x), imp)))
end)
end else begin
b
end))))

let name_function_binders = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, comp) -> begin
(let _93_159 = (let _93_158 = (name_binders binders)
in (_93_158, comp))
in (FStar_Absyn_Syntax.mk_Typ_fun _93_159 None t.FStar_Absyn_Syntax.pos))
end
| _26_215 -> begin
t
end))

let null_binders_of_tks = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _26_2 -> (match (_26_2) with
| (FStar_Util.Inl (k), imp) -> begin
(let _93_164 = (let _93_163 = (FStar_Absyn_Syntax.null_t_binder k)
in (FStar_All.pipe_left Prims.fst _93_163))
in (_93_164, imp))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _93_166 = (let _93_165 = (FStar_Absyn_Syntax.null_v_binder t)
in (FStar_All.pipe_left Prims.fst _93_165))
in (_93_166, imp))
end)))))

let binders_of_tks = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _26_3 -> (match (_26_3) with
| (FStar_Util.Inl (k), imp) -> begin
(let _93_171 = (let _93_170 = (gen_bvar_p k.FStar_Absyn_Syntax.pos k)
in FStar_Util.Inl (_93_170))
in (_93_171, imp))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _93_173 = (let _93_172 = (gen_bvar_p t.FStar_Absyn_Syntax.pos t)
in FStar_Util.Inr (_93_172))
in (_93_173, imp))
end)))))

let binders_of_freevars = (fun fvs -> (let _93_179 = (let _93_176 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.ftvs)
in (FStar_All.pipe_right _93_176 (FStar_List.map FStar_Absyn_Syntax.t_binder)))
in (let _93_178 = (let _93_177 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_All.pipe_right _93_177 (FStar_List.map FStar_Absyn_Syntax.v_binder)))
in (FStar_List.append _93_179 _93_178))))

let subst_to_string = (fun s -> (let _93_182 = (FStar_All.pipe_right s (FStar_List.map (fun _26_4 -> (match (_26_4) with
| FStar_Util.Inl (b, _26_241) -> begin
b.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText
end
| FStar_Util.Inr (x, _26_246) -> begin
x.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText
end))))
in (FStar_All.pipe_right _93_182 (FStar_String.concat ", "))))

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
(let _93_207 = (let _93_206 = (compose_subst s' s)
in (let _93_205 = (FStar_Util.mk_ref None)
in (t', _93_206, _93_205)))
in (FStar_Absyn_Syntax.mk_Typ_delayed _93_207 None t.FStar_Absyn_Syntax.pos))
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
(let _93_212 = (let _93_211 = (FStar_Util.mk_ref None)
in (t0, s, _93_211))
in (FStar_Absyn_Syntax.mk_Typ_delayed _93_212 None t.FStar_Absyn_Syntax.pos))
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
(let _93_217 = (let _93_216 = (compose_subst s' s)
in (let _93_215 = (FStar_Util.mk_ref None)
in (e, _93_216, _93_215)))
in (FStar_Absyn_Syntax.mk_Exp_delayed _93_217 None e.FStar_Absyn_Syntax.pos))
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
(let _93_221 = (let _93_220 = (FStar_Util.mk_ref None)
in (e0, s, _93_220))
in (FStar_Absyn_Syntax.mk_Exp_delayed _93_221 None e0.FStar_Absyn_Syntax.pos))
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
(let _93_226 = (let _93_225 = (compose_subst s' s)
in (let _93_224 = (FStar_Util.mk_ref None)
in (k, _93_225, _93_224)))
in (FStar_Absyn_Syntax.mk_Kind_delayed _93_226 k0.FStar_Absyn_Syntax.pos))
end
| _26_363 -> begin
(let _93_228 = (let _93_227 = (FStar_Util.mk_ref None)
in (k0, s, _93_227))
in (FStar_Absyn_Syntax.mk_Kind_delayed _93_228 k0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_flags' = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _26_7 -> (match (_26_7) with
| FStar_Absyn_Syntax.DECREASES (a) -> begin
(let _93_232 = (subst_exp' s a)
in FStar_Absyn_Syntax.DECREASES (_93_232))
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
in (let _93_242 = (subst_typ' s t.FStar_Absyn_Syntax.result_typ)
in (let _93_241 = (FStar_List.map (fun _26_8 -> (match (_26_8) with
| (FStar_Util.Inl (t), imp) -> begin
(let _93_237 = (let _93_236 = (subst_typ' s t)
in FStar_Util.Inl (_93_236))
in (_93_237, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _93_239 = (let _93_238 = (subst_exp' s e)
in FStar_Util.Inr (_93_238))
in (_93_239, imp))
end)) t.FStar_Absyn_Syntax.effect_args)
in (let _93_240 = (subst_flags' s t.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _26_377.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _93_242; FStar_Absyn_Syntax.effect_args = _93_241; FStar_Absyn_Syntax.flags = _93_240}))))
end))
and subst_comp' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _26_394 -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _93_245 = (subst_typ' s t)
in (FStar_Absyn_Syntax.mk_Total _93_245))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _93_246 = (subst_comp_typ' s ct)
in (FStar_Absyn_Syntax.mk_Comp _93_246))
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
(let _93_274 = (let _93_273 = (let _26_418 = a
in (let _93_272 = (subst_kind s a.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _26_418.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _93_272; FStar_Absyn_Syntax.p = _26_418.FStar_Absyn_Syntax.p}))
in FStar_Util.Inl (_93_273))
in (_93_274, imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _93_277 = (let _93_276 = (let _26_424 = x
in (let _93_275 = (subst_typ s x.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _26_424.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _93_275; FStar_Absyn_Syntax.p = _26_424.FStar_Absyn_Syntax.p}))
in FStar_Util.Inr (_93_276))
in (_93_277, imp))
end))

let subst_arg = (fun s _26_10 -> (match (_26_10) with
| (FStar_Util.Inl (t), imp) -> begin
(let _93_281 = (let _93_280 = (subst_typ s t)
in FStar_Util.Inl (_93_280))
in (_93_281, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _93_283 = (let _93_282 = (subst_exp s e)
in FStar_Util.Inr (_93_282))
in (_93_283, imp))
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

let mk_subst_one_binder = (fun b1 b2 -> if ((FStar_Absyn_Syntax.is_null_binder b1) || (FStar_Absyn_Syntax.is_null_binder b2)) then begin
[]
end else begin
(match (((Prims.fst b1), (Prims.fst b2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
if (bvar_eq a b) then begin
[]
end else begin
(let _93_298 = (let _93_297 = (let _93_296 = (btvar_to_typ a)
in (b.FStar_Absyn_Syntax.v, _93_296))
in FStar_Util.Inl (_93_297))
in (_93_298)::[])
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (bvar_eq x y) then begin
[]
end else begin
(let _93_301 = (let _93_300 = (let _93_299 = (bvar_to_exp x)
in (y.FStar_Absyn_Syntax.v, _93_299))
in FStar_Util.Inr (_93_300))
in (_93_301)::[])
end
end
| _26_485 -> begin
[]
end)
end)

let mk_subst_binder = (fun bs1 bs2 -> (let rec aux = (fun out bs1 bs2 -> (match ((bs1, bs2)) with
| ([], []) -> begin
Some (out)
end
| (b1::bs1, b2::bs2) -> begin
(let _93_313 = (let _93_312 = (mk_subst_one_binder b1 b2)
in (FStar_List.append _93_312 out))
in (aux _93_313 bs1 bs2))
end
| _26_503 -> begin
None
end))
in (aux [] bs1 bs2)))

let subst_of_list = (fun formals actuals -> if ((FStar_List.length formals) = (FStar_List.length actuals)) then begin
(FStar_List.map2 subst_formal formals actuals)
end else begin
(FStar_All.failwith "Ill-formed substitution")
end)

type red_ctrl =
{stop_if_empty_subst : Prims.bool; descend : Prims.bool}

let is_Mkred_ctrl = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkred_ctrl"))))

let alpha_ctrl = {stop_if_empty_subst = false; descend = true}

let subst_ctrl = {stop_if_empty_subst = true; descend = true}

let null_ctrl = {stop_if_empty_subst = true; descend = false}

let extend_subst = (fun e s -> (FStar_List.append (((mk_subst e))::[]) s))

let map_knd = (fun s vk mt me descend binders k -> (let _93_334 = (subst_kind' s k)
in (_93_334, descend)))

let map_typ = (fun s mk vt me descend binders t -> (let _93_342 = (subst_typ' s t)
in (_93_342, descend)))

let map_exp = (fun s mk me ve descend binders e -> (let _93_350 = (subst_exp' s e)
in (_93_350, descend)))

let map_flags = (fun s map_exp descend binders flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _26_11 -> (match (_26_11) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _93_367 = (let _93_366 = (map_exp descend binders e)
in (FStar_All.pipe_right _93_366 Prims.fst))
in FStar_Absyn_Syntax.DECREASES (_93_367))
end
| f -> begin
f
end)))))

let map_comp = (fun s mk map_typ map_exp descend binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _26_552 = (map_typ descend binders t)
in (match (_26_552) with
| (t, descend) -> begin
(let _93_390 = (FStar_Absyn_Syntax.mk_Total t)
in (_93_390, descend))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _26_557 = (map_typ descend binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_26_557) with
| (t, descend) -> begin
(let _26_560 = (FStar_Absyn_Visit.map_args map_typ map_exp descend binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_26_560) with
| (args, descend) -> begin
(let _93_393 = (let _93_392 = (let _26_561 = ct
in (let _93_391 = (map_flags s map_exp descend binders ct.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _26_561.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _93_391}))
in (FStar_Absyn_Syntax.mk_Comp _93_392))
in (_93_393, descend))
end))
end))
end))

let visit_knd = (fun s vk mt me ctrl binders k -> (let k = (FStar_Absyn_Visit.compress_kind k)
in if ctrl.descend then begin
(let _26_574 = (vk null_ctrl binders k)
in (match (_26_574) with
| (k, _26_573) -> begin
(k, ctrl)
end))
end else begin
(map_knd s vk mt me null_ctrl binders k)
end))

let rec compress_kind = (fun k -> (let k = (FStar_Absyn_Visit.compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (k', s, m) -> begin
(let k' = (let _93_439 = (FStar_Absyn_Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] k')
in (FStar_All.pipe_left Prims.fst _93_439))
in (let k' = (compress_kind k')
in (let _26_584 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k')))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, actuals) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (formals, k') -> begin
(let _93_441 = (let _93_440 = (subst_of_list formals actuals)
in (subst_kind _93_440 k'))
in (compress_kind _93_441))
end
| _26_597 -> begin
if ((FStar_List.length actuals) = 0) then begin
k
end else begin
(FStar_All.failwith "Wrong arity for kind unifier")
end
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
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((FStar_Util.Inl (a), imp))::bs, boundvars, s)
end else begin
(let boundvars' = (FStar_Util.Inl (a.FStar_Absyn_Syntax.v))::boundvars
in (let _26_637 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(FStar_Util.Inl (a), s, boundvars')
end
| _26_631 -> begin
(let b = (let _93_518 = (freshen_bvd a.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _93_518 k))
in (let s = (let _93_521 = (let _93_520 = (let _93_519 = (btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _93_519))
in FStar_Util.Inl (_93_520))
in (extend_subst _93_521 s))
in (FStar_Util.Inl (b), s, (FStar_Util.Inl (b.FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_26_637) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end)
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _26_645 = (map_typ s mk vt me null_ctrl boundvars x.FStar_Absyn_Syntax.sort)
in (match (_26_645) with
| (t, _26_644) -> begin
(let x = (let _26_646 = x
in {FStar_Absyn_Syntax.v = _26_646.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _26_646.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((FStar_Util.Inr (x), imp))::bs, boundvars, s)
end else begin
(let boundvars' = (FStar_Util.Inr (x.FStar_Absyn_Syntax.v))::boundvars
in (let _26_658 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(FStar_Util.Inr (x), s, boundvars')
end
| _26_652 -> begin
(let y = (let _93_531 = (freshen_bvd x.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _93_531 t))
in (let s = (let _93_534 = (let _93_533 = (let _93_532 = (bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _93_532))
in FStar_Util.Inr (_93_533))
in (extend_subst _93_534 s))
in (FStar_Util.Inr (y), s, (FStar_Util.Inr (y.FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_26_658) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end)
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
(let _93_545 = (let _93_544 = (map_typ s mk vt me null_ctrl boundvars t)
in (FStar_All.pipe_left Prims.fst _93_544))
in FStar_Util.Inl (_93_545))
end
| (_26_673, FStar_Util.Inr (c)) -> begin
(let _93_568 = (let _93_567 = (map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl boundvars c)
in (FStar_All.pipe_left Prims.fst _93_567))
in FStar_Util.Inr (_93_568))
end)
in ((FStar_List.rev bs), tc))
end)))
in (let t0 = t
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_26_680) -> begin
(let _93_570 = (let _93_569 = (subst_typ' s t0)
in (FStar_All.pipe_left compress_typ _93_569))
in (_93_570, ctrl))
end
| _26_683 when (not (ctrl.descend)) -> begin
(map_typ s mk vt me null_ctrl boundvars t)
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((visit_prod bs (FStar_Util.Inr (c)))) with
| (bs, FStar_Util.Inr (c)) -> begin
(let _93_580 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t0.FStar_Absyn_Syntax.pos)
in (_93_580, ctrl))
end
| _26_693 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((visit_prod (((FStar_Util.Inr (x), None))::[]) (FStar_Util.Inl (t)))) with
| ((FStar_Util.Inr (x), _26_701)::[], FStar_Util.Inl (t)) -> begin
(let _93_581 = (FStar_Absyn_Syntax.mk_Typ_refine (x, t) None t0.FStar_Absyn_Syntax.pos)
in (_93_581, ctrl))
end
| _26_708 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(match ((visit_prod bs (FStar_Util.Inl (t)))) with
| (bs, FStar_Util.Inl (t)) -> begin
(let _93_582 = (FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t0.FStar_Absyn_Syntax.pos)
in (_93_582, ctrl))
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
(let res = (let _93_602 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] t')
in (FStar_All.pipe_left Prims.fst _93_602))
in (let res = (compress_typ' res)
in (let _26_736 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(let t = (let _93_604 = (mk_t ())
in (compress_typ' _93_604))
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
(let _93_670 = (let _93_669 = (subst_exp' s e)
in (FStar_All.pipe_left compress_exp _93_669))
in (_93_670, ctrl))
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
(let e = (let _93_699 = (FStar_Absyn_Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] e')
in (FStar_All.pipe_left Prims.fst _93_699))
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
in (let doit = (fun t -> (let _93_724 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp alpha_ctrl [] t)
in (FStar_All.pipe_left Prims.fst _93_724)))
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_lam (bs, _)) | (FStar_Absyn_Syntax.Typ_fun (bs, _)) -> begin
if (FStar_Util.for_all FStar_Absyn_Syntax.is_null_binder bs) then begin
t
end else begin
(doit t)
end
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
(let _93_731 = (compress_typ t)
in Some (_93_731))
end))

let mk_discriminator = (fun lid -> (let _93_736 = (let _93_735 = (let _93_734 = (FStar_Absyn_Syntax.mk_ident ((Prims.strcat "is_" lid.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText), lid.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idRange))
in (_93_734)::[])
in (FStar_List.append lid.FStar_Absyn_Syntax.ns _93_735))
in (FStar_Absyn_Syntax.lid_of_ids _93_736)))

let is_name = (fun lid -> (let c = (FStar_Util.char_at lid.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText 0)
in (FStar_Util.is_upper c)))

let ml_comp = (fun t r -> (let _93_744 = (let _93_743 = (set_lid_range FStar_Absyn_Const.effect_ML_lid r)
in {FStar_Absyn_Syntax.effect_name = _93_743; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.MLEFFECT)::[]})
in (FStar_Absyn_Syntax.mk_Comp _93_744)))

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

let is_pure_or_ghost_function = (fun t -> (match ((let _93_783 = (compress_typ t)
in _93_783.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_26_930, c) -> begin
(is_pure_or_ghost_comp c)
end
| _26_935 -> begin
true
end))

let is_lemma = (fun t -> (match ((let _93_786 = (compress_typ t)
in _93_786.FStar_Absyn_Syntax.n)) with
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

let is_smt_lemma = (fun t -> (match ((let _93_789 = (compress_typ t)
in _93_789.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_26_950, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) when (FStar_Absyn_Syntax.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| _req::_ens::(FStar_Util.Inr (pats), _26_961)::_26_957 -> begin
(match ((let _93_790 = (unmeta_exp pats)
in _93_790.FStar_Absyn_Syntax.n)) with
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

let rec is_atom = (fun e -> (match ((let _93_800 = (compress_exp e)
in _93_800.FStar_Absyn_Syntax.n)) with
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

let is_fun = (fun e -> (match ((let _93_814 = (compress_exp e)
in _93_814.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (_26_1092) -> begin
true
end
| _26_1095 -> begin
false
end))

let is_function_typ = (fun t -> (match ((let _93_817 = (compress_typ t)
in _93_817.FStar_Absyn_Syntax.n)) with
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
(let _93_851 = (let _93_850 = (let _93_849 = (let _93_848 = (FStar_Absyn_Syntax.range_of_lid l)
in (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l _93_848))
in (_93_849, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_93_850))
in (FStar_Absyn_Syntax.mk_Exp_meta _93_851))
end
| _26_1393 -> begin
(let _93_856 = (let _93_855 = (let _93_854 = (let _93_853 = (let _93_852 = (FStar_Absyn_Syntax.range_of_lid l)
in (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l _93_852))
in (mk_exp_app _93_853 args))
in (_93_854, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_93_855))
in (FStar_Absyn_Syntax.mk_Exp_meta _93_856))
end))

let mangle_field_name = (fun x -> (FStar_Absyn_Syntax.mk_ident ((Prims.strcat "^fname^" x.FStar_Absyn_Syntax.idText), x.FStar_Absyn_Syntax.idRange)))

let unmangle_field_name = (fun x -> if (FStar_Util.starts_with x.FStar_Absyn_Syntax.idText "^fname^") then begin
(let _93_862 = (let _93_861 = (FStar_Util.substring_from x.FStar_Absyn_Syntax.idText 7)
in (_93_861, x.FStar_Absyn_Syntax.idRange))
in (FStar_Absyn_Syntax.mk_ident _93_862))
end else begin
x
end)

let mk_field_projector_name = (fun lid x i -> (let nm = if (FStar_Absyn_Syntax.is_null_bvar x) then begin
(let _93_868 = (let _93_867 = (let _93_866 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _93_866))
in (_93_867, x.FStar_Absyn_Syntax.p))
in (FStar_Absyn_Syntax.mk_ident _93_868))
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (let y = (let _26_1402 = x.FStar_Absyn_Syntax.v
in {FStar_Absyn_Syntax.ppname = nm; FStar_Absyn_Syntax.realname = _26_1402.FStar_Absyn_Syntax.realname})
in (let _93_873 = (let _93_872 = (let _93_871 = (FStar_Absyn_Syntax.ids_of_lid lid)
in (let _93_870 = (let _93_869 = (unmangle_field_name nm)
in (_93_869)::[])
in (FStar_List.append _93_871 _93_870)))
in (FStar_Absyn_Syntax.lid_of_ids _93_872))
in (_93_873, y)))))

let unchecked_unify = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (_26_1408) -> begin
(let _93_878 = (let _93_877 = (let _93_876 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _93_876))
in (FStar_Util.format1 "Changing a fixed uvar! U%s\n" _93_877))
in (FStar_All.failwith _93_878))
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

let union_uvs = (fun uvs1 uvs2 -> (let _93_907 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_k uvs2.FStar_Absyn_Syntax.uvars_k)
in (let _93_906 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_t uvs2.FStar_Absyn_Syntax.uvars_t)
in (let _93_905 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_e uvs2.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _93_907; FStar_Absyn_Syntax.uvars_t = _93_906; FStar_Absyn_Syntax.uvars_e = _93_905}))))

let union_fvs = (fun fvs1 fvs2 -> (let _93_913 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs)
in (let _93_912 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)
in {FStar_Absyn_Syntax.ftvs = _93_913; FStar_Absyn_Syntax.fxvs = _93_912})))

let union_fvs_uvs = (fun _26_1456 _26_1459 -> (match ((_26_1456, _26_1459)) with
| ((fvs1, uvs1), (fvs2, uvs2)) -> begin
(let _93_919 = (union_fvs fvs1 fvs2)
in (let _93_918 = (union_uvs uvs1 uvs2)
in (_93_919, _93_918)))
end))

let sub_fv = (fun _26_1462 _26_1465 -> (match ((_26_1462, _26_1465)) with
| ((fvs, uvs), (tvars, vvars)) -> begin
(let _93_940 = (let _26_1466 = fvs
in (let _93_939 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.ftvs tvars)
in (let _93_938 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.fxvs vvars)
in {FStar_Absyn_Syntax.ftvs = _93_939; FStar_Absyn_Syntax.fxvs = _93_938})))
in (_93_940, uvs))
end))

let stash = (fun uvonly s _26_1474 -> (match (_26_1474) with
| (fvs, uvs) -> begin
(let _26_1475 = (FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.uvs (Some (uvs)))
in if uvonly then begin
()
end else begin
(FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.fvs (Some (fvs)))
end)
end))

let single_fv = (fun x -> (let _93_951 = (FStar_Absyn_Syntax.new_ftv_set ())
in (FStar_Util.set_add x _93_951)))

let single_uv = (fun u -> (let _93_959 = (FStar_Absyn_Syntax.new_uv_set ())
in (FStar_Util.set_add u _93_959)))

let single_uvt = (fun u -> (let _93_967 = (FStar_Absyn_Syntax.new_uvt_set ())
in (FStar_Util.set_add u _93_967)))

let rec vs_typ' = (fun t uvonly cont -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_26_1486) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end else begin
(let _93_1082 = (let _93_1081 = (let _26_1490 = FStar_Absyn_Syntax.no_fvs
in (let _93_1080 = (single_fv a)
in {FStar_Absyn_Syntax.ftvs = _93_1080; FStar_Absyn_Syntax.fxvs = _26_1490.FStar_Absyn_Syntax.fxvs}))
in (_93_1081, FStar_Absyn_Syntax.no_uvs))
in (cont _93_1082))
end
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let _93_1085 = (let _93_1084 = (let _26_1496 = FStar_Absyn_Syntax.no_uvs
in (let _93_1083 = (single_uvt (uv, k))
in {FStar_Absyn_Syntax.uvars_k = _26_1496.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _93_1083; FStar_Absyn_Syntax.uvars_e = _26_1496.FStar_Absyn_Syntax.uvars_e}))
in (FStar_Absyn_Syntax.no_fvs, _93_1084))
in (cont _93_1085))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(vs_binders bs uvonly (fun _26_1508 -> (match (_26_1508) with
| (bvs, vs1) -> begin
(vs_comp c uvonly (fun vs2 -> (let _93_1089 = (let _93_1088 = (union_fvs_uvs vs1 vs2)
in (sub_fv _93_1088 bvs))
in (cont _93_1089))))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(vs_binders bs uvonly (fun _26_1516 -> (match (_26_1516) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _93_1093 = (let _93_1092 = (union_fvs_uvs vs1 vs2)
in (sub_fv _93_1092 bvs))
in (cont _93_1093))))
end)))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(vs_binders (((FStar_Util.Inr (x), None))::[]) uvonly (fun _26_1524 -> (match (_26_1524) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _93_1097 = (let _93_1096 = (union_fvs_uvs vs1 vs2)
in (sub_fv _93_1096 bvs))
in (cont _93_1097))))
end)))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(vs_typ t uvonly (fun vs1 -> (vs_args args uvonly (fun vs2 -> (let _93_1100 = (union_fvs_uvs vs1 vs2)
in (cont _93_1100))))))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _26_1534) -> begin
(vs_typ t uvonly cont)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _26_1540)) -> begin
(vs_typ t1 uvonly (fun vs1 -> (vs_typ t2 uvonly (fun vs2 -> (let _93_1103 = (union_fvs_uvs vs1 vs2)
in (cont _93_1103))))))
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
(let _93_1140 = (let _93_1139 = (let _93_1137 = (FStar_Util.set_add a tvars)
in (_93_1137, vvars))
in (let _93_1138 = (union_fvs_uvs vs vs2)
in (_93_1139, _93_1138)))
in (cont _93_1140))
end)))))
end
| (FStar_Util.Inr (x), _26_1595)::rest -> begin
(vs_typ x.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _26_1603 -> (match (_26_1603) with
| ((tvars, vvars), vs2) -> begin
(let _93_1164 = (let _93_1163 = (let _93_1161 = (FStar_Util.set_add x vvars)
in (tvars, _93_1161))
in (let _93_1162 = (union_fvs_uvs vs vs2)
in (_93_1163, _93_1162)))
in (cont _93_1164))
end)))))
end))
and vs_args = (fun args uvonly cont -> (match (args) with
| [] -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| (FStar_Util.Inl (t), _26_1613)::tl -> begin
(vs_typ t uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _93_1168 = (union_fvs_uvs ft1 ft2)
in (cont _93_1168))))))
end
| (FStar_Util.Inr (e), _26_1622)::tl -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _93_1171 = (union_fvs_uvs ft1 ft2)
in (cont _93_1171))))))
end))
and vs_typ = (fun t uvonly cont -> (match ((let _93_1174 = (FStar_ST.read t.FStar_Absyn_Syntax.fvs)
in (let _93_1173 = (FStar_ST.read t.FStar_Absyn_Syntax.uvs)
in (_93_1174, _93_1173)))) with
| (Some (_26_1632), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_typ' t uvonly (fun fvs -> (let _26_1640 = (stash uvonly t fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_typ' t uvonly (fun fvs -> (let _26_1647 = (stash uvonly t fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_kind' = (fun k uvonly cont -> (let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_26_1660, k) -> begin
(let _93_1179 = (let _93_1178 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "%s: Impossible ... found a Kind_lam bare" _93_1178))
in (FStar_All.failwith _93_1179))
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
(let _93_1183 = (let _93_1182 = (let _26_1677 = uvs
in (let _93_1181 = (FStar_Util.set_add uv uvs.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _93_1181; FStar_Absyn_Syntax.uvars_t = _26_1677.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _26_1677.FStar_Absyn_Syntax.uvars_e}))
in (fvs, _93_1182))
in (cont _93_1183))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev (_26_1680, k) -> begin
(vs_kind k uvonly cont)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(vs_binders bs uvonly (fun _26_1690 -> (match (_26_1690) with
| (bvs, vs1) -> begin
(vs_kind k uvonly (fun vs2 -> (let _93_1187 = (let _93_1186 = (union_fvs_uvs vs1 vs2)
in (sub_fv _93_1186 bvs))
in (cont _93_1187))))
end)))
end)))
and vs_kind = (fun k uvonly cont -> (match ((let _93_1190 = (FStar_ST.read k.FStar_Absyn_Syntax.fvs)
in (let _93_1189 = (FStar_ST.read k.FStar_Absyn_Syntax.uvs)
in (_93_1190, _93_1189)))) with
| (Some (_26_1697), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_kind' k uvonly (fun fvs -> (let _26_1705 = (stash uvonly k fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_kind' k uvonly (fun fvs -> (let _26_1712 = (stash uvonly k fvs)
in (cont fvs))))
end
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
(let _93_1196 = (let _93_1195 = (let _26_1737 = FStar_Absyn_Syntax.no_uvs
in (let _93_1194 = (single_uvt (uv, t))
in {FStar_Absyn_Syntax.uvars_k = _26_1737.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _26_1737.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _93_1194}))
in (FStar_Absyn_Syntax.no_fvs, _93_1195))
in (cont _93_1196))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end else begin
(let _93_1199 = (let _93_1198 = (let _26_1741 = FStar_Absyn_Syntax.no_fvs
in (let _93_1197 = (single_fv x)
in {FStar_Absyn_Syntax.ftvs = _26_1741.FStar_Absyn_Syntax.ftvs; FStar_Absyn_Syntax.fxvs = _93_1197}))
in (_93_1198, FStar_Absyn_Syntax.no_uvs))
in (cont _93_1199))
end
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _26_1745, _26_1747) -> begin
(vs_exp e uvonly cont)
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(vs_binders bs uvonly (fun _26_1756 -> (match (_26_1756) with
| (bvs, vs1) -> begin
(vs_exp e uvonly (fun vs2 -> (let _93_1203 = (let _93_1202 = (union_fvs_uvs vs1 vs2)
in (sub_fv _93_1202 bvs))
in (cont _93_1203))))
end)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args args uvonly (fun ft2 -> (let _93_1206 = (union_fvs_uvs ft1 ft2)
in (cont _93_1206))))))
end
| (FStar_Absyn_Syntax.Exp_match (_)) | (FStar_Absyn_Syntax.Exp_let (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _26_1772)) -> begin
(vs_exp e uvonly cont)
end)))
and vs_exp = (fun e uvonly cont -> (match ((let _93_1209 = (FStar_ST.read e.FStar_Absyn_Syntax.fvs)
in (let _93_1208 = (FStar_ST.read e.FStar_Absyn_Syntax.uvs)
in (_93_1209, _93_1208)))) with
| (Some (_26_1781), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_exp' e uvonly (fun fvs -> (let _26_1789 = (stash uvonly e fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_exp' e uvonly (fun fvs -> (let _26_1796 = (stash uvonly e fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_comp' = (fun c uvonly k -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(vs_typ t uvonly k)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
if uvonly then begin
(vs_typ ct.FStar_Absyn_Syntax.result_typ uvonly k)
end else begin
(vs_typ ct.FStar_Absyn_Syntax.result_typ uvonly (fun vs1 -> (vs_args ct.FStar_Absyn_Syntax.effect_args uvonly (fun vs2 -> (let _93_1215 = (union_fvs_uvs vs1 vs2)
in (k _93_1215))))))
end
end))
and vs_comp = (fun c uvonly cont -> (match ((let _93_1218 = (FStar_ST.read c.FStar_Absyn_Syntax.fvs)
in (let _93_1217 = (FStar_ST.read c.FStar_Absyn_Syntax.uvs)
in (_93_1218, _93_1217)))) with
| (Some (_26_1818), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_comp' c uvonly (fun fvs -> (let _26_1826 = (stash uvonly c fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_comp' c uvonly (fun fvs -> (let _26_1833 = (stash uvonly c fvs)
in (cont fvs))))
end
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
(vs_either hd uvonly (fun ft1 -> (vs_either_l tl uvonly (fun ft2 -> (let _93_1225 = (union_fvs_uvs ft1 ft2)
in (cont _93_1225))))))
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
(let _93_1241 = (freevars_typ t)
in (FStar_All.pipe_left (union_fvs out) _93_1241))
end
| FStar_Util.Inr (e) -> begin
(let _93_1242 = (freevars_exp e)
in (FStar_All.pipe_left (union_fvs out) _93_1242))
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

let rec update_uvars = (fun s uvs -> (let out = (let _93_1316 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_k)
in (FStar_All.pipe_right _93_1316 (FStar_List.fold_left (fun out u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(let _93_1314 = (uvars_in_kind k)
in (union_uvs _93_1314 out))
end
| _26_1911 -> begin
(let _26_1912 = out
in (let _93_1315 = (FStar_Util.set_add u out.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _93_1315; FStar_Absyn_Syntax.uvars_t = _26_1912.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _26_1912.FStar_Absyn_Syntax.uvars_e}))
end)) FStar_Absyn_Syntax.no_uvs)))
in (let out = (let _93_1321 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _93_1321 (FStar_List.fold_left (fun out _26_1918 -> (match (_26_1918) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (t) -> begin
(let _93_1319 = (uvars_in_typ t)
in (union_uvs _93_1319 out))
end
| _26_1922 -> begin
(let _26_1923 = out
in (let _93_1320 = (FStar_Util.set_add (u, t) out.FStar_Absyn_Syntax.uvars_t)
in {FStar_Absyn_Syntax.uvars_k = _26_1923.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _93_1320; FStar_Absyn_Syntax.uvars_e = _26_1923.FStar_Absyn_Syntax.uvars_e}))
end)
end)) out)))
in (let out = (let _93_1326 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_e)
in (FStar_All.pipe_right _93_1326 (FStar_List.fold_left (fun out _26_1929 -> (match (_26_1929) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(let _93_1324 = (uvars_in_exp e)
in (union_uvs _93_1324 out))
end
| _26_1933 -> begin
(let _26_1934 = out
in (let _93_1325 = (FStar_Util.set_add (u, t) out.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _26_1934.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _26_1934.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _93_1325}))
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
and uvars_in_kind = (fun k -> (let _93_1329 = (vs_kind k true (fun _26_1951 -> (match (_26_1951) with
| (_26_1949, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumKind (k))) _93_1329)))
and uvars_in_typ = (fun t -> (let _93_1332 = (vs_typ t true (fun _26_1956 -> (match (_26_1956) with
| (_26_1954, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumType (t))) _93_1332)))
and uvars_in_exp = (fun e -> (let _93_1335 = (vs_exp e true (fun _26_1961 -> (match (_26_1961) with
| (_26_1959, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumExp (e))) _93_1335)))
and uvars_in_comp = (fun c -> (let _93_1338 = (vs_comp c true (fun _26_1966 -> (match (_26_1966) with
| (_26_1964, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumComp (c))) _93_1338)))

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
(let _93_1359 = (FStar_Absyn_Syntax.mk_Total t)
in (tps, _93_1359))
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

let mk_tuple_lid = (fun n r -> (let t = (let _93_1372 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Tuple%s" _93_1372))
in (let _93_1373 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _93_1373 r))))

let mk_tuple_data_lid = (fun n r -> (let t = (let _93_1378 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkTuple%s" _93_1378))
in (let _93_1379 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _93_1379 r))))

let is_tuple_data_lid = (fun f n -> (let _93_1384 = (mk_tuple_data_lid n FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.lid_equals f _93_1384)))

let is_dtuple_constructor = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str "Prims.DTuple")
end
| _26_2054 -> begin
false
end))

let mk_dtuple_lid = (fun n r -> (let t = (let _93_1391 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "DTuple%s" _93_1391))
in (let _93_1392 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _93_1392 r))))

let mk_dtuple_data_lid = (fun n r -> (let t = (let _93_1397 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkDTuple%s" _93_1397))
in (let _93_1398 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _93_1398 r))))

let is_lid_equality = (fun x -> ((((FStar_Absyn_Syntax.lid_equals x FStar_Absyn_Const.eq_lid) || (FStar_Absyn_Syntax.lid_equals x FStar_Absyn_Const.eq2_lid)) || (FStar_Absyn_Syntax.lid_equals x FStar_Absyn_Const.eqA_lid)) || (FStar_Absyn_Syntax.lid_equals x FStar_Absyn_Const.eqT_lid)))

let is_forall = (fun lid -> ((FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.forall_lid) || (FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.allTyp_lid)))

let is_exists = (fun lid -> ((FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.exists_lid) || (FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.exTyp_lid)))

let is_qlid = (fun lid -> ((is_forall lid) || (is_exists lid)))

let is_equality = (fun x -> (is_lid_equality x.FStar_Absyn_Syntax.v))

let lid_is_connective = (let lst = (FStar_Absyn_Const.and_lid)::(FStar_Absyn_Const.or_lid)::(FStar_Absyn_Const.not_lid)::(FStar_Absyn_Const.iff_lid)::(FStar_Absyn_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Absyn_Syntax.lid_equals lid) lst)))

let is_constructor = (fun t lid -> (match ((let _93_1414 = (pre_typ t)
in _93_1414.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
(FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v lid)
end
| _26_2073 -> begin
false
end))

let rec is_constructed_typ = (fun t lid -> (match ((let _93_1419 = (pre_typ t)
in _93_1419.FStar_Absyn_Syntax.n)) with
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
(let _93_1428 = (FStar_Absyn_Syntax.text_of_lid fn1)
in (let _93_1427 = (FStar_Absyn_Syntax.text_of_lid fn2)
in (FStar_String.compare _93_1428 _93_1427)))
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

let b2t_v = (let _93_1432 = (let _93_1431 = (let _93_1430 = (let _93_1429 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder t_bool)
in (_93_1429)::[])
in (_93_1430, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _93_1431 FStar_Absyn_Syntax.dummyRange))
in (ftv FStar_Absyn_Const.b2t_lid _93_1432))

let mk_conj_opt = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _93_1443 = (let _93_1442 = (let _93_1440 = (let _93_1439 = (FStar_Absyn_Syntax.targ phi1)
in (let _93_1438 = (let _93_1437 = (FStar_Absyn_Syntax.targ phi2)
in (_93_1437)::[])
in (_93_1439)::_93_1438))
in (tand, _93_1440))
in (let _93_1441 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _93_1442 None _93_1441)))
in Some (_93_1443))
end))

let mk_binop = (fun op_t phi1 phi2 -> (let _93_1455 = (let _93_1453 = (let _93_1452 = (FStar_Absyn_Syntax.targ phi1)
in (let _93_1451 = (let _93_1450 = (FStar_Absyn_Syntax.targ phi2)
in (_93_1450)::[])
in (_93_1452)::_93_1451))
in (op_t, _93_1453))
in (let _93_1454 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _93_1455 None _93_1454))))

let mk_neg = (fun phi -> (let _93_1461 = (let _93_1460 = (ftv FStar_Absyn_Const.not_lid kt_kt)
in (let _93_1459 = (let _93_1458 = (FStar_Absyn_Syntax.targ phi)
in (_93_1458)::[])
in (_93_1460, _93_1459)))
in (FStar_Absyn_Syntax.mk_Typ_app _93_1461 None phi.FStar_Absyn_Syntax.pos)))

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

let mk_imp = (fun phi1 phi2 -> (match ((let _93_1478 = (compress_typ phi1)
in _93_1478.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid) -> begin
t_true
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
phi2
end
| _26_2145 -> begin
(match ((let _93_1479 = (compress_typ phi2)
in _93_1479.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when ((FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) || (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid)) -> begin
phi2
end
| _26_2149 -> begin
(mk_binop timp phi1 phi2)
end)
end))

let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))

let b2t = (fun e -> (let _93_1488 = (let _93_1487 = (let _93_1486 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg e)
in (_93_1486)::[])
in (b2t_v, _93_1487))
in (FStar_Absyn_Syntax.mk_Typ_app _93_1488 None e.FStar_Absyn_Syntax.pos)))

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

let eq_k = (let a = (let _93_1491 = (new_bvd None)
in (bvd_to_bvar_s _93_1491 FStar_Absyn_Syntax.ktype))
in (let atyp = (btvar_to_typ a)
in (let b = (let _93_1492 = (new_bvd None)
in (bvd_to_bvar_s _93_1492 FStar_Absyn_Syntax.ktype))
in (let btyp = (btvar_to_typ b)
in (let _93_1499 = (let _93_1498 = (let _93_1497 = (let _93_1496 = (let _93_1495 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (let _93_1494 = (let _93_1493 = (FStar_Absyn_Syntax.null_v_binder btyp)
in (_93_1493)::[])
in (_93_1495)::_93_1494))
in ((FStar_Util.Inl (b), Some (FStar_Absyn_Syntax.Implicit)))::_93_1496)
in ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit)))::_93_1497)
in (_93_1498, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _93_1499 FStar_Absyn_Syntax.dummyRange))))))

let teq = (ftv FStar_Absyn_Const.eq2_lid eq_k)

let mk_eq = (fun t1 t2 e1 e2 -> (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((_, FStar_Absyn_Syntax.Typ_unknown)) -> begin
(FStar_All.failwith "DIE! mk_eq with tun")
end
| _26_2212 -> begin
(let _93_1517 = (let _93_1515 = (let _93_1514 = (FStar_Absyn_Syntax.itarg t1)
in (let _93_1513 = (let _93_1512 = (FStar_Absyn_Syntax.itarg t2)
in (let _93_1511 = (let _93_1510 = (FStar_Absyn_Syntax.varg e1)
in (let _93_1509 = (let _93_1508 = (FStar_Absyn_Syntax.varg e2)
in (_93_1508)::[])
in (_93_1510)::_93_1509))
in (_93_1512)::_93_1511))
in (_93_1514)::_93_1513))
in (teq, _93_1515))
in (let _93_1516 = (FStar_Range.union_ranges e1.FStar_Absyn_Syntax.pos e2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _93_1517 None _93_1516)))
end))

let eq_typ = (ftv FStar_Absyn_Const.eqT_lid FStar_Absyn_Syntax.kun)

let mk_eq_typ = (fun t1 t2 -> (let _93_1527 = (let _93_1525 = (let _93_1524 = (FStar_Absyn_Syntax.targ t1)
in (let _93_1523 = (let _93_1522 = (FStar_Absyn_Syntax.targ t2)
in (_93_1522)::[])
in (_93_1524)::_93_1523))
in (eq_typ, _93_1525))
in (let _93_1526 = (FStar_Range.union_ranges t1.FStar_Absyn_Syntax.pos t2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _93_1527 None _93_1526))))

let lex_t = (ftv FStar_Absyn_Const.lex_t_lid FStar_Absyn_Syntax.ktype)

let lex_top = (let lexnil = (withinfo FStar_Absyn_Const.lextop_lid lex_t FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.mk_Exp_fvar (lexnil, Some (FStar_Absyn_Syntax.Data_ctor)) None FStar_Absyn_Syntax.dummyRange))

let lex_pair = (let a = (gen_bvar FStar_Absyn_Syntax.ktype)
in (let lexcons = (let _93_1537 = (let _93_1536 = (let _93_1535 = (let _93_1533 = (FStar_Absyn_Syntax.t_binder a)
in (let _93_1532 = (let _93_1531 = (let _93_1528 = (btvar_to_typ a)
in (FStar_Absyn_Syntax.null_v_binder _93_1528))
in (let _93_1530 = (let _93_1529 = (FStar_Absyn_Syntax.null_v_binder lex_t)
in (_93_1529)::[])
in (_93_1531)::_93_1530))
in (_93_1533)::_93_1532))
in (let _93_1534 = (FStar_Absyn_Syntax.mk_Total lex_t)
in (_93_1535, _93_1534)))
in (FStar_Absyn_Syntax.mk_Typ_fun _93_1536 None FStar_Absyn_Syntax.dummyRange))
in (withinfo FStar_Absyn_Const.lexcons_lid _93_1537 FStar_Absyn_Syntax.dummyRange))
in (FStar_Absyn_Syntax.mk_Exp_fvar (lexcons, Some (FStar_Absyn_Syntax.Data_ctor)) None FStar_Absyn_Syntax.dummyRange)))

let forall_kind = (let a = (let _93_1538 = (new_bvd None)
in (bvd_to_bvar_s _93_1538 FStar_Absyn_Syntax.ktype))
in (let atyp = (btvar_to_typ a)
in (let _93_1546 = (let _93_1545 = (let _93_1544 = (let _93_1543 = (let _93_1542 = (let _93_1541 = (let _93_1540 = (let _93_1539 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (_93_1539)::[])
in (_93_1540, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _93_1541 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _93_1542))
in (_93_1543)::[])
in ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit)))::_93_1544)
in (_93_1545, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _93_1546 FStar_Absyn_Syntax.dummyRange))))

let tforall = (ftv FStar_Absyn_Const.forall_lid forall_kind)

let allT_k = (fun k -> (let _93_1555 = (let _93_1554 = (let _93_1553 = (let _93_1552 = (let _93_1551 = (let _93_1550 = (let _93_1549 = (FStar_Absyn_Syntax.null_t_binder k)
in (_93_1549)::[])
in (_93_1550, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _93_1551 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _93_1552))
in (_93_1553)::[])
in (_93_1554, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _93_1555 FStar_Absyn_Syntax.dummyRange)))

let eqT_k = (fun k -> (let _93_1562 = (let _93_1561 = (let _93_1560 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder k)
in (let _93_1559 = (let _93_1558 = (FStar_Absyn_Syntax.null_t_binder k)
in (_93_1558)::[])
in (_93_1560)::_93_1559))
in (_93_1561, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _93_1562 FStar_Absyn_Syntax.dummyRange)))

let tforall_typ = (fun k -> (let _93_1565 = (allT_k k)
in (ftv FStar_Absyn_Const.allTyp_lid _93_1565)))

let mk_forallT = (fun a b -> (let _93_1577 = (let _93_1576 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _93_1575 = (let _93_1574 = (let _93_1573 = (let _93_1572 = (let _93_1571 = (let _93_1570 = (FStar_Absyn_Syntax.t_binder a)
in (_93_1570)::[])
in (_93_1571, b))
in (FStar_Absyn_Syntax.mk_Typ_lam _93_1572 None b.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _93_1573))
in (_93_1574)::[])
in (_93_1576, _93_1575)))
in (FStar_Absyn_Syntax.mk_Typ_app _93_1577 None b.FStar_Absyn_Syntax.pos)))

let mk_forall = (fun x body -> (let r = FStar_Absyn_Syntax.dummyRange
in (let _93_1588 = (let _93_1587 = (let _93_1586 = (let _93_1585 = (let _93_1584 = (let _93_1583 = (let _93_1582 = (FStar_Absyn_Syntax.v_binder x)
in (_93_1582)::[])
in (_93_1583, body))
in (FStar_Absyn_Syntax.mk_Typ_lam _93_1584 None r))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _93_1585))
in (_93_1586)::[])
in (tforall, _93_1587))
in (FStar_Absyn_Syntax.mk_Typ_app _93_1588 None r))))

let rec close_forall = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
f
end else begin
(let body = (FStar_Absyn_Syntax.mk_Typ_lam ((b)::[], f) None f.FStar_Absyn_Syntax.pos)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _93_1598 = (let _93_1597 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _93_1596 = (let _93_1595 = (FStar_Absyn_Syntax.targ body)
in (_93_1595)::[])
in (_93_1597, _93_1596)))
in (FStar_Absyn_Syntax.mk_Typ_app _93_1598 None f.FStar_Absyn_Syntax.pos))
end
| FStar_Util.Inr (x) -> begin
(let _93_1602 = (let _93_1601 = (let _93_1600 = (let _93_1599 = (FStar_Absyn_Syntax.targ body)
in (_93_1599)::[])
in ((FStar_Util.Inl (x.FStar_Absyn_Syntax.sort), Some (FStar_Absyn_Syntax.Implicit)))::_93_1600)
in (tforall, _93_1601))
in (FStar_Absyn_Syntax.mk_Typ_app _93_1602 None f.FStar_Absyn_Syntax.pos))
end))
end) bs f))

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
FStar_Absyn_Syntax.args Prims.list

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
if (((is_constructor t lid) && ((FStar_List.length args) = (FStar_List.length arity))) && (FStar_List.forall2 (fun arg flag -> (match (arg) with
| (FStar_Util.Inl (_26_2300), _26_2303) -> begin
(flag = type_sort)
end
| (FStar_Util.Inr (_26_2306), _26_2309) -> begin
(flag = term_sort)
end)) args arity)) then begin
Some (BaseConn ((lid, args)))
end else begin
None
end
end))
end))
in (FStar_Util.find_map connectives (aux f))))))))
end)))
in (let patterns = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, pats)) -> begin
(let _93_1666 = (compress_typ t)
in (pats, _93_1666))
end
| _26_2320 -> begin
(let _93_1667 = (compress_typ t)
in ([], _93_1667))
end)))
in (let destruct_q_conn = (fun t -> (let is_q = (fun fa l -> if fa then begin
(is_forall l)
end else begin
(is_exists l)
end)
in (let flat = (fun t -> (let _26_2330 = (head_and_args t)
in (match (_26_2330) with
| (t, args) -> begin
(let _93_1681 = (FStar_All.pipe_right args (FStar_List.map (fun _26_26 -> (match (_26_26) with
| (FStar_Util.Inl (t), imp) -> begin
(let _93_1678 = (let _93_1677 = (compress_typ t)
in FStar_Util.Inl (_93_1677))
in (_93_1678, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _93_1680 = (let _93_1679 = (compress_exp e)
in FStar_Util.Inr (_93_1679))
in (_93_1680, imp))
end))))
in (t, _93_1681))
end)))
in (let rec aux = (fun qopt out t -> (match ((let _93_1688 = (flat t)
in (qopt, _93_1688))) with
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




