
open Prims
let handle_err = (fun warning ret e -> (match (e) with
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(let _29_34 = (let _120_8 = (let _120_7 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s : %s\n%s\n" _120_7 (if warning then begin
"Warning"
end else begin
"Error"
end) msg))
in (FStar_Util.print_string _120_8))
in ())
end
| FStar_Util.NYI (s) -> begin
(let _29_38 = (let _120_9 = (FStar_Util.format1 "Feature not yet implemented: %s" s)
in (FStar_Util.print_string _120_9))
in ())
end
| FStar_Absyn_Syntax.Err (s) -> begin
(let _120_10 = (FStar_Util.format1 "Error: %s" s)
in (FStar_Util.print_string _120_10))
end
| _29_43 -> begin
(Prims.raise e)
end))

let handleable = (fun _29_1 -> (match (_29_1) with
| (FStar_Absyn_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Absyn_Syntax.Err (_)) -> begin
true
end
| _29_55 -> begin
false
end))

type gensym_t =
{gensym : Prims.unit  ->  Prims.string; reset : Prims.unit  ->  Prims.unit}

let is_Mkgensym_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkgensym_t"))))

let gs = (let ctr = (FStar_Util.mk_ref 0)
in (let n_resets = (FStar_Util.mk_ref 0)
in {gensym = (fun _29_61 -> (match (()) with
| () -> begin
(let _120_38 = (let _120_35 = (let _120_34 = (let _120_33 = (FStar_ST.read n_resets)
in (FStar_Util.string_of_int _120_33))
in (Prims.strcat "_" _120_34))
in (Prims.strcat _120_35 "_"))
in (let _120_37 = (let _120_36 = (let _29_62 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
in (FStar_Util.string_of_int _120_36))
in (Prims.strcat _120_38 _120_37)))
end)); reset = (fun _29_64 -> (match (()) with
| () -> begin
(let _29_65 = (FStar_ST.op_Colon_Equals ctr 0)
in (FStar_Util.incr n_resets))
end))}))

let gensym = (fun _29_67 -> (match (()) with
| () -> begin
(gs.gensym ())
end))

let reset_gensym = (fun _29_68 -> (match (()) with
| () -> begin
(gs.reset ())
end))

let rec gensyms = (fun x -> (match (x) with
| 0 -> begin
[]
end
| n -> begin
(let _120_47 = (gensym ())
in (let _120_46 = (gensyms (n - 1))
in (_120_47)::_120_46))
end))

let genident = (fun r -> (let sym = (gensym ())
in (match (r) with
| None -> begin
(FStar_Ident.mk_ident (sym, FStar_Absyn_Syntax.dummyRange))
end
| Some (r) -> begin
(FStar_Ident.mk_ident (sym, r))
end)))

let bvd_eq = (fun bvd1 bvd2 -> (bvd1.FStar_Absyn_Syntax.realname.FStar_Ident.idText = bvd2.FStar_Absyn_Syntax.realname.FStar_Ident.idText))

let range_of_bvd = (fun x -> x.FStar_Absyn_Syntax.ppname.FStar_Ident.idRange)

let mkbvd = (fun _29_82 -> (match (_29_82) with
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
(FStar_Ident.lid_equals l m)
end
| _29_109 -> begin
false
end))

let fvar_eq = (fun fv1 fv2 -> (FStar_Ident.lid_equals fv1.FStar_Absyn_Syntax.v fv2.FStar_Absyn_Syntax.v))

let bvd_to_bvar_s = (fun bvd sort -> {FStar_Absyn_Syntax.v = bvd; FStar_Absyn_Syntax.sort = sort; FStar_Absyn_Syntax.p = bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idRange})

let bvar_to_bvd = (fun bv -> bv.FStar_Absyn_Syntax.v)

let btvar_to_typ = (fun bv -> (FStar_Absyn_Syntax.mk_Typ_btvar bv None bv.FStar_Absyn_Syntax.p))

let bvd_to_typ = (fun bvd k -> (btvar_to_typ (bvd_to_bvar_s bvd k)))

let bvar_to_exp = (fun bv -> (FStar_Absyn_Syntax.mk_Exp_bvar bv None bv.FStar_Absyn_Syntax.p))

let bvd_to_exp = (fun bvd t -> (bvar_to_exp (bvd_to_bvar_s bvd t)))

let new_bvd = (fun ropt -> (let f = (fun ropt -> (let id = (genident ropt)
in (mkbvd (id, id))))
in (f ropt)))

let freshen_bvd = (fun bvd' -> (let _120_88 = (let _120_87 = (genident (Some ((range_of_bvd bvd'))))
in (bvd'.FStar_Absyn_Syntax.ppname, _120_87))
in (mkbvd _120_88)))

let freshen_bvar = (fun b -> (let _120_90 = (freshen_bvd b.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _120_90 b.FStar_Absyn_Syntax.sort)))

let gen_bvar = (fun sort -> (let bvd = (new_bvd None)
in (bvd_to_bvar_s bvd sort)))

let gen_bvar_p = (fun r sort -> (let bvd = (new_bvd (Some (r)))
in (bvd_to_bvar_s bvd sort)))

let bvdef_of_str = (fun s -> (let f = (fun s -> (let id = (FStar_Ident.id_of_text s)
in (mkbvd (id, id))))
in (f s)))

let set_bvd_range = (fun bvd r -> {FStar_Absyn_Syntax.ppname = (FStar_Ident.mk_ident (bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText, r)); FStar_Absyn_Syntax.realname = (FStar_Ident.mk_ident (bvd.FStar_Absyn_Syntax.realname.FStar_Ident.idText, r))})

let set_lid_range = (fun l r -> (let ids = (FStar_All.pipe_right (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[])) (FStar_List.map (fun i -> (FStar_Ident.mk_ident (i.FStar_Ident.idText, r)))))
in (FStar_Ident.lid_of_ids ids)))

let fv = (fun l -> (withinfo l FStar_Absyn_Syntax.tun (FStar_Ident.range_of_lid l)))

let fvvar_of_lid = (fun l t -> (withinfo l t (FStar_Ident.range_of_lid l)))

let fvar = (fun dc l r -> (let _120_115 = (let _120_114 = (let _120_113 = (set_lid_range l r)
in (fv _120_113))
in (_120_114, dc))
in (FStar_Absyn_Syntax.mk_Exp_fvar _120_115 None r)))

let ftv = (fun l k -> (FStar_Absyn_Syntax.mk_Typ_const (withinfo l k (FStar_Ident.range_of_lid l)) None (FStar_Ident.range_of_lid l)))

let order_bvd = (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (_29_155), FStar_Util.Inr (_29_158)) -> begin
(- (1))
end
| (FStar_Util.Inr (_29_162), FStar_Util.Inl (_29_165)) -> begin
1
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText)
end))

let arg_of_non_null_binder = (fun _29_180 -> (match (_29_180) with
| (b, imp) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let _120_124 = (let _120_123 = (btvar_to_typ a)
in FStar_Util.Inl (_120_123))
in (_120_124, imp))
end
| FStar_Util.Inr (x) -> begin
(let _120_126 = (let _120_125 = (bvar_to_exp x)
in FStar_Util.Inr (_120_125))
in (_120_126, imp))
end)
end))

let args_of_non_null_binders = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
[]
end else begin
(let _120_130 = (arg_of_non_null_binder b)
in (_120_130)::[])
end))))

let args_of_binders = (fun binders -> (let _120_140 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(let b = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _120_135 = (let _120_134 = (gen_bvar a.FStar_Absyn_Syntax.sort)
in FStar_Util.Inl (_120_134))
in (_120_135, (Prims.snd b)))
end
| FStar_Util.Inr (x) -> begin
(let _120_137 = (let _120_136 = (gen_bvar x.FStar_Absyn_Syntax.sort)
in FStar_Util.Inr (_120_136))
in (_120_137, (Prims.snd b)))
end)
in (let _120_138 = (arg_of_non_null_binder b)
in (b, _120_138)))
end else begin
(let _120_139 = (arg_of_non_null_binder b)
in (b, _120_139))
end)))
in (FStar_All.pipe_right _120_140 FStar_List.unzip)))

let name_binders = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(let b = (let _120_146 = (let _120_145 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _120_145))
in (FStar_Ident.id_of_text _120_146))
in (let b = (bvd_to_bvar_s (mkbvd (b, b)) a.FStar_Absyn_Syntax.sort)
in (FStar_Util.Inl (b), imp)))
end
| (FStar_Util.Inr (y), imp) -> begin
(let x = (let _120_148 = (let _120_147 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _120_147))
in (FStar_Ident.id_of_text _120_148))
in (let x = (bvd_to_bvar_s (mkbvd (x, x)) y.FStar_Absyn_Syntax.sort)
in (FStar_Util.Inr (x), imp)))
end)
end else begin
b
end))))

let name_function_binders = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, comp) -> begin
(let _120_152 = (let _120_151 = (name_binders binders)
in (_120_151, comp))
in (FStar_Absyn_Syntax.mk_Typ_fun _120_152 None t.FStar_Absyn_Syntax.pos))
end
| _29_215 -> begin
t
end))

let null_binders_of_tks = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _29_2 -> (match (_29_2) with
| (FStar_Util.Inl (k), imp) -> begin
(let _120_156 = (FStar_All.pipe_left Prims.fst (FStar_Absyn_Syntax.null_t_binder k))
in (_120_156, imp))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _120_157 = (FStar_All.pipe_left Prims.fst (FStar_Absyn_Syntax.null_v_binder t))
in (_120_157, imp))
end)))))

let binders_of_tks = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _29_3 -> (match (_29_3) with
| (FStar_Util.Inl (k), imp) -> begin
(let _120_162 = (let _120_161 = (gen_bvar_p k.FStar_Absyn_Syntax.pos k)
in FStar_Util.Inl (_120_161))
in (_120_162, imp))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _120_164 = (let _120_163 = (gen_bvar_p t.FStar_Absyn_Syntax.pos t)
in FStar_Util.Inr (_120_163))
in (_120_164, imp))
end)))))

let binders_of_freevars = (fun fvs -> (let _120_170 = (let _120_167 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.ftvs)
in (FStar_All.pipe_right _120_167 (FStar_List.map FStar_Absyn_Syntax.t_binder)))
in (let _120_169 = (let _120_168 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_All.pipe_right _120_168 (FStar_List.map FStar_Absyn_Syntax.v_binder)))
in (FStar_List.append _120_170 _120_169))))

let subst_to_string = (fun s -> (let _120_173 = (FStar_All.pipe_right s (FStar_List.map (fun _29_4 -> (match (_29_4) with
| FStar_Util.Inl (b, _29_241) -> begin
b.FStar_Absyn_Syntax.realname.FStar_Ident.idText
end
| FStar_Util.Inr (x, _29_246) -> begin
x.FStar_Absyn_Syntax.realname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _120_173 (FStar_String.concat ", "))))

let subst_tvar = (fun s a -> (FStar_Util.find_map s (fun _29_5 -> (match (_29_5) with
| FStar_Util.Inl (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _29_257 -> begin
None
end))))

let subst_xvar = (fun s a -> (FStar_Util.find_map s (fun _29_6 -> (match (_29_6) with
| FStar_Util.Inr (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _29_266 -> begin
None
end))))

let rec subst_typ' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_typ t)
end
| _29_273 -> begin
(let t0 = (FStar_Absyn_Visit.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s'), m) -> begin
(let _120_198 = (let _120_197 = (compose_subst s' s)
in (let _120_196 = (FStar_Util.mk_ref None)
in (t', _120_197, _120_196)))
in (FStar_Absyn_Syntax.mk_Typ_delayed _120_198 None t.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(let t = (mk_t ())
in (let _29_288 = (FStar_ST.op_Colon_Equals m (Some (t)))
in (subst_typ' s t)))
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let rec aux = (fun s' -> (match (s') with
| s0::rest -> begin
(match ((subst_tvar s0 a)) with
| Some (t) -> begin
(subst_typ' rest t)
end
| _29_300 -> begin
(aux rest)
end)
end
| _29_302 -> begin
t0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
t0
end
| _29_311 -> begin
(let _120_203 = (let _120_202 = (FStar_Util.mk_ref None)
in (t0, s, _120_202))
in (FStar_Absyn_Syntax.mk_Typ_delayed _120_203 None t.FStar_Absyn_Syntax.pos))
end))
end))
and subst_exp' = (fun s e -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_exp e)
end
| _29_318 -> begin
(let e0 = (FStar_Absyn_Visit.compress_exp e)
in (match (e0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e, s', m) -> begin
(let _120_208 = (let _120_207 = (compose_subst s' s)
in (let _120_206 = (FStar_Util.mk_ref None)
in (e, _120_207, _120_206)))
in (FStar_Absyn_Syntax.mk_Exp_delayed _120_208 None e.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let rec aux = (fun s -> (match (s) with
| s0::rest -> begin
(match ((subst_xvar s0 x)) with
| Some (e) -> begin
(subst_exp' rest e)
end
| _29_335 -> begin
(aux rest)
end)
end
| _29_337 -> begin
e0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
e0
end
| _29_345 -> begin
(let _120_212 = (let _120_211 = (FStar_Util.mk_ref None)
in (e0, s, _120_211))
in (FStar_Absyn_Syntax.mk_Exp_delayed _120_212 None e0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_kind' = (fun s k -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_kind k)
end
| _29_352 -> begin
(let k0 = (FStar_Absyn_Visit.compress_kind k)
in (match (k0.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
k0
end
| FStar_Absyn_Syntax.Kind_delayed (k, s', m) -> begin
(let _120_217 = (let _120_216 = (compose_subst s' s)
in (let _120_215 = (FStar_Util.mk_ref None)
in (k, _120_216, _120_215)))
in (FStar_Absyn_Syntax.mk_Kind_delayed _120_217 k0.FStar_Absyn_Syntax.pos))
end
| _29_363 -> begin
(let _120_219 = (let _120_218 = (FStar_Util.mk_ref None)
in (k0, s, _120_218))
in (FStar_Absyn_Syntax.mk_Kind_delayed _120_219 k0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_flags' = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _29_7 -> (match (_29_7) with
| FStar_Absyn_Syntax.DECREASES (a) -> begin
(let _120_223 = (subst_exp' s a)
in FStar_Absyn_Syntax.DECREASES (_120_223))
end
| f -> begin
f
end)))))
and subst_comp_typ' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _29_376 -> begin
(let _29_377 = t
in (let _120_233 = (subst_typ' s t.FStar_Absyn_Syntax.result_typ)
in (let _120_232 = (FStar_List.map (fun _29_8 -> (match (_29_8) with
| (FStar_Util.Inl (t), imp) -> begin
(let _120_228 = (let _120_227 = (subst_typ' s t)
in FStar_Util.Inl (_120_227))
in (_120_228, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _120_230 = (let _120_229 = (subst_exp' s e)
in FStar_Util.Inr (_120_229))
in (_120_230, imp))
end)) t.FStar_Absyn_Syntax.effect_args)
in (let _120_231 = (subst_flags' s t.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _29_377.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _120_233; FStar_Absyn_Syntax.effect_args = _120_232; FStar_Absyn_Syntax.flags = _120_231}))))
end))
and subst_comp' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _29_394 -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _120_236 = (subst_typ' s t)
in (FStar_Absyn_Syntax.mk_Total _120_236))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _120_237 = (subst_comp_typ' s ct)
in (FStar_Absyn_Syntax.mk_Comp _120_237))
end)
end))
and compose_subst = (fun s1 s2 -> (FStar_List.append s1 s2))

let mk_subst = (fun s -> (s)::[])

let subst_kind = (fun s t -> (subst_kind' (mk_subst s) t))

let subst_typ = (fun s t -> (subst_typ' (mk_subst s) t))

let subst_exp = (fun s t -> (subst_exp' (mk_subst s) t))

let subst_flags = (fun s t -> (subst_flags' (mk_subst s) t))

let subst_comp = (fun s t -> (subst_comp' (mk_subst s) t))

let subst_binder = (fun s _29_9 -> (match (_29_9) with
| (FStar_Util.Inl (a), imp) -> begin
(let _120_265 = (let _120_264 = (let _29_418 = a
in (let _120_263 = (subst_kind s a.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _29_418.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _120_263; FStar_Absyn_Syntax.p = _29_418.FStar_Absyn_Syntax.p}))
in FStar_Util.Inl (_120_264))
in (_120_265, imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _120_268 = (let _120_267 = (let _29_424 = x
in (let _120_266 = (subst_typ s x.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _29_424.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _120_266; FStar_Absyn_Syntax.p = _29_424.FStar_Absyn_Syntax.p}))
in FStar_Util.Inr (_120_267))
in (_120_268, imp))
end))

let subst_arg = (fun s _29_10 -> (match (_29_10) with
| (FStar_Util.Inl (t), imp) -> begin
(let _120_272 = (let _120_271 = (subst_typ s t)
in FStar_Util.Inl (_120_271))
in (_120_272, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _120_274 = (let _120_273 = (subst_exp s e)
in FStar_Util.Inr (_120_273))
in (_120_274, imp))
end))

let subst_binders = (fun s bs -> (match (s) with
| [] -> begin
bs
end
| _29_440 -> begin
(FStar_List.map (subst_binder s) bs)
end))

let subst_args = (fun s args -> (match (s) with
| [] -> begin
args
end
| _29_445 -> begin
(FStar_List.map (subst_arg s) args)
end))

let subst_formal = (fun f a -> (match ((f, a)) with
| ((FStar_Util.Inl (a), _29_451), (FStar_Util.Inl (t), _29_456)) -> begin
FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t))
end
| ((FStar_Util.Inr (x), _29_462), (FStar_Util.Inr (v), _29_467)) -> begin
FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v))
end
| _29_471 -> begin
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
(let _120_289 = (let _120_288 = (let _120_287 = (btvar_to_typ a)
in (b.FStar_Absyn_Syntax.v, _120_287))
in FStar_Util.Inl (_120_288))
in (_120_289)::[])
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (bvar_eq x y) then begin
[]
end else begin
(let _120_292 = (let _120_291 = (let _120_290 = (bvar_to_exp x)
in (y.FStar_Absyn_Syntax.v, _120_290))
in FStar_Util.Inr (_120_291))
in (_120_292)::[])
end
end
| _29_485 -> begin
[]
end)
end)

let mk_subst_binder = (fun bs1 bs2 -> (let rec aux = (fun out bs1 bs2 -> (match ((bs1, bs2)) with
| ([], []) -> begin
Some (out)
end
| (b1::bs1, b2::bs2) -> begin
(let _120_304 = (let _120_303 = (mk_subst_one_binder b1 b2)
in (FStar_List.append _120_303 out))
in (aux _120_304 bs1 bs2))
end
| _29_503 -> begin
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

let map_knd = (fun s vk mt me descend binders k -> (let _120_325 = (subst_kind' s k)
in (_120_325, descend)))

let map_typ = (fun s mk vt me descend binders t -> (let _120_333 = (subst_typ' s t)
in (_120_333, descend)))

let map_exp = (fun s mk me ve descend binders e -> (let _120_341 = (subst_exp' s e)
in (_120_341, descend)))

let map_flags = (fun s map_exp descend binders flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _29_11 -> (match (_29_11) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _120_358 = (let _120_357 = (map_exp descend binders e)
in (FStar_All.pipe_right _120_357 Prims.fst))
in FStar_Absyn_Syntax.DECREASES (_120_358))
end
| f -> begin
f
end)))))

let map_comp = (fun s mk map_typ map_exp descend binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _29_552 = (map_typ descend binders t)
in (match (_29_552) with
| (t, descend) -> begin
(let _120_381 = (FStar_Absyn_Syntax.mk_Total t)
in (_120_381, descend))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _29_557 = (map_typ descend binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_29_557) with
| (t, descend) -> begin
(let _29_560 = (FStar_Absyn_Visit.map_args map_typ map_exp descend binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_29_560) with
| (args, descend) -> begin
(let _120_384 = (let _120_383 = (let _29_561 = ct
in (let _120_382 = (map_flags s map_exp descend binders ct.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _29_561.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _120_382}))
in (FStar_Absyn_Syntax.mk_Comp _120_383))
in (_120_384, descend))
end))
end))
end))

let visit_knd = (fun s vk mt me ctrl binders k -> (let k = (FStar_Absyn_Visit.compress_kind k)
in if ctrl.descend then begin
(let _29_574 = (vk null_ctrl binders k)
in (match (_29_574) with
| (k, _29_573) -> begin
(k, ctrl)
end))
end else begin
(map_knd s vk mt me null_ctrl binders k)
end))

let rec compress_kind = (fun k -> (let k = (FStar_Absyn_Visit.compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (k', s, m) -> begin
(let k' = (let _120_430 = (FStar_Absyn_Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] k')
in (FStar_All.pipe_left Prims.fst _120_430))
in (let k' = (compress_kind k')
in (let _29_584 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k')))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, actuals) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (formals, k') -> begin
(let _120_432 = (let _120_431 = (subst_of_list formals actuals)
in (subst_kind _120_431 k'))
in (compress_kind _120_432))
end
| _29_597 -> begin
if ((FStar_List.length actuals) = 0) then begin
k
end else begin
(FStar_All.failwith "Wrong arity for kind unifier")
end
end)
end
| _29_599 -> begin
k
end)
end
| _29_601 -> begin
k
end)))

let rec visit_typ = (fun s mk vt me ctrl boundvars t -> (let visit_prod = (fun bs tc -> (let _29_662 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _29_615 b -> (match (_29_615) with
| (bs, boundvars, s) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(let _29_624 = (map_knd s mk vt me null_ctrl boundvars a.FStar_Absyn_Syntax.sort)
in (match (_29_624) with
| (k, _29_623) -> begin
(let a = (let _29_625 = a
in {FStar_Absyn_Syntax.v = _29_625.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _29_625.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((FStar_Util.Inl (a), imp))::bs, boundvars, s)
end else begin
(let boundvars' = (FStar_Util.Inl (a.FStar_Absyn_Syntax.v))::boundvars
in (let _29_637 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(FStar_Util.Inl (a), s, boundvars')
end
| _29_631 -> begin
(let b = (let _120_509 = (freshen_bvd a.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _120_509 k))
in (let s = (let _120_512 = (let _120_511 = (let _120_510 = (btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _120_510))
in FStar_Util.Inl (_120_511))
in (extend_subst _120_512 s))
in (FStar_Util.Inl (b), s, (FStar_Util.Inl (b.FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_29_637) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end)
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _29_645 = (map_typ s mk vt me null_ctrl boundvars x.FStar_Absyn_Syntax.sort)
in (match (_29_645) with
| (t, _29_644) -> begin
(let x = (let _29_646 = x
in {FStar_Absyn_Syntax.v = _29_646.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _29_646.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((FStar_Util.Inr (x), imp))::bs, boundvars, s)
end else begin
(let boundvars' = (FStar_Util.Inr (x.FStar_Absyn_Syntax.v))::boundvars
in (let _29_658 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(FStar_Util.Inr (x), s, boundvars')
end
| _29_652 -> begin
(let y = (let _120_522 = (freshen_bvd x.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _120_522 t))
in (let s = (let _120_525 = (let _120_524 = (let _120_523 = (bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _120_523))
in FStar_Util.Inr (_120_524))
in (extend_subst _120_525 s))
in (FStar_Util.Inr (y), s, (FStar_Util.Inr (y.FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_29_658) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end)
end))
end)
end)) ([], boundvars, s)))
in (match (_29_662) with
| (bs, boundvars, s) -> begin
(let tc = (match ((s, tc)) with
| ([], _29_665) -> begin
tc
end
| (_29_668, FStar_Util.Inl (t)) -> begin
(let _120_536 = (let _120_535 = (map_typ s mk vt me null_ctrl boundvars t)
in (FStar_All.pipe_left Prims.fst _120_535))
in FStar_Util.Inl (_120_536))
end
| (_29_673, FStar_Util.Inr (c)) -> begin
(let _120_559 = (let _120_558 = (map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl boundvars c)
in (FStar_All.pipe_left Prims.fst _120_558))
in FStar_Util.Inr (_120_559))
end)
in ((FStar_List.rev bs), tc))
end)))
in (let t0 = t
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_29_680) -> begin
(let _120_561 = (let _120_560 = (subst_typ' s t0)
in (FStar_All.pipe_left compress_typ _120_560))
in (_120_561, ctrl))
end
| _29_683 when (not (ctrl.descend)) -> begin
(map_typ s mk vt me null_ctrl boundvars t)
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((visit_prod bs (FStar_Util.Inr (c)))) with
| (bs, FStar_Util.Inr (c)) -> begin
(let _120_571 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t0.FStar_Absyn_Syntax.pos)
in (_120_571, ctrl))
end
| _29_693 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((visit_prod (((FStar_Util.Inr (x), None))::[]) (FStar_Util.Inl (t)))) with
| ((FStar_Util.Inr (x), _29_701)::[], FStar_Util.Inl (t)) -> begin
(let _120_572 = (FStar_Absyn_Syntax.mk_Typ_refine (x, t) None t0.FStar_Absyn_Syntax.pos)
in (_120_572, ctrl))
end
| _29_708 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(match ((visit_prod bs (FStar_Util.Inl (t)))) with
| (bs, FStar_Util.Inl (t)) -> begin
(let _120_573 = (FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t0.FStar_Absyn_Syntax.pos)
in (_120_573, ctrl))
end
| _29_718 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _29_720 -> begin
(let _29_724 = (vt null_ctrl boundvars t)
in (match (_29_724) with
| (t, _29_723) -> begin
(t, ctrl)
end))
end))))
and compress_typ' = (fun t -> (let t = (FStar_Absyn_Visit.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s), m) -> begin
(let res = (let _120_593 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] t')
in (FStar_All.pipe_left Prims.fst _120_593))
in (let res = (compress_typ' res)
in (let _29_736 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(let t = (let _120_595 = (mk_t ())
in (compress_typ' _120_595))
in (let _29_744 = (FStar_ST.op_Colon_Equals m (Some (t)))
in t))
end
| _29_747 -> begin
t
end)))
and compress_typ = (fun t -> (let t = (compress_typ' t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_29_751) -> begin
(FStar_All.failwith "Impossible: compress returned a delayed type")
end
| _29_754 -> begin
t
end)))

let rec visit_exp = (fun s mk me ve ctrl binders e -> (let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_29_764) -> begin
(let _120_661 = (let _120_660 = (subst_exp' s e)
in (FStar_All.pipe_left compress_exp _120_660))
in (_120_661, ctrl))
end
| _29_767 when (not (ctrl.descend)) -> begin
(map_exp s mk me ve ctrl binders e)
end
| _29_769 -> begin
(let _29_773 = (ve null_ctrl binders e)
in (match (_29_773) with
| (e, _29_772) -> begin
(e, ctrl)
end))
end)))
and compress_exp = (fun e -> (let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e', s, m) -> begin
(let e = (let _120_690 = (FStar_Absyn_Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] e')
in (FStar_All.pipe_left Prims.fst _120_690))
in (let res = (compress_exp e)
in (let _29_783 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| _29_786 -> begin
e
end)))

let rec unmeta_exp = (fun e -> (let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _29_791)) -> begin
(unmeta_exp e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _29_797, _29_799) -> begin
(unmeta_exp e)
end
| _29_803 -> begin
e
end)))

let alpha_typ = (fun t -> (let t = (compress_typ t)
in (let s = (mk_subst [])
in (let doit = (fun t -> (let _120_715 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp alpha_ctrl [] t)
in (FStar_All.pipe_left Prims.fst _120_715)))
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_lam (bs, _)) | (FStar_Absyn_Syntax.Typ_fun (bs, _)) -> begin
if (FStar_Util.for_all FStar_Absyn_Syntax.is_null_binder bs) then begin
t
end else begin
(doit t)
end
end
| FStar_Absyn_Syntax.Typ_refine (_29_819) -> begin
(doit t)
end
| _29_822 -> begin
t
end)))))

let formals_for_actuals = (fun formals actuals -> (FStar_List.map2 (fun formal actual -> (match (((Prims.fst formal), (Prims.fst actual))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, b))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, y))
end
| _29_838 -> begin
(FStar_All.failwith "Ill-typed substitution")
end)) formals actuals))

let compress_typ_opt = (fun _29_12 -> (match (_29_12) with
| None -> begin
None
end
| Some (t) -> begin
(let _120_722 = (compress_typ t)
in Some (_120_722))
end))

let mk_discriminator = (fun lid -> (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Absyn_Syntax.mk_ident ((Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText), lid.FStar_Ident.ident.FStar_Ident.idRange)))::[]))))

let is_name = (fun lid -> (let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText 0)
in (FStar_Util.is_upper c)))

let ml_comp = (fun t r -> (let _120_732 = (let _120_731 = (set_lid_range FStar_Absyn_Const.effect_ML_lid r)
in {FStar_Absyn_Syntax.effect_name = _120_731; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.MLEFFECT)::[]})
in (FStar_Absyn_Syntax.mk_Comp _120_732)))

let total_comp = (fun t r -> (FStar_Absyn_Syntax.mk_Total t))

let gtotal_comp = (fun t -> (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_GTot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.SOMETRIVIAL)::[]}))

let comp_set_flags = (fun c f -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_29_854) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _29_858 = c
in {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp ((let _29_860 = ct
in {FStar_Absyn_Syntax.effect_name = _29_860.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _29_860.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _29_860.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = f})); FStar_Absyn_Syntax.tk = _29_858.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _29_858.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _29_858.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _29_858.FStar_Absyn_Syntax.uvs})
end))

let comp_flags = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_29_864) -> begin
(FStar_Absyn_Syntax.TOTAL)::[]
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
ct.FStar_Absyn_Syntax.flags
end))

let comp_effect_name = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c.FStar_Absyn_Syntax.effect_name
end
| FStar_Absyn_Syntax.Total (_29_872) -> begin
FStar_Absyn_Const.effect_Tot_lid
end))

let comp_to_comp_typ = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c
end
| FStar_Absyn_Syntax.Total (t) -> begin
{FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.TOTAL)::[]}
end))

let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _29_13 -> (match (_29_13) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _29_884 -> begin
false
end)))))

let is_total_lcomp = (fun c -> ((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _29_14 -> (match (_29_14) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _29_890 -> begin
false
end))))))

let is_tot_or_gtot_lcomp = (fun c -> (((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _29_15 -> (match (_29_15) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _29_896 -> begin
false
end))))))

let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _29_16 -> (match (_29_16) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _29_902 -> begin
false
end)))))

let is_lcomp_partial_return = (fun c -> (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _29_17 -> (match (_29_17) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _29_908 -> begin
false
end)))))

let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_GTot_lid (comp_effect_name c))))

let is_pure_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_29_912) -> begin
true
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
((((is_tot_or_gtot_comp c) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _29_18 -> (match (_29_18) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _29_919 -> begin
false
end)))))
end))

let is_ghost_effect = (fun l -> (((FStar_Ident.lid_equals FStar_Absyn_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_Ghost_lid l)))

let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))

let is_pure_lcomp = (fun lc -> ((((is_total_lcomp lc) || (FStar_Ident.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _29_19 -> (match (_29_19) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _29_926 -> begin
false
end))))))

let is_pure_or_ghost_lcomp = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Absyn_Syntax.eff_name)))

let is_pure_or_ghost_function = (fun t -> (match ((let _120_771 = (compress_typ t)
in _120_771.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_29_930, c) -> begin
(is_pure_or_ghost_comp c)
end
| _29_935 -> begin
true
end))

let is_lemma = (fun t -> (match ((let _120_774 = (compress_typ t)
in _120_774.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_29_938, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid)
end
| _29_945 -> begin
false
end)
end
| _29_947 -> begin
false
end))

let is_smt_lemma = (fun t -> (match ((let _120_777 = (compress_typ t)
in _120_777.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_29_950, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| _req::_ens::(FStar_Util.Inr (pats), _29_961)::_29_957 -> begin
(match ((let _120_778 = (unmeta_exp pats)
in _120_778.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _29_978); FStar_Absyn_Syntax.tk = _29_975; FStar_Absyn_Syntax.pos = _29_973; FStar_Absyn_Syntax.fvs = _29_971; FStar_Absyn_Syntax.uvs = _29_969}, _29_983) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid)
end
| _29_987 -> begin
false
end)
end
| _29_989 -> begin
false
end)
end
| _29_991 -> begin
false
end)
end
| _29_993 -> begin
false
end))

let is_ml_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _29_20 -> (match (_29_20) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _29_1000 -> begin
false
end)))))
end
| _29_1002 -> begin
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
| FStar_Absyn_Syntax.Total (_29_1011) -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Absyn_Syntax.mk_Comp (let _29_1015 = ct
in {FStar_Absyn_Syntax.effect_name = _29_1015.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = _29_1015.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = _29_1015.FStar_Absyn_Syntax.flags}))
end))

let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _29_21 -> (match (_29_21) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _29_1022 -> begin
false
end)))))

let rec is_atom = (fun e -> (match ((let _120_788 = (compress_exp e)
in _120_788.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _29_1035)) -> begin
(is_atom e)
end
| _29_1040 -> begin
false
end))

let primops = (FStar_Absyn_Const.op_Eq)::(FStar_Absyn_Const.op_notEq)::(FStar_Absyn_Const.op_LT)::(FStar_Absyn_Const.op_LTE)::(FStar_Absyn_Const.op_GT)::(FStar_Absyn_Const.op_GTE)::(FStar_Absyn_Const.op_Subtraction)::(FStar_Absyn_Const.op_Minus)::(FStar_Absyn_Const.op_Addition)::(FStar_Absyn_Const.op_Multiply)::(FStar_Absyn_Const.op_Division)::(FStar_Absyn_Const.op_Modulus)::(FStar_Absyn_Const.op_And)::(FStar_Absyn_Const.op_Or)::(FStar_Absyn_Const.op_Negation)::[]

let is_primop = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _29_1044) -> begin
(FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _29_1048 -> begin
false
end))

let rec unascribe = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_ascribed (e, _29_1052, _29_1054) -> begin
(unascribe e)
end
| _29_1058 -> begin
e
end))

let rec ascribe_typ = (fun t k -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t', _29_1063) -> begin
(ascribe_typ t' k)
end
| _29_1067 -> begin
(FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.FStar_Absyn_Syntax.pos)
end))

let rec unascribe_typ = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t, _29_1071) -> begin
(unascribe_typ t)
end
| _29_1075 -> begin
t
end))

let rec unrefine = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _29_1080) -> begin
(unrefine x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _29_1085) -> begin
(unrefine t)
end
| _29_1089 -> begin
t
end)))

let is_fun = (fun e -> (match ((let _120_802 = (compress_exp e)
in _120_802.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (_29_1092) -> begin
true
end
| _29_1095 -> begin
false
end))

let is_function_typ = (fun t -> (match ((let _120_805 = (compress_typ t)
in _120_805.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_29_1098) -> begin
true
end
| _29_1101 -> begin
false
end))

let rec pre_typ = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _29_1106) -> begin
(pre_typ x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _29_1111) -> begin
(pre_typ t)
end
| _29_1115 -> begin
t
end)))

let destruct = (fun typ lid -> (let typ = (compress_typ typ)
in (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _29_1126; FStar_Absyn_Syntax.pos = _29_1124; FStar_Absyn_Syntax.fvs = _29_1122; FStar_Absyn_Syntax.uvs = _29_1120}, args) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some (args)
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some ([])
end
| _29_1136 -> begin
None
end)))

let rec lids_of_sigelt = (fun se -> (match (se) with
| (FStar_Absyn_Syntax.Sig_let (_, _, lids, _)) | (FStar_Absyn_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Absyn_Syntax.Sig_tycon (lid, _, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_datacon (lid, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_val_decl (lid, _, _, _)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (lid, _, _, _)) | (FStar_Absyn_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| FStar_Absyn_Syntax.Sig_new_effect (n, _29_1230) -> begin
(n.FStar_Absyn_Syntax.mname)::[]
end
| (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) -> begin
[]
end))

let lid_of_sigelt = (fun se -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _29_1246 -> begin
None
end))

let range_of_sigelt = (fun x -> (match (x) with
| (FStar_Absyn_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_datacon (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_val_decl (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_assume (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_let (_, r, _, _)) | (FStar_Absyn_Syntax.Sig_main (_, r)) | (FStar_Absyn_Syntax.Sig_pragma (_, r)) | (FStar_Absyn_Syntax.Sig_new_effect (_, r)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))

let range_of_lb = (fun _29_22 -> (match (_29_22) with
| (FStar_Util.Inl (x), _29_1357, _29_1359) -> begin
(range_of_bvd x)
end
| (FStar_Util.Inr (l), _29_1364, _29_1366) -> begin
(FStar_Ident.range_of_lid l)
end))

let range_of_arg = (fun _29_23 -> (match (_29_23) with
| (FStar_Util.Inl (hd), _29_1372) -> begin
hd.FStar_Absyn_Syntax.pos
end
| (FStar_Util.Inr (hd), _29_1377) -> begin
hd.FStar_Absyn_Syntax.pos
end))

let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))

let mk_typ_app = (fun f args -> (let r = (range_of_args args f.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (f, args) None r)))

let mk_exp_app = (fun f args -> (let r = (range_of_args args f.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Exp_app (f, args) None r)))

let mk_data = (fun l args -> (match (args) with
| [] -> begin
(let _120_838 = (let _120_837 = (let _120_836 = (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (_120_836, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_120_837))
in (FStar_Absyn_Syntax.mk_Exp_meta _120_838))
end
| _29_1393 -> begin
(let _120_842 = (let _120_841 = (let _120_840 = (let _120_839 = (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (mk_exp_app _120_839 args))
in (_120_840, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_120_841))
in (FStar_Absyn_Syntax.mk_Exp_meta _120_842))
end))

let mangle_field_name = (fun x -> (FStar_Ident.mk_ident ((Prims.strcat "^fname^" x.FStar_Ident.idText), x.FStar_Ident.idRange)))

let unmangle_field_name = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _120_848 = (let _120_847 = (FStar_Util.substring_from x.FStar_Ident.idText 7)
in (_120_847, x.FStar_Ident.idRange))
in (FStar_Ident.mk_ident _120_848))
end else begin
x
end)

let mk_field_projector_name = (fun lid x i -> (let nm = if (FStar_Absyn_Syntax.is_null_bvar x) then begin
(let _120_854 = (let _120_853 = (let _120_852 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _120_852))
in (_120_853, x.FStar_Absyn_Syntax.p))
in (FStar_Absyn_Syntax.mk_ident _120_854))
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (let y = (let _29_1402 = x.FStar_Absyn_Syntax.v
in {FStar_Absyn_Syntax.ppname = nm; FStar_Absyn_Syntax.realname = _29_1402.FStar_Absyn_Syntax.realname})
in (let _120_858 = (let _120_857 = (let _120_856 = (let _120_855 = (unmangle_field_name nm)
in (_120_855)::[])
in (FStar_List.append (FStar_Ident.ids_of_lid lid) _120_856))
in (FStar_Ident.lid_of_ids _120_857))
in (_120_858, y)))))

let unchecked_unify = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (_29_1408) -> begin
(let _120_863 = (let _120_862 = (let _120_861 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _120_861))
in (FStar_Util.format1 "Changing a fixed uvar! U%s\n" _120_862))
in (FStar_All.failwith _120_863))
end
| _29_1411 -> begin
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
| _29_1427 -> begin
false
end))

let eq_binder = (fun b1 b2 -> (match (((Prims.fst b1), (Prims.fst b2))) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| _29_1441 -> begin
false
end))

let uv_eq = (fun _29_1445 _29_1449 -> (match ((_29_1445, _29_1449)) with
| ((uv1, _29_1444), (uv2, _29_1448)) -> begin
(FStar_Unionfind.equivalent uv1 uv2)
end))

let union_uvs = (fun uvs1 uvs2 -> (let _120_892 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_k uvs2.FStar_Absyn_Syntax.uvars_k)
in (let _120_891 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_t uvs2.FStar_Absyn_Syntax.uvars_t)
in (let _120_890 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_e uvs2.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _120_892; FStar_Absyn_Syntax.uvars_t = _120_891; FStar_Absyn_Syntax.uvars_e = _120_890}))))

let union_fvs = (fun fvs1 fvs2 -> (let _120_898 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs)
in (let _120_897 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)
in {FStar_Absyn_Syntax.ftvs = _120_898; FStar_Absyn_Syntax.fxvs = _120_897})))

let union_fvs_uvs = (fun _29_1456 _29_1459 -> (match ((_29_1456, _29_1459)) with
| ((fvs1, uvs1), (fvs2, uvs2)) -> begin
(let _120_904 = (union_fvs fvs1 fvs2)
in (let _120_903 = (union_uvs uvs1 uvs2)
in (_120_904, _120_903)))
end))

let sub_fv = (fun _29_1462 _29_1465 -> (match ((_29_1462, _29_1465)) with
| ((fvs, uvs), (tvars, vvars)) -> begin
(let _120_925 = (let _29_1466 = fvs
in (let _120_924 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.ftvs tvars)
in (let _120_923 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.fxvs vvars)
in {FStar_Absyn_Syntax.ftvs = _120_924; FStar_Absyn_Syntax.fxvs = _120_923})))
in (_120_925, uvs))
end))

let stash = (fun uvonly s _29_1474 -> (match (_29_1474) with
| (fvs, uvs) -> begin
(let _29_1475 = (FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.uvs (Some (uvs)))
in if uvonly then begin
()
end else begin
(FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.fvs (Some (fvs)))
end)
end))

let single_fv = (fun x -> (let _120_936 = (FStar_Absyn_Syntax.new_ftv_set ())
in (FStar_Util.set_add x _120_936)))

let single_uv = (fun u -> (let _120_944 = (FStar_Absyn_Syntax.new_uv_set ())
in (FStar_Util.set_add u _120_944)))

let single_uvt = (fun u -> (let _120_952 = (FStar_Absyn_Syntax.new_uvt_set ())
in (FStar_Util.set_add u _120_952)))

let rec vs_typ' = (fun t uvonly cont -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_29_1486) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end else begin
(let _120_1067 = (let _120_1066 = (let _29_1490 = FStar_Absyn_Syntax.no_fvs
in (let _120_1065 = (single_fv a)
in {FStar_Absyn_Syntax.ftvs = _120_1065; FStar_Absyn_Syntax.fxvs = _29_1490.FStar_Absyn_Syntax.fxvs}))
in (_120_1066, FStar_Absyn_Syntax.no_uvs))
in (cont _120_1067))
end
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let _120_1070 = (let _120_1069 = (let _29_1496 = FStar_Absyn_Syntax.no_uvs
in (let _120_1068 = (single_uvt (uv, k))
in {FStar_Absyn_Syntax.uvars_k = _29_1496.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _120_1068; FStar_Absyn_Syntax.uvars_e = _29_1496.FStar_Absyn_Syntax.uvars_e}))
in (FStar_Absyn_Syntax.no_fvs, _120_1069))
in (cont _120_1070))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(vs_binders bs uvonly (fun _29_1508 -> (match (_29_1508) with
| (bvs, vs1) -> begin
(vs_comp c uvonly (fun vs2 -> (let _120_1074 = (let _120_1073 = (union_fvs_uvs vs1 vs2)
in (sub_fv _120_1073 bvs))
in (cont _120_1074))))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(vs_binders bs uvonly (fun _29_1516 -> (match (_29_1516) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _120_1078 = (let _120_1077 = (union_fvs_uvs vs1 vs2)
in (sub_fv _120_1077 bvs))
in (cont _120_1078))))
end)))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(vs_binders (((FStar_Util.Inr (x), None))::[]) uvonly (fun _29_1524 -> (match (_29_1524) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _120_1082 = (let _120_1081 = (union_fvs_uvs vs1 vs2)
in (sub_fv _120_1081 bvs))
in (cont _120_1082))))
end)))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(vs_typ t uvonly (fun vs1 -> (vs_args args uvonly (fun vs2 -> (let _120_1085 = (union_fvs_uvs vs1 vs2)
in (cont _120_1085))))))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _29_1534) -> begin
(vs_typ t uvonly cont)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _29_1540)) -> begin
(vs_typ t1 uvonly (fun vs1 -> (vs_typ t2 uvonly (fun vs2 -> (let _120_1088 = (union_fvs_uvs vs1 vs2)
in (cont _120_1088))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) -> begin
(vs_typ t uvonly cont)
end)))
and vs_binders = (fun bs uvonly cont -> (match (bs) with
| [] -> begin
(cont (no_bvars, (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs)))
end
| (FStar_Util.Inl (a), _29_1582)::rest -> begin
(vs_kind a.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _29_1590 -> (match (_29_1590) with
| ((tvars, vvars), vs2) -> begin
(let _120_1125 = (let _120_1124 = (let _120_1122 = (FStar_Util.set_add a tvars)
in (_120_1122, vvars))
in (let _120_1123 = (union_fvs_uvs vs vs2)
in (_120_1124, _120_1123)))
in (cont _120_1125))
end)))))
end
| (FStar_Util.Inr (x), _29_1595)::rest -> begin
(vs_typ x.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _29_1603 -> (match (_29_1603) with
| ((tvars, vvars), vs2) -> begin
(let _120_1149 = (let _120_1148 = (let _120_1146 = (FStar_Util.set_add x vvars)
in (tvars, _120_1146))
in (let _120_1147 = (union_fvs_uvs vs vs2)
in (_120_1148, _120_1147)))
in (cont _120_1149))
end)))))
end))
and vs_args = (fun args uvonly cont -> (match (args) with
| [] -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| (FStar_Util.Inl (t), _29_1613)::tl -> begin
(vs_typ t uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _120_1153 = (union_fvs_uvs ft1 ft2)
in (cont _120_1153))))))
end
| (FStar_Util.Inr (e), _29_1622)::tl -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _120_1156 = (union_fvs_uvs ft1 ft2)
in (cont _120_1156))))))
end))
and vs_typ = (fun t uvonly cont -> (match ((let _120_1159 = (FStar_ST.read t.FStar_Absyn_Syntax.fvs)
in (let _120_1158 = (FStar_ST.read t.FStar_Absyn_Syntax.uvs)
in (_120_1159, _120_1158)))) with
| (Some (_29_1632), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_typ' t uvonly (fun fvs -> (let _29_1640 = (stash uvonly t fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_typ' t uvonly (fun fvs -> (let _29_1647 = (stash uvonly t fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_kind' = (fun k uvonly cont -> (let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_29_1660, k) -> begin
(let _120_1164 = (let _120_1163 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "%s: Impossible ... found a Kind_lam bare" _120_1163))
in (FStar_All.failwith _120_1164))
end
| FStar_Absyn_Syntax.Kind_delayed (_29_1665) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(vs_args args uvonly (fun _29_1676 -> (match (_29_1676) with
| (fvs, uvs) -> begin
(let _120_1168 = (let _120_1167 = (let _29_1677 = uvs
in (let _120_1166 = (FStar_Util.set_add uv uvs.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _120_1166; FStar_Absyn_Syntax.uvars_t = _29_1677.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _29_1677.FStar_Absyn_Syntax.uvars_e}))
in (fvs, _120_1167))
in (cont _120_1168))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev (_29_1680, k) -> begin
(vs_kind k uvonly cont)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(vs_binders bs uvonly (fun _29_1690 -> (match (_29_1690) with
| (bvs, vs1) -> begin
(vs_kind k uvonly (fun vs2 -> (let _120_1172 = (let _120_1171 = (union_fvs_uvs vs1 vs2)
in (sub_fv _120_1171 bvs))
in (cont _120_1172))))
end)))
end)))
and vs_kind = (fun k uvonly cont -> (match ((let _120_1175 = (FStar_ST.read k.FStar_Absyn_Syntax.fvs)
in (let _120_1174 = (FStar_ST.read k.FStar_Absyn_Syntax.uvs)
in (_120_1175, _120_1174)))) with
| (Some (_29_1697), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_kind' k uvonly (fun fvs -> (let _29_1705 = (stash uvonly k fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_kind' k uvonly (fun fvs -> (let _29_1712 = (stash uvonly k fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_exp' = (fun e uvonly cont -> (let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_29_1725) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(let _120_1181 = (let _120_1180 = (let _29_1737 = FStar_Absyn_Syntax.no_uvs
in (let _120_1179 = (single_uvt (uv, t))
in {FStar_Absyn_Syntax.uvars_k = _29_1737.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _29_1737.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _120_1179}))
in (FStar_Absyn_Syntax.no_fvs, _120_1180))
in (cont _120_1181))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end else begin
(let _120_1184 = (let _120_1183 = (let _29_1741 = FStar_Absyn_Syntax.no_fvs
in (let _120_1182 = (single_fv x)
in {FStar_Absyn_Syntax.ftvs = _29_1741.FStar_Absyn_Syntax.ftvs; FStar_Absyn_Syntax.fxvs = _120_1182}))
in (_120_1183, FStar_Absyn_Syntax.no_uvs))
in (cont _120_1184))
end
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _29_1745, _29_1747) -> begin
(vs_exp e uvonly cont)
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(vs_binders bs uvonly (fun _29_1756 -> (match (_29_1756) with
| (bvs, vs1) -> begin
(vs_exp e uvonly (fun vs2 -> (let _120_1188 = (let _120_1187 = (union_fvs_uvs vs1 vs2)
in (sub_fv _120_1187 bvs))
in (cont _120_1188))))
end)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args args uvonly (fun ft2 -> (let _120_1191 = (union_fvs_uvs ft1 ft2)
in (cont _120_1191))))))
end
| (FStar_Absyn_Syntax.Exp_match (_)) | (FStar_Absyn_Syntax.Exp_let (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _29_1772)) -> begin
(vs_exp e uvonly cont)
end)))
and vs_exp = (fun e uvonly cont -> (match ((let _120_1194 = (FStar_ST.read e.FStar_Absyn_Syntax.fvs)
in (let _120_1193 = (FStar_ST.read e.FStar_Absyn_Syntax.uvs)
in (_120_1194, _120_1193)))) with
| (Some (_29_1781), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_exp' e uvonly (fun fvs -> (let _29_1789 = (stash uvonly e fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_exp' e uvonly (fun fvs -> (let _29_1796 = (stash uvonly e fvs)
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
(vs_typ ct.FStar_Absyn_Syntax.result_typ uvonly (fun vs1 -> (vs_args ct.FStar_Absyn_Syntax.effect_args uvonly (fun vs2 -> (let _120_1200 = (union_fvs_uvs vs1 vs2)
in (k _120_1200))))))
end
end))
and vs_comp = (fun c uvonly cont -> (match ((let _120_1203 = (FStar_ST.read c.FStar_Absyn_Syntax.fvs)
in (let _120_1202 = (FStar_ST.read c.FStar_Absyn_Syntax.uvs)
in (_120_1203, _120_1202)))) with
| (Some (_29_1818), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_comp' c uvonly (fun fvs -> (let _29_1826 = (stash uvonly c fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_comp' c uvonly (fun fvs -> (let _29_1833 = (stash uvonly c fvs)
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
(vs_either hd uvonly (fun ft1 -> (vs_either_l tl uvonly (fun ft2 -> (let _120_1210 = (union_fvs_uvs ft1 ft2)
in (cont _120_1210))))))
end))

let freevars_kind = (fun k -> (vs_kind k false (fun _29_1862 -> (match (_29_1862) with
| (x, _29_1861) -> begin
x
end))))

let freevars_typ = (fun t -> (vs_typ t false (fun _29_1867 -> (match (_29_1867) with
| (x, _29_1866) -> begin
x
end))))

let freevars_exp = (fun e -> (vs_exp e false (fun _29_1872 -> (match (_29_1872) with
| (x, _29_1871) -> begin
x
end))))

let freevars_comp = (fun c -> (vs_comp c false (fun _29_1877 -> (match (_29_1877) with
| (x, _29_1876) -> begin
x
end))))

let freevars_args = (fun args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(let _120_1226 = (freevars_typ t)
in (FStar_All.pipe_left (union_fvs out) _120_1226))
end
| FStar_Util.Inr (e) -> begin
(let _120_1227 = (freevars_exp e)
in (FStar_All.pipe_left (union_fvs out) _120_1227))
end)) FStar_Absyn_Syntax.no_fvs)))

let is_free = (fun axs fvs -> (FStar_All.pipe_right axs (FStar_Util.for_some (fun _29_24 -> (match (_29_24) with
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
| SynSumKind (_29_1894) -> begin
_29_1894
end))

let ___SynSumType____0 = (fun projectee -> (match (projectee) with
| SynSumType (_29_1897) -> begin
_29_1897
end))

let ___SynSumExp____0 = (fun projectee -> (match (projectee) with
| SynSumExp (_29_1900) -> begin
_29_1900
end))

let ___SynSumComp____0 = (fun projectee -> (match (projectee) with
| SynSumComp (_29_1903) -> begin
_29_1903
end))

let rec update_uvars = (fun s uvs -> (let out = (let _120_1301 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_k)
in (FStar_All.pipe_right _120_1301 (FStar_List.fold_left (fun out u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(let _120_1299 = (uvars_in_kind k)
in (union_uvs _120_1299 out))
end
| _29_1911 -> begin
(let _29_1912 = out
in (let _120_1300 = (FStar_Util.set_add u out.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _120_1300; FStar_Absyn_Syntax.uvars_t = _29_1912.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _29_1912.FStar_Absyn_Syntax.uvars_e}))
end)) FStar_Absyn_Syntax.no_uvs)))
in (let out = (let _120_1306 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _120_1306 (FStar_List.fold_left (fun out _29_1918 -> (match (_29_1918) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (t) -> begin
(let _120_1304 = (uvars_in_typ t)
in (union_uvs _120_1304 out))
end
| _29_1922 -> begin
(let _29_1923 = out
in (let _120_1305 = (FStar_Util.set_add (u, t) out.FStar_Absyn_Syntax.uvars_t)
in {FStar_Absyn_Syntax.uvars_k = _29_1923.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _120_1305; FStar_Absyn_Syntax.uvars_e = _29_1923.FStar_Absyn_Syntax.uvars_e}))
end)
end)) out)))
in (let out = (let _120_1311 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_e)
in (FStar_All.pipe_right _120_1311 (FStar_List.fold_left (fun out _29_1929 -> (match (_29_1929) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(let _120_1309 = (uvars_in_exp e)
in (union_uvs _120_1309 out))
end
| _29_1933 -> begin
(let _29_1934 = out
in (let _120_1310 = (FStar_Util.set_add (u, t) out.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _29_1934.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _29_1934.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _120_1310}))
end)
end)) out)))
in (let _29_1945 = (match (s) with
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
and uvars_in_kind = (fun k -> (let _120_1314 = (vs_kind k true (fun _29_1951 -> (match (_29_1951) with
| (_29_1949, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumKind (k))) _120_1314)))
and uvars_in_typ = (fun t -> (let _120_1317 = (vs_typ t true (fun _29_1956 -> (match (_29_1956) with
| (_29_1954, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumType (t))) _120_1317)))
and uvars_in_exp = (fun e -> (let _120_1320 = (vs_exp e true (fun _29_1961 -> (match (_29_1961) with
| (_29_1959, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumExp (e))) _120_1320)))
and uvars_in_comp = (fun c -> (let _120_1323 = (vs_comp c true (fun _29_1966 -> (match (_29_1966) with
| (_29_1964, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumComp (c))) _120_1323)))

let uvars_included_in = (fun u1 u2 -> (((FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_k u2.FStar_Absyn_Syntax.uvars_k) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_t u2.FStar_Absyn_Syntax.uvars_t)) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_e u2.FStar_Absyn_Syntax.uvars_e)))

let rec kind_formals = (fun k -> (let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_29_1972) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
([], k)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _29_1986 = (kind_formals k)
in (match (_29_1986) with
| (bs', k) -> begin
((FStar_List.append bs bs'), k)
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_29_1988, k) -> begin
(kind_formals k)
end
| FStar_Absyn_Syntax.Kind_delayed (_29_1993) -> begin
(FStar_All.failwith "Impossible")
end)))

let close_for_kind = (fun t k -> (let _29_2000 = (kind_formals k)
in (match (_29_2000) with
| (bs, _29_1999) -> begin
(match (bs) with
| [] -> begin
t
end
| _29_2003 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.FStar_Absyn_Syntax.pos)
end)
end)))

let rec unabbreviate_kind = (fun k -> (let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_abbrev (_29_2007, k) -> begin
(unabbreviate_kind k)
end
| _29_2012 -> begin
k
end)))

let close_with_lam = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _29_2017 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (tps, t) None t.FStar_Absyn_Syntax.pos)
end))

let close_with_arrow = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _29_2022 -> begin
(let _29_2031 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
((FStar_List.append tps bs'), c)
end
| _29_2028 -> begin
(let _120_1344 = (FStar_Absyn_Syntax.mk_Total t)
in (tps, _120_1344))
end)
in (match (_29_2031) with
| (bs, c) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.FStar_Absyn_Syntax.pos)
end))
end))

let close_typ = close_with_arrow

let close_kind = (fun tps k -> (match (tps) with
| [] -> begin
k
end
| _29_2036 -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow' (tps, k) k.FStar_Absyn_Syntax.pos)
end))

let is_tuple_constructor = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Ident.str "Prims.Tuple")
end
| _29_2041 -> begin
false
end))

let mk_tuple_lid = (fun n r -> (let t = (let _120_1357 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Tuple%s" _120_1357))
in (let _120_1358 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _120_1358 r))))

let mk_tuple_data_lid = (fun n r -> (let t = (let _120_1363 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkTuple%s" _120_1363))
in (let _120_1364 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _120_1364 r))))

let is_tuple_data_lid = (fun f n -> (let _120_1369 = (mk_tuple_data_lid n FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.lid_equals f _120_1369)))

let is_dtuple_constructor = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Ident.str "Prims.DTuple")
end
| _29_2054 -> begin
false
end))

let mk_dtuple_lid = (fun n r -> (let t = (let _120_1376 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "DTuple%s" _120_1376))
in (let _120_1377 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _120_1377 r))))

let mk_dtuple_data_lid = (fun n r -> (let t = (let _120_1382 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkDTuple%s" _120_1382))
in (let _120_1383 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _120_1383 r))))

let is_lid_equality = (fun x -> ((((FStar_Ident.lid_equals x FStar_Absyn_Const.eq_lid) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eq2_lid)) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eqA_lid)) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eqT_lid)))

let is_forall = (fun lid -> ((FStar_Ident.lid_equals lid FStar_Absyn_Const.forall_lid) || (FStar_Ident.lid_equals lid FStar_Absyn_Const.allTyp_lid)))

let is_exists = (fun lid -> ((FStar_Ident.lid_equals lid FStar_Absyn_Const.exists_lid) || (FStar_Ident.lid_equals lid FStar_Absyn_Const.exTyp_lid)))

let is_qlid = (fun lid -> ((is_forall lid) || (is_exists lid)))

let is_equality = (fun x -> (is_lid_equality x.FStar_Absyn_Syntax.v))

let lid_is_connective = (let lst = (FStar_Absyn_Const.and_lid)::(FStar_Absyn_Const.or_lid)::(FStar_Absyn_Const.not_lid)::(FStar_Absyn_Const.iff_lid)::(FStar_Absyn_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))

let is_constructor = (fun t lid -> (match ((let _120_1399 = (pre_typ t)
in _120_1399.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid)
end
| _29_2073 -> begin
false
end))

let rec is_constructed_typ = (fun t lid -> (match ((let _120_1404 = (pre_typ t)
in _120_1404.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (_29_2077) -> begin
(is_constructor t lid)
end
| FStar_Absyn_Syntax.Typ_app (t, _29_2081) -> begin
(is_constructed_typ t lid)
end
| _29_2085 -> begin
false
end))

let rec get_tycon = (fun t -> (let t = (pre_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
Some (t)
end
| FStar_Absyn_Syntax.Typ_app (t, _29_2096) -> begin
(get_tycon t)
end
| _29_2100 -> begin
None
end)))

let base_kind = (fun _29_25 -> (match (_29_25) with
| FStar_Absyn_Syntax.Kind_type -> begin
true
end
| _29_2104 -> begin
false
end))

let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _29_2110 _29_2114 -> (match ((_29_2110, _29_2114)) with
| ((fn1, _29_2109), (fn2, _29_2113)) -> begin
(FStar_String.compare (FStar_Ident.text_of_lid fn1) (FStar_Ident.text_of_lid fn2))
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

let b2t_v = (let _120_1415 = (let _120_1414 = (let _120_1413 = (let _120_1412 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder t_bool)
in (_120_1412)::[])
in (_120_1413, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _120_1414 FStar_Absyn_Syntax.dummyRange))
in (ftv FStar_Absyn_Const.b2t_lid _120_1415))

let mk_conj_opt = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _120_1421 = (let _120_1420 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (tand, ((FStar_Absyn_Syntax.targ phi1))::((FStar_Absyn_Syntax.targ phi2))::[]) None _120_1420))
in Some (_120_1421))
end))

let mk_binop = (fun op_t phi1 phi2 -> (let _120_1428 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (op_t, ((FStar_Absyn_Syntax.targ phi1))::((FStar_Absyn_Syntax.targ phi2))::[]) None _120_1428)))

let mk_neg = (fun phi -> (let _120_1432 = (let _120_1431 = (ftv FStar_Absyn_Const.not_lid kt_kt)
in (_120_1431, ((FStar_Absyn_Syntax.targ phi))::[]))
in (FStar_Absyn_Syntax.mk_Typ_app _120_1432 None phi.FStar_Absyn_Syntax.pos)))

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

let mk_imp = (fun phi1 phi2 -> (match ((let _120_1449 = (compress_typ phi1)
in _120_1449.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid) -> begin
t_true
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
phi2
end
| _29_2145 -> begin
(match ((let _120_1450 = (compress_typ phi2)
in _120_1450.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when ((FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) || (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid)) -> begin
phi2
end
| _29_2149 -> begin
(mk_binop timp phi1 phi2)
end)
end))

let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))

let b2t = (fun e -> (let _120_1459 = (let _120_1458 = (let _120_1457 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg e)
in (_120_1457)::[])
in (b2t_v, _120_1458))
in (FStar_Absyn_Syntax.mk_Typ_app _120_1459 None e.FStar_Absyn_Syntax.pos)))

let rec unmeta_typ = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(unmeta_typ t)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _29_2189)) -> begin
(mk_conj t1 t2)
end
| _29_2194 -> begin
t
end)))

let eq_k = (let a = (let _120_1462 = (new_bvd None)
in (bvd_to_bvar_s _120_1462 FStar_Absyn_Syntax.ktype))
in (let atyp = (btvar_to_typ a)
in (let b = (let _120_1463 = (new_bvd None)
in (bvd_to_bvar_s _120_1463 FStar_Absyn_Syntax.ktype))
in (let btyp = (btvar_to_typ b)
in (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit)))::((FStar_Util.Inl (b), Some (FStar_Absyn_Syntax.Implicit)))::((FStar_Absyn_Syntax.null_v_binder atyp))::((FStar_Absyn_Syntax.null_v_binder btyp))::[], FStar_Absyn_Syntax.ktype) FStar_Absyn_Syntax.dummyRange)))))

let teq = (ftv FStar_Absyn_Const.eq2_lid eq_k)

let mk_eq = (fun t1 t2 e1 e2 -> (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((_, FStar_Absyn_Syntax.Typ_unknown)) -> begin
(FStar_All.failwith "DIE! mk_eq with tun")
end
| _29_2212 -> begin
(let _120_1472 = (FStar_Range.union_ranges e1.FStar_Absyn_Syntax.pos e2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (teq, ((FStar_Absyn_Syntax.itarg t1))::((FStar_Absyn_Syntax.itarg t2))::((FStar_Absyn_Syntax.varg e1))::((FStar_Absyn_Syntax.varg e2))::[]) None _120_1472))
end))

let eq_typ = (ftv FStar_Absyn_Const.eqT_lid FStar_Absyn_Syntax.kun)

let mk_eq_typ = (fun t1 t2 -> (let _120_1477 = (FStar_Range.union_ranges t1.FStar_Absyn_Syntax.pos t2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (eq_typ, ((FStar_Absyn_Syntax.targ t1))::((FStar_Absyn_Syntax.targ t2))::[]) None _120_1477)))

let lex_t = (ftv FStar_Absyn_Const.lex_t_lid FStar_Absyn_Syntax.ktype)

let lex_top = (let lexnil = (withinfo FStar_Absyn_Const.lextop_lid lex_t FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.mk_Exp_fvar (lexnil, Some (FStar_Absyn_Syntax.Data_ctor)) None FStar_Absyn_Syntax.dummyRange))

let lex_pair = (let a = (gen_bvar FStar_Absyn_Syntax.ktype)
in (let lexcons = (let _120_1484 = (let _120_1483 = (let _120_1482 = (let _120_1480 = (let _120_1479 = (let _120_1478 = (btvar_to_typ a)
in (FStar_Absyn_Syntax.null_v_binder _120_1478))
in (_120_1479)::((FStar_Absyn_Syntax.null_v_binder lex_t))::[])
in ((FStar_Absyn_Syntax.t_binder a))::_120_1480)
in (let _120_1481 = (FStar_Absyn_Syntax.mk_Total lex_t)
in (_120_1482, _120_1481)))
in (FStar_Absyn_Syntax.mk_Typ_fun _120_1483 None FStar_Absyn_Syntax.dummyRange))
in (withinfo FStar_Absyn_Const.lexcons_lid _120_1484 FStar_Absyn_Syntax.dummyRange))
in (FStar_Absyn_Syntax.mk_Exp_fvar (lexcons, Some (FStar_Absyn_Syntax.Data_ctor)) None FStar_Absyn_Syntax.dummyRange)))

let forall_kind = (let a = (let _120_1485 = (new_bvd None)
in (bvd_to_bvar_s _120_1485 FStar_Absyn_Syntax.ktype))
in (let atyp = (btvar_to_typ a)
in (let _120_1490 = (let _120_1489 = (let _120_1488 = (let _120_1487 = (let _120_1486 = (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_v_binder atyp))::[], FStar_Absyn_Syntax.ktype) FStar_Absyn_Syntax.dummyRange)
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _120_1486))
in (_120_1487)::[])
in ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit)))::_120_1488)
in (_120_1489, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _120_1490 FStar_Absyn_Syntax.dummyRange))))

let tforall = (ftv FStar_Absyn_Const.forall_lid forall_kind)

let allT_k = (fun k -> (let _120_1496 = (let _120_1495 = (let _120_1494 = (let _120_1493 = (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder k))::[], FStar_Absyn_Syntax.ktype) FStar_Absyn_Syntax.dummyRange)
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _120_1493))
in (_120_1494)::[])
in (_120_1495, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _120_1496 FStar_Absyn_Syntax.dummyRange)))

let eqT_k = (fun k -> (let _120_1501 = (let _120_1500 = (let _120_1499 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder k)
in (_120_1499)::((FStar_Absyn_Syntax.null_t_binder k))::[])
in (_120_1500, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _120_1501 FStar_Absyn_Syntax.dummyRange)))

let tforall_typ = (fun k -> (let _120_1504 = (allT_k k)
in (ftv FStar_Absyn_Const.allTyp_lid _120_1504)))

let mk_forallT = (fun a b -> (let _120_1513 = (let _120_1512 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _120_1511 = (let _120_1510 = (let _120_1509 = (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_Absyn_Syntax.t_binder a))::[], b) None b.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _120_1509))
in (_120_1510)::[])
in (_120_1512, _120_1511)))
in (FStar_Absyn_Syntax.mk_Typ_app _120_1513 None b.FStar_Absyn_Syntax.pos)))

let mk_forall = (fun x body -> (let r = FStar_Absyn_Syntax.dummyRange
in (let _120_1521 = (let _120_1520 = (let _120_1519 = (let _120_1518 = (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_Absyn_Syntax.v_binder x))::[], body) None r)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _120_1518))
in (_120_1519)::[])
in (tforall, _120_1520))
in (FStar_Absyn_Syntax.mk_Typ_app _120_1521 None r))))

let rec close_forall = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
f
end else begin
(let body = (FStar_Absyn_Syntax.mk_Typ_lam ((b)::[], f) None f.FStar_Absyn_Syntax.pos)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _120_1529 = (let _120_1528 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (_120_1528, ((FStar_Absyn_Syntax.targ body))::[]))
in (FStar_Absyn_Syntax.mk_Typ_app _120_1529 None f.FStar_Absyn_Syntax.pos))
end
| FStar_Util.Inr (x) -> begin
(FStar_Absyn_Syntax.mk_Typ_app (tforall, ((FStar_Util.Inl (x.FStar_Absyn_Syntax.sort), Some (FStar_Absyn_Syntax.Implicit)))::((FStar_Absyn_Syntax.targ body))::[]) None f.FStar_Absyn_Syntax.pos)
end))
end) bs f))

let rec is_wild_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_wild (_29_2239) -> begin
true
end
| _29_2242 -> begin
false
end))

let head_and_args = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(head, args)
end
| _29_2250 -> begin
(t, [])
end)))

let head_and_args_e = (fun e -> (let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(head, args)
end
| _29_2258 -> begin
(e, [])
end)))

let function_formals = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
Some ((bs, c))
end
| _29_2266 -> begin
None
end)))

let is_interpreted = (fun l -> (let theory_syms = (FStar_Absyn_Const.op_Eq)::(FStar_Absyn_Const.op_notEq)::(FStar_Absyn_Const.op_LT)::(FStar_Absyn_Const.op_LTE)::(FStar_Absyn_Const.op_GT)::(FStar_Absyn_Const.op_GTE)::(FStar_Absyn_Const.op_Subtraction)::(FStar_Absyn_Const.op_Minus)::(FStar_Absyn_Const.op_Addition)::(FStar_Absyn_Const.op_Multiply)::(FStar_Absyn_Const.op_Division)::(FStar_Absyn_Const.op_Modulus)::(FStar_Absyn_Const.op_And)::(FStar_Absyn_Const.op_Or)::(FStar_Absyn_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))

type qpats =
FStar_Absyn_Syntax.args Prims.list

type connective =
| QAll of (FStar_Absyn_Syntax.binders * qpats * FStar_Absyn_Syntax.typ)
| QEx of (FStar_Absyn_Syntax.binders * qpats * FStar_Absyn_Syntax.typ)
| BaseConn of (FStar_Ident.lident * FStar_Absyn_Syntax.args)

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
| QAll (_29_2271) -> begin
_29_2271
end))

let ___QEx____0 = (fun projectee -> (match (projectee) with
| QEx (_29_2274) -> begin
_29_2274
end))

let ___BaseConn____0 = (fun projectee -> (match (projectee) with
| BaseConn (_29_2277) -> begin
_29_2277
end))

let destruct_typ_as_formula = (fun f -> (let destruct_base_conn = (fun f -> (let _29_2283 = (true, false)
in (match (_29_2283) with
| (type_sort, term_sort) -> begin
(let oneType = (type_sort)::[]
in (let twoTypes = (type_sort)::(type_sort)::[]
in (let threeTys = (type_sort)::(type_sort)::(type_sort)::[]
in (let twoTerms = (term_sort)::(term_sort)::[]
in (let connectives = ((FStar_Absyn_Const.true_lid, []))::((FStar_Absyn_Const.false_lid, []))::((FStar_Absyn_Const.and_lid, twoTypes))::((FStar_Absyn_Const.or_lid, twoTypes))::((FStar_Absyn_Const.imp_lid, twoTypes))::((FStar_Absyn_Const.iff_lid, twoTypes))::((FStar_Absyn_Const.ite_lid, threeTys))::((FStar_Absyn_Const.not_lid, oneType))::((FStar_Absyn_Const.eqT_lid, twoTypes))::((FStar_Absyn_Const.eq2_lid, twoTerms))::((FStar_Absyn_Const.eq2_lid, (FStar_List.append twoTypes twoTerms)))::[]
in (let rec aux = (fun f _29_2293 -> (match (_29_2293) with
| (lid, arity) -> begin
(let _29_2296 = (head_and_args f)
in (match (_29_2296) with
| (t, args) -> begin
if (((is_constructor t lid) && ((FStar_List.length args) = (FStar_List.length arity))) && (FStar_List.forall2 (fun arg flag -> (match (arg) with
| (FStar_Util.Inl (_29_2300), _29_2303) -> begin
(flag = type_sort)
end
| (FStar_Util.Inr (_29_2306), _29_2309) -> begin
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
(let _120_1593 = (compress_typ t)
in (pats, _120_1593))
end
| _29_2320 -> begin
(let _120_1594 = (compress_typ t)
in ([], _120_1594))
end)))
in (let destruct_q_conn = (fun t -> (let is_q = (fun fa l -> if fa then begin
(is_forall l)
end else begin
(is_exists l)
end)
in (let flat = (fun t -> (let _29_2330 = (head_and_args t)
in (match (_29_2330) with
| (t, args) -> begin
(let _120_1608 = (FStar_All.pipe_right args (FStar_List.map (fun _29_26 -> (match (_29_26) with
| (FStar_Util.Inl (t), imp) -> begin
(let _120_1605 = (let _120_1604 = (compress_typ t)
in FStar_Util.Inl (_120_1604))
in (_120_1605, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _120_1607 = (let _120_1606 = (compress_exp e)
in FStar_Util.Inr (_120_1606))
in (_120_1607, imp))
end))))
in (t, _120_1608))
end)))
in (let rec aux = (fun qopt out t -> (match ((let _120_1615 = (flat t)
in (qopt, _120_1615))) with
| ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _::(FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_q fa tc.FStar_Absyn_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _::(FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_qlid tc.FStar_Absyn_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Absyn_Syntax.v))) ((b)::out) t2)
end
| (Some (true), _29_2478) -> begin
(let _29_2482 = (patterns t)
in (match (_29_2482) with
| (pats, body) -> begin
Some (QAll (((FStar_List.rev out), pats, body)))
end))
end
| (Some (false), _29_2486) -> begin
(let _29_2490 = (patterns t)
in (match (_29_2490) with
| (pats, body) -> begin
Some (QEx (((FStar_List.rev out), pats, body)))
end))
end
| _29_2492 -> begin
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




