
open Prims
let handle_err = (fun warning ret e -> (match (e) with
| FStar_Util.Failure (s) -> begin
(let _92_7 = (FStar_Util.format1 "Fatal: %s" s)
in (FStar_Util.print_string _92_7))
end
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(let _26_36 = (let _92_9 = (let _92_8 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s : %s\n%s\n" _92_8 (if warning then begin
"Warning"
end else begin
"Error"
end) msg))
in (FStar_Util.print_string _92_9))
in ())
end
| FStar_Util.NYI (s) -> begin
(let _26_40 = (let _92_10 = (FStar_Util.format1 "Feature not yet implemented: %s" s)
in (FStar_Util.print_string _92_10))
in ())
end
| FStar_Absyn_Syntax.Err (s) -> begin
(let _92_11 = (FStar_Util.format1 "Error: %s" s)
in (FStar_Util.print_string _92_11))
end
| _26_45 -> begin
(Prims.raise e)
end))

let handleable = (fun _26_1 -> (match (_26_1) with
| (FStar_Util.Failure (_)) | (FStar_Absyn_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Absyn_Syntax.Err (_)) -> begin
true
end
| _26_60 -> begin
false
end))

type gensym_t =
{gensym : Prims.unit  ->  Prims.string; reset : Prims.unit  ->  Prims.unit}

let is_Mkgensym_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkgensym_t"))))

let gs = (let ctr = (FStar_Util.mk_ref 0)
in (let n_resets = (FStar_Util.mk_ref 0)
in {gensym = (fun _26_66 -> (match (()) with
| () -> begin
(let _92_39 = (let _92_36 = (let _92_35 = (let _92_34 = (FStar_ST.read n_resets)
in (FStar_Util.string_of_int _92_34))
in (Prims.strcat "_" _92_35))
in (Prims.strcat _92_36 "_"))
in (let _92_38 = (let _92_37 = (let _26_67 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
in (FStar_Util.string_of_int _92_37))
in (Prims.strcat _92_39 _92_38)))
end)); reset = (fun _26_69 -> (match (()) with
| () -> begin
(let _26_70 = (FStar_ST.op_Colon_Equals ctr 0)
in (FStar_Util.incr n_resets))
end))}))

let gensym = (fun _26_72 -> (match (()) with
| () -> begin
(gs.gensym ())
end))

let reset_gensym = (fun _26_73 -> (match (()) with
| () -> begin
(gs.reset ())
end))

let rec gensyms = (fun x -> (match (x) with
| 0 -> begin
[]
end
| n -> begin
(let _92_48 = (gensym ())
in (let _92_47 = (gensyms (n - 1))
in (_92_48)::_92_47))
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

let mkbvd = (fun _26_87 -> (match (_26_87) with
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
| _26_114 -> begin
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

let freshen_bvd = (fun bvd' -> (let _92_89 = (let _92_88 = (genident (Some ((range_of_bvd bvd'))))
in (bvd'.FStar_Absyn_Syntax.ppname, _92_88))
in (mkbvd _92_89)))

let freshen_bvar = (fun b -> (let _92_91 = (freshen_bvd b.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _92_91 b.FStar_Absyn_Syntax.sort)))

let gen_bvar = (fun sort -> (let bvd = (new_bvd None)
in (bvd_to_bvar_s bvd sort)))

let gen_bvar_p = (fun r sort -> (let bvd = (new_bvd (Some (r)))
in (bvd_to_bvar_s bvd sort)))

let bvdef_of_str = (fun s -> (let f = (fun s -> (let id = (FStar_Absyn_Syntax.id_of_text s)
in (mkbvd (id, id))))
in (f s)))

let set_bvd_range = (fun bvd r -> (let _92_100 = (FStar_Absyn_Syntax.mk_ident (bvd.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText, r))
in (let _92_99 = (FStar_Absyn_Syntax.mk_ident (bvd.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText, r))
in {FStar_Absyn_Syntax.ppname = _92_100; FStar_Absyn_Syntax.realname = _92_99})))

let set_lid_range = (fun l r -> (let ids = (FStar_All.pipe_right (FStar_List.append l.FStar_Absyn_Syntax.ns ((l.FStar_Absyn_Syntax.ident)::[])) (FStar_List.map (fun i -> (FStar_Absyn_Syntax.mk_ident (i.FStar_Absyn_Syntax.idText, r)))))
in (FStar_Absyn_Syntax.lid_of_ids ids)))

let fv = (fun l -> (let _92_108 = (FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l FStar_Absyn_Syntax.tun _92_108)))

let fvvar_of_lid = (fun l t -> (let _92_111 = (FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l t _92_111)))

let fvar = (fun dc l r -> (let _92_120 = (let _92_119 = (let _92_118 = (set_lid_range l r)
in (fv _92_118))
in (_92_119, dc))
in (FStar_Absyn_Syntax.mk_Exp_fvar _92_120 None r)))

let ftv = (fun l k -> (let _92_127 = (let _92_125 = (FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l k _92_125))
in (let _92_126 = (FStar_Absyn_Syntax.range_of_lid l)
in (FStar_Absyn_Syntax.mk_Typ_const _92_127 None _92_126))))

let order_bvd = (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (_26_160), FStar_Util.Inr (_26_163)) -> begin
(- (1))
end
| (FStar_Util.Inr (_26_167), FStar_Util.Inl (_26_170)) -> begin
1
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText y.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText y.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText)
end))

let arg_of_non_null_binder = (fun _26_185 -> (match (_26_185) with
| (b, imp) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let _92_132 = (let _92_131 = (btvar_to_typ a)
in FStar_Util.Inl (_92_131))
in (_92_132, imp))
end
| FStar_Util.Inr (x) -> begin
(let _92_134 = (let _92_133 = (bvar_to_exp x)
in FStar_Util.Inr (_92_133))
in (_92_134, imp))
end)
end))

let args_of_non_null_binders = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
[]
end else begin
(let _92_138 = (arg_of_non_null_binder b)
in (_92_138)::[])
end))))

let args_of_binders = (fun binders -> (let _92_148 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(let b = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _92_143 = (let _92_142 = (gen_bvar a.FStar_Absyn_Syntax.sort)
in FStar_Util.Inl (_92_142))
in (_92_143, (Prims.snd b)))
end
| FStar_Util.Inr (x) -> begin
(let _92_145 = (let _92_144 = (gen_bvar x.FStar_Absyn_Syntax.sort)
in FStar_Util.Inr (_92_144))
in (_92_145, (Prims.snd b)))
end)
in (let _92_146 = (arg_of_non_null_binder b)
in (b, _92_146)))
end else begin
(let _92_147 = (arg_of_non_null_binder b)
in (b, _92_147))
end)))
in (FStar_All.pipe_right _92_148 FStar_List.unzip)))

let name_binders = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(let b = (let _92_154 = (let _92_153 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _92_153))
in (FStar_Absyn_Syntax.id_of_text _92_154))
in (let b = (bvd_to_bvar_s (mkbvd (b, b)) a.FStar_Absyn_Syntax.sort)
in (FStar_Util.Inl (b), imp)))
end
| (FStar_Util.Inr (y), imp) -> begin
(let x = (let _92_156 = (let _92_155 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _92_155))
in (FStar_Absyn_Syntax.id_of_text _92_156))
in (let x = (bvd_to_bvar_s (mkbvd (x, x)) y.FStar_Absyn_Syntax.sort)
in (FStar_Util.Inr (x), imp)))
end)
end else begin
b
end))))

let name_function_binders = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, comp) -> begin
(let _92_160 = (let _92_159 = (name_binders binders)
in (_92_159, comp))
in (FStar_Absyn_Syntax.mk_Typ_fun _92_160 None t.FStar_Absyn_Syntax.pos))
end
| _26_220 -> begin
t
end))

let null_binders_of_tks = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _26_2 -> (match (_26_2) with
| (FStar_Util.Inl (k), imp) -> begin
(let _92_165 = (let _92_164 = (FStar_Absyn_Syntax.null_t_binder k)
in (FStar_All.pipe_left Prims.fst _92_164))
in (_92_165, imp))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _92_167 = (let _92_166 = (FStar_Absyn_Syntax.null_v_binder t)
in (FStar_All.pipe_left Prims.fst _92_166))
in (_92_167, imp))
end)))))

let binders_of_tks = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _26_3 -> (match (_26_3) with
| (FStar_Util.Inl (k), imp) -> begin
(let _92_172 = (let _92_171 = (gen_bvar_p k.FStar_Absyn_Syntax.pos k)
in FStar_Util.Inl (_92_171))
in (_92_172, imp))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _92_174 = (let _92_173 = (gen_bvar_p t.FStar_Absyn_Syntax.pos t)
in FStar_Util.Inr (_92_173))
in (_92_174, imp))
end)))))

let binders_of_freevars = (fun fvs -> (let _92_180 = (let _92_177 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.ftvs)
in (FStar_All.pipe_right _92_177 (FStar_List.map FStar_Absyn_Syntax.t_binder)))
in (let _92_179 = (let _92_178 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_All.pipe_right _92_178 (FStar_List.map FStar_Absyn_Syntax.v_binder)))
in (FStar_List.append _92_180 _92_179))))

let subst_to_string = (fun s -> (let _92_183 = (FStar_All.pipe_right s (FStar_List.map (fun _26_4 -> (match (_26_4) with
| FStar_Util.Inl (b, _26_246) -> begin
b.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText
end
| FStar_Util.Inr (x, _26_251) -> begin
x.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText
end))))
in (FStar_All.pipe_right _92_183 (FStar_String.concat ", "))))

let subst_tvar = (fun s a -> (FStar_Util.find_map s (fun _26_5 -> (match (_26_5) with
| FStar_Util.Inl (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _26_262 -> begin
None
end))))

let subst_xvar = (fun s a -> (FStar_Util.find_map s (fun _26_6 -> (match (_26_6) with
| FStar_Util.Inr (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _26_271 -> begin
None
end))))

let rec subst_typ' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_typ t)
end
| _26_278 -> begin
(let t0 = (FStar_Absyn_Visit.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s'), m) -> begin
(let _92_208 = (let _92_207 = (compose_subst s' s)
in (let _92_206 = (FStar_Util.mk_ref None)
in (t', _92_207, _92_206)))
in (FStar_Absyn_Syntax.mk_Typ_delayed _92_208 None t.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(let t = (mk_t ())
in (let _26_293 = (FStar_ST.op_Colon_Equals m (Some (t)))
in (subst_typ' s t)))
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let rec aux = (fun s' -> (match (s') with
| s0::rest -> begin
(match ((subst_tvar s0 a)) with
| Some (t) -> begin
(subst_typ' rest t)
end
| _26_305 -> begin
(aux rest)
end)
end
| _26_307 -> begin
t0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
t0
end
| _26_316 -> begin
(let _92_213 = (let _92_212 = (FStar_Util.mk_ref None)
in (t0, s, _92_212))
in (FStar_Absyn_Syntax.mk_Typ_delayed _92_213 None t.FStar_Absyn_Syntax.pos))
end))
end))
and subst_exp' = (fun s e -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_exp e)
end
| _26_323 -> begin
(let e0 = (FStar_Absyn_Visit.compress_exp e)
in (match (e0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e, s', m) -> begin
(let _92_218 = (let _92_217 = (compose_subst s' s)
in (let _92_216 = (FStar_Util.mk_ref None)
in (e, _92_217, _92_216)))
in (FStar_Absyn_Syntax.mk_Exp_delayed _92_218 None e.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let rec aux = (fun s -> (match (s) with
| s0::rest -> begin
(match ((subst_xvar s0 x)) with
| Some (e) -> begin
(subst_exp' rest e)
end
| _26_340 -> begin
(aux rest)
end)
end
| _26_342 -> begin
e0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
e0
end
| _26_350 -> begin
(let _92_222 = (let _92_221 = (FStar_Util.mk_ref None)
in (e0, s, _92_221))
in (FStar_Absyn_Syntax.mk_Exp_delayed _92_222 None e0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_kind' = (fun s k -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_kind k)
end
| _26_357 -> begin
(let k0 = (FStar_Absyn_Visit.compress_kind k)
in (match (k0.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
k0
end
| FStar_Absyn_Syntax.Kind_delayed (k, s', m) -> begin
(let _92_227 = (let _92_226 = (compose_subst s' s)
in (let _92_225 = (FStar_Util.mk_ref None)
in (k, _92_226, _92_225)))
in (FStar_Absyn_Syntax.mk_Kind_delayed _92_227 k0.FStar_Absyn_Syntax.pos))
end
| _26_368 -> begin
(let _92_229 = (let _92_228 = (FStar_Util.mk_ref None)
in (k0, s, _92_228))
in (FStar_Absyn_Syntax.mk_Kind_delayed _92_229 k0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_flags' = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _26_7 -> (match (_26_7) with
| FStar_Absyn_Syntax.DECREASES (a) -> begin
(let _92_233 = (subst_exp' s a)
in FStar_Absyn_Syntax.DECREASES (_92_233))
end
| f -> begin
f
end)))))
and subst_comp_typ' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _26_381 -> begin
(let _26_382 = t
in (let _92_243 = (subst_typ' s t.FStar_Absyn_Syntax.result_typ)
in (let _92_242 = (FStar_List.map (fun _26_8 -> (match (_26_8) with
| (FStar_Util.Inl (t), imp) -> begin
(let _92_238 = (let _92_237 = (subst_typ' s t)
in FStar_Util.Inl (_92_237))
in (_92_238, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _92_240 = (let _92_239 = (subst_exp' s e)
in FStar_Util.Inr (_92_239))
in (_92_240, imp))
end)) t.FStar_Absyn_Syntax.effect_args)
in (let _92_241 = (subst_flags' s t.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _26_382.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _92_243; FStar_Absyn_Syntax.effect_args = _92_242; FStar_Absyn_Syntax.flags = _92_241}))))
end))
and subst_comp' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _26_399 -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _92_246 = (subst_typ' s t)
in (FStar_Absyn_Syntax.mk_Total _92_246))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _92_247 = (subst_comp_typ' s ct)
in (FStar_Absyn_Syntax.mk_Comp _92_247))
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
(let _92_275 = (let _92_274 = (let _26_423 = a
in (let _92_273 = (subst_kind s a.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _26_423.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _92_273; FStar_Absyn_Syntax.p = _26_423.FStar_Absyn_Syntax.p}))
in FStar_Util.Inl (_92_274))
in (_92_275, imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _92_278 = (let _92_277 = (let _26_429 = x
in (let _92_276 = (subst_typ s x.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _26_429.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _92_276; FStar_Absyn_Syntax.p = _26_429.FStar_Absyn_Syntax.p}))
in FStar_Util.Inr (_92_277))
in (_92_278, imp))
end))

let subst_arg = (fun s _26_10 -> (match (_26_10) with
| (FStar_Util.Inl (t), imp) -> begin
(let _92_282 = (let _92_281 = (subst_typ s t)
in FStar_Util.Inl (_92_281))
in (_92_282, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _92_284 = (let _92_283 = (subst_exp s e)
in FStar_Util.Inr (_92_283))
in (_92_284, imp))
end))

let subst_binders = (fun s bs -> (match (s) with
| [] -> begin
bs
end
| _26_445 -> begin
(FStar_List.map (subst_binder s) bs)
end))

let subst_args = (fun s args -> (match (s) with
| [] -> begin
args
end
| _26_450 -> begin
(FStar_List.map (subst_arg s) args)
end))

let subst_formal = (fun f a -> (match ((f, a)) with
| ((FStar_Util.Inl (a), _26_456), (FStar_Util.Inl (t), _26_461)) -> begin
FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t))
end
| ((FStar_Util.Inr (x), _26_467), (FStar_Util.Inr (v), _26_472)) -> begin
FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v))
end
| _26_476 -> begin
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
(let _92_299 = (let _92_298 = (let _92_297 = (btvar_to_typ a)
in (b.FStar_Absyn_Syntax.v, _92_297))
in FStar_Util.Inl (_92_298))
in (_92_299)::[])
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (bvar_eq x y) then begin
[]
end else begin
(let _92_302 = (let _92_301 = (let _92_300 = (bvar_to_exp x)
in (y.FStar_Absyn_Syntax.v, _92_300))
in FStar_Util.Inr (_92_301))
in (_92_302)::[])
end
end
| _26_490 -> begin
[]
end)
end)

let mk_subst_binder = (fun bs1 bs2 -> (let rec aux = (fun out bs1 bs2 -> (match ((bs1, bs2)) with
| ([], []) -> begin
Some (out)
end
| (b1::bs1, b2::bs2) -> begin
(let _92_314 = (let _92_313 = (mk_subst_one_binder b1 b2)
in (FStar_List.append _92_313 out))
in (aux _92_314 bs1 bs2))
end
| _26_508 -> begin
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

let map_knd = (fun s vk mt me descend binders k -> (let _92_335 = (subst_kind' s k)
in (_92_335, descend)))

let map_typ = (fun s mk vt me descend binders t -> (let _92_343 = (subst_typ' s t)
in (_92_343, descend)))

let map_exp = (fun s mk me ve descend binders e -> (let _92_351 = (subst_exp' s e)
in (_92_351, descend)))

let map_flags = (fun s map_exp descend binders flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _26_11 -> (match (_26_11) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _92_368 = (let _92_367 = (map_exp descend binders e)
in (FStar_All.pipe_right _92_367 Prims.fst))
in FStar_Absyn_Syntax.DECREASES (_92_368))
end
| f -> begin
f
end)))))

let map_comp = (fun s mk map_typ map_exp descend binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _26_557 = (map_typ descend binders t)
in (match (_26_557) with
| (t, descend) -> begin
(let _92_391 = (FStar_Absyn_Syntax.mk_Total t)
in (_92_391, descend))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _26_562 = (map_typ descend binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_26_562) with
| (t, descend) -> begin
(let _26_565 = (FStar_Absyn_Visit.map_args map_typ map_exp descend binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_26_565) with
| (args, descend) -> begin
(let _92_394 = (let _92_393 = (let _26_566 = ct
in (let _92_392 = (map_flags s map_exp descend binders ct.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _26_566.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _92_392}))
in (FStar_Absyn_Syntax.mk_Comp _92_393))
in (_92_394, descend))
end))
end))
end))

let visit_knd = (fun s vk mt me ctrl binders k -> (let k = (FStar_Absyn_Visit.compress_kind k)
in if ctrl.descend then begin
(let _26_579 = (vk null_ctrl binders k)
in (match (_26_579) with
| (k, _26_578) -> begin
(k, ctrl)
end))
end else begin
(map_knd s vk mt me null_ctrl binders k)
end))

let rec compress_kind = (fun k -> (let k = (FStar_Absyn_Visit.compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (k', s, m) -> begin
(let k' = (let _92_440 = (FStar_Absyn_Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] k')
in (FStar_All.pipe_left Prims.fst _92_440))
in (let k' = (compress_kind k')
in (let _26_589 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k')))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, actuals) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (formals, k') -> begin
(let _92_442 = (let _92_441 = (subst_of_list formals actuals)
in (subst_kind _92_441 k'))
in (compress_kind _92_442))
end
| _26_602 -> begin
if ((FStar_List.length actuals) = 0) then begin
k
end else begin
(FStar_All.failwith "Wrong arity for kind unifier")
end
end)
end
| _26_604 -> begin
k
end)
end
| _26_606 -> begin
k
end)))

let rec visit_typ = (fun s mk vt me ctrl boundvars t -> (let visit_prod = (fun bs tc -> (let _26_667 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _26_620 b -> (match (_26_620) with
| (bs, boundvars, s) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(let _26_629 = (map_knd s mk vt me null_ctrl boundvars a.FStar_Absyn_Syntax.sort)
in (match (_26_629) with
| (k, _26_628) -> begin
(let a = (let _26_630 = a
in {FStar_Absyn_Syntax.v = _26_630.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _26_630.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((FStar_Util.Inl (a), imp))::bs, boundvars, s)
end else begin
(let boundvars' = (FStar_Util.Inl (a.FStar_Absyn_Syntax.v))::boundvars
in (let _26_642 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(FStar_Util.Inl (a), s, boundvars')
end
| _26_636 -> begin
(let b = (let _92_519 = (freshen_bvd a.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _92_519 k))
in (let s = (let _92_522 = (let _92_521 = (let _92_520 = (btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _92_520))
in FStar_Util.Inl (_92_521))
in (extend_subst _92_522 s))
in (FStar_Util.Inl (b), s, (FStar_Util.Inl (b.FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_26_642) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end)
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _26_650 = (map_typ s mk vt me null_ctrl boundvars x.FStar_Absyn_Syntax.sort)
in (match (_26_650) with
| (t, _26_649) -> begin
(let x = (let _26_651 = x
in {FStar_Absyn_Syntax.v = _26_651.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _26_651.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((FStar_Util.Inr (x), imp))::bs, boundvars, s)
end else begin
(let boundvars' = (FStar_Util.Inr (x.FStar_Absyn_Syntax.v))::boundvars
in (let _26_663 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(FStar_Util.Inr (x), s, boundvars')
end
| _26_657 -> begin
(let y = (let _92_532 = (freshen_bvd x.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _92_532 t))
in (let s = (let _92_535 = (let _92_534 = (let _92_533 = (bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _92_533))
in FStar_Util.Inr (_92_534))
in (extend_subst _92_535 s))
in (FStar_Util.Inr (y), s, (FStar_Util.Inr (y.FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_26_663) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end)
end))
end)
end)) ([], boundvars, s)))
in (match (_26_667) with
| (bs, boundvars, s) -> begin
(let tc = (match ((s, tc)) with
| ([], _26_670) -> begin
tc
end
| (_26_673, FStar_Util.Inl (t)) -> begin
(let _92_546 = (let _92_545 = (map_typ s mk vt me null_ctrl boundvars t)
in (FStar_All.pipe_left Prims.fst _92_545))
in FStar_Util.Inl (_92_546))
end
| (_26_678, FStar_Util.Inr (c)) -> begin
(let _92_569 = (let _92_568 = (map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl boundvars c)
in (FStar_All.pipe_left Prims.fst _92_568))
in FStar_Util.Inr (_92_569))
end)
in ((FStar_List.rev bs), tc))
end)))
in (let t0 = t
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_26_685) -> begin
(let _92_571 = (let _92_570 = (subst_typ' s t0)
in (FStar_All.pipe_left compress_typ _92_570))
in (_92_571, ctrl))
end
| _26_688 when (not (ctrl.descend)) -> begin
(map_typ s mk vt me null_ctrl boundvars t)
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((visit_prod bs (FStar_Util.Inr (c)))) with
| (bs, FStar_Util.Inr (c)) -> begin
(let _92_581 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t0.FStar_Absyn_Syntax.pos)
in (_92_581, ctrl))
end
| _26_698 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((visit_prod (((FStar_Util.Inr (x), None))::[]) (FStar_Util.Inl (t)))) with
| ((FStar_Util.Inr (x), _26_706)::[], FStar_Util.Inl (t)) -> begin
(let _92_582 = (FStar_Absyn_Syntax.mk_Typ_refine (x, t) None t0.FStar_Absyn_Syntax.pos)
in (_92_582, ctrl))
end
| _26_713 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(match ((visit_prod bs (FStar_Util.Inl (t)))) with
| (bs, FStar_Util.Inl (t)) -> begin
(let _92_583 = (FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t0.FStar_Absyn_Syntax.pos)
in (_92_583, ctrl))
end
| _26_723 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _26_725 -> begin
(let _26_729 = (vt null_ctrl boundvars t)
in (match (_26_729) with
| (t, _26_728) -> begin
(t, ctrl)
end))
end))))
and compress_typ' = (fun t -> (let t = (FStar_Absyn_Visit.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s), m) -> begin
(let res = (let _92_603 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] t')
in (FStar_All.pipe_left Prims.fst _92_603))
in (let res = (compress_typ' res)
in (let _26_741 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(let t = (let _92_605 = (mk_t ())
in (compress_typ' _92_605))
in (let _26_749 = (FStar_ST.op_Colon_Equals m (Some (t)))
in t))
end
| _26_752 -> begin
t
end)))
and compress_typ = (fun t -> (let t = (compress_typ' t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_26_756) -> begin
(FStar_All.failwith "Impossible: compress returned a delayed type")
end
| _26_759 -> begin
t
end)))

let rec visit_exp = (fun s mk me ve ctrl binders e -> (let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_26_769) -> begin
(let _92_671 = (let _92_670 = (subst_exp' s e)
in (FStar_All.pipe_left compress_exp _92_670))
in (_92_671, ctrl))
end
| _26_772 when (not (ctrl.descend)) -> begin
(map_exp s mk me ve ctrl binders e)
end
| _26_774 -> begin
(let _26_778 = (ve null_ctrl binders e)
in (match (_26_778) with
| (e, _26_777) -> begin
(e, ctrl)
end))
end)))
and compress_exp = (fun e -> (let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e', s, m) -> begin
(let e = (let _92_700 = (FStar_Absyn_Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] e')
in (FStar_All.pipe_left Prims.fst _92_700))
in (let res = (compress_exp e)
in (let _26_788 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| _26_791 -> begin
e
end)))

let rec unmeta_exp = (fun e -> (let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _26_796)) -> begin
(unmeta_exp e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _26_802, _26_804) -> begin
(unmeta_exp e)
end
| _26_808 -> begin
e
end)))

let alpha_typ = (fun t -> (let t = (compress_typ t)
in (let s = (mk_subst [])
in (let doit = (fun t -> (let _92_725 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp alpha_ctrl [] t)
in (FStar_All.pipe_left Prims.fst _92_725)))
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_lam (bs, _)) | (FStar_Absyn_Syntax.Typ_fun (bs, _)) -> begin
if (FStar_Util.for_all FStar_Absyn_Syntax.is_null_binder bs) then begin
t
end else begin
(doit t)
end
end
| FStar_Absyn_Syntax.Typ_refine (_26_824) -> begin
(doit t)
end
| _26_827 -> begin
t
end)))))

let formals_for_actuals = (fun formals actuals -> (FStar_List.map2 (fun formal actual -> (match (((Prims.fst formal), (Prims.fst actual))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, b))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, y))
end
| _26_843 -> begin
(FStar_All.failwith "Ill-typed substitution")
end)) formals actuals))

let compress_typ_opt = (fun _26_12 -> (match (_26_12) with
| None -> begin
None
end
| Some (t) -> begin
(let _92_732 = (compress_typ t)
in Some (_92_732))
end))

let mk_discriminator = (fun lid -> (let _92_737 = (let _92_736 = (let _92_735 = (FStar_Absyn_Syntax.mk_ident ((Prims.strcat "is_" lid.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText), lid.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idRange))
in (_92_735)::[])
in (FStar_List.append lid.FStar_Absyn_Syntax.ns _92_736))
in (FStar_Absyn_Syntax.lid_of_ids _92_737)))

let is_name = (fun lid -> (let c = (FStar_Util.char_at lid.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText 0)
in (FStar_Util.is_upper c)))

let ml_comp = (fun t r -> (let _92_745 = (let _92_744 = (set_lid_range FStar_Absyn_Const.effect_ML_lid r)
in {FStar_Absyn_Syntax.effect_name = _92_744; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.MLEFFECT)::[]})
in (FStar_Absyn_Syntax.mk_Comp _92_745)))

let total_comp = (fun t r -> (FStar_Absyn_Syntax.mk_Total t))

let gtotal_comp = (fun t -> (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_GTot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.SOMETRIVIAL)::[]}))

let comp_set_flags = (fun c f -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_26_859) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _26_863 = c
in {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp ((let _26_865 = ct
in {FStar_Absyn_Syntax.effect_name = _26_865.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _26_865.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _26_865.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = f})); FStar_Absyn_Syntax.tk = _26_863.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _26_863.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _26_863.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _26_863.FStar_Absyn_Syntax.uvs})
end))

let comp_flags = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_26_869) -> begin
(FStar_Absyn_Syntax.TOTAL)::[]
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
ct.FStar_Absyn_Syntax.flags
end))

let comp_effect_name = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c.FStar_Absyn_Syntax.effect_name
end
| FStar_Absyn_Syntax.Total (_26_877) -> begin
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
| _26_889 -> begin
false
end)))))

let is_total_lcomp = (fun c -> ((FStar_Absyn_Syntax.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _26_14 -> (match (_26_14) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _26_895 -> begin
false
end))))))

let is_tot_or_gtot_lcomp = (fun c -> (((FStar_Absyn_Syntax.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_Absyn_Syntax.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _26_15 -> (match (_26_15) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _26_901 -> begin
false
end))))))

let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _26_16 -> (match (_26_16) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _26_907 -> begin
false
end)))))

let is_lcomp_partial_return = (fun c -> (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _26_17 -> (match (_26_17) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _26_913 -> begin
false
end)))))

let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Absyn_Syntax.lid_equals FStar_Absyn_Const.effect_GTot_lid (comp_effect_name c))))

let is_pure_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_26_917) -> begin
true
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
((((is_tot_or_gtot_comp c) || (FStar_Absyn_Syntax.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Absyn_Syntax.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _26_18 -> (match (_26_18) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _26_924 -> begin
false
end)))))
end))

let is_ghost_effect = (fun l -> (((FStar_Absyn_Syntax.lid_equals FStar_Absyn_Const.effect_GTot_lid l) || (FStar_Absyn_Syntax.lid_equals FStar_Absyn_Const.effect_GHOST_lid l)) || (FStar_Absyn_Syntax.lid_equals FStar_Absyn_Const.effect_Ghost_lid l)))

let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))

let is_pure_lcomp = (fun lc -> ((((is_total_lcomp lc) || (FStar_Absyn_Syntax.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Absyn_Syntax.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _26_19 -> (match (_26_19) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _26_931 -> begin
false
end))))))

let is_pure_or_ghost_lcomp = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Absyn_Syntax.eff_name)))

let is_pure_or_ghost_function = (fun t -> (match ((let _92_784 = (compress_typ t)
in _92_784.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_26_935, c) -> begin
(is_pure_or_ghost_comp c)
end
| _26_940 -> begin
true
end))

let is_lemma = (fun t -> (match ((let _92_787 = (compress_typ t)
in _92_787.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_26_943, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Absyn_Syntax.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid)
end
| _26_950 -> begin
false
end)
end
| _26_952 -> begin
false
end))

let is_smt_lemma = (fun t -> (match ((let _92_790 = (compress_typ t)
in _92_790.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_26_955, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) when (FStar_Absyn_Syntax.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| _req::_ens::(FStar_Util.Inr (pats), _26_966)::_26_962 -> begin
(match ((let _92_791 = (unmeta_exp pats)
in _92_791.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _26_983); FStar_Absyn_Syntax.tk = _26_980; FStar_Absyn_Syntax.pos = _26_978; FStar_Absyn_Syntax.fvs = _26_976; FStar_Absyn_Syntax.uvs = _26_974}, _26_988) -> begin
(FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid)
end
| _26_992 -> begin
false
end)
end
| _26_994 -> begin
false
end)
end
| _26_996 -> begin
false
end)
end
| _26_998 -> begin
false
end))

let is_ml_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
((FStar_Absyn_Syntax.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _26_20 -> (match (_26_20) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _26_1005 -> begin
false
end)))))
end
| _26_1007 -> begin
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
| FStar_Absyn_Syntax.Total (_26_1016) -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Absyn_Syntax.mk_Comp (let _26_1020 = ct
in {FStar_Absyn_Syntax.effect_name = _26_1020.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = _26_1020.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = _26_1020.FStar_Absyn_Syntax.flags}))
end))

let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _26_21 -> (match (_26_21) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _26_1027 -> begin
false
end)))))

let rec is_atom = (fun e -> (match ((let _92_801 = (compress_exp e)
in _92_801.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _26_1040)) -> begin
(is_atom e)
end
| _26_1045 -> begin
false
end))

let primops = (FStar_Absyn_Const.op_Eq)::(FStar_Absyn_Const.op_notEq)::(FStar_Absyn_Const.op_LT)::(FStar_Absyn_Const.op_LTE)::(FStar_Absyn_Const.op_GT)::(FStar_Absyn_Const.op_GTE)::(FStar_Absyn_Const.op_Subtraction)::(FStar_Absyn_Const.op_Minus)::(FStar_Absyn_Const.op_Addition)::(FStar_Absyn_Const.op_Multiply)::(FStar_Absyn_Const.op_Division)::(FStar_Absyn_Const.op_Modulus)::(FStar_Absyn_Const.op_And)::(FStar_Absyn_Const.op_Or)::(FStar_Absyn_Const.op_Negation)::[]

let is_primop = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _26_1049) -> begin
(FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _26_1053 -> begin
false
end))

let rec unascribe = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_ascribed (e, _26_1057, _26_1059) -> begin
(unascribe e)
end
| _26_1063 -> begin
e
end))

let rec ascribe_typ = (fun t k -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t', _26_1068) -> begin
(ascribe_typ t' k)
end
| _26_1072 -> begin
(FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.FStar_Absyn_Syntax.pos)
end))

let rec unascribe_typ = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t, _26_1076) -> begin
(unascribe_typ t)
end
| _26_1080 -> begin
t
end))

let rec unrefine = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _26_1085) -> begin
(unrefine x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _26_1090) -> begin
(unrefine t)
end
| _26_1094 -> begin
t
end)))

let is_fun = (fun e -> (match ((let _92_815 = (compress_exp e)
in _92_815.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (_26_1097) -> begin
true
end
| _26_1100 -> begin
false
end))

let is_function_typ = (fun t -> (match ((let _92_818 = (compress_typ t)
in _92_818.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_26_1103) -> begin
true
end
| _26_1106 -> begin
false
end))

let rec pre_typ = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _26_1111) -> begin
(pre_typ x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _26_1116) -> begin
(pre_typ t)
end
| _26_1120 -> begin
t
end)))

let destruct = (fun typ lid -> (let typ = (compress_typ typ)
in (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _26_1131; FStar_Absyn_Syntax.pos = _26_1129; FStar_Absyn_Syntax.fvs = _26_1127; FStar_Absyn_Syntax.uvs = _26_1125}, args) when (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some (args)
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some ([])
end
| _26_1141 -> begin
None
end)))

let rec lids_of_sigelt = (fun se -> (match (se) with
| (FStar_Absyn_Syntax.Sig_let (_, _, lids, _)) | (FStar_Absyn_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Absyn_Syntax.Sig_tycon (lid, _, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_datacon (lid, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_val_decl (lid, _, _, _)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (lid, _, _, _)) | (FStar_Absyn_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| FStar_Absyn_Syntax.Sig_new_effect (n, _26_1235) -> begin
(n.FStar_Absyn_Syntax.mname)::[]
end
| (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) -> begin
[]
end))

let lid_of_sigelt = (fun se -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _26_1251 -> begin
None
end))

let range_of_sigelt = (fun x -> (match (x) with
| (FStar_Absyn_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_datacon (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_val_decl (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_assume (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_let (_, r, _, _)) | (FStar_Absyn_Syntax.Sig_main (_, r)) | (FStar_Absyn_Syntax.Sig_pragma (_, r)) | (FStar_Absyn_Syntax.Sig_new_effect (_, r)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))

let range_of_lb = (fun _26_22 -> (match (_26_22) with
| (FStar_Util.Inl (x), _26_1362, _26_1364) -> begin
(range_of_bvd x)
end
| (FStar_Util.Inr (l), _26_1369, _26_1371) -> begin
(FStar_Absyn_Syntax.range_of_lid l)
end))

let range_of_arg = (fun _26_23 -> (match (_26_23) with
| (FStar_Util.Inl (hd), _26_1377) -> begin
hd.FStar_Absyn_Syntax.pos
end
| (FStar_Util.Inr (hd), _26_1382) -> begin
hd.FStar_Absyn_Syntax.pos
end))

let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))

let mk_typ_app = (fun f args -> (let r = (range_of_args args f.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (f, args) None r)))

let mk_exp_app = (fun f args -> (let r = (range_of_args args f.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Exp_app (f, args) None r)))

let mk_data = (fun l args -> (match (args) with
| [] -> begin
(let _92_852 = (let _92_851 = (let _92_850 = (let _92_849 = (FStar_Absyn_Syntax.range_of_lid l)
in (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l _92_849))
in (_92_850, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_92_851))
in (FStar_Absyn_Syntax.mk_Exp_meta _92_852))
end
| _26_1398 -> begin
(let _92_857 = (let _92_856 = (let _92_855 = (let _92_854 = (let _92_853 = (FStar_Absyn_Syntax.range_of_lid l)
in (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l _92_853))
in (mk_exp_app _92_854 args))
in (_92_855, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_92_856))
in (FStar_Absyn_Syntax.mk_Exp_meta _92_857))
end))

let mangle_field_name = (fun x -> (FStar_Absyn_Syntax.mk_ident ((Prims.strcat "^fname^" x.FStar_Absyn_Syntax.idText), x.FStar_Absyn_Syntax.idRange)))

let unmangle_field_name = (fun x -> if (FStar_Util.starts_with x.FStar_Absyn_Syntax.idText "^fname^") then begin
(let _92_863 = (let _92_862 = (FStar_Util.substring_from x.FStar_Absyn_Syntax.idText 7)
in (_92_862, x.FStar_Absyn_Syntax.idRange))
in (FStar_Absyn_Syntax.mk_ident _92_863))
end else begin
x
end)

let mk_field_projector_name = (fun lid x i -> (let nm = if (FStar_Absyn_Syntax.is_null_bvar x) then begin
(let _92_869 = (let _92_868 = (let _92_867 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _92_867))
in (_92_868, x.FStar_Absyn_Syntax.p))
in (FStar_Absyn_Syntax.mk_ident _92_869))
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (let y = (let _26_1407 = x.FStar_Absyn_Syntax.v
in {FStar_Absyn_Syntax.ppname = nm; FStar_Absyn_Syntax.realname = _26_1407.FStar_Absyn_Syntax.realname})
in (let _92_874 = (let _92_873 = (let _92_872 = (FStar_Absyn_Syntax.ids_of_lid lid)
in (let _92_871 = (let _92_870 = (unmangle_field_name nm)
in (_92_870)::[])
in (FStar_List.append _92_872 _92_871)))
in (FStar_Absyn_Syntax.lid_of_ids _92_873))
in (_92_874, y)))))

let unchecked_unify = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (_26_1413) -> begin
(let _92_879 = (let _92_878 = (let _92_877 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _92_877))
in (FStar_Util.format1 "Changing a fixed uvar! U%s\n" _92_878))
in (FStar_All.failwith _92_879))
end
| _26_1416 -> begin
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
| _26_1432 -> begin
false
end))

let eq_binder = (fun b1 b2 -> (match (((Prims.fst b1), (Prims.fst b2))) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| _26_1446 -> begin
false
end))

let uv_eq = (fun _26_1450 _26_1454 -> (match ((_26_1450, _26_1454)) with
| ((uv1, _26_1449), (uv2, _26_1453)) -> begin
(FStar_Unionfind.equivalent uv1 uv2)
end))

let union_uvs = (fun uvs1 uvs2 -> (let _92_908 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_k uvs2.FStar_Absyn_Syntax.uvars_k)
in (let _92_907 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_t uvs2.FStar_Absyn_Syntax.uvars_t)
in (let _92_906 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_e uvs2.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _92_908; FStar_Absyn_Syntax.uvars_t = _92_907; FStar_Absyn_Syntax.uvars_e = _92_906}))))

let union_fvs = (fun fvs1 fvs2 -> (let _92_914 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs)
in (let _92_913 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)
in {FStar_Absyn_Syntax.ftvs = _92_914; FStar_Absyn_Syntax.fxvs = _92_913})))

let union_fvs_uvs = (fun _26_1461 _26_1464 -> (match ((_26_1461, _26_1464)) with
| ((fvs1, uvs1), (fvs2, uvs2)) -> begin
(let _92_920 = (union_fvs fvs1 fvs2)
in (let _92_919 = (union_uvs uvs1 uvs2)
in (_92_920, _92_919)))
end))

let sub_fv = (fun _26_1467 _26_1470 -> (match ((_26_1467, _26_1470)) with
| ((fvs, uvs), (tvars, vvars)) -> begin
(let _92_941 = (let _26_1471 = fvs
in (let _92_940 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.ftvs tvars)
in (let _92_939 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.fxvs vvars)
in {FStar_Absyn_Syntax.ftvs = _92_940; FStar_Absyn_Syntax.fxvs = _92_939})))
in (_92_941, uvs))
end))

let stash = (fun uvonly s _26_1479 -> (match (_26_1479) with
| (fvs, uvs) -> begin
(let _26_1480 = (FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.uvs (Some (uvs)))
in if uvonly then begin
()
end else begin
(FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.fvs (Some (fvs)))
end)
end))

let single_fv = (fun x -> (let _92_952 = (FStar_Absyn_Syntax.new_ftv_set ())
in (FStar_Util.set_add x _92_952)))

let single_uv = (fun u -> (let _92_960 = (FStar_Absyn_Syntax.new_uv_set ())
in (FStar_Util.set_add u _92_960)))

let single_uvt = (fun u -> (let _92_968 = (FStar_Absyn_Syntax.new_uvt_set ())
in (FStar_Util.set_add u _92_968)))

let rec vs_typ' = (fun t uvonly cont -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_26_1491) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end else begin
(let _92_1083 = (let _92_1082 = (let _26_1495 = FStar_Absyn_Syntax.no_fvs
in (let _92_1081 = (single_fv a)
in {FStar_Absyn_Syntax.ftvs = _92_1081; FStar_Absyn_Syntax.fxvs = _26_1495.FStar_Absyn_Syntax.fxvs}))
in (_92_1082, FStar_Absyn_Syntax.no_uvs))
in (cont _92_1083))
end
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let _92_1086 = (let _92_1085 = (let _26_1501 = FStar_Absyn_Syntax.no_uvs
in (let _92_1084 = (single_uvt (uv, k))
in {FStar_Absyn_Syntax.uvars_k = _26_1501.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _92_1084; FStar_Absyn_Syntax.uvars_e = _26_1501.FStar_Absyn_Syntax.uvars_e}))
in (FStar_Absyn_Syntax.no_fvs, _92_1085))
in (cont _92_1086))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(vs_binders bs uvonly (fun _26_1513 -> (match (_26_1513) with
| (bvs, vs1) -> begin
(vs_comp c uvonly (fun vs2 -> (let _92_1090 = (let _92_1089 = (union_fvs_uvs vs1 vs2)
in (sub_fv _92_1089 bvs))
in (cont _92_1090))))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(vs_binders bs uvonly (fun _26_1521 -> (match (_26_1521) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _92_1094 = (let _92_1093 = (union_fvs_uvs vs1 vs2)
in (sub_fv _92_1093 bvs))
in (cont _92_1094))))
end)))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(vs_binders (((FStar_Util.Inr (x), None))::[]) uvonly (fun _26_1529 -> (match (_26_1529) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _92_1098 = (let _92_1097 = (union_fvs_uvs vs1 vs2)
in (sub_fv _92_1097 bvs))
in (cont _92_1098))))
end)))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(vs_typ t uvonly (fun vs1 -> (vs_args args uvonly (fun vs2 -> (let _92_1101 = (union_fvs_uvs vs1 vs2)
in (cont _92_1101))))))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _26_1539) -> begin
(vs_typ t uvonly cont)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _26_1545)) -> begin
(vs_typ t1 uvonly (fun vs1 -> (vs_typ t2 uvonly (fun vs2 -> (let _92_1104 = (union_fvs_uvs vs1 vs2)
in (cont _92_1104))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) -> begin
(vs_typ t uvonly cont)
end)))
and vs_binders = (fun bs uvonly cont -> (match (bs) with
| [] -> begin
(cont (no_bvars, (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs)))
end
| (FStar_Util.Inl (a), _26_1587)::rest -> begin
(vs_kind a.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _26_1595 -> (match (_26_1595) with
| ((tvars, vvars), vs2) -> begin
(let _92_1141 = (let _92_1140 = (let _92_1138 = (FStar_Util.set_add a tvars)
in (_92_1138, vvars))
in (let _92_1139 = (union_fvs_uvs vs vs2)
in (_92_1140, _92_1139)))
in (cont _92_1141))
end)))))
end
| (FStar_Util.Inr (x), _26_1600)::rest -> begin
(vs_typ x.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _26_1608 -> (match (_26_1608) with
| ((tvars, vvars), vs2) -> begin
(let _92_1165 = (let _92_1164 = (let _92_1162 = (FStar_Util.set_add x vvars)
in (tvars, _92_1162))
in (let _92_1163 = (union_fvs_uvs vs vs2)
in (_92_1164, _92_1163)))
in (cont _92_1165))
end)))))
end))
and vs_args = (fun args uvonly cont -> (match (args) with
| [] -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| (FStar_Util.Inl (t), _26_1618)::tl -> begin
(vs_typ t uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _92_1169 = (union_fvs_uvs ft1 ft2)
in (cont _92_1169))))))
end
| (FStar_Util.Inr (e), _26_1627)::tl -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _92_1172 = (union_fvs_uvs ft1 ft2)
in (cont _92_1172))))))
end))
and vs_typ = (fun t uvonly cont -> (match ((let _92_1175 = (FStar_ST.read t.FStar_Absyn_Syntax.fvs)
in (let _92_1174 = (FStar_ST.read t.FStar_Absyn_Syntax.uvs)
in (_92_1175, _92_1174)))) with
| (Some (_26_1637), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_typ' t uvonly (fun fvs -> (let _26_1645 = (stash uvonly t fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_typ' t uvonly (fun fvs -> (let _26_1652 = (stash uvonly t fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_kind' = (fun k uvonly cont -> (let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_26_1665, k) -> begin
(let _92_1180 = (let _92_1179 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "%s: Impossible ... found a Kind_lam bare" _92_1179))
in (FStar_All.failwith _92_1180))
end
| FStar_Absyn_Syntax.Kind_delayed (_26_1670) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(vs_args args uvonly (fun _26_1681 -> (match (_26_1681) with
| (fvs, uvs) -> begin
(let _92_1184 = (let _92_1183 = (let _26_1682 = uvs
in (let _92_1182 = (FStar_Util.set_add uv uvs.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _92_1182; FStar_Absyn_Syntax.uvars_t = _26_1682.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _26_1682.FStar_Absyn_Syntax.uvars_e}))
in (fvs, _92_1183))
in (cont _92_1184))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev (_26_1685, k) -> begin
(vs_kind k uvonly cont)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(vs_binders bs uvonly (fun _26_1695 -> (match (_26_1695) with
| (bvs, vs1) -> begin
(vs_kind k uvonly (fun vs2 -> (let _92_1188 = (let _92_1187 = (union_fvs_uvs vs1 vs2)
in (sub_fv _92_1187 bvs))
in (cont _92_1188))))
end)))
end)))
and vs_kind = (fun k uvonly cont -> (match ((let _92_1191 = (FStar_ST.read k.FStar_Absyn_Syntax.fvs)
in (let _92_1190 = (FStar_ST.read k.FStar_Absyn_Syntax.uvs)
in (_92_1191, _92_1190)))) with
| (Some (_26_1702), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_kind' k uvonly (fun fvs -> (let _26_1710 = (stash uvonly k fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_kind' k uvonly (fun fvs -> (let _26_1717 = (stash uvonly k fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_exp' = (fun e uvonly cont -> (let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_26_1730) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(let _92_1197 = (let _92_1196 = (let _26_1742 = FStar_Absyn_Syntax.no_uvs
in (let _92_1195 = (single_uvt (uv, t))
in {FStar_Absyn_Syntax.uvars_k = _26_1742.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _26_1742.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _92_1195}))
in (FStar_Absyn_Syntax.no_fvs, _92_1196))
in (cont _92_1197))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end else begin
(let _92_1200 = (let _92_1199 = (let _26_1746 = FStar_Absyn_Syntax.no_fvs
in (let _92_1198 = (single_fv x)
in {FStar_Absyn_Syntax.ftvs = _26_1746.FStar_Absyn_Syntax.ftvs; FStar_Absyn_Syntax.fxvs = _92_1198}))
in (_92_1199, FStar_Absyn_Syntax.no_uvs))
in (cont _92_1200))
end
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _26_1750, _26_1752) -> begin
(vs_exp e uvonly cont)
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(vs_binders bs uvonly (fun _26_1761 -> (match (_26_1761) with
| (bvs, vs1) -> begin
(vs_exp e uvonly (fun vs2 -> (let _92_1204 = (let _92_1203 = (union_fvs_uvs vs1 vs2)
in (sub_fv _92_1203 bvs))
in (cont _92_1204))))
end)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args args uvonly (fun ft2 -> (let _92_1207 = (union_fvs_uvs ft1 ft2)
in (cont _92_1207))))))
end
| (FStar_Absyn_Syntax.Exp_match (_)) | (FStar_Absyn_Syntax.Exp_let (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _26_1777)) -> begin
(vs_exp e uvonly cont)
end)))
and vs_exp = (fun e uvonly cont -> (match ((let _92_1210 = (FStar_ST.read e.FStar_Absyn_Syntax.fvs)
in (let _92_1209 = (FStar_ST.read e.FStar_Absyn_Syntax.uvs)
in (_92_1210, _92_1209)))) with
| (Some (_26_1786), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_exp' e uvonly (fun fvs -> (let _26_1794 = (stash uvonly e fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_exp' e uvonly (fun fvs -> (let _26_1801 = (stash uvonly e fvs)
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
(vs_typ ct.FStar_Absyn_Syntax.result_typ uvonly (fun vs1 -> (vs_args ct.FStar_Absyn_Syntax.effect_args uvonly (fun vs2 -> (let _92_1216 = (union_fvs_uvs vs1 vs2)
in (k _92_1216))))))
end
end))
and vs_comp = (fun c uvonly cont -> (match ((let _92_1219 = (FStar_ST.read c.FStar_Absyn_Syntax.fvs)
in (let _92_1218 = (FStar_ST.read c.FStar_Absyn_Syntax.uvs)
in (_92_1219, _92_1218)))) with
| (Some (_26_1823), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_comp' c uvonly (fun fvs -> (let _26_1831 = (stash uvonly c fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_comp' c uvonly (fun fvs -> (let _26_1838 = (stash uvonly c fvs)
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
(vs_either hd uvonly (fun ft1 -> (vs_either_l tl uvonly (fun ft2 -> (let _92_1226 = (union_fvs_uvs ft1 ft2)
in (cont _92_1226))))))
end))

let freevars_kind = (fun k -> (vs_kind k false (fun _26_1867 -> (match (_26_1867) with
| (x, _26_1866) -> begin
x
end))))

let freevars_typ = (fun t -> (vs_typ t false (fun _26_1872 -> (match (_26_1872) with
| (x, _26_1871) -> begin
x
end))))

let freevars_exp = (fun e -> (vs_exp e false (fun _26_1877 -> (match (_26_1877) with
| (x, _26_1876) -> begin
x
end))))

let freevars_comp = (fun c -> (vs_comp c false (fun _26_1882 -> (match (_26_1882) with
| (x, _26_1881) -> begin
x
end))))

let freevars_args = (fun args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(let _92_1242 = (freevars_typ t)
in (FStar_All.pipe_left (union_fvs out) _92_1242))
end
| FStar_Util.Inr (e) -> begin
(let _92_1243 = (freevars_exp e)
in (FStar_All.pipe_left (union_fvs out) _92_1243))
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
| SynSumKind (_26_1899) -> begin
_26_1899
end))

let ___SynSumType____0 = (fun projectee -> (match (projectee) with
| SynSumType (_26_1902) -> begin
_26_1902
end))

let ___SynSumExp____0 = (fun projectee -> (match (projectee) with
| SynSumExp (_26_1905) -> begin
_26_1905
end))

let ___SynSumComp____0 = (fun projectee -> (match (projectee) with
| SynSumComp (_26_1908) -> begin
_26_1908
end))

let rec update_uvars = (fun s uvs -> (let out = (let _92_1317 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_k)
in (FStar_All.pipe_right _92_1317 (FStar_List.fold_left (fun out u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(let _92_1315 = (uvars_in_kind k)
in (union_uvs _92_1315 out))
end
| _26_1916 -> begin
(let _26_1917 = out
in (let _92_1316 = (FStar_Util.set_add u out.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _92_1316; FStar_Absyn_Syntax.uvars_t = _26_1917.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _26_1917.FStar_Absyn_Syntax.uvars_e}))
end)) FStar_Absyn_Syntax.no_uvs)))
in (let out = (let _92_1322 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _92_1322 (FStar_List.fold_left (fun out _26_1923 -> (match (_26_1923) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (t) -> begin
(let _92_1320 = (uvars_in_typ t)
in (union_uvs _92_1320 out))
end
| _26_1927 -> begin
(let _26_1928 = out
in (let _92_1321 = (FStar_Util.set_add (u, t) out.FStar_Absyn_Syntax.uvars_t)
in {FStar_Absyn_Syntax.uvars_k = _26_1928.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _92_1321; FStar_Absyn_Syntax.uvars_e = _26_1928.FStar_Absyn_Syntax.uvars_e}))
end)
end)) out)))
in (let out = (let _92_1327 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_e)
in (FStar_All.pipe_right _92_1327 (FStar_List.fold_left (fun out _26_1934 -> (match (_26_1934) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(let _92_1325 = (uvars_in_exp e)
in (union_uvs _92_1325 out))
end
| _26_1938 -> begin
(let _26_1939 = out
in (let _92_1326 = (FStar_Util.set_add (u, t) out.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _26_1939.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _26_1939.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _92_1326}))
end)
end)) out)))
in (let _26_1950 = (match (s) with
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
and uvars_in_kind = (fun k -> (let _92_1330 = (vs_kind k true (fun _26_1956 -> (match (_26_1956) with
| (_26_1954, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumKind (k))) _92_1330)))
and uvars_in_typ = (fun t -> (let _92_1333 = (vs_typ t true (fun _26_1961 -> (match (_26_1961) with
| (_26_1959, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumType (t))) _92_1333)))
and uvars_in_exp = (fun e -> (let _92_1336 = (vs_exp e true (fun _26_1966 -> (match (_26_1966) with
| (_26_1964, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumExp (e))) _92_1336)))
and uvars_in_comp = (fun c -> (let _92_1339 = (vs_comp c true (fun _26_1971 -> (match (_26_1971) with
| (_26_1969, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumComp (c))) _92_1339)))

let uvars_included_in = (fun u1 u2 -> (((FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_k u2.FStar_Absyn_Syntax.uvars_k) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_t u2.FStar_Absyn_Syntax.uvars_t)) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_e u2.FStar_Absyn_Syntax.uvars_e)))

let rec kind_formals = (fun k -> (let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_26_1977) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
([], k)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _26_1991 = (kind_formals k)
in (match (_26_1991) with
| (bs', k) -> begin
((FStar_List.append bs bs'), k)
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_26_1993, k) -> begin
(kind_formals k)
end
| FStar_Absyn_Syntax.Kind_delayed (_26_1998) -> begin
(FStar_All.failwith "Impossible")
end)))

let close_for_kind = (fun t k -> (let _26_2005 = (kind_formals k)
in (match (_26_2005) with
| (bs, _26_2004) -> begin
(match (bs) with
| [] -> begin
t
end
| _26_2008 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.FStar_Absyn_Syntax.pos)
end)
end)))

let rec unabbreviate_kind = (fun k -> (let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_abbrev (_26_2012, k) -> begin
(unabbreviate_kind k)
end
| _26_2017 -> begin
k
end)))

let close_with_lam = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _26_2022 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (tps, t) None t.FStar_Absyn_Syntax.pos)
end))

let close_with_arrow = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _26_2027 -> begin
(let _26_2036 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
((FStar_List.append tps bs'), c)
end
| _26_2033 -> begin
(let _92_1360 = (FStar_Absyn_Syntax.mk_Total t)
in (tps, _92_1360))
end)
in (match (_26_2036) with
| (bs, c) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.FStar_Absyn_Syntax.pos)
end))
end))

let close_typ = close_with_arrow

let close_kind = (fun tps k -> (match (tps) with
| [] -> begin
k
end
| _26_2041 -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow' (tps, k) k.FStar_Absyn_Syntax.pos)
end))

let is_tuple_constructor = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str "Prims.Tuple")
end
| _26_2046 -> begin
false
end))

let mk_tuple_lid = (fun n r -> (let t = (let _92_1373 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Tuple%s" _92_1373))
in (let _92_1374 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _92_1374 r))))

let mk_tuple_data_lid = (fun n r -> (let t = (let _92_1379 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkTuple%s" _92_1379))
in (let _92_1380 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _92_1380 r))))

let is_tuple_data_lid = (fun f n -> (let _92_1385 = (mk_tuple_data_lid n FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.lid_equals f _92_1385)))

let is_dtuple_constructor = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str "Prims.DTuple")
end
| _26_2059 -> begin
false
end))

let mk_dtuple_lid = (fun n r -> (let t = (let _92_1392 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "DTuple%s" _92_1392))
in (let _92_1393 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _92_1393 r))))

let mk_dtuple_data_lid = (fun n r -> (let t = (let _92_1398 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkDTuple%s" _92_1398))
in (let _92_1399 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _92_1399 r))))

let is_lid_equality = (fun x -> ((((FStar_Absyn_Syntax.lid_equals x FStar_Absyn_Const.eq_lid) || (FStar_Absyn_Syntax.lid_equals x FStar_Absyn_Const.eq2_lid)) || (FStar_Absyn_Syntax.lid_equals x FStar_Absyn_Const.eqA_lid)) || (FStar_Absyn_Syntax.lid_equals x FStar_Absyn_Const.eqT_lid)))

let is_forall = (fun lid -> ((FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.forall_lid) || (FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.allTyp_lid)))

let is_exists = (fun lid -> ((FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.exists_lid) || (FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.exTyp_lid)))

let is_qlid = (fun lid -> ((is_forall lid) || (is_exists lid)))

let is_equality = (fun x -> (is_lid_equality x.FStar_Absyn_Syntax.v))

let lid_is_connective = (let lst = (FStar_Absyn_Const.and_lid)::(FStar_Absyn_Const.or_lid)::(FStar_Absyn_Const.not_lid)::(FStar_Absyn_Const.iff_lid)::(FStar_Absyn_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Absyn_Syntax.lid_equals lid) lst)))

let is_constructor = (fun t lid -> (match ((let _92_1415 = (pre_typ t)
in _92_1415.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
(FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v lid)
end
| _26_2078 -> begin
false
end))

let rec is_constructed_typ = (fun t lid -> (match ((let _92_1420 = (pre_typ t)
in _92_1420.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (_26_2082) -> begin
(is_constructor t lid)
end
| FStar_Absyn_Syntax.Typ_app (t, _26_2086) -> begin
(is_constructed_typ t lid)
end
| _26_2090 -> begin
false
end))

let rec get_tycon = (fun t -> (let t = (pre_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
Some (t)
end
| FStar_Absyn_Syntax.Typ_app (t, _26_2101) -> begin
(get_tycon t)
end
| _26_2105 -> begin
None
end)))

let base_kind = (fun _26_25 -> (match (_26_25) with
| FStar_Absyn_Syntax.Kind_type -> begin
true
end
| _26_2109 -> begin
false
end))

let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _26_2115 _26_2119 -> (match ((_26_2115, _26_2119)) with
| ((fn1, _26_2114), (fn2, _26_2118)) -> begin
(let _92_1429 = (FStar_Absyn_Syntax.text_of_lid fn1)
in (let _92_1428 = (FStar_Absyn_Syntax.text_of_lid fn2)
in (FStar_String.compare _92_1429 _92_1428)))
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

let b2t_v = (let _92_1433 = (let _92_1432 = (let _92_1431 = (let _92_1430 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder t_bool)
in (_92_1430)::[])
in (_92_1431, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _92_1432 FStar_Absyn_Syntax.dummyRange))
in (ftv FStar_Absyn_Const.b2t_lid _92_1433))

let mk_conj_opt = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _92_1444 = (let _92_1443 = (let _92_1441 = (let _92_1440 = (FStar_Absyn_Syntax.targ phi1)
in (let _92_1439 = (let _92_1438 = (FStar_Absyn_Syntax.targ phi2)
in (_92_1438)::[])
in (_92_1440)::_92_1439))
in (tand, _92_1441))
in (let _92_1442 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _92_1443 None _92_1442)))
in Some (_92_1444))
end))

let mk_binop = (fun op_t phi1 phi2 -> (let _92_1456 = (let _92_1454 = (let _92_1453 = (FStar_Absyn_Syntax.targ phi1)
in (let _92_1452 = (let _92_1451 = (FStar_Absyn_Syntax.targ phi2)
in (_92_1451)::[])
in (_92_1453)::_92_1452))
in (op_t, _92_1454))
in (let _92_1455 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _92_1456 None _92_1455))))

let mk_neg = (fun phi -> (let _92_1462 = (let _92_1461 = (ftv FStar_Absyn_Const.not_lid kt_kt)
in (let _92_1460 = (let _92_1459 = (FStar_Absyn_Syntax.targ phi)
in (_92_1459)::[])
in (_92_1461, _92_1460)))
in (FStar_Absyn_Syntax.mk_Typ_app _92_1462 None phi.FStar_Absyn_Syntax.pos)))

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

let mk_imp = (fun phi1 phi2 -> (match ((let _92_1479 = (compress_typ phi1)
in _92_1479.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid) -> begin
t_true
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
phi2
end
| _26_2150 -> begin
(match ((let _92_1480 = (compress_typ phi2)
in _92_1480.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when ((FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) || (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid)) -> begin
phi2
end
| _26_2154 -> begin
(mk_binop timp phi1 phi2)
end)
end))

let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))

let b2t = (fun e -> (let _92_1489 = (let _92_1488 = (let _92_1487 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg e)
in (_92_1487)::[])
in (b2t_v, _92_1488))
in (FStar_Absyn_Syntax.mk_Typ_app _92_1489 None e.FStar_Absyn_Syntax.pos)))

let rec unmeta_typ = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(unmeta_typ t)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _26_2194)) -> begin
(mk_conj t1 t2)
end
| _26_2199 -> begin
t
end)))

let eq_k = (let a = (let _92_1492 = (new_bvd None)
in (bvd_to_bvar_s _92_1492 FStar_Absyn_Syntax.ktype))
in (let atyp = (btvar_to_typ a)
in (let b = (let _92_1493 = (new_bvd None)
in (bvd_to_bvar_s _92_1493 FStar_Absyn_Syntax.ktype))
in (let btyp = (btvar_to_typ b)
in (let _92_1500 = (let _92_1499 = (let _92_1498 = (let _92_1497 = (let _92_1496 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (let _92_1495 = (let _92_1494 = (FStar_Absyn_Syntax.null_v_binder btyp)
in (_92_1494)::[])
in (_92_1496)::_92_1495))
in ((FStar_Util.Inl (b), Some (FStar_Absyn_Syntax.Implicit)))::_92_1497)
in ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit)))::_92_1498)
in (_92_1499, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _92_1500 FStar_Absyn_Syntax.dummyRange))))))

let teq = (ftv FStar_Absyn_Const.eq2_lid eq_k)

let mk_eq = (fun t1 t2 e1 e2 -> (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((_, FStar_Absyn_Syntax.Typ_unknown)) -> begin
(FStar_All.failwith "DIE! mk_eq with tun")
end
| _26_2217 -> begin
(let _92_1518 = (let _92_1516 = (let _92_1515 = (FStar_Absyn_Syntax.itarg t1)
in (let _92_1514 = (let _92_1513 = (FStar_Absyn_Syntax.itarg t2)
in (let _92_1512 = (let _92_1511 = (FStar_Absyn_Syntax.varg e1)
in (let _92_1510 = (let _92_1509 = (FStar_Absyn_Syntax.varg e2)
in (_92_1509)::[])
in (_92_1511)::_92_1510))
in (_92_1513)::_92_1512))
in (_92_1515)::_92_1514))
in (teq, _92_1516))
in (let _92_1517 = (FStar_Range.union_ranges e1.FStar_Absyn_Syntax.pos e2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _92_1518 None _92_1517)))
end))

let eq_typ = (ftv FStar_Absyn_Const.eqT_lid FStar_Absyn_Syntax.kun)

let mk_eq_typ = (fun t1 t2 -> (let _92_1528 = (let _92_1526 = (let _92_1525 = (FStar_Absyn_Syntax.targ t1)
in (let _92_1524 = (let _92_1523 = (FStar_Absyn_Syntax.targ t2)
in (_92_1523)::[])
in (_92_1525)::_92_1524))
in (eq_typ, _92_1526))
in (let _92_1527 = (FStar_Range.union_ranges t1.FStar_Absyn_Syntax.pos t2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _92_1528 None _92_1527))))

let lex_t = (ftv FStar_Absyn_Const.lex_t_lid FStar_Absyn_Syntax.ktype)

let lex_top = (let lexnil = (withinfo FStar_Absyn_Const.lextop_lid lex_t FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.mk_Exp_fvar (lexnil, Some (FStar_Absyn_Syntax.Data_ctor)) None FStar_Absyn_Syntax.dummyRange))

let lex_pair = (let a = (gen_bvar FStar_Absyn_Syntax.ktype)
in (let lexcons = (let _92_1538 = (let _92_1537 = (let _92_1536 = (let _92_1534 = (FStar_Absyn_Syntax.t_binder a)
in (let _92_1533 = (let _92_1532 = (let _92_1529 = (btvar_to_typ a)
in (FStar_Absyn_Syntax.null_v_binder _92_1529))
in (let _92_1531 = (let _92_1530 = (FStar_Absyn_Syntax.null_v_binder lex_t)
in (_92_1530)::[])
in (_92_1532)::_92_1531))
in (_92_1534)::_92_1533))
in (let _92_1535 = (FStar_Absyn_Syntax.mk_Total lex_t)
in (_92_1536, _92_1535)))
in (FStar_Absyn_Syntax.mk_Typ_fun _92_1537 None FStar_Absyn_Syntax.dummyRange))
in (withinfo FStar_Absyn_Const.lexcons_lid _92_1538 FStar_Absyn_Syntax.dummyRange))
in (FStar_Absyn_Syntax.mk_Exp_fvar (lexcons, Some (FStar_Absyn_Syntax.Data_ctor)) None FStar_Absyn_Syntax.dummyRange)))

let forall_kind = (let a = (let _92_1539 = (new_bvd None)
in (bvd_to_bvar_s _92_1539 FStar_Absyn_Syntax.ktype))
in (let atyp = (btvar_to_typ a)
in (let _92_1547 = (let _92_1546 = (let _92_1545 = (let _92_1544 = (let _92_1543 = (let _92_1542 = (let _92_1541 = (let _92_1540 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (_92_1540)::[])
in (_92_1541, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _92_1542 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _92_1543))
in (_92_1544)::[])
in ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit)))::_92_1545)
in (_92_1546, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _92_1547 FStar_Absyn_Syntax.dummyRange))))

let tforall = (ftv FStar_Absyn_Const.forall_lid forall_kind)

let allT_k = (fun k -> (let _92_1556 = (let _92_1555 = (let _92_1554 = (let _92_1553 = (let _92_1552 = (let _92_1551 = (let _92_1550 = (FStar_Absyn_Syntax.null_t_binder k)
in (_92_1550)::[])
in (_92_1551, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _92_1552 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _92_1553))
in (_92_1554)::[])
in (_92_1555, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _92_1556 FStar_Absyn_Syntax.dummyRange)))

let eqT_k = (fun k -> (let _92_1563 = (let _92_1562 = (let _92_1561 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder k)
in (let _92_1560 = (let _92_1559 = (FStar_Absyn_Syntax.null_t_binder k)
in (_92_1559)::[])
in (_92_1561)::_92_1560))
in (_92_1562, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _92_1563 FStar_Absyn_Syntax.dummyRange)))

let tforall_typ = (fun k -> (let _92_1566 = (allT_k k)
in (ftv FStar_Absyn_Const.allTyp_lid _92_1566)))

let mk_forallT = (fun a b -> (let _92_1578 = (let _92_1577 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _92_1576 = (let _92_1575 = (let _92_1574 = (let _92_1573 = (let _92_1572 = (let _92_1571 = (FStar_Absyn_Syntax.t_binder a)
in (_92_1571)::[])
in (_92_1572, b))
in (FStar_Absyn_Syntax.mk_Typ_lam _92_1573 None b.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _92_1574))
in (_92_1575)::[])
in (_92_1577, _92_1576)))
in (FStar_Absyn_Syntax.mk_Typ_app _92_1578 None b.FStar_Absyn_Syntax.pos)))

let mk_forall = (fun x body -> (let r = FStar_Absyn_Syntax.dummyRange
in (let _92_1589 = (let _92_1588 = (let _92_1587 = (let _92_1586 = (let _92_1585 = (let _92_1584 = (let _92_1583 = (FStar_Absyn_Syntax.v_binder x)
in (_92_1583)::[])
in (_92_1584, body))
in (FStar_Absyn_Syntax.mk_Typ_lam _92_1585 None r))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _92_1586))
in (_92_1587)::[])
in (tforall, _92_1588))
in (FStar_Absyn_Syntax.mk_Typ_app _92_1589 None r))))

let rec close_forall = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
f
end else begin
(let body = (FStar_Absyn_Syntax.mk_Typ_lam ((b)::[], f) None f.FStar_Absyn_Syntax.pos)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _92_1599 = (let _92_1598 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _92_1597 = (let _92_1596 = (FStar_Absyn_Syntax.targ body)
in (_92_1596)::[])
in (_92_1598, _92_1597)))
in (FStar_Absyn_Syntax.mk_Typ_app _92_1599 None f.FStar_Absyn_Syntax.pos))
end
| FStar_Util.Inr (x) -> begin
(let _92_1603 = (let _92_1602 = (let _92_1601 = (let _92_1600 = (FStar_Absyn_Syntax.targ body)
in (_92_1600)::[])
in ((FStar_Util.Inl (x.FStar_Absyn_Syntax.sort), Some (FStar_Absyn_Syntax.Implicit)))::_92_1601)
in (tforall, _92_1602))
in (FStar_Absyn_Syntax.mk_Typ_app _92_1603 None f.FStar_Absyn_Syntax.pos))
end))
end) bs f))

let rec is_wild_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_wild (_26_2244) -> begin
true
end
| _26_2247 -> begin
false
end))

let head_and_args = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(head, args)
end
| _26_2255 -> begin
(t, [])
end)))

let head_and_args_e = (fun e -> (let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(head, args)
end
| _26_2263 -> begin
(e, [])
end)))

let function_formals = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
Some ((bs, c))
end
| _26_2271 -> begin
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
| QAll (_26_2276) -> begin
_26_2276
end))

let ___QEx____0 = (fun projectee -> (match (projectee) with
| QEx (_26_2279) -> begin
_26_2279
end))

let ___BaseConn____0 = (fun projectee -> (match (projectee) with
| BaseConn (_26_2282) -> begin
_26_2282
end))

let destruct_typ_as_formula = (fun f -> (let destruct_base_conn = (fun f -> (let _26_2288 = (true, false)
in (match (_26_2288) with
| (type_sort, term_sort) -> begin
(let oneType = (type_sort)::[]
in (let twoTypes = (type_sort)::(type_sort)::[]
in (let threeTys = (type_sort)::(type_sort)::(type_sort)::[]
in (let twoTerms = (term_sort)::(term_sort)::[]
in (let connectives = ((FStar_Absyn_Const.true_lid, []))::((FStar_Absyn_Const.false_lid, []))::((FStar_Absyn_Const.and_lid, twoTypes))::((FStar_Absyn_Const.or_lid, twoTypes))::((FStar_Absyn_Const.imp_lid, twoTypes))::((FStar_Absyn_Const.iff_lid, twoTypes))::((FStar_Absyn_Const.ite_lid, threeTys))::((FStar_Absyn_Const.not_lid, oneType))::((FStar_Absyn_Const.eqT_lid, twoTypes))::((FStar_Absyn_Const.eq2_lid, twoTerms))::((FStar_Absyn_Const.eq2_lid, (FStar_List.append twoTypes twoTerms)))::[]
in (let rec aux = (fun f _26_2298 -> (match (_26_2298) with
| (lid, arity) -> begin
(let _26_2301 = (head_and_args f)
in (match (_26_2301) with
| (t, args) -> begin
if (((is_constructor t lid) && ((FStar_List.length args) = (FStar_List.length arity))) && (FStar_List.forall2 (fun arg flag -> (match (arg) with
| (FStar_Util.Inl (_26_2305), _26_2308) -> begin
(flag = type_sort)
end
| (FStar_Util.Inr (_26_2311), _26_2314) -> begin
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
(let _92_1667 = (compress_typ t)
in (pats, _92_1667))
end
| _26_2325 -> begin
(let _92_1668 = (compress_typ t)
in ([], _92_1668))
end)))
in (let destruct_q_conn = (fun t -> (let is_q = (fun fa l -> if fa then begin
(is_forall l)
end else begin
(is_exists l)
end)
in (let flat = (fun t -> (let _26_2335 = (head_and_args t)
in (match (_26_2335) with
| (t, args) -> begin
(let _92_1682 = (FStar_All.pipe_right args (FStar_List.map (fun _26_26 -> (match (_26_26) with
| (FStar_Util.Inl (t), imp) -> begin
(let _92_1679 = (let _92_1678 = (compress_typ t)
in FStar_Util.Inl (_92_1678))
in (_92_1679, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _92_1681 = (let _92_1680 = (compress_exp e)
in FStar_Util.Inr (_92_1680))
in (_92_1681, imp))
end))))
in (t, _92_1682))
end)))
in (let rec aux = (fun qopt out t -> (match ((let _92_1689 = (flat t)
in (qopt, _92_1689))) with
| ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _::(FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_q fa tc.FStar_Absyn_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _::(FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_qlid tc.FStar_Absyn_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Absyn_Syntax.v))) ((b)::out) t2)
end
| (Some (true), _26_2483) -> begin
(let _26_2487 = (patterns t)
in (match (_26_2487) with
| (pats, body) -> begin
Some (QAll (((FStar_List.rev out), pats, body)))
end))
end
| (Some (false), _26_2491) -> begin
(let _26_2495 = (patterns t)
in (match (_26_2495) with
| (pats, body) -> begin
Some (QEx (((FStar_List.rev out), pats, body)))
end))
end
| _26_2497 -> begin
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




