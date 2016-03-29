
open Prims
# 29 "FStar.Syntax.Util.fst"
let handle_err : Prims.bool  ->  Prims.exn  ->  Prims.unit = (fun warning e -> (match (e) with
| FStar_Syntax_Syntax.Error (msg, r) -> begin
(let _107_6 = (let _107_5 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s : %s\n%s\n" _107_5 (if warning then begin
"Warning"
end else begin
"Error"
end) msg))
in (FStar_Util.print_string _107_6))
end
| FStar_Util.NYI (s) -> begin
(let _107_7 = (FStar_Util.format1 "Feature not yet implemented: %s" s)
in (FStar_Util.print_string _107_7))
end
| FStar_Syntax_Syntax.Err (s) -> begin
(let _107_8 = (FStar_Util.format1 "Error: %s" s)
in (FStar_Util.print_string _107_8))
end
| _28_23 -> begin
(Prims.raise e)
end))

# 39 "FStar.Syntax.Util.fst"
let handleable : Prims.exn  ->  Prims.bool = (fun _28_1 -> (match (_28_1) with
| (FStar_Syntax_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Syntax_Syntax.Err (_)) -> begin
true
end
| _28_35 -> begin
false
end))

# 50 "FStar.Syntax.Util.fst"
let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.mk_ident ((Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText), lid.FStar_Ident.ident.FStar_Ident.idRange)))::[]))))

# 53 "FStar.Syntax.Util.fst"
let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (
# 54 "FStar.Syntax.Util.fst"
let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText 0)
in (FStar_Util.is_upper c)))

# 57 "FStar.Syntax.Util.fst"
let arg_of_non_null_binder = (fun _28_41 -> (match (_28_41) with
| (b, imp) -> begin
(let _107_16 = (FStar_Syntax_Syntax.bv_to_name b)
in (_107_16, imp))
end))

# 59 "FStar.Syntax.Util.fst"
let args_of_non_null_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
[]
end else begin
(let _107_20 = (arg_of_non_null_binder b)
in (_107_20)::[])
end))))

# 64 "FStar.Syntax.Util.fst"
let args_of_binders : FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun binders -> (let _107_27 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
(
# 67 "FStar.Syntax.Util.fst"
let b = (let _107_24 = (FStar_Syntax_Syntax.new_bv None (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_107_24, (Prims.snd b)))
in (let _107_25 = (arg_of_non_null_binder b)
in (b, _107_25)))
end else begin
(let _107_26 = (arg_of_non_null_binder b)
in (b, _107_26))
end)))
in (FStar_All.pipe_right _107_27 FStar_List.unzip)))

# 71 "FStar.Syntax.Util.fst"
let name_binders : FStar_Syntax_Syntax.binder Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
(
# 74 "FStar.Syntax.Util.fst"
let _28_52 = b
in (match (_28_52) with
| (a, imp) -> begin
(
# 75 "FStar.Syntax.Util.fst"
let b = (let _107_33 = (let _107_32 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _107_32))
in (FStar_Ident.id_of_text _107_33))
in (
# 76 "FStar.Syntax.Util.fst"
let b = {FStar_Syntax_Syntax.ppname = b; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = a.FStar_Syntax_Syntax.sort}
in (b, imp)))
end))
end else begin
b
end))))

# 80 "FStar.Syntax.Util.fst"
let name_function_binders = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _107_37 = (let _107_36 = (let _107_35 = (name_binders binders)
in (_107_35, comp))
in FStar_Syntax_Syntax.Tm_arrow (_107_36))
in (FStar_Syntax_Syntax.mk _107_37 None t.FStar_Syntax_Syntax.pos))
end
| _28_61 -> begin
t
end))

# 84 "FStar.Syntax.Util.fst"
let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _28_65 -> (match (_28_65) with
| (t, imp) -> begin
(let _107_42 = (let _107_41 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left Prims.fst _107_41))
in (_107_42, imp))
end)))))

# 87 "FStar.Syntax.Util.fst"
let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _28_69 -> (match (_28_69) with
| (t, imp) -> begin
(let _107_46 = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (_107_46, imp))
end)))))

# 90 "FStar.Syntax.Util.fst"
let binders_of_freevars : FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (let _107_49 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _107_49 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))

# 92 "FStar.Syntax.Util.fst"
let mk_subst = (fun s -> (s)::[])

# 94 "FStar.Syntax.Util.fst"
let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> if ((FStar_List.length formals) = (FStar_List.length actuals)) then begin
(FStar_List.fold_right2 (fun f a out -> (FStar_Syntax_Syntax.NT (((Prims.fst f), (Prims.fst a))))::out) formals actuals [])
end else begin
(FStar_All.failwith "Ill-formed substitution")
end)

# 99 "FStar.Syntax.Util.fst"
let rename_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun replace_xs with_ys -> if ((FStar_List.length replace_xs) = (FStar_List.length with_ys)) then begin
(FStar_List.map2 (fun _28_82 _28_86 -> (match ((_28_82, _28_86)) with
| ((x, _28_81), (y, _28_85)) -> begin
(let _107_65 = (let _107_64 = (FStar_Syntax_Syntax.bv_to_name y)
in (x, _107_64))
in FStar_Syntax_Syntax.NT (_107_65))
end)) replace_xs with_ys)
end else begin
(FStar_All.failwith "Ill-formed substitution")
end)

# 106 "FStar.Syntax.Util.fst"
let rec unmeta : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (
# 107 "FStar.Syntax.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_meta (e, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e, _, _)) -> begin
(unmeta e)
end
| _28_101 -> begin
e
end)))

# 119 "FStar.Syntax.Util.fst"
let rec univ_kernel : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.universe * Prims.int) = (fun u -> (match (u) with
| (FStar_Syntax_Syntax.U_unknown) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
(u, 0)
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(
# 124 "FStar.Syntax.Util.fst"
let _28_115 = (univ_kernel u)
in (match (_28_115) with
| (k, n) -> begin
(k, (n + 1))
end))
end
| (FStar_Syntax_Syntax.U_max (_)) | (FStar_Syntax_Syntax.U_bvar (_)) -> begin
(FStar_All.failwith "Imposible")
end))

# 130 "FStar.Syntax.Util.fst"
let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (let _107_72 = (univ_kernel u)
in (Prims.snd _107_72)))

# 138 "FStar.Syntax.Util.fst"
let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match ((u1, u2)) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) -> begin
(FStar_All.failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
0
end
| (FStar_Syntax_Syntax.U_unknown, _28_142) -> begin
(- (1))
end
| (_28_145, FStar_Syntax_Syntax.U_unknown) -> begin
1
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
0
end
| (FStar_Syntax_Syntax.U_zero, _28_153) -> begin
(- (1))
end
| (_28_156, FStar_Syntax_Syntax.U_zero) -> begin
1
end
| (FStar_Syntax_Syntax.U_name (u1), FStar_Syntax_Syntax.U_name (u2)) -> begin
(FStar_String.compare u1.FStar_Ident.idText u2.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (_28_165), FStar_Syntax_Syntax.U_unif (_28_168)) -> begin
(- (1))
end
| (FStar_Syntax_Syntax.U_unif (_28_172), FStar_Syntax_Syntax.U_name (_28_175)) -> begin
1
end
| (FStar_Syntax_Syntax.U_unif (u1), FStar_Syntax_Syntax.U_unif (u2)) -> begin
((FStar_Unionfind.uvar_id u1) - (FStar_Unionfind.uvar_id u2))
end
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(
# 157 "FStar.Syntax.Util.fst"
let n1 = (FStar_List.length us1)
in (
# 158 "FStar.Syntax.Util.fst"
let n2 = (FStar_List.length us2)
in if (n1 <> n2) then begin
(n1 - n2)
end else begin
(
# 161 "FStar.Syntax.Util.fst"
let copt = (let _107_78 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map _107_78 (fun _28_192 -> (match (_28_192) with
| (u1, u2) -> begin
(
# 162 "FStar.Syntax.Util.fst"
let c = (compare_univs u1 u2)
in if (c <> 0) then begin
Some (c)
end else begin
None
end)
end))))
in (match (copt) with
| None -> begin
0
end
| Some (c) -> begin
c
end))
end))
end
| (FStar_Syntax_Syntax.U_max (_28_199), _28_202) -> begin
(- (1))
end
| (_28_205, FStar_Syntax_Syntax.U_max (_28_207)) -> begin
1
end
| _28_211 -> begin
(
# 175 "FStar.Syntax.Util.fst"
let _28_214 = (univ_kernel u1)
in (match (_28_214) with
| (k1, n1) -> begin
(
# 176 "FStar.Syntax.Util.fst"
let _28_217 = (univ_kernel u2)
in (match (_28_217) with
| (k2, n2) -> begin
(
# 177 "FStar.Syntax.Util.fst"
let r = (compare_univs k1 k2)
in if (r = 0) then begin
(n1 - n2)
end else begin
r
end)
end))
end))
end))

# 182 "FStar.Syntax.Util.fst"
let eq_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.bool = (fun u1 u2 -> ((compare_univs u1 u2) = 0))

# 188 "FStar.Syntax.Util.fst"
let ml_comp : FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (let _107_88 = (let _107_87 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_ML_lid r)
in {FStar_Syntax_Syntax.effect_name = _107_87; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]})
in (FStar_Syntax_Syntax.mk_Comp _107_88)))

# 204 "FStar.Syntax.Util.fst"
let comp_set_flags : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun c f -> (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (_)) | (FStar_Syntax_Syntax.GTotal (_)) -> begin
c
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 207 "FStar.Syntax.Util.fst"
let _28_233 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ((
# 207 "FStar.Syntax.Util.fst"
let _28_235 = ct
in {FStar_Syntax_Syntax.effect_name = _28_235.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _28_235.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _28_235.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})); FStar_Syntax_Syntax.tk = _28_233.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _28_233.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _28_233.FStar_Syntax_Syntax.vars})
end))

# 209 "FStar.Syntax.Util.fst"
let comp_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_28_239) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (_28_242) -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.flags
end))

# 214 "FStar.Syntax.Util.fst"
let comp_effect_name = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
c.FStar_Syntax_Syntax.effect_name
end
| FStar_Syntax_Syntax.Total (_28_250) -> begin
FStar_Syntax_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (_28_253) -> begin
FStar_Syntax_Const.effect_GTot_lid
end))

# 219 "FStar.Syntax.Util.fst"
let comp_to_comp_typ : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
c
end
| FStar_Syntax_Syntax.Total (t) -> begin
{FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.TOTAL)::[]}
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
{FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_GTot_lid; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.SOMETRIVIAL)::[]}
end))

# 225 "FStar.Syntax.Util.fst"
let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _28_2 -> (match (_28_2) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _28_267 -> begin
false
end)))))

# 228 "FStar.Syntax.Util.fst"
let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _28_3 -> (match (_28_3) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _28_273 -> begin
false
end))))))

# 230 "FStar.Syntax.Util.fst"
let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _28_4 -> (match (_28_4) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _28_279 -> begin
false
end))))))

# 234 "FStar.Syntax.Util.fst"
let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _28_5 -> (match (_28_5) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _28_285 -> begin
false
end)))))

# 236 "FStar.Syntax.Util.fst"
let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _28_6 -> (match (_28_6) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _28_291 -> begin
false
end)))))

# 238 "FStar.Syntax.Util.fst"
let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid (comp_effect_name c))))

# 242 "FStar.Syntax.Util.fst"
let is_pure_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_28_295) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (_28_298) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
((((is_total_comp c) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Pure_lid)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _28_7 -> (match (_28_7) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _28_305 -> begin
false
end)))))
end))

# 250 "FStar.Syntax.Util.fst"
let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_Ghost_lid l)))

# 255 "FStar.Syntax.Util.fst"
let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))

# 257 "FStar.Syntax.Util.fst"
let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((((is_total_lcomp lc) || (FStar_Ident.lid_equals lc.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals lc.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Pure_lid)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _28_8 -> (match (_28_8) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _28_312 -> begin
false
end))))))

# 263 "FStar.Syntax.Util.fst"
let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))

# 266 "FStar.Syntax.Util.fst"
let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _107_123 = (FStar_Syntax_Subst.compress t)
in _107_123.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_28_316, c) -> begin
(is_pure_or_ghost_comp c)
end
| _28_321 -> begin
true
end))

# 270 "FStar.Syntax.Util.fst"
let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _107_126 = (FStar_Syntax_Subst.compress t)
in _107_126.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_28_324, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid)
end
| _28_331 -> begin
false
end)
end
| _28_333 -> begin
false
end))

# 279 "FStar.Syntax.Util.fst"
let head_and_args : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.args) = (fun t -> (
# 280 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(head, args)
end
| _28_341 -> begin
(t, [])
end)))

# 285 "FStar.Syntax.Util.fst"
let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 286 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (t, _28_346) -> begin
(FStar_Syntax_Subst.compress t)
end
| _28_350 -> begin
t
end)))

# 291 "FStar.Syntax.Util.fst"
let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _107_133 = (FStar_Syntax_Subst.compress t)
in _107_133.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_28_353, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| _req::_ens::(pats, _28_363)::_28_360 -> begin
(
# 297 "FStar.Syntax.Util.fst"
let pats' = (unmeta pats)
in (
# 298 "FStar.Syntax.Util.fst"
let _28_374 = (head_and_args pats')
in (match (_28_374) with
| (head, _28_373) -> begin
(match ((let _107_134 = (un_uinst head)
in _107_134.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid)
end
| _28_378 -> begin
false
end)
end)))
end
| _28_380 -> begin
false
end)
end
| _28_382 -> begin
false
end)
end
| _28_384 -> begin
false
end))

# 309 "FStar.Syntax.Util.fst"
let is_ml_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _28_9 -> (match (_28_9) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _28_391 -> begin
false
end)))))
end
| _28_393 -> begin
false
end))

# 315 "FStar.Syntax.Util.fst"
let comp_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (t)) | (FStar_Syntax_Syntax.GTotal (t)) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))

# 320 "FStar.Syntax.Util.fst"
let set_result_typ = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_28_403) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (_28_406) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (
# 323 "FStar.Syntax.Util.fst"
let _28_410 = ct
in {FStar_Syntax_Syntax.effect_name = _28_410.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = _28_410.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _28_410.FStar_Syntax_Syntax.flags}))
end))

# 325 "FStar.Syntax.Util.fst"
let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _28_10 -> (match (_28_10) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _28_417 -> begin
false
end)))))

# 331 "FStar.Syntax.Util.fst"
let primops : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]

# 347 "FStar.Syntax.Util.fst"
let is_primop_lid : FStar_Ident.lident  ->  Prims.bool = (fun l -> (FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals l))))

# 349 "FStar.Syntax.Util.fst"
let is_primop = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_primop_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| _28_423 -> begin
false
end))

# 353 "FStar.Syntax.Util.fst"
let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (
# 354 "FStar.Syntax.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e, _28_428, _28_430) -> begin
(unascribe e)
end
| _28_434 -> begin
e
end)))

# 359 "FStar.Syntax.Util.fst"
let rec ascribe = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', _28_439, _28_441) -> begin
(ascribe t' k)
end
| _28_445 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((t, k, None))) None t.FStar_Syntax_Syntax.pos)
end))

# 363 "FStar.Syntax.Util.fst"
let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 364 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _28_450) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _28_455, _28_457) -> begin
(unrefine t)
end
| _28_461 -> begin
t
end)))

# 370 "FStar.Syntax.Util.fst"
let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (match ((let _107_153 = (FStar_Syntax_Subst.compress e)
in _107_153.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_28_464) -> begin
true
end
| _28_467 -> begin
false
end))

# 374 "FStar.Syntax.Util.fst"
let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _107_156 = (FStar_Syntax_Subst.compress t)
in _107_156.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_28_470) -> begin
true
end
| _28_473 -> begin
false
end))

# 378 "FStar.Syntax.Util.fst"
let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 379 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _28_478) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _28_483, _28_485) -> begin
(pre_typ t)
end
| _28_489 -> begin
t
end)))

# 385 "FStar.Syntax.Util.fst"
let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.args Prims.option = (fun typ lid -> (
# 386 "FStar.Syntax.Util.fst"
let typ = (FStar_Syntax_Subst.compress typ)
in (match ((let _107_163 = (un_uinst typ)
in _107_163.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 389 "FStar.Syntax.Util.fst"
let head = (un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
Some (args)
end
| _28_501 -> begin
None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
Some ([])
end
| _28_505 -> begin
None
end)))

# 397 "FStar.Syntax.Util.fst"
let rec lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_let (_, _, lids, _)) | (FStar_Syntax_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_datacon (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_declare_typ (lid, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n, _28_589) -> begin
(n.FStar_Syntax_Syntax.mname)::[]
end
| (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) -> begin
[]
end))

# 410 "FStar.Syntax.Util.fst"
let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.option = (fun se -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _28_605 -> begin
None
end))

# 414 "FStar.Syntax.Util.fst"
let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Syntax_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_datacon (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_assume (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_let (_, r, _, _)) | (FStar_Syntax_Syntax.Sig_main (_, r)) | (FStar_Syntax_Syntax.Sig_pragma (_, r)) | (FStar_Syntax_Syntax.Sig_new_effect (_, r)) | (FStar_Syntax_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))

# 427 "FStar.Syntax.Util.fst"
let range_of_lb = (fun _28_11 -> (match (_28_11) with
| (FStar_Util.Inl (x), _28_706, _28_708) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), _28_713, _28_715) -> begin
(FStar_Ident.range_of_lid l)
end))

# 431 "FStar.Syntax.Util.fst"
let range_of_arg = (fun _28_720 -> (match (_28_720) with
| (hd, _28_719) -> begin
hd.FStar_Syntax_Syntax.pos
end))

# 433 "FStar.Syntax.Util.fst"
let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))

# 436 "FStar.Syntax.Util.fst"
let mk_app = (fun f args -> (
# 437 "FStar.Syntax.Util.fst"
let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((f, args))) None r)))

# 440 "FStar.Syntax.Util.fst"
let mk_data = (fun l args -> (match (args) with
| [] -> begin
(let _107_182 = (let _107_181 = (let _107_180 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_107_180, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_107_181))
in (FStar_Syntax_Syntax.mk _107_182 None (FStar_Ident.range_of_lid l)))
end
| _28_732 -> begin
(
# 445 "FStar.Syntax.Util.fst"
let e = (let _107_183 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app _107_183 args))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))) None e.FStar_Syntax_Syntax.pos))
end))

# 448 "FStar.Syntax.Util.fst"
let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident ((Prims.strcat "^fname^" x.FStar_Ident.idText), x.FStar_Ident.idRange)))

# 449 "FStar.Syntax.Util.fst"
let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _107_189 = (let _107_188 = (FStar_Util.substring_from x.FStar_Ident.idText 7)
in (_107_188, x.FStar_Ident.idRange))
in (FStar_Ident.mk_ident _107_189))
end else begin
x
end)

# 454 "FStar.Syntax.Util.fst"
let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (
# 455 "FStar.Syntax.Util.fst"
let nm = if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _107_199 = (let _107_198 = (let _107_196 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _107_196))
in (let _107_197 = (FStar_Syntax_Syntax.range_of_bv x)
in (_107_198, _107_197)))
in (FStar_Ident.mk_ident _107_199))
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (
# 458 "FStar.Syntax.Util.fst"
let y = (
# 458 "FStar.Syntax.Util.fst"
let _28_740 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = _28_740.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _28_740.FStar_Syntax_Syntax.sort})
in (let _107_203 = (let _107_202 = (let _107_201 = (let _107_200 = (unmangle_field_name nm)
in (_107_200)::[])
in (FStar_List.append (FStar_Ident.ids_of_lid lid) _107_201))
in (FStar_Ident.lid_of_ids _107_202))
in (_107_203, y)))))

# 461 "FStar.Syntax.Util.fst"
let set_uvar = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (_28_746) -> begin
(let _107_208 = (let _107_207 = (let _107_206 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _107_206))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" _107_207))
in (FStar_All.failwith _107_208))
end
| _28_749 -> begin
(FStar_Unionfind.change uv (FStar_Syntax_Syntax.Fixed (t)))
end))

# 466 "FStar.Syntax.Util.fst"
let qualifier_equal : FStar_Syntax_Syntax.qualifier  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun q1 q2 -> (match ((q1, q2)) with
| (FStar_Syntax_Syntax.Discriminator (l1), FStar_Syntax_Syntax.Discriminator (l2)) -> begin
(FStar_Ident.lid_equals l1 l2)
end
| (FStar_Syntax_Syntax.Projector (l1a, l1b), FStar_Syntax_Syntax.Projector (l2a, l2b)) -> begin
((FStar_Ident.lid_equals l1a l2a) && (l1b.FStar_Ident.idText = l2b.FStar_Ident.idText))
end
| ((FStar_Syntax_Syntax.RecordType (f1), FStar_Syntax_Syntax.RecordType (f2))) | ((FStar_Syntax_Syntax.RecordConstructor (f1), FStar_Syntax_Syntax.RecordConstructor (f2))) -> begin
(((FStar_List.length f1) = (FStar_List.length f2)) && (FStar_List.forall2 FStar_Ident.lid_equals f1 f2))
end
| (FStar_Syntax_Syntax.DefaultEffect (Some (l1)), FStar_Syntax_Syntax.DefaultEffect (Some (l2))) -> begin
(FStar_Ident.lid_equals l1 l2)
end
| _28_782 -> begin
(q1 = q2)
end))

# 478 "FStar.Syntax.Util.fst"
let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (
# 479 "FStar.Syntax.Util.fst"
let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 482 "FStar.Syntax.Util.fst"
let _28_791 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_28_791) with
| (bs, c) -> begin
if (is_tot_or_gtot_comp c) then begin
(
# 484 "FStar.Syntax.Util.fst"
let _28_794 = (arrow_formals_comp (comp_result c))
in (match (_28_794) with
| (bs', k) -> begin
((FStar_List.append bs bs'), k)
end))
end else begin
(bs, c)
end
end))
end
| _28_796 -> begin
(let _107_215 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _107_215))
end)))

# 489 "FStar.Syntax.Util.fst"
let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.typ) = (fun k -> (
# 490 "FStar.Syntax.Util.fst"
let _28_800 = (arrow_formals_comp k)
in (match (_28_800) with
| (bs, c) -> begin
(bs, (comp_result c))
end)))

# 493 "FStar.Syntax.Util.fst"
let rec abs_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.term) = (fun t -> (match ((let _107_220 = (FStar_Syntax_Subst.compress t)
in _107_220.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, t, _28_805) -> begin
(
# 495 "FStar.Syntax.Util.fst"
let _28_810 = (abs_formals t)
in (match (_28_810) with
| (bs', t) -> begin
(FStar_Syntax_Subst.open_term (FStar_List.append bs bs') t)
end))
end
| _28_812 -> begin
([], t)
end))

# 499 "FStar.Syntax.Util.fst"
let abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> (match (bs) with
| [] -> begin
t
end
| _28_818 -> begin
(
# 502 "FStar.Syntax.Util.fst"
let body = (let _107_227 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress _107_227))
in (match ((body.FStar_Syntax_Syntax.n, lopt)) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t, lopt'), None) -> begin
(let _107_231 = (let _107_230 = (let _107_229 = (let _107_228 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append _107_228 bs'))
in (_107_229, t, lopt))
in FStar_Syntax_Syntax.Tm_abs (_107_230))
in (FStar_Syntax_Syntax.mk _107_231 None t.FStar_Syntax_Syntax.pos))
end
| _28_828 -> begin
(
# 507 "FStar.Syntax.Util.fst"
let lopt = (match (lopt) with
| None -> begin
None
end
| Some (lc) -> begin
(let _107_232 = (FStar_Syntax_Subst.close_lcomp bs lc)
in Some (_107_232))
end)
in (let _107_235 = (let _107_234 = (let _107_233 = (FStar_Syntax_Subst.close_binders bs)
in (_107_233, body, lopt))
in FStar_Syntax_Syntax.Tm_abs (_107_234))
in (FStar_Syntax_Syntax.mk _107_235 None t.FStar_Syntax_Syntax.pos)))
end))
end))

# 512 "FStar.Syntax.Util.fst"
let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| _28_837 -> begin
(let _107_243 = (let _107_242 = (let _107_241 = (FStar_Syntax_Subst.close_binders bs)
in (let _107_240 = (FStar_Syntax_Subst.close_comp bs c)
in (_107_241, _107_240)))
in FStar_Syntax_Syntax.Tm_arrow (_107_242))
in (FStar_Syntax_Syntax.mk _107_243 None c.FStar_Syntax_Syntax.pos))
end))

# 515 "FStar.Syntax.Util.fst"
let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun b t -> (let _107_255 = (let _107_251 = (let _107_250 = (let _107_249 = (let _107_248 = (FStar_Syntax_Syntax.mk_binder b)
in (_107_248)::[])
in (FStar_Syntax_Subst.close _107_249 t))
in (b, _107_250))
in FStar_Syntax_Syntax.Tm_refine (_107_251))
in (let _107_254 = (FStar_ST.read b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (let _107_253 = (let _107_252 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges _107_252 t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk _107_255 _107_254 _107_253)))))

# 516 "FStar.Syntax.Util.fst"
let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))

# 518 "FStar.Syntax.Util.fst"
let mk_letbinding : FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def})

# 525 "FStar.Syntax.Util.fst"
let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list Prims.option  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def -> (
# 526 "FStar.Syntax.Util.fst"
let def = (match (recs) with
| None -> begin
def
end
| Some (fvs) -> begin
(
# 529 "FStar.Syntax.Util.fst"
let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _107_280 -> FStar_Syntax_Syntax.U_name (_107_280))))
in (
# 530 "FStar.Syntax.Util.fst"
let inst = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, universes))))
in (FStar_Syntax_InstFV.instantiate inst def)))
end)
in (
# 532 "FStar.Syntax.Util.fst"
let typ = (FStar_Syntax_Subst.close_univ_vars univ_vars typ)
in (
# 533 "FStar.Syntax.Util.fst"
let def = (FStar_Syntax_Subst.close_univ_vars univ_vars def)
in (mk_letbinding lbname univ_vars typ eff def)))))

# 536 "FStar.Syntax.Util.fst"
let open_univ_vars_binders_and_comp : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 539 "FStar.Syntax.Util.fst"
let _28_867 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_28_867) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _28_869 -> begin
(
# 542 "FStar.Syntax.Util.fst"
let t' = (arrow binders c)
in (
# 543 "FStar.Syntax.Util.fst"
let _28_873 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_28_873) with
| (uvs, t') -> begin
(match ((let _107_288 = (FStar_Syntax_Subst.compress t')
in _107_288.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _28_879 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 551 "FStar.Syntax.Util.fst"
let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.starts_with fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.tuple")
end
| _28_884 -> begin
false
end))

# 555 "FStar.Syntax.Util.fst"
let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 556 "FStar.Syntax.Util.fst"
let t = (let _107_295 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "tuple%s" _107_295))
in (let _107_296 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _107_296 r))))

# 559 "FStar.Syntax.Util.fst"
let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 560 "FStar.Syntax.Util.fst"
let t = (let _107_301 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Mktuple%s" _107_301))
in (let _107_302 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _107_302 r))))

# 563 "FStar.Syntax.Util.fst"
let is_tuple_data_lid : FStar_Ident.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _107_307 = (mk_tuple_data_lid n FStar_Range.dummyRange)
in (FStar_Ident.lid_equals f _107_307)))

# 566 "FStar.Syntax.Util.fst"
let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.starts_with fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.dtuple")
end
| _28_897 -> begin
false
end))

# 570 "FStar.Syntax.Util.fst"
let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 571 "FStar.Syntax.Util.fst"
let t = (let _107_314 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "dtuple%s" _107_314))
in (let _107_315 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _107_315 r))))

# 574 "FStar.Syntax.Util.fst"
let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 575 "FStar.Syntax.Util.fst"
let t = (let _107_320 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Mkdtuple%s" _107_320))
in (let _107_321 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _107_321 r))))

# 578 "FStar.Syntax.Util.fst"
let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> (FStar_Ident.lid_equals x FStar_Syntax_Const.eq2_lid))

# 580 "FStar.Syntax.Util.fst"
let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.forall_lid))

# 581 "FStar.Syntax.Util.fst"
let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.exists_lid))

# 582 "FStar.Syntax.Util.fst"
let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))

# 583 "FStar.Syntax.Util.fst"
let is_equality = (fun x -> (is_lid_equality x.FStar_Syntax_Syntax.v))

# 585 "FStar.Syntax.Util.fst"
let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (
# 586 "FStar.Syntax.Util.fst"
let lst = (FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.not_lid)::(FStar_Syntax_Const.iff_lid)::(FStar_Syntax_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))

# 590 "FStar.Syntax.Util.fst"
let is_constructor : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _107_337 = (pre_typ t)
in _107_337.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| _28_916 -> begin
false
end))

# 595 "FStar.Syntax.Util.fst"
let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _107_342 = (pre_typ t)
in _107_342.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (_28_920) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t, _28_924) -> begin
(is_constructed_typ t lid)
end
| _28_928 -> begin
false
end))

# 600 "FStar.Syntax.Util.fst"
let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun t -> (
# 601 "FStar.Syntax.Util.fst"
let t = (pre_typ t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_app (t, _28_942) -> begin
(get_tycon t)
end
| _28_946 -> begin
None
end)))

# 609 "FStar.Syntax.Util.fst"
let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _28_952 _28_956 -> (match ((_28_952, _28_956)) with
| ((fn1, _28_951), (fn2, _28_955)) -> begin
(FStar_String.compare (FStar_Ident.text_of_lid fn1) (FStar_Ident.text_of_lid fn2))
end)))))

# 616 "FStar.Syntax.Util.fst"
let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (
# 617 "FStar.Syntax.Util.fst"
let theory_syms = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))

# 639 "FStar.Syntax.Util.fst"
let ktype : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None FStar_Range.dummyRange)

# 640 "FStar.Syntax.Util.fst"
let ktype0 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) None FStar_Range.dummyRange)

# 643 "FStar.Syntax.Util.fst"
let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun _28_959 -> (match (()) with
| () -> begin
(
# 644 "FStar.Syntax.Util.fst"
let u = (let _107_353 = (FStar_Unionfind.fresh None)
in (FStar_All.pipe_left (fun _107_352 -> FStar_Syntax_Syntax.U_unif (_107_352)) _107_353))
in (let _107_354 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None FStar_Range.dummyRange)
in (_107_354, u)))
end))

# 647 "FStar.Syntax.Util.fst"
let kt_kt : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Const.kunary ktype0 ktype0)

# 648 "FStar.Syntax.Util.fst"
let kt_kt_kt : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Const.kbin ktype0 ktype0 ktype0)

# 650 "FStar.Syntax.Util.fst"
let fvar_const : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun l -> (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant None))

# 651 "FStar.Syntax.Util.fst"
let tand : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.and_lid)

# 652 "FStar.Syntax.Util.fst"
let tor : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.or_lid)

# 653 "FStar.Syntax.Util.fst"
let timp : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.imp_lid)

# 654 "FStar.Syntax.Util.fst"
let tiff : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.iff_lid)

# 655 "FStar.Syntax.Util.fst"
let t_bool : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.bool_lid)

# 656 "FStar.Syntax.Util.fst"
let t_false : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.false_lid)

# 657 "FStar.Syntax.Util.fst"
let t_true : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.true_lid)

# 658 "FStar.Syntax.Util.fst"
let b2t_v : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.b2t_lid)

# 659 "FStar.Syntax.Util.fst"
let t_not : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.not_lid)

# 661 "FStar.Syntax.Util.fst"
let mk_conj_opt : FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _107_368 = (let _107_367 = (let _107_365 = (let _107_364 = (let _107_363 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _107_362 = (let _107_361 = (FStar_Syntax_Syntax.as_arg phi2)
in (_107_361)::[])
in (_107_363)::_107_362))
in (tand, _107_364))
in FStar_Syntax_Syntax.Tm_app (_107_365))
in (let _107_366 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _107_367 None _107_366)))
in Some (_107_368))
end))

# 664 "FStar.Syntax.Util.fst"
let mk_binop = (fun op_t phi1 phi2 -> (let _107_378 = (let _107_376 = (let _107_375 = (let _107_374 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _107_373 = (let _107_372 = (FStar_Syntax_Syntax.as_arg phi2)
in (_107_372)::[])
in (_107_374)::_107_373))
in (op_t, _107_375))
in FStar_Syntax_Syntax.Tm_app (_107_376))
in (let _107_377 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _107_378 None _107_377))))

# 665 "FStar.Syntax.Util.fst"
let mk_neg = (fun phi -> (let _107_383 = (let _107_382 = (let _107_381 = (let _107_380 = (FStar_Syntax_Syntax.as_arg phi)
in (_107_380)::[])
in (t_not, _107_381))
in FStar_Syntax_Syntax.Tm_app (_107_382))
in (FStar_Syntax_Syntax.mk _107_383 None phi.FStar_Syntax_Syntax.pos)))

# 666 "FStar.Syntax.Util.fst"
let mk_conj = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))

# 667 "FStar.Syntax.Util.fst"
let mk_conj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
end
| hd::tl -> begin
(FStar_List.fold_right mk_conj tl hd)
end))

# 670 "FStar.Syntax.Util.fst"
let mk_disj = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))

# 671 "FStar.Syntax.Util.fst"
let mk_disj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
t_false
end
| hd::tl -> begin
(FStar_List.fold_right mk_disj tl hd)
end))

# 674 "FStar.Syntax.Util.fst"
let mk_imp : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (match ((let _107_396 = (FStar_Syntax_Subst.compress phi1)
in _107_396.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid) -> begin
t_true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
phi2
end
| _28_992 -> begin
(match ((let _107_397 = (FStar_Syntax_Subst.compress phi2)
in _107_397.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when ((FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) || (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid)) -> begin
phi2
end
| _28_996 -> begin
(mk_binop timp phi1 phi2)
end)
end))

# 684 "FStar.Syntax.Util.fst"
let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))

# 685 "FStar.Syntax.Util.fst"
let b2t = (fun e -> (let _107_404 = (let _107_403 = (let _107_402 = (let _107_401 = (FStar_Syntax_Syntax.as_arg e)
in (_107_401)::[])
in (b2t_v, _107_402))
in FStar_Syntax_Syntax.Tm_app (_107_403))
in (FStar_Syntax_Syntax.mk _107_404 None e.FStar_Syntax_Syntax.pos)))

# 687 "FStar.Syntax.Util.fst"
let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.eq2_lid)

# 689 "FStar.Syntax.Util.fst"
let mk_eq = (fun t1 t2 e1 e2 -> (let _107_415 = (let _107_413 = (let _107_412 = (let _107_411 = (FStar_Syntax_Syntax.as_arg e1)
in (let _107_410 = (let _107_409 = (FStar_Syntax_Syntax.as_arg e2)
in (_107_409)::[])
in (_107_411)::_107_410))
in (teq, _107_412))
in FStar_Syntax_Syntax.Tm_app (_107_413))
in (let _107_414 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _107_415 None _107_414))))

# 691 "FStar.Syntax.Util.fst"
let mk_has_type = (fun t x t' -> (
# 692 "FStar.Syntax.Util.fst"
let t_has_type = (fvar_const FStar_Syntax_Const.has_type_lid)
in (
# 693 "FStar.Syntax.Util.fst"
let t_has_type = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((t_has_type, (FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]))) None FStar_Range.dummyRange)
in (let _107_426 = (let _107_425 = (let _107_424 = (let _107_423 = (FStar_Syntax_Syntax.iarg t)
in (let _107_422 = (let _107_421 = (FStar_Syntax_Syntax.as_arg x)
in (let _107_420 = (let _107_419 = (FStar_Syntax_Syntax.as_arg t')
in (_107_419)::[])
in (_107_421)::_107_420))
in (_107_423)::_107_422))
in (t_has_type, _107_424))
in FStar_Syntax_Syntax.Tm_app (_107_425))
in (FStar_Syntax_Syntax.mk _107_426 None FStar_Range.dummyRange)))))

# 696 "FStar.Syntax.Util.fst"
let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.lex_t_lid)

# 697 "FStar.Syntax.Util.fst"
let lex_top : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lextop_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))

# 698 "FStar.Syntax.Util.fst"
let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lexcons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))

# 699 "FStar.Syntax.Util.fst"
let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.forall_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)

# 701 "FStar.Syntax.Util.fst"
let lcomp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (
# 702 "FStar.Syntax.Util.fst"
let c = (comp_to_comp_typ c0)
in {FStar_Syntax_Syntax.eff_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.res_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.cflags = c.FStar_Syntax_Syntax.flags; FStar_Syntax_Syntax.comp = (fun _28_1011 -> (match (()) with
| () -> begin
c0
end))}))

# 708 "FStar.Syntax.Util.fst"
let mk_forall : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun x body -> (let _107_443 = (let _107_442 = (let _107_441 = (let _107_440 = (let _107_439 = (let _107_438 = (let _107_434 = (FStar_Syntax_Syntax.mk_binder x)
in (_107_434)::[])
in (let _107_437 = (let _107_436 = (let _107_435 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (FStar_All.pipe_left lcomp_of_comp _107_435))
in Some (_107_436))
in (abs _107_438 body _107_437)))
in (FStar_Syntax_Syntax.as_arg _107_439))
in (_107_440)::[])
in (tforall, _107_441))
in FStar_Syntax_Syntax.Tm_app (_107_442))
in (FStar_Syntax_Syntax.mk _107_443 None FStar_Range.dummyRange)))

# 711 "FStar.Syntax.Util.fst"
let rec close_forall : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
f
end else begin
(mk_forall (Prims.fst b) f)
end) bs f))

# 714 "FStar.Syntax.Util.fst"
let rec is_wild_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (_28_1020) -> begin
true
end
| _28_1023 -> begin
false
end))

# 719 "FStar.Syntax.Util.fst"
let if_then_else = (fun b t1 t2 -> (
# 720 "FStar.Syntax.Util.fst"
let then_branch = (let _107_454 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t1.FStar_Syntax_Syntax.pos)
in (_107_454, None, t1))
in (
# 721 "FStar.Syntax.Util.fst"
let else_branch = (let _107_455 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Syntax_Syntax.pos)
in (_107_455, None, t2))
in (let _107_457 = (let _107_456 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos _107_456))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((b, (then_branch)::(else_branch)::[]))) None _107_457)))))

# 727 "FStar.Syntax.Util.fst"
type qpats =
FStar_Syntax_Syntax.args Prims.list

# 728 "FStar.Syntax.Util.fst"
type connective =
| QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args)

# 729 "FStar.Syntax.Util.fst"
let is_QAll = (fun _discr_ -> (match (_discr_) with
| QAll (_) -> begin
true
end
| _ -> begin
false
end))

# 730 "FStar.Syntax.Util.fst"
let is_QEx = (fun _discr_ -> (match (_discr_) with
| QEx (_) -> begin
true
end
| _ -> begin
false
end))

# 731 "FStar.Syntax.Util.fst"
let is_BaseConn = (fun _discr_ -> (match (_discr_) with
| BaseConn (_) -> begin
true
end
| _ -> begin
false
end))

# 729 "FStar.Syntax.Util.fst"
let ___QAll____0 = (fun projectee -> (match (projectee) with
| QAll (_28_1031) -> begin
_28_1031
end))

# 730 "FStar.Syntax.Util.fst"
let ___QEx____0 = (fun projectee -> (match (projectee) with
| QEx (_28_1034) -> begin
_28_1034
end))

# 731 "FStar.Syntax.Util.fst"
let ___BaseConn____0 = (fun projectee -> (match (projectee) with
| BaseConn (_28_1037) -> begin
_28_1037
end))

# 733 "FStar.Syntax.Util.fst"
let destruct_typ_as_formula : FStar_Syntax_Syntax.term  ->  connective Prims.option = (fun f -> (
# 734 "FStar.Syntax.Util.fst"
let destruct_base_conn = (fun f -> (
# 735 "FStar.Syntax.Util.fst"
let connectives = ((FStar_Syntax_Const.true_lid, 0))::((FStar_Syntax_Const.false_lid, 0))::((FStar_Syntax_Const.and_lid, 2))::((FStar_Syntax_Const.or_lid, 2))::((FStar_Syntax_Const.imp_lid, 2))::((FStar_Syntax_Const.iff_lid, 2))::((FStar_Syntax_Const.ite_lid, 3))::((FStar_Syntax_Const.not_lid, 1))::((FStar_Syntax_Const.eq2_lid, 4))::((FStar_Syntax_Const.eq2_lid, 2))::[]
in (
# 746 "FStar.Syntax.Util.fst"
let rec aux = (fun f _28_1046 -> (match (_28_1046) with
| (lid, arity) -> begin
(
# 747 "FStar.Syntax.Util.fst"
let _28_1049 = (head_and_args f)
in (match (_28_1049) with
| (t, args) -> begin
(
# 748 "FStar.Syntax.Util.fst"
let t = (un_uinst t)
in if ((is_constructor t lid) && ((FStar_List.length args) = arity)) then begin
Some (BaseConn ((lid, args)))
end else begin
None
end)
end))
end))
in (FStar_Util.find_map connectives (aux f)))))
in (
# 755 "FStar.Syntax.Util.fst"
let patterns = (fun t -> (
# 756 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(let _107_510 = (FStar_Syntax_Subst.compress t)
in (pats, _107_510))
end
| _28_1060 -> begin
(let _107_511 = (FStar_Syntax_Subst.compress t)
in ([], _107_511))
end)))
in (
# 761 "FStar.Syntax.Util.fst"
let destruct_q_conn = (fun t -> (
# 762 "FStar.Syntax.Util.fst"
let is_q = (fun fa fv -> if fa then begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end else begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)
in (
# 763 "FStar.Syntax.Util.fst"
let flat = (fun t -> (
# 764 "FStar.Syntax.Util.fst"
let _28_1070 = (head_and_args t)
in (match (_28_1070) with
| (t, args) -> begin
(let _107_523 = (un_uinst t)
in (let _107_522 = (FStar_All.pipe_right args (FStar_List.map (fun _28_1073 -> (match (_28_1073) with
| (t, imp) -> begin
(let _107_521 = (unascribe t)
in (_107_521, imp))
end))))
in (_107_523, _107_522)))
end)))
in (
# 766 "FStar.Syntax.Util.fst"
let rec aux = (fun qopt out t -> (match ((let _107_530 = (flat t)
in (qopt, _107_530))) with
| ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) | ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _::({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) | ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _::({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (Some (b), _28_1200) -> begin
(
# 778 "FStar.Syntax.Util.fst"
let bs = (FStar_List.rev out)
in (
# 779 "FStar.Syntax.Util.fst"
let _28_1205 = (FStar_Syntax_Subst.open_term bs t)
in (match (_28_1205) with
| (bs, t) -> begin
(
# 780 "FStar.Syntax.Util.fst"
let _28_1208 = (patterns t)
in (match (_28_1208) with
| (pats, body) -> begin
if b then begin
Some (QAll ((bs, pats, body)))
end else begin
Some (QEx ((bs, pats, body)))
end
end))
end)))
end
| _28_1210 -> begin
None
end))
in (aux None [] t)))))
in (
# 788 "FStar.Syntax.Util.fst"
let phi = (FStar_Syntax_Subst.compress f)
in (match ((destruct_base_conn phi)) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end))))))




