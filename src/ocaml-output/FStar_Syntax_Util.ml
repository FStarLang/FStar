
open Prims
# 29 "FStar.Syntax.Util.fst"
let handle_err : Prims.bool  ->  Prims.exn  ->  Prims.unit = (fun warning e -> (match (e) with
| FStar_Syntax_Syntax.Error (msg, r) -> begin
(let _127_6 = (let _127_5 = (FStar_Range.string_of_range r)
in (_127_5)::(if warning then begin
"Warning"
end else begin
"Error"
end)::(msg)::[])
in (FStar_Util.fprint FStar_Util.stderr "%s : %s\n%s\n" _127_6))
end
| FStar_Util.NYI (s) -> begin
(FStar_Util.fprint FStar_Util.stderr "Feature not yet implemented: %s" ((s)::[]))
end
| FStar_Syntax_Syntax.Err (s) -> begin
(FStar_Util.fprint FStar_Util.stderr "Error: %s" ((s)::[]))
end
| _38_23 -> begin
(Prims.raise e)
end))

# 39 "FStar.Syntax.Util.fst"
let handleable : Prims.exn  ->  Prims.bool = (fun _38_1 -> (match (_38_1) with
| (FStar_Syntax_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Syntax_Syntax.Err (_)) -> begin
true
end
| _38_35 -> begin
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
let arg_of_non_null_binder = (fun _38_41 -> (match (_38_41) with
| (b, imp) -> begin
(let _127_14 = (FStar_Syntax_Syntax.bv_to_name b)
in (_127_14, imp))
end))

# 59 "FStar.Syntax.Util.fst"
let args_of_non_null_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
[]
end else begin
(let _127_18 = (arg_of_non_null_binder b)
in (_127_18)::[])
end))))

# 64 "FStar.Syntax.Util.fst"
let args_of_binders : FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun binders -> (let _127_25 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
(
# 67 "FStar.Syntax.Util.fst"
let b = (let _127_22 = (FStar_Syntax_Syntax.new_bv None (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_127_22, (Prims.snd b)))
in (let _127_23 = (arg_of_non_null_binder b)
in (b, _127_23)))
end else begin
(let _127_24 = (arg_of_non_null_binder b)
in (b, _127_24))
end)))
in (FStar_All.pipe_right _127_25 FStar_List.unzip)))

# 71 "FStar.Syntax.Util.fst"
let name_binders : FStar_Syntax_Syntax.binder Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
(
# 74 "FStar.Syntax.Util.fst"
let _38_52 = b
in (match (_38_52) with
| (a, imp) -> begin
(
# 75 "FStar.Syntax.Util.fst"
let b = (let _127_31 = (let _127_30 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _127_30))
in (FStar_Ident.id_of_text _127_31))
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
(let _127_35 = (let _127_34 = (let _127_33 = (name_binders binders)
in (_127_33, comp))
in FStar_Syntax_Syntax.Tm_arrow (_127_34))
in (FStar_Syntax_Syntax.mk _127_35 None t.FStar_Syntax_Syntax.pos))
end
| _38_61 -> begin
t
end))

# 84 "FStar.Syntax.Util.fst"
let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _38_65 -> (match (_38_65) with
| (t, imp) -> begin
(let _127_40 = (let _127_39 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left Prims.fst _127_39))
in (_127_40, imp))
end)))))

# 87 "FStar.Syntax.Util.fst"
let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _38_69 -> (match (_38_69) with
| (t, imp) -> begin
(let _127_44 = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (_127_44, imp))
end)))))

# 90 "FStar.Syntax.Util.fst"
let binders_of_freevars : FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (let _127_47 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _127_47 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))

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
(FStar_List.map2 (fun _38_82 _38_86 -> (match ((_38_82, _38_86)) with
| ((x, _38_81), (y, _38_85)) -> begin
(let _127_63 = (let _127_62 = (FStar_Syntax_Syntax.bv_to_name y)
in (x, _127_62))
in FStar_Syntax_Syntax.NT (_127_63))
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
| _38_101 -> begin
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
let _38_115 = (univ_kernel u)
in (match (_38_115) with
| (k, n) -> begin
(k, (n + 1))
end))
end
| (FStar_Syntax_Syntax.U_max (_)) | (FStar_Syntax_Syntax.U_bvar (_)) -> begin
(FStar_All.failwith "Imposible")
end))

# 130 "FStar.Syntax.Util.fst"
let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (let _127_70 = (univ_kernel u)
in (Prims.snd _127_70)))

# 138 "FStar.Syntax.Util.fst"
let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match ((u1, u2)) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) -> begin
(FStar_All.failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
0
end
| (FStar_Syntax_Syntax.U_unknown, _38_142) -> begin
(- (1))
end
| (_38_145, FStar_Syntax_Syntax.U_unknown) -> begin
1
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
0
end
| (FStar_Syntax_Syntax.U_zero, _38_153) -> begin
(- (1))
end
| (_38_156, FStar_Syntax_Syntax.U_zero) -> begin
1
end
| (FStar_Syntax_Syntax.U_name (u1), FStar_Syntax_Syntax.U_name (u2)) -> begin
(FStar_String.compare u1.FStar_Ident.idText u2.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (_38_165), FStar_Syntax_Syntax.U_unif (_38_168)) -> begin
(- (1))
end
| (FStar_Syntax_Syntax.U_unif (_38_172), FStar_Syntax_Syntax.U_name (_38_175)) -> begin
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
let copt = (let _127_76 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map _127_76 (fun _38_192 -> (match (_38_192) with
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
| (FStar_Syntax_Syntax.U_max (_38_199), _38_202) -> begin
(- (1))
end
| (_38_205, FStar_Syntax_Syntax.U_max (_38_207)) -> begin
1
end
| _38_211 -> begin
(
# 175 "FStar.Syntax.Util.fst"
let _38_214 = (univ_kernel u1)
in (match (_38_214) with
| (k1, n1) -> begin
(
# 176 "FStar.Syntax.Util.fst"
let _38_217 = (univ_kernel u2)
in (match (_38_217) with
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
let ml_comp : FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (let _127_86 = (let _127_85 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_ML_lid r)
in {FStar_Syntax_Syntax.effect_name = _127_85; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]})
in (FStar_Syntax_Syntax.mk_Comp _127_86)))

# 204 "FStar.Syntax.Util.fst"
let comp_set_flags : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun c f -> (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (_)) | (FStar_Syntax_Syntax.GTotal (_)) -> begin
c
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 207 "FStar.Syntax.Util.fst"
let _38_233 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ((
# 207 "FStar.Syntax.Util.fst"
let _38_235 = ct
in {FStar_Syntax_Syntax.effect_name = _38_235.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _38_235.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _38_235.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})); FStar_Syntax_Syntax.tk = _38_233.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _38_233.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _38_233.FStar_Syntax_Syntax.vars})
end))

# 209 "FStar.Syntax.Util.fst"
let comp_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_38_239) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (_38_242) -> begin
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
| FStar_Syntax_Syntax.Total (_38_250) -> begin
FStar_Syntax_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (_38_253) -> begin
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
let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _38_2 -> (match (_38_2) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _38_267 -> begin
false
end)))))

# 228 "FStar.Syntax.Util.fst"
let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _38_3 -> (match (_38_3) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _38_273 -> begin
false
end))))))

# 230 "FStar.Syntax.Util.fst"
let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _38_4 -> (match (_38_4) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _38_279 -> begin
false
end))))))

# 234 "FStar.Syntax.Util.fst"
let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _38_5 -> (match (_38_5) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _38_285 -> begin
false
end)))))

# 236 "FStar.Syntax.Util.fst"
let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _38_6 -> (match (_38_6) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _38_291 -> begin
false
end)))))

# 238 "FStar.Syntax.Util.fst"
let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid (comp_effect_name c))))

# 242 "FStar.Syntax.Util.fst"
let is_pure_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Pure_lid)))

# 247 "FStar.Syntax.Util.fst"
let is_pure_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_38_296) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (_38_299) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _38_7 -> (match (_38_7) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _38_306 -> begin
false
end)))))
end))

# 254 "FStar.Syntax.Util.fst"
let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_Ghost_lid l)))

# 259 "FStar.Syntax.Util.fst"
let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))

# 261 "FStar.Syntax.Util.fst"
let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _38_8 -> (match (_38_8) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _38_313 -> begin
false
end))))))

# 266 "FStar.Syntax.Util.fst"
let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))

# 269 "FStar.Syntax.Util.fst"
let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _127_123 = (FStar_Syntax_Subst.compress t)
in _127_123.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_38_317, c) -> begin
(is_pure_or_ghost_comp c)
end
| _38_322 -> begin
true
end))

# 273 "FStar.Syntax.Util.fst"
let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _127_126 = (FStar_Syntax_Subst.compress t)
in _127_126.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_38_325, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid)
end
| _38_332 -> begin
false
end)
end
| _38_334 -> begin
false
end))

# 282 "FStar.Syntax.Util.fst"
let head_and_args : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.args) = (fun t -> (
# 283 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(head, args)
end
| _38_342 -> begin
(t, [])
end)))

# 288 "FStar.Syntax.Util.fst"
let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 289 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (t, _38_347) -> begin
(FStar_Syntax_Subst.compress t)
end
| _38_351 -> begin
t
end)))

# 294 "FStar.Syntax.Util.fst"
let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _127_133 = (FStar_Syntax_Subst.compress t)
in _127_133.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_38_354, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| _req::_ens::(pats, _38_364)::_38_361 -> begin
(
# 300 "FStar.Syntax.Util.fst"
let pats' = (unmeta pats)
in (
# 301 "FStar.Syntax.Util.fst"
let _38_375 = (head_and_args pats')
in (match (_38_375) with
| (head, _38_374) -> begin
(match ((let _127_134 = (un_uinst head)
in _127_134.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid)
end
| _38_379 -> begin
false
end)
end)))
end
| _38_381 -> begin
false
end)
end
| _38_383 -> begin
false
end)
end
| _38_385 -> begin
false
end))

# 312 "FStar.Syntax.Util.fst"
let is_ml_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _38_9 -> (match (_38_9) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _38_392 -> begin
false
end)))))
end
| _38_394 -> begin
false
end))

# 318 "FStar.Syntax.Util.fst"
let comp_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (t)) | (FStar_Syntax_Syntax.GTotal (t)) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))

# 323 "FStar.Syntax.Util.fst"
let set_result_typ = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_38_404) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (_38_407) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (
# 326 "FStar.Syntax.Util.fst"
let _38_411 = ct
in {FStar_Syntax_Syntax.effect_name = _38_411.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = _38_411.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _38_411.FStar_Syntax_Syntax.flags}))
end))

# 328 "FStar.Syntax.Util.fst"
let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _38_10 -> (match (_38_10) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _38_418 -> begin
false
end)))))

# 334 "FStar.Syntax.Util.fst"
let primops : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]

# 350 "FStar.Syntax.Util.fst"
let is_primop_lid : FStar_Ident.lident  ->  Prims.bool = (fun l -> (FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals l))))

# 352 "FStar.Syntax.Util.fst"
let is_primop = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_primop_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| _38_424 -> begin
false
end))

# 356 "FStar.Syntax.Util.fst"
let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (
# 357 "FStar.Syntax.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e, _38_429, _38_431) -> begin
(unascribe e)
end
| _38_435 -> begin
e
end)))

# 362 "FStar.Syntax.Util.fst"
let rec ascribe = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', _38_440, _38_442) -> begin
(ascribe t' k)
end
| _38_446 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((t, k, None))) None t.FStar_Syntax_Syntax.pos)
end))

# 366 "FStar.Syntax.Util.fst"
let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 367 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _38_451) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _38_456, _38_458) -> begin
(unrefine t)
end
| _38_462 -> begin
t
end)))

# 373 "FStar.Syntax.Util.fst"
let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (match ((let _127_153 = (FStar_Syntax_Subst.compress e)
in _127_153.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_38_465) -> begin
true
end
| _38_468 -> begin
false
end))

# 377 "FStar.Syntax.Util.fst"
let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _127_156 = (FStar_Syntax_Subst.compress t)
in _127_156.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_38_471) -> begin
true
end
| _38_474 -> begin
false
end))

# 381 "FStar.Syntax.Util.fst"
let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 382 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _38_479) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _38_484, _38_486) -> begin
(pre_typ t)
end
| _38_490 -> begin
t
end)))

# 388 "FStar.Syntax.Util.fst"
let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.args Prims.option = (fun typ lid -> (
# 389 "FStar.Syntax.Util.fst"
let typ = (FStar_Syntax_Subst.compress typ)
in (match ((let _127_163 = (un_uinst typ)
in _127_163.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 392 "FStar.Syntax.Util.fst"
let head = (un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
Some (args)
end
| _38_502 -> begin
None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
Some ([])
end
| _38_506 -> begin
None
end)))

# 400 "FStar.Syntax.Util.fst"
let rec lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_let (_, _, lids, _)) | (FStar_Syntax_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_datacon (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_declare_typ (lid, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (n, _)) | (FStar_Syntax_Syntax.Sig_new_effect (n, _)) -> begin
(n.FStar_Syntax_Syntax.mname)::[]
end
| (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) -> begin
[]
end))

# 414 "FStar.Syntax.Util.fst"
let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.option = (fun se -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _38_610 -> begin
None
end))

# 418 "FStar.Syntax.Util.fst"
let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Syntax_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_datacon (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_assume (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_let (_, r, _, _)) | (FStar_Syntax_Syntax.Sig_main (_, r)) | (FStar_Syntax_Syntax.Sig_pragma (_, r)) | (FStar_Syntax_Syntax.Sig_new_effect (_, r)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_, r)) | (FStar_Syntax_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))

# 432 "FStar.Syntax.Util.fst"
let range_of_lb = (fun _38_11 -> (match (_38_11) with
| (FStar_Util.Inl (x), _38_715, _38_717) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), _38_722, _38_724) -> begin
(FStar_Ident.range_of_lid l)
end))

# 436 "FStar.Syntax.Util.fst"
let range_of_arg = (fun _38_729 -> (match (_38_729) with
| (hd, _38_728) -> begin
hd.FStar_Syntax_Syntax.pos
end))

# 438 "FStar.Syntax.Util.fst"
let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))

# 441 "FStar.Syntax.Util.fst"
let mk_app = (fun f args -> (
# 442 "FStar.Syntax.Util.fst"
let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((f, args))) None r)))

# 445 "FStar.Syntax.Util.fst"
let mk_data = (fun l args -> (match (args) with
| [] -> begin
(let _127_182 = (let _127_181 = (let _127_180 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_127_180, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_127_181))
in (FStar_Syntax_Syntax.mk _127_182 None (FStar_Ident.range_of_lid l)))
end
| _38_741 -> begin
(
# 450 "FStar.Syntax.Util.fst"
let e = (let _127_183 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app _127_183 args))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))) None e.FStar_Syntax_Syntax.pos))
end))

# 453 "FStar.Syntax.Util.fst"
let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident ((Prims.strcat "^fname^" x.FStar_Ident.idText), x.FStar_Ident.idRange)))

# 454 "FStar.Syntax.Util.fst"
let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _127_189 = (let _127_188 = (FStar_Util.substring_from x.FStar_Ident.idText 7)
in (_127_188, x.FStar_Ident.idRange))
in (FStar_Ident.mk_ident _127_189))
end else begin
x
end)

# 459 "FStar.Syntax.Util.fst"
let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (
# 460 "FStar.Syntax.Util.fst"
let nm = if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _127_199 = (let _127_198 = (let _127_196 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _127_196))
in (let _127_197 = (FStar_Syntax_Syntax.range_of_bv x)
in (_127_198, _127_197)))
in (FStar_Ident.mk_ident _127_199))
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (
# 463 "FStar.Syntax.Util.fst"
let y = (
# 463 "FStar.Syntax.Util.fst"
let _38_749 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = _38_749.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _38_749.FStar_Syntax_Syntax.sort})
in (let _127_203 = (let _127_202 = (let _127_201 = (let _127_200 = (unmangle_field_name nm)
in (_127_200)::[])
in (FStar_List.append (FStar_Ident.ids_of_lid lid) _127_201))
in (FStar_Ident.lid_of_ids _127_202))
in (_127_203, y)))))

# 466 "FStar.Syntax.Util.fst"
let set_uvar = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (_38_755) -> begin
(let _127_208 = (let _127_207 = (let _127_206 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _127_206))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" _127_207))
in (FStar_All.failwith _127_208))
end
| _38_758 -> begin
(FStar_Unionfind.change uv (FStar_Syntax_Syntax.Fixed (t)))
end))

# 471 "FStar.Syntax.Util.fst"
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
| _38_784 -> begin
(q1 = q2)
end))

# 482 "FStar.Syntax.Util.fst"
let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (
# 483 "FStar.Syntax.Util.fst"
let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 486 "FStar.Syntax.Util.fst"
let _38_793 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_38_793) with
| (bs, c) -> begin
if (is_tot_or_gtot_comp c) then begin
(
# 488 "FStar.Syntax.Util.fst"
let _38_796 = (arrow_formals_comp (comp_result c))
in (match (_38_796) with
| (bs', k) -> begin
((FStar_List.append bs bs'), k)
end))
end else begin
(bs, c)
end
end))
end
| _38_798 -> begin
(let _127_215 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _127_215))
end)))

# 493 "FStar.Syntax.Util.fst"
let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.typ) = (fun k -> (
# 494 "FStar.Syntax.Util.fst"
let _38_802 = (arrow_formals_comp k)
in (match (_38_802) with
| (bs, c) -> begin
(bs, (comp_result c))
end)))

# 497 "FStar.Syntax.Util.fst"
let rec abs_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.term) = (fun t -> (match ((let _127_220 = (FStar_Syntax_Subst.compress t)
in _127_220.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, t, _38_807) -> begin
(
# 499 "FStar.Syntax.Util.fst"
let _38_812 = (abs_formals t)
in (match (_38_812) with
| (bs', t) -> begin
(FStar_Syntax_Subst.open_term (FStar_List.append bs bs') t)
end))
end
| _38_814 -> begin
([], t)
end))

# 503 "FStar.Syntax.Util.fst"
let abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> (match (bs) with
| [] -> begin
t
end
| _38_820 -> begin
(
# 506 "FStar.Syntax.Util.fst"
let body = (let _127_227 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress _127_227))
in (match ((body.FStar_Syntax_Syntax.n, lopt)) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t, lopt'), None) -> begin
(let _127_231 = (let _127_230 = (let _127_229 = (let _127_228 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append _127_228 bs'))
in (_127_229, t, lopt))
in FStar_Syntax_Syntax.Tm_abs (_127_230))
in (FStar_Syntax_Syntax.mk _127_231 None t.FStar_Syntax_Syntax.pos))
end
| _38_830 -> begin
(
# 511 "FStar.Syntax.Util.fst"
let lopt = (match (lopt) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt
end
| Some (FStar_Util.Inl (lc)) -> begin
(let _127_233 = (let _127_232 = (FStar_Syntax_Subst.close_lcomp bs lc)
in FStar_Util.Inl (_127_232))
in Some (_127_233))
end)
in (let _127_236 = (let _127_235 = (let _127_234 = (FStar_Syntax_Subst.close_binders bs)
in (_127_234, body, lopt))
in FStar_Syntax_Syntax.Tm_abs (_127_235))
in (FStar_Syntax_Syntax.mk _127_236 None t.FStar_Syntax_Syntax.pos)))
end))
end))

# 517 "FStar.Syntax.Util.fst"
let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| _38_844 -> begin
(let _127_244 = (let _127_243 = (let _127_242 = (FStar_Syntax_Subst.close_binders bs)
in (let _127_241 = (FStar_Syntax_Subst.close_comp bs c)
in (_127_242, _127_241)))
in FStar_Syntax_Syntax.Tm_arrow (_127_243))
in (FStar_Syntax_Syntax.mk _127_244 None c.FStar_Syntax_Syntax.pos))
end))

# 520 "FStar.Syntax.Util.fst"
let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun b t -> (let _127_256 = (let _127_252 = (let _127_251 = (let _127_250 = (let _127_249 = (FStar_Syntax_Syntax.mk_binder b)
in (_127_249)::[])
in (FStar_Syntax_Subst.close _127_250 t))
in (b, _127_251))
in FStar_Syntax_Syntax.Tm_refine (_127_252))
in (let _127_255 = (FStar_ST.read b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (let _127_254 = (let _127_253 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges _127_253 t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk _127_256 _127_255 _127_254)))))

# 521 "FStar.Syntax.Util.fst"
let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))

# 523 "FStar.Syntax.Util.fst"
let mk_letbinding : FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def})

# 530 "FStar.Syntax.Util.fst"
let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list Prims.option  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def -> (
# 531 "FStar.Syntax.Util.fst"
let def = (match ((recs, univ_vars)) with
| ((None, _)) | ((_, [])) -> begin
def
end
| (Some (fvs), _38_870) -> begin
(
# 535 "FStar.Syntax.Util.fst"
let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _127_281 -> FStar_Syntax_Syntax.U_name (_127_281))))
in (
# 536 "FStar.Syntax.Util.fst"
let inst = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, universes))))
in (FStar_Syntax_InstFV.instantiate inst def)))
end)
in (
# 538 "FStar.Syntax.Util.fst"
let typ = (FStar_Syntax_Subst.close_univ_vars univ_vars typ)
in (
# 539 "FStar.Syntax.Util.fst"
let def = (FStar_Syntax_Subst.close_univ_vars univ_vars def)
in (mk_letbinding lbname univ_vars typ eff def)))))

# 542 "FStar.Syntax.Util.fst"
let open_univ_vars_binders_and_comp : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 545 "FStar.Syntax.Util.fst"
let _38_884 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_38_884) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _38_886 -> begin
(
# 548 "FStar.Syntax.Util.fst"
let t' = (arrow binders c)
in (
# 549 "FStar.Syntax.Util.fst"
let _38_890 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_38_890) with
| (uvs, t') -> begin
(match ((let _127_289 = (FStar_Syntax_Subst.compress t')
in _127_289.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _38_896 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 557 "FStar.Syntax.Util.fst"
let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.starts_with fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.tuple")
end
| _38_901 -> begin
false
end))

# 561 "FStar.Syntax.Util.fst"
let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 562 "FStar.Syntax.Util.fst"
let t = (let _127_296 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "tuple%s" _127_296))
in (let _127_297 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _127_297 r))))

# 565 "FStar.Syntax.Util.fst"
let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 566 "FStar.Syntax.Util.fst"
let t = (let _127_302 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Mktuple%s" _127_302))
in (let _127_303 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _127_303 r))))

# 569 "FStar.Syntax.Util.fst"
let is_tuple_data_lid : FStar_Ident.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _127_308 = (mk_tuple_data_lid n FStar_Range.dummyRange)
in (FStar_Ident.lid_equals f _127_308)))

# 572 "FStar.Syntax.Util.fst"
let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.starts_with fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.dtuple")
end
| _38_914 -> begin
false
end))

# 576 "FStar.Syntax.Util.fst"
let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 577 "FStar.Syntax.Util.fst"
let t = (let _127_315 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "dtuple%s" _127_315))
in (let _127_316 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _127_316 r))))

# 580 "FStar.Syntax.Util.fst"
let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 581 "FStar.Syntax.Util.fst"
let t = (let _127_321 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Mkdtuple%s" _127_321))
in (let _127_322 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _127_322 r))))

# 584 "FStar.Syntax.Util.fst"
let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> (FStar_Ident.lid_equals x FStar_Syntax_Const.eq2_lid))

# 586 "FStar.Syntax.Util.fst"
let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.forall_lid))

# 587 "FStar.Syntax.Util.fst"
let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.exists_lid))

# 588 "FStar.Syntax.Util.fst"
let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))

# 589 "FStar.Syntax.Util.fst"
let is_equality = (fun x -> (is_lid_equality x.FStar_Syntax_Syntax.v))

# 591 "FStar.Syntax.Util.fst"
let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (
# 592 "FStar.Syntax.Util.fst"
let lst = (FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.not_lid)::(FStar_Syntax_Const.iff_lid)::(FStar_Syntax_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))

# 596 "FStar.Syntax.Util.fst"
let is_constructor : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _127_338 = (pre_typ t)
in _127_338.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| _38_933 -> begin
false
end))

# 601 "FStar.Syntax.Util.fst"
let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _127_343 = (pre_typ t)
in _127_343.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (_38_937) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t, _38_941) -> begin
(is_constructed_typ t lid)
end
| _38_945 -> begin
false
end))

# 606 "FStar.Syntax.Util.fst"
let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun t -> (
# 607 "FStar.Syntax.Util.fst"
let t = (pre_typ t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_app (t, _38_959) -> begin
(get_tycon t)
end
| _38_963 -> begin
None
end)))

# 615 "FStar.Syntax.Util.fst"
let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _38_969 _38_973 -> (match ((_38_969, _38_973)) with
| ((fn1, _38_968), (fn2, _38_972)) -> begin
(FStar_String.compare (FStar_Ident.text_of_lid fn1) (FStar_Ident.text_of_lid fn2))
end)))))

# 622 "FStar.Syntax.Util.fst"
let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (
# 623 "FStar.Syntax.Util.fst"
let theory_syms = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))

# 645 "FStar.Syntax.Util.fst"
let ktype : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None FStar_Range.dummyRange)

# 646 "FStar.Syntax.Util.fst"
let ktype0 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) None FStar_Range.dummyRange)

# 649 "FStar.Syntax.Util.fst"
let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun _38_976 -> (match (()) with
| () -> begin
(
# 650 "FStar.Syntax.Util.fst"
let u = (let _127_354 = (FStar_Unionfind.fresh None)
in (FStar_All.pipe_left (fun _127_353 -> FStar_Syntax_Syntax.U_unif (_127_353)) _127_354))
in (let _127_355 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None FStar_Range.dummyRange)
in (_127_355, u)))
end))

# 653 "FStar.Syntax.Util.fst"
let kt_kt : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Const.kunary ktype0 ktype0)

# 654 "FStar.Syntax.Util.fst"
let kt_kt_kt : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Const.kbin ktype0 ktype0 ktype0)

# 656 "FStar.Syntax.Util.fst"
let fvar_const : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun l -> (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant None))

# 657 "FStar.Syntax.Util.fst"
let tand : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.and_lid)

# 658 "FStar.Syntax.Util.fst"
let tor : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.or_lid)

# 659 "FStar.Syntax.Util.fst"
let timp : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.imp_lid)

# 660 "FStar.Syntax.Util.fst"
let tiff : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.iff_lid)

# 661 "FStar.Syntax.Util.fst"
let t_bool : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.bool_lid)

# 662 "FStar.Syntax.Util.fst"
let t_false : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.false_lid)

# 663 "FStar.Syntax.Util.fst"
let t_true : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.true_lid)

# 664 "FStar.Syntax.Util.fst"
let b2t_v : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.b2t_lid)

# 665 "FStar.Syntax.Util.fst"
let t_not : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.not_lid)

# 667 "FStar.Syntax.Util.fst"
let mk_conj_opt : FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _127_369 = (let _127_368 = (let _127_366 = (let _127_365 = (let _127_364 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _127_363 = (let _127_362 = (FStar_Syntax_Syntax.as_arg phi2)
in (_127_362)::[])
in (_127_364)::_127_363))
in (tand, _127_365))
in FStar_Syntax_Syntax.Tm_app (_127_366))
in (let _127_367 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _127_368 None _127_367)))
in Some (_127_369))
end))

# 670 "FStar.Syntax.Util.fst"
let mk_binop = (fun op_t phi1 phi2 -> (let _127_379 = (let _127_377 = (let _127_376 = (let _127_375 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _127_374 = (let _127_373 = (FStar_Syntax_Syntax.as_arg phi2)
in (_127_373)::[])
in (_127_375)::_127_374))
in (op_t, _127_376))
in FStar_Syntax_Syntax.Tm_app (_127_377))
in (let _127_378 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _127_379 None _127_378))))

# 671 "FStar.Syntax.Util.fst"
let mk_neg = (fun phi -> (let _127_384 = (let _127_383 = (let _127_382 = (let _127_381 = (FStar_Syntax_Syntax.as_arg phi)
in (_127_381)::[])
in (t_not, _127_382))
in FStar_Syntax_Syntax.Tm_app (_127_383))
in (FStar_Syntax_Syntax.mk _127_384 None phi.FStar_Syntax_Syntax.pos)))

# 672 "FStar.Syntax.Util.fst"
let mk_conj = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))

# 673 "FStar.Syntax.Util.fst"
let mk_conj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
end
| hd::tl -> begin
(FStar_List.fold_right mk_conj tl hd)
end))

# 676 "FStar.Syntax.Util.fst"
let mk_disj = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))

# 677 "FStar.Syntax.Util.fst"
let mk_disj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
t_false
end
| hd::tl -> begin
(FStar_List.fold_right mk_disj tl hd)
end))

# 680 "FStar.Syntax.Util.fst"
let mk_imp : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (match ((let _127_397 = (FStar_Syntax_Subst.compress phi1)
in _127_397.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid) -> begin
t_true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
phi2
end
| _38_1009 -> begin
(match ((let _127_398 = (FStar_Syntax_Subst.compress phi2)
in _127_398.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when ((FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) || (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid)) -> begin
phi2
end
| _38_1013 -> begin
(mk_binop timp phi1 phi2)
end)
end))

# 690 "FStar.Syntax.Util.fst"
let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))

# 691 "FStar.Syntax.Util.fst"
let b2t = (fun e -> (let _127_405 = (let _127_404 = (let _127_403 = (let _127_402 = (FStar_Syntax_Syntax.as_arg e)
in (_127_402)::[])
in (b2t_v, _127_403))
in FStar_Syntax_Syntax.Tm_app (_127_404))
in (FStar_Syntax_Syntax.mk _127_405 None e.FStar_Syntax_Syntax.pos)))

# 693 "FStar.Syntax.Util.fst"
let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.eq2_lid)

# 695 "FStar.Syntax.Util.fst"
let mk_eq = (fun t1 t2 e1 e2 -> (let _127_416 = (let _127_414 = (let _127_413 = (let _127_412 = (FStar_Syntax_Syntax.as_arg e1)
in (let _127_411 = (let _127_410 = (FStar_Syntax_Syntax.as_arg e2)
in (_127_410)::[])
in (_127_412)::_127_411))
in (teq, _127_413))
in FStar_Syntax_Syntax.Tm_app (_127_414))
in (let _127_415 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _127_416 None _127_415))))

# 697 "FStar.Syntax.Util.fst"
let mk_has_type = (fun t x t' -> (
# 698 "FStar.Syntax.Util.fst"
let t_has_type = (fvar_const FStar_Syntax_Const.has_type_lid)
in (
# 699 "FStar.Syntax.Util.fst"
let t_has_type = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((t_has_type, (FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]))) None FStar_Range.dummyRange)
in (let _127_427 = (let _127_426 = (let _127_425 = (let _127_424 = (FStar_Syntax_Syntax.iarg t)
in (let _127_423 = (let _127_422 = (FStar_Syntax_Syntax.as_arg x)
in (let _127_421 = (let _127_420 = (FStar_Syntax_Syntax.as_arg t')
in (_127_420)::[])
in (_127_422)::_127_421))
in (_127_424)::_127_423))
in (t_has_type, _127_425))
in FStar_Syntax_Syntax.Tm_app (_127_426))
in (FStar_Syntax_Syntax.mk _127_427 None FStar_Range.dummyRange)))))

# 702 "FStar.Syntax.Util.fst"
let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.lex_t_lid)

# 703 "FStar.Syntax.Util.fst"
let lex_top : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lextop_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))

# 704 "FStar.Syntax.Util.fst"
let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lexcons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))

# 705 "FStar.Syntax.Util.fst"
let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.forall_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)

# 707 "FStar.Syntax.Util.fst"
let lcomp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (
# 708 "FStar.Syntax.Util.fst"
let c = (comp_to_comp_typ c0)
in {FStar_Syntax_Syntax.eff_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.res_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.cflags = c.FStar_Syntax_Syntax.flags; FStar_Syntax_Syntax.comp = (fun _38_1028 -> (match (()) with
| () -> begin
c0
end))}))

# 714 "FStar.Syntax.Util.fst"
let mk_forall : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun x body -> (let _127_445 = (let _127_444 = (let _127_443 = (let _127_442 = (let _127_441 = (let _127_440 = (let _127_435 = (FStar_Syntax_Syntax.mk_binder x)
in (_127_435)::[])
in (let _127_439 = (let _127_438 = (let _127_437 = (let _127_436 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (FStar_All.pipe_left lcomp_of_comp _127_436))
in FStar_Util.Inl (_127_437))
in Some (_127_438))
in (abs _127_440 body _127_439)))
in (FStar_Syntax_Syntax.as_arg _127_441))
in (_127_442)::[])
in (tforall, _127_443))
in FStar_Syntax_Syntax.Tm_app (_127_444))
in (FStar_Syntax_Syntax.mk _127_445 None FStar_Range.dummyRange)))

# 717 "FStar.Syntax.Util.fst"
let rec close_forall : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
f
end else begin
(mk_forall (Prims.fst b) f)
end) bs f))

# 720 "FStar.Syntax.Util.fst"
let rec is_wild_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (_38_1037) -> begin
true
end
| _38_1040 -> begin
false
end))

# 725 "FStar.Syntax.Util.fst"
let if_then_else = (fun b t1 t2 -> (
# 726 "FStar.Syntax.Util.fst"
let then_branch = (let _127_456 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t1.FStar_Syntax_Syntax.pos)
in (_127_456, None, t1))
in (
# 727 "FStar.Syntax.Util.fst"
let else_branch = (let _127_457 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Syntax_Syntax.pos)
in (_127_457, None, t2))
in (let _127_459 = (let _127_458 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos _127_458))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((b, (then_branch)::(else_branch)::[]))) None _127_459)))))

# 733 "FStar.Syntax.Util.fst"
type qpats =
FStar_Syntax_Syntax.args Prims.list

# 734 "FStar.Syntax.Util.fst"
type connective =
| QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args)

# 735 "FStar.Syntax.Util.fst"
let is_QAll = (fun _discr_ -> (match (_discr_) with
| QAll (_) -> begin
true
end
| _ -> begin
false
end))

# 736 "FStar.Syntax.Util.fst"
let is_QEx = (fun _discr_ -> (match (_discr_) with
| QEx (_) -> begin
true
end
| _ -> begin
false
end))

# 737 "FStar.Syntax.Util.fst"
let is_BaseConn = (fun _discr_ -> (match (_discr_) with
| BaseConn (_) -> begin
true
end
| _ -> begin
false
end))

# 735 "FStar.Syntax.Util.fst"
let ___QAll____0 = (fun projectee -> (match (projectee) with
| QAll (_38_1048) -> begin
_38_1048
end))

# 736 "FStar.Syntax.Util.fst"
let ___QEx____0 = (fun projectee -> (match (projectee) with
| QEx (_38_1051) -> begin
_38_1051
end))

# 737 "FStar.Syntax.Util.fst"
let ___BaseConn____0 = (fun projectee -> (match (projectee) with
| BaseConn (_38_1054) -> begin
_38_1054
end))

# 739 "FStar.Syntax.Util.fst"
let destruct_typ_as_formula : FStar_Syntax_Syntax.term  ->  connective Prims.option = (fun f -> (
# 740 "FStar.Syntax.Util.fst"
let destruct_base_conn = (fun f -> (
# 741 "FStar.Syntax.Util.fst"
let connectives = ((FStar_Syntax_Const.true_lid, 0))::((FStar_Syntax_Const.false_lid, 0))::((FStar_Syntax_Const.and_lid, 2))::((FStar_Syntax_Const.or_lid, 2))::((FStar_Syntax_Const.imp_lid, 2))::((FStar_Syntax_Const.iff_lid, 2))::((FStar_Syntax_Const.ite_lid, 3))::((FStar_Syntax_Const.not_lid, 1))::((FStar_Syntax_Const.eq2_lid, 4))::((FStar_Syntax_Const.eq2_lid, 2))::[]
in (
# 752 "FStar.Syntax.Util.fst"
let rec aux = (fun f _38_1063 -> (match (_38_1063) with
| (lid, arity) -> begin
(
# 753 "FStar.Syntax.Util.fst"
let _38_1066 = (head_and_args f)
in (match (_38_1066) with
| (t, args) -> begin
(
# 754 "FStar.Syntax.Util.fst"
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
# 761 "FStar.Syntax.Util.fst"
let patterns = (fun t -> (
# 762 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(let _127_512 = (FStar_Syntax_Subst.compress t)
in (pats, _127_512))
end
| _38_1077 -> begin
(let _127_513 = (FStar_Syntax_Subst.compress t)
in ([], _127_513))
end)))
in (
# 767 "FStar.Syntax.Util.fst"
let destruct_q_conn = (fun t -> (
# 768 "FStar.Syntax.Util.fst"
let is_q = (fun fa fv -> if fa then begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end else begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)
in (
# 769 "FStar.Syntax.Util.fst"
let flat = (fun t -> (
# 770 "FStar.Syntax.Util.fst"
let _38_1087 = (head_and_args t)
in (match (_38_1087) with
| (t, args) -> begin
(let _127_525 = (un_uinst t)
in (let _127_524 = (FStar_All.pipe_right args (FStar_List.map (fun _38_1090 -> (match (_38_1090) with
| (t, imp) -> begin
(let _127_523 = (unascribe t)
in (_127_523, imp))
end))))
in (_127_525, _127_524)))
end)))
in (
# 772 "FStar.Syntax.Util.fst"
let rec aux = (fun qopt out t -> (match ((let _127_532 = (flat t)
in (qopt, _127_532))) with
| ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) | ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _::({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) | ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _::({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (Some (b), _38_1217) -> begin
(
# 784 "FStar.Syntax.Util.fst"
let bs = (FStar_List.rev out)
in (
# 785 "FStar.Syntax.Util.fst"
let _38_1222 = (FStar_Syntax_Subst.open_term bs t)
in (match (_38_1222) with
| (bs, t) -> begin
(
# 786 "FStar.Syntax.Util.fst"
let _38_1225 = (patterns t)
in (match (_38_1225) with
| (pats, body) -> begin
if b then begin
Some (QAll ((bs, pats, body)))
end else begin
Some (QEx ((bs, pats, body)))
end
end))
end)))
end
| _38_1227 -> begin
None
end))
in (aux None [] t)))))
in (
# 794 "FStar.Syntax.Util.fst"
let phi = (FStar_Syntax_Subst.compress f)
in (match ((destruct_base_conn phi)) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end))))))




