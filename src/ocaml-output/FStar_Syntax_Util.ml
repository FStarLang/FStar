
open Prims
# 29 "FStar.Syntax.Util.fst"
let handle_err : Prims.bool  ->  Prims.unit  ->  Prims.exn  ->  Prims.unit = (fun warning ret e -> (match (e) with
| FStar_Syntax_Syntax.Error (msg, r) -> begin
(
# 32 "FStar.Syntax.Util.fst"
let _35_19 = (let _114_8 = (let _114_7 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s : %s\n%s\n" _114_7 (if warning then begin
"Warning"
end else begin
"Error"
end) msg))
in (FStar_Util.print_string _114_8))
in ())
end
| FStar_Util.NYI (s) -> begin
(
# 35 "FStar.Syntax.Util.fst"
let _35_23 = (let _114_9 = (FStar_Util.format1 "Feature not yet implemented: %s" s)
in (FStar_Util.print_string _114_9))
in ())
end
| FStar_Syntax_Syntax.Err (s) -> begin
(let _114_10 = (FStar_Util.format1 "Error: %s" s)
in (FStar_Util.print_string _114_10))
end
| _35_28 -> begin
(Prims.raise e)
end))

# 41 "FStar.Syntax.Util.fst"
let handleable : Prims.exn  ->  Prims.bool = (fun _35_1 -> (match (_35_1) with
| (FStar_Syntax_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Syntax_Syntax.Err (_)) -> begin
true
end
| _35_40 -> begin
false
end))

# 52 "FStar.Syntax.Util.fst"
let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.mk_ident ((Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText), lid.FStar_Ident.ident.FStar_Ident.idRange)))::[]))))

# 55 "FStar.Syntax.Util.fst"
let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (
# 56 "FStar.Syntax.Util.fst"
let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText 0)
in (FStar_Util.is_upper c)))

# 59 "FStar.Syntax.Util.fst"
let arg_of_non_null_binder = (fun _35_46 -> (match (_35_46) with
| (b, imp) -> begin
(let _114_18 = (FStar_Syntax_Syntax.bv_to_name b)
in (_114_18, imp))
end))

# 61 "FStar.Syntax.Util.fst"
let args_of_non_null_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
[]
end else begin
(let _114_22 = (arg_of_non_null_binder b)
in (_114_22)::[])
end))))

# 66 "FStar.Syntax.Util.fst"
let args_of_binders : FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun binders -> (let _114_29 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
(
# 69 "FStar.Syntax.Util.fst"
let b = (let _114_26 = (FStar_Syntax_Syntax.new_bv None (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_114_26, (Prims.snd b)))
in (let _114_27 = (arg_of_non_null_binder b)
in (b, _114_27)))
end else begin
(let _114_28 = (arg_of_non_null_binder b)
in (b, _114_28))
end)))
in (FStar_All.pipe_right _114_29 FStar_List.unzip)))

# 73 "FStar.Syntax.Util.fst"
let name_binders : FStar_Syntax_Syntax.binder Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
(
# 76 "FStar.Syntax.Util.fst"
let _35_57 = b
in (match (_35_57) with
| (a, imp) -> begin
(
# 77 "FStar.Syntax.Util.fst"
let b = (let _114_35 = (let _114_34 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _114_34))
in (FStar_Ident.id_of_text _114_35))
in (
# 78 "FStar.Syntax.Util.fst"
let b = {FStar_Syntax_Syntax.ppname = b; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = a.FStar_Syntax_Syntax.sort}
in (b, imp)))
end))
end else begin
b
end))))

# 82 "FStar.Syntax.Util.fst"
let name_function_binders = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _114_39 = (let _114_38 = (let _114_37 = (name_binders binders)
in (_114_37, comp))
in FStar_Syntax_Syntax.Tm_arrow (_114_38))
in (FStar_Syntax_Syntax.mk _114_39 None t.FStar_Syntax_Syntax.pos))
end
| _35_66 -> begin
t
end))

# 86 "FStar.Syntax.Util.fst"
let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _35_70 -> (match (_35_70) with
| (t, imp) -> begin
(let _114_44 = (let _114_43 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left Prims.fst _114_43))
in (_114_44, imp))
end)))))

# 89 "FStar.Syntax.Util.fst"
let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _35_74 -> (match (_35_74) with
| (t, imp) -> begin
(let _114_48 = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (_114_48, imp))
end)))))

# 92 "FStar.Syntax.Util.fst"
let binders_of_freevars : (FStar_Syntax_Syntax.bv Prims.list * (FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  Prims.bool))  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (let _114_57 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _114_57 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))

# 94 "FStar.Syntax.Util.fst"
let mk_subst = (fun s -> (s)::[])

# 96 "FStar.Syntax.Util.fst"
let subst_formal : FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.arg  ->  FStar_Syntax_Syntax.subst_elt = (fun f a -> FStar_Syntax_Syntax.DB ((0, (Prims.fst a))))

# 97 "FStar.Syntax.Util.fst"
let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> if ((FStar_List.length formals) = (FStar_List.length actuals)) then begin
(let _114_70 = (FStar_List.fold_right2 (fun f a _35_85 -> (match (_35_85) with
| (n, out) -> begin
((n + 1), (FStar_Syntax_Syntax.DB ((n, (Prims.fst a))))::out)
end)) formals actuals (0, []))
in (FStar_All.pipe_right _114_70 Prims.snd))
end else begin
(FStar_All.failwith "Ill-formed substitution")
end)

# 105 "FStar.Syntax.Util.fst"
let rec unmeta : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (
# 106 "FStar.Syntax.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_meta (e, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e, _, _)) -> begin
(unmeta e)
end
| _35_100 -> begin
e
end)))

# 118 "FStar.Syntax.Util.fst"
let rec univ_kernel : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.universe * Prims.int) = (fun u -> (match (u) with
| (FStar_Syntax_Syntax.U_unknown) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
(u, 0)
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(
# 123 "FStar.Syntax.Util.fst"
let _35_114 = (univ_kernel u)
in (match (_35_114) with
| (k, n) -> begin
(k, (n + 1))
end))
end
| (FStar_Syntax_Syntax.U_max (_)) | (FStar_Syntax_Syntax.U_bvar (_)) -> begin
(FStar_All.failwith "Imposible")
end))

# 129 "FStar.Syntax.Util.fst"
let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (let _114_77 = (univ_kernel u)
in (Prims.snd _114_77)))

# 137 "FStar.Syntax.Util.fst"
let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match ((u1, u2)) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) -> begin
(FStar_All.failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
0
end
| (FStar_Syntax_Syntax.U_unknown, _35_141) -> begin
(- (1))
end
| (_35_144, FStar_Syntax_Syntax.U_unknown) -> begin
1
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
0
end
| (FStar_Syntax_Syntax.U_zero, _35_152) -> begin
(- (1))
end
| (_35_155, FStar_Syntax_Syntax.U_zero) -> begin
1
end
| (FStar_Syntax_Syntax.U_name (u1), FStar_Syntax_Syntax.U_name (u2)) -> begin
(FStar_String.compare u1.FStar_Ident.idText u2.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (_35_164), FStar_Syntax_Syntax.U_unif (_35_167)) -> begin
(- (1))
end
| (FStar_Syntax_Syntax.U_unif (_35_171), FStar_Syntax_Syntax.U_name (_35_174)) -> begin
1
end
| (FStar_Syntax_Syntax.U_unif (u1), FStar_Syntax_Syntax.U_unif (u2)) -> begin
((FStar_Unionfind.uvar_id u1) - (FStar_Unionfind.uvar_id u2))
end
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(
# 156 "FStar.Syntax.Util.fst"
let n1 = (FStar_List.length us1)
in (
# 157 "FStar.Syntax.Util.fst"
let n2 = (FStar_List.length us2)
in if (n1 <> n2) then begin
(n1 - n2)
end else begin
(
# 160 "FStar.Syntax.Util.fst"
let copt = (let _114_83 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map _114_83 (fun _35_191 -> (match (_35_191) with
| (u1, u2) -> begin
(
# 161 "FStar.Syntax.Util.fst"
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
| (FStar_Syntax_Syntax.U_max (_35_198), _35_201) -> begin
(- (1))
end
| (_35_204, FStar_Syntax_Syntax.U_max (_35_206)) -> begin
1
end
| _35_210 -> begin
(
# 174 "FStar.Syntax.Util.fst"
let _35_213 = (univ_kernel u1)
in (match (_35_213) with
| (k1, n1) -> begin
(
# 175 "FStar.Syntax.Util.fst"
let _35_216 = (univ_kernel u2)
in (match (_35_216) with
| (k2, n2) -> begin
(
# 176 "FStar.Syntax.Util.fst"
let r = (compare_univs k1 k2)
in if (r = 0) then begin
(n1 - n2)
end else begin
r
end)
end))
end))
end))

# 181 "FStar.Syntax.Util.fst"
let eq_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.bool = (fun u1 u2 -> ((compare_univs u1 u2) = 0))

# 187 "FStar.Syntax.Util.fst"
let ml_comp : FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (let _114_93 = (let _114_92 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_ML_lid r)
in {FStar_Syntax_Syntax.effect_name = _114_92; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]})
in (FStar_Syntax_Syntax.mk_Comp _114_93)))

# 203 "FStar.Syntax.Util.fst"
let comp_set_flags : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun c f -> (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (_)) | (FStar_Syntax_Syntax.GTotal (_)) -> begin
c
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 206 "FStar.Syntax.Util.fst"
let _35_232 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ((
# 206 "FStar.Syntax.Util.fst"
let _35_234 = ct
in {FStar_Syntax_Syntax.effect_name = _35_234.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _35_234.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _35_234.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})); FStar_Syntax_Syntax.tk = _35_232.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _35_232.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _35_232.FStar_Syntax_Syntax.vars})
end))

# 208 "FStar.Syntax.Util.fst"
let comp_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_35_238) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (_35_241) -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.flags
end))

# 213 "FStar.Syntax.Util.fst"
let comp_effect_name = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
c.FStar_Syntax_Syntax.effect_name
end
| FStar_Syntax_Syntax.Total (_35_249) -> begin
FStar_Syntax_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (_35_252) -> begin
FStar_Syntax_Const.effect_GTot_lid
end))

# 218 "FStar.Syntax.Util.fst"
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

# 224 "FStar.Syntax.Util.fst"
let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _35_2 -> (match (_35_2) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _35_266 -> begin
false
end)))))

# 227 "FStar.Syntax.Util.fst"
let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _35_3 -> (match (_35_3) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _35_272 -> begin
false
end))))))

# 229 "FStar.Syntax.Util.fst"
let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _35_4 -> (match (_35_4) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _35_278 -> begin
false
end))))))

# 233 "FStar.Syntax.Util.fst"
let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _35_5 -> (match (_35_5) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _35_284 -> begin
false
end)))))

# 235 "FStar.Syntax.Util.fst"
let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _35_6 -> (match (_35_6) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _35_290 -> begin
false
end)))))

# 237 "FStar.Syntax.Util.fst"
let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid (comp_effect_name c))))

# 241 "FStar.Syntax.Util.fst"
let is_pure_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_35_294) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (_35_297) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
((((is_total_comp c) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Pure_lid)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _35_7 -> (match (_35_7) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _35_304 -> begin
false
end)))))
end))

# 249 "FStar.Syntax.Util.fst"
let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_Ghost_lid l)))

# 254 "FStar.Syntax.Util.fst"
let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))

# 256 "FStar.Syntax.Util.fst"
let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((((is_total_lcomp lc) || (FStar_Ident.lid_equals lc.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals lc.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Pure_lid)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _35_8 -> (match (_35_8) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _35_311 -> begin
false
end))))))

# 262 "FStar.Syntax.Util.fst"
let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))

# 265 "FStar.Syntax.Util.fst"
let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _114_128 = (FStar_Syntax_Subst.compress t)
in _114_128.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_35_315, c) -> begin
(is_pure_or_ghost_comp c)
end
| _35_320 -> begin
true
end))

# 269 "FStar.Syntax.Util.fst"
let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _114_131 = (FStar_Syntax_Subst.compress t)
in _114_131.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_35_323, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid)
end
| _35_330 -> begin
false
end)
end
| _35_332 -> begin
false
end))

# 278 "FStar.Syntax.Util.fst"
let head_and_args : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.args) = (fun t -> (
# 279 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(head, args)
end
| _35_340 -> begin
(t, [])
end)))

# 284 "FStar.Syntax.Util.fst"
let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (match ((let _114_136 = (FStar_Syntax_Subst.compress t)
in _114_136.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (t, _35_344) -> begin
t
end
| _35_348 -> begin
t
end))

# 288 "FStar.Syntax.Util.fst"
let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _114_139 = (FStar_Syntax_Subst.compress t)
in _114_139.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_35_351, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| _req::_ens::(pats, _35_361)::_35_358 -> begin
(
# 294 "FStar.Syntax.Util.fst"
let pats' = (unmeta pats)
in (
# 295 "FStar.Syntax.Util.fst"
let _35_372 = (head_and_args pats')
in (match (_35_372) with
| (head, _35_371) -> begin
(match ((let _114_140 = (un_uinst head)
in _114_140.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _35_375) -> begin
(FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.cons_lid)
end
| _35_379 -> begin
false
end)
end)))
end
| _35_381 -> begin
false
end)
end
| _35_383 -> begin
false
end)
end
| _35_385 -> begin
false
end))

# 306 "FStar.Syntax.Util.fst"
let is_ml_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _35_9 -> (match (_35_9) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _35_392 -> begin
false
end)))))
end
| _35_394 -> begin
false
end))

# 312 "FStar.Syntax.Util.fst"
let comp_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (t)) | (FStar_Syntax_Syntax.GTotal (t)) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))

# 317 "FStar.Syntax.Util.fst"
let set_result_typ = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_35_404) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (_35_407) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (
# 320 "FStar.Syntax.Util.fst"
let _35_411 = ct
in {FStar_Syntax_Syntax.effect_name = _35_411.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = _35_411.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _35_411.FStar_Syntax_Syntax.flags}))
end))

# 322 "FStar.Syntax.Util.fst"
let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _35_10 -> (match (_35_10) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _35_418 -> begin
false
end)))))

# 328 "FStar.Syntax.Util.fst"
let primops : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]

# 345 "FStar.Syntax.Util.fst"
let is_primop = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _35_422) -> begin
(FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v)))
end
| _35_426 -> begin
false
end))

# 349 "FStar.Syntax.Util.fst"
let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (
# 350 "FStar.Syntax.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e, _35_431, _35_433) -> begin
(unascribe e)
end
| _35_437 -> begin
e
end)))

# 355 "FStar.Syntax.Util.fst"
let rec ascribe = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', _35_442, _35_444) -> begin
(ascribe t' k)
end
| _35_448 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((t, k, None))) None t.FStar_Syntax_Syntax.pos)
end))

# 359 "FStar.Syntax.Util.fst"
let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 360 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _35_453) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _35_458, _35_460) -> begin
(unrefine t)
end
| _35_464 -> begin
t
end)))

# 366 "FStar.Syntax.Util.fst"
let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (match ((let _114_157 = (FStar_Syntax_Subst.compress e)
in _114_157.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_35_467) -> begin
true
end
| _35_470 -> begin
false
end))

# 370 "FStar.Syntax.Util.fst"
let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _114_160 = (FStar_Syntax_Subst.compress t)
in _114_160.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_35_473) -> begin
true
end
| _35_476 -> begin
false
end))

# 374 "FStar.Syntax.Util.fst"
let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 375 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _35_481) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _35_486, _35_488) -> begin
(pre_typ t)
end
| _35_492 -> begin
t
end)))

# 381 "FStar.Syntax.Util.fst"
let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.args Prims.option = (fun typ lid -> (
# 382 "FStar.Syntax.Util.fst"
let typ = (FStar_Syntax_Subst.compress typ)
in (match (typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _35_504); FStar_Syntax_Syntax.tk = _35_501; FStar_Syntax_Syntax.pos = _35_499; FStar_Syntax_Syntax.vars = _35_497}, args) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v lid) -> begin
Some (args)
end
| FStar_Syntax_Syntax.Tm_fvar (tc, _35_513) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v lid) -> begin
Some ([])
end
| _35_517 -> begin
None
end)))

# 388 "FStar.Syntax.Util.fst"
let rec lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_let (_, _, lids, _)) | (FStar_Syntax_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_datacon (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_declare_typ (lid, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n, _35_601) -> begin
(n.FStar_Syntax_Syntax.mname)::[]
end
| (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) -> begin
[]
end))

# 401 "FStar.Syntax.Util.fst"
let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.option = (fun se -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _35_617 -> begin
None
end))

# 405 "FStar.Syntax.Util.fst"
let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Syntax_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_datacon (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_assume (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_let (_, r, _, _)) | (FStar_Syntax_Syntax.Sig_main (_, r)) | (FStar_Syntax_Syntax.Sig_pragma (_, r)) | (FStar_Syntax_Syntax.Sig_new_effect (_, r)) | (FStar_Syntax_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))

# 418 "FStar.Syntax.Util.fst"
let range_of_lb = (fun _35_11 -> (match (_35_11) with
| (FStar_Util.Inl (x), _35_718, _35_720) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), _35_725, _35_727) -> begin
(FStar_Ident.range_of_lid l)
end))

# 422 "FStar.Syntax.Util.fst"
let range_of_arg = (fun _35_732 -> (match (_35_732) with
| (hd, _35_731) -> begin
hd.FStar_Syntax_Syntax.pos
end))

# 424 "FStar.Syntax.Util.fst"
let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))

# 427 "FStar.Syntax.Util.fst"
let mk_app = (fun f args -> (
# 428 "FStar.Syntax.Util.fst"
let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((f, args))) None r)))

# 431 "FStar.Syntax.Util.fst"
let mk_data = (fun l args -> (match (args) with
| [] -> begin
(let _114_185 = (let _114_184 = (let _114_183 = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (_114_183, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_114_184))
in (FStar_Syntax_Syntax.mk _114_185 None (FStar_Ident.range_of_lid l)))
end
| _35_744 -> begin
(
# 436 "FStar.Syntax.Util.fst"
let e = (let _114_186 = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (mk_app _114_186 args))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))) None e.FStar_Syntax_Syntax.pos))
end))

# 439 "FStar.Syntax.Util.fst"
let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident ((Prims.strcat "^fname^" x.FStar_Ident.idText), x.FStar_Ident.idRange)))

# 440 "FStar.Syntax.Util.fst"
let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _114_192 = (let _114_191 = (FStar_Util.substring_from x.FStar_Ident.idText 7)
in (_114_191, x.FStar_Ident.idRange))
in (FStar_Ident.mk_ident _114_192))
end else begin
x
end)

# 445 "FStar.Syntax.Util.fst"
let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (
# 446 "FStar.Syntax.Util.fst"
let nm = if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _114_202 = (let _114_201 = (let _114_199 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _114_199))
in (let _114_200 = (FStar_Syntax_Syntax.range_of_bv x)
in (_114_201, _114_200)))
in (FStar_Ident.mk_ident _114_202))
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (
# 449 "FStar.Syntax.Util.fst"
let y = (
# 449 "FStar.Syntax.Util.fst"
let _35_752 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = _35_752.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _35_752.FStar_Syntax_Syntax.sort})
in (let _114_206 = (let _114_205 = (let _114_204 = (let _114_203 = (unmangle_field_name nm)
in (_114_203)::[])
in (FStar_List.append (FStar_Ident.ids_of_lid lid) _114_204))
in (FStar_Ident.lid_of_ids _114_205))
in (_114_206, y)))))

# 452 "FStar.Syntax.Util.fst"
let set_uvar = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (_35_758) -> begin
(let _114_211 = (let _114_210 = (let _114_209 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _114_209))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" _114_210))
in (FStar_All.failwith _114_211))
end
| _35_761 -> begin
(FStar_Unionfind.change uv (FStar_Syntax_Syntax.Fixed (t)))
end))

# 457 "FStar.Syntax.Util.fst"
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
| _35_794 -> begin
(q1 = q2)
end))

# 469 "FStar.Syntax.Util.fst"
let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (
# 470 "FStar.Syntax.Util.fst"
let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 473 "FStar.Syntax.Util.fst"
let _35_803 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_35_803) with
| (bs, c) -> begin
if (is_tot_or_gtot_comp c) then begin
(
# 475 "FStar.Syntax.Util.fst"
let _35_806 = (arrow_formals_comp (comp_result c))
in (match (_35_806) with
| (bs', k) -> begin
((FStar_List.append bs bs'), k)
end))
end else begin
(bs, c)
end
end))
end
| _35_808 -> begin
(let _114_218 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _114_218))
end)))

# 480 "FStar.Syntax.Util.fst"
let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.typ) = (fun k -> (
# 481 "FStar.Syntax.Util.fst"
let _35_812 = (arrow_formals_comp k)
in (match (_35_812) with
| (bs, c) -> begin
(bs, (comp_result c))
end)))

# 484 "FStar.Syntax.Util.fst"
let abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> (match (bs) with
| [] -> begin
t
end
| _35_818 -> begin
(
# 487 "FStar.Syntax.Util.fst"
let body = (let _114_227 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress _114_227))
in (match ((body.FStar_Syntax_Syntax.n, lopt)) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t, lopt'), None) -> begin
(let _114_231 = (let _114_230 = (let _114_229 = (let _114_228 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append _114_228 bs'))
in (_114_229, t, lopt))
in FStar_Syntax_Syntax.Tm_abs (_114_230))
in (FStar_Syntax_Syntax.mk _114_231 None t.FStar_Syntax_Syntax.pos))
end
| _35_828 -> begin
(
# 492 "FStar.Syntax.Util.fst"
let lopt = (match (lopt) with
| None -> begin
None
end
| Some (lc) -> begin
(let _114_232 = (FStar_Syntax_Subst.close_lcomp bs lc)
in Some (_114_232))
end)
in (let _114_235 = (let _114_234 = (let _114_233 = (FStar_Syntax_Subst.close_binders bs)
in (_114_233, body, lopt))
in FStar_Syntax_Syntax.Tm_abs (_114_234))
in (FStar_Syntax_Syntax.mk _114_235 None t.FStar_Syntax_Syntax.pos)))
end))
end))

# 497 "FStar.Syntax.Util.fst"
let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| _35_837 -> begin
(let _114_243 = (let _114_242 = (let _114_241 = (FStar_Syntax_Subst.close_binders bs)
in (let _114_240 = (FStar_Syntax_Subst.close_comp bs c)
in (_114_241, _114_240)))
in FStar_Syntax_Syntax.Tm_arrow (_114_242))
in (FStar_Syntax_Syntax.mk _114_243 None c.FStar_Syntax_Syntax.pos))
end))

# 500 "FStar.Syntax.Util.fst"
let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun b t -> (let _114_255 = (let _114_251 = (let _114_250 = (let _114_249 = (let _114_248 = (FStar_Syntax_Syntax.mk_binder b)
in (_114_248)::[])
in (FStar_Syntax_Subst.close _114_249 t))
in (b, _114_250))
in FStar_Syntax_Syntax.Tm_refine (_114_251))
in (let _114_254 = (FStar_ST.read b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (let _114_253 = (let _114_252 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges _114_252 t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk _114_255 _114_254 _114_253)))))

# 501 "FStar.Syntax.Util.fst"
let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))

# 503 "FStar.Syntax.Util.fst"
let mk_letbinding : FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def})

# 510 "FStar.Syntax.Util.fst"
let close_univs_and_mk_letbinding : FStar_Ident.lident Prims.list Prims.option  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def -> (
# 511 "FStar.Syntax.Util.fst"
let def = (match (recs) with
| None -> begin
def
end
| Some (lids) -> begin
(
# 514 "FStar.Syntax.Util.fst"
let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _114_280 -> FStar_Syntax_Syntax.U_name (_114_280))))
in (
# 515 "FStar.Syntax.Util.fst"
let inst = (FStar_All.pipe_right lids (FStar_List.map (fun l -> (l, universes))))
in (FStar_Syntax_InstFV.instantiate inst def)))
end)
in (
# 517 "FStar.Syntax.Util.fst"
let typ = (FStar_Syntax_Subst.close_univ_vars univ_vars typ)
in (
# 518 "FStar.Syntax.Util.fst"
let def = (FStar_Syntax_Subst.close_univ_vars univ_vars def)
in (mk_letbinding lbname univ_vars typ eff def)))))

# 521 "FStar.Syntax.Util.fst"
let open_univ_vars_binders_and_comp : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 524 "FStar.Syntax.Util.fst"
let _35_867 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_35_867) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _35_869 -> begin
(
# 527 "FStar.Syntax.Util.fst"
let t' = (arrow binders c)
in (
# 528 "FStar.Syntax.Util.fst"
let _35_873 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_35_873) with
| (uvs, t') -> begin
(match ((let _114_288 = (FStar_Syntax_Subst.compress t')
in _114_288.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _35_879 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 536 "FStar.Syntax.Util.fst"
let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (l, _35_883) -> begin
(FStar_Util.starts_with l.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.Tuple")
end
| _35_887 -> begin
false
end))

# 540 "FStar.Syntax.Util.fst"
let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 541 "FStar.Syntax.Util.fst"
let t = (let _114_295 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Tuple%s" _114_295))
in (let _114_296 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _114_296 r))))

# 544 "FStar.Syntax.Util.fst"
let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 545 "FStar.Syntax.Util.fst"
let t = (let _114_301 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkTuple%s" _114_301))
in (let _114_302 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _114_302 r))))

# 548 "FStar.Syntax.Util.fst"
let is_tuple_data_lid : FStar_Ident.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _114_307 = (mk_tuple_data_lid n FStar_Range.dummyRange)
in (FStar_Ident.lid_equals f _114_307)))

# 551 "FStar.Syntax.Util.fst"
let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (l, _35_899) -> begin
(FStar_Util.starts_with l.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.DTuple")
end
| _35_903 -> begin
false
end))

# 555 "FStar.Syntax.Util.fst"
let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 556 "FStar.Syntax.Util.fst"
let t = (let _114_314 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "DTuple%s" _114_314))
in (let _114_315 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _114_315 r))))

# 559 "FStar.Syntax.Util.fst"
let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 560 "FStar.Syntax.Util.fst"
let t = (let _114_320 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkDTuple%s" _114_320))
in (let _114_321 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _114_321 r))))

# 563 "FStar.Syntax.Util.fst"
let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> (FStar_Ident.lid_equals x FStar_Syntax_Const.eq2_lid))

# 565 "FStar.Syntax.Util.fst"
let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.forall_lid))

# 566 "FStar.Syntax.Util.fst"
let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.exists_lid))

# 567 "FStar.Syntax.Util.fst"
let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))

# 568 "FStar.Syntax.Util.fst"
let is_equality = (fun x -> (is_lid_equality x.FStar_Syntax_Syntax.v))

# 570 "FStar.Syntax.Util.fst"
let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (
# 571 "FStar.Syntax.Util.fst"
let lst = (FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.not_lid)::(FStar_Syntax_Const.iff_lid)::(FStar_Syntax_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))

# 575 "FStar.Syntax.Util.fst"
let is_constructor : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _114_337 = (pre_typ t)
in _114_337.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _35_921) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v lid)
end
| _35_925 -> begin
false
end))

# 580 "FStar.Syntax.Util.fst"
let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _114_342 = (pre_typ t)
in _114_342.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (_35_929) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t, _35_933) -> begin
(is_constructed_typ t lid)
end
| _35_937 -> begin
false
end))

# 585 "FStar.Syntax.Util.fst"
let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun t -> (
# 586 "FStar.Syntax.Util.fst"
let t = (pre_typ t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_app (t, _35_951) -> begin
(get_tycon t)
end
| _35_955 -> begin
None
end)))

# 594 "FStar.Syntax.Util.fst"
let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _35_961 _35_965 -> (match ((_35_961, _35_965)) with
| ((fn1, _35_960), (fn2, _35_964)) -> begin
(FStar_String.compare (FStar_Ident.text_of_lid fn1) (FStar_Ident.text_of_lid fn2))
end)))))

# 601 "FStar.Syntax.Util.fst"
let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (
# 602 "FStar.Syntax.Util.fst"
let theory_syms = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))

# 624 "FStar.Syntax.Util.fst"
let ktype : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None FStar_Range.dummyRange)

# 625 "FStar.Syntax.Util.fst"
let ktype0 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) None FStar_Range.dummyRange)

# 628 "FStar.Syntax.Util.fst"
let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun _35_968 -> (match (()) with
| () -> begin
(
# 629 "FStar.Syntax.Util.fst"
let u = (let _114_353 = (FStar_Unionfind.fresh None)
in (FStar_All.pipe_left (fun _114_352 -> FStar_Syntax_Syntax.U_unif (_114_352)) _114_353))
in (let _114_354 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None FStar_Range.dummyRange)
in (_114_354, u)))
end))

# 632 "FStar.Syntax.Util.fst"
let kt_kt : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Const.kunary ktype0 ktype0)

# 633 "FStar.Syntax.Util.fst"
let kt_kt_kt : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Const.kbin ktype0 ktype0 ktype0)

# 635 "FStar.Syntax.Util.fst"
let tand : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.and_lid FStar_Range.dummyRange)

# 636 "FStar.Syntax.Util.fst"
let tor : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.or_lid FStar_Range.dummyRange)

# 637 "FStar.Syntax.Util.fst"
let timp : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.imp_lid FStar_Range.dummyRange)

# 638 "FStar.Syntax.Util.fst"
let tiff : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.iff_lid FStar_Range.dummyRange)

# 639 "FStar.Syntax.Util.fst"
let t_bool : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.bool_lid FStar_Range.dummyRange)

# 640 "FStar.Syntax.Util.fst"
let t_false : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.false_lid FStar_Range.dummyRange)

# 641 "FStar.Syntax.Util.fst"
let t_true : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid FStar_Range.dummyRange)

# 642 "FStar.Syntax.Util.fst"
let b2t_v : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.b2t_lid FStar_Range.dummyRange)

# 643 "FStar.Syntax.Util.fst"
let t_not : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.not_lid FStar_Range.dummyRange)

# 645 "FStar.Syntax.Util.fst"
let mk_conj_opt : FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _114_366 = (let _114_365 = (let _114_363 = (let _114_362 = (let _114_361 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _114_360 = (let _114_359 = (FStar_Syntax_Syntax.as_arg phi2)
in (_114_359)::[])
in (_114_361)::_114_360))
in (tand, _114_362))
in FStar_Syntax_Syntax.Tm_app (_114_363))
in (let _114_364 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _114_365 None _114_364)))
in Some (_114_366))
end))

# 648 "FStar.Syntax.Util.fst"
let mk_binop = (fun op_t phi1 phi2 -> (let _114_376 = (let _114_374 = (let _114_373 = (let _114_372 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _114_371 = (let _114_370 = (FStar_Syntax_Syntax.as_arg phi2)
in (_114_370)::[])
in (_114_372)::_114_371))
in (op_t, _114_373))
in FStar_Syntax_Syntax.Tm_app (_114_374))
in (let _114_375 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _114_376 None _114_375))))

# 649 "FStar.Syntax.Util.fst"
let mk_neg = (fun phi -> (let _114_381 = (let _114_380 = (let _114_379 = (let _114_378 = (FStar_Syntax_Syntax.as_arg phi)
in (_114_378)::[])
in (t_not, _114_379))
in FStar_Syntax_Syntax.Tm_app (_114_380))
in (FStar_Syntax_Syntax.mk _114_381 None phi.FStar_Syntax_Syntax.pos)))

# 650 "FStar.Syntax.Util.fst"
let mk_conj = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))

# 651 "FStar.Syntax.Util.fst"
let mk_conj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid FStar_Range.dummyRange)
end
| hd::tl -> begin
(FStar_List.fold_right mk_conj tl hd)
end))

# 654 "FStar.Syntax.Util.fst"
let mk_disj = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))

# 655 "FStar.Syntax.Util.fst"
let mk_disj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
t_false
end
| hd::tl -> begin
(FStar_List.fold_right mk_disj tl hd)
end))

# 658 "FStar.Syntax.Util.fst"
let mk_imp : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (match ((let _114_394 = (FStar_Syntax_Subst.compress phi1)
in _114_394.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _35_997) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.false_lid) -> begin
t_true
end
| FStar_Syntax_Syntax.Tm_fvar (tc, _35_1002) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
phi2
end
| _35_1006 -> begin
(match ((let _114_395 = (FStar_Syntax_Subst.compress phi2)
in _114_395.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _35_1009) when ((FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) || (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.false_lid)) -> begin
phi2
end
| _35_1013 -> begin
(mk_binop timp phi1 phi2)
end)
end))

# 668 "FStar.Syntax.Util.fst"
let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))

# 669 "FStar.Syntax.Util.fst"
let b2t = (fun e -> (let _114_402 = (let _114_401 = (let _114_400 = (let _114_399 = (FStar_Syntax_Syntax.as_arg e)
in (_114_399)::[])
in (b2t_v, _114_400))
in FStar_Syntax_Syntax.Tm_app (_114_401))
in (FStar_Syntax_Syntax.mk _114_402 None e.FStar_Syntax_Syntax.pos)))

# 671 "FStar.Syntax.Util.fst"
let eq_pred_t : FStar_Syntax_Syntax.typ = (
# 672 "FStar.Syntax.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv None ktype0)
in (
# 673 "FStar.Syntax.Util.fst"
let atyp = (FStar_Syntax_Syntax.bv_to_tm a)
in (
# 674 "FStar.Syntax.Util.fst"
let b = (FStar_Syntax_Syntax.new_bv None ktype0)
in (
# 675 "FStar.Syntax.Util.fst"
let btyp = (FStar_Syntax_Syntax.bv_to_tm b)
in (let _114_409 = (let _114_407 = (let _114_406 = (let _114_405 = (FStar_Syntax_Syntax.null_binder atyp)
in (let _114_404 = (let _114_403 = (FStar_Syntax_Syntax.null_binder btyp)
in (_114_403)::[])
in (_114_405)::_114_404))
in ((b, Some (FStar_Syntax_Syntax.imp_tag)))::_114_406)
in ((a, Some (FStar_Syntax_Syntax.imp_tag)))::_114_407)
in (let _114_408 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (arrow _114_409 _114_408)))))))

# 679 "FStar.Syntax.Util.fst"
let teq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.eq2_lid FStar_Range.dummyRange)

# 681 "FStar.Syntax.Util.fst"
let mk_eq = (fun t1 t2 e1 e2 -> (let _114_420 = (let _114_418 = (let _114_417 = (let _114_416 = (FStar_Syntax_Syntax.as_arg e1)
in (let _114_415 = (let _114_414 = (FStar_Syntax_Syntax.as_arg e2)
in (_114_414)::[])
in (_114_416)::_114_415))
in (teq, _114_417))
in FStar_Syntax_Syntax.Tm_app (_114_418))
in (let _114_419 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _114_420 None _114_419))))

# 683 "FStar.Syntax.Util.fst"
let mk_has_type = (fun t x t' -> (
# 684 "FStar.Syntax.Util.fst"
let t_has_type = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.has_type_lid FStar_Range.dummyRange)
in (
# 685 "FStar.Syntax.Util.fst"
let t_has_type = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((t_has_type, (FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]))) None FStar_Range.dummyRange)
in (let _114_431 = (let _114_430 = (let _114_429 = (let _114_428 = (FStar_Syntax_Syntax.iarg t)
in (let _114_427 = (let _114_426 = (FStar_Syntax_Syntax.as_arg x)
in (let _114_425 = (let _114_424 = (FStar_Syntax_Syntax.as_arg t')
in (_114_424)::[])
in (_114_426)::_114_425))
in (_114_428)::_114_427))
in (t_has_type, _114_429))
in FStar_Syntax_Syntax.Tm_app (_114_430))
in (FStar_Syntax_Syntax.mk _114_431 None FStar_Range.dummyRange)))))

# 688 "FStar.Syntax.Util.fst"
let lex_t : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid FStar_Range.dummyRange)

# 689 "FStar.Syntax.Util.fst"
let lex_top : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Data_ctor)) FStar_Syntax_Const.lextop_lid FStar_Range.dummyRange)

# 690 "FStar.Syntax.Util.fst"
let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Data_ctor)) FStar_Syntax_Const.lexcons_lid FStar_Range.dummyRange)

# 691 "FStar.Syntax.Util.fst"
let forall_t : FStar_Syntax_Syntax.typ = (
# 692 "FStar.Syntax.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv None ktype0)
in (
# 693 "FStar.Syntax.Util.fst"
let atyp = (FStar_Syntax_Syntax.bv_to_tm a)
in (let _114_435 = (let _114_433 = (let _114_432 = (FStar_Syntax_Syntax.null_binder atyp)
in (_114_432)::[])
in ((a, Some (FStar_Syntax_Syntax.imp_tag)))::_114_433)
in (let _114_434 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (arrow _114_435 _114_434)))))

# 695 "FStar.Syntax.Util.fst"
let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.forall_lid FStar_Range.dummyRange)

# 697 "FStar.Syntax.Util.fst"
let lcomp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (
# 698 "FStar.Syntax.Util.fst"
let c = (comp_to_comp_typ c0)
in {FStar_Syntax_Syntax.eff_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.res_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.cflags = c.FStar_Syntax_Syntax.flags; FStar_Syntax_Syntax.comp = (fun _35_1034 -> (match (()) with
| () -> begin
c0
end))}))

# 704 "FStar.Syntax.Util.fst"
let mk_forall : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun x body -> (let _114_452 = (let _114_451 = (let _114_450 = (let _114_449 = (let _114_448 = (let _114_447 = (let _114_443 = (FStar_Syntax_Syntax.mk_binder x)
in (_114_443)::[])
in (let _114_446 = (let _114_445 = (let _114_444 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (FStar_All.pipe_left lcomp_of_comp _114_444))
in Some (_114_445))
in (abs _114_447 body _114_446)))
in (FStar_Syntax_Syntax.as_arg _114_448))
in (_114_449)::[])
in (tforall, _114_450))
in FStar_Syntax_Syntax.Tm_app (_114_451))
in (FStar_Syntax_Syntax.mk _114_452 None FStar_Range.dummyRange)))

# 707 "FStar.Syntax.Util.fst"
let rec close_forall : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
f
end else begin
(mk_forall (Prims.fst b) f)
end) bs f))

# 710 "FStar.Syntax.Util.fst"
let rec is_wild_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (_35_1043) -> begin
true
end
| _35_1046 -> begin
false
end))

# 715 "FStar.Syntax.Util.fst"
let if_then_else = (fun b t1 t2 -> (
# 716 "FStar.Syntax.Util.fst"
let then_branch = (let _114_463 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t1.FStar_Syntax_Syntax.pos)
in (_114_463, None, t1))
in (
# 717 "FStar.Syntax.Util.fst"
let else_branch = (let _114_464 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Syntax_Syntax.pos)
in (_114_464, None, t2))
in (let _114_466 = (let _114_465 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos _114_465))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((b, (then_branch)::(else_branch)::[]))) None _114_466)))))

# 723 "FStar.Syntax.Util.fst"
type qpats =
FStar_Syntax_Syntax.args Prims.list

# 724 "FStar.Syntax.Util.fst"
type connective =
| QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args)

# 725 "FStar.Syntax.Util.fst"
let is_QAll = (fun _discr_ -> (match (_discr_) with
| QAll (_) -> begin
true
end
| _ -> begin
false
end))

# 726 "FStar.Syntax.Util.fst"
let is_QEx = (fun _discr_ -> (match (_discr_) with
| QEx (_) -> begin
true
end
| _ -> begin
false
end))

# 727 "FStar.Syntax.Util.fst"
let is_BaseConn = (fun _discr_ -> (match (_discr_) with
| BaseConn (_) -> begin
true
end
| _ -> begin
false
end))

# 725 "FStar.Syntax.Util.fst"
let ___QAll____0 : connective  ->  (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) = (fun projectee -> (match (projectee) with
| QAll (_35_1054) -> begin
_35_1054
end))

# 726 "FStar.Syntax.Util.fst"
let ___QEx____0 : connective  ->  (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) = (fun projectee -> (match (projectee) with
| QEx (_35_1057) -> begin
_35_1057
end))

# 727 "FStar.Syntax.Util.fst"
let ___BaseConn____0 : connective  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.args) = (fun projectee -> (match (projectee) with
| BaseConn (_35_1060) -> begin
_35_1060
end))

# 729 "FStar.Syntax.Util.fst"
let destruct_typ_as_formula : FStar_Syntax_Syntax.term  ->  connective Prims.option = (fun f -> (
# 730 "FStar.Syntax.Util.fst"
let destruct_base_conn = (fun f -> (
# 731 "FStar.Syntax.Util.fst"
let connectives = ((FStar_Syntax_Const.true_lid, 0))::((FStar_Syntax_Const.false_lid, 0))::((FStar_Syntax_Const.and_lid, 2))::((FStar_Syntax_Const.or_lid, 2))::((FStar_Syntax_Const.imp_lid, 2))::((FStar_Syntax_Const.iff_lid, 2))::((FStar_Syntax_Const.ite_lid, 3))::((FStar_Syntax_Const.not_lid, 1))::((FStar_Syntax_Const.eq2_lid, 4))::((FStar_Syntax_Const.eq2_lid, 2))::[]
in (
# 742 "FStar.Syntax.Util.fst"
let rec aux = (fun f _35_1069 -> (match (_35_1069) with
| (lid, arity) -> begin
(
# 743 "FStar.Syntax.Util.fst"
let _35_1072 = (head_and_args f)
in (match (_35_1072) with
| (t, args) -> begin
(
# 744 "FStar.Syntax.Util.fst"
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
# 751 "FStar.Syntax.Util.fst"
let patterns = (fun t -> (
# 752 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(let _114_519 = (FStar_Syntax_Subst.compress t)
in (pats, _114_519))
end
| _35_1083 -> begin
(let _114_520 = (FStar_Syntax_Subst.compress t)
in ([], _114_520))
end)))
in (
# 757 "FStar.Syntax.Util.fst"
let destruct_q_conn = (fun t -> (
# 758 "FStar.Syntax.Util.fst"
let is_q = (fun fa l -> if fa then begin
(is_forall l)
end else begin
(is_exists l)
end)
in (
# 759 "FStar.Syntax.Util.fst"
let flat = (fun t -> (
# 760 "FStar.Syntax.Util.fst"
let _35_1093 = (head_and_args t)
in (match (_35_1093) with
| (t, args) -> begin
(let _114_532 = (un_uinst t)
in (let _114_531 = (FStar_All.pipe_right args (FStar_List.map (fun _35_1096 -> (match (_35_1096) with
| (t, imp) -> begin
(let _114_530 = (unascribe t)
in (_114_530, imp))
end))))
in (_114_532, _114_531)))
end)))
in (
# 762 "FStar.Syntax.Util.fst"
let rec aux = (fun qopt out t -> (match ((let _114_539 = (flat t)
in (qopt, _114_539))) with
| ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) | ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _::({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) when (is_q fa tc.FStar_Syntax_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) | ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _::({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) when (is_qlid tc.FStar_Syntax_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (Some (b), _35_1235) -> begin
(
# 774 "FStar.Syntax.Util.fst"
let bs = (FStar_List.rev out)
in (
# 775 "FStar.Syntax.Util.fst"
let _35_1240 = (FStar_Syntax_Subst.open_term bs t)
in (match (_35_1240) with
| (bs, t) -> begin
(
# 776 "FStar.Syntax.Util.fst"
let _35_1243 = (patterns t)
in (match (_35_1243) with
| (pats, body) -> begin
if b then begin
Some (QAll ((bs, pats, body)))
end else begin
Some (QEx ((bs, pats, body)))
end
end))
end)))
end
| _35_1245 -> begin
None
end))
in (aux None [] t)))))
in (
# 784 "FStar.Syntax.Util.fst"
let phi = (FStar_Syntax_Subst.compress f)
in (match ((destruct_base_conn phi)) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end))))))




