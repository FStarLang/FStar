
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

# 307 "FStar.Syntax.Util.fst"
let smt_lemma_pats : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.list = (fun p -> (
# 308 "FStar.Syntax.Util.fst"
let rec list_elements = (fun e -> (
# 309 "FStar.Syntax.Util.fst"
let _35_391 = (let _114_145 = (unmeta e)
in (head_and_args _114_145))
in (match (_35_391) with
| (head, args) -> begin
(match ((let _114_147 = (let _114_146 = (un_uinst head)
in _114_146.FStar_Syntax_Syntax.n)
in (_114_147, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv, _35_394), _35_398) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv, _35_402), _35_414::(hd, _35_411)::(tl, _35_407)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.cons_lid) -> begin
(let _114_148 = (list_elements tl)
in (hd)::_114_148)
end
| _35_418 -> begin
[]
end)
end)))
in (
# 316 "FStar.Syntax.Util.fst"
let v_or_t_pat = (fun p -> (
# 317 "FStar.Syntax.Util.fst"
let _35_423 = (let _114_151 = (unmeta p)
in (FStar_All.pipe_right _114_151 head_and_args))
in (match (_35_423) with
| (head, args) -> begin
(match ((let _114_153 = (let _114_152 = (un_uinst head)
in _114_152.FStar_Syntax_Syntax.n)
in (_114_153, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv, _35_426), (_35_434, _35_436)::(e, _35_431)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpat_lid) -> begin
e
end
| _35_441 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (
# 322 "FStar.Syntax.Util.fst"
let elts = (list_elements p)
in (
# 324 "FStar.Syntax.Util.fst"
let smt_pat_or = (fun t -> (
# 325 "FStar.Syntax.Util.fst"
let _35_447 = (let _114_156 = (unmeta t)
in (FStar_All.pipe_right _114_156 head_and_args))
in (match (_35_447) with
| (head, args) -> begin
(match ((let _114_158 = (let _114_157 = (un_uinst head)
in _114_157.FStar_Syntax_Syntax.n)
in (_114_158, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv, _35_450), (e, _35_455)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _35_460 -> begin
None
end)
end)))
in (match (elts) with
| t::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _114_161 = (list_elements e)
in (FStar_All.pipe_right _114_161 (FStar_List.map (fun branch -> (let _114_160 = (list_elements branch)
in (FStar_All.pipe_right _114_160 (FStar_List.map v_or_t_pat)))))))
end
| _35_467 -> begin
(let _114_162 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_114_162)::[])
end)
end
| _35_469 -> begin
(let _114_163 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_114_163)::[])
end))))))

# 340 "FStar.Syntax.Util.fst"
let is_ml_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _35_9 -> (match (_35_9) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _35_476 -> begin
false
end)))))
end
| _35_478 -> begin
false
end))

# 346 "FStar.Syntax.Util.fst"
let comp_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (t)) | (FStar_Syntax_Syntax.GTotal (t)) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))

# 351 "FStar.Syntax.Util.fst"
let set_result_typ = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_35_488) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (_35_491) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (
# 354 "FStar.Syntax.Util.fst"
let _35_495 = ct
in {FStar_Syntax_Syntax.effect_name = _35_495.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = _35_495.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _35_495.FStar_Syntax_Syntax.flags}))
end))

# 356 "FStar.Syntax.Util.fst"
let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _35_10 -> (match (_35_10) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _35_502 -> begin
false
end)))))

# 362 "FStar.Syntax.Util.fst"
let primops : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]

# 379 "FStar.Syntax.Util.fst"
let is_primop = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _35_506) -> begin
(FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v)))
end
| _35_510 -> begin
false
end))

# 383 "FStar.Syntax.Util.fst"
let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (
# 384 "FStar.Syntax.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e, _35_515, _35_517) -> begin
(unascribe e)
end
| _35_521 -> begin
e
end)))

# 389 "FStar.Syntax.Util.fst"
let rec ascribe = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', _35_526, _35_528) -> begin
(ascribe t' k)
end
| _35_532 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((t, k, None))) None t.FStar_Syntax_Syntax.pos)
end))

# 393 "FStar.Syntax.Util.fst"
let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 394 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _35_537) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _35_542, _35_544) -> begin
(unrefine t)
end
| _35_548 -> begin
t
end)))

# 400 "FStar.Syntax.Util.fst"
let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (match ((let _114_180 = (FStar_Syntax_Subst.compress e)
in _114_180.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_35_551) -> begin
true
end
| _35_554 -> begin
false
end))

# 404 "FStar.Syntax.Util.fst"
let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _114_183 = (FStar_Syntax_Subst.compress t)
in _114_183.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_35_557) -> begin
true
end
| _35_560 -> begin
false
end))

# 408 "FStar.Syntax.Util.fst"
let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 409 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _35_565) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _35_570, _35_572) -> begin
(pre_typ t)
end
| _35_576 -> begin
t
end)))

# 415 "FStar.Syntax.Util.fst"
let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.args Prims.option = (fun typ lid -> (
# 416 "FStar.Syntax.Util.fst"
let typ = (FStar_Syntax_Subst.compress typ)
in (match (typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _35_588); FStar_Syntax_Syntax.tk = _35_585; FStar_Syntax_Syntax.pos = _35_583; FStar_Syntax_Syntax.vars = _35_581}, args) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v lid) -> begin
Some (args)
end
| FStar_Syntax_Syntax.Tm_fvar (tc, _35_597) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v lid) -> begin
Some ([])
end
| _35_601 -> begin
None
end)))

# 422 "FStar.Syntax.Util.fst"
let rec lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_let (_, _, lids, _)) | (FStar_Syntax_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_datacon (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_declare_typ (lid, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n, _35_685) -> begin
(n.FStar_Syntax_Syntax.mname)::[]
end
| (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) -> begin
[]
end))

# 435 "FStar.Syntax.Util.fst"
let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.option = (fun se -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _35_701 -> begin
None
end))

# 439 "FStar.Syntax.Util.fst"
let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Syntax_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_datacon (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_assume (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_let (_, r, _, _)) | (FStar_Syntax_Syntax.Sig_main (_, r)) | (FStar_Syntax_Syntax.Sig_pragma (_, r)) | (FStar_Syntax_Syntax.Sig_new_effect (_, r)) | (FStar_Syntax_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))

# 452 "FStar.Syntax.Util.fst"
let range_of_lb = (fun _35_11 -> (match (_35_11) with
| (FStar_Util.Inl (x), _35_802, _35_804) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), _35_809, _35_811) -> begin
(FStar_Ident.range_of_lid l)
end))

# 456 "FStar.Syntax.Util.fst"
let range_of_arg = (fun _35_816 -> (match (_35_816) with
| (hd, _35_815) -> begin
hd.FStar_Syntax_Syntax.pos
end))

# 458 "FStar.Syntax.Util.fst"
let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))

# 461 "FStar.Syntax.Util.fst"
let mk_app = (fun f args -> (
# 462 "FStar.Syntax.Util.fst"
let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((f, args))) None r)))

# 465 "FStar.Syntax.Util.fst"
let mk_data = (fun l args -> (match (args) with
| [] -> begin
(let _114_208 = (let _114_207 = (let _114_206 = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (_114_206, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_114_207))
in (FStar_Syntax_Syntax.mk _114_208 None (FStar_Ident.range_of_lid l)))
end
| _35_828 -> begin
(
# 470 "FStar.Syntax.Util.fst"
let e = (let _114_209 = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (mk_app _114_209 args))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))) None e.FStar_Syntax_Syntax.pos))
end))

# 473 "FStar.Syntax.Util.fst"
let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident ((Prims.strcat "^fname^" x.FStar_Ident.idText), x.FStar_Ident.idRange)))

# 474 "FStar.Syntax.Util.fst"
let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _114_215 = (let _114_214 = (FStar_Util.substring_from x.FStar_Ident.idText 7)
in (_114_214, x.FStar_Ident.idRange))
in (FStar_Ident.mk_ident _114_215))
end else begin
x
end)

# 479 "FStar.Syntax.Util.fst"
let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (
# 480 "FStar.Syntax.Util.fst"
let nm = if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _114_225 = (let _114_224 = (let _114_222 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _114_222))
in (let _114_223 = (FStar_Syntax_Syntax.range_of_bv x)
in (_114_224, _114_223)))
in (FStar_Ident.mk_ident _114_225))
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (
# 483 "FStar.Syntax.Util.fst"
let y = (
# 483 "FStar.Syntax.Util.fst"
let _35_836 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = _35_836.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _35_836.FStar_Syntax_Syntax.sort})
in (let _114_229 = (let _114_228 = (let _114_227 = (let _114_226 = (unmangle_field_name nm)
in (_114_226)::[])
in (FStar_List.append (FStar_Ident.ids_of_lid lid) _114_227))
in (FStar_Ident.lid_of_ids _114_228))
in (_114_229, y)))))

# 486 "FStar.Syntax.Util.fst"
let set_uvar = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (_35_842) -> begin
(let _114_234 = (let _114_233 = (let _114_232 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _114_232))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" _114_233))
in (FStar_All.failwith _114_234))
end
| _35_845 -> begin
(FStar_Unionfind.change uv (FStar_Syntax_Syntax.Fixed (t)))
end))

# 491 "FStar.Syntax.Util.fst"
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
| _35_878 -> begin
(q1 = q2)
end))

# 503 "FStar.Syntax.Util.fst"
let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (
# 504 "FStar.Syntax.Util.fst"
let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 507 "FStar.Syntax.Util.fst"
let _35_887 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_35_887) with
| (bs, c) -> begin
if (is_tot_or_gtot_comp c) then begin
(
# 509 "FStar.Syntax.Util.fst"
let _35_890 = (arrow_formals_comp (comp_result c))
in (match (_35_890) with
| (bs', k) -> begin
((FStar_List.append bs bs'), k)
end))
end else begin
(bs, c)
end
end))
end
| _35_892 -> begin
(let _114_241 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _114_241))
end)))

# 514 "FStar.Syntax.Util.fst"
let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.typ) = (fun k -> (
# 515 "FStar.Syntax.Util.fst"
let _35_896 = (arrow_formals_comp k)
in (match (_35_896) with
| (bs, c) -> begin
(bs, (comp_result c))
end)))

# 518 "FStar.Syntax.Util.fst"
let abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> (match (bs) with
| [] -> begin
t
end
| _35_902 -> begin
(
# 521 "FStar.Syntax.Util.fst"
let body = (let _114_250 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress _114_250))
in (match ((body.FStar_Syntax_Syntax.n, lopt)) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t, lopt'), None) -> begin
(let _114_254 = (let _114_253 = (let _114_252 = (let _114_251 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append _114_251 bs'))
in (_114_252, t, lopt))
in FStar_Syntax_Syntax.Tm_abs (_114_253))
in (FStar_Syntax_Syntax.mk _114_254 None t.FStar_Syntax_Syntax.pos))
end
| _35_912 -> begin
(
# 526 "FStar.Syntax.Util.fst"
let lopt = (match (lopt) with
| None -> begin
None
end
| Some (lc) -> begin
(let _114_255 = (FStar_Syntax_Subst.close_lcomp bs lc)
in Some (_114_255))
end)
in (let _114_258 = (let _114_257 = (let _114_256 = (FStar_Syntax_Subst.close_binders bs)
in (_114_256, body, lopt))
in FStar_Syntax_Syntax.Tm_abs (_114_257))
in (FStar_Syntax_Syntax.mk _114_258 None t.FStar_Syntax_Syntax.pos)))
end))
end))

# 531 "FStar.Syntax.Util.fst"
let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| _35_921 -> begin
(let _114_266 = (let _114_265 = (let _114_264 = (FStar_Syntax_Subst.close_binders bs)
in (let _114_263 = (FStar_Syntax_Subst.close_comp bs c)
in (_114_264, _114_263)))
in FStar_Syntax_Syntax.Tm_arrow (_114_265))
in (FStar_Syntax_Syntax.mk _114_266 None c.FStar_Syntax_Syntax.pos))
end))

# 534 "FStar.Syntax.Util.fst"
let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun b t -> (let _114_278 = (let _114_274 = (let _114_273 = (let _114_272 = (let _114_271 = (FStar_Syntax_Syntax.mk_binder b)
in (_114_271)::[])
in (FStar_Syntax_Subst.close _114_272 t))
in (b, _114_273))
in FStar_Syntax_Syntax.Tm_refine (_114_274))
in (let _114_277 = (FStar_ST.read b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (let _114_276 = (let _114_275 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges _114_275 t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk _114_278 _114_277 _114_276)))))

# 535 "FStar.Syntax.Util.fst"
let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))

# 537 "FStar.Syntax.Util.fst"
let mk_letbinding : FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def})

# 544 "FStar.Syntax.Util.fst"
let close_univs_and_mk_letbinding : FStar_Ident.lident Prims.list Prims.option  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def -> (
# 545 "FStar.Syntax.Util.fst"
let def = (match (recs) with
| None -> begin
def
end
| Some (lids) -> begin
(
# 548 "FStar.Syntax.Util.fst"
let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _114_303 -> FStar_Syntax_Syntax.U_name (_114_303))))
in (
# 549 "FStar.Syntax.Util.fst"
let inst = (FStar_All.pipe_right lids (FStar_List.map (fun l -> (l, universes))))
in (FStar_Syntax_InstFV.inst inst def)))
end)
in (
# 551 "FStar.Syntax.Util.fst"
let typ = (FStar_Syntax_Subst.close_univ_vars univ_vars typ)
in (
# 552 "FStar.Syntax.Util.fst"
let def = (FStar_Syntax_Subst.close_univ_vars univ_vars def)
in (mk_letbinding lbname univ_vars typ eff def)))))

# 555 "FStar.Syntax.Util.fst"
let open_univ_vars_binders_and_comp : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 558 "FStar.Syntax.Util.fst"
let _35_951 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_35_951) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _35_953 -> begin
(
# 561 "FStar.Syntax.Util.fst"
let t' = (arrow binders c)
in (
# 562 "FStar.Syntax.Util.fst"
let _35_957 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_35_957) with
| (uvs, t') -> begin
(match ((let _114_311 = (FStar_Syntax_Subst.compress t')
in _114_311.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _35_963 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 570 "FStar.Syntax.Util.fst"
let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (l, _35_967) -> begin
(FStar_Util.starts_with l.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.Tuple")
end
| _35_971 -> begin
false
end))

# 574 "FStar.Syntax.Util.fst"
let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 575 "FStar.Syntax.Util.fst"
let t = (let _114_318 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Tuple%s" _114_318))
in (let _114_319 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _114_319 r))))

# 578 "FStar.Syntax.Util.fst"
let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 579 "FStar.Syntax.Util.fst"
let t = (let _114_324 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkTuple%s" _114_324))
in (let _114_325 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _114_325 r))))

# 582 "FStar.Syntax.Util.fst"
let is_tuple_data_lid : FStar_Ident.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _114_330 = (mk_tuple_data_lid n FStar_Range.dummyRange)
in (FStar_Ident.lid_equals f _114_330)))

# 585 "FStar.Syntax.Util.fst"
let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (l, _35_983) -> begin
(FStar_Util.starts_with l.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.DTuple")
end
| _35_987 -> begin
false
end))

# 589 "FStar.Syntax.Util.fst"
let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 590 "FStar.Syntax.Util.fst"
let t = (let _114_337 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "DTuple%s" _114_337))
in (let _114_338 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _114_338 r))))

# 593 "FStar.Syntax.Util.fst"
let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 594 "FStar.Syntax.Util.fst"
let t = (let _114_343 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkDTuple%s" _114_343))
in (let _114_344 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _114_344 r))))

# 597 "FStar.Syntax.Util.fst"
let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> (FStar_Ident.lid_equals x FStar_Syntax_Const.eq2_lid))

# 599 "FStar.Syntax.Util.fst"
let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.forall_lid))

# 600 "FStar.Syntax.Util.fst"
let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.exists_lid))

# 601 "FStar.Syntax.Util.fst"
let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))

# 602 "FStar.Syntax.Util.fst"
let is_equality = (fun x -> (is_lid_equality x.FStar_Syntax_Syntax.v))

# 604 "FStar.Syntax.Util.fst"
let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (
# 605 "FStar.Syntax.Util.fst"
let lst = (FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.not_lid)::(FStar_Syntax_Const.iff_lid)::(FStar_Syntax_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))

# 609 "FStar.Syntax.Util.fst"
let is_constructor : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _114_360 = (pre_typ t)
in _114_360.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _35_1005) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v lid)
end
| _35_1009 -> begin
false
end))

# 614 "FStar.Syntax.Util.fst"
let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _114_365 = (pre_typ t)
in _114_365.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (_35_1013) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t, _35_1017) -> begin
(is_constructed_typ t lid)
end
| _35_1021 -> begin
false
end))

# 619 "FStar.Syntax.Util.fst"
let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun t -> (
# 620 "FStar.Syntax.Util.fst"
let t = (pre_typ t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_app (t, _35_1035) -> begin
(get_tycon t)
end
| _35_1039 -> begin
None
end)))

# 628 "FStar.Syntax.Util.fst"
let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _35_1045 _35_1049 -> (match ((_35_1045, _35_1049)) with
| ((fn1, _35_1044), (fn2, _35_1048)) -> begin
(FStar_String.compare (FStar_Ident.text_of_lid fn1) (FStar_Ident.text_of_lid fn2))
end)))))

# 635 "FStar.Syntax.Util.fst"
let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (
# 636 "FStar.Syntax.Util.fst"
let theory_syms = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))

# 658 "FStar.Syntax.Util.fst"
let ktype : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None FStar_Range.dummyRange)

# 659 "FStar.Syntax.Util.fst"
let ktype0 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) None FStar_Range.dummyRange)

# 662 "FStar.Syntax.Util.fst"
let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun _35_1052 -> (match (()) with
| () -> begin
(
# 663 "FStar.Syntax.Util.fst"
let u = (let _114_376 = (FStar_Unionfind.fresh None)
in (FStar_All.pipe_left (fun _114_375 -> FStar_Syntax_Syntax.U_unif (_114_375)) _114_376))
in (let _114_377 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None FStar_Range.dummyRange)
in (_114_377, u)))
end))

# 666 "FStar.Syntax.Util.fst"
let kt_kt : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Const.kunary ktype0 ktype0)

# 667 "FStar.Syntax.Util.fst"
let kt_kt_kt : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Const.kbin ktype0 ktype0 ktype0)

# 669 "FStar.Syntax.Util.fst"
let tand : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.and_lid FStar_Range.dummyRange)

# 670 "FStar.Syntax.Util.fst"
let tor : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.or_lid FStar_Range.dummyRange)

# 671 "FStar.Syntax.Util.fst"
let timp : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.imp_lid FStar_Range.dummyRange)

# 672 "FStar.Syntax.Util.fst"
let tiff : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.iff_lid FStar_Range.dummyRange)

# 673 "FStar.Syntax.Util.fst"
let t_bool : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.bool_lid FStar_Range.dummyRange)

# 674 "FStar.Syntax.Util.fst"
let t_false : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.false_lid FStar_Range.dummyRange)

# 675 "FStar.Syntax.Util.fst"
let t_true : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid FStar_Range.dummyRange)

# 676 "FStar.Syntax.Util.fst"
let b2t_v : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.b2t_lid FStar_Range.dummyRange)

# 677 "FStar.Syntax.Util.fst"
let t_not : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.not_lid FStar_Range.dummyRange)

# 679 "FStar.Syntax.Util.fst"
let mk_conj_opt : FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _114_389 = (let _114_388 = (let _114_386 = (let _114_385 = (let _114_384 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _114_383 = (let _114_382 = (FStar_Syntax_Syntax.as_arg phi2)
in (_114_382)::[])
in (_114_384)::_114_383))
in (tand, _114_385))
in FStar_Syntax_Syntax.Tm_app (_114_386))
in (let _114_387 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _114_388 None _114_387)))
in Some (_114_389))
end))

# 682 "FStar.Syntax.Util.fst"
let mk_binop = (fun op_t phi1 phi2 -> (let _114_399 = (let _114_397 = (let _114_396 = (let _114_395 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _114_394 = (let _114_393 = (FStar_Syntax_Syntax.as_arg phi2)
in (_114_393)::[])
in (_114_395)::_114_394))
in (op_t, _114_396))
in FStar_Syntax_Syntax.Tm_app (_114_397))
in (let _114_398 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _114_399 None _114_398))))

# 683 "FStar.Syntax.Util.fst"
let mk_neg = (fun phi -> (let _114_404 = (let _114_403 = (let _114_402 = (let _114_401 = (FStar_Syntax_Syntax.as_arg phi)
in (_114_401)::[])
in (t_not, _114_402))
in FStar_Syntax_Syntax.Tm_app (_114_403))
in (FStar_Syntax_Syntax.mk _114_404 None phi.FStar_Syntax_Syntax.pos)))

# 684 "FStar.Syntax.Util.fst"
let mk_conj = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))

# 685 "FStar.Syntax.Util.fst"
let mk_conj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid FStar_Range.dummyRange)
end
| hd::tl -> begin
(FStar_List.fold_right mk_conj tl hd)
end))

# 688 "FStar.Syntax.Util.fst"
let mk_disj = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))

# 689 "FStar.Syntax.Util.fst"
let mk_disj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
t_false
end
| hd::tl -> begin
(FStar_List.fold_right mk_disj tl hd)
end))

# 692 "FStar.Syntax.Util.fst"
let mk_imp : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (match ((let _114_417 = (FStar_Syntax_Subst.compress phi1)
in _114_417.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _35_1081) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.false_lid) -> begin
t_true
end
| FStar_Syntax_Syntax.Tm_fvar (tc, _35_1086) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
phi2
end
| _35_1090 -> begin
(match ((let _114_418 = (FStar_Syntax_Subst.compress phi2)
in _114_418.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _35_1093) when ((FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) || (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.false_lid)) -> begin
phi2
end
| _35_1097 -> begin
(mk_binop timp phi1 phi2)
end)
end))

# 702 "FStar.Syntax.Util.fst"
let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))

# 703 "FStar.Syntax.Util.fst"
let b2t = (fun e -> (let _114_425 = (let _114_424 = (let _114_423 = (let _114_422 = (FStar_Syntax_Syntax.as_arg e)
in (_114_422)::[])
in (b2t_v, _114_423))
in FStar_Syntax_Syntax.Tm_app (_114_424))
in (FStar_Syntax_Syntax.mk _114_425 None e.FStar_Syntax_Syntax.pos)))

# 705 "FStar.Syntax.Util.fst"
let eq_pred_t : FStar_Syntax_Syntax.typ = (
# 706 "FStar.Syntax.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv None ktype0)
in (
# 707 "FStar.Syntax.Util.fst"
let atyp = (FStar_Syntax_Syntax.bv_to_tm a)
in (
# 708 "FStar.Syntax.Util.fst"
let b = (FStar_Syntax_Syntax.new_bv None ktype0)
in (
# 709 "FStar.Syntax.Util.fst"
let btyp = (FStar_Syntax_Syntax.bv_to_tm b)
in (let _114_432 = (let _114_430 = (let _114_429 = (let _114_428 = (FStar_Syntax_Syntax.null_binder atyp)
in (let _114_427 = (let _114_426 = (FStar_Syntax_Syntax.null_binder btyp)
in (_114_426)::[])
in (_114_428)::_114_427))
in ((b, Some (FStar_Syntax_Syntax.Implicit)))::_114_429)
in ((a, Some (FStar_Syntax_Syntax.Implicit)))::_114_430)
in (let _114_431 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (arrow _114_432 _114_431)))))))

# 713 "FStar.Syntax.Util.fst"
let teq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.eq2_lid FStar_Range.dummyRange)

# 715 "FStar.Syntax.Util.fst"
let mk_eq = (fun t1 t2 e1 e2 -> (let _114_443 = (let _114_441 = (let _114_440 = (let _114_439 = (FStar_Syntax_Syntax.as_arg e1)
in (let _114_438 = (let _114_437 = (FStar_Syntax_Syntax.as_arg e2)
in (_114_437)::[])
in (_114_439)::_114_438))
in (teq, _114_440))
in FStar_Syntax_Syntax.Tm_app (_114_441))
in (let _114_442 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _114_443 None _114_442))))

# 717 "FStar.Syntax.Util.fst"
let mk_has_type = (fun t x t' -> (
# 718 "FStar.Syntax.Util.fst"
let t_has_type = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.has_type_lid FStar_Range.dummyRange)
in (
# 719 "FStar.Syntax.Util.fst"
let t_has_type = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((t_has_type, (FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]))) None FStar_Range.dummyRange)
in (let _114_454 = (let _114_453 = (let _114_452 = (let _114_451 = (FStar_Syntax_Syntax.iarg t)
in (let _114_450 = (let _114_449 = (FStar_Syntax_Syntax.as_arg x)
in (let _114_448 = (let _114_447 = (FStar_Syntax_Syntax.as_arg t')
in (_114_447)::[])
in (_114_449)::_114_448))
in (_114_451)::_114_450))
in (t_has_type, _114_452))
in FStar_Syntax_Syntax.Tm_app (_114_453))
in (FStar_Syntax_Syntax.mk _114_454 None FStar_Range.dummyRange)))))

# 722 "FStar.Syntax.Util.fst"
let lex_t : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid FStar_Range.dummyRange)

# 723 "FStar.Syntax.Util.fst"
let lex_top : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Data_ctor)) FStar_Syntax_Const.lextop_lid FStar_Range.dummyRange)

# 724 "FStar.Syntax.Util.fst"
let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Data_ctor)) FStar_Syntax_Const.lexcons_lid FStar_Range.dummyRange)

# 725 "FStar.Syntax.Util.fst"
let forall_t : FStar_Syntax_Syntax.typ = (
# 726 "FStar.Syntax.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv None ktype0)
in (
# 727 "FStar.Syntax.Util.fst"
let atyp = (FStar_Syntax_Syntax.bv_to_tm a)
in (let _114_458 = (let _114_456 = (let _114_455 = (FStar_Syntax_Syntax.null_binder atyp)
in (_114_455)::[])
in ((a, Some (FStar_Syntax_Syntax.Implicit)))::_114_456)
in (let _114_457 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (arrow _114_458 _114_457)))))

# 729 "FStar.Syntax.Util.fst"
let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.forall_lid FStar_Range.dummyRange)

# 731 "FStar.Syntax.Util.fst"
let lcomp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (
# 732 "FStar.Syntax.Util.fst"
let c = (comp_to_comp_typ c0)
in {FStar_Syntax_Syntax.eff_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.res_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.cflags = c.FStar_Syntax_Syntax.flags; FStar_Syntax_Syntax.comp = (fun _35_1118 -> (match (()) with
| () -> begin
c0
end))}))

# 738 "FStar.Syntax.Util.fst"
let mk_forall : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun x body -> (let _114_475 = (let _114_474 = (let _114_473 = (let _114_472 = (let _114_471 = (let _114_470 = (let _114_466 = (FStar_Syntax_Syntax.mk_binder x)
in (_114_466)::[])
in (let _114_469 = (let _114_468 = (let _114_467 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (FStar_All.pipe_left lcomp_of_comp _114_467))
in Some (_114_468))
in (abs _114_470 body _114_469)))
in (FStar_Syntax_Syntax.as_arg _114_471))
in (_114_472)::[])
in (tforall, _114_473))
in FStar_Syntax_Syntax.Tm_app (_114_474))
in (FStar_Syntax_Syntax.mk _114_475 None FStar_Range.dummyRange)))

# 741 "FStar.Syntax.Util.fst"
let rec close_forall : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
f
end else begin
(mk_forall (Prims.fst b) f)
end) bs f))

# 744 "FStar.Syntax.Util.fst"
let rec is_wild_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (_35_1127) -> begin
true
end
| _35_1130 -> begin
false
end))

# 749 "FStar.Syntax.Util.fst"
let if_then_else = (fun b t1 t2 -> (
# 750 "FStar.Syntax.Util.fst"
let then_branch = (let _114_486 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t1.FStar_Syntax_Syntax.pos)
in (_114_486, None, t1))
in (
# 751 "FStar.Syntax.Util.fst"
let else_branch = (let _114_487 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Syntax_Syntax.pos)
in (_114_487, None, t2))
in (let _114_489 = (let _114_488 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos _114_488))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((b, (then_branch)::(else_branch)::[]))) None _114_489)))))

# 757 "FStar.Syntax.Util.fst"
type qpats =
FStar_Syntax_Syntax.args Prims.list

# 758 "FStar.Syntax.Util.fst"
type connective =
| QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args)

# 759 "FStar.Syntax.Util.fst"
let is_QAll = (fun _discr_ -> (match (_discr_) with
| QAll (_) -> begin
true
end
| _ -> begin
false
end))

# 760 "FStar.Syntax.Util.fst"
let is_QEx = (fun _discr_ -> (match (_discr_) with
| QEx (_) -> begin
true
end
| _ -> begin
false
end))

# 761 "FStar.Syntax.Util.fst"
let is_BaseConn = (fun _discr_ -> (match (_discr_) with
| BaseConn (_) -> begin
true
end
| _ -> begin
false
end))

# 759 "FStar.Syntax.Util.fst"
let ___QAll____0 : connective  ->  (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) = (fun projectee -> (match (projectee) with
| QAll (_35_1138) -> begin
_35_1138
end))

# 760 "FStar.Syntax.Util.fst"
let ___QEx____0 : connective  ->  (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) = (fun projectee -> (match (projectee) with
| QEx (_35_1141) -> begin
_35_1141
end))

# 761 "FStar.Syntax.Util.fst"
let ___BaseConn____0 : connective  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.args) = (fun projectee -> (match (projectee) with
| BaseConn (_35_1144) -> begin
_35_1144
end))

# 763 "FStar.Syntax.Util.fst"
let destruct_typ_as_formula : FStar_Syntax_Syntax.term  ->  connective Prims.option = (fun f -> (
# 764 "FStar.Syntax.Util.fst"
let destruct_base_conn = (fun f -> (
# 765 "FStar.Syntax.Util.fst"
let connectives = ((FStar_Syntax_Const.true_lid, 0))::((FStar_Syntax_Const.false_lid, 0))::((FStar_Syntax_Const.and_lid, 2))::((FStar_Syntax_Const.or_lid, 2))::((FStar_Syntax_Const.imp_lid, 2))::((FStar_Syntax_Const.iff_lid, 2))::((FStar_Syntax_Const.ite_lid, 3))::((FStar_Syntax_Const.not_lid, 1))::((FStar_Syntax_Const.eq2_lid, 4))::((FStar_Syntax_Const.eq2_lid, 2))::[]
in (
# 776 "FStar.Syntax.Util.fst"
let rec aux = (fun f _35_1153 -> (match (_35_1153) with
| (lid, arity) -> begin
(
# 777 "FStar.Syntax.Util.fst"
let _35_1156 = (head_and_args f)
in (match (_35_1156) with
| (t, args) -> begin
(
# 778 "FStar.Syntax.Util.fst"
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
# 785 "FStar.Syntax.Util.fst"
let patterns = (fun t -> (
# 786 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(let _114_542 = (FStar_Syntax_Subst.compress t)
in (pats, _114_542))
end
| _35_1167 -> begin
(let _114_543 = (FStar_Syntax_Subst.compress t)
in ([], _114_543))
end)))
in (
# 791 "FStar.Syntax.Util.fst"
let destruct_q_conn = (fun t -> (
# 792 "FStar.Syntax.Util.fst"
let is_q = (fun fa l -> if fa then begin
(is_forall l)
end else begin
(is_exists l)
end)
in (
# 793 "FStar.Syntax.Util.fst"
let flat = (fun t -> (
# 794 "FStar.Syntax.Util.fst"
let _35_1177 = (head_and_args t)
in (match (_35_1177) with
| (t, args) -> begin
(let _114_555 = (un_uinst t)
in (let _114_554 = (FStar_All.pipe_right args (FStar_List.map (fun _35_1180 -> (match (_35_1180) with
| (t, imp) -> begin
(let _114_553 = (unascribe t)
in (_114_553, imp))
end))))
in (_114_555, _114_554)))
end)))
in (
# 796 "FStar.Syntax.Util.fst"
let rec aux = (fun qopt out t -> (match ((let _114_562 = (flat t)
in (qopt, _114_562))) with
| ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) | ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _::({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) when (is_q fa tc.FStar_Syntax_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) | ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _::({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) when (is_qlid tc.FStar_Syntax_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (Some (b), _35_1319) -> begin
(
# 808 "FStar.Syntax.Util.fst"
let bs = (FStar_List.rev out)
in (
# 809 "FStar.Syntax.Util.fst"
let _35_1324 = (FStar_Syntax_Subst.open_term bs t)
in (match (_35_1324) with
| (bs, t) -> begin
(
# 810 "FStar.Syntax.Util.fst"
let _35_1327 = (patterns t)
in (match (_35_1327) with
| (pats, body) -> begin
if b then begin
Some (QAll ((bs, pats, body)))
end else begin
Some (QEx ((bs, pats, body)))
end
end))
end)))
end
| _35_1329 -> begin
None
end))
in (aux None [] t)))))
in (
# 818 "FStar.Syntax.Util.fst"
let phi = (FStar_Syntax_Subst.compress f)
in (match ((destruct_base_conn phi)) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end))))))




