
open Prims
# 29 "FStar.Syntax.Util.fst"
let handle_err : Prims.bool  ->  Prims.unit  ->  Prims.exn  ->  Prims.unit = (fun warning ret e -> (match (e) with
| FStar_Syntax_Syntax.Error (msg, r) -> begin
(
# 32 "FStar.Syntax.Util.fst"
let _34_19 = (let _115_8 = (let _115_7 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s : %s\n%s\n" _115_7 (if warning then begin
"Warning"
end else begin
"Error"
end) msg))
in (FStar_Util.print_string _115_8))
in ())
end
| FStar_Util.NYI (s) -> begin
(
# 35 "FStar.Syntax.Util.fst"
let _34_23 = (let _115_9 = (FStar_Util.format1 "Feature not yet implemented: %s" s)
in (FStar_Util.print_string _115_9))
in ())
end
| FStar_Syntax_Syntax.Err (s) -> begin
(let _115_10 = (FStar_Util.format1 "Error: %s" s)
in (FStar_Util.print_string _115_10))
end
| _34_28 -> begin
(Prims.raise e)
end))

# 41 "FStar.Syntax.Util.fst"
let handleable : Prims.exn  ->  Prims.bool = (fun _34_1 -> (match (_34_1) with
| (FStar_Syntax_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Syntax_Syntax.Err (_)) -> begin
true
end
| _34_40 -> begin
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
let arg_of_non_null_binder = (fun _34_46 -> (match (_34_46) with
| (b, imp) -> begin
(let _115_18 = (FStar_Syntax_Syntax.bv_to_name b)
in (_115_18, imp))
end))

# 61 "FStar.Syntax.Util.fst"
let args_of_non_null_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
[]
end else begin
(let _115_22 = (arg_of_non_null_binder b)
in (_115_22)::[])
end))))

# 66 "FStar.Syntax.Util.fst"
let args_of_binders : FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun binders -> (let _115_29 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
(
# 69 "FStar.Syntax.Util.fst"
let b = (let _115_26 = (FStar_Syntax_Syntax.new_bv None (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_115_26, (Prims.snd b)))
in (let _115_27 = (arg_of_non_null_binder b)
in (b, _115_27)))
end else begin
(let _115_28 = (arg_of_non_null_binder b)
in (b, _115_28))
end)))
in (FStar_All.pipe_right _115_29 FStar_List.unzip)))

# 73 "FStar.Syntax.Util.fst"
let name_binders : FStar_Syntax_Syntax.binder Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
(
# 76 "FStar.Syntax.Util.fst"
let _34_57 = b
in (match (_34_57) with
| (a, imp) -> begin
(
# 77 "FStar.Syntax.Util.fst"
let b = (let _115_35 = (let _115_34 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _115_34))
in (FStar_Ident.id_of_text _115_35))
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
(let _115_39 = (let _115_38 = (let _115_37 = (name_binders binders)
in (_115_37, comp))
in FStar_Syntax_Syntax.Tm_arrow (_115_38))
in (FStar_Syntax_Syntax.mk _115_39 None t.FStar_Syntax_Syntax.pos))
end
| _34_66 -> begin
t
end))

# 86 "FStar.Syntax.Util.fst"
let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _34_70 -> (match (_34_70) with
| (t, imp) -> begin
(let _115_44 = (let _115_43 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left Prims.fst _115_43))
in (_115_44, imp))
end)))))

# 89 "FStar.Syntax.Util.fst"
let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _34_74 -> (match (_34_74) with
| (t, imp) -> begin
(let _115_48 = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (_115_48, imp))
end)))))

# 92 "FStar.Syntax.Util.fst"
let binders_of_freevars : (FStar_Syntax_Syntax.bv Prims.list * (FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  Prims.bool))  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (let _115_57 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _115_57 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))

# 94 "FStar.Syntax.Util.fst"
let mk_subst = (fun s -> (s)::[])

# 96 "FStar.Syntax.Util.fst"
let subst_formal : FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.arg  ->  FStar_Syntax_Syntax.subst_elt = (fun f a -> FStar_Syntax_Syntax.DB ((0, (Prims.fst a))))

# 97 "FStar.Syntax.Util.fst"
let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> if ((FStar_List.length formals) = (FStar_List.length actuals)) then begin
(let _115_70 = (FStar_List.fold_right2 (fun f a _34_85 -> (match (_34_85) with
| (n, out) -> begin
((n + 1), (FStar_Syntax_Syntax.DB ((n, (Prims.fst a))))::out)
end)) formals actuals (0, []))
in (FStar_All.pipe_right _115_70 Prims.snd))
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
| _34_100 -> begin
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
let _34_114 = (univ_kernel u)
in (match (_34_114) with
| (k, n) -> begin
(k, (n + 1))
end))
end
| (FStar_Syntax_Syntax.U_max (_)) | (FStar_Syntax_Syntax.U_bvar (_)) -> begin
(FStar_All.failwith "Imposible")
end))

# 129 "FStar.Syntax.Util.fst"
let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (let _115_77 = (univ_kernel u)
in (Prims.snd _115_77)))

# 137 "FStar.Syntax.Util.fst"
let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match ((u1, u2)) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) -> begin
(FStar_All.failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
0
end
| (FStar_Syntax_Syntax.U_unknown, _34_141) -> begin
(- (1))
end
| (_34_144, FStar_Syntax_Syntax.U_unknown) -> begin
1
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
0
end
| (FStar_Syntax_Syntax.U_zero, _34_152) -> begin
(- (1))
end
| (_34_155, FStar_Syntax_Syntax.U_zero) -> begin
1
end
| (FStar_Syntax_Syntax.U_name (u1), FStar_Syntax_Syntax.U_name (u2)) -> begin
(FStar_String.compare u1.FStar_Ident.idText u2.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (_34_164), FStar_Syntax_Syntax.U_unif (_34_167)) -> begin
(- (1))
end
| (FStar_Syntax_Syntax.U_unif (_34_171), FStar_Syntax_Syntax.U_name (_34_174)) -> begin
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
let copt = (let _115_83 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map _115_83 (fun _34_191 -> (match (_34_191) with
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
| (FStar_Syntax_Syntax.U_max (_34_198), _34_201) -> begin
(- (1))
end
| (_34_204, FStar_Syntax_Syntax.U_max (_34_206)) -> begin
1
end
| _34_210 -> begin
(
# 174 "FStar.Syntax.Util.fst"
let _34_213 = (univ_kernel u1)
in (match (_34_213) with
| (k1, n1) -> begin
(
# 175 "FStar.Syntax.Util.fst"
let _34_216 = (univ_kernel u2)
in (match (_34_216) with
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
let ml_comp : FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (let _115_93 = (let _115_92 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_ML_lid r)
in {FStar_Syntax_Syntax.effect_name = _115_92; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]})
in (FStar_Syntax_Syntax.mk_Comp _115_93)))

# 203 "FStar.Syntax.Util.fst"
let comp_set_flags : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun c f -> (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (_)) | (FStar_Syntax_Syntax.GTotal (_)) -> begin
c
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 206 "FStar.Syntax.Util.fst"
let _34_232 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ((
# 206 "FStar.Syntax.Util.fst"
let _34_234 = ct
in {FStar_Syntax_Syntax.effect_name = _34_234.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _34_234.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _34_234.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})); FStar_Syntax_Syntax.tk = _34_232.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _34_232.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _34_232.FStar_Syntax_Syntax.vars})
end))

# 208 "FStar.Syntax.Util.fst"
let comp_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_34_238) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (_34_241) -> begin
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
| FStar_Syntax_Syntax.Total (_34_249) -> begin
FStar_Syntax_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (_34_252) -> begin
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
let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _34_2 -> (match (_34_2) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _34_266 -> begin
false
end)))))

# 227 "FStar.Syntax.Util.fst"
let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _34_3 -> (match (_34_3) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _34_272 -> begin
false
end))))))

# 229 "FStar.Syntax.Util.fst"
let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _34_4 -> (match (_34_4) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _34_278 -> begin
false
end))))))

# 233 "FStar.Syntax.Util.fst"
let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _34_5 -> (match (_34_5) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _34_284 -> begin
false
end)))))

# 235 "FStar.Syntax.Util.fst"
let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _34_6 -> (match (_34_6) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _34_290 -> begin
false
end)))))

# 237 "FStar.Syntax.Util.fst"
let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid (comp_effect_name c))))

# 241 "FStar.Syntax.Util.fst"
let is_pure_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_34_294) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (_34_297) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
((((is_total_comp c) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Pure_lid)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _34_7 -> (match (_34_7) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _34_304 -> begin
false
end)))))
end))

# 249 "FStar.Syntax.Util.fst"
let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_Ghost_lid l)))

# 254 "FStar.Syntax.Util.fst"
let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))

# 256 "FStar.Syntax.Util.fst"
let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((((is_total_lcomp lc) || (FStar_Ident.lid_equals lc.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals lc.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Pure_lid)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _34_8 -> (match (_34_8) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _34_311 -> begin
false
end))))))

# 262 "FStar.Syntax.Util.fst"
let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))

# 265 "FStar.Syntax.Util.fst"
let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _115_128 = (FStar_Syntax_Subst.compress t)
in _115_128.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_34_315, c) -> begin
(is_pure_or_ghost_comp c)
end
| _34_320 -> begin
true
end))

# 269 "FStar.Syntax.Util.fst"
let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _115_131 = (FStar_Syntax_Subst.compress t)
in _115_131.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_34_323, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid)
end
| _34_330 -> begin
false
end)
end
| _34_332 -> begin
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
| _34_340 -> begin
(t, [])
end)))

# 284 "FStar.Syntax.Util.fst"
let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (match ((let _115_136 = (FStar_Syntax_Subst.compress t)
in _115_136.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (t, _34_344) -> begin
t
end
| _34_348 -> begin
t
end))

# 288 "FStar.Syntax.Util.fst"
let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _115_139 = (FStar_Syntax_Subst.compress t)
in _115_139.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_34_351, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| _req::_ens::(pats, _34_361)::_34_358 -> begin
(
# 294 "FStar.Syntax.Util.fst"
let pats' = (unmeta pats)
in (
# 295 "FStar.Syntax.Util.fst"
let _34_372 = (head_and_args pats')
in (match (_34_372) with
| (head, _34_371) -> begin
(match ((let _115_140 = (un_uinst head)
in _115_140.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _34_375) -> begin
(FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.cons_lid)
end
| _34_379 -> begin
false
end)
end)))
end
| _34_381 -> begin
false
end)
end
| _34_383 -> begin
false
end)
end
| _34_385 -> begin
false
end))

# 306 "FStar.Syntax.Util.fst"
let is_ml_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _34_9 -> (match (_34_9) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _34_392 -> begin
false
end)))))
end
| _34_394 -> begin
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
| FStar_Syntax_Syntax.Total (_34_404) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (_34_407) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (
# 320 "FStar.Syntax.Util.fst"
let _34_411 = ct
in {FStar_Syntax_Syntax.effect_name = _34_411.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = _34_411.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _34_411.FStar_Syntax_Syntax.flags}))
end))

# 322 "FStar.Syntax.Util.fst"
let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _34_10 -> (match (_34_10) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _34_418 -> begin
false
end)))))

# 328 "FStar.Syntax.Util.fst"
let primops : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]

# 345 "FStar.Syntax.Util.fst"
let is_primop = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _34_422) -> begin
(FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v)))
end
| _34_426 -> begin
false
end))

# 349 "FStar.Syntax.Util.fst"
let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (
# 350 "FStar.Syntax.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e, _34_431, _34_433) -> begin
(unascribe e)
end
| _34_437 -> begin
e
end)))

# 355 "FStar.Syntax.Util.fst"
let rec ascribe = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', _34_442, _34_444) -> begin
(ascribe t' k)
end
| _34_448 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((t, k, None))) None t.FStar_Syntax_Syntax.pos)
end))

# 359 "FStar.Syntax.Util.fst"
let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 360 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _34_453) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _34_458, _34_460) -> begin
(unrefine t)
end
| _34_464 -> begin
t
end)))

# 366 "FStar.Syntax.Util.fst"
let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (match ((let _115_157 = (FStar_Syntax_Subst.compress e)
in _115_157.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_34_467) -> begin
true
end
| _34_470 -> begin
false
end))

# 370 "FStar.Syntax.Util.fst"
let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _115_160 = (FStar_Syntax_Subst.compress t)
in _115_160.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_34_473) -> begin
true
end
| _34_476 -> begin
false
end))

# 374 "FStar.Syntax.Util.fst"
let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 375 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _34_481) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _34_486, _34_488) -> begin
(pre_typ t)
end
| _34_492 -> begin
t
end)))

# 381 "FStar.Syntax.Util.fst"
let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.args Prims.option = (fun typ lid -> (
# 382 "FStar.Syntax.Util.fst"
let typ = (FStar_Syntax_Subst.compress typ)
in (match ((let _115_167 = (un_uinst typ)
in _115_167.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 385 "FStar.Syntax.Util.fst"
let head = (un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _34_503) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v lid) -> begin
Some (args)
end
| _34_507 -> begin
None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc, _34_510) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v lid) -> begin
Some ([])
end
| _34_514 -> begin
None
end)))

# 393 "FStar.Syntax.Util.fst"
let rec lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_let (_, _, lids, _)) | (FStar_Syntax_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_datacon (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_declare_typ (lid, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n, _34_598) -> begin
(n.FStar_Syntax_Syntax.mname)::[]
end
| (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) -> begin
[]
end))

# 406 "FStar.Syntax.Util.fst"
let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.option = (fun se -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _34_614 -> begin
None
end))

# 410 "FStar.Syntax.Util.fst"
let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Syntax_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_datacon (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_assume (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_let (_, r, _, _)) | (FStar_Syntax_Syntax.Sig_main (_, r)) | (FStar_Syntax_Syntax.Sig_pragma (_, r)) | (FStar_Syntax_Syntax.Sig_new_effect (_, r)) | (FStar_Syntax_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))

# 423 "FStar.Syntax.Util.fst"
let range_of_lb = (fun _34_11 -> (match (_34_11) with
| (FStar_Util.Inl (x), _34_715, _34_717) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), _34_722, _34_724) -> begin
(FStar_Ident.range_of_lid l)
end))

# 427 "FStar.Syntax.Util.fst"
let range_of_arg = (fun _34_729 -> (match (_34_729) with
| (hd, _34_728) -> begin
hd.FStar_Syntax_Syntax.pos
end))

# 429 "FStar.Syntax.Util.fst"
let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))

# 432 "FStar.Syntax.Util.fst"
let mk_app = (fun f args -> (
# 433 "FStar.Syntax.Util.fst"
let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((f, args))) None r)))

# 436 "FStar.Syntax.Util.fst"
let mk_data = (fun l args -> (match (args) with
| [] -> begin
(let _115_186 = (let _115_185 = (let _115_184 = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (_115_184, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_115_185))
in (FStar_Syntax_Syntax.mk _115_186 None (FStar_Ident.range_of_lid l)))
end
| _34_741 -> begin
(
# 441 "FStar.Syntax.Util.fst"
let e = (let _115_187 = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (mk_app _115_187 args))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))) None e.FStar_Syntax_Syntax.pos))
end))

# 444 "FStar.Syntax.Util.fst"
let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident ((Prims.strcat "^fname^" x.FStar_Ident.idText), x.FStar_Ident.idRange)))

# 445 "FStar.Syntax.Util.fst"
let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _115_193 = (let _115_192 = (FStar_Util.substring_from x.FStar_Ident.idText 7)
in (_115_192, x.FStar_Ident.idRange))
in (FStar_Ident.mk_ident _115_193))
end else begin
x
end)

# 450 "FStar.Syntax.Util.fst"
let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (
# 451 "FStar.Syntax.Util.fst"
let nm = if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _115_203 = (let _115_202 = (let _115_200 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _115_200))
in (let _115_201 = (FStar_Syntax_Syntax.range_of_bv x)
in (_115_202, _115_201)))
in (FStar_Ident.mk_ident _115_203))
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (
# 454 "FStar.Syntax.Util.fst"
let y = (
# 454 "FStar.Syntax.Util.fst"
let _34_749 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = _34_749.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _34_749.FStar_Syntax_Syntax.sort})
in (let _115_207 = (let _115_206 = (let _115_205 = (let _115_204 = (unmangle_field_name nm)
in (_115_204)::[])
in (FStar_List.append (FStar_Ident.ids_of_lid lid) _115_205))
in (FStar_Ident.lid_of_ids _115_206))
in (_115_207, y)))))

# 457 "FStar.Syntax.Util.fst"
let set_uvar = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (_34_755) -> begin
(let _115_212 = (let _115_211 = (let _115_210 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _115_210))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" _115_211))
in (FStar_All.failwith _115_212))
end
| _34_758 -> begin
(FStar_Unionfind.change uv (FStar_Syntax_Syntax.Fixed (t)))
end))

# 462 "FStar.Syntax.Util.fst"
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
| _34_791 -> begin
(q1 = q2)
end))

# 474 "FStar.Syntax.Util.fst"
let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (
# 475 "FStar.Syntax.Util.fst"
let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 478 "FStar.Syntax.Util.fst"
let _34_800 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_34_800) with
| (bs, c) -> begin
if (is_tot_or_gtot_comp c) then begin
(
# 480 "FStar.Syntax.Util.fst"
let _34_803 = (arrow_formals_comp (comp_result c))
in (match (_34_803) with
| (bs', k) -> begin
((FStar_List.append bs bs'), k)
end))
end else begin
(bs, c)
end
end))
end
| _34_805 -> begin
(let _115_219 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _115_219))
end)))

# 485 "FStar.Syntax.Util.fst"
let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.typ) = (fun k -> (
# 486 "FStar.Syntax.Util.fst"
let _34_809 = (arrow_formals_comp k)
in (match (_34_809) with
| (bs, c) -> begin
(bs, (comp_result c))
end)))

# 489 "FStar.Syntax.Util.fst"
let abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> (match (bs) with
| [] -> begin
t
end
| _34_815 -> begin
(
# 492 "FStar.Syntax.Util.fst"
let body = (let _115_228 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress _115_228))
in (match ((body.FStar_Syntax_Syntax.n, lopt)) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t, lopt'), None) -> begin
(let _115_232 = (let _115_231 = (let _115_230 = (let _115_229 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append _115_229 bs'))
in (_115_230, t, lopt))
in FStar_Syntax_Syntax.Tm_abs (_115_231))
in (FStar_Syntax_Syntax.mk _115_232 None t.FStar_Syntax_Syntax.pos))
end
| _34_825 -> begin
(
# 497 "FStar.Syntax.Util.fst"
let lopt = (match (lopt) with
| None -> begin
None
end
| Some (lc) -> begin
(let _115_233 = (FStar_Syntax_Subst.close_lcomp bs lc)
in Some (_115_233))
end)
in (let _115_236 = (let _115_235 = (let _115_234 = (FStar_Syntax_Subst.close_binders bs)
in (_115_234, body, lopt))
in FStar_Syntax_Syntax.Tm_abs (_115_235))
in (FStar_Syntax_Syntax.mk _115_236 None t.FStar_Syntax_Syntax.pos)))
end))
end))

# 502 "FStar.Syntax.Util.fst"
let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| _34_834 -> begin
(let _115_244 = (let _115_243 = (let _115_242 = (FStar_Syntax_Subst.close_binders bs)
in (let _115_241 = (FStar_Syntax_Subst.close_comp bs c)
in (_115_242, _115_241)))
in FStar_Syntax_Syntax.Tm_arrow (_115_243))
in (FStar_Syntax_Syntax.mk _115_244 None c.FStar_Syntax_Syntax.pos))
end))

# 505 "FStar.Syntax.Util.fst"
let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun b t -> (let _115_256 = (let _115_252 = (let _115_251 = (let _115_250 = (let _115_249 = (FStar_Syntax_Syntax.mk_binder b)
in (_115_249)::[])
in (FStar_Syntax_Subst.close _115_250 t))
in (b, _115_251))
in FStar_Syntax_Syntax.Tm_refine (_115_252))
in (let _115_255 = (FStar_ST.read b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (let _115_254 = (let _115_253 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges _115_253 t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk _115_256 _115_255 _115_254)))))

# 506 "FStar.Syntax.Util.fst"
let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))

# 508 "FStar.Syntax.Util.fst"
let mk_letbinding : FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def})

# 515 "FStar.Syntax.Util.fst"
let close_univs_and_mk_letbinding : FStar_Ident.lident Prims.list Prims.option  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def -> (
# 516 "FStar.Syntax.Util.fst"
let def = (match (recs) with
| None -> begin
def
end
| Some (lids) -> begin
(
# 519 "FStar.Syntax.Util.fst"
let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _115_281 -> FStar_Syntax_Syntax.U_name (_115_281))))
in (
# 520 "FStar.Syntax.Util.fst"
let inst = (FStar_All.pipe_right lids (FStar_List.map (fun l -> (l, universes))))
in (FStar_Syntax_InstFV.instantiate inst def)))
end)
in (
# 522 "FStar.Syntax.Util.fst"
let typ = (FStar_Syntax_Subst.close_univ_vars univ_vars typ)
in (
# 523 "FStar.Syntax.Util.fst"
let def = (FStar_Syntax_Subst.close_univ_vars univ_vars def)
in (mk_letbinding lbname univ_vars typ eff def)))))

# 526 "FStar.Syntax.Util.fst"
let open_univ_vars_binders_and_comp : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 529 "FStar.Syntax.Util.fst"
let _34_864 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_34_864) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _34_866 -> begin
(
# 532 "FStar.Syntax.Util.fst"
let t' = (arrow binders c)
in (
# 533 "FStar.Syntax.Util.fst"
let _34_870 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_34_870) with
| (uvs, t') -> begin
(match ((let _115_289 = (FStar_Syntax_Subst.compress t')
in _115_289.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _34_876 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 541 "FStar.Syntax.Util.fst"
let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (l, _34_880) -> begin
(FStar_Util.starts_with l.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.Tuple")
end
| _34_884 -> begin
false
end))

# 545 "FStar.Syntax.Util.fst"
let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 546 "FStar.Syntax.Util.fst"
let t = (let _115_296 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Tuple%s" _115_296))
in (let _115_297 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _115_297 r))))

# 549 "FStar.Syntax.Util.fst"
let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 550 "FStar.Syntax.Util.fst"
let t = (let _115_302 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkTuple%s" _115_302))
in (let _115_303 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _115_303 r))))

# 553 "FStar.Syntax.Util.fst"
let is_tuple_data_lid : FStar_Ident.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _115_308 = (mk_tuple_data_lid n FStar_Range.dummyRange)
in (FStar_Ident.lid_equals f _115_308)))

# 556 "FStar.Syntax.Util.fst"
let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (l, _34_896) -> begin
(FStar_Util.starts_with l.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.DTuple")
end
| _34_900 -> begin
false
end))

# 560 "FStar.Syntax.Util.fst"
let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 561 "FStar.Syntax.Util.fst"
let t = (let _115_315 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "DTuple%s" _115_315))
in (let _115_316 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _115_316 r))))

# 564 "FStar.Syntax.Util.fst"
let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 565 "FStar.Syntax.Util.fst"
let t = (let _115_321 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkDTuple%s" _115_321))
in (let _115_322 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _115_322 r))))

# 568 "FStar.Syntax.Util.fst"
let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> (FStar_Ident.lid_equals x FStar_Syntax_Const.eq2_lid))

# 570 "FStar.Syntax.Util.fst"
let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.forall_lid))

# 571 "FStar.Syntax.Util.fst"
let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.exists_lid))

# 572 "FStar.Syntax.Util.fst"
let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))

# 573 "FStar.Syntax.Util.fst"
let is_equality = (fun x -> (is_lid_equality x.FStar_Syntax_Syntax.v))

# 575 "FStar.Syntax.Util.fst"
let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (
# 576 "FStar.Syntax.Util.fst"
let lst = (FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.not_lid)::(FStar_Syntax_Const.iff_lid)::(FStar_Syntax_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))

# 580 "FStar.Syntax.Util.fst"
let is_constructor : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _115_338 = (pre_typ t)
in _115_338.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _34_918) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v lid)
end
| _34_922 -> begin
false
end))

# 585 "FStar.Syntax.Util.fst"
let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _115_343 = (pre_typ t)
in _115_343.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (_34_926) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t, _34_930) -> begin
(is_constructed_typ t lid)
end
| _34_934 -> begin
false
end))

# 590 "FStar.Syntax.Util.fst"
let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun t -> (
# 591 "FStar.Syntax.Util.fst"
let t = (pre_typ t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_app (t, _34_948) -> begin
(get_tycon t)
end
| _34_952 -> begin
None
end)))

# 599 "FStar.Syntax.Util.fst"
let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _34_958 _34_962 -> (match ((_34_958, _34_962)) with
| ((fn1, _34_957), (fn2, _34_961)) -> begin
(FStar_String.compare (FStar_Ident.text_of_lid fn1) (FStar_Ident.text_of_lid fn2))
end)))))

# 606 "FStar.Syntax.Util.fst"
let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (
# 607 "FStar.Syntax.Util.fst"
let theory_syms = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))

# 629 "FStar.Syntax.Util.fst"
let ktype : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None FStar_Range.dummyRange)

# 630 "FStar.Syntax.Util.fst"
let ktype0 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) None FStar_Range.dummyRange)

# 633 "FStar.Syntax.Util.fst"
let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun _34_965 -> (match (()) with
| () -> begin
(
# 634 "FStar.Syntax.Util.fst"
let u = (let _115_354 = (FStar_Unionfind.fresh None)
in (FStar_All.pipe_left (fun _115_353 -> FStar_Syntax_Syntax.U_unif (_115_353)) _115_354))
in (let _115_355 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None FStar_Range.dummyRange)
in (_115_355, u)))
end))

# 637 "FStar.Syntax.Util.fst"
let kt_kt : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Const.kunary ktype0 ktype0)

# 638 "FStar.Syntax.Util.fst"
let kt_kt_kt : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Const.kbin ktype0 ktype0 ktype0)

# 640 "FStar.Syntax.Util.fst"
let tand : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.and_lid FStar_Range.dummyRange)

# 641 "FStar.Syntax.Util.fst"
let tor : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.or_lid FStar_Range.dummyRange)

# 642 "FStar.Syntax.Util.fst"
let timp : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.imp_lid FStar_Range.dummyRange)

# 643 "FStar.Syntax.Util.fst"
let tiff : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.iff_lid FStar_Range.dummyRange)

# 644 "FStar.Syntax.Util.fst"
let t_bool : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.bool_lid FStar_Range.dummyRange)

# 645 "FStar.Syntax.Util.fst"
let t_false : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.false_lid FStar_Range.dummyRange)

# 646 "FStar.Syntax.Util.fst"
let t_true : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid FStar_Range.dummyRange)

# 647 "FStar.Syntax.Util.fst"
let b2t_v : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.b2t_lid FStar_Range.dummyRange)

# 648 "FStar.Syntax.Util.fst"
let t_not : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.not_lid FStar_Range.dummyRange)

# 650 "FStar.Syntax.Util.fst"
let mk_conj_opt : FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _115_367 = (let _115_366 = (let _115_364 = (let _115_363 = (let _115_362 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _115_361 = (let _115_360 = (FStar_Syntax_Syntax.as_arg phi2)
in (_115_360)::[])
in (_115_362)::_115_361))
in (tand, _115_363))
in FStar_Syntax_Syntax.Tm_app (_115_364))
in (let _115_365 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _115_366 None _115_365)))
in Some (_115_367))
end))

# 653 "FStar.Syntax.Util.fst"
let mk_binop = (fun op_t phi1 phi2 -> (let _115_377 = (let _115_375 = (let _115_374 = (let _115_373 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _115_372 = (let _115_371 = (FStar_Syntax_Syntax.as_arg phi2)
in (_115_371)::[])
in (_115_373)::_115_372))
in (op_t, _115_374))
in FStar_Syntax_Syntax.Tm_app (_115_375))
in (let _115_376 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _115_377 None _115_376))))

# 654 "FStar.Syntax.Util.fst"
let mk_neg = (fun phi -> (let _115_382 = (let _115_381 = (let _115_380 = (let _115_379 = (FStar_Syntax_Syntax.as_arg phi)
in (_115_379)::[])
in (t_not, _115_380))
in FStar_Syntax_Syntax.Tm_app (_115_381))
in (FStar_Syntax_Syntax.mk _115_382 None phi.FStar_Syntax_Syntax.pos)))

# 655 "FStar.Syntax.Util.fst"
let mk_conj = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))

# 656 "FStar.Syntax.Util.fst"
let mk_conj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid FStar_Range.dummyRange)
end
| hd::tl -> begin
(FStar_List.fold_right mk_conj tl hd)
end))

# 659 "FStar.Syntax.Util.fst"
let mk_disj = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))

# 660 "FStar.Syntax.Util.fst"
let mk_disj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
t_false
end
| hd::tl -> begin
(FStar_List.fold_right mk_disj tl hd)
end))

# 663 "FStar.Syntax.Util.fst"
let mk_imp : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (match ((let _115_395 = (FStar_Syntax_Subst.compress phi1)
in _115_395.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _34_994) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.false_lid) -> begin
t_true
end
| FStar_Syntax_Syntax.Tm_fvar (tc, _34_999) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
phi2
end
| _34_1003 -> begin
(match ((let _115_396 = (FStar_Syntax_Subst.compress phi2)
in _115_396.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _34_1006) when ((FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) || (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.false_lid)) -> begin
phi2
end
| _34_1010 -> begin
(mk_binop timp phi1 phi2)
end)
end))

# 673 "FStar.Syntax.Util.fst"
let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))

# 674 "FStar.Syntax.Util.fst"
let b2t = (fun e -> (let _115_403 = (let _115_402 = (let _115_401 = (let _115_400 = (FStar_Syntax_Syntax.as_arg e)
in (_115_400)::[])
in (b2t_v, _115_401))
in FStar_Syntax_Syntax.Tm_app (_115_402))
in (FStar_Syntax_Syntax.mk _115_403 None e.FStar_Syntax_Syntax.pos)))

# 676 "FStar.Syntax.Util.fst"
let eq_pred_t : FStar_Syntax_Syntax.typ = (
# 677 "FStar.Syntax.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv None ktype0)
in (
# 678 "FStar.Syntax.Util.fst"
let atyp = (FStar_Syntax_Syntax.bv_to_tm a)
in (
# 679 "FStar.Syntax.Util.fst"
let b = (FStar_Syntax_Syntax.new_bv None ktype0)
in (
# 680 "FStar.Syntax.Util.fst"
let btyp = (FStar_Syntax_Syntax.bv_to_tm b)
in (let _115_410 = (let _115_408 = (let _115_407 = (let _115_406 = (FStar_Syntax_Syntax.null_binder atyp)
in (let _115_405 = (let _115_404 = (FStar_Syntax_Syntax.null_binder btyp)
in (_115_404)::[])
in (_115_406)::_115_405))
in ((b, Some (FStar_Syntax_Syntax.imp_tag)))::_115_407)
in ((a, Some (FStar_Syntax_Syntax.imp_tag)))::_115_408)
in (let _115_409 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (arrow _115_410 _115_409)))))))

# 684 "FStar.Syntax.Util.fst"
let teq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.eq2_lid FStar_Range.dummyRange)

# 686 "FStar.Syntax.Util.fst"
let mk_eq = (fun t1 t2 e1 e2 -> (let _115_421 = (let _115_419 = (let _115_418 = (let _115_417 = (FStar_Syntax_Syntax.as_arg e1)
in (let _115_416 = (let _115_415 = (FStar_Syntax_Syntax.as_arg e2)
in (_115_415)::[])
in (_115_417)::_115_416))
in (teq, _115_418))
in FStar_Syntax_Syntax.Tm_app (_115_419))
in (let _115_420 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _115_421 None _115_420))))

# 688 "FStar.Syntax.Util.fst"
let mk_has_type = (fun t x t' -> (
# 689 "FStar.Syntax.Util.fst"
let t_has_type = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.has_type_lid FStar_Range.dummyRange)
in (
# 690 "FStar.Syntax.Util.fst"
let t_has_type = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((t_has_type, (FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]))) None FStar_Range.dummyRange)
in (let _115_432 = (let _115_431 = (let _115_430 = (let _115_429 = (FStar_Syntax_Syntax.iarg t)
in (let _115_428 = (let _115_427 = (FStar_Syntax_Syntax.as_arg x)
in (let _115_426 = (let _115_425 = (FStar_Syntax_Syntax.as_arg t')
in (_115_425)::[])
in (_115_427)::_115_426))
in (_115_429)::_115_428))
in (t_has_type, _115_430))
in FStar_Syntax_Syntax.Tm_app (_115_431))
in (FStar_Syntax_Syntax.mk _115_432 None FStar_Range.dummyRange)))))

# 693 "FStar.Syntax.Util.fst"
let lex_t : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid FStar_Range.dummyRange)

# 694 "FStar.Syntax.Util.fst"
let lex_top : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Data_ctor)) FStar_Syntax_Const.lextop_lid FStar_Range.dummyRange)

# 695 "FStar.Syntax.Util.fst"
let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Data_ctor)) FStar_Syntax_Const.lexcons_lid FStar_Range.dummyRange)

# 696 "FStar.Syntax.Util.fst"
let forall_t : FStar_Syntax_Syntax.typ = (
# 697 "FStar.Syntax.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv None ktype0)
in (
# 698 "FStar.Syntax.Util.fst"
let atyp = (FStar_Syntax_Syntax.bv_to_tm a)
in (let _115_436 = (let _115_434 = (let _115_433 = (FStar_Syntax_Syntax.null_binder atyp)
in (_115_433)::[])
in ((a, Some (FStar_Syntax_Syntax.imp_tag)))::_115_434)
in (let _115_435 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (arrow _115_436 _115_435)))))

# 700 "FStar.Syntax.Util.fst"
let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.forall_lid FStar_Range.dummyRange)

# 702 "FStar.Syntax.Util.fst"
let lcomp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (
# 703 "FStar.Syntax.Util.fst"
let c = (comp_to_comp_typ c0)
in {FStar_Syntax_Syntax.eff_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.res_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.cflags = c.FStar_Syntax_Syntax.flags; FStar_Syntax_Syntax.comp = (fun _34_1031 -> (match (()) with
| () -> begin
c0
end))}))

# 709 "FStar.Syntax.Util.fst"
let mk_forall : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun x body -> (let _115_453 = (let _115_452 = (let _115_451 = (let _115_450 = (let _115_449 = (let _115_448 = (let _115_444 = (FStar_Syntax_Syntax.mk_binder x)
in (_115_444)::[])
in (let _115_447 = (let _115_446 = (let _115_445 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (FStar_All.pipe_left lcomp_of_comp _115_445))
in Some (_115_446))
in (abs _115_448 body _115_447)))
in (FStar_Syntax_Syntax.as_arg _115_449))
in (_115_450)::[])
in (tforall, _115_451))
in FStar_Syntax_Syntax.Tm_app (_115_452))
in (FStar_Syntax_Syntax.mk _115_453 None FStar_Range.dummyRange)))

# 712 "FStar.Syntax.Util.fst"
let rec close_forall : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
f
end else begin
(mk_forall (Prims.fst b) f)
end) bs f))

# 715 "FStar.Syntax.Util.fst"
let rec is_wild_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (_34_1040) -> begin
true
end
| _34_1043 -> begin
false
end))

# 720 "FStar.Syntax.Util.fst"
let if_then_else = (fun b t1 t2 -> (
# 721 "FStar.Syntax.Util.fst"
let then_branch = (let _115_464 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t1.FStar_Syntax_Syntax.pos)
in (_115_464, None, t1))
in (
# 722 "FStar.Syntax.Util.fst"
let else_branch = (let _115_465 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Syntax_Syntax.pos)
in (_115_465, None, t2))
in (let _115_467 = (let _115_466 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos _115_466))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((b, (then_branch)::(else_branch)::[]))) None _115_467)))))

# 728 "FStar.Syntax.Util.fst"
type qpats =
FStar_Syntax_Syntax.args Prims.list

# 729 "FStar.Syntax.Util.fst"
type connective =
| QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args)

# 730 "FStar.Syntax.Util.fst"
let is_QAll = (fun _discr_ -> (match (_discr_) with
| QAll (_) -> begin
true
end
| _ -> begin
false
end))

# 731 "FStar.Syntax.Util.fst"
let is_QEx = (fun _discr_ -> (match (_discr_) with
| QEx (_) -> begin
true
end
| _ -> begin
false
end))

# 732 "FStar.Syntax.Util.fst"
let is_BaseConn = (fun _discr_ -> (match (_discr_) with
| BaseConn (_) -> begin
true
end
| _ -> begin
false
end))

# 730 "FStar.Syntax.Util.fst"
let ___QAll____0 : connective  ->  (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) = (fun projectee -> (match (projectee) with
| QAll (_34_1051) -> begin
_34_1051
end))

# 731 "FStar.Syntax.Util.fst"
let ___QEx____0 : connective  ->  (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) = (fun projectee -> (match (projectee) with
| QEx (_34_1054) -> begin
_34_1054
end))

# 732 "FStar.Syntax.Util.fst"
let ___BaseConn____0 : connective  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.args) = (fun projectee -> (match (projectee) with
| BaseConn (_34_1057) -> begin
_34_1057
end))

# 734 "FStar.Syntax.Util.fst"
let destruct_typ_as_formula : FStar_Syntax_Syntax.term  ->  connective Prims.option = (fun f -> (
# 735 "FStar.Syntax.Util.fst"
let destruct_base_conn = (fun f -> (
# 736 "FStar.Syntax.Util.fst"
let connectives = ((FStar_Syntax_Const.true_lid, 0))::((FStar_Syntax_Const.false_lid, 0))::((FStar_Syntax_Const.and_lid, 2))::((FStar_Syntax_Const.or_lid, 2))::((FStar_Syntax_Const.imp_lid, 2))::((FStar_Syntax_Const.iff_lid, 2))::((FStar_Syntax_Const.ite_lid, 3))::((FStar_Syntax_Const.not_lid, 1))::((FStar_Syntax_Const.eq2_lid, 4))::((FStar_Syntax_Const.eq2_lid, 2))::[]
in (
# 747 "FStar.Syntax.Util.fst"
let rec aux = (fun f _34_1066 -> (match (_34_1066) with
| (lid, arity) -> begin
(
# 748 "FStar.Syntax.Util.fst"
let _34_1069 = (head_and_args f)
in (match (_34_1069) with
| (t, args) -> begin
(
# 749 "FStar.Syntax.Util.fst"
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
# 756 "FStar.Syntax.Util.fst"
let patterns = (fun t -> (
# 757 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(let _115_520 = (FStar_Syntax_Subst.compress t)
in (pats, _115_520))
end
| _34_1080 -> begin
(let _115_521 = (FStar_Syntax_Subst.compress t)
in ([], _115_521))
end)))
in (
# 762 "FStar.Syntax.Util.fst"
let destruct_q_conn = (fun t -> (
# 763 "FStar.Syntax.Util.fst"
let is_q = (fun fa l -> if fa then begin
(is_forall l)
end else begin
(is_exists l)
end)
in (
# 764 "FStar.Syntax.Util.fst"
let flat = (fun t -> (
# 765 "FStar.Syntax.Util.fst"
let _34_1090 = (head_and_args t)
in (match (_34_1090) with
| (t, args) -> begin
(let _115_533 = (un_uinst t)
in (let _115_532 = (FStar_All.pipe_right args (FStar_List.map (fun _34_1093 -> (match (_34_1093) with
| (t, imp) -> begin
(let _115_531 = (unascribe t)
in (_115_531, imp))
end))))
in (_115_533, _115_532)))
end)))
in (
# 767 "FStar.Syntax.Util.fst"
let rec aux = (fun qopt out t -> (match ((let _115_540 = (flat t)
in (qopt, _115_540))) with
| ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) | ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _::({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) when (is_q fa tc.FStar_Syntax_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) | ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _::({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) when (is_qlid tc.FStar_Syntax_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (Some (b), _34_1232) -> begin
(
# 779 "FStar.Syntax.Util.fst"
let bs = (FStar_List.rev out)
in (
# 780 "FStar.Syntax.Util.fst"
let _34_1237 = (FStar_Syntax_Subst.open_term bs t)
in (match (_34_1237) with
| (bs, t) -> begin
(
# 781 "FStar.Syntax.Util.fst"
let _34_1240 = (patterns t)
in (match (_34_1240) with
| (pats, body) -> begin
if b then begin
Some (QAll ((bs, pats, body)))
end else begin
Some (QEx ((bs, pats, body)))
end
end))
end)))
end
| _34_1242 -> begin
None
end))
in (aux None [] t)))))
in (
# 789 "FStar.Syntax.Util.fst"
let phi = (FStar_Syntax_Subst.compress f)
in (match ((destruct_base_conn phi)) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end))))))




