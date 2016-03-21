
open Prims
# 29 "FStar.Syntax.Util.fst"
let handle_err : Prims.bool  ->  Prims.exn  ->  Prims.unit = (fun warning e -> (match (e) with
| FStar_Syntax_Syntax.Error (msg, r) -> begin
(let _118_6 = (let _118_5 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s : %s\n%s\n" _118_5 (if warning then begin
"Warning"
end else begin
"Error"
end) msg))
in (FStar_Util.print_string _118_6))
end
| FStar_Util.NYI (s) -> begin
(let _118_7 = (FStar_Util.format1 "Feature not yet implemented: %s" s)
in (FStar_Util.print_string _118_7))
end
| FStar_Syntax_Syntax.Err (s) -> begin
(let _118_8 = (FStar_Util.format1 "Error: %s" s)
in (FStar_Util.print_string _118_8))
end
| _34_23 -> begin
(Prims.raise e)
end))

# 39 "FStar.Syntax.Util.fst"
let handleable : Prims.exn  ->  Prims.bool = (fun _34_1 -> (match (_34_1) with
| (FStar_Syntax_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Syntax_Syntax.Err (_)) -> begin
true
end
| _34_35 -> begin
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
let arg_of_non_null_binder = (fun _34_41 -> (match (_34_41) with
| (b, imp) -> begin
(let _118_16 = (FStar_Syntax_Syntax.bv_to_name b)
in (_118_16, imp))
end))

# 59 "FStar.Syntax.Util.fst"
let args_of_non_null_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
[]
end else begin
(let _118_20 = (arg_of_non_null_binder b)
in (_118_20)::[])
end))))

# 64 "FStar.Syntax.Util.fst"
let args_of_binders : FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun binders -> (let _118_27 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
(
# 67 "FStar.Syntax.Util.fst"
let b = (let _118_24 = (FStar_Syntax_Syntax.new_bv None (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_118_24, (Prims.snd b)))
in (let _118_25 = (arg_of_non_null_binder b)
in (b, _118_25)))
end else begin
(let _118_26 = (arg_of_non_null_binder b)
in (b, _118_26))
end)))
in (FStar_All.pipe_right _118_27 FStar_List.unzip)))

# 71 "FStar.Syntax.Util.fst"
let name_binders : FStar_Syntax_Syntax.binder Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
(
# 74 "FStar.Syntax.Util.fst"
let _34_52 = b
in (match (_34_52) with
| (a, imp) -> begin
(
# 75 "FStar.Syntax.Util.fst"
let b = (let _118_33 = (let _118_32 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _118_32))
in (FStar_Ident.id_of_text _118_33))
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
(let _118_37 = (let _118_36 = (let _118_35 = (name_binders binders)
in (_118_35, comp))
in FStar_Syntax_Syntax.Tm_arrow (_118_36))
in (FStar_Syntax_Syntax.mk _118_37 None t.FStar_Syntax_Syntax.pos))
end
| _34_61 -> begin
t
end))

# 84 "FStar.Syntax.Util.fst"
let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _34_65 -> (match (_34_65) with
| (t, imp) -> begin
(let _118_42 = (let _118_41 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left Prims.fst _118_41))
in (_118_42, imp))
end)))))

# 87 "FStar.Syntax.Util.fst"
let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _34_69 -> (match (_34_69) with
| (t, imp) -> begin
(let _118_46 = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (_118_46, imp))
end)))))

# 90 "FStar.Syntax.Util.fst"
let binders_of_freevars : (FStar_Syntax_Syntax.bv Prims.list * (FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  Prims.bool))  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (let _118_55 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _118_55 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))

# 92 "FStar.Syntax.Util.fst"
let mk_subst = (fun s -> (s)::[])

# 94 "FStar.Syntax.Util.fst"
let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> if ((FStar_List.length formals) = (FStar_List.length actuals)) then begin
(FStar_List.fold_right2 (fun f a out -> (FStar_Syntax_Syntax.NT (((Prims.fst f), (Prims.fst a))))::out) formals actuals [])
end else begin
(FStar_All.failwith "Ill-formed substitution")
end)

# 101 "FStar.Syntax.Util.fst"
let rec unmeta : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (
# 102 "FStar.Syntax.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_meta (e, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e, _, _)) -> begin
(unmeta e)
end
| _34_91 -> begin
e
end)))

# 114 "FStar.Syntax.Util.fst"
let rec univ_kernel : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.universe * Prims.int) = (fun u -> (match (u) with
| (FStar_Syntax_Syntax.U_unknown) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
(u, 0)
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(
# 119 "FStar.Syntax.Util.fst"
let _34_105 = (univ_kernel u)
in (match (_34_105) with
| (k, n) -> begin
(k, (n + 1))
end))
end
| (FStar_Syntax_Syntax.U_max (_)) | (FStar_Syntax_Syntax.U_bvar (_)) -> begin
(FStar_All.failwith "Imposible")
end))

# 125 "FStar.Syntax.Util.fst"
let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (let _118_70 = (univ_kernel u)
in (Prims.snd _118_70)))

# 133 "FStar.Syntax.Util.fst"
let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match ((u1, u2)) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) -> begin
(FStar_All.failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
0
end
| (FStar_Syntax_Syntax.U_unknown, _34_132) -> begin
(- (1))
end
| (_34_135, FStar_Syntax_Syntax.U_unknown) -> begin
1
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
0
end
| (FStar_Syntax_Syntax.U_zero, _34_143) -> begin
(- (1))
end
| (_34_146, FStar_Syntax_Syntax.U_zero) -> begin
1
end
| (FStar_Syntax_Syntax.U_name (u1), FStar_Syntax_Syntax.U_name (u2)) -> begin
(FStar_String.compare u1.FStar_Ident.idText u2.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (_34_155), FStar_Syntax_Syntax.U_unif (_34_158)) -> begin
(- (1))
end
| (FStar_Syntax_Syntax.U_unif (_34_162), FStar_Syntax_Syntax.U_name (_34_165)) -> begin
1
end
| (FStar_Syntax_Syntax.U_unif (u1), FStar_Syntax_Syntax.U_unif (u2)) -> begin
((FStar_Unionfind.uvar_id u1) - (FStar_Unionfind.uvar_id u2))
end
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(
# 152 "FStar.Syntax.Util.fst"
let n1 = (FStar_List.length us1)
in (
# 153 "FStar.Syntax.Util.fst"
let n2 = (FStar_List.length us2)
in if (n1 <> n2) then begin
(n1 - n2)
end else begin
(
# 156 "FStar.Syntax.Util.fst"
let copt = (let _118_76 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map _118_76 (fun _34_182 -> (match (_34_182) with
| (u1, u2) -> begin
(
# 157 "FStar.Syntax.Util.fst"
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
| (FStar_Syntax_Syntax.U_max (_34_189), _34_192) -> begin
(- (1))
end
| (_34_195, FStar_Syntax_Syntax.U_max (_34_197)) -> begin
1
end
| _34_201 -> begin
(
# 170 "FStar.Syntax.Util.fst"
let _34_204 = (univ_kernel u1)
in (match (_34_204) with
| (k1, n1) -> begin
(
# 171 "FStar.Syntax.Util.fst"
let _34_207 = (univ_kernel u2)
in (match (_34_207) with
| (k2, n2) -> begin
(
# 172 "FStar.Syntax.Util.fst"
let r = (compare_univs k1 k2)
in if (r = 0) then begin
(n1 - n2)
end else begin
r
end)
end))
end))
end))

# 177 "FStar.Syntax.Util.fst"
let eq_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.bool = (fun u1 u2 -> ((compare_univs u1 u2) = 0))

# 183 "FStar.Syntax.Util.fst"
let ml_comp : FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (let _118_86 = (let _118_85 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_ML_lid r)
in {FStar_Syntax_Syntax.effect_name = _118_85; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]})
in (FStar_Syntax_Syntax.mk_Comp _118_86)))

# 199 "FStar.Syntax.Util.fst"
let comp_set_flags : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun c f -> (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (_)) | (FStar_Syntax_Syntax.GTotal (_)) -> begin
c
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 202 "FStar.Syntax.Util.fst"
let _34_223 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ((
# 202 "FStar.Syntax.Util.fst"
let _34_225 = ct
in {FStar_Syntax_Syntax.effect_name = _34_225.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _34_225.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _34_225.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})); FStar_Syntax_Syntax.tk = _34_223.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _34_223.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _34_223.FStar_Syntax_Syntax.vars})
end))

# 204 "FStar.Syntax.Util.fst"
let comp_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_34_229) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (_34_232) -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.flags
end))

# 209 "FStar.Syntax.Util.fst"
let comp_effect_name = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
c.FStar_Syntax_Syntax.effect_name
end
| FStar_Syntax_Syntax.Total (_34_240) -> begin
FStar_Syntax_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (_34_243) -> begin
FStar_Syntax_Const.effect_GTot_lid
end))

# 214 "FStar.Syntax.Util.fst"
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

# 220 "FStar.Syntax.Util.fst"
let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _34_2 -> (match (_34_2) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _34_257 -> begin
false
end)))))

# 223 "FStar.Syntax.Util.fst"
let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _34_3 -> (match (_34_3) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _34_263 -> begin
false
end))))))

# 225 "FStar.Syntax.Util.fst"
let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _34_4 -> (match (_34_4) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _34_269 -> begin
false
end))))))

# 229 "FStar.Syntax.Util.fst"
let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _34_5 -> (match (_34_5) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _34_275 -> begin
false
end)))))

# 231 "FStar.Syntax.Util.fst"
let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _34_6 -> (match (_34_6) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _34_281 -> begin
false
end)))))

# 233 "FStar.Syntax.Util.fst"
let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid (comp_effect_name c))))

# 237 "FStar.Syntax.Util.fst"
let is_pure_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_34_285) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (_34_288) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
((((is_total_comp c) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Pure_lid)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _34_7 -> (match (_34_7) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _34_295 -> begin
false
end)))))
end))

# 245 "FStar.Syntax.Util.fst"
let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_Ghost_lid l)))

# 250 "FStar.Syntax.Util.fst"
let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))

# 252 "FStar.Syntax.Util.fst"
let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((((is_total_lcomp lc) || (FStar_Ident.lid_equals lc.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals lc.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Pure_lid)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _34_8 -> (match (_34_8) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _34_302 -> begin
false
end))))))

# 258 "FStar.Syntax.Util.fst"
let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))

# 261 "FStar.Syntax.Util.fst"
let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _118_121 = (FStar_Syntax_Subst.compress t)
in _118_121.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_34_306, c) -> begin
(is_pure_or_ghost_comp c)
end
| _34_311 -> begin
true
end))

# 265 "FStar.Syntax.Util.fst"
let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _118_124 = (FStar_Syntax_Subst.compress t)
in _118_124.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_34_314, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid)
end
| _34_321 -> begin
false
end)
end
| _34_323 -> begin
false
end))

# 274 "FStar.Syntax.Util.fst"
let head_and_args : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.args) = (fun t -> (
# 275 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(head, args)
end
| _34_331 -> begin
(t, [])
end)))

# 280 "FStar.Syntax.Util.fst"
let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 281 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (t, _34_336) -> begin
(FStar_Syntax_Subst.compress t)
end
| _34_340 -> begin
t
end)))

# 286 "FStar.Syntax.Util.fst"
let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _118_131 = (FStar_Syntax_Subst.compress t)
in _118_131.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_34_343, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| _req::_ens::(pats, _34_353)::_34_350 -> begin
(
# 292 "FStar.Syntax.Util.fst"
let pats' = (unmeta pats)
in (
# 293 "FStar.Syntax.Util.fst"
let _34_364 = (head_and_args pats')
in (match (_34_364) with
| (head, _34_363) -> begin
(match ((let _118_132 = (un_uinst head)
in _118_132.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid)
end
| _34_368 -> begin
false
end)
end)))
end
| _34_370 -> begin
false
end)
end
| _34_372 -> begin
false
end)
end
| _34_374 -> begin
false
end))

# 304 "FStar.Syntax.Util.fst"
let is_ml_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _34_9 -> (match (_34_9) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _34_381 -> begin
false
end)))))
end
| _34_383 -> begin
false
end))

# 310 "FStar.Syntax.Util.fst"
let comp_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (t)) | (FStar_Syntax_Syntax.GTotal (t)) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))

# 315 "FStar.Syntax.Util.fst"
let set_result_typ = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_34_393) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (_34_396) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (
# 318 "FStar.Syntax.Util.fst"
let _34_400 = ct
in {FStar_Syntax_Syntax.effect_name = _34_400.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = _34_400.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _34_400.FStar_Syntax_Syntax.flags}))
end))

# 320 "FStar.Syntax.Util.fst"
let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _34_10 -> (match (_34_10) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _34_407 -> begin
false
end)))))

# 326 "FStar.Syntax.Util.fst"
let primops : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]

# 342 "FStar.Syntax.Util.fst"
let is_primop_lid : FStar_Ident.lident  ->  Prims.bool = (fun l -> (FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals l))))

# 344 "FStar.Syntax.Util.fst"
let is_primop = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_primop_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| _34_413 -> begin
false
end))

# 348 "FStar.Syntax.Util.fst"
let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (
# 349 "FStar.Syntax.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e, _34_418, _34_420) -> begin
(unascribe e)
end
| _34_424 -> begin
e
end)))

# 354 "FStar.Syntax.Util.fst"
let rec ascribe = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', _34_429, _34_431) -> begin
(ascribe t' k)
end
| _34_435 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((t, k, None))) None t.FStar_Syntax_Syntax.pos)
end))

# 358 "FStar.Syntax.Util.fst"
let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 359 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _34_440) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _34_445, _34_447) -> begin
(unrefine t)
end
| _34_451 -> begin
t
end)))

# 365 "FStar.Syntax.Util.fst"
let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (match ((let _118_151 = (FStar_Syntax_Subst.compress e)
in _118_151.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_34_454) -> begin
true
end
| _34_457 -> begin
false
end))

# 369 "FStar.Syntax.Util.fst"
let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _118_154 = (FStar_Syntax_Subst.compress t)
in _118_154.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_34_460) -> begin
true
end
| _34_463 -> begin
false
end))

# 373 "FStar.Syntax.Util.fst"
let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 374 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _34_468) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _34_473, _34_475) -> begin
(pre_typ t)
end
| _34_479 -> begin
t
end)))

# 380 "FStar.Syntax.Util.fst"
let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.args Prims.option = (fun typ lid -> (
# 381 "FStar.Syntax.Util.fst"
let typ = (FStar_Syntax_Subst.compress typ)
in (match ((let _118_161 = (un_uinst typ)
in _118_161.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 384 "FStar.Syntax.Util.fst"
let head = (un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
Some (args)
end
| _34_491 -> begin
None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
Some ([])
end
| _34_495 -> begin
None
end)))

# 392 "FStar.Syntax.Util.fst"
let rec lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_let (_, _, lids, _)) | (FStar_Syntax_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_datacon (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_declare_typ (lid, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n, _34_579) -> begin
(n.FStar_Syntax_Syntax.mname)::[]
end
| (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) -> begin
[]
end))

# 405 "FStar.Syntax.Util.fst"
let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.option = (fun se -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _34_595 -> begin
None
end))

# 409 "FStar.Syntax.Util.fst"
let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Syntax_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_datacon (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_assume (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_let (_, r, _, _)) | (FStar_Syntax_Syntax.Sig_main (_, r)) | (FStar_Syntax_Syntax.Sig_pragma (_, r)) | (FStar_Syntax_Syntax.Sig_new_effect (_, r)) | (FStar_Syntax_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))

# 422 "FStar.Syntax.Util.fst"
let range_of_lb = (fun _34_11 -> (match (_34_11) with
| (FStar_Util.Inl (x), _34_696, _34_698) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), _34_703, _34_705) -> begin
(FStar_Ident.range_of_lid l)
end))

# 426 "FStar.Syntax.Util.fst"
let range_of_arg = (fun _34_710 -> (match (_34_710) with
| (hd, _34_709) -> begin
hd.FStar_Syntax_Syntax.pos
end))

# 428 "FStar.Syntax.Util.fst"
let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))

# 431 "FStar.Syntax.Util.fst"
let mk_app = (fun f args -> (
# 432 "FStar.Syntax.Util.fst"
let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((f, args))) None r)))

# 435 "FStar.Syntax.Util.fst"
let mk_data = (fun l args -> (match (args) with
| [] -> begin
(let _118_180 = (let _118_179 = (let _118_178 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_118_178, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_118_179))
in (FStar_Syntax_Syntax.mk _118_180 None (FStar_Ident.range_of_lid l)))
end
| _34_722 -> begin
(
# 440 "FStar.Syntax.Util.fst"
let e = (let _118_181 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app _118_181 args))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))) None e.FStar_Syntax_Syntax.pos))
end))

# 443 "FStar.Syntax.Util.fst"
let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident ((Prims.strcat "^fname^" x.FStar_Ident.idText), x.FStar_Ident.idRange)))

# 444 "FStar.Syntax.Util.fst"
let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _118_187 = (let _118_186 = (FStar_Util.substring_from x.FStar_Ident.idText 7)
in (_118_186, x.FStar_Ident.idRange))
in (FStar_Ident.mk_ident _118_187))
end else begin
x
end)

# 449 "FStar.Syntax.Util.fst"
let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (
# 450 "FStar.Syntax.Util.fst"
let nm = if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _118_197 = (let _118_196 = (let _118_194 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _118_194))
in (let _118_195 = (FStar_Syntax_Syntax.range_of_bv x)
in (_118_196, _118_195)))
in (FStar_Ident.mk_ident _118_197))
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (
# 453 "FStar.Syntax.Util.fst"
let y = (
# 453 "FStar.Syntax.Util.fst"
let _34_730 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = _34_730.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _34_730.FStar_Syntax_Syntax.sort})
in (let _118_201 = (let _118_200 = (let _118_199 = (let _118_198 = (unmangle_field_name nm)
in (_118_198)::[])
in (FStar_List.append (FStar_Ident.ids_of_lid lid) _118_199))
in (FStar_Ident.lid_of_ids _118_200))
in (_118_201, y)))))

# 456 "FStar.Syntax.Util.fst"
let set_uvar = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (_34_736) -> begin
(let _118_206 = (let _118_205 = (let _118_204 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _118_204))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" _118_205))
in (FStar_All.failwith _118_206))
end
| _34_739 -> begin
(FStar_Unionfind.change uv (FStar_Syntax_Syntax.Fixed (t)))
end))

# 461 "FStar.Syntax.Util.fst"
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
| _34_772 -> begin
(q1 = q2)
end))

# 473 "FStar.Syntax.Util.fst"
let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (
# 474 "FStar.Syntax.Util.fst"
let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 477 "FStar.Syntax.Util.fst"
let _34_781 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_34_781) with
| (bs, c) -> begin
if (is_tot_or_gtot_comp c) then begin
(
# 479 "FStar.Syntax.Util.fst"
let _34_784 = (arrow_formals_comp (comp_result c))
in (match (_34_784) with
| (bs', k) -> begin
((FStar_List.append bs bs'), k)
end))
end else begin
(bs, c)
end
end))
end
| _34_786 -> begin
(let _118_213 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _118_213))
end)))

# 484 "FStar.Syntax.Util.fst"
let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.typ) = (fun k -> (
# 485 "FStar.Syntax.Util.fst"
let _34_790 = (arrow_formals_comp k)
in (match (_34_790) with
| (bs, c) -> begin
(bs, (comp_result c))
end)))

# 488 "FStar.Syntax.Util.fst"
let abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> (match (bs) with
| [] -> begin
t
end
| _34_796 -> begin
(
# 491 "FStar.Syntax.Util.fst"
let body = (let _118_222 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress _118_222))
in (match ((body.FStar_Syntax_Syntax.n, lopt)) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t, lopt'), None) -> begin
(let _118_226 = (let _118_225 = (let _118_224 = (let _118_223 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append _118_223 bs'))
in (_118_224, t, lopt))
in FStar_Syntax_Syntax.Tm_abs (_118_225))
in (FStar_Syntax_Syntax.mk _118_226 None t.FStar_Syntax_Syntax.pos))
end
| _34_806 -> begin
(
# 496 "FStar.Syntax.Util.fst"
let lopt = (match (lopt) with
| None -> begin
None
end
| Some (lc) -> begin
(let _118_227 = (FStar_Syntax_Subst.close_lcomp bs lc)
in Some (_118_227))
end)
in (let _118_230 = (let _118_229 = (let _118_228 = (FStar_Syntax_Subst.close_binders bs)
in (_118_228, body, lopt))
in FStar_Syntax_Syntax.Tm_abs (_118_229))
in (FStar_Syntax_Syntax.mk _118_230 None t.FStar_Syntax_Syntax.pos)))
end))
end))

# 501 "FStar.Syntax.Util.fst"
let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| _34_815 -> begin
(let _118_238 = (let _118_237 = (let _118_236 = (FStar_Syntax_Subst.close_binders bs)
in (let _118_235 = (FStar_Syntax_Subst.close_comp bs c)
in (_118_236, _118_235)))
in FStar_Syntax_Syntax.Tm_arrow (_118_237))
in (FStar_Syntax_Syntax.mk _118_238 None c.FStar_Syntax_Syntax.pos))
end))

# 504 "FStar.Syntax.Util.fst"
let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun b t -> (let _118_250 = (let _118_246 = (let _118_245 = (let _118_244 = (let _118_243 = (FStar_Syntax_Syntax.mk_binder b)
in (_118_243)::[])
in (FStar_Syntax_Subst.close _118_244 t))
in (b, _118_245))
in FStar_Syntax_Syntax.Tm_refine (_118_246))
in (let _118_249 = (FStar_ST.read b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (let _118_248 = (let _118_247 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges _118_247 t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk _118_250 _118_249 _118_248)))))

# 505 "FStar.Syntax.Util.fst"
let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))

# 507 "FStar.Syntax.Util.fst"
let mk_letbinding : FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def})

# 514 "FStar.Syntax.Util.fst"
let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list Prims.option  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def -> (
# 515 "FStar.Syntax.Util.fst"
let def = (match (recs) with
| None -> begin
def
end
| Some (fvs) -> begin
(
# 518 "FStar.Syntax.Util.fst"
let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _118_275 -> FStar_Syntax_Syntax.U_name (_118_275))))
in (
# 519 "FStar.Syntax.Util.fst"
let inst = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, universes))))
in (FStar_Syntax_InstFV.instantiate inst def)))
end)
in (
# 521 "FStar.Syntax.Util.fst"
let typ = (FStar_Syntax_Subst.close_univ_vars univ_vars typ)
in (
# 522 "FStar.Syntax.Util.fst"
let def = (FStar_Syntax_Subst.close_univ_vars univ_vars def)
in (mk_letbinding lbname univ_vars typ eff def)))))

# 525 "FStar.Syntax.Util.fst"
let open_univ_vars_binders_and_comp : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(
# 528 "FStar.Syntax.Util.fst"
let _34_845 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_34_845) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _34_847 -> begin
(
# 531 "FStar.Syntax.Util.fst"
let t' = (arrow binders c)
in (
# 532 "FStar.Syntax.Util.fst"
let _34_851 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_34_851) with
| (uvs, t') -> begin
(match ((let _118_283 = (FStar_Syntax_Subst.compress t')
in _118_283.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _34_857 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

# 540 "FStar.Syntax.Util.fst"
let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.starts_with fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.tuple")
end
| _34_862 -> begin
false
end))

# 544 "FStar.Syntax.Util.fst"
let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 545 "FStar.Syntax.Util.fst"
let t = (let _118_290 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "tuple%s" _118_290))
in (let _118_291 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _118_291 r))))

# 548 "FStar.Syntax.Util.fst"
let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 549 "FStar.Syntax.Util.fst"
let t = (let _118_296 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Mktuple%s" _118_296))
in (let _118_297 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _118_297 r))))

# 552 "FStar.Syntax.Util.fst"
let is_tuple_data_lid : FStar_Ident.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _118_302 = (mk_tuple_data_lid n FStar_Range.dummyRange)
in (FStar_Ident.lid_equals f _118_302)))

# 555 "FStar.Syntax.Util.fst"
let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.starts_with fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.dtuple")
end
| _34_875 -> begin
false
end))

# 559 "FStar.Syntax.Util.fst"
let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 560 "FStar.Syntax.Util.fst"
let t = (let _118_309 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "dtuple%s" _118_309))
in (let _118_310 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _118_310 r))))

# 563 "FStar.Syntax.Util.fst"
let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 564 "FStar.Syntax.Util.fst"
let t = (let _118_315 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Mkdtuple%s" _118_315))
in (let _118_316 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _118_316 r))))

# 567 "FStar.Syntax.Util.fst"
let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> (FStar_Ident.lid_equals x FStar_Syntax_Const.eq2_lid))

# 569 "FStar.Syntax.Util.fst"
let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.forall_lid))

# 570 "FStar.Syntax.Util.fst"
let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.exists_lid))

# 571 "FStar.Syntax.Util.fst"
let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))

# 572 "FStar.Syntax.Util.fst"
let is_equality = (fun x -> (is_lid_equality x.FStar_Syntax_Syntax.v))

# 574 "FStar.Syntax.Util.fst"
let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (
# 575 "FStar.Syntax.Util.fst"
let lst = (FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.not_lid)::(FStar_Syntax_Const.iff_lid)::(FStar_Syntax_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))

# 579 "FStar.Syntax.Util.fst"
let is_constructor : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _118_332 = (pre_typ t)
in _118_332.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| _34_894 -> begin
false
end))

# 584 "FStar.Syntax.Util.fst"
let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _118_337 = (pre_typ t)
in _118_337.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (_34_898) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t, _34_902) -> begin
(is_constructed_typ t lid)
end
| _34_906 -> begin
false
end))

# 589 "FStar.Syntax.Util.fst"
let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun t -> (
# 590 "FStar.Syntax.Util.fst"
let t = (pre_typ t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_app (t, _34_920) -> begin
(get_tycon t)
end
| _34_924 -> begin
None
end)))

# 598 "FStar.Syntax.Util.fst"
let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _34_930 _34_934 -> (match ((_34_930, _34_934)) with
| ((fn1, _34_929), (fn2, _34_933)) -> begin
(FStar_String.compare (FStar_Ident.text_of_lid fn1) (FStar_Ident.text_of_lid fn2))
end)))))

# 605 "FStar.Syntax.Util.fst"
let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (
# 606 "FStar.Syntax.Util.fst"
let theory_syms = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))

# 628 "FStar.Syntax.Util.fst"
let ktype : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None FStar_Range.dummyRange)

# 629 "FStar.Syntax.Util.fst"
let ktype0 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) None FStar_Range.dummyRange)

# 632 "FStar.Syntax.Util.fst"
let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun _34_937 -> (match (()) with
| () -> begin
(
# 633 "FStar.Syntax.Util.fst"
let u = (let _118_348 = (FStar_Unionfind.fresh None)
in (FStar_All.pipe_left (fun _118_347 -> FStar_Syntax_Syntax.U_unif (_118_347)) _118_348))
in (let _118_349 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None FStar_Range.dummyRange)
in (_118_349, u)))
end))

# 636 "FStar.Syntax.Util.fst"
let kt_kt : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Const.kunary ktype0 ktype0)

# 637 "FStar.Syntax.Util.fst"
let kt_kt_kt : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Const.kbin ktype0 ktype0 ktype0)

# 639 "FStar.Syntax.Util.fst"
let fvar_const : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun l -> (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant None))

# 640 "FStar.Syntax.Util.fst"
let tand : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.and_lid)

# 641 "FStar.Syntax.Util.fst"
let tor : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.or_lid)

# 642 "FStar.Syntax.Util.fst"
let timp : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.imp_lid)

# 643 "FStar.Syntax.Util.fst"
let tiff : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.iff_lid)

# 644 "FStar.Syntax.Util.fst"
let t_bool : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.bool_lid)

# 645 "FStar.Syntax.Util.fst"
let t_false : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.false_lid)

# 646 "FStar.Syntax.Util.fst"
let t_true : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.true_lid)

# 647 "FStar.Syntax.Util.fst"
let b2t_v : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.b2t_lid)

# 648 "FStar.Syntax.Util.fst"
let t_not : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.not_lid)

# 650 "FStar.Syntax.Util.fst"
let mk_conj_opt : FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _118_363 = (let _118_362 = (let _118_360 = (let _118_359 = (let _118_358 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _118_357 = (let _118_356 = (FStar_Syntax_Syntax.as_arg phi2)
in (_118_356)::[])
in (_118_358)::_118_357))
in (tand, _118_359))
in FStar_Syntax_Syntax.Tm_app (_118_360))
in (let _118_361 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _118_362 None _118_361)))
in Some (_118_363))
end))

# 653 "FStar.Syntax.Util.fst"
let mk_binop = (fun op_t phi1 phi2 -> (let _118_373 = (let _118_371 = (let _118_370 = (let _118_369 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _118_368 = (let _118_367 = (FStar_Syntax_Syntax.as_arg phi2)
in (_118_367)::[])
in (_118_369)::_118_368))
in (op_t, _118_370))
in FStar_Syntax_Syntax.Tm_app (_118_371))
in (let _118_372 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _118_373 None _118_372))))

# 654 "FStar.Syntax.Util.fst"
let mk_neg = (fun phi -> (let _118_378 = (let _118_377 = (let _118_376 = (let _118_375 = (FStar_Syntax_Syntax.as_arg phi)
in (_118_375)::[])
in (t_not, _118_376))
in FStar_Syntax_Syntax.Tm_app (_118_377))
in (FStar_Syntax_Syntax.mk _118_378 None phi.FStar_Syntax_Syntax.pos)))

# 655 "FStar.Syntax.Util.fst"
let mk_conj = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))

# 656 "FStar.Syntax.Util.fst"
let mk_conj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
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
let mk_imp : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (match ((let _118_391 = (FStar_Syntax_Subst.compress phi1)
in _118_391.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid) -> begin
t_true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
phi2
end
| _34_970 -> begin
(match ((let _118_392 = (FStar_Syntax_Subst.compress phi2)
in _118_392.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when ((FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) || (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid)) -> begin
phi2
end
| _34_974 -> begin
(mk_binop timp phi1 phi2)
end)
end))

# 673 "FStar.Syntax.Util.fst"
let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))

# 674 "FStar.Syntax.Util.fst"
let b2t = (fun e -> (let _118_399 = (let _118_398 = (let _118_397 = (let _118_396 = (FStar_Syntax_Syntax.as_arg e)
in (_118_396)::[])
in (b2t_v, _118_397))
in FStar_Syntax_Syntax.Tm_app (_118_398))
in (FStar_Syntax_Syntax.mk _118_399 None e.FStar_Syntax_Syntax.pos)))

# 676 "FStar.Syntax.Util.fst"
let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.eq2_lid)

# 678 "FStar.Syntax.Util.fst"
let mk_eq = (fun t1 t2 e1 e2 -> (let _118_410 = (let _118_408 = (let _118_407 = (let _118_406 = (FStar_Syntax_Syntax.as_arg e1)
in (let _118_405 = (let _118_404 = (FStar_Syntax_Syntax.as_arg e2)
in (_118_404)::[])
in (_118_406)::_118_405))
in (teq, _118_407))
in FStar_Syntax_Syntax.Tm_app (_118_408))
in (let _118_409 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _118_410 None _118_409))))

# 680 "FStar.Syntax.Util.fst"
let mk_has_type = (fun t x t' -> (
# 681 "FStar.Syntax.Util.fst"
let t_has_type = (fvar_const FStar_Syntax_Const.has_type_lid)
in (
# 682 "FStar.Syntax.Util.fst"
let t_has_type = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((t_has_type, (FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]))) None FStar_Range.dummyRange)
in (let _118_421 = (let _118_420 = (let _118_419 = (let _118_418 = (FStar_Syntax_Syntax.iarg t)
in (let _118_417 = (let _118_416 = (FStar_Syntax_Syntax.as_arg x)
in (let _118_415 = (let _118_414 = (FStar_Syntax_Syntax.as_arg t')
in (_118_414)::[])
in (_118_416)::_118_415))
in (_118_418)::_118_417))
in (t_has_type, _118_419))
in FStar_Syntax_Syntax.Tm_app (_118_420))
in (FStar_Syntax_Syntax.mk _118_421 None FStar_Range.dummyRange)))))

# 685 "FStar.Syntax.Util.fst"
let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.lex_t_lid)

# 686 "FStar.Syntax.Util.fst"
let lex_top : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lextop_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))

# 687 "FStar.Syntax.Util.fst"
let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lexcons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))

# 688 "FStar.Syntax.Util.fst"
let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.forall_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)

# 690 "FStar.Syntax.Util.fst"
let lcomp_of_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (
# 691 "FStar.Syntax.Util.fst"
let c = (comp_to_comp_typ c0)
in {FStar_Syntax_Syntax.eff_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.res_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.cflags = c.FStar_Syntax_Syntax.flags; FStar_Syntax_Syntax.comp = (fun _34_989 -> (match (()) with
| () -> begin
c0
end))}))

# 697 "FStar.Syntax.Util.fst"
let mk_forall : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun x body -> (let _118_438 = (let _118_437 = (let _118_436 = (let _118_435 = (let _118_434 = (let _118_433 = (let _118_429 = (FStar_Syntax_Syntax.mk_binder x)
in (_118_429)::[])
in (let _118_432 = (let _118_431 = (let _118_430 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (FStar_All.pipe_left lcomp_of_comp _118_430))
in Some (_118_431))
in (abs _118_433 body _118_432)))
in (FStar_Syntax_Syntax.as_arg _118_434))
in (_118_435)::[])
in (tforall, _118_436))
in FStar_Syntax_Syntax.Tm_app (_118_437))
in (FStar_Syntax_Syntax.mk _118_438 None FStar_Range.dummyRange)))

# 700 "FStar.Syntax.Util.fst"
let rec close_forall : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
f
end else begin
(mk_forall (Prims.fst b) f)
end) bs f))

# 703 "FStar.Syntax.Util.fst"
let rec is_wild_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (_34_998) -> begin
true
end
| _34_1001 -> begin
false
end))

# 708 "FStar.Syntax.Util.fst"
let if_then_else = (fun b t1 t2 -> (
# 709 "FStar.Syntax.Util.fst"
let then_branch = (let _118_449 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t1.FStar_Syntax_Syntax.pos)
in (_118_449, None, t1))
in (
# 710 "FStar.Syntax.Util.fst"
let else_branch = (let _118_450 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Syntax_Syntax.pos)
in (_118_450, None, t2))
in (let _118_452 = (let _118_451 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos _118_451))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((b, (then_branch)::(else_branch)::[]))) None _118_452)))))

# 716 "FStar.Syntax.Util.fst"
type qpats =
FStar_Syntax_Syntax.args Prims.list

# 717 "FStar.Syntax.Util.fst"
type connective =
| QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args)

# 718 "FStar.Syntax.Util.fst"
let is_QAll = (fun _discr_ -> (match (_discr_) with
| QAll (_) -> begin
true
end
| _ -> begin
false
end))

# 719 "FStar.Syntax.Util.fst"
let is_QEx = (fun _discr_ -> (match (_discr_) with
| QEx (_) -> begin
true
end
| _ -> begin
false
end))

# 720 "FStar.Syntax.Util.fst"
let is_BaseConn = (fun _discr_ -> (match (_discr_) with
| BaseConn (_) -> begin
true
end
| _ -> begin
false
end))

# 718 "FStar.Syntax.Util.fst"
let ___QAll____0 = (fun projectee -> (match (projectee) with
| QAll (_34_1009) -> begin
_34_1009
end))

# 719 "FStar.Syntax.Util.fst"
let ___QEx____0 = (fun projectee -> (match (projectee) with
| QEx (_34_1012) -> begin
_34_1012
end))

# 720 "FStar.Syntax.Util.fst"
let ___BaseConn____0 = (fun projectee -> (match (projectee) with
| BaseConn (_34_1015) -> begin
_34_1015
end))

# 722 "FStar.Syntax.Util.fst"
let destruct_typ_as_formula : FStar_Syntax_Syntax.term  ->  connective Prims.option = (fun f -> (
# 723 "FStar.Syntax.Util.fst"
let destruct_base_conn = (fun f -> (
# 724 "FStar.Syntax.Util.fst"
let connectives = ((FStar_Syntax_Const.true_lid, 0))::((FStar_Syntax_Const.false_lid, 0))::((FStar_Syntax_Const.and_lid, 2))::((FStar_Syntax_Const.or_lid, 2))::((FStar_Syntax_Const.imp_lid, 2))::((FStar_Syntax_Const.iff_lid, 2))::((FStar_Syntax_Const.ite_lid, 3))::((FStar_Syntax_Const.not_lid, 1))::((FStar_Syntax_Const.eq2_lid, 4))::((FStar_Syntax_Const.eq2_lid, 2))::[]
in (
# 735 "FStar.Syntax.Util.fst"
let rec aux = (fun f _34_1024 -> (match (_34_1024) with
| (lid, arity) -> begin
(
# 736 "FStar.Syntax.Util.fst"
let _34_1027 = (head_and_args f)
in (match (_34_1027) with
| (t, args) -> begin
(
# 737 "FStar.Syntax.Util.fst"
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
# 744 "FStar.Syntax.Util.fst"
let patterns = (fun t -> (
# 745 "FStar.Syntax.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(let _118_505 = (FStar_Syntax_Subst.compress t)
in (pats, _118_505))
end
| _34_1038 -> begin
(let _118_506 = (FStar_Syntax_Subst.compress t)
in ([], _118_506))
end)))
in (
# 750 "FStar.Syntax.Util.fst"
let destruct_q_conn = (fun t -> (
# 751 "FStar.Syntax.Util.fst"
let is_q = (fun fa fv -> if fa then begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end else begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)
in (
# 752 "FStar.Syntax.Util.fst"
let flat = (fun t -> (
# 753 "FStar.Syntax.Util.fst"
let _34_1048 = (head_and_args t)
in (match (_34_1048) with
| (t, args) -> begin
(let _118_518 = (un_uinst t)
in (let _118_517 = (FStar_All.pipe_right args (FStar_List.map (fun _34_1051 -> (match (_34_1051) with
| (t, imp) -> begin
(let _118_516 = (unascribe t)
in (_118_516, imp))
end))))
in (_118_518, _118_517)))
end)))
in (
# 755 "FStar.Syntax.Util.fst"
let rec aux = (fun qopt out t -> (match ((let _118_525 = (flat t)
in (qopt, _118_525))) with
| ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) | ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _::({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) | ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _::({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (Some (b), _34_1178) -> begin
(
# 767 "FStar.Syntax.Util.fst"
let bs = (FStar_List.rev out)
in (
# 768 "FStar.Syntax.Util.fst"
let _34_1183 = (FStar_Syntax_Subst.open_term bs t)
in (match (_34_1183) with
| (bs, t) -> begin
(
# 769 "FStar.Syntax.Util.fst"
let _34_1186 = (patterns t)
in (match (_34_1186) with
| (pats, body) -> begin
if b then begin
Some (QAll ((bs, pats, body)))
end else begin
Some (QEx ((bs, pats, body)))
end
end))
end)))
end
| _34_1188 -> begin
None
end))
in (aux None [] t)))))
in (
# 777 "FStar.Syntax.Util.fst"
let phi = (FStar_Syntax_Subst.compress f)
in (match ((destruct_base_conn phi)) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end))))))




