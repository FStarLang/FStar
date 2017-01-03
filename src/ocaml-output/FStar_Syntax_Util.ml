
open Prims

let qual_id : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _137_5 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _137_5 id.FStar_Ident.idRange)))


let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.mk_ident (((Prims.strcat FStar_Ident.reserved_prefix (Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText))), (lid.FStar_Ident.ident.FStar_Ident.idRange))))::[]))))


let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (

let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_Util.is_upper c)))


let arg_of_non_null_binder = (fun _39_20 -> (match (_39_20) with
| (b, imp) -> begin
(let _137_11 = (FStar_Syntax_Syntax.bv_to_name b)
in ((_137_11), (imp)))
end))


let args_of_non_null_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
[]
end else begin
(let _137_15 = (arg_of_non_null_binder b)
in (_137_15)::[])
end))))


let args_of_binders : FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun binders -> (let _137_22 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
(

let b = (let _137_19 = (FStar_Syntax_Syntax.new_bv None (Prims.fst b).FStar_Syntax_Syntax.sort)
in ((_137_19), ((Prims.snd b))))
in (let _137_20 = (arg_of_non_null_binder b)
in ((b), (_137_20))))
end else begin
(let _137_21 = (arg_of_non_null_binder b)
in ((b), (_137_21)))
end)))
in (FStar_All.pipe_right _137_22 FStar_List.unzip)))


let name_binders : FStar_Syntax_Syntax.binder Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
(

let _39_31 = b
in (match (_39_31) with
| (a, imp) -> begin
(

let b = (let _137_28 = (let _137_27 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _137_27))
in (FStar_Ident.id_of_text _137_28))
in (

let b = {FStar_Syntax_Syntax.ppname = b; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = a.FStar_Syntax_Syntax.sort}
in ((b), (imp))))
end))
end else begin
b
end))))


let name_function_binders = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _137_32 = (let _137_31 = (let _137_30 = (name_binders binders)
in ((_137_30), (comp)))
in FStar_Syntax_Syntax.Tm_arrow (_137_31))
in (FStar_Syntax_Syntax.mk _137_32 None t.FStar_Syntax_Syntax.pos))
end
| _39_40 -> begin
t
end))


let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _39_44 -> (match (_39_44) with
| (t, imp) -> begin
(let _137_37 = (let _137_36 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left Prims.fst _137_36))
in ((_137_37), (imp)))
end)))))


let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _39_48 -> (match (_39_48) with
| (t, imp) -> begin
(let _137_41 = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in ((_137_41), (imp)))
end)))))


let binders_of_freevars : FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (let _137_44 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _137_44 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))


let mk_subst = (fun s -> (s)::[])


let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> if ((FStar_List.length formals) = (FStar_List.length actuals)) then begin
(FStar_List.fold_right2 (fun f a out -> (FStar_Syntax_Syntax.NT ((((Prims.fst f)), ((Prims.fst a)))))::out) formals actuals [])
end else begin
(failwith "Ill-formed substitution")
end)


let rename_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun replace_xs with_ys -> if ((FStar_List.length replace_xs) = (FStar_List.length with_ys)) then begin
(FStar_List.map2 (fun _39_61 _39_65 -> (match (((_39_61), (_39_65))) with
| ((x, _39_60), (y, _39_64)) -> begin
(let _137_60 = (let _137_59 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (_137_59)))
in FStar_Syntax_Syntax.NT (_137_60))
end)) replace_xs with_ys)
end else begin
(failwith "Ill-formed substitution")
end)


let rec unmeta : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_meta (e, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e, _, _)) -> begin
(unmeta e)
end
| _39_80 -> begin
e
end)))


let rec univ_kernel : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.universe * Prims.int) = (fun u -> (match (u) with
| (FStar_Syntax_Syntax.U_unknown) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(

let _39_94 = (univ_kernel u)
in (match (_39_94) with
| (k, n) -> begin
((k), ((n + (Prims.parse_int "1"))))
end))
end
| FStar_Syntax_Syntax.U_max (_39_96) -> begin
(failwith "Imposible: univ_kernel (U_max _)")
end
| FStar_Syntax_Syntax.U_bvar (_39_99) -> begin
(failwith "Imposible: univ_kernel (U_bvar _)")
end))


let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (let _137_67 = (univ_kernel u)
in (Prims.snd _137_67)))


let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match (((u1), (u2))) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) -> begin
(failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_unknown, _39_121) -> begin
(~- ((Prims.parse_int "1")))
end
| (_39_124, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_zero, _39_132) -> begin
(~- ((Prims.parse_int "1")))
end
| (_39_135, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_name (u1), FStar_Syntax_Syntax.U_name (u2)) -> begin
(FStar_String.compare u1.FStar_Ident.idText u2.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (_39_144), FStar_Syntax_Syntax.U_unif (_39_147)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Syntax_Syntax.U_unif (_39_151), FStar_Syntax_Syntax.U_name (_39_154)) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_unif (u1), FStar_Syntax_Syntax.U_unif (u2)) -> begin
((FStar_Unionfind.uvar_id u1) - (FStar_Unionfind.uvar_id u2))
end
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(

let n1 = (FStar_List.length us1)
in (

let n2 = (FStar_List.length us2)
in if (n1 <> n2) then begin
(n1 - n2)
end else begin
(

let copt = (let _137_73 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map _137_73 (fun _39_171 -> (match (_39_171) with
| (u1, u2) -> begin
(

let c = (compare_univs u1 u2)
in if (c <> (Prims.parse_int "0")) then begin
Some (c)
end else begin
None
end)
end))))
in (match (copt) with
| None -> begin
(Prims.parse_int "0")
end
| Some (c) -> begin
c
end))
end))
end
| (FStar_Syntax_Syntax.U_max (_39_178), _39_181) -> begin
(~- ((Prims.parse_int "1")))
end
| (_39_184, FStar_Syntax_Syntax.U_max (_39_186)) -> begin
(Prims.parse_int "1")
end
| _39_190 -> begin
(

let _39_193 = (univ_kernel u1)
in (match (_39_193) with
| (k1, n1) -> begin
(

let _39_196 = (univ_kernel u2)
in (match (_39_196) with
| (k2, n2) -> begin
(

let r = (compare_univs k1 k2)
in if (r = (Prims.parse_int "0")) then begin
(n1 - n2)
end else begin
r
end)
end))
end))
end))


let eq_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.bool = (fun u1 u2 -> ((compare_univs u1 u2) = (Prims.parse_int "0")))


let ml_comp : FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_ML_lid r); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]}))


let comp_effect_name = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
c.FStar_Syntax_Syntax.effect_name
end
| FStar_Syntax_Syntax.Total (_39_206) -> begin
FStar_Syntax_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (_39_209) -> begin
FStar_Syntax_Const.effect_GTot_lid
end))


let comp_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_39_213) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (_39_216) -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.flags
end))


let comp_set_flags : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun c f -> (

let comp_to_comp_typ = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
c
end
| (FStar_Syntax_Syntax.Total (t, u_opt)) | (FStar_Syntax_Syntax.GTotal (t, u_opt)) -> begin
(let _137_92 = (let _137_91 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] _137_91))
in {FStar_Syntax_Syntax.comp_univs = _137_92; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)})
end))
in (

let _39_233 = c
in (let _137_94 = (let _137_93 = (

let _39_235 = (comp_to_comp_typ c)
in {FStar_Syntax_Syntax.comp_univs = _39_235.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _39_235.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _39_235.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _39_235.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})
in FStar_Syntax_Syntax.Comp (_137_93))
in {FStar_Syntax_Syntax.n = _137_94; FStar_Syntax_Syntax.tk = _39_233.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _39_233.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _39_233.FStar_Syntax_Syntax.vars}))))


let comp_to_comp_typ : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
c
end
| (FStar_Syntax_Syntax.Total (t, Some (u))) | (FStar_Syntax_Syntax.GTotal (t, Some (u))) -> begin
{FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)}
end
| _39_249 -> begin
(failwith "Assertion failed: Computation type without universe")
end))


let is_named_tot = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
(FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Tot_lid)
end
| FStar_Syntax_Syntax.Total (_39_254) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (_39_257) -> begin
false
end))


let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _39_1 -> (match (_39_1) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _39_264 -> begin
false
end)))))


let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _39_2 -> (match (_39_2) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _39_270 -> begin
false
end))))))


let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _39_3 -> (match (_39_3) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _39_276 -> begin
false
end))))))


let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _39_4 -> (match (_39_4) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _39_282 -> begin
false
end)))))


let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _39_5 -> (match (_39_5) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _39_288 -> begin
false
end)))))


let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Pure_lid)))


let is_pure_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_39_293) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (_39_296) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_6 -> (match (_39_6) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _39_303 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_Ghost_lid l)))


let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _39_7 -> (match (_39_7) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _39_310 -> begin
false
end))))))


let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))


let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _137_126 = (FStar_Syntax_Subst.compress t)
in _137_126.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_39_314, c) -> begin
(is_pure_or_ghost_comp c)
end
| _39_319 -> begin
true
end))


let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _137_129 = (FStar_Syntax_Subst.compress t)
in _137_129.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_39_322, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid)
end
| _39_329 -> begin
false
end)
end
| _39_331 -> begin
false
end))


let head_and_args : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.args) = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
((head), (args))
end
| _39_339 -> begin
((t), ([]))
end)))


let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (t, _39_344) -> begin
(FStar_Syntax_Subst.compress t)
end
| _39_348 -> begin
t
end)))


let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _137_136 = (FStar_Syntax_Subst.compress t)
in _137_136.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_39_351, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| (_req)::(_ens)::((pats, _39_361))::_39_358 -> begin
(

let pats' = (unmeta pats)
in (

let _39_372 = (head_and_args pats')
in (match (_39_372) with
| (head, _39_371) -> begin
(match ((let _137_137 = (un_uinst head)
in _137_137.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid)
end
| _39_376 -> begin
false
end)
end)))
end
| _39_378 -> begin
false
end)
end
| _39_380 -> begin
false
end)
end
| _39_382 -> begin
false
end))


let is_ml_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_8 -> (match (_39_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _39_389 -> begin
false
end)))))
end
| _39_391 -> begin
false
end))


let comp_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (t, _)) | (FStar_Syntax_Syntax.GTotal (t, _)) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let set_result_typ = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_39_407) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (_39_410) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (

let _39_414 = ct
in {FStar_Syntax_Syntax.comp_univs = _39_414.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _39_414.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = _39_414.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _39_414.FStar_Syntax_Syntax.flags}))
end))


let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _39_9 -> (match (_39_9) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _39_421 -> begin
false
end)))))


let primops : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]


let is_primop_lid : FStar_Ident.lident  ->  Prims.bool = (fun l -> (FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals l))))


let is_primop = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_primop_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| _39_427 -> begin
false
end))


let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e, _39_432, _39_434) -> begin
(unascribe e)
end
| _39_438 -> begin
e
end)))


let rec ascribe = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', _39_443, _39_445) -> begin
(ascribe t' k)
end
| _39_449 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((t), (k), (None)))) None t.FStar_Syntax_Syntax.pos)
end))


type eq_result =
| Equal
| NotEqual
| Unknown


let is_Equal = (fun _discr_ -> (match (_discr_) with
| Equal (_) -> begin
true
end
| _ -> begin
false
end))


let is_NotEqual = (fun _discr_ -> (match (_discr_) with
| NotEqual (_) -> begin
true
end
| _ -> begin
false
end))


let is_Unknown = (fun _discr_ -> (match (_discr_) with
| Unknown (_) -> begin
true
end
| _ -> begin
false
end))


let rec eq_tm : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  eq_result = (fun t1 t2 -> (

let t1 = (unascribe t1)
in (

let t2 = (unascribe t2)
in (

let equal_if = (fun _39_10 -> (match (_39_10) with
| true -> begin
Equal
end
| _39_457 -> begin
Unknown
end))
in (

let equal_iff = (fun _39_11 -> (match (_39_11) with
| true -> begin
Equal
end
| _39_462 -> begin
NotEqual
end))
in (

let eq_and = (fun f g -> (match (f) with
| NotEqual -> begin
NotEqual
end
| Equal -> begin
(g ())
end
| _39_470 -> begin
Unknown
end))
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(equal_if (FStar_Syntax_Syntax.bv_eq a b))
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(let _137_176 = (FStar_Syntax_Syntax.fv_eq f g)
in (equal_if _137_176))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst (g, vs)) -> begin
(let _137_179 = (eq_tm f g)
in (eq_and _137_179 (fun _39_490 -> (match (()) with
| () -> begin
(let _137_178 = (eq_univs_list us vs)
in (equal_if _137_178))
end))))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(equal_iff (c = d))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, _39_498), FStar_Syntax_Syntax.Tm_uvar (u2, _39_503)) -> begin
(let _137_180 = (FStar_Unionfind.equivalent u1 u2)
in (equal_if _137_180))
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
(let _137_182 = (eq_tm h1 h2)
in (eq_and _137_182 (fun _39_516 -> (match (()) with
| () -> begin
(eq_args args1 args2)
end))))
end
| (FStar_Syntax_Syntax.Tm_type (u), FStar_Syntax_Syntax.Tm_type (v)) -> begin
(let _137_183 = (eq_univs u v)
in (equal_if _137_183))
end
| (FStar_Syntax_Syntax.Tm_meta (t1, _39_524), _39_528) -> begin
(eq_tm t1 t2)
end
| (_39_531, FStar_Syntax_Syntax.Tm_meta (t2, _39_534)) -> begin
(eq_tm t1 t2)
end
| _39_539 -> begin
Unknown
end)))))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
| (((a, _39_548))::a1, ((b, _39_554))::b1) -> begin
(match ((eq_tm a b)) with
| Equal -> begin
(eq_args a1 b1)
end
| _39_560 -> begin
Unknown
end)
end
| _39_562 -> begin
NotEqual
end))
and eq_univs_list : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.universes  ->  Prims.bool = (fun us vs -> (((FStar_List.length us) = (FStar_List.length vs)) && (FStar_List.forall2 eq_univs us vs)))


let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _39_569) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _39_574, _39_576) -> begin
(unrefine t)
end
| _39_580 -> begin
t
end)))


let rec is_unit : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _137_192 = (unrefine t)
in _137_192.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_583) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid))
end
| FStar_Syntax_Syntax.Tm_uinst (t, _39_589) -> begin
(is_unit t)
end
| _39_593 -> begin
false
end))


let rec non_informative : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _137_195 = (unrefine t)
in _137_195.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_596) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.erased_lid))
end
| FStar_Syntax_Syntax.Tm_app (head, _39_602) -> begin
(non_informative head)
end
| FStar_Syntax_Syntax.Tm_uinst (t, _39_607) -> begin
(non_informative t)
end
| FStar_Syntax_Syntax.Tm_arrow (_39_611, c) -> begin
((is_tot_or_gtot_comp c) && (non_informative (comp_result c)))
end
| _39_616 -> begin
false
end))


let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (match ((let _137_198 = (FStar_Syntax_Subst.compress e)
in _137_198.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_39_619) -> begin
true
end
| _39_622 -> begin
false
end))


let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _137_201 = (FStar_Syntax_Subst.compress t)
in _137_201.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_39_625) -> begin
true
end
| _39_628 -> begin
false
end))


let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _39_633) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _39_638, _39_640) -> begin
(pre_typ t)
end
| _39_644 -> begin
t
end)))


let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.args Prims.option = (fun typ lid -> (

let typ = (FStar_Syntax_Subst.compress typ)
in (match ((let _137_208 = (un_uinst typ)
in _137_208.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
Some (args)
end
| _39_656 -> begin
None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
Some ([])
end
| _39_660 -> begin
None
end)))


let lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_let (_, _, lids, _, _)) | (FStar_Syntax_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_datacon (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_declare_typ (lid, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (n, _)) | (FStar_Syntax_Syntax.Sig_new_effect (n, _)) -> begin
(n.FStar_Syntax_Syntax.mname)::[]
end
| (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) -> begin
[]
end))


let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
Some (l)
end
| _39_768 -> begin
None
end))


let quals_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun x -> (match (x) with
| (FStar_Syntax_Syntax.Sig_bundle (_, quals, _, _)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_, _, _, _, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_, _, _, _, quals, _, _)) | (FStar_Syntax_Syntax.Sig_datacon (_, _, _, _, _, quals, _, _)) | (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_assume (_, _, quals, _)) | (FStar_Syntax_Syntax.Sig_let (_, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_new_effect ({FStar_Syntax_Syntax.qualifiers = quals; FStar_Syntax_Syntax.cattributes = _; FStar_Syntax_Syntax.mname = _; FStar_Syntax_Syntax.univs = _; FStar_Syntax_Syntax.binders = _; FStar_Syntax_Syntax.signature = _; FStar_Syntax_Syntax.ret_wp = _; FStar_Syntax_Syntax.bind_wp = _; FStar_Syntax_Syntax.if_then_else = _; FStar_Syntax_Syntax.ite_wp = _; FStar_Syntax_Syntax.stronger = _; FStar_Syntax_Syntax.close_wp = _; FStar_Syntax_Syntax.assert_p = _; FStar_Syntax_Syntax.assume_p = _; FStar_Syntax_Syntax.null_wp = _; FStar_Syntax_Syntax.trivial = _; FStar_Syntax_Syntax.repr = _; FStar_Syntax_Syntax.return_repr = _; FStar_Syntax_Syntax.bind_repr = _; FStar_Syntax_Syntax.actions = _}, _)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free ({FStar_Syntax_Syntax.qualifiers = quals; FStar_Syntax_Syntax.cattributes = _; FStar_Syntax_Syntax.mname = _; FStar_Syntax_Syntax.univs = _; FStar_Syntax_Syntax.binders = _; FStar_Syntax_Syntax.signature = _; FStar_Syntax_Syntax.ret_wp = _; FStar_Syntax_Syntax.bind_wp = _; FStar_Syntax_Syntax.if_then_else = _; FStar_Syntax_Syntax.ite_wp = _; FStar_Syntax_Syntax.stronger = _; FStar_Syntax_Syntax.close_wp = _; FStar_Syntax_Syntax.assert_p = _; FStar_Syntax_Syntax.assume_p = _; FStar_Syntax_Syntax.null_wp = _; FStar_Syntax_Syntax.trivial = _; FStar_Syntax_Syntax.repr = _; FStar_Syntax_Syntax.return_repr = _; FStar_Syntax_Syntax.bind_repr = _; FStar_Syntax_Syntax.actions = _}, _)) -> begin
quals
end
| (FStar_Syntax_Syntax.Sig_sub_effect (_, _)) | (FStar_Syntax_Syntax.Sig_pragma (_, _)) | (FStar_Syntax_Syntax.Sig_main (_, _)) -> begin
[]
end))


let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Syntax_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_datacon (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_assume (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_let (_, r, _, _, _)) | (FStar_Syntax_Syntax.Sig_main (_, r)) | (FStar_Syntax_Syntax.Sig_pragma (_, r)) | (FStar_Syntax_Syntax.Sig_new_effect (_, r)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_, r)) | (FStar_Syntax_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))


let range_of_lb = (fun _39_12 -> (match (_39_12) with
| (FStar_Util.Inl (x), _39_1065, _39_1067) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), _39_1072, _39_1074) -> begin
(FStar_Ident.range_of_lid l)
end))


let range_of_arg = (fun _39_1079 -> (match (_39_1079) with
| (hd, _39_1078) -> begin
hd.FStar_Syntax_Syntax.pos
end))


let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))


let mk_app = (fun f args -> (

let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((f), (args)))) None r)))


let mk_data = (fun l args -> (match (args) with
| [] -> begin
(let _137_229 = (let _137_228 = (let _137_227 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_137_227), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (_137_228))
in (FStar_Syntax_Syntax.mk _137_229 None (FStar_Ident.range_of_lid l)))
end
| _39_1091 -> begin
(

let e = (let _137_230 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app _137_230 args))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))) None e.FStar_Syntax_Syntax.pos))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "^fname^" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _137_236 = (let _137_235 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "7"))
in ((_137_235), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident _137_236))
end else begin
x
end)


let field_projector_prefix : Prims.string = "__proj__"


let field_projector_sep : Prims.string = "__item__"


let field_projector_contains_constructor : Prims.string  ->  Prims.bool = (fun s -> (FStar_Util.starts_with s field_projector_prefix))


let mk_field_projector_name_from_string : Prims.string  ->  Prims.string  ->  Prims.string = (fun constr field -> (Prims.strcat field_projector_prefix (Prims.strcat constr (Prims.strcat field_projector_sep field))))


let mk_field_projector_name_from_ident : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid i -> (

let j = (unmangle_field_name i)
in (

let jtext = j.FStar_Ident.idText
in (

let newi = if (field_projector_contains_constructor jtext) then begin
j
end else begin
(FStar_Ident.mk_ident (((mk_field_projector_name_from_string lid.FStar_Ident.ident.FStar_Ident.idText jtext)), (i.FStar_Ident.idRange)))
end
in (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((newi)::[])))))))


let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (

let nm = if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _137_256 = (let _137_255 = (let _137_253 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _137_253))
in (let _137_254 = (FStar_Syntax_Syntax.range_of_bv x)
in ((_137_255), (_137_254))))
in (FStar_Ident.mk_ident _137_256))
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (

let y = (

let _39_1107 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = _39_1107.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _39_1107.FStar_Syntax_Syntax.sort})
in (let _137_257 = (mk_field_projector_name_from_ident lid nm)
in ((_137_257), (y))))))


let set_uvar = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (_39_1113) -> begin
(let _137_262 = (let _137_261 = (let _137_260 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _137_260))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" _137_261))
in (failwith _137_262))
end
| _39_1116 -> begin
(FStar_Unionfind.change uv (FStar_Syntax_Syntax.Fixed (t)))
end))


let qualifier_equal : FStar_Syntax_Syntax.qualifier  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun q1 q2 -> (match (((q1), (q2))) with
| (FStar_Syntax_Syntax.Discriminator (l1), FStar_Syntax_Syntax.Discriminator (l2)) -> begin
(FStar_Ident.lid_equals l1 l2)
end
| (FStar_Syntax_Syntax.Projector (l1a, l1b), FStar_Syntax_Syntax.Projector (l2a, l2b)) -> begin
((FStar_Ident.lid_equals l1a l2a) && (l1b.FStar_Ident.idText = l2b.FStar_Ident.idText))
end
| ((FStar_Syntax_Syntax.RecordType (ns1, f1), FStar_Syntax_Syntax.RecordType (ns2, f2))) | ((FStar_Syntax_Syntax.RecordConstructor (ns1, f1), FStar_Syntax_Syntax.RecordConstructor (ns2, f2))) -> begin
(((((FStar_List.length ns1) = (FStar_List.length ns2)) && (FStar_List.forall2 (fun x1 x2 -> (x1.FStar_Ident.idText = x2.FStar_Ident.idText)) f1 f2)) && ((FStar_List.length f1) = (FStar_List.length f2))) && (FStar_List.forall2 (fun x1 x2 -> (x1.FStar_Ident.idText = x2.FStar_Ident.idText)) f1 f2))
end
| _39_1152 -> begin
(q1 = q2)
end))


let abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> if ((FStar_List.length bs) = (Prims.parse_int "0")) then begin
t
end else begin
(

let close_lopt = (fun lopt -> (match (lopt) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt
end
| Some (FStar_Util.Inl (lc)) -> begin
(let _137_280 = (let _137_279 = (FStar_Syntax_Subst.close_lcomp bs lc)
in FStar_Util.Inl (_137_279))
in Some (_137_280))
end))
in (match (bs) with
| [] -> begin
t
end
| _39_1168 -> begin
(

let body = (let _137_281 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress _137_281))
in (match (((body.FStar_Syntax_Syntax.n), (lopt))) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t, lopt'), None) -> begin
(let _137_286 = (let _137_285 = (let _137_284 = (let _137_282 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append _137_282 bs'))
in (let _137_283 = (close_lopt lopt')
in ((_137_284), (t), (_137_283))))
in FStar_Syntax_Syntax.Tm_abs (_137_285))
in (FStar_Syntax_Syntax.mk _137_286 None t.FStar_Syntax_Syntax.pos))
end
| _39_1178 -> begin
(let _137_290 = (let _137_289 = (let _137_288 = (FStar_Syntax_Subst.close_binders bs)
in (let _137_287 = (close_lopt lopt)
in ((_137_288), (body), (_137_287))))
in FStar_Syntax_Syntax.Tm_abs (_137_289))
in (FStar_Syntax_Syntax.mk _137_290 None t.FStar_Syntax_Syntax.pos))
end))
end))
end)


let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| _39_1183 -> begin
(let _137_298 = (let _137_297 = (let _137_296 = (FStar_Syntax_Subst.close_binders bs)
in (let _137_295 = (FStar_Syntax_Subst.close_comp bs c)
in ((_137_296), (_137_295))))
in FStar_Syntax_Syntax.Tm_arrow (_137_297))
in (FStar_Syntax_Syntax.mk _137_298 None c.FStar_Syntax_Syntax.pos))
end))


let flat_arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun bs c -> (

let t = (arrow bs c)
in (match ((let _137_303 = (FStar_Syntax_Subst.compress t)
in _137_303.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, _39_1193) -> begin
(match ((let _137_304 = (FStar_Syntax_Subst.compress tres)
in _137_304.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(let _137_305 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs bs')), (c')))) _137_305 t.FStar_Syntax_Syntax.pos))
end
| _39_1201 -> begin
t
end)
end
| _39_1203 -> begin
t
end)
end
| _39_1205 -> begin
t
end)))


let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun b t -> (let _137_317 = (let _137_313 = (let _137_312 = (let _137_311 = (let _137_310 = (FStar_Syntax_Syntax.mk_binder b)
in (_137_310)::[])
in (FStar_Syntax_Subst.close _137_311 t))
in ((b), (_137_312)))
in FStar_Syntax_Syntax.Tm_refine (_137_313))
in (let _137_316 = (FStar_ST.read b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (let _137_315 = (let _137_314 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges _137_314 t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk _137_317 _137_316 _137_315)))))


let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))


let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _39_1217 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_39_1217) with
| (bs, c) -> begin
if (is_tot_or_gtot_comp c) then begin
(

let _39_1220 = (arrow_formals_comp (comp_result c))
in (match (_39_1220) with
| (bs', k) -> begin
(((FStar_List.append bs bs')), (k))
end))
end else begin
((bs), (c))
end
end))
end
| _39_1222 -> begin
(let _137_322 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_137_322)))
end)))


let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.typ) = (fun k -> (

let _39_1226 = (arrow_formals_comp k)
in (match (_39_1226) with
| (bs, c) -> begin
((bs), ((comp_result c)))
end)))


let abs_formals : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option) = (fun t -> (

let rec aux = (fun t what -> (match ((let _137_332 = (let _137_331 = (FStar_Syntax_Subst.compress t)
in (FStar_All.pipe_left unascribe _137_331))
in _137_332.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, t, what) -> begin
(

let _39_1239 = (aux t what)
in (match (_39_1239) with
| (bs', t, what) -> begin
(((FStar_List.append bs bs')), (t), (what))
end))
end
| _39_1241 -> begin
(([]), (t), (what))
end))
in (

let _39_1245 = (aux t None)
in (match (_39_1245) with
| (bs, t, what) -> begin
(

let _39_1248 = (FStar_Syntax_Subst.open_term bs t)
in (match (_39_1248) with
| (bs, t) -> begin
((bs), (t), (what))
end))
end))))


let mk_letbinding : FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def})


let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list Prims.option  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def -> (

let def = (match (((recs), (univ_vars))) with
| ((None, _)) | ((_, [])) -> begin
def
end
| (Some (fvs), _39_1271) -> begin
(

let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _137_355 -> FStar_Syntax_Syntax.U_name (_137_355))))
in (

let inst = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (universes)))))
in (FStar_Syntax_InstFV.instantiate inst def)))
end)
in (

let typ = (FStar_Syntax_Subst.close_univ_vars univ_vars typ)
in (

let def = (FStar_Syntax_Subst.close_univ_vars univ_vars def)
in (mk_letbinding lbname univ_vars typ eff def)))))


let open_univ_vars_binders_and_comp : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _39_1285 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_39_1285) with
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
| _39_1287 -> begin
(

let t' = (arrow binders c)
in (

let _39_1291 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_39_1291) with
| (uvs, t') -> begin
(match ((let _137_363 = (FStar_Syntax_Subst.compress t')
in _137_363.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| _39_1297 -> begin
(failwith "Impossible")
end)
end)))
end))


let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.starts_with fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.tuple")
end
| _39_1302 -> begin
false
end))


let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _137_370 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "tuple%s" _137_370))
in (let _137_371 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _137_371 r))))


let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _137_376 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Mktuple%s" _137_376))
in (let _137_377 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _137_377 r))))


let is_tuple_data_lid : FStar_Ident.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _137_382 = (mk_tuple_data_lid n FStar_Range.dummyRange)
in (FStar_Ident.lid_equals f _137_382)))


let is_tuple_data_lid' : FStar_Ident.lident  ->  Prims.bool = (fun f -> ((f.FStar_Ident.nsstr = "Prims") && (FStar_Util.starts_with f.FStar_Ident.ident.FStar_Ident.idText "Mktuple")))


let is_tuple_constructor_lid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Util.starts_with (FStar_Ident.text_of_lid lid) "Prims.tuple"))


let is_dtuple_constructor_lid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((lid.FStar_Ident.nsstr = "Prims") && (FStar_Util.starts_with lid.FStar_Ident.ident.FStar_Ident.idText "Prims.dtuple")))


let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_dtuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| _39_1318 -> begin
false
end))


let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _137_395 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "dtuple%s" _137_395))
in (let _137_396 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _137_396 r))))


let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _137_401 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Mkdtuple%s" _137_401))
in (let _137_402 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _137_402 r))))


let is_dtuple_data_lid' : FStar_Ident.lident  ->  Prims.bool = (fun f -> (FStar_Util.starts_with (FStar_Ident.text_of_lid f) "Mkdtuple"))


let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> (FStar_Ident.lid_equals x FStar_Syntax_Const.eq2_lid))


let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.forall_lid))


let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.exists_lid))


let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))


let is_equality = (fun x -> (is_lid_equality x.FStar_Syntax_Syntax.v))


let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (

let lst = (FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.not_lid)::(FStar_Syntax_Const.iff_lid)::(FStar_Syntax_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))


let is_constructor : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _137_420 = (pre_typ t)
in _137_420.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| _39_1338 -> begin
false
end))


let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _137_425 = (pre_typ t)
in _137_425.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (_39_1342) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t, _39_1346) -> begin
(is_constructed_typ t lid)
end
| _39_1350 -> begin
false
end))


let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun t -> (

let t = (pre_typ t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_app (t, _39_1364) -> begin
(get_tycon t)
end
| _39_1368 -> begin
None
end)))


let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (

let theory_syms = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))


let ktype : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None FStar_Range.dummyRange)


let ktype0 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) None FStar_Range.dummyRange)


let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun _39_1371 -> (match (()) with
| () -> begin
(

let u = (let _137_433 = (FStar_Unionfind.fresh None)
in (FStar_All.pipe_left (fun _137_432 -> FStar_Syntax_Syntax.U_unif (_137_432)) _137_433))
in (let _137_434 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None FStar_Range.dummyRange)
in ((_137_434), (u))))
end))


let kt_kt : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Const.kunary ktype0 ktype0)


let kt_kt_kt : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Const.kbin ktype0 ktype0 ktype0)


let fvar_const : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun l -> (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant None))


let tand : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.and_lid)


let tor : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.or_lid)


let timp : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.imp_lid)


let tiff : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.iff_lid)


let t_bool : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.bool_lid)


let t_false : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.false_lid)


let t_true : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.true_lid)


let b2t_v : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.b2t_lid)


let t_not : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.not_lid)


let mk_conj_opt : FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _137_448 = (let _137_447 = (let _137_445 = (let _137_444 = (let _137_443 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _137_442 = (let _137_441 = (FStar_Syntax_Syntax.as_arg phi2)
in (_137_441)::[])
in (_137_443)::_137_442))
in ((tand), (_137_444)))
in FStar_Syntax_Syntax.Tm_app (_137_445))
in (let _137_446 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _137_447 None _137_446)))
in Some (_137_448))
end))


let mk_binop = (fun op_t phi1 phi2 -> (let _137_458 = (let _137_456 = (let _137_455 = (let _137_454 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _137_453 = (let _137_452 = (FStar_Syntax_Syntax.as_arg phi2)
in (_137_452)::[])
in (_137_454)::_137_453))
in ((op_t), (_137_455)))
in FStar_Syntax_Syntax.Tm_app (_137_456))
in (let _137_457 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _137_458 None _137_457))))


let mk_neg = (fun phi -> (let _137_463 = (let _137_462 = (let _137_461 = (let _137_460 = (FStar_Syntax_Syntax.as_arg phi)
in (_137_460)::[])
in ((t_not), (_137_461)))
in FStar_Syntax_Syntax.Tm_app (_137_462))
in (FStar_Syntax_Syntax.mk _137_463 None phi.FStar_Syntax_Syntax.pos)))


let mk_conj = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))


let mk_conj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
end
| (hd)::tl -> begin
(FStar_List.fold_right mk_conj tl hd)
end))


let mk_disj = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))


let mk_disj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
t_false
end
| (hd)::tl -> begin
(FStar_List.fold_right mk_disj tl hd)
end))


let mk_imp : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (match ((let _137_476 = (FStar_Syntax_Subst.compress phi1)
in _137_476.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid) -> begin
t_true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
phi2
end
| _39_1404 -> begin
(match ((let _137_477 = (FStar_Syntax_Subst.compress phi2)
in _137_477.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when ((FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) || (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid)) -> begin
phi2
end
| _39_1408 -> begin
(mk_binop timp phi1 phi2)
end)
end))


let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))


let b2t = (fun e -> (let _137_484 = (let _137_483 = (let _137_482 = (let _137_481 = (FStar_Syntax_Syntax.as_arg e)
in (_137_481)::[])
in ((b2t_v), (_137_482)))
in FStar_Syntax_Syntax.Tm_app (_137_483))
in (FStar_Syntax_Syntax.mk _137_484 None e.FStar_Syntax_Syntax.pos)))


let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.eq2_lid)


let mk_eq = (fun t1 t2 e1 e2 -> (let _137_495 = (let _137_493 = (let _137_492 = (let _137_491 = (FStar_Syntax_Syntax.as_arg e1)
in (let _137_490 = (let _137_489 = (FStar_Syntax_Syntax.as_arg e2)
in (_137_489)::[])
in (_137_491)::_137_490))
in ((teq), (_137_492)))
in FStar_Syntax_Syntax.Tm_app (_137_493))
in (let _137_494 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _137_495 None _137_494))))


let mk_has_type = (fun t x t' -> (

let t_has_type = (fvar_const FStar_Syntax_Const.has_type_lid)
in (

let t_has_type = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_has_type), ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))) None FStar_Range.dummyRange)
in (let _137_506 = (let _137_505 = (let _137_504 = (let _137_503 = (FStar_Syntax_Syntax.iarg t)
in (let _137_502 = (let _137_501 = (FStar_Syntax_Syntax.as_arg x)
in (let _137_500 = (let _137_499 = (FStar_Syntax_Syntax.as_arg t')
in (_137_499)::[])
in (_137_501)::_137_500))
in (_137_503)::_137_502))
in ((t_has_type), (_137_504)))
in FStar_Syntax_Syntax.Tm_app (_137_505))
in (FStar_Syntax_Syntax.mk _137_506 None FStar_Range.dummyRange)))))


let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.lex_t_lid)


let lex_top : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lextop_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))


let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lexcons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))


let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.forall_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)


let t_haseq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.haseq_lid FStar_Syntax_Syntax.Delta_constant None)


let lcomp_of_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (

let _39_1432 = (match (c0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_39_1423) -> begin
((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))
end
| FStar_Syntax_Syntax.GTotal (_39_1426) -> begin
((FStar_Syntax_Const.effect_GTot_lid), ((FStar_Syntax_Syntax.SOMETRIVIAL)::[]))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
((c.FStar_Syntax_Syntax.effect_name), (c.FStar_Syntax_Syntax.flags))
end)
in (match (_39_1432) with
| (eff_name, flags) -> begin
{FStar_Syntax_Syntax.eff_name = eff_name; FStar_Syntax_Syntax.res_typ = (comp_result c0); FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = (fun _39_1433 -> (match (()) with
| () -> begin
c0
end))}
end)))


let mk_forall : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun x body -> (let _137_526 = (let _137_525 = (let _137_524 = (let _137_523 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (let _137_522 = (let _137_521 = (let _137_520 = (let _137_519 = (let _137_514 = (FStar_Syntax_Syntax.mk_binder x)
in (_137_514)::[])
in (let _137_518 = (let _137_517 = (let _137_516 = (let _137_515 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (FStar_All.pipe_left lcomp_of_comp _137_515))
in FStar_Util.Inl (_137_516))
in Some (_137_517))
in (abs _137_519 body _137_518)))
in (FStar_Syntax_Syntax.as_arg _137_520))
in (_137_521)::[])
in (_137_523)::_137_522))
in ((tforall), (_137_524)))
in FStar_Syntax_Syntax.Tm_app (_137_525))
in (FStar_Syntax_Syntax.mk _137_526 None FStar_Range.dummyRange)))


let rec close_forall : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
f
end else begin
(mk_forall (Prims.fst b) f)
end) bs f))


let rec is_wild_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (_39_1442) -> begin
true
end
| _39_1445 -> begin
false
end))


let if_then_else = (fun b t1 t2 -> (

let then_branch = (let _137_537 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t1.FStar_Syntax_Syntax.pos)
in ((_137_537), (None), (t1)))
in (

let else_branch = (let _137_538 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Syntax_Syntax.pos)
in ((_137_538), (None), (t2)))
in (let _137_540 = (let _137_539 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos _137_539))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) None _137_540)))))


type qpats =
FStar_Syntax_Syntax.args Prims.list


type connective =
| QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args)


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
| QAll (_39_1453) -> begin
_39_1453
end))


let ___QEx____0 = (fun projectee -> (match (projectee) with
| QEx (_39_1456) -> begin
_39_1456
end))


let ___BaseConn____0 = (fun projectee -> (match (projectee) with
| BaseConn (_39_1459) -> begin
_39_1459
end))


let destruct_typ_as_formula : FStar_Syntax_Syntax.term  ->  connective Prims.option = (fun f -> (

let rec unmeta_monadic = (fun f -> (

let f = (FStar_Syntax_Subst.compress f)
in (match (f.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (_))) | (FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (_))) -> begin
(unmeta_monadic t)
end
| _39_1476 -> begin
f
end)))
in (

let destruct_base_conn = (fun f -> (

let connectives = (((FStar_Syntax_Const.true_lid), ((Prims.parse_int "0"))))::(((FStar_Syntax_Const.false_lid), ((Prims.parse_int "0"))))::(((FStar_Syntax_Const.and_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.or_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.imp_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.iff_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.ite_lid), ((Prims.parse_int "3"))))::(((FStar_Syntax_Const.not_lid), ((Prims.parse_int "1"))))::(((FStar_Syntax_Const.eq2_lid), ((Prims.parse_int "3"))))::(((FStar_Syntax_Const.eq2_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.eq3_lid), ((Prims.parse_int "4"))))::(((FStar_Syntax_Const.eq3_lid), ((Prims.parse_int "2"))))::[]
in (

let rec aux = (fun f _39_1484 -> (match (_39_1484) with
| (lid, arity) -> begin
(

let _39_1487 = (let _137_593 = (unmeta_monadic f)
in (head_and_args _137_593))
in (match (_39_1487) with
| (t, args) -> begin
(

let t = (un_uinst t)
in if ((is_constructor t lid) && ((FStar_List.length args) = arity)) then begin
Some (BaseConn (((lid), (args))))
end else begin
None
end)
end))
end))
in (FStar_Util.find_map connectives (aux f)))))
in (

let patterns = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(let _137_596 = (FStar_Syntax_Subst.compress t)
in ((pats), (_137_596)))
end
| _39_1498 -> begin
(let _137_597 = (FStar_Syntax_Subst.compress t)
in (([]), (_137_597)))
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa fv -> if fa then begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end else begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)
in (

let flat = (fun t -> (

let _39_1508 = (head_and_args t)
in (match (_39_1508) with
| (t, args) -> begin
(let _137_609 = (un_uinst t)
in (let _137_608 = (FStar_All.pipe_right args (FStar_List.map (fun _39_1511 -> (match (_39_1511) with
| (t, imp) -> begin
(let _137_607 = (unascribe t)
in ((_137_607), (imp)))
end))))
in ((_137_609), (_137_608))))
end)))
in (

let rec aux = (fun qopt out t -> (match ((let _137_616 = (flat t)
in ((qopt), (_137_616)))) with
| ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) | ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (_)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) | ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (_)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (Some (b), _39_1638) -> begin
(

let bs = (FStar_List.rev out)
in (

let _39_1643 = (FStar_Syntax_Subst.open_term bs t)
in (match (_39_1643) with
| (bs, t) -> begin
(

let _39_1646 = (patterns t)
in (match (_39_1646) with
| (pats, body) -> begin
if b then begin
Some (QAll (((bs), (pats), (body))))
end else begin
Some (QEx (((bs), (pats), (body))))
end
end))
end)))
end
| _39_1648 -> begin
None
end))
in (aux None [] t)))))
in (

let phi = (unmeta_monadic f)
in (match ((destruct_base_conn phi)) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end)))))))


let action_as_lb : FStar_Ident.lident  ->  FStar_Syntax_Syntax.action  ->  FStar_Syntax_Syntax.sigelt = (fun eff_lid a -> (

let lb = (let _137_622 = (let _137_621 = (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.Delta_equational None)
in FStar_Util.Inr (_137_621))
in (close_univs_and_mk_letbinding None _137_622 a.FStar_Syntax_Syntax.action_univs a.FStar_Syntax_Syntax.action_typ FStar_Syntax_Const.effect_Tot_lid a.FStar_Syntax_Syntax.action_defn))
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos), ((a.FStar_Syntax_Syntax.action_name)::[]), ((FStar_Syntax_Syntax.Visible_default)::(FStar_Syntax_Syntax.Action (eff_lid))::[]), ([])))))


let mk_reify = (fun t -> (

let reify_ = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) None t.FStar_Syntax_Syntax.pos)
in (let _137_627 = (let _137_626 = (let _137_625 = (let _137_624 = (FStar_Syntax_Syntax.as_arg t)
in (_137_624)::[])
in ((reify_), (_137_625)))
in FStar_Syntax_Syntax.Tm_app (_137_626))
in (FStar_Syntax_Syntax.mk _137_627 None t.FStar_Syntax_Syntax.pos))))


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_39_1661) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| (FStar_Syntax_Syntax.Tm_uinst (t, _)) | (FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}, _)) | (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) | (FStar_Syntax_Syntax.Tm_app (t, _)) | (FStar_Syntax_Syntax.Tm_abs (_, t, _)) | (FStar_Syntax_Syntax.Tm_let (_, t)) -> begin
(delta_qualifier t)
end)))


let incr_delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let d = (delta_qualifier t)
in (

let rec aux = (fun d -> (match (d) with
| FStar_Syntax_Syntax.Delta_equational -> begin
d
end
| FStar_Syntax_Syntax.Delta_constant -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))
end
| FStar_Syntax_Syntax.Delta_defined_at_level (i) -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i + (Prims.parse_int "1")))
end
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(aux d)
end))
in (aux d))))


let is_unknown : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _137_639 = (FStar_Syntax_Subst.compress t)
in _137_639.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _39_1738 -> begin
false
end))


let rec list_elements : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.list Prims.option = (fun e -> (

let _39_1742 = (let _137_642 = (unmeta e)
in (head_and_args _137_642))
in (match (_39_1742) with
| (head, args) -> begin
(match ((let _137_644 = (let _137_643 = (un_uinst head)
in _137_643.FStar_Syntax_Syntax.n)
in ((_137_644), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _39_1746) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_39_1759)::((hd, _39_1756))::((tl, _39_1752))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _137_647 = (let _137_646 = (let _137_645 = (list_elements tl)
in (FStar_Util.must _137_645))
in (hd)::_137_646)
in Some (_137_647))
end
| _39_1763 -> begin
None
end)
end)))




