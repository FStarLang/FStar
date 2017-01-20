
open Prims

<<<<<<< HEAD
let qual_id : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _0_269 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _0_269 id.FStar_Ident.idRange)))
=======
let qual_id : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid id -> (let _137_5 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::(id)::[])))
in (FStar_Ident.set_lid_range _137_5 id.FStar_Ident.idRange)))
>>>>>>> origin/master


let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.mk_ident (((Prims.strcat FStar_Ident.reserved_prefix (Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText))), (lid.FStar_Ident.ident.FStar_Ident.idRange))))::[]))))


let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (

let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_Util.is_upper c)))


<<<<<<< HEAD
let arg_of_non_null_binder = (fun uu____24 -> (match (uu____24) with
| (b, imp) -> begin
(let _0_270 = (FStar_Syntax_Syntax.bv_to_name b)
in ((_0_270), (imp)))
=======
let arg_of_non_null_binder = (fun _38_20 -> (match (_38_20) with
| (b, imp) -> begin
(let _137_11 = (FStar_Syntax_Syntax.bv_to_name b)
in ((_137_11), (imp)))
>>>>>>> origin/master
end))


let args_of_non_null_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> (

let uu____41 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____41) with
| true -> begin
[]
<<<<<<< HEAD
end
| uu____47 -> begin
(let _0_271 = (arg_of_non_null_binder b)
in (_0_271)::[])
end))))))

=======
end else begin
(let _137_15 = (arg_of_non_null_binder b)
in (_137_15)::[])
end))))
>>>>>>> origin/master

let args_of_binders : FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list) = (fun binders -> (let _0_275 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> (

<<<<<<< HEAD
let uu____94 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____94) with
| true -> begin
(

let b = (let _0_272 = (FStar_Syntax_Syntax.new_bv None (Prims.fst b).FStar_Syntax_Syntax.sort)
in ((_0_272), ((Prims.snd b))))
in (let _0_273 = (arg_of_non_null_binder b)
in ((b), (_0_273))))
end
| uu____108 -> begin
(let _0_274 = (arg_of_non_null_binder b)
in ((b), (_0_274)))
end)))))
in (FStar_All.pipe_right _0_275 FStar_List.unzip)))

=======
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
>>>>>>> origin/master

let name_binders : FStar_Syntax_Syntax.binder Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> (

let uu____131 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____131) with
| true -> begin
(

<<<<<<< HEAD
let uu____134 = b
in (match (uu____134) with
| (a, imp) -> begin
(

let b = (FStar_Ident.id_of_text (let _0_276 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _0_276)))
=======
let _38_31 = b
in (match (_38_31) with
| (a, imp) -> begin
(

let b = (let _137_28 = (let _137_27 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _137_27))
in (FStar_Ident.id_of_text _137_28))
>>>>>>> origin/master
in (

let b = {FStar_Syntax_Syntax.ppname = b; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = a.FStar_Syntax_Syntax.sort}
in ((b), (imp))))
end))
end
| uu____141 -> begin
b
end))))))


let name_function_binders = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
<<<<<<< HEAD
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((let _0_277 = (name_binders binders)
in ((_0_277), (comp)))))) None t.FStar_Syntax_Syntax.pos)
end
| uu____180 -> begin
=======
(let _137_32 = (let _137_31 = (let _137_30 = (name_binders binders)
in ((_137_30), (comp)))
in FStar_Syntax_Syntax.Tm_arrow (_137_31))
in (FStar_Syntax_Syntax.mk _137_32 None t.FStar_Syntax_Syntax.pos))
end
| _38_40 -> begin
>>>>>>> origin/master
t
end))


<<<<<<< HEAD
let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____203 -> (match (uu____203) with
| (t, imp) -> begin
(let _0_279 = (let _0_278 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left Prims.fst _0_278))
in ((_0_279), (imp)))
end)))))


let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun uu____236 -> (match (uu____236) with
| (t, imp) -> begin
(let _0_280 = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in ((_0_280), (imp)))
end)))))


let binders_of_freevars : FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (let _0_281 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _0_281 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))
=======
let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _38_44 -> (match (_38_44) with
| (t, imp) -> begin
(let _137_37 = (let _137_36 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left Prims.fst _137_36))
in ((_137_37), (imp)))
end)))))


let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _38_48 -> (match (_38_48) with
| (t, imp) -> begin
(let _137_41 = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in ((_137_41), (imp)))
end)))))


let binders_of_freevars : FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (let _137_44 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _137_44 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))
>>>>>>> origin/master


let mk_subst = (fun s -> (s)::[])


let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> (match (((FStar_List.length formals) = (FStar_List.length actuals))) with
| true -> begin
(FStar_List.fold_right2 (fun f a out -> (FStar_Syntax_Syntax.NT ((((Prims.fst f)), ((Prims.fst a)))))::out) formals actuals [])
end
| uu____302 -> begin
(failwith "Ill-formed substitution")
end))


<<<<<<< HEAD
let rename_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun replace_xs with_ys -> (match (((FStar_List.length replace_xs) = (FStar_List.length with_ys))) with
| true -> begin
(FStar_List.map2 (fun uu____321 uu____322 -> (match (((uu____321), (uu____322))) with
| ((x, uu____332), (y, uu____334)) -> begin
FStar_Syntax_Syntax.NT ((let _0_282 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (_0_282))))
=======
let rename_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun replace_xs with_ys -> if ((FStar_List.length replace_xs) = (FStar_List.length with_ys)) then begin
(FStar_List.map2 (fun _38_61 _38_65 -> (match (((_38_61), (_38_65))) with
| ((x, _38_60), (y, _38_64)) -> begin
(let _137_60 = (let _137_59 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (_137_59)))
in FStar_Syntax_Syntax.NT (_137_60))
>>>>>>> origin/master
end)) replace_xs with_ys)
end
| uu____339 -> begin
(failwith "Ill-formed substitution")
end))


let rec unmeta : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_meta (e, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e, _, _)) -> begin
(unmeta e)
end
<<<<<<< HEAD
| uu____363 -> begin
=======
| _38_80 -> begin
>>>>>>> origin/master
e
end)))


let rec univ_kernel : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.universe * Prims.int) = (fun u -> (match (u) with
| (FStar_Syntax_Syntax.U_unknown) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(

<<<<<<< HEAD
let uu____374 = (univ_kernel u)
in (match (uu____374) with
=======
let _38_94 = (univ_kernel u)
in (match (_38_94) with
>>>>>>> origin/master
| (k, n) -> begin
((k), ((n + (Prims.parse_int "1"))))
end))
end
<<<<<<< HEAD
| FStar_Syntax_Syntax.U_max (uu____381) -> begin
(failwith "Imposible: univ_kernel (U_max _)")
end
| FStar_Syntax_Syntax.U_bvar (uu____385) -> begin
=======
| FStar_Syntax_Syntax.U_max (_38_96) -> begin
(failwith "Imposible: univ_kernel (U_max _)")
end
| FStar_Syntax_Syntax.U_bvar (_38_99) -> begin
>>>>>>> origin/master
(failwith "Imposible: univ_kernel (U_bvar _)")
end))


<<<<<<< HEAD
let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (Prims.snd (univ_kernel u)))
=======
let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (let _137_67 = (univ_kernel u)
in (Prims.snd _137_67)))
>>>>>>> origin/master


let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match (((u1), (u2))) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) -> begin
(failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "0")
end
<<<<<<< HEAD
| (FStar_Syntax_Syntax.U_unknown, uu____401) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____402, FStar_Syntax_Syntax.U_unknown) -> begin
=======
| (FStar_Syntax_Syntax.U_unknown, _38_121) -> begin
(~- ((Prims.parse_int "1")))
end
| (_38_124, FStar_Syntax_Syntax.U_unknown) -> begin
>>>>>>> origin/master
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "0")
end
<<<<<<< HEAD
| (FStar_Syntax_Syntax.U_zero, uu____403) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____404, FStar_Syntax_Syntax.U_zero) -> begin
=======
| (FStar_Syntax_Syntax.U_zero, _38_132) -> begin
(~- ((Prims.parse_int "1")))
end
| (_38_135, FStar_Syntax_Syntax.U_zero) -> begin
>>>>>>> origin/master
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_name (u1), FStar_Syntax_Syntax.U_name (u2)) -> begin
(FStar_String.compare u1.FStar_Ident.idText u2.FStar_Ident.idText)
end
<<<<<<< HEAD
| (FStar_Syntax_Syntax.U_name (uu____407), FStar_Syntax_Syntax.U_unif (uu____408)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Syntax_Syntax.U_unif (uu____411), FStar_Syntax_Syntax.U_name (uu____412)) -> begin
=======
| (FStar_Syntax_Syntax.U_name (_38_144), FStar_Syntax_Syntax.U_unif (_38_147)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Syntax_Syntax.U_unif (_38_151), FStar_Syntax_Syntax.U_name (_38_154)) -> begin
>>>>>>> origin/master
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_unif (u1), FStar_Syntax_Syntax.U_unif (u2)) -> begin
(let _0_284 = (FStar_Unionfind.uvar_id u1)
in (let _0_283 = (FStar_Unionfind.uvar_id u2)
in (_0_284 - _0_283)))
end
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(

let n1 = (FStar_List.length us1)
in (

let n2 = (FStar_List.length us2)
in (match ((n1 <> n2)) with
| true -> begin
(n1 - n2)
end
| uu____440 -> begin
(

<<<<<<< HEAD
let copt = (let _0_285 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map _0_285 (fun uu____445 -> (match (uu____445) with
=======
let copt = (let _137_73 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map _137_73 (fun _38_171 -> (match (_38_171) with
>>>>>>> origin/master
| (u1, u2) -> begin
(

let c = (compare_univs u1 u2)
in (match ((c <> (Prims.parse_int "0"))) with
| true -> begin
Some (c)
end
| uu____453 -> begin
None
end))
end))))
in (match (copt) with
| None -> begin
(Prims.parse_int "0")
end
| Some (c) -> begin
c
end))
end)))
end
<<<<<<< HEAD
| (FStar_Syntax_Syntax.U_max (uu____455), uu____456) -> begin
(~- ((Prims.parse_int "1")))
end
| (uu____458, FStar_Syntax_Syntax.U_max (uu____459)) -> begin
(Prims.parse_int "1")
end
| uu____461 -> begin
(

let uu____464 = (univ_kernel u1)
in (match (uu____464) with
| (k1, n1) -> begin
(

let uu____469 = (univ_kernel u2)
in (match (uu____469) with
=======
| (FStar_Syntax_Syntax.U_max (_38_178), _38_181) -> begin
(~- ((Prims.parse_int "1")))
end
| (_38_184, FStar_Syntax_Syntax.U_max (_38_186)) -> begin
(Prims.parse_int "1")
end
| _38_190 -> begin
(

let _38_193 = (univ_kernel u1)
in (match (_38_193) with
| (k1, n1) -> begin
(

let _38_196 = (univ_kernel u2)
in (match (_38_196) with
>>>>>>> origin/master
| (k2, n2) -> begin
(

let r = (compare_univs k1 k2)
in (match ((r = (Prims.parse_int "0"))) with
| true -> begin
(n1 - n2)
end
| uu____475 -> begin
r
end))
end))
end))
end))


let eq_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.bool = (fun u1 u2 -> (let _0_286 = (compare_univs u1 u2)
in (_0_286 = (Prims.parse_int "0"))))


let ml_comp : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_ML_lid r); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]}))


let comp_effect_name = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
c.FStar_Syntax_Syntax.effect_name
end
<<<<<<< HEAD
| FStar_Syntax_Syntax.Total (uu____508) -> begin
FStar_Syntax_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (uu____514) -> begin
=======
| FStar_Syntax_Syntax.Total (_38_206) -> begin
FStar_Syntax_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (_38_209) -> begin
>>>>>>> origin/master
FStar_Syntax_Const.effect_GTot_lid
end))


let comp_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
<<<<<<< HEAD
| FStar_Syntax_Syntax.Total (uu____532) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (uu____538) -> begin
=======
| FStar_Syntax_Syntax.Total (_38_213) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (_38_216) -> begin
>>>>>>> origin/master
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
<<<<<<< HEAD
(let _0_288 = (let _0_287 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] _0_287))
in {FStar_Syntax_Syntax.comp_univs = _0_288; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)})
end))
in (

let uu___189_581 = c
in (let _0_289 = FStar_Syntax_Syntax.Comp ((

let uu___190_582 = (comp_to_comp_typ c)
in {FStar_Syntax_Syntax.comp_univs = uu___190_582.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___190_582.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___190_582.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___190_582.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f}))
in {FStar_Syntax_Syntax.n = _0_289; FStar_Syntax_Syntax.tk = uu___189_581.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___189_581.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___189_581.FStar_Syntax_Syntax.vars}))))
=======
(let _137_92 = (let _137_91 = (FStar_Util.map_opt u_opt (fun x -> (x)::[]))
in (FStar_Util.dflt [] _137_91))
in {FStar_Syntax_Syntax.comp_univs = _137_92; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)})
end))
in (

let _38_233 = c
in (let _137_94 = (let _137_93 = (

let _38_235 = (comp_to_comp_typ c)
in {FStar_Syntax_Syntax.comp_univs = _38_235.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _38_235.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _38_235.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _38_235.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})
in FStar_Syntax_Syntax.Comp (_137_93))
in {FStar_Syntax_Syntax.n = _137_94; FStar_Syntax_Syntax.tk = _38_233.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _38_233.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _38_233.FStar_Syntax_Syntax.vars}))))
>>>>>>> origin/master


let comp_to_comp_typ : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
c
end
| (FStar_Syntax_Syntax.Total (t, Some (u))) | (FStar_Syntax_Syntax.GTotal (t, Some (u))) -> begin
{FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)}
end
<<<<<<< HEAD
| uu____607 -> begin
=======
| _38_249 -> begin
>>>>>>> origin/master
(failwith "Assertion failed: Computation type without universe")
end))


let is_named_tot = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
(FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Tot_lid)
end
<<<<<<< HEAD
| FStar_Syntax_Syntax.Total (uu____620) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____626) -> begin
=======
| FStar_Syntax_Syntax.Total (_38_254) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (_38_257) -> begin
>>>>>>> origin/master
false
end))


<<<<<<< HEAD
let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___177_644 -> (match (uu___177_644) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| uu____645 -> begin
=======
let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _38_1 -> (match (_38_1) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _38_264 -> begin
>>>>>>> origin/master
false
end)))))


<<<<<<< HEAD
let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___178_650 -> (match (uu___178_650) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| uu____651 -> begin
=======
let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _38_2 -> (match (_38_2) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _38_270 -> begin
>>>>>>> origin/master
false
end))))))


<<<<<<< HEAD
let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___179_656 -> (match (uu___179_656) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| uu____657 -> begin
=======
let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _38_3 -> (match (_38_3) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _38_276 -> begin
>>>>>>> origin/master
false
end))))))


<<<<<<< HEAD
let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___180_670 -> (match (uu___180_670) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| uu____671 -> begin
=======
let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _38_4 -> (match (_38_4) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _38_282 -> begin
>>>>>>> origin/master
false
end)))))


<<<<<<< HEAD
let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___181_676 -> (match (uu___181_676) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| uu____677 -> begin
=======
let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _38_5 -> (match (_38_5) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _38_288 -> begin
>>>>>>> origin/master
false
end)))))


let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Pure_lid)))


let is_pure_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
<<<<<<< HEAD
| FStar_Syntax_Syntax.Total (uu____703) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (uu____709) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___182_717 -> (match (uu___182_717) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____718 -> begin
=======
| FStar_Syntax_Syntax.Total (_38_293) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (_38_296) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _38_6 -> (match (_38_6) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _38_303 -> begin
>>>>>>> origin/master
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_Ghost_lid l)))


let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


<<<<<<< HEAD
let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___183_737 -> (match (uu___183_737) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| uu____738 -> begin
=======
let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _38_7 -> (match (_38_7) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _38_310 -> begin
>>>>>>> origin/master
false
end))))))


let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))


<<<<<<< HEAD
let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____745 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____745) with
| FStar_Syntax_Syntax.Tm_arrow (uu____746, c) -> begin
(is_pure_or_ghost_comp c)
end
| uu____758 -> begin
=======
let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _137_126 = (FStar_Syntax_Subst.compress t)
in _137_126.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_38_314, c) -> begin
(is_pure_or_ghost_comp c)
end
| _38_319 -> begin
>>>>>>> origin/master
true
end)))


let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

<<<<<<< HEAD
let uu____762 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____762) with
| FStar_Syntax_Syntax.Tm_arrow (uu____763, c) -> begin
=======
let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _137_129 = (FStar_Syntax_Subst.compress t)
in _137_129.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_38_322, c) -> begin
>>>>>>> origin/master
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid)
end
<<<<<<< HEAD
| uu____776 -> begin
false
end)
end
| uu____777 -> begin
=======
| _38_329 -> begin
false
end)
end
| _38_331 -> begin
>>>>>>> origin/master
false
end)))


let head_and_args : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list) = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
((head), (args))
end
<<<<<<< HEAD
| uu____823 -> begin
=======
| _38_339 -> begin
>>>>>>> origin/master
((t), ([]))
end)))


let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
<<<<<<< HEAD
| FStar_Syntax_Syntax.Tm_uinst (t, uu____838) -> begin
(FStar_Syntax_Subst.compress t)
end
| uu____843 -> begin
=======
| FStar_Syntax_Syntax.Tm_uinst (t, _38_344) -> begin
(FStar_Syntax_Subst.compress t)
end
| _38_348 -> begin
>>>>>>> origin/master
t
end)))


<<<<<<< HEAD
let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____847 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____847) with
| FStar_Syntax_Syntax.Tm_arrow (uu____848, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| (_req)::(_ens)::((pats, uu____864))::uu____865 -> begin
=======
let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _137_136 = (FStar_Syntax_Subst.compress t)
in _137_136.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_38_351, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| (_req)::(_ens)::((pats, _38_361))::_38_358 -> begin
>>>>>>> origin/master
(

let pats' = (unmeta pats)
in (

<<<<<<< HEAD
let uu____896 = (head_and_args pats')
in (match (uu____896) with
| (head, uu____907) -> begin
(

let uu____922 = (un_uinst head).FStar_Syntax_Syntax.n
in (match (uu____922) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid)
end
| uu____924 -> begin
=======
let _38_372 = (head_and_args pats')
in (match (_38_372) with
| (head, _38_371) -> begin
(match ((let _137_137 = (un_uinst head)
in _137_137.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid)
end
| _38_376 -> begin
>>>>>>> origin/master
false
end))
end)))
end
<<<<<<< HEAD
| uu____925 -> begin
false
end)
end
| uu____931 -> begin
false
end)
end
| uu____932 -> begin
=======
| _38_378 -> begin
false
end)
end
| _38_380 -> begin
false
end)
end
| _38_382 -> begin
>>>>>>> origin/master
false
end)))


let is_ml_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
<<<<<<< HEAD
((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___184_946 -> (match (uu___184_946) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____947 -> begin
false
end)))))
end
| uu____948 -> begin
=======
((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _38_8 -> (match (_38_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _38_389 -> begin
false
end)))))
end
| _38_391 -> begin
>>>>>>> origin/master
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
<<<<<<< HEAD
| FStar_Syntax_Syntax.Total (uu____992) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (uu____998) -> begin
=======
| FStar_Syntax_Syntax.Total (_38_407) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (_38_410) -> begin
>>>>>>> origin/master
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (

<<<<<<< HEAD
let uu___191_1005 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___191_1005.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___191_1005.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = uu___191_1005.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___191_1005.FStar_Syntax_Syntax.flags}))
end))


let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun uu___185_1018 -> (match (uu___185_1018) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| uu____1019 -> begin
=======
let _38_414 = ct
in {FStar_Syntax_Syntax.comp_univs = _38_414.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _38_414.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = _38_414.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _38_414.FStar_Syntax_Syntax.flags}))
end))


let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _38_9 -> (match (_38_9) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _38_421 -> begin
>>>>>>> origin/master
false
end)))))


let primops : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]


let is_primop_lid : FStar_Ident.lident  ->  Prims.bool = (fun l -> (FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals l))))


let is_primop = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_primop_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
<<<<<<< HEAD
| uu____1041 -> begin
=======
| _38_427 -> begin
>>>>>>> origin/master
false
end))


let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
<<<<<<< HEAD
| FStar_Syntax_Syntax.Tm_ascribed (e, uu____1047, uu____1048) -> begin
(unascribe e)
end
| uu____1067 -> begin
=======
| FStar_Syntax_Syntax.Tm_ascribed (e, _38_432, _38_434) -> begin
(unascribe e)
end
| _38_438 -> begin
>>>>>>> origin/master
e
end)))


let rec ascribe = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
<<<<<<< HEAD
| FStar_Syntax_Syntax.Tm_ascribed (t', uu____1099, uu____1100) -> begin
(ascribe t' k)
end
| uu____1119 -> begin
=======
| FStar_Syntax_Syntax.Tm_ascribed (t', _38_443, _38_445) -> begin
(ascribe t' k)
end
| _38_449 -> begin
>>>>>>> origin/master
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((t), (k), (None)))) None t.FStar_Syntax_Syntax.pos)
end))

type eq_result =
| Equal
| NotEqual
| Unknown


let uu___is_Equal : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Equal -> begin
true
end
| uu____1136 -> begin
false
end))


let uu___is_NotEqual : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NotEqual -> begin
true
end
| uu____1140 -> begin
false
end))


let uu___is_Unknown : eq_result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unknown -> begin
true
end
| uu____1144 -> begin
false
end))


let rec eq_tm : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  eq_result = (fun t1 t2 -> (

let t1 = (unascribe t1)
in (

let t2 = (unascribe t2)
in (

<<<<<<< HEAD
let equal_if = (fun uu___186_1164 -> (match (uu___186_1164) with
| true -> begin
Equal
end
| uu____1165 -> begin
=======
let equal_if = (fun _38_10 -> (match (_38_10) with
| true -> begin
Equal
end
| _38_457 -> begin
>>>>>>> origin/master
Unknown
end))
in (

<<<<<<< HEAD
let equal_iff = (fun uu___187_1169 -> (match (uu___187_1169) with
| true -> begin
Equal
end
| uu____1170 -> begin
=======
let equal_iff = (fun _38_11 -> (match (_38_11) with
| true -> begin
Equal
end
| _38_462 -> begin
>>>>>>> origin/master
NotEqual
end))
in (

let eq_and = (fun f g -> (match (f) with
| Equal -> begin
(g ())
end
<<<<<<< HEAD
| uu____1183 -> begin
=======
| _38_469 -> begin
>>>>>>> origin/master
Unknown
end))
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(equal_if (FStar_Syntax_Syntax.bv_eq a b))
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
<<<<<<< HEAD
(equal_if (FStar_Syntax_Syntax.fv_eq f g))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst (g, vs)) -> begin
(let _0_290 = (eq_tm f g)
in (eq_and _0_290 (fun uu____1200 -> (equal_if (eq_univs_list us vs)))))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(equal_iff (FStar_Const.eq_const c d))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, uu____1204), FStar_Syntax_Syntax.Tm_uvar (u2, uu____1206)) -> begin
(equal_if (FStar_Unionfind.equivalent u1 u2))
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
(let _0_291 = (eq_tm h1 h2)
in (eq_and _0_291 (fun uu____1266 -> (eq_args args1 args2))))
end
| (FStar_Syntax_Syntax.Tm_type (u), FStar_Syntax_Syntax.Tm_type (v)) -> begin
(equal_if (eq_univs u v))
end
| (FStar_Syntax_Syntax.Tm_meta (t1, uu____1270), uu____1271) -> begin
(eq_tm t1 t2)
end
| (uu____1276, FStar_Syntax_Syntax.Tm_meta (t2, uu____1278)) -> begin
(eq_tm t1 t2)
end
| uu____1283 -> begin
=======
(let _137_176 = (FStar_Syntax_Syntax.fv_eq f g)
in (equal_if _137_176))
end
| (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst (g, vs)) -> begin
(let _137_179 = (eq_tm f g)
in (eq_and _137_179 (fun _38_489 -> (match (()) with
| () -> begin
(let _137_178 = (eq_univs_list us vs)
in (equal_if _137_178))
end))))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(let _137_180 = (FStar_Const.eq_const c d)
in (equal_iff _137_180))
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, _38_497), FStar_Syntax_Syntax.Tm_uvar (u2, _38_502)) -> begin
(let _137_181 = (FStar_Unionfind.equivalent u1 u2)
in (equal_if _137_181))
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
(let _137_183 = (eq_tm h1 h2)
in (eq_and _137_183 (fun _38_515 -> (match (()) with
| () -> begin
(eq_args args1 args2)
end))))
end
| (FStar_Syntax_Syntax.Tm_type (u), FStar_Syntax_Syntax.Tm_type (v)) -> begin
(let _137_184 = (eq_univs u v)
in (equal_if _137_184))
end
| (FStar_Syntax_Syntax.Tm_meta (t1, _38_523), _38_527) -> begin
(eq_tm t1 t2)
end
| (_38_530, FStar_Syntax_Syntax.Tm_meta (t2, _38_533)) -> begin
(eq_tm t1 t2)
end
| _38_538 -> begin
>>>>>>> origin/master
Unknown
end)))))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  eq_result = (fun a1 a2 -> (match (((a1), (a2))) with
| ([], []) -> begin
Equal
end
<<<<<<< HEAD
| (((a, uu____1307))::a1, ((b, uu____1310))::b1) -> begin
(

let uu____1348 = (eq_tm a b)
in (match (uu____1348) with
| Equal -> begin
(eq_args a1 b1)
end
| uu____1349 -> begin
=======
| (((a, _38_547))::a1, ((b, _38_553))::b1) -> begin
(match ((eq_tm a b)) with
| Equal -> begin
(eq_args a1 b1)
end
| _38_559 -> begin
>>>>>>> origin/master
Unknown
end))
end
<<<<<<< HEAD
| uu____1350 -> begin
=======
| _38_561 -> begin
>>>>>>> origin/master
Unknown
end))
and eq_univs_list : FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.universes  ->  Prims.bool = (fun us vs -> (((FStar_List.length us) = (FStar_List.length vs)) && (FStar_List.forall2 eq_univs us vs)))


let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
<<<<<<< HEAD
| FStar_Syntax_Syntax.Tm_refine (x, uu____1364) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____1370, uu____1371) -> begin
(unrefine t)
end
| uu____1390 -> begin
=======
| FStar_Syntax_Syntax.Tm_refine (x, _38_568) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _38_573, _38_575) -> begin
(unrefine t)
end
| _38_579 -> begin
>>>>>>> origin/master
t
end)))


<<<<<<< HEAD
let rec is_unit : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1394 = (unrefine t).FStar_Syntax_Syntax.n
in (match (uu____1394) with
| FStar_Syntax_Syntax.Tm_type (uu____1395) -> begin
=======
let rec is_unit : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _137_193 = (unrefine t)
in _137_193.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_38_582) -> begin
>>>>>>> origin/master
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid))
end
<<<<<<< HEAD
| FStar_Syntax_Syntax.Tm_uinst (t, uu____1398) -> begin
(is_unit t)
end
| uu____1403 -> begin
=======
| FStar_Syntax_Syntax.Tm_uinst (t, _38_588) -> begin
(is_unit t)
end
| _38_592 -> begin
>>>>>>> origin/master
false
end)))


let rec non_informative : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

<<<<<<< HEAD
let uu____1407 = (unrefine t).FStar_Syntax_Syntax.n
in (match (uu____1407) with
| FStar_Syntax_Syntax.Tm_type (uu____1408) -> begin
=======
let rec non_informative : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _137_196 = (unrefine t)
in _137_196.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_38_595) -> begin
>>>>>>> origin/master
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.erased_lid))
end
<<<<<<< HEAD
| FStar_Syntax_Syntax.Tm_app (head, uu____1411) -> begin
(non_informative head)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____1427) -> begin
(non_informative t)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1432, c) -> begin
((is_tot_or_gtot_comp c) && (non_informative (comp_result c)))
end
| uu____1444 -> begin
=======
| FStar_Syntax_Syntax.Tm_app (head, _38_601) -> begin
(non_informative head)
end
| FStar_Syntax_Syntax.Tm_uinst (t, _38_606) -> begin
(non_informative t)
end
| FStar_Syntax_Syntax.Tm_arrow (_38_610, c) -> begin
((is_tot_or_gtot_comp c) && (non_informative (comp_result c)))
end
| _38_615 -> begin
>>>>>>> origin/master
false
end)))


<<<<<<< HEAD
let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (

let uu____1448 = (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
in (match (uu____1448) with
| FStar_Syntax_Syntax.Tm_abs (uu____1449) -> begin
true
end
| uu____1464 -> begin
=======
let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (match ((let _137_199 = (FStar_Syntax_Subst.compress e)
in _137_199.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_38_618) -> begin
true
end
| _38_621 -> begin
>>>>>>> origin/master
false
end)))


<<<<<<< HEAD
let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1468 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____1468) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1469) -> begin
true
end
| uu____1477 -> begin
=======
let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _137_202 = (FStar_Syntax_Subst.compress t)
in _137_202.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_38_624) -> begin
true
end
| _38_627 -> begin
>>>>>>> origin/master
false
end)))


let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
<<<<<<< HEAD
| FStar_Syntax_Syntax.Tm_refine (x, uu____1483) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____1489, uu____1490) -> begin
(pre_typ t)
end
| uu____1509 -> begin
=======
| FStar_Syntax_Syntax.Tm_refine (x, _38_632) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _38_637, _38_639) -> begin
(pre_typ t)
end
| _38_643 -> begin
>>>>>>> origin/master
t
end)))


let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.option = (fun typ lid -> (

let typ = (FStar_Syntax_Subst.compress typ)
<<<<<<< HEAD
in (

let uu____1523 = (un_uinst typ).FStar_Syntax_Syntax.n
in (match (uu____1523) with
=======
in (match ((let _137_209 = (un_uinst typ)
in _137_209.FStar_Syntax_Syntax.n)) with
>>>>>>> origin/master
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
Some (args)
end
<<<<<<< HEAD
| uu____1559 -> begin
=======
| _38_655 -> begin
>>>>>>> origin/master
None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
Some ([])
end
<<<<<<< HEAD
| uu____1575 -> begin
=======
| _38_659 -> begin
>>>>>>> origin/master
None
end))))


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
<<<<<<< HEAD
| uu____1652 -> begin
=======
| _38_767 -> begin
>>>>>>> origin/master
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


<<<<<<< HEAD
let range_of_lb = (fun uu___188_1835 -> (match (uu___188_1835) with
| (FStar_Util.Inl (x), uu____1842, uu____1843) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), uu____1847, uu____1848) -> begin
=======
let range_of_lb = (fun _38_12 -> (match (_38_12) with
| (FStar_Util.Inl (x), _38_1064, _38_1066) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), _38_1071, _38_1073) -> begin
>>>>>>> origin/master
(FStar_Ident.range_of_lid l)
end))


<<<<<<< HEAD
let range_of_arg = (fun uu____1865 -> (match (uu____1865) with
| (hd, uu____1871) -> begin
=======
let range_of_arg = (fun _38_1078 -> (match (_38_1078) with
| (hd, _38_1077) -> begin
>>>>>>> origin/master
hd.FStar_Syntax_Syntax.pos
end))


let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))


let mk_app = (fun f args -> (

let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((f), (args)))) None r)))


let mk_data = (fun l args -> (match (args) with
| [] -> begin
<<<<<<< HEAD
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((let _0_292 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_0_292), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))) None (FStar_Ident.range_of_lid l))
end
| uu____1993 -> begin
(

let e = (let _0_293 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app _0_293 args))
=======
(let _137_230 = (let _137_229 = (let _137_228 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_137_228), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (_137_229))
in (FStar_Syntax_Syntax.mk _137_230 None (FStar_Ident.range_of_lid l)))
end
| _38_1090 -> begin
(

let e = (let _137_231 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app _137_231 args))
>>>>>>> origin/master
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))) None e.FStar_Syntax_Syntax.pos))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "^fname^" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


<<<<<<< HEAD
let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (match ((FStar_Util.starts_with x.FStar_Ident.idText "^fname^")) with
| true -> begin
(FStar_Ident.mk_ident (let _0_294 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "7"))
in ((_0_294), (x.FStar_Ident.idRange))))
end
| uu____2014 -> begin
=======
let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _137_237 = (let _137_236 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "7"))
in ((_137_236), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident _137_237))
end else begin
>>>>>>> origin/master
x
end))


let field_projector_prefix : Prims.string = "__proj__"


let field_projector_sep : Prims.string = "__item__"


let field_projector_contains_constructor : Prims.string  ->  Prims.bool = (fun s -> (FStar_Util.starts_with s field_projector_prefix))


let mk_field_projector_name_from_string : Prims.string  ->  Prims.string  ->  Prims.string = (fun constr field -> (Prims.strcat field_projector_prefix (Prims.strcat constr (Prims.strcat field_projector_sep field))))


let mk_field_projector_name_from_ident : FStar_Ident.lident  ->  FStar_Ident.ident  ->  FStar_Ident.lident = (fun lid i -> (

let j = (unmangle_field_name i)
in (

let jtext = j.FStar_Ident.idText
in (

let newi = (match ((field_projector_contains_constructor jtext)) with
| true -> begin
j
end
| uu____2033 -> begin
(FStar_Ident.mk_ident (((mk_field_projector_name_from_string lid.FStar_Ident.ident.FStar_Ident.idText jtext)), (i.FStar_Ident.idRange)))
end)
in (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns ((newi)::[])))))))


let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (

<<<<<<< HEAD
let nm = (

let uu____2046 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____2046) with
| true -> begin
(FStar_Ident.mk_ident (let _0_297 = (let _0_295 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _0_295))
in (let _0_296 = (FStar_Syntax_Syntax.range_of_bv x)
in ((_0_297), (_0_296)))))
=======
let nm = if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _137_257 = (let _137_256 = (let _137_254 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _137_254))
in (let _137_255 = (FStar_Syntax_Syntax.range_of_bv x)
in ((_137_256), (_137_255))))
in (FStar_Ident.mk_ident _137_257))
end else begin
x.FStar_Syntax_Syntax.ppname
>>>>>>> origin/master
end
| uu____2047 -> begin
x.FStar_Syntax_Syntax.ppname
end))
in (

let y = (

<<<<<<< HEAD
let uu___192_2049 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = uu___192_2049.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___192_2049.FStar_Syntax_Syntax.sort})
in (let _0_298 = (mk_field_projector_name_from_ident lid nm)
in ((_0_298), (y))))))


let set_uvar = (fun uv t -> (

let uu____2066 = (FStar_Unionfind.find uv)
in (match (uu____2066) with
| FStar_Syntax_Syntax.Fixed (uu____2069) -> begin
(failwith (let _0_300 = (let _0_299 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _0_299))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" _0_300)))
end
| uu____2071 -> begin
=======
let _38_1106 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = _38_1106.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _38_1106.FStar_Syntax_Syntax.sort})
in (let _137_258 = (mk_field_projector_name_from_ident lid nm)
in ((_137_258), (y))))))


let set_uvar = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (_38_1112) -> begin
(let _137_263 = (let _137_262 = (let _137_261 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _137_261))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" _137_262))
in (failwith _137_263))
end
| _38_1115 -> begin
>>>>>>> origin/master
(FStar_Unionfind.change uv (FStar_Syntax_Syntax.Fixed (t)))
end)))


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
<<<<<<< HEAD
| uu____2118 -> begin
=======
| _38_1151 -> begin
>>>>>>> origin/master
(q1 = q2)
end))


let abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> (match (((FStar_List.length bs) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____2152 -> begin
(

let close_lopt = (fun lopt -> (match (lopt) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt
end
| Some (FStar_Util.Inl (lc)) -> begin
<<<<<<< HEAD
Some (FStar_Util.Inl ((FStar_Syntax_Subst.close_lcomp bs lc)))
=======
(let _137_281 = (let _137_280 = (FStar_Syntax_Subst.close_lcomp bs lc)
in FStar_Util.Inl (_137_280))
in Some (_137_281))
>>>>>>> origin/master
end))
in (match (bs) with
| [] -> begin
t
end
<<<<<<< HEAD
| uu____2214 -> begin
(

let body = (FStar_Syntax_Subst.compress (FStar_Syntax_Subst.close bs t))
in (match (((body.FStar_Syntax_Syntax.n), (lopt))) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t, lopt'), None) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((let _0_303 = (let _0_301 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append _0_301 bs'))
in (let _0_302 = (close_lopt lopt')
in ((_0_303), (t), (_0_302))))))) None t.FStar_Syntax_Syntax.pos)
end
| uu____2282 -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((let _0_305 = (FStar_Syntax_Subst.close_binders bs)
in (let _0_304 = (close_lopt lopt)
in ((_0_305), (body), (_0_304))))))) None t.FStar_Syntax_Syntax.pos)
end))
=======
| _38_1167 -> begin
(

let body = (let _137_282 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress _137_282))
in (match (((body.FStar_Syntax_Syntax.n), (lopt))) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t, lopt'), None) -> begin
(let _137_287 = (let _137_286 = (let _137_285 = (let _137_283 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append _137_283 bs'))
in (let _137_284 = (close_lopt lopt')
in ((_137_285), (t), (_137_284))))
in FStar_Syntax_Syntax.Tm_abs (_137_286))
in (FStar_Syntax_Syntax.mk _137_287 None t.FStar_Syntax_Syntax.pos))
end
| _38_1177 -> begin
(let _137_291 = (let _137_290 = (let _137_289 = (FStar_Syntax_Subst.close_binders bs)
in (let _137_288 = (close_lopt lopt)
in ((_137_289), (body), (_137_288))))
in FStar_Syntax_Syntax.Tm_abs (_137_290))
in (FStar_Syntax_Syntax.mk _137_291 None t.FStar_Syntax_Syntax.pos))
>>>>>>> origin/master
end))
end))


let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
<<<<<<< HEAD
| uu____2327 -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((let _0_307 = (FStar_Syntax_Subst.close_binders bs)
in (let _0_306 = (FStar_Syntax_Subst.close_comp bs c)
in ((_0_307), (_0_306))))))) None c.FStar_Syntax_Syntax.pos)
=======
| _38_1182 -> begin
(let _137_299 = (let _137_298 = (let _137_297 = (FStar_Syntax_Subst.close_binders bs)
in (let _137_296 = (FStar_Syntax_Subst.close_comp bs c)
in ((_137_297), (_137_296))))
in FStar_Syntax_Syntax.Tm_arrow (_137_298))
in (FStar_Syntax_Syntax.mk _137_299 None c.FStar_Syntax_Syntax.pos))
>>>>>>> origin/master
end))


let flat_arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun bs c -> (

let t = (arrow bs c)
<<<<<<< HEAD
in (

let uu____2360 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____2360) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, uu____2378) -> begin
(

let uu____2385 = (FStar_Syntax_Subst.compress tres).FStar_Syntax_Syntax.n
in (match (uu____2385) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(let _0_308 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs bs')), (c'))))) _0_308 t.FStar_Syntax_Syntax.pos))
end
| uu____2418 -> begin
=======
in (match ((let _137_304 = (FStar_Syntax_Subst.compress t)
in _137_304.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, _38_1192) -> begin
(match ((let _137_305 = (FStar_Syntax_Subst.compress tres)
in _137_305.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(let _137_306 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs bs')), (c')))) _137_306 t.FStar_Syntax_Syntax.pos))
end
| _38_1200 -> begin
>>>>>>> origin/master
t
end))
end
<<<<<<< HEAD
| uu____2419 -> begin
t
end)
end
| uu____2420 -> begin
=======
| _38_1202 -> begin
t
end)
end
| _38_1204 -> begin
>>>>>>> origin/master
t
end))))


<<<<<<< HEAD
let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun b t -> (let _0_314 = (FStar_ST.read b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (let _0_313 = (let _0_312 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges _0_312 t.FStar_Syntax_Syntax.pos))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((let _0_311 = (let _0_310 = (let _0_309 = (FStar_Syntax_Syntax.mk_binder b)
in (_0_309)::[])
in (FStar_Syntax_Subst.close _0_310 t))
in ((b), (_0_311)))))) _0_314 _0_313))))
=======
let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun b t -> (let _137_318 = (let _137_314 = (let _137_313 = (let _137_312 = (let _137_311 = (FStar_Syntax_Syntax.mk_binder b)
in (_137_311)::[])
in (FStar_Syntax_Subst.close _137_312 t))
in ((b), (_137_313)))
in FStar_Syntax_Syntax.Tm_refine (_137_314))
in (let _137_317 = (FStar_ST.read b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (let _137_316 = (let _137_315 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges _137_315 t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk _137_318 _137_317 _137_316)))))
>>>>>>> origin/master


let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))


let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

<<<<<<< HEAD
let uu____2469 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____2469) with
=======
let _38_1216 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_38_1216) with
>>>>>>> origin/master
| (bs, c) -> begin
(

<<<<<<< HEAD
let uu____2479 = (is_tot_or_gtot_comp c)
in (match (uu____2479) with
| true -> begin
(

let uu____2485 = (arrow_formals_comp (comp_result c))
in (match (uu____2485) with
=======
let _38_1219 = (arrow_formals_comp (comp_result c))
in (match (_38_1219) with
>>>>>>> origin/master
| (bs', k) -> begin
(((FStar_List.append bs bs')), (k))
end))
end
| uu____2509 -> begin
((bs), (c))
end))
end))
end
<<<<<<< HEAD
| uu____2510 -> begin
(let _0_315 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_0_315)))
=======
| _38_1221 -> begin
(let _137_323 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_137_323)))
>>>>>>> origin/master
end)))


let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun k -> (

<<<<<<< HEAD
let uu____2526 = (arrow_formals_comp k)
in (match (uu____2526) with
=======
let _38_1225 = (arrow_formals_comp k)
in (match (_38_1225) with
>>>>>>> origin/master
| (bs, c) -> begin
((bs), ((comp_result c)))
end)))


let abs_formals : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option) = (fun t -> (

<<<<<<< HEAD
let rec aux = (fun t what -> (

let uu____2595 = (let _0_316 = (FStar_Syntax_Subst.compress t)
in (FStar_All.pipe_left unascribe _0_316)).FStar_Syntax_Syntax.n
in (match (uu____2595) with
| FStar_Syntax_Syntax.Tm_abs (bs, t, what) -> begin
(

let uu____2633 = (aux t what)
in (match (uu____2633) with
=======
let rec aux = (fun t what -> (match ((let _137_333 = (let _137_332 = (FStar_Syntax_Subst.compress t)
in (FStar_All.pipe_left unascribe _137_332))
in _137_333.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, t, what) -> begin
(

let _38_1238 = (aux t what)
in (match (_38_1238) with
>>>>>>> origin/master
| (bs', t, what) -> begin
(((FStar_List.append bs bs')), (t), (what))
end))
end
<<<<<<< HEAD
| uu____2690 -> begin
=======
| _38_1240 -> begin
>>>>>>> origin/master
(([]), (t), (what))
end)))
in (

<<<<<<< HEAD
let uu____2702 = (aux t None)
in (match (uu____2702) with
| (bs, t, what) -> begin
(

let uu____2750 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____2750) with
=======
let _38_1244 = (aux t None)
in (match (_38_1244) with
| (bs, t, what) -> begin
(

let _38_1247 = (FStar_Syntax_Subst.open_term bs t)
in (match (_38_1247) with
>>>>>>> origin/master
| (bs, t) -> begin
((bs), (t), (what))
end))
end))))


let mk_letbinding : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def})


let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list Prims.option  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Ident.ident Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def -> (

let def = (match (((recs), (univ_vars))) with
| ((None, _)) | ((_, [])) -> begin
def
end
<<<<<<< HEAD
| (Some (fvs), uu____2841) -> begin
(

let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _0_317 -> FStar_Syntax_Syntax.U_name (_0_317))))
=======
| (Some (fvs), _38_1270) -> begin
(

let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _137_356 -> FStar_Syntax_Syntax.U_name (_137_356))))
>>>>>>> origin/master
in (

let inst = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (universes)))))
in (FStar_Syntax_InstFV.instantiate inst def)))
end)
in (

let typ = (FStar_Syntax_Subst.close_univ_vars univ_vars typ)
in (

let def = (FStar_Syntax_Subst.close_univ_vars univ_vars def)
in (mk_letbinding lbname univ_vars typ eff def)))))


let open_univ_vars_binders_and_comp : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

<<<<<<< HEAD
let uu____2902 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____2902) with
=======
let _38_1284 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_38_1284) with
>>>>>>> origin/master
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
<<<<<<< HEAD
| uu____2918 -> begin
=======
| _38_1286 -> begin
>>>>>>> origin/master
(

let t' = (arrow binders c)
in (

<<<<<<< HEAD
let uu____2925 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____2925) with
| (uvs, t') -> begin
(

let uu____2936 = (FStar_Syntax_Subst.compress t').FStar_Syntax_Syntax.n
in (match (uu____2936) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| uu____2960 -> begin
=======
let _38_1290 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_38_1290) with
| (uvs, t') -> begin
(match ((let _137_364 = (FStar_Syntax_Subst.compress t')
in _137_364.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| _38_1296 -> begin
>>>>>>> origin/master
(failwith "Impossible")
end))
end)))
end))


let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.starts_with fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.tuple")
end
<<<<<<< HEAD
| uu____2975 -> begin
=======
| _38_1301 -> begin
>>>>>>> origin/master
false
end))


let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

<<<<<<< HEAD
let t = (let _0_318 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "tuple%s" _0_318))
in (let _0_319 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _0_319 r))))
=======
let t = (let _137_371 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "tuple%s" _137_371))
in (let _137_372 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _137_372 r))))
>>>>>>> origin/master


let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

<<<<<<< HEAD
let t = (let _0_320 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Mktuple%s" _0_320))
in (let _0_321 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _0_321 r))))


let is_tuple_data_lid : FStar_Ident.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _0_322 = (mk_tuple_data_lid n FStar_Range.dummyRange)
in (FStar_Ident.lid_equals f _0_322)))
=======
let t = (let _137_377 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Mktuple%s" _137_377))
in (let _137_378 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _137_378 r))))


let is_tuple_data_lid : FStar_Ident.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _137_383 = (mk_tuple_data_lid n FStar_Range.dummyRange)
in (FStar_Ident.lid_equals f _137_383)))
>>>>>>> origin/master


let is_tuple_data_lid' : FStar_Ident.lident  ->  Prims.bool = (fun f -> ((f.FStar_Ident.nsstr = "Prims") && (FStar_Util.starts_with f.FStar_Ident.ident.FStar_Ident.idText "Mktuple")))


let is_tuple_constructor_lid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Util.starts_with (FStar_Ident.text_of_lid lid) "Prims.tuple"))


let is_dtuple_constructor_lid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((lid.FStar_Ident.nsstr = "Prims") && (FStar_Util.starts_with lid.FStar_Ident.ident.FStar_Ident.idText "Prims.dtuple")))


let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_dtuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
<<<<<<< HEAD
| uu____3013 -> begin
=======
| _38_1317 -> begin
>>>>>>> origin/master
false
end))


let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

<<<<<<< HEAD
let t = (let _0_323 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "dtuple%s" _0_323))
in (let _0_324 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _0_324 r))))
=======
let t = (let _137_396 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "dtuple%s" _137_396))
in (let _137_397 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _137_397 r))))
>>>>>>> origin/master


let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

<<<<<<< HEAD
let t = (let _0_325 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Mkdtuple%s" _0_325))
in (let _0_326 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _0_326 r))))
=======
let t = (let _137_402 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Mkdtuple%s" _137_402))
in (let _137_403 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _137_403 r))))
>>>>>>> origin/master


let is_dtuple_data_lid' : FStar_Ident.lident  ->  Prims.bool = (fun f -> (FStar_Util.starts_with (FStar_Ident.text_of_lid f) "Mkdtuple"))


let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> (FStar_Ident.lid_equals x FStar_Syntax_Const.eq2_lid))


let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.forall_lid))


let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.exists_lid))


let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))


let is_equality = (fun x -> (is_lid_equality x.FStar_Syntax_Syntax.v))


let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (

let lst = (FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.not_lid)::(FStar_Syntax_Const.iff_lid)::(FStar_Syntax_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))


<<<<<<< HEAD
let is_constructor : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____3065 = (pre_typ t).FStar_Syntax_Syntax.n
in (match (uu____3065) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| uu____3071 -> begin
=======
let is_constructor : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _137_421 = (pre_typ t)
in _137_421.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| _38_1337 -> begin
>>>>>>> origin/master
false
end)))


<<<<<<< HEAD
let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (

let uu____3078 = (pre_typ t).FStar_Syntax_Syntax.n
in (match (uu____3078) with
| FStar_Syntax_Syntax.Tm_fvar (uu____3079) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t, uu____3081) -> begin
(is_constructed_typ t lid)
end
| uu____3096 -> begin
=======
let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _137_426 = (pre_typ t)
in _137_426.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (_38_1341) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t, _38_1345) -> begin
(is_constructed_typ t lid)
end
| _38_1349 -> begin
>>>>>>> origin/master
false
end)))


let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun t -> (

let t = (pre_typ t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
Some (t)
end
<<<<<<< HEAD
| FStar_Syntax_Syntax.Tm_app (t, uu____3107) -> begin
(get_tycon t)
end
| uu____3122 -> begin
=======
| FStar_Syntax_Syntax.Tm_app (t, _38_1363) -> begin
(get_tycon t)
end
| _38_1367 -> begin
>>>>>>> origin/master
None
end)))


let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (

let theory_syms = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))


let ktype : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown))) None FStar_Range.dummyRange)


let ktype0 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero))) None FStar_Range.dummyRange)


<<<<<<< HEAD
let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun uu____3152 -> (

let u = (let _0_328 = (FStar_Unionfind.fresh None)
in (FStar_All.pipe_left (fun _0_327 -> FStar_Syntax_Syntax.U_unif (_0_327)) _0_328))
in (let _0_329 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u))) None FStar_Range.dummyRange)
in ((_0_329), (u)))))
=======
let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun _38_1370 -> (match (()) with
| () -> begin
(

let u = (let _137_434 = (FStar_Unionfind.fresh None)
in (FStar_All.pipe_left (fun _137_433 -> FStar_Syntax_Syntax.U_unif (_137_433)) _137_434))
in (let _137_435 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None FStar_Range.dummyRange)
in ((_137_435), (u))))
end))
>>>>>>> origin/master


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
<<<<<<< HEAD
Some ((let _0_334 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_333 = (let _0_332 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _0_331 = (let _0_330 = (FStar_Syntax_Syntax.as_arg phi2)
in (_0_330)::[])
in (_0_332)::_0_331))
in ((tand), (_0_333)))))) None _0_334)))
end))


let mk_binop = (fun op_t phi1 phi2 -> (let _0_339 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_338 = (let _0_337 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _0_336 = (let _0_335 = (FStar_Syntax_Syntax.as_arg phi2)
in (_0_335)::[])
in (_0_337)::_0_336))
in ((op_t), (_0_338)))))) None _0_339)))


let mk_neg = (fun phi -> ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_341 = (let _0_340 = (FStar_Syntax_Syntax.as_arg phi)
in (_0_340)::[])
in ((t_not), (_0_341)))))) None phi.FStar_Syntax_Syntax.pos))
=======
(let _137_449 = (let _137_448 = (let _137_446 = (let _137_445 = (let _137_444 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _137_443 = (let _137_442 = (FStar_Syntax_Syntax.as_arg phi2)
in (_137_442)::[])
in (_137_444)::_137_443))
in ((tand), (_137_445)))
in FStar_Syntax_Syntax.Tm_app (_137_446))
in (let _137_447 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _137_448 None _137_447)))
in Some (_137_449))
end))


let mk_binop = (fun op_t phi1 phi2 -> (let _137_459 = (let _137_457 = (let _137_456 = (let _137_455 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _137_454 = (let _137_453 = (FStar_Syntax_Syntax.as_arg phi2)
in (_137_453)::[])
in (_137_455)::_137_454))
in ((op_t), (_137_456)))
in FStar_Syntax_Syntax.Tm_app (_137_457))
in (let _137_458 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _137_459 None _137_458))))


let mk_neg = (fun phi -> (let _137_464 = (let _137_463 = (let _137_462 = (let _137_461 = (FStar_Syntax_Syntax.as_arg phi)
in (_137_461)::[])
in ((t_not), (_137_462)))
in FStar_Syntax_Syntax.Tm_app (_137_463))
in (FStar_Syntax_Syntax.mk _137_464 None phi.FStar_Syntax_Syntax.pos)))
>>>>>>> origin/master


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


<<<<<<< HEAD
let mk_imp : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (

let uu____3308 = (FStar_Syntax_Subst.compress phi1).FStar_Syntax_Syntax.n
in (match (uu____3308) with
=======
let mk_imp : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (match ((let _137_477 = (FStar_Syntax_Subst.compress phi1)
in _137_477.FStar_Syntax_Syntax.n)) with
>>>>>>> origin/master
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid) -> begin
t_true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
phi2
end
<<<<<<< HEAD
| uu____3311 -> begin
(

let uu____3312 = (FStar_Syntax_Subst.compress phi2).FStar_Syntax_Syntax.n
in (match (uu____3312) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when ((FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) || (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid)) -> begin
phi2
end
| uu____3314 -> begin
=======
| _38_1403 -> begin
(match ((let _137_478 = (FStar_Syntax_Subst.compress phi2)
in _137_478.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when ((FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) || (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid)) -> begin
phi2
end
| _38_1407 -> begin
>>>>>>> origin/master
(mk_binop timp phi1 phi2)
end))
end)))


let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))


<<<<<<< HEAD
let b2t = (fun e -> ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_343 = (let _0_342 = (FStar_Syntax_Syntax.as_arg e)
in (_0_342)::[])
in ((b2t_v), (_0_343)))))) None e.FStar_Syntax_Syntax.pos))
=======
let b2t = (fun e -> (let _137_485 = (let _137_484 = (let _137_483 = (let _137_482 = (FStar_Syntax_Syntax.as_arg e)
in (_137_482)::[])
in ((b2t_v), (_137_483)))
in FStar_Syntax_Syntax.Tm_app (_137_484))
in (FStar_Syntax_Syntax.mk _137_485 None e.FStar_Syntax_Syntax.pos)))
>>>>>>> origin/master


let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.eq2_lid)


<<<<<<< HEAD
let mk_eq = (fun t1 t2 e1 e2 -> (let _0_348 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_347 = (let _0_346 = (FStar_Syntax_Syntax.as_arg e1)
in (let _0_345 = (let _0_344 = (FStar_Syntax_Syntax.as_arg e2)
in (_0_344)::[])
in (_0_346)::_0_345))
in ((teq), (_0_347)))))) None _0_348)))
=======
let mk_eq = (fun t1 t2 e1 e2 -> (let _137_496 = (let _137_494 = (let _137_493 = (let _137_492 = (FStar_Syntax_Syntax.as_arg e1)
in (let _137_491 = (let _137_490 = (FStar_Syntax_Syntax.as_arg e2)
in (_137_490)::[])
in (_137_492)::_137_491))
in ((teq), (_137_493)))
in FStar_Syntax_Syntax.Tm_app (_137_494))
in (let _137_495 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _137_496 None _137_495))))
>>>>>>> origin/master


let mk_has_type = (fun t x t' -> (

let t_has_type = (fvar_const FStar_Syntax_Const.has_type_lid)
in (

let t_has_type = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_has_type), ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))) None FStar_Range.dummyRange)
<<<<<<< HEAD
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_354 = (let _0_353 = (FStar_Syntax_Syntax.iarg t)
in (let _0_352 = (let _0_351 = (FStar_Syntax_Syntax.as_arg x)
in (let _0_350 = (let _0_349 = (FStar_Syntax_Syntax.as_arg t')
in (_0_349)::[])
in (_0_351)::_0_350))
in (_0_353)::_0_352))
in ((t_has_type), (_0_354)))))) None FStar_Range.dummyRange))))
=======
in (let _137_507 = (let _137_506 = (let _137_505 = (let _137_504 = (FStar_Syntax_Syntax.iarg t)
in (let _137_503 = (let _137_502 = (FStar_Syntax_Syntax.as_arg x)
in (let _137_501 = (let _137_500 = (FStar_Syntax_Syntax.as_arg t')
in (_137_500)::[])
in (_137_502)::_137_501))
in (_137_504)::_137_503))
in ((t_has_type), (_137_505)))
in FStar_Syntax_Syntax.Tm_app (_137_506))
in (FStar_Syntax_Syntax.mk _137_507 None FStar_Range.dummyRange)))))
>>>>>>> origin/master


let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.lex_t_lid)


let lex_top : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lextop_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))


let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lexcons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))


let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.forall_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)


let t_haseq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.haseq_lid FStar_Syntax_Syntax.Delta_constant None)


let lcomp_of_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (

<<<<<<< HEAD
let uu____3430 = (match (c0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____3437) -> begin
((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))
end
| FStar_Syntax_Syntax.GTotal (uu____3444) -> begin
=======
let _38_1431 = (match (c0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_38_1422) -> begin
((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))
end
| FStar_Syntax_Syntax.GTotal (_38_1425) -> begin
>>>>>>> origin/master
((FStar_Syntax_Const.effect_GTot_lid), ((FStar_Syntax_Syntax.SOMETRIVIAL)::[]))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
((c.FStar_Syntax_Syntax.effect_name), (c.FStar_Syntax_Syntax.flags))
end)
<<<<<<< HEAD
in (match (uu____3430) with
| (eff_name, flags) -> begin
{FStar_Syntax_Syntax.eff_name = eff_name; FStar_Syntax_Syntax.res_typ = (comp_result c0); FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = (fun uu____3457 -> c0)}
end)))


let mk_forall : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun x body -> ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_362 = (let _0_361 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (let _0_360 = (let _0_359 = (FStar_Syntax_Syntax.as_arg (let _0_358 = (let _0_355 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_355)::[])
in (let _0_357 = Some (FStar_Util.Inl ((let _0_356 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (FStar_All.pipe_left lcomp_of_comp _0_356))))
in (abs _0_358 body _0_357))))
in (_0_359)::[])
in (_0_361)::_0_360))
in ((tforall), (_0_362)))))) None FStar_Range.dummyRange))
=======
in (match (_38_1431) with
| (eff_name, flags) -> begin
{FStar_Syntax_Syntax.eff_name = eff_name; FStar_Syntax_Syntax.res_typ = (comp_result c0); FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = (fun _38_1432 -> (match (()) with
| () -> begin
c0
end))}
end)))


let mk_forall : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun x body -> (let _137_527 = (let _137_526 = (let _137_525 = (let _137_524 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (let _137_523 = (let _137_522 = (let _137_521 = (let _137_520 = (let _137_515 = (FStar_Syntax_Syntax.mk_binder x)
in (_137_515)::[])
in (let _137_519 = (let _137_518 = (let _137_517 = (let _137_516 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (FStar_All.pipe_left lcomp_of_comp _137_516))
in FStar_Util.Inl (_137_517))
in Some (_137_518))
in (abs _137_520 body _137_519)))
in (FStar_Syntax_Syntax.as_arg _137_521))
in (_137_522)::[])
in (_137_524)::_137_523))
in ((tforall), (_137_525)))
in FStar_Syntax_Syntax.Tm_app (_137_526))
in (FStar_Syntax_Syntax.mk _137_527 None FStar_Range.dummyRange)))
>>>>>>> origin/master


let rec close_forall : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f -> (

let uu____3495 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____3495) with
| true -> begin
f
end
| uu____3496 -> begin
(mk_forall (Prims.fst b) f)
end))) bs f))


let rec is_wild_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
<<<<<<< HEAD
| FStar_Syntax_Syntax.Pat_wild (uu____3508) -> begin
true
end
| uu____3509 -> begin
=======
| FStar_Syntax_Syntax.Pat_wild (_38_1441) -> begin
true
end
| _38_1444 -> begin
>>>>>>> origin/master
false
end))


let if_then_else = (fun b t1 t2 -> (

<<<<<<< HEAD
let then_branch = (let _0_363 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t1.FStar_Syntax_Syntax.pos)
in ((_0_363), (None), (t1)))
in (

let else_branch = (let _0_364 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Syntax_Syntax.pos)
in ((_0_364), (None), (t2)))
in (let _0_366 = (let _0_365 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos _0_365))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) None _0_366)))))
=======
let then_branch = (let _137_538 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t1.FStar_Syntax_Syntax.pos)
in ((_137_538), (None), (t1)))
in (

let else_branch = (let _137_539 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Syntax_Syntax.pos)
in ((_137_539), (None), (t2)))
in (let _137_541 = (let _137_540 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos _137_540))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) None _137_541)))))
>>>>>>> origin/master


type qpats =
FStar_Syntax_Syntax.args Prims.list

type connective =
| QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args)


let uu___is_QAll : connective  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QAll (_0) -> begin
true
end
| uu____3653 -> begin
false
end))


let __proj__QAll__item___0 : connective  ->  (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) = (fun projectee -> (match (projectee) with
| QAll (_0) -> begin
_0
end))


let uu___is_QEx : connective  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QEx (_0) -> begin
true
end
| uu____3677 -> begin
false
end))


<<<<<<< HEAD
let __proj__QEx__item___0 : connective  ->  (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) = (fun projectee -> (match (projectee) with
| QEx (_0) -> begin
_0
end))


let uu___is_BaseConn : connective  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BaseConn (_0) -> begin
true
end
| uu____3700 -> begin
false
end))


let __proj__BaseConn__item___0 : connective  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.args) = (fun projectee -> (match (projectee) with
| BaseConn (_0) -> begin
_0
=======
let ___QAll____0 = (fun projectee -> (match (projectee) with
| QAll (_38_1452) -> begin
_38_1452
end))


let ___QEx____0 = (fun projectee -> (match (projectee) with
| QEx (_38_1455) -> begin
_38_1455
end))


let ___BaseConn____0 = (fun projectee -> (match (projectee) with
| BaseConn (_38_1458) -> begin
_38_1458
>>>>>>> origin/master
end))


let destruct_typ_as_formula : FStar_Syntax_Syntax.term  ->  connective Prims.option = (fun f -> (

let rec unmeta_monadic = (fun f -> (

let f = (FStar_Syntax_Subst.compress f)
in (match (f.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (_))) | (FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (_))) -> begin
(unmeta_monadic t)
end
<<<<<<< HEAD
| uu____3735 -> begin
=======
| _38_1475 -> begin
>>>>>>> origin/master
f
end)))
in (

let destruct_base_conn = (fun f -> (

let connectives = (((FStar_Syntax_Const.true_lid), ((Prims.parse_int "0"))))::(((FStar_Syntax_Const.false_lid), ((Prims.parse_int "0"))))::(((FStar_Syntax_Const.and_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.or_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.imp_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.iff_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.ite_lid), ((Prims.parse_int "3"))))::(((FStar_Syntax_Const.not_lid), ((Prims.parse_int "1"))))::(((FStar_Syntax_Const.eq2_lid), ((Prims.parse_int "3"))))::(((FStar_Syntax_Const.eq2_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.eq3_lid), ((Prims.parse_int "4"))))::(((FStar_Syntax_Const.eq3_lid), ((Prims.parse_int "2"))))::[]
in (

<<<<<<< HEAD
let rec aux = (fun f uu____3780 -> (match (uu____3780) with
| (lid, arity) -> begin
(

let uu____3786 = (head_and_args (unmeta_monadic f))
in (match (uu____3786) with
=======
let rec aux = (fun f _38_1483 -> (match (_38_1483) with
| (lid, arity) -> begin
(

let _38_1486 = (let _137_594 = (unmeta_monadic f)
in (head_and_args _137_594))
in (match (_38_1486) with
>>>>>>> origin/master
| (t, args) -> begin
(

let t = (un_uinst t)
in (

let uu____3814 = ((is_constructor t lid) && ((FStar_List.length args) = arity))
in (match (uu____3814) with
| true -> begin
Some (BaseConn (((lid), (args))))
end
| uu____3829 -> begin
None
end)))
end))
end))
in (FStar_Util.find_map connectives (aux f)))))
in (

let patterns = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
<<<<<<< HEAD
(let _0_367 = (FStar_Syntax_Subst.compress t)
in ((pats), (_0_367)))
end
| uu____3871 -> begin
(let _0_368 = (FStar_Syntax_Subst.compress t)
in (([]), (_0_368)))
=======
(let _137_597 = (FStar_Syntax_Subst.compress t)
in ((pats), (_137_597)))
end
| _38_1497 -> begin
(let _137_598 = (FStar_Syntax_Subst.compress t)
in (([]), (_137_598)))
>>>>>>> origin/master
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa fv -> (match (fa) with
| true -> begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| uu____3899 -> begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in (

let flat = (fun t -> (

<<<<<<< HEAD
let uu____3913 = (head_and_args t)
in (match (uu____3913) with
| (t, args) -> begin
(let _0_371 = (un_uinst t)
in (let _0_370 = (FStar_All.pipe_right args (FStar_List.map (fun uu____3959 -> (match (uu____3959) with
| (t, imp) -> begin
(let _0_369 = (unascribe t)
in ((_0_369), (imp)))
end))))
in ((_0_371), (_0_370))))
end)))
in (

let rec aux = (fun qopt out t -> (

let uu____3985 = (let _0_372 = (flat t)
in ((qopt), (_0_372)))
in (match (uu____3985) with
=======
let _38_1507 = (head_and_args t)
in (match (_38_1507) with
| (t, args) -> begin
(let _137_610 = (un_uinst t)
in (let _137_609 = (FStar_All.pipe_right args (FStar_List.map (fun _38_1510 -> (match (_38_1510) with
| (t, imp) -> begin
(let _137_608 = (unascribe t)
in ((_137_608), (imp)))
end))))
in ((_137_610), (_137_609))))
end)))
in (

let rec aux = (fun qopt out t -> (match ((let _137_617 = (flat t)
in ((qopt), (_137_617)))) with
>>>>>>> origin/master
| ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) | ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (_)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) | ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (_)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
<<<<<<< HEAD
| (Some (b), uu____4247) -> begin
=======
| (Some (b), _38_1637) -> begin
>>>>>>> origin/master
(

let bs = (FStar_List.rev out)
in (

<<<<<<< HEAD
let uu____4265 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____4265) with
| (bs, t) -> begin
(

let uu____4271 = (patterns t)
in (match (uu____4271) with
=======
let _38_1642 = (FStar_Syntax_Subst.open_term bs t)
in (match (_38_1642) with
| (bs, t) -> begin
(

let _38_1645 = (patterns t)
in (match (_38_1645) with
>>>>>>> origin/master
| (pats, body) -> begin
(match (b) with
| true -> begin
Some (QAll (((bs), (pats), (body))))
end
| uu____4302 -> begin
Some (QEx (((bs), (pats), (body))))
end)
end))
end)))
end
<<<<<<< HEAD
| uu____4309 -> begin
=======
| _38_1647 -> begin
>>>>>>> origin/master
None
end)))
in (aux None [] t)))))
in (

let phi = (unmeta_monadic f)
in (

let uu____4321 = (destruct_base_conn phi)
in (match (uu____4321) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end))))))))


let action_as_lb : FStar_Ident.lident  ->  FStar_Syntax_Syntax.action  ->  FStar_Syntax_Syntax.sigelt = (fun eff_lid a -> (

<<<<<<< HEAD
let lb = (let _0_373 = FStar_Util.Inr ((FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.Delta_equational None))
in (close_univs_and_mk_letbinding None _0_373 a.FStar_Syntax_Syntax.action_univs a.FStar_Syntax_Syntax.action_typ FStar_Syntax_Const.effect_Tot_lid a.FStar_Syntax_Syntax.action_defn))
=======
let lb = (let _137_623 = (let _137_622 = (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.Delta_equational None)
in FStar_Util.Inr (_137_622))
in (close_univs_and_mk_letbinding None _137_623 a.FStar_Syntax_Syntax.action_univs a.FStar_Syntax_Syntax.action_typ FStar_Syntax_Const.effect_Tot_lid a.FStar_Syntax_Syntax.action_defn))
>>>>>>> origin/master
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos), ((a.FStar_Syntax_Syntax.action_name)::[]), ((FStar_Syntax_Syntax.Visible_default)::(FStar_Syntax_Syntax.Action (eff_lid))::[]), ([])))))


let mk_reify = (fun t -> (

let reify_ = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) None t.FStar_Syntax_Syntax.pos)
<<<<<<< HEAD
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_375 = (let _0_374 = (FStar_Syntax_Syntax.as_arg t)
in (_0_374)::[])
in ((reify_), (_0_375)))))) None t.FStar_Syntax_Syntax.pos)))
=======
in (let _137_628 = (let _137_627 = (let _137_626 = (let _137_625 = (FStar_Syntax_Syntax.as_arg t)
in (_137_625)::[])
in ((reify_), (_137_626)))
in FStar_Syntax_Syntax.Tm_app (_137_627))
in (FStar_Syntax_Syntax.mk _137_628 None t.FStar_Syntax_Syntax.pos))))
>>>>>>> origin/master


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
<<<<<<< HEAD
| FStar_Syntax_Syntax.Tm_delayed (uu____4375) -> begin
=======
| FStar_Syntax_Syntax.Tm_delayed (_38_1660) -> begin
>>>>>>> origin/master
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


<<<<<<< HEAD
let is_unknown : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____4481 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____4481) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____4482 -> begin
=======
let is_unknown : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _137_640 = (FStar_Syntax_Subst.compress t)
in _137_640.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _38_1737 -> begin
>>>>>>> origin/master
false
end)))


let rec list_elements : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.list Prims.option = (fun e -> (

<<<<<<< HEAD
let uu____4490 = (head_and_args (unmeta e))
in (match (uu____4490) with
| (head, args) -> begin
(

let uu____4518 = (let _0_376 = (un_uinst head).FStar_Syntax_Syntax.n
in ((_0_376), (args)))
in (match (uu____4518) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____4534) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4547)::((hd, uu____4549))::((tl, uu____4551))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
Some ((let _0_377 = (FStar_Util.must (list_elements tl))
in (hd)::_0_377))
end
| uu____4591 -> begin
=======
let _38_1741 = (let _137_643 = (unmeta e)
in (head_and_args _137_643))
in (match (_38_1741) with
| (head, args) -> begin
(match ((let _137_645 = (let _137_644 = (un_uinst head)
in _137_644.FStar_Syntax_Syntax.n)
in ((_137_645), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _38_1745) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_38_1758)::((hd, _38_1755))::((tl, _38_1751))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _137_648 = (let _137_647 = (let _137_646 = (list_elements tl)
in (FStar_Util.must _137_646))
in (hd)::_137_647)
in Some (_137_648))
end
| _38_1762 -> begin
>>>>>>> origin/master
None
end))
end)))




