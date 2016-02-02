
open Prims
let handle_err = (fun warning ret e -> (match (e) with
| FStar_Syntax_Syntax.Error (msg, r) -> begin
(let _41_19 = (let _118_8 = (let _118_7 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s : %s\n%s\n" _118_7 (if warning then begin
"Warning"
end else begin
"Error"
end) msg))
in (FStar_Util.print_string _118_8))
in ())
end
| FStar_Util.NYI (s) -> begin
(let _41_23 = (let _118_9 = (FStar_Util.format1 "Feature not yet implemented: %s" s)
in (FStar_Util.print_string _118_9))
in ())
end
| FStar_Syntax_Syntax.Err (s) -> begin
(let _118_10 = (FStar_Util.format1 "Error: %s" s)
in (FStar_Util.print_string _118_10))
end
| _41_28 -> begin
(Prims.raise e)
end))

let handleable = (fun _41_1 -> (match (_41_1) with
| (FStar_Syntax_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Syntax_Syntax.Err (_)) -> begin
true
end
| _41_40 -> begin
false
end))

let mk_discriminator = (fun lid -> (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.mk_ident ((Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText), lid.FStar_Ident.ident.FStar_Ident.idRange)))::[]))))

let is_name = (fun lid -> (let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText 0)
in (FStar_Util.is_upper c)))

let arg_of_non_null_binder = (fun _41_46 -> (match (_41_46) with
| (b, imp) -> begin
(let _118_18 = (FStar_Syntax_Syntax.bv_to_name b)
in (_118_18, imp))
end))

let args_of_non_null_binders = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
[]
end else begin
(let _118_22 = (arg_of_non_null_binder b)
in (_118_22)::[])
end))))

let args_of_binders = (fun binders -> (let _118_29 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
(let b = (let _118_26 = (FStar_Syntax_Syntax.new_bv None (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_118_26, (Prims.snd b)))
in (let _118_27 = (arg_of_non_null_binder b)
in (b, _118_27)))
end else begin
(let _118_28 = (arg_of_non_null_binder b)
in (b, _118_28))
end)))
in (FStar_All.pipe_right _118_29 FStar_List.unzip)))

let name_binders = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
(let _41_57 = b
in (match (_41_57) with
| (a, imp) -> begin
(let b = (let _118_35 = (let _118_34 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _118_34))
in (FStar_Ident.id_of_text _118_35))
in (let b = {FStar_Syntax_Syntax.ppname = b; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = a.FStar_Syntax_Syntax.sort}
in (b, imp)))
end))
end else begin
b
end))))

let name_function_binders = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _118_39 = (let _118_38 = (let _118_37 = (name_binders binders)
in (_118_37, comp))
in FStar_Syntax_Syntax.Tm_arrow (_118_38))
in (FStar_Syntax_Syntax.mk _118_39 None t.FStar_Syntax_Syntax.pos))
end
| _41_66 -> begin
t
end))

let null_binders_of_tks = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _41_70 -> (match (_41_70) with
| (t, imp) -> begin
(let _118_44 = (let _118_43 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left Prims.fst _118_43))
in (_118_44, imp))
end)))))

let binders_of_tks = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _41_74 -> (match (_41_74) with
| (t, imp) -> begin
(let _118_48 = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (_118_48, imp))
end)))))

let binders_of_freevars = (fun fvs -> (let _118_57 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _118_57 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))

let mk_subst = (fun s -> (s)::[])

let subst_formal = (fun f a -> FStar_Syntax_Syntax.DB ((0, (Prims.fst a))))

let subst_of_list = (fun formals actuals -> if ((FStar_List.length formals) = (FStar_List.length actuals)) then begin
(let _118_70 = (FStar_List.fold_right2 (fun f a _41_85 -> (match (_41_85) with
| (n, out) -> begin
((n + 1), (FStar_Syntax_Syntax.DB ((n, (Prims.fst a))))::out)
end)) formals actuals (0, []))
in (FStar_All.pipe_right _118_70 Prims.snd))
end else begin
(FStar_All.failwith "Ill-formed substitution")
end)

let rec unmeta = (fun e -> (let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_meta (e, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e, _, _)) -> begin
(unmeta e)
end
| _41_100 -> begin
e
end)))

let rec univ_kernel = (fun u -> (match (u) with
| (FStar_Syntax_Syntax.U_unknown) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
(u, 0)
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _41_114 = (univ_kernel u)
in (match (_41_114) with
| (k, n) -> begin
(k, (n + 1))
end))
end
| (FStar_Syntax_Syntax.U_max (_)) | (FStar_Syntax_Syntax.U_bvar (_)) -> begin
(FStar_All.failwith "Imposible")
end))

let constant_univ_as_nat = (fun u -> (let _118_77 = (univ_kernel u)
in (Prims.snd _118_77)))

let rec compare_univs = (fun u1 u2 -> (match ((u1, u2)) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(FStar_All.failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
0
end
| (FStar_Syntax_Syntax.U_zero, _41_149) -> begin
(- (1))
end
| (_41_152, FStar_Syntax_Syntax.U_zero) -> begin
1
end
| (FStar_Syntax_Syntax.U_name (u1), FStar_Syntax_Syntax.U_name (u2)) -> begin
(FStar_String.compare u1.FStar_Ident.idText u2.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (_41_161), FStar_Syntax_Syntax.U_unif (_41_164)) -> begin
(- (1))
end
| (FStar_Syntax_Syntax.U_unif (_41_168), FStar_Syntax_Syntax.U_name (_41_171)) -> begin
1
end
| (FStar_Syntax_Syntax.U_unif (u1), FStar_Syntax_Syntax.U_unif (u2)) -> begin
((FStar_Unionfind.uvar_id u1) - (FStar_Unionfind.uvar_id u2))
end
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(let n1 = (FStar_List.length us1)
in (let n2 = (FStar_List.length us2)
in if (n1 <> n2) then begin
(n1 - n2)
end else begin
(let copt = (let _118_83 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map _118_83 (fun _41_188 -> (match (_41_188) with
| (u1, u2) -> begin
(let c = (compare_univs u1 u2)
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
| (FStar_Syntax_Syntax.U_max (_41_195), _41_198) -> begin
(- (1))
end
| (_41_201, FStar_Syntax_Syntax.U_max (_41_203)) -> begin
1
end
| _41_207 -> begin
(let _41_210 = (univ_kernel u1)
in (match (_41_210) with
| (k1, n1) -> begin
(let _41_213 = (univ_kernel u2)
in (match (_41_213) with
| (k2, n2) -> begin
(let r = (compare_univs k1 k2)
in if (r = 0) then begin
(n1 - n2)
end else begin
r
end)
end))
end))
end))

let eq_univs = (fun u1 u2 -> ((compare_univs u1 u2) = 0))

let ml_comp = (fun t r -> (let _118_93 = (let _118_92 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_ML_lid r)
in {FStar_Syntax_Syntax.effect_name = _118_92; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]})
in (FStar_Syntax_Syntax.mk_Comp _118_93)))

let comp_set_flags = (fun c f -> (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (_)) | (FStar_Syntax_Syntax.GTotal (_)) -> begin
c
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _41_229 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ((let _41_231 = ct
in {FStar_Syntax_Syntax.effect_name = _41_231.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _41_231.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _41_231.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})); FStar_Syntax_Syntax.tk = _41_229.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _41_229.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _41_229.FStar_Syntax_Syntax.vars})
end))

let comp_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_41_235) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (_41_238) -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.flags
end))

let comp_effect_name = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
c.FStar_Syntax_Syntax.effect_name
end
| FStar_Syntax_Syntax.Total (_41_246) -> begin
FStar_Syntax_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (_41_249) -> begin
FStar_Syntax_Const.effect_GTot_lid
end))

let comp_to_comp_typ = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
c
end
| FStar_Syntax_Syntax.Total (t) -> begin
{FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.TOTAL)::[]}
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
{FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_GTot_lid; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.SOMETRIVIAL)::[]}
end))

let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _41_2 -> (match (_41_2) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _41_263 -> begin
false
end)))))

let is_total_lcomp = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _41_3 -> (match (_41_3) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _41_269 -> begin
false
end))))))

let is_tot_or_gtot_lcomp = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _41_4 -> (match (_41_4) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _41_275 -> begin
false
end))))))

let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _41_5 -> (match (_41_5) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _41_281 -> begin
false
end)))))

let is_lcomp_partial_return = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _41_6 -> (match (_41_6) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _41_287 -> begin
false
end)))))

let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid (comp_effect_name c))))

let is_pure_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_41_291) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (_41_294) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
((((is_total_comp c) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Pure_lid)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _41_7 -> (match (_41_7) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _41_301 -> begin
false
end)))))
end))

let is_ghost_effect = (fun l -> (((FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_Ghost_lid l)))

let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))

let is_pure_lcomp = (fun lc -> ((((is_total_lcomp lc) || (FStar_Ident.lid_equals lc.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals lc.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Pure_lid)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _41_8 -> (match (_41_8) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _41_308 -> begin
false
end))))))

let is_pure_or_ghost_lcomp = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))

let is_pure_or_ghost_function = (fun t -> (match ((let _118_128 = (FStar_Syntax_Subst.compress t)
in _118_128.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_41_312, c) -> begin
(is_pure_or_ghost_comp c)
end
| _41_317 -> begin
true
end))

let is_lemma = (fun t -> (match ((let _118_131 = (FStar_Syntax_Subst.compress t)
in _118_131.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_41_320, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid)
end
| _41_327 -> begin
false
end)
end
| _41_329 -> begin
false
end))

let is_smt_lemma = (fun t -> (match ((let _118_134 = (FStar_Syntax_Subst.compress t)
in _118_134.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_41_332, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| _req::_ens::(pats, _41_342)::_41_339 -> begin
(match ((let _118_135 = (unmeta pats)
in _118_135.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _41_357); FStar_Syntax_Syntax.tk = _41_354; FStar_Syntax_Syntax.pos = _41_352; FStar_Syntax_Syntax.vars = _41_350}, _41_362) -> begin
(FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.cons_lid)
end
| _41_366 -> begin
false
end)
end
| _41_368 -> begin
false
end)
end
| _41_370 -> begin
false
end)
end
| _41_372 -> begin
false
end))

let is_ml_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _41_9 -> (match (_41_9) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _41_379 -> begin
false
end)))))
end
| _41_381 -> begin
false
end))

let comp_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (t)) | (FStar_Syntax_Syntax.GTotal (t)) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))

let set_result_typ = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_41_391) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (_41_394) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (let _41_398 = ct
in {FStar_Syntax_Syntax.effect_name = _41_398.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = _41_398.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _41_398.FStar_Syntax_Syntax.flags}))
end))

let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _41_10 -> (match (_41_10) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _41_405 -> begin
false
end)))))

let primops = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]

let is_primop = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _41_409) -> begin
(FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v)))
end
| _41_413 -> begin
false
end))

let rec unascribe = (fun e -> (let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e, _41_418, _41_420) -> begin
(unascribe e)
end
| _41_424 -> begin
e
end)))

let rec ascribe = (fun t k -> (Obj.magic ((match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', _41_429, _41_431) -> begin
(Obj.repr (ascribe k))
end
| _41_435 -> begin
(Obj.repr (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((t, k, None))) None t.FStar_Syntax_Syntax.pos))
end))))

let rec unrefine = (fun t -> (let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _41_440) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _41_445, _41_447) -> begin
(unrefine t)
end
| _41_451 -> begin
t
end)))

let is_fun = (fun e -> (match ((let _118_152 = (FStar_Syntax_Subst.compress e)
in _118_152.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_41_454) -> begin
true
end
| _41_457 -> begin
false
end))

let is_function_typ = (fun t -> (match ((let _118_155 = (FStar_Syntax_Subst.compress t)
in _118_155.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_41_460) -> begin
true
end
| _41_463 -> begin
false
end))

let rec pre_typ = (fun t -> (let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _41_468) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _41_473, _41_475) -> begin
(pre_typ t)
end
| _41_479 -> begin
t
end)))

let destruct = (fun typ lid -> (let typ = (FStar_Syntax_Subst.compress typ)
in (match (typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _41_491); FStar_Syntax_Syntax.tk = _41_488; FStar_Syntax_Syntax.pos = _41_486; FStar_Syntax_Syntax.vars = _41_484}, args) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v lid) -> begin
Some (args)
end
| FStar_Syntax_Syntax.Tm_fvar (tc, _41_500) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v lid) -> begin
Some ([])
end
| _41_504 -> begin
None
end)))

let rec lids_of_sigelt = (fun se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_let (_, _, lids, _)) | (FStar_Syntax_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (lid, _, _, _, _, _, _, _))) | (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (lid, _, _, _, _, _, _, _))) | (FStar_Syntax_Syntax.Sig_declare_typ (lid, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect (n, _41_588) -> begin
(n.FStar_Syntax_Syntax.mname)::[]
end
| (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) -> begin
[]
end))

let lid_of_sigelt = (fun se -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _41_604 -> begin
None
end))

let range_of_sigelt = (fun x -> (match (x) with
| (FStar_Syntax_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_inductive_typ (Prims.MkTuple8 (_, _, _, _, _, _, _, r))) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_datacon (Prims.MkTuple8 (_, _, _, _, _, _, _, r))) | (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_assume (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_let (_, r, _, _)) | (FStar_Syntax_Syntax.Sig_main (_, r)) | (FStar_Syntax_Syntax.Sig_pragma (_, r)) | (FStar_Syntax_Syntax.Sig_new_effect (_, r)) | (FStar_Syntax_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))

let range_of_lb = (fun _41_11 -> (match (_41_11) with
| (FStar_Util.Inl (x), _41_705, _41_707) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), _41_712, _41_714) -> begin
(FStar_Ident.range_of_lid l)
end))

let range_of_arg = (fun _41_719 -> (match (_41_719) with
| (hd, _41_718) -> begin
hd.FStar_Syntax_Syntax.pos
end))

let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))

let mk_app = (fun f args -> (let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((f, args))) None r)))

let mk_data = (fun l args -> (match (args) with
| [] -> begin
(let _118_180 = (let _118_179 = (let _118_178 = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (_118_178, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_118_179))
in (FStar_Syntax_Syntax.mk _118_180 None (FStar_Ident.range_of_lid l)))
end
| _41_731 -> begin
(let e = (let _118_181 = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (mk_app _118_181 args))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))) None e.FStar_Syntax_Syntax.pos))
end))

let mangle_field_name = (fun x -> (FStar_Ident.mk_ident ((Prims.strcat "^fname^" x.FStar_Ident.idText), x.FStar_Ident.idRange)))

let unmangle_field_name = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _118_187 = (let _118_186 = (FStar_Util.substring_from x.FStar_Ident.idText 7)
in (_118_186, x.FStar_Ident.idRange))
in (FStar_Ident.mk_ident _118_187))
end else begin
x
end)

let mk_field_projector_name = (fun lid x i -> (let nm = if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _118_197 = (let _118_196 = (let _118_194 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _118_194))
in (let _118_195 = (FStar_Syntax_Syntax.range_of_bv x)
in (_118_196, _118_195)))
in (FStar_Ident.mk_ident _118_197))
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (let y = (let _41_739 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = _41_739.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _41_739.FStar_Syntax_Syntax.sort})
in (let _118_201 = (let _118_200 = (let _118_199 = (let _118_198 = (unmangle_field_name nm)
in (_118_198)::[])
in (FStar_List.append (FStar_Ident.ids_of_lid lid) _118_199))
in (FStar_Ident.lid_of_ids _118_200))
in (_118_201, y)))))

let set_uvar = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (_41_745) -> begin
(let _118_206 = (let _118_205 = (let _118_204 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _118_204))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" _118_205))
in (FStar_All.failwith _118_206))
end
| _41_748 -> begin
(FStar_Unionfind.change uv (FStar_Syntax_Syntax.Fixed (t)))
end))

let qualifier_equal = (fun q1 q2 -> (match ((q1, q2)) with
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
| _41_781 -> begin
(q1 = q2)
end))

let rec arrow_formals_comp = (fun k -> (let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _41_790 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_41_790) with
| (bs, c) -> begin
if (is_tot_or_gtot_comp c) then begin
(let _41_793 = (arrow_formals_comp (comp_result c))
in (match (_41_793) with
| (bs', k) -> begin
((FStar_List.append bs bs'), k)
end))
end else begin
(bs, c)
end
end))
end
| _41_795 -> begin
(let _118_213 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _118_213))
end)))

let rec arrow_formals = (fun k -> (let _41_799 = (arrow_formals_comp k)
in (match (_41_799) with
| (bs, c) -> begin
(bs, (comp_result c))
end)))

let abs = (fun bs t lopt -> (match (bs) with
| [] -> begin
t
end
| _41_805 -> begin
(let body = (let _118_222 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress _118_222))
in (match ((body.FStar_Syntax_Syntax.n, lopt)) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t, lopt'), None) -> begin
(let _118_226 = (let _118_225 = (let _118_224 = (let _118_223 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append _118_223 bs'))
in (_118_224, t, lopt))
in FStar_Syntax_Syntax.Tm_abs (_118_225))
in (FStar_Syntax_Syntax.mk _118_226 None t.FStar_Syntax_Syntax.pos))
end
| _41_815 -> begin
(let lopt = (match (lopt) with
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

let arrow = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| _41_824 -> begin
(let _118_238 = (let _118_237 = (let _118_236 = (FStar_Syntax_Subst.close_binders bs)
in (let _118_235 = (FStar_Syntax_Subst.close_comp bs c)
in (_118_236, _118_235)))
in FStar_Syntax_Syntax.Tm_arrow (_118_237))
in (FStar_Syntax_Syntax.mk _118_238 None c.FStar_Syntax_Syntax.pos))
end))

let refine = (fun b t -> (let _118_250 = (let _118_246 = (let _118_245 = (let _118_244 = (let _118_243 = (FStar_Syntax_Syntax.mk_binder b)
in (_118_243)::[])
in (FStar_Syntax_Subst.close _118_244 t))
in (b, _118_245))
in FStar_Syntax_Syntax.Tm_refine (_118_246))
in (let _118_249 = (FStar_ST.read b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (let _118_248 = (let _118_247 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges _118_247 t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk _118_250 _118_249 _118_248)))))

let branch = (fun b -> (FStar_Syntax_Subst.close_branch b))

let mk_letbinding = (fun lbname univ_vars typ eff def -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def})

let close_univs_and_mk_letbinding = (fun recs lbname univ_vars typ eff def -> (let def = (match (recs) with
| None -> begin
def
end
| Some (lids) -> begin
(let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _118_275 -> FStar_Syntax_Syntax.U_name (_118_275))))
in (let inst = (FStar_All.pipe_right lids (FStar_List.map (fun l -> (l, universes))))
in (FStar_Syntax_InstFV.inst inst def)))
end)
in (let typ = (FStar_Syntax_Subst.close_univ_vars univ_vars typ)
in (let def = (FStar_Syntax_Subst.close_univ_vars univ_vars def)
in (mk_letbinding lbname univ_vars typ eff def)))))

let open_univ_vars_binders_and_comp = (fun uvs binders c -> (match (binders) with
| [] -> begin
(let _41_854 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_41_854) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _41_856 -> begin
(let t' = (arrow binders c)
in (let _41_860 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_41_860) with
| (uvs, t') -> begin
(match ((let _118_283 = (FStar_Syntax_Subst.compress t')
in _118_283.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _41_866 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))

let is_tuple_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (l, _41_870) -> begin
(FStar_Util.starts_with l.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.Tuple")
end
| _41_874 -> begin
false
end))

let mk_tuple_lid = (fun n r -> (let t = (let _118_290 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Tuple%s" _118_290))
in (let _118_291 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _118_291 r))))

let mk_tuple_data_lid = (fun n r -> (let t = (let _118_296 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkTuple%s" _118_296))
in (let _118_297 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _118_297 r))))

let is_tuple_data_lid = (fun f n -> (let _118_302 = (mk_tuple_data_lid n FStar_Range.dummyRange)
in (FStar_Ident.lid_equals f _118_302)))

let is_dtuple_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (l, _41_886) -> begin
(FStar_Util.starts_with l.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.DTuple")
end
| _41_890 -> begin
false
end))

let mk_dtuple_lid = (fun n r -> (let t = (let _118_309 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "DTuple%s" _118_309))
in (let _118_310 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _118_310 r))))

let mk_dtuple_data_lid = (fun n r -> (let t = (let _118_315 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkDTuple%s" _118_315))
in (let _118_316 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _118_316 r))))

let is_lid_equality = (fun x -> (FStar_Ident.lid_equals x FStar_Syntax_Const.eq2_lid))

let is_forall = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.forall_lid))

let is_exists = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.exists_lid))

let is_qlid = (fun lid -> ((is_forall lid) || (is_exists lid)))

let is_equality = (fun x -> (is_lid_equality x.FStar_Syntax_Syntax.v))

let lid_is_connective = (let lst = (FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.not_lid)::(FStar_Syntax_Const.iff_lid)::(FStar_Syntax_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))

let is_constructor = (fun t lid -> (match ((let _118_332 = (pre_typ t)
in _118_332.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _41_908) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v lid)
end
| _41_912 -> begin
false
end))

let rec is_constructed_typ = (fun t lid -> (match ((let _118_337 = (pre_typ t)
in _118_337.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (_41_916) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t, _41_920) -> begin
(is_constructed_typ t lid)
end
| _41_924 -> begin
false
end))

let rec get_tycon = (fun t -> (let t = (pre_typ t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_app (t, _41_938) -> begin
(get_tycon t)
end
| _41_942 -> begin
None
end)))

let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _41_948 _41_952 -> (match ((_41_948, _41_952)) with
| ((fn1, _41_947), (fn2, _41_951)) -> begin
(FStar_String.compare (FStar_Ident.text_of_lid fn1) (FStar_Ident.text_of_lid fn2))
end)))))

let is_interpreted = (fun l -> (let theory_syms = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))

let ktype = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None FStar_Range.dummyRange)

let ktype0 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) None FStar_Range.dummyRange)

let type_u = (fun _41_955 -> (match (()) with
| () -> begin
(let u = (let _118_348 = (FStar_Unionfind.fresh None)
in (FStar_All.pipe_left (fun _118_347 -> FStar_Syntax_Syntax.U_unif (_118_347)) _118_348))
in (let _118_349 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None FStar_Range.dummyRange)
in (_118_349, u)))
end))

let kt_kt = (FStar_Syntax_Const.kunary ktype0 ktype0)

let kt_kt_kt = (FStar_Syntax_Const.kbin ktype0 ktype0 ktype0)

let tand = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.and_lid FStar_Range.dummyRange)

let tor = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.or_lid FStar_Range.dummyRange)

let timp = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.imp_lid FStar_Range.dummyRange)

let tiff = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.iff_lid FStar_Range.dummyRange)

let t_bool = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.bool_lid FStar_Range.dummyRange)

let t_false = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.false_lid FStar_Range.dummyRange)

let t_true = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid FStar_Range.dummyRange)

let b2t_v = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.b2t_lid FStar_Range.dummyRange)

let t_not = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.not_lid FStar_Range.dummyRange)

let mk_conj_opt = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _118_361 = (let _118_360 = (let _118_358 = (let _118_357 = (let _118_356 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _118_355 = (let _118_354 = (FStar_Syntax_Syntax.as_arg phi2)
in (_118_354)::[])
in (_118_356)::_118_355))
in (tand, _118_357))
in FStar_Syntax_Syntax.Tm_app (_118_358))
in (let _118_359 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _118_360 None _118_359)))
in Some (_118_361))
end))

let mk_binop = (fun op_t phi1 phi2 -> (let _118_371 = (let _118_369 = (let _118_368 = (let _118_367 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _118_366 = (let _118_365 = (FStar_Syntax_Syntax.as_arg phi2)
in (_118_365)::[])
in (_118_367)::_118_366))
in (op_t, _118_368))
in FStar_Syntax_Syntax.Tm_app (_118_369))
in (let _118_370 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _118_371 None _118_370))))

let mk_neg = (fun phi -> (let _118_376 = (let _118_375 = (let _118_374 = (let _118_373 = (FStar_Syntax_Syntax.as_arg phi)
in (_118_373)::[])
in (t_not, _118_374))
in FStar_Syntax_Syntax.Tm_app (_118_375))
in (FStar_Syntax_Syntax.mk _118_376 None phi.FStar_Syntax_Syntax.pos)))

let mk_conj = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))

let mk_conj_l = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid FStar_Range.dummyRange)
end
| hd::tl -> begin
(FStar_List.fold_right mk_conj tl hd)
end))

let mk_disj = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))

let mk_disj_l = (fun phi -> (match (phi) with
| [] -> begin
t_false
end
| hd::tl -> begin
(FStar_List.fold_right mk_disj tl hd)
end))

let mk_imp = (fun phi1 phi2 -> (match ((let _118_389 = (FStar_Syntax_Subst.compress phi1)
in _118_389.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _41_984) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.false_lid) -> begin
t_true
end
| FStar_Syntax_Syntax.Tm_fvar (tc, _41_989) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
phi2
end
| _41_993 -> begin
(match ((let _118_390 = (FStar_Syntax_Subst.compress phi2)
in _118_390.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _41_996) when ((FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) || (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.false_lid)) -> begin
phi2
end
| _41_1000 -> begin
(mk_binop timp phi1 phi2)
end)
end))

let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))

let b2t = (fun e -> (let _118_397 = (let _118_396 = (let _118_395 = (let _118_394 = (FStar_Syntax_Syntax.as_arg e)
in (_118_394)::[])
in (b2t_v, _118_395))
in FStar_Syntax_Syntax.Tm_app (_118_396))
in (FStar_Syntax_Syntax.mk _118_397 None e.FStar_Syntax_Syntax.pos)))

let eq_pred_t = (let a = (FStar_Syntax_Syntax.new_bv None ktype0)
in (let atyp = (FStar_Syntax_Syntax.bv_to_tm a)
in (let b = (FStar_Syntax_Syntax.new_bv None ktype0)
in (let btyp = (FStar_Syntax_Syntax.bv_to_tm b)
in (let _118_404 = (let _118_402 = (let _118_401 = (let _118_400 = (FStar_Syntax_Syntax.null_binder atyp)
in (let _118_399 = (let _118_398 = (FStar_Syntax_Syntax.null_binder btyp)
in (_118_398)::[])
in (_118_400)::_118_399))
in ((b, Some (FStar_Syntax_Syntax.Implicit)))::_118_401)
in ((a, Some (FStar_Syntax_Syntax.Implicit)))::_118_402)
in (let _118_403 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (arrow _118_404 _118_403)))))))

let teq = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.eq2_lid FStar_Range.dummyRange)

let mk_eq = (fun t1 t2 e1 e2 -> (let _118_415 = (let _118_413 = (let _118_412 = (let _118_411 = (FStar_Syntax_Syntax.as_arg e1)
in (let _118_410 = (let _118_409 = (FStar_Syntax_Syntax.as_arg e2)
in (_118_409)::[])
in (_118_411)::_118_410))
in (teq, _118_412))
in FStar_Syntax_Syntax.Tm_app (_118_413))
in (let _118_414 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _118_415 None _118_414))))

let lex_t = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.lex_t_lid FStar_Range.dummyRange)

let lex_top = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Data_ctor)) FStar_Syntax_Const.lextop_lid FStar_Range.dummyRange)

let lex_pair = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Data_ctor)) FStar_Syntax_Const.lexcons_lid FStar_Range.dummyRange)

let forall_t = (let a = (FStar_Syntax_Syntax.new_bv None ktype0)
in (let atyp = (FStar_Syntax_Syntax.bv_to_tm a)
in (let _118_419 = (let _118_417 = (let _118_416 = (FStar_Syntax_Syntax.null_binder atyp)
in (_118_416)::[])
in ((a, Some (FStar_Syntax_Syntax.Implicit)))::_118_417)
in (let _118_418 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (arrow _118_419 _118_418)))))

let tforall = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.forall_lid FStar_Range.dummyRange)

let lcomp_of_comp = (fun c0 -> (let c = (comp_to_comp_typ c0)
in {FStar_Syntax_Syntax.eff_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.res_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.cflags = c.FStar_Syntax_Syntax.flags; FStar_Syntax_Syntax.comp = (fun _41_1016 -> (match (()) with
| () -> begin
c0
end))}))

let mk_forall = (fun x body -> (let _118_436 = (let _118_435 = (let _118_434 = (let _118_433 = (let _118_432 = (let _118_431 = (let _118_427 = (FStar_Syntax_Syntax.mk_binder x)
in (_118_427)::[])
in (let _118_430 = (let _118_429 = (let _118_428 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (FStar_All.pipe_left lcomp_of_comp _118_428))
in Some (_118_429))
in (abs _118_431 body _118_430)))
in (FStar_Syntax_Syntax.as_arg _118_432))
in (_118_433)::[])
in (tforall, _118_434))
in FStar_Syntax_Syntax.Tm_app (_118_435))
in (FStar_Syntax_Syntax.mk _118_436 None FStar_Range.dummyRange)))

let rec close_forall = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
f
end else begin
(mk_forall (Prims.fst b) f)
end) bs f))

let rec is_wild_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (_41_1025) -> begin
true
end
| _41_1028 -> begin
false
end))

let head_and_args = (fun t -> (let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(head, args)
end
| _41_1036 -> begin
(t, [])
end)))

let if_then_else = (fun b t1 t2 -> (let then_branch = (let _118_449 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t1.FStar_Syntax_Syntax.pos)
in (_118_449, None, t1))
in (let else_branch = (let _118_450 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Syntax_Syntax.pos)
in (_118_450, None, t2))
in (let _118_452 = (let _118_451 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos _118_451))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((b, (then_branch)::(else_branch)::[]))) None _118_452)))))

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
| QAll (_41_1044) -> begin
_41_1044
end))

let ___QEx____0 = (fun projectee -> (match (projectee) with
| QEx (_41_1047) -> begin
_41_1047
end))

let ___BaseConn____0 = (fun projectee -> (match (projectee) with
| BaseConn (_41_1050) -> begin
_41_1050
end))

let destruct_typ_as_formula = (fun f -> (let un_uinst = (fun t -> (match ((let _118_499 = (FStar_Syntax_Subst.compress t)
in _118_499.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (t, _41_1056) -> begin
t
end
| _41_1060 -> begin
t
end))
in (let destruct_base_conn = (fun f -> (let connectives = ((FStar_Syntax_Const.true_lid, 0))::((FStar_Syntax_Const.false_lid, 0))::((FStar_Syntax_Const.and_lid, 2))::((FStar_Syntax_Const.or_lid, 2))::((FStar_Syntax_Const.imp_lid, 2))::((FStar_Syntax_Const.iff_lid, 2))::((FStar_Syntax_Const.ite_lid, 3))::((FStar_Syntax_Const.not_lid, 1))::((FStar_Syntax_Const.eq2_lid, 4))::((FStar_Syntax_Const.eq2_lid, 2))::[]
in (let rec aux = (fun f _41_1068 -> (match (_41_1068) with
| (lid, arity) -> begin
(let _41_1071 = (head_and_args f)
in (match (_41_1071) with
| (t, args) -> begin
(let t = (un_uinst t)
in if ((is_constructor t lid) && ((FStar_List.length args) = arity)) then begin
Some (BaseConn ((lid, args)))
end else begin
None
end)
end))
end))
in (FStar_Util.find_map connectives (aux f)))))
in (let patterns = (fun t -> (let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(let _118_508 = (FStar_Syntax_Subst.compress t)
in (pats, _118_508))
end
| _41_1082 -> begin
(let _118_509 = (FStar_Syntax_Subst.compress t)
in ([], _118_509))
end)))
in (let destruct_q_conn = (fun t -> (let is_q = (fun fa l -> if fa then begin
(is_forall l)
end else begin
(is_exists l)
end)
in (let flat = (fun t -> (let _41_1092 = (head_and_args t)
in (match (_41_1092) with
| (t, args) -> begin
(let _118_521 = (un_uinst t)
in (let _118_520 = (FStar_All.pipe_right args (FStar_List.map (fun _41_1095 -> (match (_41_1095) with
| (t, imp) -> begin
(let _118_519 = (unascribe t)
in (_118_519, imp))
end))))
in (_118_521, _118_520)))
end)))
in (let rec aux = (fun qopt out t -> (match ((let _118_528 = (flat t)
in (qopt, _118_528))) with
| ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) | ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _::({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) when (is_q fa tc.FStar_Syntax_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) | ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _::({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (b::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)::[]))) when (is_qlid tc.FStar_Syntax_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (Some (b), _41_1234) -> begin
(let bs = (FStar_List.rev out)
in (let _41_1239 = (FStar_Syntax_Subst.open_term bs t)
in (match (_41_1239) with
| (bs, t) -> begin
(let _41_1242 = (patterns t)
in (match (_41_1242) with
| (pats, body) -> begin
if b then begin
Some (QAll ((bs, pats, body)))
end else begin
Some (QEx ((bs, pats, body)))
end
end))
end)))
end
| _41_1244 -> begin
None
end))
in (aux None [] t)))))
in (let phi = (FStar_Syntax_Subst.compress f)
in (match ((destruct_base_conn phi)) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end)))))))




