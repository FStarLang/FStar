
open Prims
let no_free_vars = {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}

let singleton_bv = (fun x -> (let _89_4 = (let _89_3 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Util.set_add x _89_3))
in {FStar_Syntax_Syntax.free_names = _89_4; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}))

let singleton_uv = (fun x -> (let _89_8 = (let _89_7 = (FStar_Syntax_Syntax.new_uv_set ())
in (FStar_Util.set_add x _89_7))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = _89_8; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}))

let singleton_univ = (fun x -> (let _89_12 = (let _89_11 = (FStar_Syntax_Syntax.new_universe_uvar_set ())
in (FStar_Util.set_add x _89_11))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = _89_12}))

let union = (fun f1 f2 -> (let _89_19 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_names f2.FStar_Syntax_Syntax.free_names)
in (let _89_18 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_uvars f2.FStar_Syntax_Syntax.free_uvars)
in (let _89_17 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_univs f2.FStar_Syntax_Syntax.free_univs)
in {FStar_Syntax_Syntax.free_names = _89_19; FStar_Syntax_Syntax.free_uvars = _89_18; FStar_Syntax_Syntax.free_univs = _89_17}))))

let rec free_univs = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_bvar (_)) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unknown) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(free_univs u)
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_List.fold_left (fun out x -> (let _89_24 = (free_univs x)
in (union out _89_24))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u) -> begin
if ((FStar_Unionfind.uvar_id u) = 11303) then begin
(FStar_All.failwith "11303!")
end else begin
(singleton_univ u)
end
end))

let rec free_names_and_uvs' = (fun tm -> (let aux_binders = (fun bs acc -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n _36_31 -> (match (_36_31) with
| (x, _36_30) -> begin
(let _89_40 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _89_40))
end)) acc)))
in (let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_36_34) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(singleton_bv x)
end
| FStar_Syntax_Syntax.Tm_uvar (x, t) -> begin
(singleton_uv (x, t))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(free_univs u)
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let f = (free_names_and_uvars t)
in (FStar_List.fold_left (fun out u -> (let _89_46 = (free_univs u)
in (union out _89_46))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, _36_64) -> begin
(let _89_47 = (free_names_and_uvars t)
in (aux_binders bs _89_47))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _89_48 = (free_names_and_uvars_comp c)
in (aux_binders bs _89_48))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(let _89_49 = (free_names_and_uvars t)
in (aux_binders (((bv, None))::[]) _89_49))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _89_50 = (free_names_and_uvars t)
in (free_names_and_uvars_args args _89_50))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(let _89_59 = (let _89_58 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n _36_87 -> (match (_36_87) with
| (p, wopt, t) -> begin
(let n1 = (match (wopt) with
| None -> begin
no_free_vars
end
| Some (w) -> begin
(free_names_and_uvars w)
end)
in (let n2 = (free_names_and_uvars t)
in (let n = (let _89_53 = (union n2 n)
in (union n1 _89_53))
in (let _89_57 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _89_57 (FStar_List.fold_left (fun n x -> (let _89_56 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _89_56))) n))))))
end)) _89_58))
in (FStar_All.pipe_right pats _89_59))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, _36_99) -> begin
(let _89_61 = (free_names_and_uvars t1)
in (let _89_60 = (free_names_and_uvars t2)
in (union _89_61 _89_60)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(let _89_68 = (let _89_67 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n lb -> (let _89_66 = (let _89_65 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp)
in (let _89_64 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef)
in (union _89_65 _89_64)))
in (union n _89_66))) _89_67))
in (FStar_All.pipe_right (Prims.snd lbs) _89_68))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _89_69 = (free_names_and_uvars t)
in (FStar_List.fold_right free_names_and_uvars_args args _89_69))
end
| FStar_Syntax_Syntax.Tm_meta (t, _36_115) -> begin
(free_names_and_uvars t)
end))))
and free_names_and_uvars = (fun t -> (let t = (FStar_Syntax_Subst.compress t)
in (match ((FStar_ST.read t.FStar_Syntax_Syntax.vars)) with
| Some (n) -> begin
if (should_invalidate_cache n) then begin
(let _36_122 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.vars None)
in (free_names_and_uvars t))
end else begin
n
end
end
| _36_125 -> begin
(let n = (free_names_and_uvs' t)
in (let _36_127 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.vars (Some (n)))
in n))
end)))
and free_names_and_uvars_args = (fun args acc -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n _36_135 -> (match (_36_135) with
| (x, _36_134) -> begin
(let _89_75 = (free_names_and_uvars x)
in (union n _89_75))
end)) acc)))
and free_names_and_uvars_binders = (fun bs acc -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n _36_142 -> (match (_36_142) with
| (x, _36_141) -> begin
(let _89_78 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _89_78))
end)) acc)))
and free_names_and_uvars_comp = (fun c -> (match ((FStar_ST.read c.FStar_Syntax_Syntax.vars)) with
| Some (n) -> begin
if (should_invalidate_cache n) then begin
(let _36_146 = (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars None)
in (free_names_and_uvars_comp c))
end else begin
n
end
end
| _36_149 -> begin
(let n = (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (t)) | (FStar_Syntax_Syntax.Total (t)) -> begin
(free_names_and_uvars t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _89_80 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args _89_80))
end)
in (let _36_156 = (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars (Some (n)))
in n))
end))
and should_invalidate_cache = (fun n -> ((let _89_83 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_uvars FStar_Util.set_elements)
in (FStar_All.pipe_right _89_83 (FStar_Util.for_some (fun _36_162 -> (match (_36_162) with
| (u, _36_161) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Fixed (_36_164) -> begin
true
end
| _36_167 -> begin
false
end)
end))))) || (let _89_85 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_univs FStar_Util.set_elements)
in (FStar_All.pipe_right _89_85 (FStar_Util.for_some (fun u -> (match ((FStar_Unionfind.find u)) with
| Some (_36_170) -> begin
true
end
| None -> begin
false
end)))))))

let names = (fun t -> (let _89_88 = (free_names_and_uvars t)
in _89_88.FStar_Syntax_Syntax.free_names))

let uvars = (fun t -> (let _89_91 = (free_names_and_uvars t)
in _89_91.FStar_Syntax_Syntax.free_uvars))

let univs = (fun t -> (let _89_94 = (free_names_and_uvars t)
in _89_94.FStar_Syntax_Syntax.free_univs))

let names_of_binders = (fun bs -> (let _89_97 = (free_names_and_uvars_binders bs no_free_vars)
in _89_97.FStar_Syntax_Syntax.free_names))




