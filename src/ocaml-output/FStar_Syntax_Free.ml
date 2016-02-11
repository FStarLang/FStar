
open Prims
# 29 "free.fs"
let no_free_vars : FStar_Syntax_Syntax.free_vars = {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}

# 34 "free.fs"
let singleton_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _139_4 = (let _139_3 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Util.set_add x _139_3))
in {FStar_Syntax_Syntax.free_names = _139_4; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}))

# 39 "free.fs"
let singleton_uv : ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _139_8 = (let _139_7 = (FStar_Syntax_Syntax.new_uv_set ())
in (FStar_Util.set_add x _139_7))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = _139_8; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}))

# 44 "free.fs"
let singleton_univ : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _139_12 = (let _139_11 = (FStar_Syntax_Syntax.new_universe_uvar_set ())
in (FStar_Util.set_add x _139_11))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = _139_12}))

# 49 "free.fs"
let union : FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars = (fun f1 f2 -> (let _139_19 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_names f2.FStar_Syntax_Syntax.free_names)
in (let _139_18 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_uvars f2.FStar_Syntax_Syntax.free_uvars)
in (let _139_17 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_univs f2.FStar_Syntax_Syntax.free_univs)
in {FStar_Syntax_Syntax.free_names = _139_19; FStar_Syntax_Syntax.free_uvars = _139_18; FStar_Syntax_Syntax.free_univs = _139_17}))))

# 55 "free.fs"
let rec free_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.free_vars = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_bvar (_)) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unknown) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(free_univs u)
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_List.fold_left (fun out x -> (let _139_24 = (free_univs x)
in (union out _139_24))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u) -> begin
if ((FStar_Unionfind.uvar_id u) = 11303) then begin
(FStar_All.failwith "11303!")
end else begin
(singleton_univ u)
end
end))

# 64 "free.fs"
let rec free_names_and_uvs' : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.free_vars = (fun tm -> (let aux_binders = (fun bs acc -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n _37_31 -> (match (_37_31) with
| (x, _37_30) -> begin
(let _139_40 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _139_40))
end)) acc)))
in (let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_37_34) -> begin
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
in (FStar_List.fold_left (fun out u -> (let _139_46 = (free_univs u)
in (union out _139_46))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, _37_64) -> begin
(let _139_47 = (free_names_and_uvars t)
in (aux_binders bs _139_47))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _139_48 = (free_names_and_uvars_comp c)
in (aux_binders bs _139_48))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(let _139_49 = (free_names_and_uvars t)
in (aux_binders (((bv, None))::[]) _139_49))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _139_50 = (free_names_and_uvars t)
in (free_names_and_uvars_args args _139_50))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(let _139_59 = (let _139_58 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n _37_87 -> (match (_37_87) with
| (p, wopt, t) -> begin
(let n1 = (match (wopt) with
| None -> begin
no_free_vars
end
| Some (w) -> begin
(free_names_and_uvars w)
end)
in (let n2 = (free_names_and_uvars t)
in (let n = (let _139_53 = (union n2 n)
in (union n1 _139_53))
in (let _139_57 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _139_57 (FStar_List.fold_left (fun n x -> (let _139_56 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _139_56))) n))))))
end)) _139_58))
in (FStar_All.pipe_right pats _139_59))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, _37_99) -> begin
(let _139_61 = (free_names_and_uvars t1)
in (let _139_60 = (free_names_and_uvars t2)
in (union _139_61 _139_60)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(let _139_68 = (let _139_67 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n lb -> (let _139_66 = (let _139_65 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp)
in (let _139_64 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef)
in (union _139_65 _139_64)))
in (union n _139_66))) _139_67))
in (FStar_All.pipe_right (Prims.snd lbs) _139_68))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _139_69 = (free_names_and_uvars t)
in (FStar_List.fold_right free_names_and_uvars_args args _139_69))
end
| FStar_Syntax_Syntax.Tm_meta (t, _37_115) -> begin
(free_names_and_uvars t)
end))))
and free_names_and_uvars : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.free_vars = (fun t -> (let t = (FStar_Syntax_Subst.compress t)
in (match ((FStar_ST.read t.FStar_Syntax_Syntax.vars)) with
| Some (n) -> begin
if (should_invalidate_cache n) then begin
(let _37_122 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.vars None)
in (free_names_and_uvars t))
end else begin
n
end
end
| _37_125 -> begin
(let n = (free_names_and_uvs' t)
in (let _37_127 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.vars (Some (n)))
in n))
end)))
and free_names_and_uvars_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars = (fun args acc -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n _37_135 -> (match (_37_135) with
| (x, _37_134) -> begin
(let _139_75 = (free_names_and_uvars x)
in (union n _139_75))
end)) acc)))
and free_names_and_uvars_binders = (fun bs acc -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n _37_142 -> (match (_37_142) with
| (x, _37_141) -> begin
(let _139_78 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _139_78))
end)) acc)))
and free_names_and_uvars_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.free_vars = (fun c -> (match ((FStar_ST.read c.FStar_Syntax_Syntax.vars)) with
| Some (n) -> begin
if (should_invalidate_cache n) then begin
(let _37_146 = (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars None)
in (free_names_and_uvars_comp c))
end else begin
n
end
end
| _37_149 -> begin
(let n = (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (t)) | (FStar_Syntax_Syntax.Total (t)) -> begin
(free_names_and_uvars t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _139_80 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args _139_80))
end)
in (let _37_156 = (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars (Some (n)))
in n))
end))
and should_invalidate_cache : FStar_Syntax_Syntax.free_vars  ->  Prims.bool = (fun n -> ((let _139_83 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_uvars FStar_Util.set_elements)
in (FStar_All.pipe_right _139_83 (FStar_Util.for_some (fun _37_162 -> (match (_37_162) with
| (u, _37_161) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Fixed (_37_164) -> begin
true
end
| _37_167 -> begin
false
end)
end))))) || (let _139_85 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_univs FStar_Util.set_elements)
in (FStar_All.pipe_right _139_85 (FStar_Util.for_some (fun u -> (match ((FStar_Unionfind.find u)) with
| Some (_37_170) -> begin
true
end
| None -> begin
false
end)))))))

# 169 "free.fs"
let names : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv Prims.list * (FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  Prims.bool)) = (fun t -> (let _139_94 = (free_names_and_uvars t)
in _139_94.FStar_Syntax_Syntax.free_names))

# 170 "free.fs"
let uvars : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.uvars = (fun t -> (let _139_97 = (free_names_and_uvars t)
in _139_97.FStar_Syntax_Syntax.free_uvars))

# 171 "free.fs"
let univs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.universe_uvar Prims.list * (FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool)) = (fun t -> (let _139_106 = (free_names_and_uvars t)
in _139_106.FStar_Syntax_Syntax.free_univs))

# 172 "free.fs"
let names_of_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv Prims.list * (FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  Prims.bool)) = (fun bs -> (let _139_115 = (free_names_and_uvars_binders bs no_free_vars)
in _139_115.FStar_Syntax_Syntax.free_names))




