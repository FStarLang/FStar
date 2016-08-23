
open Prims
# 34 "FStar.Syntax.Free.fst"
let no_free_vars : FStar_Syntax_Syntax.free_vars = {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}

# 39 "FStar.Syntax.Free.fst"
let singleton_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _129_4 = (let _129_3 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Util.set_add x _129_3))
in {FStar_Syntax_Syntax.free_names = _129_4; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}))

# 44 "FStar.Syntax.Free.fst"
let singleton_uv : ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _129_8 = (let _129_7 = (FStar_Syntax_Syntax.new_uv_set ())
in (FStar_Util.set_add x _129_7))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = _129_8; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}))

# 49 "FStar.Syntax.Free.fst"
let singleton_univ : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _129_12 = (let _129_11 = (FStar_Syntax_Syntax.new_universe_uvar_set ())
in (FStar_Util.set_add x _129_11))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = _129_12}))

# 54 "FStar.Syntax.Free.fst"
let union : FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars = (fun f1 f2 -> (let _129_19 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_names f2.FStar_Syntax_Syntax.free_names)
in (let _129_18 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_uvars f2.FStar_Syntax_Syntax.free_uvars)
in (let _129_17 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_univs f2.FStar_Syntax_Syntax.free_univs)
in {FStar_Syntax_Syntax.free_names = _129_19; FStar_Syntax_Syntax.free_uvars = _129_18; FStar_Syntax_Syntax.free_univs = _129_17}))))

# 60 "FStar.Syntax.Free.fst"
let rec free_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.free_vars = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_bvar (_)) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unknown) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(free_univs u)
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_List.fold_left (fun out x -> (let _129_24 = (free_univs x)
in (union out _129_24))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u) -> begin
(singleton_univ u)
end))

# 69 "FStar.Syntax.Free.fst"
let rec free_names_and_uvs' : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.free_vars = (fun tm -> (
# 70 "FStar.Syntax.Free.fst"
let aux_binders = (fun bs acc -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n _36_31 -> (match (_36_31) with
| (x, _36_30) -> begin
(let _129_40 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _129_40))
end)) acc)))
in (
# 72 "FStar.Syntax.Free.fst"
let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_36_34) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(singleton_bv x)
end
| FStar_Syntax_Syntax.Tm_uvar (x, t) -> begin
(singleton_uv ((x), (t)))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(free_univs u)
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(
# 92 "FStar.Syntax.Free.fst"
let f = (free_names_and_uvars t)
in (FStar_List.fold_left (fun out u -> (let _129_46 = (free_univs u)
in (union out _129_46))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, _36_64) -> begin
(let _129_47 = (free_names_and_uvars t)
in (aux_binders bs _129_47))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _129_48 = (free_names_and_uvars_comp c)
in (aux_binders bs _129_48))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(let _129_49 = (free_names_and_uvars t)
in (aux_binders ((((bv), (None)))::[]) _129_49))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _129_50 = (free_names_and_uvars t)
in (free_names_and_uvars_args args _129_50))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(let _129_59 = (let _129_58 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n _36_87 -> (match (_36_87) with
| (p, wopt, t) -> begin
(
# 109 "FStar.Syntax.Free.fst"
let n1 = (match (wopt) with
| None -> begin
no_free_vars
end
| Some (w) -> begin
(free_names_and_uvars w)
end)
in (
# 112 "FStar.Syntax.Free.fst"
let n2 = (free_names_and_uvars t)
in (
# 113 "FStar.Syntax.Free.fst"
let n = (let _129_53 = (union n2 n)
in (union n1 _129_53))
in (let _129_57 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _129_57 (FStar_List.fold_left (fun n x -> (let _129_56 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _129_56))) n))))))
end)) _129_58))
in (FStar_All.pipe_right pats _129_59))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), _36_100) -> begin
(let _129_61 = (free_names_and_uvars t1)
in (let _129_60 = (free_names_and_uvars t2)
in (union _129_61 _129_60)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), _36_107) -> begin
(let _129_63 = (free_names_and_uvars t1)
in (let _129_62 = (free_names_and_uvars_comp c)
in (union _129_63 _129_62)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(let _129_70 = (let _129_69 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n lb -> (let _129_68 = (let _129_67 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp)
in (let _129_66 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef)
in (union _129_67 _129_66)))
in (union n _129_68))) _129_69))
in (FStar_All.pipe_right (Prims.snd lbs) _129_70))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _129_71 = (free_names_and_uvars t)
in (FStar_List.fold_right free_names_and_uvars_args args _129_71))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (_36_123, t')) -> begin
(let _129_73 = (free_names_and_uvars t)
in (let _129_72 = (free_names_and_uvars t')
in (union _129_73 _129_72)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _36_131) -> begin
(free_names_and_uvars t)
end))))
and free_names_and_uvars : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.free_vars = (fun t -> (
# 138 "FStar.Syntax.Free.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match ((FStar_ST.read t.FStar_Syntax_Syntax.vars)) with
| Some (n) -> begin
if (should_invalidate_cache n) then begin
(
# 143 "FStar.Syntax.Free.fst"
let _36_138 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.vars None)
in (free_names_and_uvars t))
end else begin
n
end
end
| _36_141 -> begin
(
# 146 "FStar.Syntax.Free.fst"
let n = (free_names_and_uvs' t)
in (
# 147 "FStar.Syntax.Free.fst"
let _36_143 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.vars (Some (n)))
in n))
end)))
and free_names_and_uvars_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars = (fun args acc -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n _36_151 -> (match (_36_151) with
| (x, _36_150) -> begin
(let _129_79 = (free_names_and_uvars x)
in (union n _129_79))
end)) acc)))
and free_names_and_uvars_binders = (fun bs acc -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n _36_158 -> (match (_36_158) with
| (x, _36_157) -> begin
(let _129_82 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _129_82))
end)) acc)))
and free_names_and_uvars_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.free_vars = (fun c -> (match ((FStar_ST.read c.FStar_Syntax_Syntax.vars)) with
| Some (n) -> begin
if (should_invalidate_cache n) then begin
(
# 160 "FStar.Syntax.Free.fst"
let _36_162 = (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars None)
in (free_names_and_uvars_comp c))
end else begin
n
end
end
| _36_165 -> begin
(
# 163 "FStar.Syntax.Free.fst"
let n = (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (t)) | (FStar_Syntax_Syntax.Total (t)) -> begin
(free_names_and_uvars t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _129_84 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args _129_84))
end)
in (
# 169 "FStar.Syntax.Free.fst"
let _36_172 = (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars (Some (n)))
in n))
end))
and should_invalidate_cache : FStar_Syntax_Syntax.free_vars  ->  Prims.bool = (fun n -> ((let _129_87 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_uvars FStar_Util.set_elements)
in (FStar_All.pipe_right _129_87 (FStar_Util.for_some (fun _36_178 -> (match (_36_178) with
| (u, _36_177) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Fixed (_36_180) -> begin
true
end
| _36_183 -> begin
false
end)
end))))) || (let _129_89 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_univs FStar_Util.set_elements)
in (FStar_All.pipe_right _129_89 (FStar_Util.for_some (fun u -> (match ((FStar_Unionfind.find u)) with
| Some (_36_186) -> begin
true
end
| None -> begin
false
end)))))))

# 180 "FStar.Syntax.Free.fst"
let names : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun t -> (let _129_92 = (free_names_and_uvars t)
in _129_92.FStar_Syntax_Syntax.free_names))

# 181 "FStar.Syntax.Free.fst"
let uvars : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set = (fun t -> (let _129_95 = (free_names_and_uvars t)
in _129_95.FStar_Syntax_Syntax.free_uvars))

# 182 "FStar.Syntax.Free.fst"
let univs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun t -> (let _129_98 = (free_names_and_uvars t)
in _129_98.FStar_Syntax_Syntax.free_univs))

# 183 "FStar.Syntax.Free.fst"
let names_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun bs -> (let _129_101 = (free_names_and_uvars_binders bs no_free_vars)
in _129_101.FStar_Syntax_Syntax.free_names))




