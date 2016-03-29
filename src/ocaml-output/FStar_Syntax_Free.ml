
open Prims
# 29 "FStar.Syntax.Free.fst"
let no_free_vars : FStar_Syntax_Syntax.free_vars = {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}

# 38 "FStar.Syntax.Free.fst"
let singleton_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _105_4 = (let _105_3 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Util.set_add x _105_3))
in {FStar_Syntax_Syntax.free_names = _105_4; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}))

# 43 "FStar.Syntax.Free.fst"
let singleton_uv : ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _105_8 = (let _105_7 = (FStar_Syntax_Syntax.new_uv_set ())
in (FStar_Util.set_add x _105_7))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = _105_8; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}))

# 48 "FStar.Syntax.Free.fst"
let singleton_univ : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _105_12 = (let _105_11 = (FStar_Syntax_Syntax.new_universe_uvar_set ())
in (FStar_Util.set_add x _105_11))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = _105_12}))

# 53 "FStar.Syntax.Free.fst"
let union : FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars = (fun f1 f2 -> (let _105_19 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_names f2.FStar_Syntax_Syntax.free_names)
in (let _105_18 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_uvars f2.FStar_Syntax_Syntax.free_uvars)
in (let _105_17 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_univs f2.FStar_Syntax_Syntax.free_univs)
in {FStar_Syntax_Syntax.free_names = _105_19; FStar_Syntax_Syntax.free_uvars = _105_18; FStar_Syntax_Syntax.free_univs = _105_17}))))

# 58 "FStar.Syntax.Free.fst"
let rec free_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.free_vars = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_bvar (_)) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unknown) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(free_univs u)
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_List.fold_left (fun out x -> (let _105_24 = (free_univs x)
in (union out _105_24))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u) -> begin
(singleton_univ u)
end))

# 67 "FStar.Syntax.Free.fst"
let rec free_names_and_uvs' : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.free_vars = (fun tm -> (
# 70 "FStar.Syntax.Free.fst"
let aux_binders = (fun bs acc -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n _26_31 -> (match (_26_31) with
| (x, _26_30) -> begin
(let _105_40 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _105_40))
end)) acc)))
in (
# 72 "FStar.Syntax.Free.fst"
let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_26_34) -> begin
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
(
# 92 "FStar.Syntax.Free.fst"
let f = (free_names_and_uvars t)
in (FStar_List.fold_left (fun out u -> (let _105_46 = (free_univs u)
in (union out _105_46))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, _26_64) -> begin
(let _105_47 = (free_names_and_uvars t)
in (aux_binders bs _105_47))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _105_48 = (free_names_and_uvars_comp c)
in (aux_binders bs _105_48))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(let _105_49 = (free_names_and_uvars t)
in (aux_binders (((bv, None))::[]) _105_49))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _105_50 = (free_names_and_uvars t)
in (free_names_and_uvars_args args _105_50))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(let _105_59 = (let _105_58 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n _26_87 -> (match (_26_87) with
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
let n = (let _105_53 = (union n2 n)
in (union n1 _105_53))
in (let _105_57 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _105_57 (FStar_List.fold_left (fun n x -> (let _105_56 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _105_56))) n))))))
end)) _105_58))
in (FStar_All.pipe_right pats _105_59))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), _26_100) -> begin
(let _105_61 = (free_names_and_uvars t1)
in (let _105_60 = (free_names_and_uvars t2)
in (union _105_61 _105_60)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), _26_107) -> begin
(let _105_63 = (free_names_and_uvars t1)
in (let _105_62 = (free_names_and_uvars_comp c)
in (union _105_63 _105_62)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(let _105_70 = (let _105_69 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n lb -> (let _105_68 = (let _105_67 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp)
in (let _105_66 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef)
in (union _105_67 _105_66)))
in (union n _105_68))) _105_69))
in (FStar_All.pipe_right (Prims.snd lbs) _105_70))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _105_71 = (free_names_and_uvars t)
in (FStar_List.fold_right free_names_and_uvars_args args _105_71))
end
| FStar_Syntax_Syntax.Tm_meta (t, _26_123) -> begin
(free_names_and_uvars t)
end))))
and free_names_and_uvars : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.free_vars = (fun t -> (
# 135 "FStar.Syntax.Free.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match ((FStar_ST.read t.FStar_Syntax_Syntax.vars)) with
| Some (n) -> begin
if (should_invalidate_cache n) then begin
(
# 140 "FStar.Syntax.Free.fst"
let _26_130 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.vars None)
in (free_names_and_uvars t))
end else begin
n
end
end
| _26_133 -> begin
(
# 143 "FStar.Syntax.Free.fst"
let n = (free_names_and_uvs' t)
in (
# 144 "FStar.Syntax.Free.fst"
let _26_135 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.vars (Some (n)))
in n))
end)))
and free_names_and_uvars_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars = (fun args acc -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n _26_143 -> (match (_26_143) with
| (x, _26_142) -> begin
(let _105_77 = (free_names_and_uvars x)
in (union n _105_77))
end)) acc)))
and free_names_and_uvars_binders = (fun bs acc -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n _26_150 -> (match (_26_150) with
| (x, _26_149) -> begin
(let _105_80 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _105_80))
end)) acc)))
and free_names_and_uvars_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.free_vars = (fun c -> (match ((FStar_ST.read c.FStar_Syntax_Syntax.vars)) with
| Some (n) -> begin
if (should_invalidate_cache n) then begin
(
# 157 "FStar.Syntax.Free.fst"
let _26_154 = (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars None)
in (free_names_and_uvars_comp c))
end else begin
n
end
end
| _26_157 -> begin
(
# 160 "FStar.Syntax.Free.fst"
let n = (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (t)) | (FStar_Syntax_Syntax.Total (t)) -> begin
(free_names_and_uvars t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _105_82 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args _105_82))
end)
in (
# 166 "FStar.Syntax.Free.fst"
let _26_164 = (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars (Some (n)))
in n))
end))
and should_invalidate_cache : FStar_Syntax_Syntax.free_vars  ->  Prims.bool = (fun n -> ((let _105_85 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_uvars FStar_Util.set_elements)
in (FStar_All.pipe_right _105_85 (FStar_Util.for_some (fun _26_170 -> (match (_26_170) with
| (u, _26_169) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Fixed (_26_172) -> begin
true
end
| _26_175 -> begin
false
end)
end))))) || (let _105_87 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_univs FStar_Util.set_elements)
in (FStar_All.pipe_right _105_87 (FStar_Util.for_some (fun u -> (match ((FStar_Unionfind.find u)) with
| Some (_26_178) -> begin
true
end
| None -> begin
false
end)))))))

# 175 "FStar.Syntax.Free.fst"
let names : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun t -> (let _105_90 = (free_names_and_uvars t)
in _105_90.FStar_Syntax_Syntax.free_names))

# 177 "FStar.Syntax.Free.fst"
let uvars : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set = (fun t -> (let _105_93 = (free_names_and_uvars t)
in _105_93.FStar_Syntax_Syntax.free_uvars))

# 178 "FStar.Syntax.Free.fst"
let univs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun t -> (let _105_96 = (free_names_and_uvars t)
in _105_96.FStar_Syntax_Syntax.free_univs))

# 179 "FStar.Syntax.Free.fst"
let names_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun bs -> (let _105_99 = (free_names_and_uvars_binders bs no_free_vars)
in _105_99.FStar_Syntax_Syntax.free_names))




