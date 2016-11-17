
open Prims

let no_free_vars : FStar_Syntax_Syntax.free_vars = {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}


let singleton_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _134_4 = (let _134_3 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Util.set_add x _134_3))
in {FStar_Syntax_Syntax.free_names = _134_4; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}))


let singleton_uv : ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _134_8 = (let _134_7 = (FStar_Syntax_Syntax.new_uv_set ())
in (FStar_Util.set_add x _134_7))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = _134_8; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}))


let singleton_univ : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _134_12 = (let _134_11 = (FStar_Syntax_Syntax.new_universe_uvar_set ())
in (FStar_Util.set_add x _134_11))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = _134_12}))


let union : FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars = (fun f1 f2 -> (let _134_19 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_names f2.FStar_Syntax_Syntax.free_names)
in (let _134_18 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_uvars f2.FStar_Syntax_Syntax.free_uvars)
in (let _134_17 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_univs f2.FStar_Syntax_Syntax.free_univs)
in {FStar_Syntax_Syntax.free_names = _134_19; FStar_Syntax_Syntax.free_uvars = _134_18; FStar_Syntax_Syntax.free_univs = _134_17}))))


let rec free_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.free_vars = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_bvar (_)) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unknown) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(free_univs u)
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_List.fold_left (fun out x -> (let _134_24 = (free_univs x)
in (union out _134_24))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u) -> begin
(singleton_univ u)
end))


let rec free_names_and_uvs' : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.free_vars = (fun tm -> (

let aux_binders = (fun bs acc -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n _37_31 -> (match (_37_31) with
| (x, _37_30) -> begin
(let _134_40 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _134_40))
end)) acc)))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_37_34) -> begin
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

let f = (free_names_and_uvars t)
in (FStar_List.fold_left (fun out u -> (let _134_46 = (free_univs u)
in (union out _134_46))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, _37_64) -> begin
(let _134_47 = (free_names_and_uvars t)
in (aux_binders bs _134_47))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _134_48 = (free_names_and_uvars_comp c)
in (aux_binders bs _134_48))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(let _134_49 = (free_names_and_uvars t)
in (aux_binders ((((bv), (None)))::[]) _134_49))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _134_50 = (free_names_and_uvars t)
in (free_names_and_uvars_args args _134_50))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(let _134_59 = (let _134_58 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n _37_87 -> (match (_37_87) with
| (p, wopt, t) -> begin
(

let n1 = (match (wopt) with
| None -> begin
no_free_vars
end
| Some (w) -> begin
(free_names_and_uvars w)
end)
in (

let n2 = (free_names_and_uvars t)
in (

let n = (let _134_53 = (union n2 n)
in (union n1 _134_53))
in (let _134_57 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _134_57 (FStar_List.fold_left (fun n x -> (let _134_56 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _134_56))) n))))))
end)) _134_58))
in (FStar_All.pipe_right pats _134_59))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), _37_100) -> begin
(let _134_61 = (free_names_and_uvars t1)
in (let _134_60 = (free_names_and_uvars t2)
in (union _134_61 _134_60)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), _37_107) -> begin
(let _134_63 = (free_names_and_uvars t1)
in (let _134_62 = (free_names_and_uvars_comp c)
in (union _134_63 _134_62)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(let _134_70 = (let _134_69 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n lb -> (let _134_68 = (let _134_67 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp)
in (let _134_66 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef)
in (union _134_67 _134_66)))
in (union n _134_68))) _134_69))
in (FStar_All.pipe_right (Prims.snd lbs) _134_70))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _134_71 = (free_names_and_uvars t)
in (FStar_List.fold_right free_names_and_uvars_args args _134_71))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (_37_123, t')) -> begin
(let _134_73 = (free_names_and_uvars t)
in (let _134_72 = (free_names_and_uvars t')
in (union _134_73 _134_72)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _37_131) -> begin
(free_names_and_uvars t)
end))))
and free_names_and_uvars : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.free_vars = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match ((FStar_ST.read t.FStar_Syntax_Syntax.vars)) with
| Some (n) -> begin
if (should_invalidate_cache n) then begin
(

let _37_138 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.vars None)
in (free_names_and_uvars t))
end else begin
n
end
end
| _37_141 -> begin
(

let n = (free_names_and_uvs' t)
in (

let _37_143 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.vars (Some (n)))
in n))
end)))
and free_names_and_uvars_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars = (fun args acc -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n _37_151 -> (match (_37_151) with
| (x, _37_150) -> begin
(let _134_79 = (free_names_and_uvars x)
in (union n _134_79))
end)) acc)))
and free_names_and_uvars_binders = (fun bs acc -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n _37_158 -> (match (_37_158) with
| (x, _37_157) -> begin
(let _134_82 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _134_82))
end)) acc)))
and free_names_and_uvars_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.free_vars = (fun c -> (match ((FStar_ST.read c.FStar_Syntax_Syntax.vars)) with
| Some (n) -> begin
if (should_invalidate_cache n) then begin
(

let _37_162 = (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars None)
in (free_names_and_uvars_comp c))
end else begin
n
end
end
| _37_165 -> begin
(

let n = (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (t, None)) | (FStar_Syntax_Syntax.Total (t, None)) -> begin
(free_names_and_uvars t)
end
| (FStar_Syntax_Syntax.GTotal (t, Some (u))) | (FStar_Syntax_Syntax.Total (t, Some (u))) -> begin
(let _134_85 = (free_univs u)
in (let _134_84 = (free_names_and_uvars t)
in (union _134_85 _134_84)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let us = (let _134_86 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args _134_86))
in (FStar_List.fold_left (fun us u -> (let _134_89 = (free_univs u)
in (union us _134_89))) us ct.FStar_Syntax_Syntax.comp_univs))
end)
in (

let _37_187 = (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars (Some (n)))
in n))
end))
and should_invalidate_cache : FStar_Syntax_Syntax.free_vars  ->  Prims.bool = (fun n -> ((let _134_92 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_uvars FStar_Util.set_elements)
in (FStar_All.pipe_right _134_92 (FStar_Util.for_some (fun _37_193 -> (match (_37_193) with
| (u, _37_192) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Fixed (_37_195) -> begin
true
end
| _37_198 -> begin
false
end)
end))))) || (let _134_94 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_univs FStar_Util.set_elements)
in (FStar_All.pipe_right _134_94 (FStar_Util.for_some (fun u -> (match ((FStar_Unionfind.find u)) with
| Some (_37_201) -> begin
true
end
| None -> begin
false
end)))))))


let names : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun t -> (let _134_97 = (free_names_and_uvars t)
in _134_97.FStar_Syntax_Syntax.free_names))


let uvars : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set = (fun t -> (let _134_100 = (free_names_and_uvars t)
in _134_100.FStar_Syntax_Syntax.free_uvars))


let univs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun t -> (let _134_103 = (free_names_and_uvars t)
in _134_103.FStar_Syntax_Syntax.free_univs))


let names_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun bs -> (let _134_106 = (free_names_and_uvars_binders bs no_free_vars)
in _134_106.FStar_Syntax_Syntax.free_names))




