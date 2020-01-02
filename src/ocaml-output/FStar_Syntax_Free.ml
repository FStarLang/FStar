
open Prims
open FStar_Pervasives

type free_vars_and_fvars =
(FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)


let no_free_vars : (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (

let uu____12 = (FStar_Syntax_Syntax.new_fv_set ())
in (({FStar_Syntax_Syntax.free_names = []; FStar_Syntax_Syntax.free_uvars = []; FStar_Syntax_Syntax.free_univs = []; FStar_Syntax_Syntax.free_univ_names = []}), (uu____12)))


let singleton_fvar : FStar_Syntax_Syntax.fv  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun fv -> (

let uu____29 = (

let uu____32 = (FStar_Syntax_Syntax.new_fv_set ())
in (FStar_Util.set_add fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v uu____32))
in (((FStar_Pervasives_Native.fst no_free_vars)), (uu____29))))


let singleton_bv : FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___2_54 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = (x)::[]; FStar_Syntax_Syntax.free_uvars = uu___2_54.FStar_Syntax_Syntax.free_uvars; FStar_Syntax_Syntax.free_univs = uu___2_54.FStar_Syntax_Syntax.free_univs; FStar_Syntax_Syntax.free_univ_names = uu___2_54.FStar_Syntax_Syntax.free_univ_names})), ((FStar_Pervasives_Native.snd no_free_vars))))


let singleton_uv : FStar_Syntax_Syntax.ctx_uvar  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___5_74 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = uu___5_74.FStar_Syntax_Syntax.free_names; FStar_Syntax_Syntax.free_uvars = (x)::[]; FStar_Syntax_Syntax.free_univs = uu___5_74.FStar_Syntax_Syntax.free_univs; FStar_Syntax_Syntax.free_univ_names = uu___5_74.FStar_Syntax_Syntax.free_univ_names})), ((FStar_Pervasives_Native.snd no_free_vars))))


let singleton_univ : FStar_Syntax_Syntax.universe_uvar  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___8_94 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = uu___8_94.FStar_Syntax_Syntax.free_names; FStar_Syntax_Syntax.free_uvars = uu___8_94.FStar_Syntax_Syntax.free_uvars; FStar_Syntax_Syntax.free_univs = (x)::[]; FStar_Syntax_Syntax.free_univ_names = uu___8_94.FStar_Syntax_Syntax.free_univ_names})), ((FStar_Pervasives_Native.snd no_free_vars))))


let singleton_univ_name : FStar_Syntax_Syntax.univ_name  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___11_114 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = uu___11_114.FStar_Syntax_Syntax.free_names; FStar_Syntax_Syntax.free_uvars = uu___11_114.FStar_Syntax_Syntax.free_uvars; FStar_Syntax_Syntax.free_univs = uu___11_114.FStar_Syntax_Syntax.free_univs; FStar_Syntax_Syntax.free_univ_names = (x)::[]})), ((FStar_Pervasives_Native.snd no_free_vars))))


let union : free_vars_and_fvars  ->  free_vars_and_fvars  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun f1 f2 -> (

let uu____136 = (FStar_Util.set_union (FStar_Pervasives_Native.snd f1) (FStar_Pervasives_Native.snd f2))
in (({FStar_Syntax_Syntax.free_names = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_names (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_names); FStar_Syntax_Syntax.free_uvars = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_uvars (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_uvars); FStar_Syntax_Syntax.free_univs = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univs (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univs); FStar_Syntax_Syntax.free_univ_names = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univ_names (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univ_names)}), (uu____136))))


let rec free_univs : FStar_Syntax_Syntax.universe  ->  free_vars_and_fvars = (fun u -> (

let uu____167 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____167) with
| FStar_Syntax_Syntax.U_zero -> begin
no_free_vars
end
| FStar_Syntax_Syntax.U_bvar (uu____168) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.U_unknown -> begin
no_free_vars
end
| FStar_Syntax_Syntax.U_name (uname) -> begin
(singleton_univ_name uname)
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(free_univs u1)
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_List.fold_left (fun out x -> (

let uu____180 = (free_univs x)
in (union out uu____180))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(singleton_univ u1)
end)))


let rec free_names_and_uvs' : FStar_Syntax_Syntax.term  ->  Prims.bool  ->  free_vars_and_fvars = (fun tm use_cache -> (

let aux_binders = (fun bs from_body -> (

let from_binders = (FStar_All.pipe_right bs (FStar_List.fold_left (fun n1 uu____308 -> (match (uu____308) with
| (x, uu____316) -> begin
(

let uu____321 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n1 uu____321))
end)) no_free_vars))
in (union from_binders from_body)))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____323) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(singleton_bv x)
end
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____349) -> begin
(singleton_uv uv)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(free_univs u)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____367) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(singleton_fvar fv)
end
| FStar_Syntax_Syntax.Tm_constant (uu____369) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_lazy (uu____370) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let f = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun out u -> (

let uu____383 = (free_univs u)
in (union out uu____383))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____386) -> begin
(

let uu____411 = (free_names_and_uvars t1 use_cache)
in (aux_binders bs uu____411))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____434 = (free_names_and_uvars_comp c use_cache)
in (aux_binders bs uu____434))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t1) -> begin
(

let uu____441 = (free_names_and_uvars t1 use_cache)
in (aux_binders ((((bv), (FStar_Pervasives_Native.None)))::[]) uu____441))
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
(

let uu____482 = (free_names_and_uvars t1 use_cache)
in (free_names_and_uvars_args args uu____482 use_cache))
end
| FStar_Syntax_Syntax.Tm_match (t1, pats) -> begin
(

let uu____527 = (

let uu____546 = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun n1 uu____569 -> (match (uu____569) with
| (p, wopt, t2) -> begin
(

let n11 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
no_free_vars
end
| FStar_Pervasives_Native.Some (w) -> begin
(free_names_and_uvars w use_cache)
end)
in (

let n2 = (free_names_and_uvars t2 use_cache)
in (

let n3 = (

let uu____607 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right uu____607 (FStar_List.fold_left (fun n3 x -> (

let uu____617 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n3 uu____617))) n1)))
in (

let uu____618 = (union n11 n2)
in (union n3 uu____618)))))
end)) uu____546))
in (FStar_All.pipe_right pats uu____527))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____635) -> begin
(

let u1 = (free_names_and_uvars t1 use_cache)
in (

let u2 = (match ((FStar_Pervasives_Native.fst asc)) with
| FStar_Util.Inl (t2) -> begin
(free_names_and_uvars t2 use_cache)
end
| FStar_Util.Inr (c2) -> begin
(free_names_and_uvars_comp c2 use_cache)
end)
in (match ((FStar_Pervasives_Native.snd asc)) with
| FStar_Pervasives_Native.None -> begin
(union u1 u2)
end
| FStar_Pervasives_Native.Some (tac) -> begin
(

let uu____723 = (union u1 u2)
in (

let uu____724 = (free_names_and_uvars tac use_cache)
in (union uu____723 uu____724)))
end)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t1) -> begin
(

let uu____745 = (

let uu____752 = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun n1 lb -> (

let uu____758 = (

let uu____759 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp use_cache)
in (

let uu____760 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef use_cache)
in (union uu____759 uu____760)))
in (union n1 uu____758))) uu____752))
in (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____745))
end
| FStar_Syntax_Syntax.Tm_quoted (tm1, qi) -> begin
(match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_static -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(free_names_and_uvars tm1 use_cache)
end)
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
(

let u1 = (free_names_and_uvars t1 use_cache)
in (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (uu____779, args) -> begin
(FStar_List.fold_right (fun a acc -> (free_names_and_uvars_args a acc use_cache)) args u1)
end
| FStar_Syntax_Syntax.Meta_monadic (uu____849, t') -> begin
(

let uu____855 = (free_names_and_uvars t' use_cache)
in (union u1 uu____855))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____856, uu____857, t') -> begin
(

let uu____863 = (free_names_and_uvars t' use_cache)
in (union u1 uu____863))
end
| FStar_Syntax_Syntax.Meta_labeled (uu____864) -> begin
u1
end
| FStar_Syntax_Syntax.Meta_desugared (uu____873) -> begin
u1
end
| FStar_Syntax_Syntax.Meta_named (uu____874) -> begin
u1
end))
end))))
and free_names_and_uvars : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  free_vars_and_fvars = (fun t use_cache -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let uu____881 = (FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars)
in (match (uu____881) with
| FStar_Pervasives_Native.Some (n1) when (

let uu____908 = (should_invalidate_cache n1 use_cache)
in (not (uu____908))) -> begin
(

let uu____910 = (FStar_Syntax_Syntax.new_fv_set ())
in ((n1), (uu____910)))
end
| uu____915 -> begin
((FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars FStar_Pervasives_Native.None);
(

let n1 = (free_names_and_uvs' t1 use_cache)
in ((FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars (FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.fst n1))));
n1;
));
)
end))))
and free_names_and_uvars_args : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)  ->  Prims.bool  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun args acc use_cache -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n1 uu____1019 -> (match (uu____1019) with
| (x, uu____1029) -> begin
(

let uu____1038 = (free_names_and_uvars x use_cache)
in (union n1 uu____1038))
end)) acc)))
and free_names_and_uvars_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  free_vars_and_fvars = (fun c use_cache -> (

let uu____1044 = (FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars)
in (match (uu____1044) with
| FStar_Pervasives_Native.Some (n1) -> begin
(

let uu____1071 = (should_invalidate_cache n1 use_cache)
in (match (uu____1071) with
| true -> begin
((FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars FStar_Pervasives_Native.None);
(free_names_and_uvars_comp c use_cache);
)
end
| uu____1098 -> begin
(

let uu____1100 = (FStar_Syntax_Syntax.new_fv_set ())
in ((n1), (uu____1100)))
end))
end
| uu____1105 -> begin
(

let n1 = (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.None) -> begin
(free_names_and_uvars t use_cache)
end
| FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.None) -> begin
(free_names_and_uvars t use_cache)
end
| FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.Some (u)) -> begin
(

let uu____1143 = (free_univs u)
in (

let uu____1144 = (free_names_and_uvars t use_cache)
in (union uu____1143 uu____1144)))
end
| FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.Some (u)) -> begin
(

let uu____1153 = (free_univs u)
in (

let uu____1154 = (free_names_and_uvars t use_cache)
in (union uu____1153 uu____1154)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let us = (

let uu____1163 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ use_cache)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args uu____1163 use_cache))
in (FStar_List.fold_left (fun us1 u -> (

let uu____1175 = (free_univs u)
in (union us1 uu____1175))) us ct.FStar_Syntax_Syntax.comp_univs))
end)
in ((FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars (FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.fst n1))));
n1;
))
end)))
and should_invalidate_cache : FStar_Syntax_Syntax.free_vars  ->  Prims.bool  ->  Prims.bool = (fun n1 use_cache -> ((not (use_cache)) || ((FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars (FStar_Util.for_some (fun u -> (

let uu____1212 = (FStar_Syntax_Unionfind.find u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____1212) with
| FStar_Pervasives_Native.Some (uu____1216) -> begin
true
end
| uu____1218 -> begin
false
end))))) || (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs (FStar_Util.for_some (fun u -> (

let uu____1229 = (FStar_Syntax_Unionfind.univ_find u)
in (match (uu____1229) with
| FStar_Pervasives_Native.Some (uu____1233) -> begin
true
end
| FStar_Pervasives_Native.None -> begin
false
end))))))))


let free_names_and_uvars_binders : FStar_Syntax_Syntax.binders  ->  free_vars_and_fvars  ->  Prims.bool  ->  free_vars_and_fvars = (fun bs acc use_cache -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n1 uu____1274 -> (match (uu____1274) with
| (x, uu____1282) -> begin
(

let uu____1287 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n1 uu____1287))
end)) acc)))


let compare_uv : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.ctx_uvar  ->  Prims.int = (fun uv1 uv2 -> (

let uu____1300 = (FStar_Syntax_Unionfind.uvar_id uv1.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____1302 = (FStar_Syntax_Unionfind.uvar_id uv2.FStar_Syntax_Syntax.ctx_uvar_head)
in (uu____1300 - uu____1302))))


let new_uv_set : unit  ->  FStar_Syntax_Syntax.uvars = (fun uu____1309 -> (FStar_Util.new_set compare_uv))


let compare_universe_uvar : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.int = (fun x y -> (

let uu____1322 = (FStar_Syntax_Unionfind.univ_uvar_id x)
in (

let uu____1324 = (FStar_Syntax_Unionfind.univ_uvar_id y)
in (uu____1322 - uu____1324))))


let new_universe_uvar_set : unit  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun uu____1333 -> (FStar_Util.new_set compare_universe_uvar))


let empty : FStar_Syntax_Syntax.bv FStar_Util.set = (FStar_Util.new_set FStar_Syntax_Syntax.order_bv)


let names : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun t -> (

let uu____1347 = (

let uu____1350 = (

let uu____1351 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1351))
in uu____1350.FStar_Syntax_Syntax.free_names)
in (FStar_Util.as_set uu____1347 FStar_Syntax_Syntax.order_bv)))


let uvars : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.ctx_uvar FStar_Util.set = (fun t -> (

let uu____1369 = (

let uu____1372 = (

let uu____1373 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1373))
in uu____1372.FStar_Syntax_Syntax.free_uvars)
in (FStar_Util.as_set uu____1369 compare_uv)))


let univs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun t -> (

let uu____1391 = (

let uu____1394 = (

let uu____1395 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1395))
in uu____1394.FStar_Syntax_Syntax.free_univs)
in (FStar_Util.as_set uu____1391 compare_universe_uvar)))


let univnames : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun t -> (

let uu____1413 = (

let uu____1416 = (

let uu____1417 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1417))
in uu____1416.FStar_Syntax_Syntax.free_univ_names)
in (FStar_Util.as_set uu____1413 FStar_Syntax_Syntax.order_univ_name)))


let univnames_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun c -> (

let uu____1435 = (

let uu____1438 = (

let uu____1439 = (free_names_and_uvars_comp c true)
in (FStar_Pervasives_Native.fst uu____1439))
in uu____1438.FStar_Syntax_Syntax.free_univ_names)
in (FStar_Util.as_set uu____1435 FStar_Syntax_Syntax.order_univ_name)))


let fvars : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident FStar_Util.set = (fun t -> (

let uu____1457 = (free_names_and_uvars t false)
in (FStar_Pervasives_Native.snd uu____1457)))


let names_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun bs -> (

let uu____1475 = (

let uu____1478 = (

let uu____1479 = (free_names_and_uvars_binders bs no_free_vars true)
in (FStar_Pervasives_Native.fst uu____1479))
in uu____1478.FStar_Syntax_Syntax.free_names)
in (FStar_Util.as_set uu____1475 FStar_Syntax_Syntax.order_bv)))


let uvars_uncached : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.ctx_uvar FStar_Util.set = (fun t -> (

let uu____1497 = (

let uu____1500 = (

let uu____1501 = (free_names_and_uvars t false)
in (FStar_Pervasives_Native.fst uu____1501))
in uu____1500.FStar_Syntax_Syntax.free_uvars)
in (FStar_Util.as_set uu____1497 compare_uv)))




