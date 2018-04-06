
open Prims
open FStar_Pervasives

type free_vars_and_fvars =
(FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)


let no_free_vars : (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (

let uu____13 = (FStar_Syntax_Syntax.new_fv_set ())
in (({FStar_Syntax_Syntax.free_names = []; FStar_Syntax_Syntax.free_uvars = []; FStar_Syntax_Syntax.free_univs = []; FStar_Syntax_Syntax.free_univ_names = []}), (uu____13)))


let singleton_fvar : FStar_Syntax_Syntax.fv  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun fv -> (

let uu____43 = (

let uu____46 = (FStar_Syntax_Syntax.new_fv_set ())
in (FStar_Util.set_add fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v uu____46))
in (((FStar_Pervasives_Native.fst no_free_vars)), (uu____43))))


let singleton_bv : FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___26_65 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = (x)::[]; FStar_Syntax_Syntax.free_uvars = uu___26_65.FStar_Syntax_Syntax.free_uvars; FStar_Syntax_Syntax.free_univs = uu___26_65.FStar_Syntax_Syntax.free_univs; FStar_Syntax_Syntax.free_univ_names = uu___26_65.FStar_Syntax_Syntax.free_univ_names})), ((FStar_Pervasives_Native.snd no_free_vars))))


let singleton_uv : ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___27_114 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = uu___27_114.FStar_Syntax_Syntax.free_names; FStar_Syntax_Syntax.free_uvars = (x)::[]; FStar_Syntax_Syntax.free_univs = uu___27_114.FStar_Syntax_Syntax.free_univs; FStar_Syntax_Syntax.free_univ_names = uu___27_114.FStar_Syntax_Syntax.free_univ_names})), ((FStar_Pervasives_Native.snd no_free_vars))))


let singleton_univ : FStar_Syntax_Syntax.universe_uvar  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___28_163 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = uu___28_163.FStar_Syntax_Syntax.free_names; FStar_Syntax_Syntax.free_uvars = uu___28_163.FStar_Syntax_Syntax.free_uvars; FStar_Syntax_Syntax.free_univs = (x)::[]; FStar_Syntax_Syntax.free_univ_names = uu___28_163.FStar_Syntax_Syntax.free_univ_names})), ((FStar_Pervasives_Native.snd no_free_vars))))


let singleton_univ_name : FStar_Syntax_Syntax.univ_name  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___29_180 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = uu___29_180.FStar_Syntax_Syntax.free_names; FStar_Syntax_Syntax.free_uvars = uu___29_180.FStar_Syntax_Syntax.free_uvars; FStar_Syntax_Syntax.free_univs = uu___29_180.FStar_Syntax_Syntax.free_univs; FStar_Syntax_Syntax.free_univ_names = (x)::[]})), ((FStar_Pervasives_Native.snd no_free_vars))))


let union : free_vars_and_fvars  ->  free_vars_and_fvars  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun f1 f2 -> (

let uu____197 = (FStar_Util.set_union (FStar_Pervasives_Native.snd f1) (FStar_Pervasives_Native.snd f2))
in (({FStar_Syntax_Syntax.free_names = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_names (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_names); FStar_Syntax_Syntax.free_uvars = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_uvars (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_uvars); FStar_Syntax_Syntax.free_univs = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univs (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univs); FStar_Syntax_Syntax.free_univ_names = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univ_names (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univ_names)}), (uu____197))))


let rec free_univs : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun u -> (

let uu____247 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____247) with
| FStar_Syntax_Syntax.U_zero -> begin
no_free_vars
end
| FStar_Syntax_Syntax.U_bvar (uu____254) -> begin
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

let uu____265 = (free_univs x)
in (union out uu____265))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(singleton_univ u1)
end)))


let rec free_names_and_uvs' : FStar_Syntax_Syntax.term  ->  Prims.bool  ->  free_vars_and_fvars = (fun tm use_cache -> (

let aux_binders = (fun bs from_body -> (

let from_binders = (FStar_All.pipe_right bs (FStar_List.fold_left (fun n1 uu____347 -> (match (uu____347) with
| (x, uu____353) -> begin
(

let uu____354 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n1 uu____354))
end)) no_free_vars))
in (union from_binders from_body)))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____356) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(singleton_bv x)
end
| FStar_Syntax_Syntax.Tm_uvar (x, t1) -> begin
(singleton_uv ((x), (t1)))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(free_univs u)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____421) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(singleton_fvar fv)
end
| FStar_Syntax_Syntax.Tm_constant (uu____423) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_lazy (uu____424) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let f = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun out u -> (

let uu____437 = (free_univs u)
in (union out uu____437))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____440) -> begin
(

let uu____461 = (free_names_and_uvars t1 use_cache)
in (aux_binders bs uu____461))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____480 = (free_names_and_uvars_comp c use_cache)
in (aux_binders bs uu____480))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t1) -> begin
(

let uu____487 = (free_names_and_uvars t1 use_cache)
in (aux_binders ((((bv), (FStar_Pervasives_Native.None)))::[]) uu____487))
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
(

let uu____524 = (free_names_and_uvars t1 use_cache)
in (free_names_and_uvars_args args uu____524 use_cache))
end
| FStar_Syntax_Syntax.Tm_match (t1, pats) -> begin
(

let uu____569 = (

let uu____588 = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun n1 uu____611 -> (match (uu____611) with
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

let uu____661 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right uu____661 (FStar_List.fold_left (fun n3 x -> (

let uu____671 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n3 uu____671))) n1)))
in (

let uu____672 = (union n11 n2)
in (union n3 uu____672)))))
end)) uu____588))
in (FStar_All.pipe_right pats uu____569))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____691) -> begin
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

let uu____779 = (union u1 u2)
in (

let uu____780 = (free_names_and_uvars tac use_cache)
in (union uu____779 uu____780)))
end)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t1) -> begin
(

let uu____799 = (

let uu____804 = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun n1 lb -> (

let uu____810 = (

let uu____811 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp use_cache)
in (

let uu____812 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef use_cache)
in (union uu____811 uu____812)))
in (union n1 uu____810))) uu____804))
in (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____799))
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
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(FStar_List.fold_right (fun a acc -> (free_names_and_uvars_args a acc use_cache)) args u1)
end
| FStar_Syntax_Syntax.Meta_monadic (uu____873, t') -> begin
(

let uu____879 = (free_names_and_uvars t' use_cache)
in (union u1 uu____879))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____880, uu____881, t') -> begin
(

let uu____887 = (free_names_and_uvars t' use_cache)
in (union u1 uu____887))
end
| FStar_Syntax_Syntax.Meta_labeled (uu____888) -> begin
u1
end
| FStar_Syntax_Syntax.Meta_desugared (uu____895) -> begin
u1
end
| FStar_Syntax_Syntax.Meta_named (uu____896) -> begin
u1
end))
end))))
and free_names_and_uvars : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  free_vars_and_fvars = (fun t use_cache -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let uu____902 = (FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars)
in (match (uu____902) with
| FStar_Pervasives_Native.Some (n1) when (

let uu____935 = (should_invalidate_cache n1 use_cache)
in (not (uu____935))) -> begin
(

let uu____936 = (FStar_Syntax_Syntax.new_fv_set ())
in ((n1), (uu____936)))
end
| uu____941 -> begin
((FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars FStar_Pervasives_Native.None);
(

let n1 = (free_names_and_uvs' t1 use_cache)
in ((FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars (FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.fst n1))));
n1;
));
)
end))))
and free_names_and_uvars_args : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)  ->  Prims.bool  ->  free_vars_and_fvars = (fun args acc use_cache -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n1 uu____1044 -> (match (uu____1044) with
| (x, uu____1052) -> begin
(

let uu____1057 = (free_names_and_uvars x use_cache)
in (union n1 uu____1057))
end)) acc)))
and free_names_and_uvars_binders : FStar_Syntax_Syntax.binders  ->  free_vars_and_fvars  ->  Prims.bool  ->  free_vars_and_fvars = (fun bs acc use_cache -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n1 uu____1071 -> (match (uu____1071) with
| (x, uu____1077) -> begin
(

let uu____1078 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n1 uu____1078))
end)) acc)))
and free_names_and_uvars_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  free_vars_and_fvars = (fun c use_cache -> (

let uu____1083 = (FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars)
in (match (uu____1083) with
| FStar_Pervasives_Native.Some (n1) -> begin
(

let uu____1116 = (should_invalidate_cache n1 use_cache)
in (match (uu____1116) with
| true -> begin
((FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars FStar_Pervasives_Native.None);
(free_names_and_uvars_comp c use_cache);
)
end
| uu____1147 -> begin
(

let uu____1148 = (FStar_Syntax_Syntax.new_fv_set ())
in ((n1), (uu____1148)))
end))
end
| uu____1153 -> begin
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

let uu____1179 = (free_univs u)
in (

let uu____1180 = (free_names_and_uvars t use_cache)
in (union uu____1179 uu____1180)))
end
| FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.Some (u)) -> begin
(

let uu____1189 = (free_univs u)
in (

let uu____1190 = (free_names_and_uvars t use_cache)
in (union uu____1189 uu____1190)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let us = (

let uu____1193 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ use_cache)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args uu____1193 use_cache))
in (FStar_List.fold_left (fun us1 u -> (

let uu____1205 = (free_univs u)
in (union us1 uu____1205))) us ct.FStar_Syntax_Syntax.comp_univs))
end)
in ((FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars (FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.fst n1))));
n1;
))
end)))
and should_invalidate_cache : FStar_Syntax_Syntax.free_vars  ->  Prims.bool  ->  Prims.bool = (fun n1 use_cache -> ((not (use_cache)) || ((FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars (FStar_Util.for_some (fun uu____1269 -> (match (uu____1269) with
| (u, uu____1277) -> begin
(

let uu____1282 = (FStar_Syntax_Unionfind.find u)
in (match (uu____1282) with
| FStar_Pervasives_Native.Some (uu____1285) -> begin
true
end
| uu____1286 -> begin
false
end))
end)))) || (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs (FStar_Util.for_some (fun u -> (

let uu____1295 = (FStar_Syntax_Unionfind.univ_find u)
in (match (uu____1295) with
| FStar_Pervasives_Native.Some (uu____1298) -> begin
true
end
| FStar_Pervasives_Native.None -> begin
false
end))))))))


let compare_uv : 'Auu____1303 'Auu____1304 . (FStar_Syntax_Syntax.uvar * 'Auu____1303)  ->  (FStar_Syntax_Syntax.uvar * 'Auu____1304)  ->  Prims.int = (fun uv1 uv2 -> (

let uu____1329 = (FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv1))
in (

let uu____1330 = (FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv2))
in (uu____1329 - uu____1330))))


let new_uv_set : Prims.unit  ->  FStar_Syntax_Syntax.uvars = (fun uu____1333 -> (FStar_Util.new_set compare_uv))


let compare_universe_uvar : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.int = (fun x y -> (

let uu____1350 = (FStar_Syntax_Unionfind.univ_uvar_id x)
in (

let uu____1351 = (FStar_Syntax_Unionfind.univ_uvar_id y)
in (uu____1350 - uu____1351))))


let new_universe_uvar_set : Prims.unit  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun uu____1356 -> (FStar_Util.new_set compare_universe_uvar))


let empty : FStar_Syntax_Syntax.bv FStar_Util.set = (FStar_Util.new_set FStar_Syntax_Syntax.order_bv)


let names : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun t -> (

let uu____1366 = (

let uu____1369 = (

let uu____1370 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1370))
in uu____1369.FStar_Syntax_Syntax.free_names)
in (FStar_Util.as_set uu____1366 FStar_Syntax_Syntax.order_bv)))


let uvars : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set = (fun t -> (

let uu____1388 = (

let uu____1407 = (

let uu____1408 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1408))
in uu____1407.FStar_Syntax_Syntax.free_uvars)
in (FStar_Util.as_set uu____1388 compare_uv)))


let univs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun t -> (

let uu____1442 = (

let uu____1445 = (

let uu____1446 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1446))
in uu____1445.FStar_Syntax_Syntax.free_univs)
in (FStar_Util.as_set uu____1442 compare_universe_uvar)))


let univnames : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun t -> (

let uu____1460 = (

let uu____1463 = (

let uu____1464 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1464))
in uu____1463.FStar_Syntax_Syntax.free_univ_names)
in (FStar_Util.as_set uu____1460 FStar_Syntax_Syntax.order_univ_name)))


let fvars : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident FStar_Util.set = (fun t -> (

let uu____1478 = (free_names_and_uvars t false)
in (FStar_Pervasives_Native.snd uu____1478)))


let names_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun bs -> (

let uu____1492 = (

let uu____1495 = (

let uu____1496 = (free_names_and_uvars_binders bs no_free_vars true)
in (FStar_Pervasives_Native.fst uu____1496))
in uu____1495.FStar_Syntax_Syntax.free_names)
in (FStar_Util.as_set uu____1492 FStar_Syntax_Syntax.order_bv)))




