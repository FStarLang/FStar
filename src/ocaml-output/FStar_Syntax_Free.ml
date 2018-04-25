
open Prims
open FStar_Pervasives

type free_vars_and_fvars =
(FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)


let no_free_vars : (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (

let uu____13 = (FStar_Syntax_Syntax.new_fv_set ())
in (({FStar_Syntax_Syntax.free_names = []; FStar_Syntax_Syntax.free_uvars = []; FStar_Syntax_Syntax.free_univs = []; FStar_Syntax_Syntax.free_univ_names = []}), (uu____13)))


let singleton_fvar : FStar_Syntax_Syntax.fv  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun fv -> (

let uu____45 = (

let uu____48 = (FStar_Syntax_Syntax.new_fv_set ())
in (FStar_Util.set_add fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v uu____48))
in (((FStar_Pervasives_Native.fst no_free_vars)), (uu____45))))


let singleton_bv : FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___28_69 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = (x)::[]; FStar_Syntax_Syntax.free_uvars = uu___28_69.FStar_Syntax_Syntax.free_uvars; FStar_Syntax_Syntax.free_univs = uu___28_69.FStar_Syntax_Syntax.free_univs; FStar_Syntax_Syntax.free_univ_names = uu___28_69.FStar_Syntax_Syntax.free_univ_names})), ((FStar_Pervasives_Native.snd no_free_vars))))


let singleton_uv : ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___29_120 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = uu___29_120.FStar_Syntax_Syntax.free_names; FStar_Syntax_Syntax.free_uvars = (x)::[]; FStar_Syntax_Syntax.free_univs = uu___29_120.FStar_Syntax_Syntax.free_univs; FStar_Syntax_Syntax.free_univ_names = uu___29_120.FStar_Syntax_Syntax.free_univ_names})), ((FStar_Pervasives_Native.snd no_free_vars))))


let singleton_univ : FStar_Syntax_Syntax.universe_uvar  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___30_171 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = uu___30_171.FStar_Syntax_Syntax.free_names; FStar_Syntax_Syntax.free_uvars = uu___30_171.FStar_Syntax_Syntax.free_uvars; FStar_Syntax_Syntax.free_univs = (x)::[]; FStar_Syntax_Syntax.free_univ_names = uu___30_171.FStar_Syntax_Syntax.free_univ_names})), ((FStar_Pervasives_Native.snd no_free_vars))))


let singleton_univ_name : FStar_Syntax_Syntax.univ_name  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___31_190 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = uu___31_190.FStar_Syntax_Syntax.free_names; FStar_Syntax_Syntax.free_uvars = uu___31_190.FStar_Syntax_Syntax.free_uvars; FStar_Syntax_Syntax.free_univs = uu___31_190.FStar_Syntax_Syntax.free_univs; FStar_Syntax_Syntax.free_univ_names = (x)::[]})), ((FStar_Pervasives_Native.snd no_free_vars))))


let union : free_vars_and_fvars  ->  free_vars_and_fvars  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun f1 f2 -> (

let uu____211 = (FStar_Util.set_union (FStar_Pervasives_Native.snd f1) (FStar_Pervasives_Native.snd f2))
in (({FStar_Syntax_Syntax.free_names = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_names (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_names); FStar_Syntax_Syntax.free_uvars = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_uvars (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_uvars); FStar_Syntax_Syntax.free_univs = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univs (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univs); FStar_Syntax_Syntax.free_univ_names = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univ_names (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univ_names)}), (uu____211))))


let rec free_univs : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun u -> (

let uu____263 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____263) with
| FStar_Syntax_Syntax.U_zero -> begin
no_free_vars
end
| FStar_Syntax_Syntax.U_bvar (uu____270) -> begin
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

let uu____281 = (free_univs x)
in (union out uu____281))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(singleton_univ u1)
end)))


let rec free_names_and_uvs' : FStar_Syntax_Syntax.term  ->  Prims.bool  ->  free_vars_and_fvars = (fun tm use_cache -> (

let aux_binders = (fun bs from_body -> (

let from_binders = (FStar_All.pipe_right bs (FStar_List.fold_left (fun n1 uu____395 -> (match (uu____395) with
| (x, uu____401) -> begin
(

let uu____402 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n1 uu____402))
end)) no_free_vars))
in (union from_binders from_body)))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____404) -> begin
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
| FStar_Syntax_Syntax.Tm_bvar (uu____469) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(singleton_fvar fv)
end
| FStar_Syntax_Syntax.Tm_constant (uu____471) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_lazy (uu____472) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let f = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun out u -> (

let uu____485 = (free_univs u)
in (union out uu____485))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____488) -> begin
(

let uu____509 = (free_names_and_uvars t1 use_cache)
in (aux_binders bs uu____509))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____528 = (free_names_and_uvars_comp c use_cache)
in (aux_binders bs uu____528))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t1) -> begin
(

let uu____535 = (free_names_and_uvars t1 use_cache)
in (aux_binders ((((bv), (FStar_Pervasives_Native.None)))::[]) uu____535))
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
(

let uu____572 = (free_names_and_uvars t1 use_cache)
in (free_names_and_uvars_args args uu____572 use_cache))
end
| FStar_Syntax_Syntax.Tm_match (t1, pats) -> begin
(

let uu____617 = (

let uu____638 = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun n1 uu____661 -> (match (uu____661) with
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

let uu____711 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right uu____711 (FStar_List.fold_left (fun n3 x -> (

let uu____721 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n3 uu____721))) n1)))
in (

let uu____722 = (union n11 n2)
in (union n3 uu____722)))))
end)) uu____638))
in (FStar_All.pipe_right pats uu____617))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____741) -> begin
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

let uu____829 = (union u1 u2)
in (

let uu____830 = (free_names_and_uvars tac use_cache)
in (union uu____829 uu____830)))
end)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t1) -> begin
(

let uu____849 = (

let uu____856 = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun n1 lb -> (

let uu____862 = (

let uu____863 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp use_cache)
in (

let uu____864 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef use_cache)
in (union uu____863 uu____864)))
in (union n1 uu____862))) uu____856))
in (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____849))
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
| FStar_Syntax_Syntax.Meta_monadic (uu____925, t') -> begin
(

let uu____931 = (free_names_and_uvars t' use_cache)
in (union u1 uu____931))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____932, uu____933, t') -> begin
(

let uu____939 = (free_names_and_uvars t' use_cache)
in (union u1 uu____939))
end
| FStar_Syntax_Syntax.Meta_labeled (uu____940) -> begin
u1
end
| FStar_Syntax_Syntax.Meta_desugared (uu____947) -> begin
u1
end
| FStar_Syntax_Syntax.Meta_named (uu____948) -> begin
u1
end))
end))))
and free_names_and_uvars : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  free_vars_and_fvars = (fun t use_cache -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let uu____954 = (FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars)
in (match (uu____954) with
| FStar_Pervasives_Native.Some (n1) when (

let uu____991 = (should_invalidate_cache n1 use_cache)
in (not (uu____991))) -> begin
(

let uu____992 = (FStar_Syntax_Syntax.new_fv_set ())
in ((n1), (uu____992)))
end
| uu____997 -> begin
((FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars FStar_Pervasives_Native.None);
(

let n1 = (free_names_and_uvs' t1 use_cache)
in ((FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars (FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.fst n1))));
n1;
));
)
end))))
and free_names_and_uvars_args : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)  ->  Prims.bool  ->  free_vars_and_fvars = (fun args acc use_cache -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n1 uu____1108 -> (match (uu____1108) with
| (x, uu____1116) -> begin
(

let uu____1121 = (free_names_and_uvars x use_cache)
in (union n1 uu____1121))
end)) acc)))
and free_names_and_uvars_binders : FStar_Syntax_Syntax.binders  ->  free_vars_and_fvars  ->  Prims.bool  ->  free_vars_and_fvars = (fun bs acc use_cache -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n1 uu____1135 -> (match (uu____1135) with
| (x, uu____1141) -> begin
(

let uu____1142 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n1 uu____1142))
end)) acc)))
and free_names_and_uvars_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  free_vars_and_fvars = (fun c use_cache -> (

let uu____1147 = (FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars)
in (match (uu____1147) with
| FStar_Pervasives_Native.Some (n1) -> begin
(

let uu____1184 = (should_invalidate_cache n1 use_cache)
in (match (uu____1184) with
| true -> begin
((FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars FStar_Pervasives_Native.None);
(free_names_and_uvars_comp c use_cache);
)
end
| uu____1219 -> begin
(

let uu____1220 = (FStar_Syntax_Syntax.new_fv_set ())
in ((n1), (uu____1220)))
end))
end
| uu____1225 -> begin
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

let uu____1251 = (free_univs u)
in (

let uu____1252 = (free_names_and_uvars t use_cache)
in (union uu____1251 uu____1252)))
end
| FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.Some (u)) -> begin
(

let uu____1261 = (free_univs u)
in (

let uu____1262 = (free_names_and_uvars t use_cache)
in (union uu____1261 uu____1262)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let us = (

let uu____1265 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ use_cache)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args uu____1265 use_cache))
in (FStar_List.fold_left (fun us1 u -> (

let uu____1277 = (free_univs u)
in (union us1 uu____1277))) us ct.FStar_Syntax_Syntax.comp_univs))
end)
in ((FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars (FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.fst n1))));
n1;
))
end)))
and should_invalidate_cache : FStar_Syntax_Syntax.free_vars  ->  Prims.bool  ->  Prims.bool = (fun n1 use_cache -> ((not (use_cache)) || ((FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars (FStar_Util.for_some (fun uu____1345 -> (match (uu____1345) with
| (u, uu____1353) -> begin
(

let uu____1358 = (FStar_Syntax_Unionfind.find u)
in (match (uu____1358) with
| FStar_Pervasives_Native.Some (uu____1361) -> begin
true
end
| uu____1362 -> begin
false
end))
end)))) || (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs (FStar_Util.for_some (fun u -> (

let uu____1371 = (FStar_Syntax_Unionfind.univ_find u)
in (match (uu____1371) with
| FStar_Pervasives_Native.Some (uu____1374) -> begin
true
end
| FStar_Pervasives_Native.None -> begin
false
end))))))))


let compare_uv : 'Auu____1383 'Auu____1384 . (FStar_Syntax_Syntax.uvar * 'Auu____1383)  ->  (FStar_Syntax_Syntax.uvar * 'Auu____1384)  ->  Prims.int = (fun uv1 uv2 -> (

let uu____1411 = (FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv1))
in (

let uu____1412 = (FStar_Syntax_Unionfind.uvar_id (FStar_Pervasives_Native.fst uv2))
in (uu____1411 - uu____1412))))


let new_uv_set : unit  ->  FStar_Syntax_Syntax.uvars = (fun uu____1417 -> (FStar_Util.new_set compare_uv))


let compare_universe_uvar : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.int = (fun x y -> (

let uu____1438 = (FStar_Syntax_Unionfind.univ_uvar_id x)
in (

let uu____1439 = (FStar_Syntax_Unionfind.univ_uvar_id y)
in (uu____1438 - uu____1439))))


let new_universe_uvar_set : unit  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun uu____1446 -> (FStar_Util.new_set compare_universe_uvar))


let empty : FStar_Syntax_Syntax.bv FStar_Util.set = (FStar_Util.new_set FStar_Syntax_Syntax.order_bv)


let names : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun t -> (

let uu____1458 = (

let uu____1461 = (

let uu____1462 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1462))
in uu____1461.FStar_Syntax_Syntax.free_names)
in (FStar_Util.as_set uu____1458 FStar_Syntax_Syntax.order_bv)))


let uvars : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set = (fun t -> (

let uu____1482 = (

let uu____1501 = (

let uu____1502 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1502))
in uu____1501.FStar_Syntax_Syntax.free_uvars)
in (FStar_Util.as_set uu____1482 compare_uv)))


let univs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun t -> (

let uu____1538 = (

let uu____1541 = (

let uu____1542 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1542))
in uu____1541.FStar_Syntax_Syntax.free_univs)
in (FStar_Util.as_set uu____1538 compare_universe_uvar)))


let univnames : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun t -> (

let uu____1558 = (

let uu____1561 = (

let uu____1562 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1562))
in uu____1561.FStar_Syntax_Syntax.free_univ_names)
in (FStar_Util.as_set uu____1558 FStar_Syntax_Syntax.order_univ_name)))


let univnames_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun c -> (

let uu____1578 = (

let uu____1581 = (

let uu____1582 = (free_names_and_uvars_comp c true)
in (FStar_Pervasives_Native.fst uu____1582))
in uu____1581.FStar_Syntax_Syntax.free_univ_names)
in (FStar_Util.as_set uu____1578 FStar_Syntax_Syntax.order_univ_name)))


let fvars : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident FStar_Util.set = (fun t -> (

let uu____1598 = (free_names_and_uvars t false)
in (FStar_Pervasives_Native.snd uu____1598)))


let names_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun bs -> (

let uu____1614 = (

let uu____1617 = (

let uu____1618 = (free_names_and_uvars_binders bs no_free_vars true)
in (FStar_Pervasives_Native.fst uu____1618))
in uu____1617.FStar_Syntax_Syntax.free_names)
in (FStar_Util.as_set uu____1614 FStar_Syntax_Syntax.order_bv)))




