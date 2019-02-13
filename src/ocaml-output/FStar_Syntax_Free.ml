
open Prims
open FStar_Pervasives

type free_vars_and_fvars =
(FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)


let no_free_vars : (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (

let uu____13 = (FStar_Syntax_Syntax.new_fv_set ())
in (({FStar_Syntax_Syntax.free_names = []; FStar_Syntax_Syntax.free_uvars = []; FStar_Syntax_Syntax.free_univs = []; FStar_Syntax_Syntax.free_univ_names = []}), (uu____13)))


let singleton_fvar : FStar_Syntax_Syntax.fv  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun fv -> (

let uu____30 = (

let uu____33 = (FStar_Syntax_Syntax.new_fv_set ())
in (FStar_Util.set_add fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v uu____33))
in (((FStar_Pervasives_Native.fst no_free_vars)), (uu____30))))


let singleton_bv : FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___96_55 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = (x)::[]; FStar_Syntax_Syntax.free_uvars = uu___96_55.FStar_Syntax_Syntax.free_uvars; FStar_Syntax_Syntax.free_univs = uu___96_55.FStar_Syntax_Syntax.free_univs; FStar_Syntax_Syntax.free_univ_names = uu___96_55.FStar_Syntax_Syntax.free_univ_names})), ((FStar_Pervasives_Native.snd no_free_vars))))


let singleton_uv : FStar_Syntax_Syntax.ctx_uvar  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___97_75 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = uu___97_75.FStar_Syntax_Syntax.free_names; FStar_Syntax_Syntax.free_uvars = (x)::[]; FStar_Syntax_Syntax.free_univs = uu___97_75.FStar_Syntax_Syntax.free_univs; FStar_Syntax_Syntax.free_univ_names = uu___97_75.FStar_Syntax_Syntax.free_univ_names})), ((FStar_Pervasives_Native.snd no_free_vars))))


let singleton_univ : FStar_Syntax_Syntax.universe_uvar  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___98_95 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = uu___98_95.FStar_Syntax_Syntax.free_names; FStar_Syntax_Syntax.free_uvars = uu___98_95.FStar_Syntax_Syntax.free_uvars; FStar_Syntax_Syntax.free_univs = (x)::[]; FStar_Syntax_Syntax.free_univ_names = uu___98_95.FStar_Syntax_Syntax.free_univ_names})), ((FStar_Pervasives_Native.snd no_free_vars))))


let singleton_univ_name : FStar_Syntax_Syntax.univ_name  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___99_115 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = uu___99_115.FStar_Syntax_Syntax.free_names; FStar_Syntax_Syntax.free_uvars = uu___99_115.FStar_Syntax_Syntax.free_uvars; FStar_Syntax_Syntax.free_univs = uu___99_115.FStar_Syntax_Syntax.free_univs; FStar_Syntax_Syntax.free_univ_names = (x)::[]})), ((FStar_Pervasives_Native.snd no_free_vars))))


let union : free_vars_and_fvars  ->  free_vars_and_fvars  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun f1 f2 -> (

let uu____137 = (FStar_Util.set_union (FStar_Pervasives_Native.snd f1) (FStar_Pervasives_Native.snd f2))
in (({FStar_Syntax_Syntax.free_names = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_names (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_names); FStar_Syntax_Syntax.free_uvars = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_uvars (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_uvars); FStar_Syntax_Syntax.free_univs = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univs (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univs); FStar_Syntax_Syntax.free_univ_names = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univ_names (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univ_names)}), (uu____137))))


let rec free_univs : FStar_Syntax_Syntax.universe  ->  free_vars_and_fvars = (fun u -> (

let uu____168 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____168) with
| FStar_Syntax_Syntax.U_zero -> begin
no_free_vars
end
| FStar_Syntax_Syntax.U_bvar (uu____169) -> begin
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

let uu____181 = (free_univs x)
in (union out uu____181))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(singleton_univ u1)
end)))


let rec free_names_and_uvs' : FStar_Syntax_Syntax.term  ->  Prims.bool  ->  free_vars_and_fvars = (fun tm use_cache -> (

let aux_binders = (fun bs from_body -> (

let from_binders = (FStar_All.pipe_right bs (FStar_List.fold_left (fun n1 uu____322 -> (match (uu____322) with
| (x, uu____330) -> begin
(

let uu____335 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n1 uu____335))
end)) no_free_vars))
in (union from_binders from_body)))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____337) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(singleton_bv x)
end
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____363) -> begin
(singleton_uv uv)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(free_univs u)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____381) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(singleton_fvar fv)
end
| FStar_Syntax_Syntax.Tm_constant (uu____383) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_lazy (uu____384) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let f = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun out u -> (

let uu____397 = (free_univs u)
in (union out uu____397))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____400) -> begin
(

let uu____425 = (free_names_and_uvars t1 use_cache)
in (aux_binders bs uu____425))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____448 = (free_names_and_uvars_comp c use_cache)
in (aux_binders bs uu____448))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t1) -> begin
(

let uu____455 = (free_names_and_uvars t1 use_cache)
in (aux_binders ((((bv), (FStar_Pervasives_Native.None)))::[]) uu____455))
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
(

let uu____496 = (free_names_and_uvars t1 use_cache)
in (free_names_and_uvars_args args uu____496 use_cache))
end
| FStar_Syntax_Syntax.Tm_match (t1, pats) -> begin
(

let uu____541 = (

let uu____560 = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun n1 uu____583 -> (match (uu____583) with
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

let uu____621 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right uu____621 (FStar_List.fold_left (fun n3 x -> (

let uu____631 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n3 uu____631))) n1)))
in (

let uu____632 = (union n11 n2)
in (union n3 uu____632)))))
end)) uu____560))
in (FStar_All.pipe_right pats uu____541))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____649) -> begin
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

let uu____737 = (union u1 u2)
in (

let uu____738 = (free_names_and_uvars tac use_cache)
in (union uu____737 uu____738)))
end)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t1) -> begin
(

let uu____759 = (

let uu____766 = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun n1 lb -> (

let uu____772 = (

let uu____773 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp use_cache)
in (

let uu____774 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef use_cache)
in (union uu____773 uu____774)))
in (union n1 uu____772))) uu____766))
in (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____759))
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
| FStar_Syntax_Syntax.Meta_monadic (uu____842, t') -> begin
(

let uu____848 = (free_names_and_uvars t' use_cache)
in (union u1 uu____848))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____849, uu____850, t') -> begin
(

let uu____856 = (free_names_and_uvars t' use_cache)
in (union u1 uu____856))
end
| FStar_Syntax_Syntax.Meta_labeled (uu____857) -> begin
u1
end
| FStar_Syntax_Syntax.Meta_desugared (uu____866) -> begin
u1
end
| FStar_Syntax_Syntax.Meta_named (uu____867) -> begin
u1
end))
end))))
and free_names_and_uvars : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  free_vars_and_fvars = (fun t use_cache -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let uu____874 = (FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars)
in (match (uu____874) with
| FStar_Pervasives_Native.Some (n1) when (

let uu____901 = (should_invalidate_cache n1 use_cache)
in (not (uu____901))) -> begin
(

let uu____903 = (FStar_Syntax_Syntax.new_fv_set ())
in ((n1), (uu____903)))
end
| uu____908 -> begin
((FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars FStar_Pervasives_Native.None);
(

let n1 = (free_names_and_uvs' t1 use_cache)
in ((FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars (FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.fst n1))));
n1;
));
)
end))))
and free_names_and_uvars_args : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)  ->  Prims.bool  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun args acc use_cache -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n1 uu____1012 -> (match (uu____1012) with
| (x, uu____1022) -> begin
(

let uu____1031 = (free_names_and_uvars x use_cache)
in (union n1 uu____1031))
end)) acc)))
and free_names_and_uvars_binders : FStar_Syntax_Syntax.binders  ->  free_vars_and_fvars  ->  Prims.bool  ->  free_vars_and_fvars = (fun bs acc use_cache -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n1 uu____1056 -> (match (uu____1056) with
| (x, uu____1064) -> begin
(

let uu____1069 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n1 uu____1069))
end)) acc)))
and free_names_and_uvars_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  free_vars_and_fvars = (fun c use_cache -> (

let uu____1075 = (FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars)
in (match (uu____1075) with
| FStar_Pervasives_Native.Some (n1) -> begin
(

let uu____1102 = (should_invalidate_cache n1 use_cache)
in (match (uu____1102) with
| true -> begin
((FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars FStar_Pervasives_Native.None);
(free_names_and_uvars_comp c use_cache);
)
end
| uu____1129 -> begin
(

let uu____1131 = (FStar_Syntax_Syntax.new_fv_set ())
in ((n1), (uu____1131)))
end))
end
| uu____1136 -> begin
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

let uu____1174 = (free_univs u)
in (

let uu____1175 = (free_names_and_uvars t use_cache)
in (union uu____1174 uu____1175)))
end
| FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.Some (u)) -> begin
(

let uu____1184 = (free_univs u)
in (

let uu____1185 = (free_names_and_uvars t use_cache)
in (union uu____1184 uu____1185)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let us = (

let uu____1194 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ use_cache)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args uu____1194 use_cache))
in (FStar_List.fold_left (fun us1 u -> (

let uu____1206 = (free_univs u)
in (union us1 uu____1206))) us ct.FStar_Syntax_Syntax.comp_univs))
end)
in ((FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars (FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.fst n1))));
n1;
))
end)))
and should_invalidate_cache : FStar_Syntax_Syntax.free_vars  ->  Prims.bool  ->  Prims.bool = (fun n1 use_cache -> ((not (use_cache)) || ((FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars (FStar_Util.for_some (fun u -> (

let uu____1243 = (FStar_Syntax_Unionfind.find u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____1243) with
| FStar_Pervasives_Native.Some (uu____1247) -> begin
true
end
| uu____1249 -> begin
false
end))))) || (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs (FStar_Util.for_some (fun u -> (

let uu____1260 = (FStar_Syntax_Unionfind.univ_find u)
in (match (uu____1260) with
| FStar_Pervasives_Native.Some (uu____1264) -> begin
true
end
| FStar_Pervasives_Native.None -> begin
false
end))))))))


let compare_uv : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.ctx_uvar  ->  Prims.int = (fun uv1 uv2 -> (

let uu____1279 = (FStar_Syntax_Unionfind.uvar_id uv1.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____1281 = (FStar_Syntax_Unionfind.uvar_id uv2.FStar_Syntax_Syntax.ctx_uvar_head)
in (uu____1279 - uu____1281))))


let new_uv_set : unit  ->  FStar_Syntax_Syntax.uvars = (fun uu____1288 -> (FStar_Util.new_set compare_uv))


let compare_universe_uvar : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.int = (fun x y -> (

let uu____1301 = (FStar_Syntax_Unionfind.univ_uvar_id x)
in (

let uu____1303 = (FStar_Syntax_Unionfind.univ_uvar_id y)
in (uu____1301 - uu____1303))))


let new_universe_uvar_set : unit  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun uu____1312 -> (FStar_Util.new_set compare_universe_uvar))


let empty : FStar_Syntax_Syntax.bv FStar_Util.set = (FStar_Util.new_set FStar_Syntax_Syntax.order_bv)


let names : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun t -> (

let uu____1326 = (

let uu____1329 = (

let uu____1330 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1330))
in uu____1329.FStar_Syntax_Syntax.free_names)
in (FStar_Util.as_set uu____1326 FStar_Syntax_Syntax.order_bv)))


let uvars : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.ctx_uvar FStar_Util.set = (fun t -> (

let uu____1348 = (

let uu____1351 = (

let uu____1352 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1352))
in uu____1351.FStar_Syntax_Syntax.free_uvars)
in (FStar_Util.as_set uu____1348 compare_uv)))


let univs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun t -> (

let uu____1370 = (

let uu____1373 = (

let uu____1374 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1374))
in uu____1373.FStar_Syntax_Syntax.free_univs)
in (FStar_Util.as_set uu____1370 compare_universe_uvar)))


let univnames : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun t -> (

let uu____1392 = (

let uu____1395 = (

let uu____1396 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1396))
in uu____1395.FStar_Syntax_Syntax.free_univ_names)
in (FStar_Util.as_set uu____1392 FStar_Syntax_Syntax.order_univ_name)))


let univnames_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun c -> (

let uu____1414 = (

let uu____1417 = (

let uu____1418 = (free_names_and_uvars_comp c true)
in (FStar_Pervasives_Native.fst uu____1418))
in uu____1417.FStar_Syntax_Syntax.free_univ_names)
in (FStar_Util.as_set uu____1414 FStar_Syntax_Syntax.order_univ_name)))


let fvars : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident FStar_Util.set = (fun t -> (

let uu____1436 = (free_names_and_uvars t false)
in (FStar_Pervasives_Native.snd uu____1436)))


let names_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun bs -> (

let uu____1454 = (

let uu____1457 = (

let uu____1458 = (free_names_and_uvars_binders bs no_free_vars true)
in (FStar_Pervasives_Native.fst uu____1458))
in uu____1457.FStar_Syntax_Syntax.free_names)
in (FStar_Util.as_set uu____1454 FStar_Syntax_Syntax.order_bv)))




