
open Prims
open FStar_Pervasives

type free_vars_and_fvars =
(FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)


let new_uv_set : Prims.unit  ->  FStar_Syntax_Syntax.uvars = (fun uu____10 -> (FStar_Util.new_set (fun uu____25 uu____26 -> (match (((uu____25), (uu____26))) with
| ((x, uu____52), (y, uu____54)) -> begin
(

let uu____75 = (FStar_Syntax_Unionfind.uvar_id x)
in (

let uu____76 = (FStar_Syntax_Unionfind.uvar_id y)
in (uu____75 - uu____76)))
end)) (fun uu____80 -> (match (uu____80) with
| (x, uu____88) -> begin
(FStar_Syntax_Unionfind.uvar_id x)
end))))


let new_universe_uvar_set : Prims.unit  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun uu____98 -> (FStar_Util.new_set (fun x y -> (

let uu____107 = (FStar_Syntax_Unionfind.univ_uvar_id x)
in (

let uu____108 = (FStar_Syntax_Unionfind.univ_uvar_id y)
in (uu____107 - uu____108)))) (fun x -> (FStar_Syntax_Unionfind.univ_uvar_id x))))


let no_uvs : FStar_Syntax_Syntax.uvars = (new_uv_set ())


let no_universe_uvars : FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (new_universe_uvar_set ())


let no_free_vars : (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (

let uu____119 = (FStar_Syntax_Syntax.new_fv_set ())
in (({FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = no_uvs; FStar_Syntax_Syntax.free_univs = no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names}), (uu____119)))


let singleton_fvar : FStar_Syntax_Syntax.fv  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun fv -> (

let uu____134 = (

let uu____137 = (FStar_Syntax_Syntax.new_fv_set ())
in (FStar_Util.set_add fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v uu____137))
in (({FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = no_uvs; FStar_Syntax_Syntax.free_univs = no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names}), (uu____134))))


let singleton_bv : FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (

let uu____152 = (

let uu____153 = (

let uu____156 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Util.set_add x uu____156))
in {FStar_Syntax_Syntax.free_names = uu____153; FStar_Syntax_Syntax.free_uvars = no_uvs; FStar_Syntax_Syntax.free_univs = no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names})
in (

let uu____159 = (FStar_Syntax_Syntax.new_fv_set ())
in ((uu____152), (uu____159)))))


let singleton_uv : ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (

let uu____206 = (

let uu____207 = (

let uu____226 = (new_uv_set ())
in (FStar_Util.set_add x uu____226))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = uu____207; FStar_Syntax_Syntax.free_univs = no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names})
in (

let uu____261 = (FStar_Syntax_Syntax.new_fv_set ())
in ((uu____206), (uu____261)))))


let singleton_univ : FStar_Syntax_Syntax.universe_uvar  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (

let uu____276 = (

let uu____277 = (

let uu____280 = (new_universe_uvar_set ())
in (FStar_Util.set_add x uu____280))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = no_uvs; FStar_Syntax_Syntax.free_univs = uu____277; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names})
in (

let uu____283 = (FStar_Syntax_Syntax.new_fv_set ())
in ((uu____276), (uu____283)))))


let singleton_univ_name : FStar_Syntax_Syntax.univ_name  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (

let uu____298 = (

let uu____299 = (

let uu____302 = (FStar_Syntax_Syntax.new_universe_names_fifo_set ())
in (FStar_Util.fifo_set_add x uu____302))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = no_uvs; FStar_Syntax_Syntax.free_univs = no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = uu____299})
in (

let uu____309 = (FStar_Syntax_Syntax.new_fv_set ())
in ((uu____298), (uu____309)))))


let union : 'Auu____320 . (FStar_Syntax_Syntax.free_vars * 'Auu____320 FStar_Util.set)  ->  (FStar_Syntax_Syntax.free_vars * 'Auu____320 FStar_Util.set)  ->  (FStar_Syntax_Syntax.free_vars * 'Auu____320 FStar_Util.set) = (fun f1 f2 -> (

let uu____359 = (

let uu____360 = (FStar_Util.set_union (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_names (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_names)
in (

let uu____367 = (FStar_Util.set_union (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_uvars (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_uvars)
in (

let uu____406 = (FStar_Util.set_union (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univs (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univs)
in (

let uu____413 = (FStar_Util.fifo_set_union (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univ_names (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univ_names)
in {FStar_Syntax_Syntax.free_names = uu____360; FStar_Syntax_Syntax.free_uvars = uu____367; FStar_Syntax_Syntax.free_univs = uu____406; FStar_Syntax_Syntax.free_univ_names = uu____413}))))
in (

let uu____422 = (FStar_Util.set_union (FStar_Pervasives_Native.snd f1) (FStar_Pervasives_Native.snd f2))
in ((uu____359), (uu____422)))))


let rec free_univs : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun u -> (

let uu____441 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____441) with
| FStar_Syntax_Syntax.U_zero -> begin
no_free_vars
end
| FStar_Syntax_Syntax.U_bvar (uu____448) -> begin
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

let uu____471 = (free_univs x)
in (union out uu____471))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(singleton_univ u1)
end)))


let rec free_names_and_uvs' : FStar_Syntax_Syntax.term  ->  Prims.bool  ->  free_vars_and_fvars = (fun tm use_cache -> (

let aux_binders = (fun bs from_body -> (

let from_binders = (FStar_All.pipe_right bs (FStar_List.fold_left (fun n1 uu____631 -> (match (uu____631) with
| (x, uu____649) -> begin
(

let uu____650 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n1 uu____650))
end)) no_free_vars))
in (union from_binders from_body)))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____658) -> begin
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
| FStar_Syntax_Syntax.Tm_bvar (uu____723) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(singleton_fvar fv)
end
| FStar_Syntax_Syntax.Tm_constant (uu____725) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let f = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun out u -> (

let uu____756 = (free_univs u)
in (union out uu____756))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____765) -> begin
(

let uu____786 = (free_names_and_uvars t1 use_cache)
in (aux_binders bs uu____786))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____811 = (free_names_and_uvars_comp c use_cache)
in (aux_binders bs uu____811))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t1) -> begin
(

let uu____824 = (free_names_and_uvars t1 use_cache)
in (aux_binders ((((bv), (FStar_Pervasives_Native.None)))::[]) uu____824))
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
(

let uu____867 = (free_names_and_uvars t1 use_cache)
in (free_names_and_uvars_args args uu____867 use_cache))
end
| FStar_Syntax_Syntax.Tm_match (t1, pats) -> begin
(

let uu____912 = (

let uu____937 = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun n1 uu____972 -> (match (uu____972) with
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

let uu____1046 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right uu____1046 (FStar_List.fold_left (fun n3 x -> (

let uu____1074 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n3 uu____1074))) n1)))
in (

let uu____1081 = (union n11 n2)
in (union n3 uu____1081)))))
end)) uu____937))
in (FStar_All.pipe_right pats uu____912))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____1112) -> begin
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

let uu____1218 = (union u1 u2)
in (

let uu____1225 = (free_names_and_uvars tac use_cache)
in (union uu____1218 uu____1225)))
end)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t1) -> begin
(

let uu____1250 = (

let uu____1261 = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun n1 lb -> (

let uu____1285 = (

let uu____1292 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp use_cache)
in (

let uu____1299 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef use_cache)
in (union uu____1292 uu____1299)))
in (union n1 uu____1285))) uu____1261))
in (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____1250))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(

let uu____1332 = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_right (fun a acc -> (free_names_and_uvars_args a acc use_cache)) args uu____1332))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_monadic (uu____1372, t')) -> begin
(

let uu____1382 = (free_names_and_uvars t1 use_cache)
in (

let uu____1389 = (free_names_and_uvars t' use_cache)
in (union uu____1382 uu____1389)))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____1397) -> begin
(free_names_and_uvars t1 use_cache)
end))))
and free_names_and_uvars : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun t use_cache -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let uu____1407 = (FStar_ST.read t1.FStar_Syntax_Syntax.vars)
in (match (uu____1407) with
| FStar_Pervasives_Native.Some (n1) when (

let uu____1419 = (should_invalidate_cache n1 use_cache)
in (not (uu____1419))) -> begin
(

let uu____1420 = (FStar_Syntax_Syntax.new_fv_set ())
in ((n1), (uu____1420)))
end
| uu____1425 -> begin
((FStar_ST.write t1.FStar_Syntax_Syntax.vars FStar_Pervasives_Native.None);
(

let n1 = (free_names_and_uvs' t1 use_cache)
in ((FStar_ST.write t1.FStar_Syntax_Syntax.vars (FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.fst n1))));
n1;
));
)
end))))
and free_names_and_uvars_args : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)  ->  Prims.bool  ->  free_vars_and_fvars = (fun args acc use_cache -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n1 uu____1486 -> (match (uu____1486) with
| (x, uu____1506) -> begin
(

let uu____1511 = (free_names_and_uvars x use_cache)
in (union n1 uu____1511))
end)) acc)))
and free_names_and_uvars_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)  ->  Prims.bool  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun bs acc use_cache -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n1 uu____1549 -> (match (uu____1549) with
| (x, uu____1567) -> begin
(

let uu____1568 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n1 uu____1568))
end)) acc)))
and free_names_and_uvars_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun c use_cache -> (

let uu____1579 = (FStar_ST.read c.FStar_Syntax_Syntax.vars)
in (match (uu____1579) with
| FStar_Pervasives_Native.Some (n1) -> begin
(

let uu____1591 = (should_invalidate_cache n1 use_cache)
in (match (uu____1591) with
| true -> begin
((FStar_ST.write c.FStar_Syntax_Syntax.vars FStar_Pervasives_Native.None);
(free_names_and_uvars_comp c use_cache);
)
end
| uu____1601 -> begin
(

let uu____1602 = (FStar_Syntax_Syntax.new_fv_set ())
in ((n1), (uu____1602)))
end))
end
| uu____1607 -> begin
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

let uu____1645 = (free_univs u)
in (

let uu____1652 = (free_names_and_uvars t use_cache)
in (union uu____1645 uu____1652)))
end
| FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.Some (u)) -> begin
(

let uu____1667 = (free_univs u)
in (

let uu____1674 = (free_names_and_uvars t use_cache)
in (union uu____1667 uu____1674)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let us = (

let uu____1683 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ use_cache)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args uu____1683 use_cache))
in (FStar_List.fold_left (fun us1 u -> (

let uu____1707 = (free_univs u)
in (union us1 uu____1707))) us ct.FStar_Syntax_Syntax.comp_univs))
end)
in ((FStar_ST.write c.FStar_Syntax_Syntax.vars (FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.fst n1))));
n1;
))
end)))
and should_invalidate_cache : FStar_Syntax_Syntax.free_vars  ->  Prims.bool  ->  Prims.bool = (fun n1 use_cache -> ((not (use_cache)) || ((

let uu____1723 = (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars FStar_Util.set_elements)
in (FStar_All.pipe_right uu____1723 (FStar_Util.for_some (fun uu____1823 -> (match (uu____1823) with
| (u, uu____1831) -> begin
(

let uu____1836 = (FStar_Syntax_Unionfind.find u)
in (match (uu____1836) with
| FStar_Pervasives_Native.Some (uu____1839) -> begin
true
end
| uu____1840 -> begin
false
end))
end))))) || (

let uu____1844 = (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs FStar_Util.set_elements)
in (FStar_All.pipe_right uu____1844 (FStar_Util.for_some (fun u -> (

let uu____1857 = (FStar_Syntax_Unionfind.univ_find u)
in (match (uu____1857) with
| FStar_Pervasives_Native.Some (uu____1860) -> begin
true
end
| FStar_Pervasives_Native.None -> begin
false
end)))))))))


let names : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun t -> (

let uu____1867 = (

let uu____1868 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1868))
in uu____1867.FStar_Syntax_Syntax.free_names))


let uvars : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set = (fun t -> (

let uu____1887 = (

let uu____1888 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1888))
in uu____1887.FStar_Syntax_Syntax.free_uvars))


let univs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun t -> (

let uu____1903 = (

let uu____1904 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1904))
in uu____1903.FStar_Syntax_Syntax.free_univs))


let univnames : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun t -> (

let uu____1919 = (

let uu____1920 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1920))
in uu____1919.FStar_Syntax_Syntax.free_univ_names))


let fvars : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident FStar_Util.set = (fun t -> (

let uu____1935 = (free_names_and_uvars t false)
in (FStar_Pervasives_Native.snd uu____1935)))


let names_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun bs -> (

let uu____1950 = (

let uu____1951 = (free_names_and_uvars_binders bs no_free_vars true)
in (FStar_Pervasives_Native.fst uu____1951))
in uu____1950.FStar_Syntax_Syntax.free_names))




