
open Prims
open FStar_Pervasives

type free_vars_and_fvars =
(FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)


let no_free_vars : (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (

let uu____13 = (FStar_Syntax_Syntax.new_fv_set ())
in (({FStar_Syntax_Syntax.free_names = []; FStar_Syntax_Syntax.free_uvars = []; FStar_Syntax_Syntax.free_univs = []; FStar_Syntax_Syntax.free_univ_names = []}), (uu____13)))


let singleton_fvar : FStar_Syntax_Syntax.fv  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun fv -> (

let uu____29 = (

let uu____32 = (FStar_Syntax_Syntax.new_fv_set ())
in (FStar_Util.set_add fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v uu____32))
in (((FStar_Pervasives_Native.fst no_free_vars)), (uu____29))))


let singleton_bv : FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___25_53 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = (x)::[]; FStar_Syntax_Syntax.free_uvars = uu___25_53.FStar_Syntax_Syntax.free_uvars; FStar_Syntax_Syntax.free_univs = uu___25_53.FStar_Syntax_Syntax.free_univs; FStar_Syntax_Syntax.free_univ_names = uu___25_53.FStar_Syntax_Syntax.free_univ_names})), ((FStar_Pervasives_Native.snd no_free_vars))))


let singleton_uv : FStar_Syntax_Syntax.ctx_uvar  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___26_72 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = uu___26_72.FStar_Syntax_Syntax.free_names; FStar_Syntax_Syntax.free_uvars = (x)::[]; FStar_Syntax_Syntax.free_univs = uu___26_72.FStar_Syntax_Syntax.free_univs; FStar_Syntax_Syntax.free_univ_names = uu___26_72.FStar_Syntax_Syntax.free_univ_names})), ((FStar_Pervasives_Native.snd no_free_vars))))


let singleton_univ : FStar_Syntax_Syntax.universe_uvar  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___27_91 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = uu___27_91.FStar_Syntax_Syntax.free_names; FStar_Syntax_Syntax.free_uvars = uu___27_91.FStar_Syntax_Syntax.free_uvars; FStar_Syntax_Syntax.free_univs = (x)::[]; FStar_Syntax_Syntax.free_univ_names = uu___27_91.FStar_Syntax_Syntax.free_univ_names})), ((FStar_Pervasives_Native.snd no_free_vars))))


let singleton_univ_name : FStar_Syntax_Syntax.univ_name  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (((

let uu___28_110 = (FStar_Pervasives_Native.fst no_free_vars)
in {FStar_Syntax_Syntax.free_names = uu___28_110.FStar_Syntax_Syntax.free_names; FStar_Syntax_Syntax.free_uvars = uu___28_110.FStar_Syntax_Syntax.free_uvars; FStar_Syntax_Syntax.free_univs = uu___28_110.FStar_Syntax_Syntax.free_univs; FStar_Syntax_Syntax.free_univ_names = (x)::[]})), ((FStar_Pervasives_Native.snd no_free_vars))))


let union : free_vars_and_fvars  ->  free_vars_and_fvars  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun f1 f2 -> (

let uu____131 = (FStar_Util.set_union (FStar_Pervasives_Native.snd f1) (FStar_Pervasives_Native.snd f2))
in (({FStar_Syntax_Syntax.free_names = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_names (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_names); FStar_Syntax_Syntax.free_uvars = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_uvars (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_uvars); FStar_Syntax_Syntax.free_univs = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univs (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univs); FStar_Syntax_Syntax.free_univ_names = (FStar_List.append (FStar_Pervasives_Native.fst f1).FStar_Syntax_Syntax.free_univ_names (FStar_Pervasives_Native.fst f2).FStar_Syntax_Syntax.free_univ_names)}), (uu____131))))


let rec free_univs : FStar_Syntax_Syntax.universe  ->  free_vars_and_fvars = (fun u -> (

let uu____161 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____161) with
| FStar_Syntax_Syntax.U_zero -> begin
no_free_vars
end
| FStar_Syntax_Syntax.U_bvar (uu____162) -> begin
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

let uu____173 = (free_univs x)
in (union out uu____173))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(singleton_univ u1)
end)))


let rec free_names_and_uvs' : FStar_Syntax_Syntax.term  ->  Prims.bool  ->  free_vars_and_fvars = (fun tm use_cache -> (

let aux_binders = (fun bs from_body -> (

let from_binders = (FStar_All.pipe_right bs (FStar_List.fold_left (fun n1 uu____299 -> (match (uu____299) with
| (x, uu____305) -> begin
(

let uu____306 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n1 uu____306))
end)) no_free_vars))
in (union from_binders from_body)))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____308) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(singleton_bv x)
end
| FStar_Syntax_Syntax.Tm_uvar (uv) -> begin
(singleton_uv uv)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(free_univs u)
end
| FStar_Syntax_Syntax.Tm_bvar (uu____336) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(singleton_fvar fv)
end
| FStar_Syntax_Syntax.Tm_constant (uu____338) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_lazy (uu____339) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(

let f = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun out u -> (

let uu____352 = (free_univs u)
in (union out uu____352))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____355) -> begin
(

let uu____376 = (free_names_and_uvars t1 use_cache)
in (aux_binders bs uu____376))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____395 = (free_names_and_uvars_comp c use_cache)
in (aux_binders bs uu____395))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t1) -> begin
(

let uu____402 = (free_names_and_uvars t1 use_cache)
in (aux_binders ((((bv), (FStar_Pervasives_Native.None)))::[]) uu____402))
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
(

let uu____435 = (free_names_and_uvars t1 use_cache)
in (free_names_and_uvars_args args uu____435 use_cache))
end
| FStar_Syntax_Syntax.Tm_match (t1, pats) -> begin
(

let uu____480 = (

let uu____501 = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun n1 uu____524 -> (match (uu____524) with
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

let uu____574 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right uu____574 (FStar_List.fold_left (fun n3 x -> (

let uu____584 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n3 uu____584))) n1)))
in (

let uu____585 = (union n11 n2)
in (union n3 uu____585)))))
end)) uu____501))
in (FStar_All.pipe_right pats uu____480))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____604) -> begin
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

let uu____692 = (union u1 u2)
in (

let uu____693 = (free_names_and_uvars tac use_cache)
in (union uu____692 uu____693)))
end)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t1) -> begin
(

let uu____712 = (

let uu____719 = (free_names_and_uvars t1 use_cache)
in (FStar_List.fold_left (fun n1 lb -> (

let uu____725 = (

let uu____726 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp use_cache)
in (

let uu____727 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef use_cache)
in (union uu____726 uu____727)))
in (union n1 uu____725))) uu____719))
in (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) uu____712))
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
| FStar_Syntax_Syntax.Meta_monadic (uu____788, t') -> begin
(

let uu____794 = (free_names_and_uvars t' use_cache)
in (union u1 uu____794))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____795, uu____796, t') -> begin
(

let uu____802 = (free_names_and_uvars t' use_cache)
in (union u1 uu____802))
end
| FStar_Syntax_Syntax.Meta_labeled (uu____803) -> begin
u1
end
| FStar_Syntax_Syntax.Meta_desugared (uu____810) -> begin
u1
end
| FStar_Syntax_Syntax.Meta_named (uu____811) -> begin
u1
end))
end))))
and free_names_and_uvars : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  free_vars_and_fvars = (fun t use_cache -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let uu____817 = (FStar_ST.op_Bang t1.FStar_Syntax_Syntax.vars)
in (match (uu____817) with
| FStar_Pervasives_Native.Some (n1) when (

let uu____848 = (should_invalidate_cache n1 use_cache)
in (not (uu____848))) -> begin
(

let uu____849 = (FStar_Syntax_Syntax.new_fv_set ())
in ((n1), (uu____849)))
end
| uu____854 -> begin
((FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars FStar_Pervasives_Native.None);
(

let n1 = (free_names_and_uvs' t1 use_cache)
in ((FStar_ST.op_Colon_Equals t1.FStar_Syntax_Syntax.vars (FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.fst n1))));
n1;
));
)
end))))
and free_names_and_uvars_args : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)  ->  Prims.bool  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun args acc use_cache -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n1 uu____959 -> (match (uu____959) with
| (x, uu____967) -> begin
(

let uu____972 = (free_names_and_uvars x use_cache)
in (union n1 uu____972))
end)) acc)))
and free_names_and_uvars_binders : FStar_Syntax_Syntax.binders  ->  free_vars_and_fvars  ->  Prims.bool  ->  free_vars_and_fvars = (fun bs acc use_cache -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n1 uu____992 -> (match (uu____992) with
| (x, uu____998) -> begin
(

let uu____999 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n1 uu____999))
end)) acc)))
and free_names_and_uvars_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  free_vars_and_fvars = (fun c use_cache -> (

let uu____1004 = (FStar_ST.op_Bang c.FStar_Syntax_Syntax.vars)
in (match (uu____1004) with
| FStar_Pervasives_Native.Some (n1) -> begin
(

let uu____1035 = (should_invalidate_cache n1 use_cache)
in (match (uu____1035) with
| true -> begin
((FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars FStar_Pervasives_Native.None);
(free_names_and_uvars_comp c use_cache);
)
end
| uu____1064 -> begin
(

let uu____1065 = (FStar_Syntax_Syntax.new_fv_set ())
in ((n1), (uu____1065)))
end))
end
| uu____1070 -> begin
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

let uu____1096 = (free_univs u)
in (

let uu____1097 = (free_names_and_uvars t use_cache)
in (union uu____1096 uu____1097)))
end
| FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.Some (u)) -> begin
(

let uu____1106 = (free_univs u)
in (

let uu____1107 = (free_names_and_uvars t use_cache)
in (union uu____1106 uu____1107)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let us = (

let uu____1116 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ use_cache)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args uu____1116 use_cache))
in (FStar_List.fold_left (fun us1 u -> (

let uu____1128 = (free_univs u)
in (union us1 uu____1128))) us ct.FStar_Syntax_Syntax.comp_univs))
end)
in ((FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars (FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.fst n1))));
n1;
))
end)))
and should_invalidate_cache : FStar_Syntax_Syntax.free_vars  ->  Prims.bool  ->  Prims.bool = (fun n1 use_cache -> ((not (use_cache)) || ((FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_uvars (FStar_Util.for_some (fun u -> (

let uu____1167 = (FStar_Syntax_Unionfind.find u.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____1167) with
| FStar_Pervasives_Native.Some (uu____1170) -> begin
true
end
| uu____1171 -> begin
false
end))))) || (FStar_All.pipe_right n1.FStar_Syntax_Syntax.free_univs (FStar_Util.for_some (fun u -> (

let uu____1180 = (FStar_Syntax_Unionfind.univ_find u)
in (match (uu____1180) with
| FStar_Pervasives_Native.Some (uu____1183) -> begin
true
end
| FStar_Pervasives_Native.None -> begin
false
end))))))))


let compare_uv : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.ctx_uvar  ->  Prims.int = (fun uv1 uv2 -> (

let uu____1194 = (FStar_Syntax_Unionfind.uvar_id uv1.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____1195 = (FStar_Syntax_Unionfind.uvar_id uv2.FStar_Syntax_Syntax.ctx_uvar_head)
in (uu____1194 - uu____1195))))


let new_uv_set : unit  ->  FStar_Syntax_Syntax.uvars = (fun uu____1200 -> (FStar_Util.new_set compare_uv))


let compare_universe_uvar : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.int = (fun x y -> (

let uu____1211 = (FStar_Syntax_Unionfind.univ_uvar_id x)
in (

let uu____1212 = (FStar_Syntax_Unionfind.univ_uvar_id y)
in (uu____1211 - uu____1212))))


let new_universe_uvar_set : unit  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun uu____1219 -> (FStar_Util.new_set compare_universe_uvar))


let empty : FStar_Syntax_Syntax.bv FStar_Util.set = (FStar_Util.new_set FStar_Syntax_Syntax.order_bv)


let names : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun t -> (

let uu____1231 = (

let uu____1234 = (

let uu____1235 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1235))
in uu____1234.FStar_Syntax_Syntax.free_names)
in (FStar_Util.as_set uu____1231 FStar_Syntax_Syntax.order_bv)))


let uvars : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.ctx_uvar FStar_Util.set = (fun t -> (

let uu____1251 = (

let uu____1254 = (

let uu____1255 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1255))
in uu____1254.FStar_Syntax_Syntax.free_uvars)
in (FStar_Util.as_set uu____1251 compare_uv)))


let univs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun t -> (

let uu____1271 = (

let uu____1274 = (

let uu____1275 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1275))
in uu____1274.FStar_Syntax_Syntax.free_univs)
in (FStar_Util.as_set uu____1271 compare_universe_uvar)))


let univnames : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun t -> (

let uu____1291 = (

let uu____1294 = (

let uu____1295 = (free_names_and_uvars t true)
in (FStar_Pervasives_Native.fst uu____1295))
in uu____1294.FStar_Syntax_Syntax.free_univ_names)
in (FStar_Util.as_set uu____1291 FStar_Syntax_Syntax.order_univ_name)))


let univnames_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun c -> (

let uu____1311 = (

let uu____1314 = (

let uu____1315 = (free_names_and_uvars_comp c true)
in (FStar_Pervasives_Native.fst uu____1315))
in uu____1314.FStar_Syntax_Syntax.free_univ_names)
in (FStar_Util.as_set uu____1311 FStar_Syntax_Syntax.order_univ_name)))


let fvars : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident FStar_Util.set = (fun t -> (

let uu____1331 = (free_names_and_uvars t false)
in (FStar_Pervasives_Native.snd uu____1331)))


let names_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun bs -> (

let uu____1347 = (

let uu____1350 = (

let uu____1351 = (free_names_and_uvars_binders bs no_free_vars true)
in (FStar_Pervasives_Native.fst uu____1351))
in uu____1350.FStar_Syntax_Syntax.free_names)
in (FStar_Util.as_set uu____1347 FStar_Syntax_Syntax.order_bv)))




