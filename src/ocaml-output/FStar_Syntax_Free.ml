
open Prims

type free_vars_and_fvars =
(FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)


let no_free_vars : (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (

let uu____7 = (FStar_Syntax_Syntax.new_fv_set ())
in (({FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names}), (uu____7)))


let singleton_fvar : FStar_Syntax_Syntax.fv  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun fv -> (

let uu____18 = (

let uu____20 = (FStar_Syntax_Syntax.new_fv_set ())
in (FStar_Util.set_add fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v uu____20))
in (({FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names}), (uu____18))))


let singleton_bv : FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (

let uu____35 = (

let uu____36 = (

let uu____38 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Util.set_add x uu____38))
in {FStar_Syntax_Syntax.free_names = uu____36; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names})
in (

let uu____42 = (FStar_Syntax_Syntax.new_fv_set ())
in ((uu____35), (uu____42)))))


let singleton_uv : ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (

let uu____67 = (

let uu____68 = (

let uu____78 = (FStar_Syntax_Syntax.new_uv_set ())
in (FStar_Util.set_add x uu____78))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = uu____68; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names})
in (

let uu____98 = (FStar_Syntax_Syntax.new_fv_set ())
in ((uu____67), (uu____98)))))


let singleton_univ : FStar_Syntax_Syntax.universe_uvar  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (

let uu____107 = (

let uu____108 = (

let uu____110 = (FStar_Syntax_Syntax.new_universe_uvar_set ())
in (FStar_Util.set_add x uu____110))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = uu____108; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names})
in (

let uu____114 = (FStar_Syntax_Syntax.new_fv_set ())
in ((uu____107), (uu____114)))))


let singleton_univ_name : FStar_Syntax_Syntax.univ_name  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (

let uu____123 = (

let uu____124 = (

let uu____126 = (FStar_Syntax_Syntax.new_universe_names_fifo_set ())
in (FStar_Util.fifo_set_add x uu____126))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = uu____124})
in (

let uu____134 = (FStar_Syntax_Syntax.new_fv_set ())
in ((uu____123), (uu____134)))))


let union = (fun f1 f2 -> (

let uu____164 = (

let uu____165 = (FStar_Util.set_union (Prims.fst f1).FStar_Syntax_Syntax.free_names (Prims.fst f2).FStar_Syntax_Syntax.free_names)
in (

let uu____169 = (FStar_Util.set_union (Prims.fst f1).FStar_Syntax_Syntax.free_uvars (Prims.fst f2).FStar_Syntax_Syntax.free_uvars)
in (

let uu____189 = (FStar_Util.set_union (Prims.fst f1).FStar_Syntax_Syntax.free_univs (Prims.fst f2).FStar_Syntax_Syntax.free_univs)
in (

let uu____193 = (FStar_Util.fifo_set_union (Prims.fst f1).FStar_Syntax_Syntax.free_univ_names (Prims.fst f2).FStar_Syntax_Syntax.free_univ_names)
in {FStar_Syntax_Syntax.free_names = uu____165; FStar_Syntax_Syntax.free_uvars = uu____169; FStar_Syntax_Syntax.free_univs = uu____189; FStar_Syntax_Syntax.free_univ_names = uu____193}))))
in (

let uu____204 = (FStar_Util.set_union (Prims.snd f1) (Prims.snd f2))
in ((uu____164), (uu____204)))))


let rec free_univs : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun u -> (

let uu____215 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____215) with
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_bvar (_)) | (FStar_Syntax_Syntax.U_unknown) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.U_name (uname) -> begin
(singleton_univ_name uname)
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(free_univs u)
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_List.fold_left (fun out x -> (

let uu____232 = (free_univs x)
in (union out uu____232))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u) -> begin
(singleton_univ u)
end)))


let rec free_names_and_uvs' : FStar_Syntax_Syntax.term  ->  Prims.bool  ->  free_vars_and_fvars = (fun tm use_cache -> (

let aux_binders = (fun bs from_body -> (

let from_binders = (FStar_All.pipe_right bs (FStar_List.fold_left (fun n uu____342 -> (match (uu____342) with
| (x, uu____352) -> begin
(

let uu____353 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n uu____353))
end)) no_free_vars))
in (union from_binders from_body)))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____358) -> begin
(failwith "Impossible")
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
| FStar_Syntax_Syntax.Tm_bvar (uu____401) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(singleton_fvar fv)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let f = (free_names_and_uvars t use_cache)
in (FStar_List.fold_left (fun out u -> (

let uu____422 = (free_univs u)
in (union out uu____422))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____428) -> begin
(

let uu____451 = (free_names_and_uvars t use_cache)
in (aux_binders bs uu____451))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____467 = (free_names_and_uvars_comp c use_cache)
in (aux_binders bs uu____467))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(

let uu____477 = (free_names_and_uvars t use_cache)
in (aux_binders ((((bv), (None)))::[]) uu____477))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____504 = (free_names_and_uvars t use_cache)
in (free_names_and_uvars_args args uu____504 use_cache))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(

let uu____536 = (

let uu____553 = (free_names_and_uvars t use_cache)
in (FStar_List.fold_left (fun n uu____569 -> (match (uu____569) with
| (p, wopt, t) -> begin
(

let n1 = (match (wopt) with
| None -> begin
no_free_vars
end
| Some (w) -> begin
(free_names_and_uvars w use_cache)
end)
in (

let n2 = (free_names_and_uvars t use_cache)
in (

let n = (

let uu____619 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right uu____619 (FStar_List.fold_left (fun n x -> (

let uu____633 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n uu____633))) n)))
in (

let uu____637 = (union n1 n2)
in (union n uu____637)))))
end)) uu____553))
in (FStar_All.pipe_right pats uu____536))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), uu____657) -> begin
(

let uu____676 = (free_names_and_uvars t1 use_cache)
in (

let uu____680 = (free_names_and_uvars t2 use_cache)
in (union uu____676 uu____680)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), uu____686) -> begin
(

let uu____705 = (free_names_and_uvars t1 use_cache)
in (

let uu____709 = (free_names_and_uvars_comp c use_cache)
in (union uu____705 uu____709)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(

let uu____725 = (

let uu____732 = (free_names_and_uvars t use_cache)
in (FStar_List.fold_left (fun n lb -> (

let uu____744 = (

let uu____748 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp use_cache)
in (

let uu____752 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef use_cache)
in (union uu____748 uu____752)))
in (union n uu____744))) uu____732))
in (FStar_All.pipe_right (Prims.snd lbs) uu____725))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(

let uu____773 = (free_names_and_uvars t use_cache)
in (FStar_List.fold_right (fun a acc -> (free_names_and_uvars_args a acc use_cache)) args uu____773))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____796, t')) -> begin
(

let uu____806 = (free_names_and_uvars t use_cache)
in (

let uu____810 = (free_names_and_uvars t' use_cache)
in (union uu____806 uu____810)))
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____815) -> begin
(free_names_and_uvars t use_cache)
end))))
and free_names_and_uvars : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun t use_cache -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let uu____825 = (FStar_ST.read t.FStar_Syntax_Syntax.vars)
in (match (uu____825) with
| Some (n) when (

let uu____834 = (should_invalidate_cache n use_cache)
in (not (uu____834))) -> begin
(

let uu____835 = (FStar_Syntax_Syntax.new_fv_set ())
in ((n), (uu____835)))
end
| uu____838 -> begin
((FStar_ST.write t.FStar_Syntax_Syntax.vars None);
(

let n = (free_names_and_uvs' t use_cache)
in ((FStar_ST.write t.FStar_Syntax_Syntax.vars (Some ((Prims.fst n))));
n;
));
)
end))))
and free_names_and_uvars_args : ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)  ->  Prims.bool  ->  free_vars_and_fvars = (fun args acc use_cache -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n uu____877 -> (match (uu____877) with
| (x, uu____889) -> begin
(

let uu____894 = (free_names_and_uvars x use_cache)
in (union n uu____894))
end)) acc)))
and free_names_and_uvars_binders = (fun bs acc use_cache -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n uu____919 -> (match (uu____919) with
| (x, uu____929) -> begin
(

let uu____930 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n uu____930))
end)) acc)))
and free_names_and_uvars_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun c use_cache -> (

let uu____938 = (FStar_ST.read c.FStar_Syntax_Syntax.vars)
in (match (uu____938) with
| Some (n) -> begin
(

let uu____947 = (should_invalidate_cache n use_cache)
in (match (uu____947) with
| true -> begin
((FStar_ST.write c.FStar_Syntax_Syntax.vars None);
(free_names_and_uvars_comp c use_cache);
)
end
| uu____955 -> begin
(

let uu____956 = (FStar_Syntax_Syntax.new_fv_set ())
in ((n), (uu____956)))
end))
end
| uu____959 -> begin
(

let n = (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (t, None)) | (FStar_Syntax_Syntax.Total (t, None)) -> begin
(free_names_and_uvars t use_cache)
end
| (FStar_Syntax_Syntax.GTotal (t, Some (u))) | (FStar_Syntax_Syntax.Total (t, Some (u))) -> begin
(

let uu____991 = (free_univs u)
in (

let uu____995 = (free_names_and_uvars t use_cache)
in (union uu____991 uu____995)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let us = (

let uu____1001 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ use_cache)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args uu____1001 use_cache))
in (FStar_List.fold_left (fun us u -> (

let uu____1013 = (free_univs u)
in (union us uu____1013))) us ct.FStar_Syntax_Syntax.comp_univs))
end)
in ((FStar_ST.write c.FStar_Syntax_Syntax.vars (Some ((Prims.fst n))));
n;
))
end)))
and should_invalidate_cache : FStar_Syntax_Syntax.free_vars  ->  Prims.bool  ->  Prims.bool = (fun n use_cache -> ((not (use_cache)) || ((

let uu____1024 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_uvars FStar_Util.set_elements)
in (FStar_All.pipe_right uu____1024 (FStar_Util.for_some (fun uu____1077 -> (match (uu____1077) with
| (u, uu____1087) -> begin
(

let uu____1100 = (FStar_Unionfind.find u)
in (match (uu____1100) with
| FStar_Syntax_Syntax.Fixed (uu____1107) -> begin
true
end
| uu____1112 -> begin
false
end))
end))))) || (

let uu____1116 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_univs FStar_Util.set_elements)
in (FStar_All.pipe_right uu____1116 (FStar_Util.for_some (fun u -> (

let uu____1126 = (FStar_Unionfind.find u)
in (match (uu____1126) with
| Some (uu____1129) -> begin
true
end
| None -> begin
false
end)))))))))


let names : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun t -> (

let uu____1134 = (

let uu____1135 = (free_names_and_uvars t true)
in (Prims.fst uu____1135))
in uu____1134.FStar_Syntax_Syntax.free_names))


let uvars : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set = (fun t -> (

let uu____1146 = (

let uu____1147 = (free_names_and_uvars t true)
in (Prims.fst uu____1147))
in uu____1146.FStar_Syntax_Syntax.free_uvars))


let univs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun t -> (

let uu____1156 = (

let uu____1157 = (free_names_and_uvars t true)
in (Prims.fst uu____1157))
in uu____1156.FStar_Syntax_Syntax.free_univs))


let univnames : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun t -> (

let uu____1166 = (

let uu____1167 = (free_names_and_uvars t true)
in (Prims.fst uu____1167))
in uu____1166.FStar_Syntax_Syntax.free_univ_names))


let fvars : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident FStar_Util.set = (fun t -> (

let uu____1177 = (free_names_and_uvars t false)
in (Prims.snd uu____1177)))


let names_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun bs -> (

let uu____1186 = (

let uu____1187 = (free_names_and_uvars_binders bs no_free_vars true)
in (Prims.fst uu____1187))
in uu____1186.FStar_Syntax_Syntax.free_names))




