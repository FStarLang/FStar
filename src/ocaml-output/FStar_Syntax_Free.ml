
open Prims

let no_free_vars : FStar_Syntax_Syntax.free_vars = {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names}


let singleton_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (

let uu____6 = (

let uu____8 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Util.set_add x uu____8))
in {FStar_Syntax_Syntax.free_names = uu____6; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names}))


let singleton_uv : ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (

let uu____31 = (

let uu____41 = (FStar_Syntax_Syntax.new_uv_set ())
in (FStar_Util.set_add x uu____41))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = uu____31; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names}))


let singleton_univ : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (

let uu____64 = (

let uu____66 = (FStar_Syntax_Syntax.new_universe_uvar_set ())
in (FStar_Util.set_add x uu____66))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = uu____64; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names}))


let singleton_univ_name : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (

let uu____73 = (

let uu____75 = (FStar_Syntax_Syntax.new_universe_names_fifo_set ())
in (FStar_Util.fifo_set_add x uu____75))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = uu____73}))


let union : FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars = (fun f1 f2 -> (

let uu____89 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_names f2.FStar_Syntax_Syntax.free_names)
in (

let uu____91 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_uvars f2.FStar_Syntax_Syntax.free_uvars)
in (

let uu____109 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_univs f2.FStar_Syntax_Syntax.free_univs)
in (

let uu____111 = (FStar_Util.fifo_set_union f1.FStar_Syntax_Syntax.free_univ_names f2.FStar_Syntax_Syntax.free_univ_names)
in {FStar_Syntax_Syntax.free_names = uu____89; FStar_Syntax_Syntax.free_uvars = uu____91; FStar_Syntax_Syntax.free_univs = uu____109; FStar_Syntax_Syntax.free_univ_names = uu____111})))))


let rec free_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.free_vars = (fun u -> (

let uu____123 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____123) with
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

let uu____131 = (free_univs x)
in (union out uu____131))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u) -> begin
(singleton_univ u)
end)))


let rec free_names_and_uvs' : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.free_vars = (fun tm -> (

let aux_binders = (fun bs from_body -> (

let from_binders = (FStar_All.pipe_right bs (FStar_List.fold_left (fun n uu____190 -> (match (uu____190) with
| (x, uu____194) -> begin
(

let uu____195 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n uu____195))
end)) no_free_vars))
in (union from_binders from_body)))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____197) -> begin
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
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let f = (free_names_and_uvars t)
in (FStar_List.fold_left (fun out u -> (

let uu____252 = (free_univs u)
in (union out uu____252))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____255) -> begin
(

let uu____278 = (free_names_and_uvars t)
in (aux_binders bs uu____278))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____291 = (free_names_and_uvars_comp c)
in (aux_binders bs uu____291))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(

let uu____298 = (free_names_and_uvars t)
in (aux_binders ((((bv), (None)))::[]) uu____298))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____322 = (free_names_and_uvars t)
in (free_names_and_uvars_args args uu____322))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(

let uu____351 = (

let uu____365 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n uu____375 -> (match (uu____375) with
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

let n = (

let uu____407 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right uu____407 (FStar_List.fold_left (fun n x -> (

let uu____412 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n uu____412))) n)))
in (

let uu____413 = (union n1 n2)
in (union n uu____413)))))
end)) uu____365))
in (FStar_All.pipe_right pats uu____351))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), uu____427) -> begin
(

let uu____446 = (free_names_and_uvars t1)
in (

let uu____447 = (free_names_and_uvars t2)
in (union uu____446 uu____447)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), uu____450) -> begin
(

let uu____469 = (free_names_and_uvars t1)
in (

let uu____470 = (free_names_and_uvars_comp c)
in (union uu____469 uu____470)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(

let uu____483 = (

let uu____487 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n lb -> (

let uu____490 = (

let uu____491 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____492 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef)
in (union uu____491 uu____492)))
in (union n uu____490))) uu____487))
in (FStar_All.pipe_right (Prims.snd lbs) uu____483))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(

let uu____507 = (free_names_and_uvars t)
in (FStar_List.fold_right free_names_and_uvars_args args uu____507))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____514, t')) -> begin
(

let uu____524 = (free_names_and_uvars t)
in (

let uu____525 = (free_names_and_uvars t')
in (union uu____524 uu____525)))
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____527) -> begin
(free_names_and_uvars t)
end))))
and free_names_and_uvars : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.free_vars = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let uu____536 = (FStar_ST.read t.FStar_Syntax_Syntax.vars)
in (match (uu____536) with
| Some (n) when (

let uu____542 = (should_invalidate_cache n)
in (not (uu____542))) -> begin
n
end
| uu____543 -> begin
((FStar_ST.write t.FStar_Syntax_Syntax.vars None);
(

let n = (free_names_and_uvs' t)
in ((FStar_ST.write t.FStar_Syntax_Syntax.vars (Some (n)));
n;
));
)
end))))
and free_names_and_uvars_args : ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars = (fun args acc -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n uu____571 -> (match (uu____571) with
| (x, uu____577) -> begin
(

let uu____582 = (free_names_and_uvars x)
in (union n uu____582))
end)) acc)))
and free_names_and_uvars_binders = (fun bs acc -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n uu____594 -> (match (uu____594) with
| (x, uu____598) -> begin
(

let uu____599 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n uu____599))
end)) acc)))
and free_names_and_uvars_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.free_vars = (fun c -> (

let uu____603 = (FStar_ST.read c.FStar_Syntax_Syntax.vars)
in (match (uu____603) with
| Some (n) -> begin
(

let uu____609 = (should_invalidate_cache n)
in (match (uu____609) with
| true -> begin
((FStar_ST.write c.FStar_Syntax_Syntax.vars None);
(free_names_and_uvars_comp c);
)
end
| uu____614 -> begin
n
end))
end
| uu____615 -> begin
(

let n = (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (t, None)) | (FStar_Syntax_Syntax.Total (t, None)) -> begin
(free_names_and_uvars t)
end
| (FStar_Syntax_Syntax.GTotal (t, Some (u))) | (FStar_Syntax_Syntax.Total (t, Some (u))) -> begin
(

let uu____641 = (free_univs u)
in (

let uu____642 = (free_names_and_uvars t)
in (union uu____641 uu____642)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let us = (

let uu____645 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args uu____645))
in (FStar_List.fold_left (fun us u -> (

let uu____648 = (free_univs u)
in (union us uu____648))) us ct.FStar_Syntax_Syntax.comp_univs))
end)
in ((FStar_ST.write c.FStar_Syntax_Syntax.vars (Some (n)));
n;
))
end)))
and should_invalidate_cache : FStar_Syntax_Syntax.free_vars  ->  Prims.bool = (fun n -> ((

let uu____654 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_uvars FStar_Util.set_elements)
in (FStar_All.pipe_right uu____654 (FStar_Util.for_some (fun uu____707 -> (match (uu____707) with
| (u, uu____717) -> begin
(

let uu____730 = (FStar_Unionfind.find u)
in (match (uu____730) with
| FStar_Syntax_Syntax.Fixed (uu____737) -> begin
true
end
| uu____742 -> begin
false
end))
end))))) || (

let uu____746 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_univs FStar_Util.set_elements)
in (FStar_All.pipe_right uu____746 (FStar_Util.for_some (fun u -> (

let uu____756 = (FStar_Unionfind.find u)
in (match (uu____756) with
| Some (uu____759) -> begin
true
end
| None -> begin
false
end))))))))


let names : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun t -> (

let uu____764 = (free_names_and_uvars t)
in uu____764.FStar_Syntax_Syntax.free_names))


let uvars : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set = (fun t -> (

let uu____771 = (free_names_and_uvars t)
in uu____771.FStar_Syntax_Syntax.free_uvars))


let univs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun t -> (

let uu____776 = (free_names_and_uvars t)
in uu____776.FStar_Syntax_Syntax.free_univs))


let univnames : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun t -> (

let uu____781 = (free_names_and_uvars t)
in uu____781.FStar_Syntax_Syntax.free_univ_names))


let names_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun bs -> (

let uu____787 = (free_names_and_uvars_binders bs no_free_vars)
in uu____787.FStar_Syntax_Syntax.free_names))




