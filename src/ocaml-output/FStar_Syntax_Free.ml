
open Prims

let no_free_vars : FStar_Syntax_Syntax.free_vars = {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names}


let singleton_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _0_746 = (let _0_745 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Util.set_add x _0_745))
in {FStar_Syntax_Syntax.free_names = _0_746; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names}))


let singleton_uv : ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _0_748 = (let _0_747 = (FStar_Syntax_Syntax.new_uv_set ())
in (FStar_Util.set_add x _0_747))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = _0_748; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names}))


let singleton_univ : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _0_750 = (let _0_749 = (FStar_Syntax_Syntax.new_universe_uvar_set ())
in (FStar_Util.set_add x _0_749))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = _0_750; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names}))


let singleton_univ_name : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _0_752 = (let _0_751 = (FStar_Syntax_Syntax.new_universe_names_fifo_set ())
in (FStar_Util.fifo_set_add x _0_751))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = _0_752}))


let union : FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars = (fun f1 f2 -> (let _0_756 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_names f2.FStar_Syntax_Syntax.free_names)
in (let _0_755 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_uvars f2.FStar_Syntax_Syntax.free_uvars)
in (let _0_754 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_univs f2.FStar_Syntax_Syntax.free_univs)
in (let _0_753 = (FStar_Util.fifo_set_union f1.FStar_Syntax_Syntax.free_univ_names f2.FStar_Syntax_Syntax.free_univ_names)
in {FStar_Syntax_Syntax.free_names = _0_756; FStar_Syntax_Syntax.free_uvars = _0_755; FStar_Syntax_Syntax.free_univs = _0_754; FStar_Syntax_Syntax.free_univ_names = _0_753})))))


let rec free_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.free_vars = (fun u -> (

let uu____72 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____72) with
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
(FStar_List.fold_left (fun out x -> (let _0_757 = (free_univs x)
in (union out _0_757))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u) -> begin
(singleton_univ u)
end)))


let rec free_names_and_uvs' : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.free_vars = (fun tm -> (

let aux_binders = (fun bs from_body -> (

let from_binders = (FStar_All.pipe_right bs (FStar_List.fold_left (fun n uu____138 -> (match (uu____138) with
| (x, uu____142) -> begin
(let _0_758 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _0_758))
end)) no_free_vars))
in (union from_binders from_body)))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____144) -> begin
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
in (FStar_List.fold_left (fun out u -> (let _0_759 = (free_univs u)
in (union out _0_759))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____201) -> begin
(let _0_760 = (free_names_and_uvars t)
in (aux_binders bs _0_760))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _0_761 = (free_names_and_uvars_comp c)
in (aux_binders bs _0_761))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(let _0_762 = (free_names_and_uvars t)
in (aux_binders ((((bv), (None)))::[]) _0_762))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _0_763 = (free_names_and_uvars t)
in (free_names_and_uvars_args args _0_763))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(let _0_768 = (let _0_767 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n uu____313 -> (match (uu____313) with
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

let n = (let _0_765 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _0_765 (FStar_List.fold_left (fun n x -> (let _0_764 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _0_764))) n)))
in (let _0_766 = (union n1 n2)
in (union n _0_766)))))
end)) _0_767))
in (FStar_All.pipe_right pats _0_768))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), uu____350) -> begin
(let _0_770 = (free_names_and_uvars t1)
in (let _0_769 = (free_names_and_uvars t2)
in (union _0_770 _0_769)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), uu____371) -> begin
(let _0_772 = (free_names_and_uvars t1)
in (let _0_771 = (free_names_and_uvars_comp c)
in (union _0_772 _0_771)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(let _0_777 = (let _0_776 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n lb -> (let _0_775 = (let _0_774 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp)
in (let _0_773 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef)
in (union _0_774 _0_773)))
in (union n _0_775))) _0_776))
in (FStar_All.pipe_right (Prims.snd lbs) _0_777))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _0_778 = (free_names_and_uvars t)
in (FStar_List.fold_right free_names_and_uvars_args args _0_778))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____424, t')) -> begin
(let _0_780 = (free_names_and_uvars t)
in (let _0_779 = (free_names_and_uvars t')
in (union _0_780 _0_779)))
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____435) -> begin
(free_names_and_uvars t)
end))))
and free_names_and_uvars : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.free_vars = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let uu____444 = (FStar_ST.read t.FStar_Syntax_Syntax.vars)
in (match (uu____444) with
| Some (n) -> begin
(

let uu____450 = (should_invalidate_cache n)
in (match (uu____450) with
| true -> begin
((FStar_ST.write t.FStar_Syntax_Syntax.vars None);
(free_names_and_uvars t);
)
end
| uu____455 -> begin
n
end))
end
| uu____456 -> begin
(

let n = (free_names_and_uvs' t)
in ((FStar_ST.write t.FStar_Syntax_Syntax.vars (Some (n)));
n;
))
end))))
and free_names_and_uvars_args : ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars = (fun args acc -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n uu____480 -> (match (uu____480) with
| (x, uu____486) -> begin
(let _0_781 = (free_names_and_uvars x)
in (union n _0_781))
end)) acc)))
and free_names_and_uvars_binders = (fun bs acc -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n uu____502 -> (match (uu____502) with
| (x, uu____506) -> begin
(let _0_782 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _0_782))
end)) acc)))
and free_names_and_uvars_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.free_vars = (fun c -> (

let uu____510 = (FStar_ST.read c.FStar_Syntax_Syntax.vars)
in (match (uu____510) with
| Some (n) -> begin
(

let uu____516 = (should_invalidate_cache n)
in (match (uu____516) with
| true -> begin
((FStar_ST.write c.FStar_Syntax_Syntax.vars None);
(free_names_and_uvars_comp c);
)
end
| uu____521 -> begin
n
end))
end
| uu____522 -> begin
(

let n = (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (t, None)) | (FStar_Syntax_Syntax.Total (t, None)) -> begin
(free_names_and_uvars t)
end
| (FStar_Syntax_Syntax.GTotal (t, Some (u))) | (FStar_Syntax_Syntax.Total (t, Some (u))) -> begin
(let _0_784 = (free_univs u)
in (let _0_783 = (free_names_and_uvars t)
in (union _0_784 _0_783)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let us = (let _0_785 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args _0_785))
in (FStar_List.fold_left (fun us u -> (let _0_786 = (free_univs u)
in (union us _0_786))) us ct.FStar_Syntax_Syntax.comp_univs))
end)
in ((FStar_ST.write c.FStar_Syntax_Syntax.vars (Some (n)));
n;
))
end)))
and should_invalidate_cache : FStar_Syntax_Syntax.free_vars  ->  Prims.bool = (fun n -> ((let _0_787 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_uvars FStar_Util.set_elements)
in (FStar_All.pipe_right _0_787 (FStar_Util.for_some (fun uu____600 -> (match (uu____600) with
| (u, uu____610) -> begin
(

let uu____623 = (FStar_Unionfind.find u)
in (match (uu____623) with
| FStar_Syntax_Syntax.Fixed (uu____630) -> begin
true
end
| uu____635 -> begin
false
end))
end))))) || (let _0_788 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_univs FStar_Util.set_elements)
in (FStar_All.pipe_right _0_788 (FStar_Util.for_some (fun u -> (

let uu____647 = (FStar_Unionfind.find u)
in (match (uu____647) with
| Some (uu____650) -> begin
true
end
| None -> begin
false
end))))))))


let names : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun t -> (free_names_and_uvars t).FStar_Syntax_Syntax.free_names)


let uvars : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set = (fun t -> (free_names_and_uvars t).FStar_Syntax_Syntax.free_uvars)


let univs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun t -> (free_names_and_uvars t).FStar_Syntax_Syntax.free_univs)


let univnames : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun t -> (free_names_and_uvars t).FStar_Syntax_Syntax.free_univ_names)


let names_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun bs -> (free_names_and_uvars_binders bs no_free_vars).FStar_Syntax_Syntax.free_names)




