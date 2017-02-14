
open Prims

type free_vars_and_fvars =
(FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)


let no_free_vars : (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (let _0_672 = (FStar_Syntax_Syntax.new_fv_set ())
in (({FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names}), (_0_672)))


let singleton_fvar : FStar_Syntax_Syntax.fv  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun fv -> (let _0_674 = (let _0_673 = (FStar_Syntax_Syntax.new_fv_set ())
in (FStar_Util.set_add fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v _0_673))
in (({FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names}), (_0_674))))


let singleton_bv : FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (let _0_678 = (let _0_676 = (let _0_675 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Util.set_add x _0_675))
in {FStar_Syntax_Syntax.free_names = _0_676; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names})
in (let _0_677 = (FStar_Syntax_Syntax.new_fv_set ())
in ((_0_678), (_0_677)))))


let singleton_uv : ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (let _0_682 = (let _0_680 = (let _0_679 = (FStar_Syntax_Syntax.new_uv_set ())
in (FStar_Util.set_add x _0_679))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = _0_680; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names})
in (let _0_681 = (FStar_Syntax_Syntax.new_fv_set ())
in ((_0_682), (_0_681)))))


let singleton_univ : FStar_Syntax_Syntax.universe_uvar  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (let _0_686 = (let _0_684 = (let _0_683 = (FStar_Syntax_Syntax.new_universe_uvar_set ())
in (FStar_Util.set_add x _0_683))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = _0_684; FStar_Syntax_Syntax.free_univ_names = FStar_Syntax_Syntax.no_universe_names})
in (let _0_685 = (FStar_Syntax_Syntax.new_fv_set ())
in ((_0_686), (_0_685)))))


let singleton_univ_name : FStar_Syntax_Syntax.univ_name  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun x -> (let _0_690 = (let _0_688 = (let _0_687 = (FStar_Syntax_Syntax.new_universe_names_fifo_set ())
in (FStar_Util.fifo_set_add x _0_687))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars; FStar_Syntax_Syntax.free_univ_names = _0_688})
in (let _0_689 = (FStar_Syntax_Syntax.new_fv_set ())
in ((_0_690), (_0_689)))))


let union = (fun f1 f2 -> (let _0_696 = (let _0_694 = (FStar_Util.set_union (Prims.fst f1).FStar_Syntax_Syntax.free_names (Prims.fst f2).FStar_Syntax_Syntax.free_names)
in (let _0_693 = (FStar_Util.set_union (Prims.fst f1).FStar_Syntax_Syntax.free_uvars (Prims.fst f2).FStar_Syntax_Syntax.free_uvars)
in (let _0_692 = (FStar_Util.set_union (Prims.fst f1).FStar_Syntax_Syntax.free_univs (Prims.fst f2).FStar_Syntax_Syntax.free_univs)
in (let _0_691 = (FStar_Util.fifo_set_union (Prims.fst f1).FStar_Syntax_Syntax.free_univ_names (Prims.fst f2).FStar_Syntax_Syntax.free_univ_names)
in {FStar_Syntax_Syntax.free_names = _0_694; FStar_Syntax_Syntax.free_uvars = _0_693; FStar_Syntax_Syntax.free_univs = _0_692; FStar_Syntax_Syntax.free_univ_names = _0_691}))))
in (let _0_695 = (FStar_Util.set_union (Prims.snd f1) (Prims.snd f2))
in ((_0_696), (_0_695)))))


let rec free_univs : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun u -> (

let uu____143 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____143) with
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
(FStar_List.fold_left (fun out x -> (let _0_697 = (free_univs x)
in (union out _0_697))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u) -> begin
(singleton_univ u)
end)))


let rec free_names_and_uvs' : FStar_Syntax_Syntax.term  ->  Prims.bool  ->  free_vars_and_fvars = (fun tm use_cache -> (

let aux_binders = (fun bs from_body -> (

let from_binders = (FStar_All.pipe_right bs (FStar_List.fold_left (fun n uu____266 -> (match (uu____266) with
| (x, uu____276) -> begin
(let _0_698 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n _0_698))
end)) no_free_vars))
in (union from_binders from_body)))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____278) -> begin
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
| FStar_Syntax_Syntax.Tm_bvar (uu____321) -> begin
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
in (FStar_List.fold_left (fun out u -> (let _0_699 = (free_univs u)
in (union out _0_699))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, uu____344) -> begin
(let _0_700 = (free_names_and_uvars t use_cache)
in (aux_binders bs _0_700))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _0_701 = (free_names_and_uvars_comp c use_cache)
in (aux_binders bs _0_701))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(let _0_702 = (free_names_and_uvars t use_cache)
in (aux_binders ((((bv), (None)))::[]) _0_702))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _0_703 = (free_names_and_uvars t use_cache)
in (free_names_and_uvars_args args _0_703 use_cache))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(let _0_708 = (let _0_707 = (free_names_and_uvars t use_cache)
in (FStar_List.fold_left (fun n uu____462 -> (match (uu____462) with
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

let n = (let _0_705 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _0_705 (FStar_List.fold_left (fun n x -> (let _0_704 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n _0_704))) n)))
in (let _0_706 = (union n1 n2)
in (union n _0_706)))))
end)) _0_707))
in (FStar_All.pipe_right pats _0_708))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), uu____526) -> begin
(let _0_710 = (free_names_and_uvars t1 use_cache)
in (let _0_709 = (free_names_and_uvars t2 use_cache)
in (union _0_710 _0_709)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), uu____547) -> begin
(let _0_712 = (free_names_and_uvars t1 use_cache)
in (let _0_711 = (free_names_and_uvars_comp c use_cache)
in (union _0_712 _0_711)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(let _0_717 = (let _0_716 = (free_names_and_uvars t use_cache)
in (FStar_List.fold_left (fun n lb -> (let _0_715 = (let _0_714 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp use_cache)
in (let _0_713 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef use_cache)
in (union _0_714 _0_713)))
in (union n _0_715))) _0_716))
in (FStar_All.pipe_right (Prims.snd lbs) _0_717))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _0_718 = (free_names_and_uvars t use_cache)
in (FStar_List.fold_right (fun a acc -> (free_names_and_uvars_args a acc use_cache)) args _0_718))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (uu____622, t')) -> begin
(let _0_720 = (free_names_and_uvars t use_cache)
in (let _0_719 = (free_names_and_uvars t' use_cache)
in (union _0_720 _0_719)))
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____633) -> begin
(free_names_and_uvars t use_cache)
end))))
and free_names_and_uvars : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun t use_cache -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let uu____643 = (FStar_ST.read t.FStar_Syntax_Syntax.vars)
in (match (uu____643) with
| Some (n) when (not ((should_invalidate_cache n use_cache))) -> begin
(let _0_721 = (FStar_Syntax_Syntax.new_fv_set ())
in ((n), (_0_721)))
end
| uu____653 -> begin
((FStar_ST.write t.FStar_Syntax_Syntax.vars None);
(

let n = (free_names_and_uvs' t use_cache)
in ((FStar_ST.write t.FStar_Syntax_Syntax.vars (Some ((Prims.fst n))));
n;
));
)
end))))
and free_names_and_uvars_args : ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)  ->  Prims.bool  ->  free_vars_and_fvars = (fun args acc use_cache -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n uu____692 -> (match (uu____692) with
| (x, uu____704) -> begin
(let _0_722 = (free_names_and_uvars x use_cache)
in (union n _0_722))
end)) acc)))
and free_names_and_uvars_binders = (fun bs acc use_cache -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n uu____730 -> (match (uu____730) with
| (x, uu____740) -> begin
(let _0_723 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache)
in (union n _0_723))
end)) acc)))
and free_names_and_uvars_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  Prims.bool  ->  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) = (fun c use_cache -> (

let uu____745 = (FStar_ST.read c.FStar_Syntax_Syntax.vars)
in (match (uu____745) with
| Some (n) -> begin
(

let uu____754 = (should_invalidate_cache n use_cache)
in (match (uu____754) with
| true -> begin
((FStar_ST.write c.FStar_Syntax_Syntax.vars None);
(free_names_and_uvars_comp c use_cache);
)
end
| uu____762 -> begin
(let _0_724 = (FStar_Syntax_Syntax.new_fv_set ())
in ((n), (_0_724)))
end))
end
| uu____764 -> begin
(

let n = (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (t, None)) | (FStar_Syntax_Syntax.Total (t, None)) -> begin
(free_names_and_uvars t use_cache)
end
| (FStar_Syntax_Syntax.GTotal (t, Some (u))) | (FStar_Syntax_Syntax.Total (t, Some (u))) -> begin
(let _0_726 = (free_univs u)
in (let _0_725 = (free_names_and_uvars t use_cache)
in (union _0_726 _0_725)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let us = (let _0_727 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ use_cache)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args _0_727 use_cache))
in (FStar_List.fold_left (fun us u -> (let _0_728 = (free_univs u)
in (union us _0_728))) us ct.FStar_Syntax_Syntax.comp_univs))
end)
in ((FStar_ST.write c.FStar_Syntax_Syntax.vars (Some ((Prims.fst n))));
n;
))
end)))
and should_invalidate_cache : FStar_Syntax_Syntax.free_vars  ->  Prims.bool  ->  Prims.bool = (fun n use_cache -> ((not (use_cache)) || ((let _0_729 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_uvars FStar_Util.set_elements)
in (FStar_All.pipe_right _0_729 (FStar_Util.for_some (fun uu____856 -> (match (uu____856) with
| (u, uu____866) -> begin
(

let uu____879 = (FStar_Unionfind.find u)
in (match (uu____879) with
| FStar_Syntax_Syntax.Fixed (uu____886) -> begin
true
end
| uu____891 -> begin
false
end))
end))))) || (let _0_730 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_univs FStar_Util.set_elements)
in (FStar_All.pipe_right _0_730 (FStar_Util.for_some (fun u -> (

let uu____903 = (FStar_Unionfind.find u)
in (match (uu____903) with
| Some (uu____906) -> begin
true
end
| None -> begin
false
end)))))))))


let names : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun t -> (Prims.fst (free_names_and_uvars t true)).FStar_Syntax_Syntax.free_names)


let uvars : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set = (fun t -> (Prims.fst (free_names_and_uvars t true)).FStar_Syntax_Syntax.free_uvars)


let univs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun t -> (Prims.fst (free_names_and_uvars t true)).FStar_Syntax_Syntax.free_univs)


let univnames : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun t -> (Prims.fst (free_names_and_uvars t true)).FStar_Syntax_Syntax.free_univ_names)


let fvars : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident FStar_Util.set = (fun t -> (Prims.snd (free_names_and_uvars t false)))


let names_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun bs -> (Prims.fst (free_names_and_uvars_binders bs no_free_vars true)).FStar_Syntax_Syntax.free_names)




