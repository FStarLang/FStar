
open Prims

let tc_tycon : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_TypeChecker_Env.env_t * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals) -> begin
(

let uu____33 = (FStar_Syntax_Subst.open_term tps k)
in (match (uu____33) with
| (tps1, k1) -> begin
(

let uu____42 = (FStar_TypeChecker_TcTerm.tc_binders env tps1)
in (match (uu____42) with
| (tps2, env_tps, guard_params, us) -> begin
(

let k2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env k1)
in (

let uu____56 = (FStar_Syntax_Util.arrow_formals k2)
in (match (uu____56) with
| (indices, t) -> begin
(

let uu____80 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (uu____80) with
| (indices1, env', guard_indices, us') -> begin
(

let uu____93 = (

let uu____96 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (uu____96) with
| (t1, uu____103, g) -> begin
(

let uu____105 = (

let uu____106 = (

let uu____107 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params uu____107))
in (FStar_TypeChecker_Rel.discharge_guard env' uu____106))
in ((t1), (uu____105)))
end))
in (match (uu____93) with
| (t1, guard) -> begin
(

let k3 = (

let uu____117 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_Syntax_Util.arrow indices1 uu____117))
in (

let uu____120 = (FStar_Syntax_Util.type_u ())
in (match (uu____120) with
| (t_type, u) -> begin
((

let uu____130 = (FStar_TypeChecker_Rel.teq env' t1 t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' uu____130));
(

let t_tc = (

let uu____134 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_Syntax_Util.arrow (FStar_List.append tps2 indices1) uu____134))
in (

let tps3 = (FStar_Syntax_Subst.close_binders tps2)
in (

let k4 = (FStar_Syntax_Subst.close tps3 k3)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____142 = (FStar_TypeChecker_Env.push_let_binding env (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((uu____142), ((

let uu___83_146 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps3), (k4), (mutuals), (data), (quals))); FStar_Syntax_Syntax.sigrng = uu___83_146.FStar_Syntax_Syntax.sigrng})), (u), (guard)))))));
)
end)))
end))
end))
end)))
end))
end))
end
| uu____151 -> begin
(failwith "impossible")
end))


let tc_data : FStar_TypeChecker_Env.env_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.guard_t) = (fun env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs) -> begin
(

let uu____191 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun uu____205 -> (match (uu____205) with
| (se1, u_tc) -> begin
(

let uu____214 = (

let uu____215 = (

let uu____216 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____216))
in (FStar_Ident.lid_equals tc_lid uu____215))
in (match (uu____214) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____226, uu____227, tps, uu____229, uu____230, uu____231, uu____232) -> begin
(

let tps1 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____253 -> (match (uu____253) with
| (x, uu____260) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let tps2 = (FStar_Syntax_Subst.open_binders tps1)
in (

let uu____263 = (

let uu____267 = (FStar_TypeChecker_Env.push_binders env tps2)
in ((uu____267), (tps2), (u_tc)))
in Some (uu____263))))
end
| uu____271 -> begin
(failwith "Impossible")
end)
end
| uu____276 -> begin
None
end))
end)))
in (match (tps_u_opt) with
| Some (x) -> begin
x
end
| None -> begin
(match ((FStar_Ident.lid_equals tc_lid FStar_Syntax_Const.exn_lid)) with
| true -> begin
((env), ([]), (FStar_Syntax_Syntax.U_zero))
end
| uu____301 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected data constructor"), (se.FStar_Syntax_Syntax.sigrng)))))
end)
end))
in (match (uu____191) with
| (env1, tps, u_tc) -> begin
(

let norm_whnf = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env1)
in (

let uu____313 = (

let t1 = (norm_whnf t)
in (

let uu____322 = (

let uu____323 = (FStar_Syntax_Subst.compress t1)
in uu____323.FStar_Syntax_Syntax.n)
in (match (uu____322) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let uu____345 = (FStar_Util.first_N ntps bs)
in (match (uu____345) with
| (uu____363, bs') -> begin
(

let t2 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res))))) None t1.FStar_Syntax_Syntax.pos)
in (

let subst1 = (FStar_All.pipe_right tps (FStar_List.mapi (fun i uu____399 -> (match (uu____399) with
| (x, uu____403) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (

let uu____404 = (FStar_Syntax_Subst.subst subst1 t2)
in (FStar_Syntax_Util.arrow_formals uu____404))))
end))
end
| uu____405 -> begin
(([]), (t1))
end)))
in (match (uu____313) with
| (arguments, result) -> begin
((

let uu____426 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____426) with
| true -> begin
(

let uu____427 = (FStar_Syntax_Print.lid_to_string c)
in (

let uu____428 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (

let uu____429 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" uu____427 uu____428 uu____429))))
end
| uu____430 -> begin
()
end));
(

let uu____431 = (FStar_TypeChecker_TcTerm.tc_tparams env1 arguments)
in (match (uu____431) with
| (arguments1, env', us) -> begin
(

let uu____440 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (uu____440) with
| (result1, res_lcomp) -> begin
((

let uu____448 = (

let uu____449 = (FStar_Syntax_Subst.compress res_lcomp.FStar_Syntax_Syntax.res_typ)
in uu____449.FStar_Syntax_Syntax.n)
in (match (uu____448) with
| FStar_Syntax_Syntax.Tm_type (uu____452) -> begin
()
end
| ty -> begin
(

let uu____454 = (

let uu____455 = (

let uu____458 = (

let uu____459 = (FStar_Syntax_Print.term_to_string result1)
in (

let uu____460 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" uu____459 uu____460)))
in ((uu____458), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Errors.Error (uu____455))
in (Prims.raise uu____454))
end));
(

let uu____461 = (FStar_Syntax_Util.head_and_args result1)
in (match (uu____461) with
| (head1, uu____474) -> begin
((

let uu____490 = (

let uu____491 = (FStar_Syntax_Subst.compress head1)
in uu____491.FStar_Syntax_Syntax.n)
in (match (uu____490) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| uu____495 -> begin
(

let uu____496 = (

let uu____497 = (

let uu____500 = (

let uu____501 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (

let uu____502 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" uu____501 uu____502)))
in ((uu____500), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Errors.Error (uu____497))
in (Prims.raise uu____496))
end));
(

let g = (FStar_List.fold_left2 (fun g uu____507 u_x -> (match (uu____507) with
| (x, uu____512) -> begin
(

let uu____513 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g uu____513))
end)) FStar_TypeChecker_Rel.trivial_guard arguments1 us)
in (

let t1 = (

let uu____517 = (

let uu____521 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____535 -> (match (uu____535) with
| (x, uu____542) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append uu____521 arguments1))
in (

let uu____547 = (FStar_Syntax_Syntax.mk_Total result1)
in (FStar_Syntax_Util.arrow uu____517 uu____547)))
in (((

let uu___84_550 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t1), (tc_lid), (ntps), (quals), ([]))); FStar_Syntax_Syntax.sigrng = uu___84_550.FStar_Syntax_Syntax.sigrng})), (g))));
)
end));
)
end))
end));
)
end)))
end))
end
| uu____556 -> begin
(failwith "impossible")
end))


let generalize_and_inst_within : FStar_TypeChecker_Env.env_t  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env g tcs datas -> (

let tc_universe_vars = (FStar_List.map Prims.snd tcs)
in (

let g1 = (

let uu___85_592 = g
in {FStar_TypeChecker_Env.guard_f = uu___85_592.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___85_592.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((tc_universe_vars), ((Prims.snd g.FStar_TypeChecker_Env.univ_ineqs))); FStar_TypeChecker_Env.implicits = uu___85_592.FStar_TypeChecker_Env.implicits})
in ((

let uu____598 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____598) with
| true -> begin
(

let uu____599 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "@@@@@@Guard before generalization: %s\n" uu____599))
end
| uu____600 -> begin
()
end));
(FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun uu____610 -> (match (uu____610) with
| (se, uu____614) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____615, uu____616, tps, k, uu____619, uu____620, uu____621) -> begin
(

let uu____628 = (

let uu____629 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) uu____629))
in (FStar_Syntax_Syntax.null_binder uu____628))
end
| uu____636 -> begin
(failwith "Impossible")
end)
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____642, uu____643, t, uu____645, uu____646, uu____647, uu____648) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| uu____653 -> begin
(failwith "Impossible")
end))))
in (

let t = (

let uu____657 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') uu____657))
in ((

let uu____661 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____661) with
| true -> begin
(

let uu____662 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" uu____662))
end
| uu____663 -> begin
()
end));
(

let uu____664 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (uu____664) with
| (uvs, t1) -> begin
((

let uu____674 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____674) with
| true -> begin
(

let uu____675 = (

let uu____676 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right uu____676 (FStar_String.concat ", ")))
in (

let uu____682 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" uu____675 uu____682)))
end
| uu____683 -> begin
()
end));
(

let uu____684 = (FStar_Syntax_Subst.open_univ_vars uvs t1)
in (match (uu____684) with
| (uvs1, t2) -> begin
(

let uu____693 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____693) with
| (args, uu____706) -> begin
(

let uu____717 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (uu____717) with
| (tc_types, data_types) -> begin
(

let tcs1 = (FStar_List.map2 (fun uu____754 uu____755 -> (match (((uu____754), (uu____755))) with
| ((x, uu____765), (se, uu____767)) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____773, tps, uu____775, mutuals, datas1, quals) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs1 x.FStar_Syntax_Syntax.sort)
in (

let uu____786 = (

let uu____794 = (

let uu____795 = (FStar_Syntax_Subst.compress ty)
in uu____795.FStar_Syntax_Syntax.n)
in (match (uu____794) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c) -> begin
(

let uu____817 = (FStar_Util.first_N (FStar_List.length tps) binders1)
in (match (uu____817) with
| (tps1, rest) -> begin
(

let t3 = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____860 -> begin
(

let uu____864 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c))))) uu____864 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps1), (t3)))
end))
end
| uu____887 -> begin
(([]), (ty))
end))
in (match (uu____786) with
| (tps1, t3) -> begin
(

let uu___86_905 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs1), (tps1), (t3), (mutuals), (datas1), (quals))); FStar_Syntax_Syntax.sigrng = uu___86_905.FStar_Syntax_Syntax.sigrng})
end)))
end
| uu____914 -> begin
(failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas1 = (match (uvs1) with
| [] -> begin
datas
end
| uu____918 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs1 (FStar_List.map (fun _0_28 -> FStar_Syntax_Syntax.U_name (_0_28))))
in (

let tc_insts = (FStar_All.pipe_right tcs1 (FStar_List.map (fun uu___79_935 -> (match (uu___79_935) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____940, uu____941, uu____942, uu____943, uu____944, uu____945); FStar_Syntax_Syntax.sigrng = uu____946} -> begin
((tc), (uvs_universes))
end
| uu____954 -> begin
(failwith "Impossible")
end))))
in (FStar_List.map2 (fun uu____960 d -> (match (uu____960) with
| (t3, uu____965) -> begin
(match (d.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____967, uu____968, tc, ntps, quals, mutuals) -> begin
(

let ty = (

let uu____978 = (FStar_Syntax_InstFV.instantiate tc_insts t3.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____978 (FStar_Syntax_Subst.close_univ_vars uvs1)))
in (

let uu___87_979 = d
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((l), (uvs1), (ty), (tc), (ntps), (quals), (mutuals))); FStar_Syntax_Syntax.sigrng = uu___87_979.FStar_Syntax_Syntax.sigrng}))
end
| uu____982 -> begin
(failwith "Impossible")
end)
end)) data_types datas)))
end)
in ((tcs1), (datas1))))
end))
end))
end));
)
end));
))));
))))


let debug_log : FStar_TypeChecker_Env.env_t  ->  Prims.string  ->  Prims.unit = (fun env s -> (

let uu____991 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Positivity")))
in (match (uu____991) with
| true -> begin
(FStar_Util.print_string (Prims.strcat "Positivity::" (Prims.strcat s "\n")))
end
| uu____992 -> begin
()
end)))


let ty_occurs_in : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun ty_lid t -> (

let uu____999 = (FStar_Syntax_Free.fvars t)
in (FStar_Util.set_mem ty_lid uu____999)))


let try_get_fv : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes) = (fun t -> (

let uu____1008 = (

let uu____1009 = (FStar_Syntax_Subst.compress t)
in uu____1009.FStar_Syntax_Syntax.n)
in (match (uu____1008) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), (us))
end
| uu____1025 -> begin
(failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
end)
end
| uu____1028 -> begin
(failwith "Node is not an fvar or a Tm_uinst")
end)))


type unfolded_memo_elt =
(FStar_Ident.lident * FStar_Syntax_Syntax.args) Prims.list


type unfolded_memo_t =
unfolded_memo_elt FStar_ST.ref


let already_unfolded : FStar_Ident.lident  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ilid arrghs unfolded env -> (

let uu____1047 = (FStar_ST.read unfolded)
in (FStar_List.existsML (fun uu____1059 -> (match (uu____1059) with
| (lid, l) -> begin
((FStar_Ident.lid_equals lid ilid) && (

let args = (

let uu____1079 = (FStar_List.splitAt (FStar_List.length l) arrghs)
in (Prims.fst uu____1079))
in (FStar_List.fold_left2 (fun b a a' -> (b && (FStar_TypeChecker_Rel.teq_nosmt env (Prims.fst a) (Prims.fst a')))) true args l)))
end)) uu____1047)))


let rec ty_strictly_positive_in_type : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid btype unfolded env -> ((

let uu____1174 = (

let uu____1175 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity in type: " uu____1175))
in (debug_log env uu____1174));
(

let btype1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env btype)
in ((

let uu____1178 = (

let uu____1179 = (FStar_Syntax_Print.term_to_string btype1)
in (Prims.strcat "Checking strict positivity in type, after normalization: " uu____1179))
in (debug_log env uu____1178));
((

let uu____1180 = (ty_occurs_in ty_lid btype1)
in (not (uu____1180))) || ((debug_log env "ty does occur in this type, pressing ahead");
(

let uu____1182 = (

let uu____1183 = (FStar_Syntax_Subst.compress btype1)
in uu____1183.FStar_Syntax_Syntax.n)
in (match (uu____1182) with
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1202 = (try_get_fv t)
in (match (uu____1202) with
| (fv, us) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ty_lid)) with
| true -> begin
((debug_log env "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
(FStar_List.for_all (fun uu____1214 -> (match (uu____1214) with
| (t1, uu____1218) -> begin
(

let uu____1219 = (ty_occurs_in ty_lid t1)
in (not (uu____1219)))
end)) args);
)
end
| uu____1220 -> begin
((debug_log env "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
(ty_nested_positive_in_inductive ty_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v us args unfolded env);
)
end)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((debug_log env "Checking strict positivity in Tm_arrow");
(

let uu____1239 = (

let uu____1240 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____1240)))
in (match (uu____1239) with
| true -> begin
((debug_log env "Checking strict positivity , the arrow is impure, so return true");
true;
)
end
| uu____1242 -> begin
((debug_log env "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
((FStar_List.for_all (fun uu____1246 -> (match (uu____1246) with
| (b, uu____1250) -> begin
(

let uu____1251 = (ty_occurs_in ty_lid b.FStar_Syntax_Syntax.sort)
in (not (uu____1251)))
end)) sbs) && (

let uu____1252 = (FStar_Syntax_Subst.open_term sbs (FStar_Syntax_Util.comp_result c))
in (match (uu____1252) with
| (uu____1255, return_type) -> begin
(

let uu____1257 = (FStar_TypeChecker_Env.push_binders env sbs)
in (ty_strictly_positive_in_type ty_lid return_type unfolded uu____1257))
end)));
)
end));
)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1258) -> begin
((debug_log env "Checking strict positivity in an fvar, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_type (uu____1260) -> begin
((debug_log env "Checking strict positivity in an Tm_type, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____1263) -> begin
((debug_log env "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____1270) -> begin
((debug_log env "Checking strict positivity in an Tm_refine, recur in the bv sort)");
(ty_strictly_positive_in_type ty_lid bv.FStar_Syntax_Syntax.sort unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_match (uu____1276, branches) -> begin
((debug_log env "Checking strict positivity in an Tm_match, recur in the branches)");
(FStar_List.for_all (fun uu____1311 -> (match (uu____1311) with
| (p, uu____1319, t) -> begin
(

let bs = (

let uu____1329 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_List.map FStar_Syntax_Syntax.mk_binder uu____1329))
in (

let uu____1331 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____1331) with
| (bs1, t1) -> begin
(

let uu____1336 = (FStar_TypeChecker_Env.push_binders env bs1)
in (ty_strictly_positive_in_type ty_lid t1 unfolded uu____1336))
end)))
end)) branches);
)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____1338, uu____1339) -> begin
((debug_log env "Checking strict positivity in an Tm_ascribed, recur)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| uu____1369 -> begin
((

let uu____1371 = (

let uu____1372 = (

let uu____1373 = (FStar_Syntax_Print.tag_of_term btype1)
in (

let uu____1374 = (

let uu____1375 = (FStar_Syntax_Print.term_to_string btype1)
in (Prims.strcat " and term: " uu____1375))
in (Prims.strcat uu____1373 uu____1374)))
in (Prims.strcat "Checking strict positivity, unexpected tag: " uu____1372))
in (debug_log env uu____1371));
false;
)
end));
));
));
))
and ty_nested_positive_in_inductive : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid ilid us args unfolded env -> ((

let uu____1383 = (

let uu____1384 = (

let uu____1385 = (

let uu____1386 = (FStar_Syntax_Print.args_to_string args)
in (Prims.strcat " applied to arguments: " uu____1386))
in (Prims.strcat ilid.FStar_Ident.str uu____1385))
in (Prims.strcat "Checking nested positivity in the inductive " uu____1384))
in (debug_log env uu____1383));
(

let uu____1387 = (FStar_TypeChecker_Env.datacons_of_typ env ilid)
in (match (uu____1387) with
| (b, idatas) -> begin
(match ((not (b))) with
| true -> begin
((debug_log env "Checking nested positivity, not an inductive, return false");
false;
)
end
| uu____1396 -> begin
(

let uu____1397 = (already_unfolded ilid args unfolded env)
in (match (uu____1397) with
| true -> begin
((debug_log env "Checking nested positivity, we have already unfolded this inductive with these args");
true;
)
end
| uu____1399 -> begin
(

let num_ibs = (FStar_TypeChecker_Env.num_inductive_ty_params env ilid)
in ((

let uu____1402 = (

let uu____1403 = (

let uu____1404 = (FStar_Util.string_of_int num_ibs)
in (Prims.strcat uu____1404 ", also adding to the memo table"))
in (Prims.strcat "Checking nested positivity, number of type parameters is " uu____1403))
in (debug_log env uu____1402));
(

let uu____1406 = (

let uu____1407 = (FStar_ST.read unfolded)
in (

let uu____1411 = (

let uu____1415 = (

let uu____1423 = (

let uu____1429 = (FStar_List.splitAt num_ibs args)
in (Prims.fst uu____1429))
in ((ilid), (uu____1423)))
in (uu____1415)::[])
in (FStar_List.append uu____1407 uu____1411)))
in (FStar_ST.write unfolded uu____1406));
(FStar_List.for_all (fun d -> (ty_nested_positive_in_dlid ty_lid d ilid us args num_ibs unfolded env)) idatas);
))
end))
end)
end));
))
and ty_nested_positive_in_dlid : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  Prims.int  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid dlid ilid us args num_ibs unfolded env -> ((debug_log env (Prims.strcat "Checking nested positivity in data constructor " (Prims.strcat dlid.FStar_Ident.str (Prims.strcat " of the inductive " ilid.FStar_Ident.str))));
(

let uu____1487 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____1487) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____1499 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let dt1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env dt)
in ((

let uu____1502 = (

let uu____1503 = (FStar_Syntax_Print.term_to_string dt1)
in (Prims.strcat "Checking nested positivity in the data constructor type: " uu____1503))
in (debug_log env uu____1502));
(

let uu____1504 = (

let uu____1505 = (FStar_Syntax_Subst.compress dt1)
in uu____1505.FStar_Syntax_Syntax.n)
in (match (uu____1504) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, c) -> begin
((debug_log env "Checked nested positivity in Tm_arrow data constructor type");
(

let uu____1521 = (FStar_List.splitAt num_ibs dbs)
in (match (uu____1521) with
| (ibs, dbs1) -> begin
(

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let dbs2 = (

let uu____1548 = (FStar_Syntax_Subst.opening_of_binders ibs1)
in (FStar_Syntax_Subst.subst_binders uu____1548 dbs1))
in (

let c1 = (

let uu____1551 = (FStar_Syntax_Subst.opening_of_binders ibs1)
in (FStar_Syntax_Subst.subst_comp uu____1551 c))
in (

let uu____1553 = (FStar_List.splitAt num_ibs args)
in (match (uu____1553) with
| (args1, uu____1571) -> begin
(

let subst1 = (FStar_List.fold_left2 (fun subst1 ib arg -> (FStar_List.append subst1 ((FStar_Syntax_Syntax.NT ((((Prims.fst ib)), ((Prims.fst arg)))))::[]))) [] ibs1 args1)
in (

let dbs3 = (FStar_Syntax_Subst.subst_binders subst1 dbs2)
in (

let c2 = (

let uu____1617 = (FStar_Syntax_Subst.shift_subst (FStar_List.length dbs3) subst1)
in (FStar_Syntax_Subst.subst_comp uu____1617 c1))
in ((

let uu____1625 = (

let uu____1626 = (

let uu____1627 = (FStar_Syntax_Print.binders_to_string "; " dbs3)
in (

let uu____1628 = (

let uu____1629 = (FStar_Syntax_Print.comp_to_string c2)
in (Prims.strcat ", and c: " uu____1629))
in (Prims.strcat uu____1627 uu____1628)))
in (Prims.strcat "Checking nested positivity in the unfolded data constructor binders as: " uu____1626))
in (debug_log env uu____1625));
(ty_nested_positive_in_type ty_lid (FStar_Syntax_Syntax.Tm_arrow (((dbs3), (c2)))) ilid num_ibs unfolded env);
))))
end)))))
end));
)
end
| uu____1630 -> begin
((debug_log env "Checking nested positivity in the data constructor type that is not an arrow");
(

let uu____1632 = (

let uu____1633 = (FStar_Syntax_Subst.compress dt1)
in uu____1633.FStar_Syntax_Syntax.n)
in (ty_nested_positive_in_type ty_lid uu____1632 ilid num_ibs unfolded env));
)
end));
));
)
end));
))
and ty_nested_positive_in_type : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term'  ->  FStar_Ident.lident  ->  Prims.int  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid t ilid num_ibs unfolded env -> (match (t) with
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
((debug_log env "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself");
(

let uu____1659 = (try_get_fv t1)
in (match (uu____1659) with
| (fv, uu____1663) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ilid)) with
| true -> begin
true
end
| uu____1668 -> begin
(failwith "Impossible, expected the type to be ilid")
end)
end));
)
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((

let uu____1682 = (

let uu____1683 = (FStar_Syntax_Print.binders_to_string "; " sbs)
in (Prims.strcat "Checking nested positivity in an Tm_arrow node, with binders as: " uu____1683))
in (debug_log env uu____1682));
(

let sbs1 = (FStar_Syntax_Subst.open_binders sbs)
in (

let uu____1685 = (FStar_List.fold_left (fun uu____1692 b -> (match (uu____1692) with
| (r, env1) -> begin
(match ((not (r))) with
| true -> begin
((r), (env1))
end
| uu____1704 -> begin
(

let uu____1705 = (ty_strictly_positive_in_type ty_lid (Prims.fst b).FStar_Syntax_Syntax.sort unfolded env1)
in (

let uu____1706 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((uu____1705), (uu____1706))))
end)
end)) ((true), (env)) sbs1)
in (match (uu____1685) with
| (b, uu____1712) -> begin
b
end)));
)
end
| uu____1713 -> begin
(failwith "Nested positive check, unhandled case")
end))


let ty_positive_in_datacon : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.universes  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty_lid dlid ty_bs us unfolded env -> (

let uu____1732 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____1732) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____1744 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let uu____1746 = (

let uu____1747 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking data constructor type: " uu____1747))
in (debug_log env uu____1746));
(

let uu____1748 = (

let uu____1749 = (FStar_Syntax_Subst.compress dt)
in uu____1749.FStar_Syntax_Syntax.n)
in (match (uu____1748) with
| FStar_Syntax_Syntax.Tm_fvar (uu____1752) -> begin
((debug_log env "Data constructor type is simply an fvar, returning true");
true;
)
end
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____1755) -> begin
(

let dbs1 = (

let uu____1770 = (FStar_List.splitAt (FStar_List.length ty_bs) dbs)
in (Prims.snd uu____1770))
in (

let dbs2 = (

let uu____1792 = (FStar_Syntax_Subst.opening_of_binders ty_bs)
in (FStar_Syntax_Subst.subst_binders uu____1792 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in ((

let uu____1796 = (

let uu____1797 = (

let uu____1798 = (FStar_Util.string_of_int (FStar_List.length dbs3))
in (Prims.strcat uu____1798 " binders"))
in (Prims.strcat "Data constructor type is an arrow type, so checking strict positivity in " uu____1797))
in (debug_log env uu____1796));
(

let uu____1804 = (FStar_List.fold_left (fun uu____1811 b -> (match (uu____1811) with
| (r, env1) -> begin
(match ((not (r))) with
| true -> begin
((r), (env1))
end
| uu____1823 -> begin
(

let uu____1824 = (ty_strictly_positive_in_type ty_lid (Prims.fst b).FStar_Syntax_Syntax.sort unfolded env1)
in (

let uu____1825 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((uu____1824), (uu____1825))))
end)
end)) ((true), (env)) dbs3)
in (match (uu____1804) with
| (b, uu____1831) -> begin
b
end));
))))
end
| FStar_Syntax_Syntax.Tm_app (uu____1832, uu____1833) -> begin
((debug_log env "Data constructor type is a Tm_app, so returning true");
true;
)
end
| uu____1849 -> begin
(failwith "Unexpected data constructor type when checking positivity")
end));
)
end)))


let check_positivity : FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty env -> (

let unfolded_inductives = (FStar_Util.mk_ref [])
in (

let uu____1867 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, bs, uu____1877, uu____1878, uu____1879, uu____1880) -> begin
((lid), (us), (bs))
end
| uu____1887 -> begin
(failwith "Impossible!")
end)
in (match (uu____1867) with
| (ty_lid, ty_us, ty_bs) -> begin
(

let uu____1894 = (FStar_Syntax_Subst.univ_var_opening ty_us)
in (match (uu____1894) with
| (ty_usubst, ty_us1) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env ty_us1)
in (

let env2 = (FStar_TypeChecker_Env.push_binders env1 ty_bs)
in (

let ty_bs1 = (FStar_Syntax_Subst.subst_binders ty_usubst ty_bs)
in (

let ty_bs2 = (FStar_Syntax_Subst.open_binders ty_bs1)
in (

let uu____1909 = (

let uu____1911 = (FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid)
in (Prims.snd uu____1911))
in (FStar_List.for_all (fun d -> (

let uu____1917 = (FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name (s)) ty_us1)
in (ty_positive_in_datacon ty_lid d ty_bs2 uu____1917 unfolded_inductives env2))) uu____1909))))))
end))
end))))


let datacon_typ : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term = (fun data -> (match (data.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1924, uu____1925, t, uu____1927, uu____1928, uu____1929, uu____1930) -> begin
t
end
| uu____1935 -> begin
(failwith "Impossible!")
end))


let optimized_haseq_soundness_for_data : FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term = (fun ty_lid data usubst bs -> (

let dt = (datacon_typ data)
in (

let dt1 = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____1952 = (

let uu____1953 = (FStar_Syntax_Subst.compress dt1)
in uu____1953.FStar_Syntax_Syntax.n)
in (match (uu____1952) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____1957) -> begin
(

let dbs1 = (

let uu____1972 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd uu____1972))
in (

let dbs2 = (

let uu____1994 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____1994 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (

let uu____2003 = (

let uu____2004 = (

let uu____2005 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (uu____2005)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2004))
in (uu____2003 None FStar_Range.dummyRange))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b1 = (

let uu____2012 = (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add either the \'noeq\' or \'unopteq\' qualifier" ty_lid.FStar_Ident.str)
in (FStar_TypeChecker_Util.label uu____2012 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b1))))) FStar_Syntax_Util.t_true dbs3)
in (FStar_List.fold_right (fun b t -> (

let uu____2017 = (

let uu____2018 = (

let uu____2019 = (

let uu____2020 = (

let uu____2021 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2021 None))
in (FStar_Syntax_Syntax.as_arg uu____2020))
in (uu____2019)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2018))
in (uu____2017 None FStar_Range.dummyRange))) dbs3 cond)))))
end
| uu____2038 -> begin
FStar_Syntax_Util.t_true
end)))))


let optimized_haseq_ty = (fun all_datas_in_the_bundle usubst us acc ty -> (

let uu____2097 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2109, bs, t, uu____2112, d_lids, uu____2114) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____2122 -> begin
(failwith "Impossible!")
end)
in (match (uu____2097) with
| (lid, bs, t, d_lids) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t1 = (

let uu____2147 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst)
in (FStar_Syntax_Subst.subst uu____2147 t))
in (

let uu____2154 = (FStar_Syntax_Subst.open_term bs1 t1)
in (match (uu____2154) with
| (bs2, t2) -> begin
(

let ibs = (

let uu____2174 = (

let uu____2175 = (FStar_Syntax_Subst.compress t2)
in uu____2175.FStar_Syntax_Syntax.n)
in (match (uu____2174) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____2182) -> begin
ibs
end
| uu____2193 -> begin
[]
end))
in (

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____2198 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____2199 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____2198 uu____2199)))
in (

let ind1 = (

let uu____2204 = (

let uu____2205 = (FStar_List.map (fun uu____2210 -> (match (uu____2210) with
| (bv, aq) -> begin
(

let uu____2217 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2217), (aq)))
end)) bs2)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____2205))
in (uu____2204 None FStar_Range.dummyRange))
in (

let ind2 = (

let uu____2225 = (

let uu____2226 = (FStar_List.map (fun uu____2231 -> (match (uu____2231) with
| (bv, aq) -> begin
(

let uu____2238 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2238), (aq)))
end)) ibs1)
in (FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2226))
in (uu____2225 None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____2246 = (

let uu____2247 = (

let uu____2248 = (FStar_Syntax_Syntax.as_arg ind2)
in (uu____2248)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2247))
in (uu____2246 None FStar_Range.dummyRange))
in (

let bs' = (FStar_List.filter (fun b -> (

let uu____2262 = acc
in (match (uu____2262) with
| (uu____2270, en, uu____2272, uu____2273) -> begin
(

let opt = (

let uu____2282 = (

let uu____2283 = (FStar_Syntax_Util.type_u ())
in (Prims.fst uu____2283))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort uu____2282 false))
in (match (opt) with
| None -> begin
false
end
| Some (uu____2286) -> begin
true
end))
end))) bs2)
in (

let haseq_bs = (FStar_List.fold_left (fun t3 b -> (

let uu____2290 = (

let uu____2291 = (

let uu____2292 = (

let uu____2293 = (

let uu____2294 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg uu____2294))
in (uu____2293)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2292))
in (uu____2291 None FStar_Range.dummyRange))
in (FStar_Syntax_Util.mk_conj t3 uu____2290))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml1 = (

let uu___88_2303 = fml
in (

let uu____2304 = (

let uu____2305 = (

let uu____2310 = (

let uu____2311 = (

let uu____2318 = (

let uu____2320 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____2320)::[])
in (uu____2318)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____2311))
in ((fml), (uu____2310)))
in FStar_Syntax_Syntax.Tm_meta (uu____2305))
in {FStar_Syntax_Syntax.n = uu____2304; FStar_Syntax_Syntax.tk = uu___88_2303.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___88_2303.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___88_2303.FStar_Syntax_Syntax.vars}))
in (

let fml2 = (FStar_List.fold_right (fun b t3 -> (

let uu____2332 = (

let uu____2333 = (

let uu____2334 = (

let uu____2335 = (

let uu____2336 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2336 None))
in (FStar_Syntax_Syntax.as_arg uu____2335))
in (uu____2334)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2333))
in (uu____2332 None FStar_Range.dummyRange))) ibs1 fml1)
in (

let fml3 = (FStar_List.fold_right (fun b t3 -> (

let uu____2358 = (

let uu____2359 = (

let uu____2360 = (

let uu____2361 = (

let uu____2362 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2362 None))
in (FStar_Syntax_Syntax.as_arg uu____2361))
in (uu____2360)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2359))
in (uu____2358 None FStar_Range.dummyRange))) bs2 fml2)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml3)
in (

let uu____2382 = acc
in (match (uu____2382) with
| (l_axioms, env, guard', cond') -> begin
(

let env1 = (FStar_TypeChecker_Env.push_binders env bs2)
in (

let env2 = (FStar_TypeChecker_Env.push_binders env1 ibs1)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2416, uu____2417, uu____2418, t_lid, uu____2420, uu____2421, uu____2422) -> begin
(t_lid = lid)
end
| uu____2427 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let cond = (FStar_List.fold_left (fun acc1 d -> (

let uu____2431 = (optimized_haseq_soundness_for_data lid d usubst bs2)
in (FStar_Syntax_Util.mk_conj acc1 uu____2431))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (

let uu____2433 = (FStar_Syntax_Util.mk_conj guard' guard)
in (

let uu____2436 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml3)))::[]))), (env2), (uu____2433), (uu____2436)))))))))
end)))))))))))))))
end))))
end)))


let optimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 tc_assume -> (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2502, us, uu____2504, uu____2505, uu____2506, uu____2507, uu____2508) -> begin
us
end
| uu____2515 -> begin
(failwith "Impossible!")
end))
in (

let uu____2516 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____2516) with
| (usubst, us1) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env us1)
in (

let uu____2532 = (FStar_List.fold_left (optimized_haseq_ty datas usubst us1) (([]), (env1), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (uu____2532) with
| (axioms, env2, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let uu____2564 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi)
in (match (uu____2564) with
| (phi1, uu____2569) -> begin
((

let uu____2571 = (FStar_TypeChecker_Env.should_verify env2)
in (match (uu____2571) with
| true -> begin
(

let uu____2572 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi1)))
in (FStar_TypeChecker_Rel.force_trivial_guard env2 uu____2572))
end
| uu____2573 -> begin
()
end));
(

let ses = (FStar_List.fold_left (fun l uu____2580 -> (match (uu____2580) with
| (lid, fml) -> begin
(

let se = (tc_assume env2 lid fml [] FStar_Range.dummyRange)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in ((env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
ses;
));
)
end)))
end)));
))
end))))


let unoptimized_haseq_data : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun usubst bs haseq_ind mutuals acc data -> (

let rec is_mutual = (fun t -> (

let uu____2623 = (

let uu____2624 = (FStar_Syntax_Subst.compress t)
in uu____2624.FStar_Syntax_Syntax.n)
in (match (uu____2623) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', uu____2634) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
(

let uu____2661 = (is_mutual t')
in (match (uu____2661) with
| true -> begin
true
end
| uu____2662 -> begin
(

let uu____2663 = (FStar_List.map Prims.fst args)
in (exists_mutual uu____2663))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t', uu____2676) -> begin
(is_mutual t')
end
| uu____2681 -> begin
false
end)))
and exists_mutual = (fun uu___80_2682 -> (match (uu___80_2682) with
| [] -> begin
false
end
| (hd1)::tl1 -> begin
((is_mutual hd1) || (exists_mutual tl1))
end))
in (

let dt = (datacon_typ data)
in (

let dt1 = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____2699 = (

let uu____2700 = (FStar_Syntax_Subst.compress dt1)
in uu____2700.FStar_Syntax_Syntax.n)
in (match (uu____2699) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____2706) -> begin
(

let dbs1 = (

let uu____2721 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd uu____2721))
in (

let dbs2 = (

let uu____2743 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____2743 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (

let uu____2755 = (

let uu____2756 = (

let uu____2757 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (uu____2757)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2756))
in (uu____2755 None FStar_Range.dummyRange))
in (

let haseq_sort1 = (

let uu____2763 = (is_mutual sort)
in (match (uu____2763) with
| true -> begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end
| uu____2764 -> begin
haseq_sort
end))
in (FStar_Syntax_Util.mk_conj t haseq_sort1))))) FStar_Syntax_Util.t_true dbs3)
in (

let cond1 = (FStar_List.fold_right (fun b t -> (

let uu____2770 = (

let uu____2771 = (

let uu____2772 = (

let uu____2773 = (

let uu____2774 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2774 None))
in (FStar_Syntax_Syntax.as_arg uu____2773))
in (uu____2772)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2771))
in (uu____2770 None FStar_Range.dummyRange))) dbs3 cond)
in (FStar_Syntax_Util.mk_conj acc cond1))))))
end
| uu____2791 -> begin
acc
end))))))


let unoptimized_haseq_ty = (fun all_datas_in_the_bundle mutuals usubst us acc ty -> (

let uu____2834 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2846, bs, t, uu____2849, d_lids, uu____2851) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____2859 -> begin
(failwith "Impossible!")
end)
in (match (uu____2834) with
| (lid, bs, t, d_lids) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t1 = (

let uu____2875 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst)
in (FStar_Syntax_Subst.subst uu____2875 t))
in (

let uu____2882 = (FStar_Syntax_Subst.open_term bs1 t1)
in (match (uu____2882) with
| (bs2, t2) -> begin
(

let ibs = (

let uu____2893 = (

let uu____2894 = (FStar_Syntax_Subst.compress t2)
in uu____2894.FStar_Syntax_Syntax.n)
in (match (uu____2893) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____2901) -> begin
ibs
end
| uu____2912 -> begin
[]
end))
in (

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____2917 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____2918 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____2917 uu____2918)))
in (

let ind1 = (

let uu____2923 = (

let uu____2924 = (FStar_List.map (fun uu____2929 -> (match (uu____2929) with
| (bv, aq) -> begin
(

let uu____2936 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2936), (aq)))
end)) bs2)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____2924))
in (uu____2923 None FStar_Range.dummyRange))
in (

let ind2 = (

let uu____2944 = (

let uu____2945 = (FStar_List.map (fun uu____2950 -> (match (uu____2950) with
| (bv, aq) -> begin
(

let uu____2957 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2957), (aq)))
end)) ibs1)
in (FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2945))
in (uu____2944 None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____2965 = (

let uu____2966 = (

let uu____2967 = (FStar_Syntax_Syntax.as_arg ind2)
in (uu____2967)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2966))
in (uu____2965 None FStar_Range.dummyRange))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2975, uu____2976, uu____2977, t_lid, uu____2979, uu____2980, uu____2981) -> begin
(t_lid = lid)
end
| uu____2986 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let data_cond = (FStar_List.fold_left (unoptimized_haseq_data usubst bs2 haseq_ind mutuals) FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml1 = (

let uu___89_2992 = fml
in (

let uu____2993 = (

let uu____2994 = (

let uu____2999 = (

let uu____3000 = (

let uu____3007 = (

let uu____3009 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____3009)::[])
in (uu____3007)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____3000))
in ((fml), (uu____2999)))
in FStar_Syntax_Syntax.Tm_meta (uu____2994))
in {FStar_Syntax_Syntax.n = uu____2993; FStar_Syntax_Syntax.tk = uu___89_2992.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___89_2992.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___89_2992.FStar_Syntax_Syntax.vars}))
in (

let fml2 = (FStar_List.fold_right (fun b t3 -> (

let uu____3021 = (

let uu____3022 = (

let uu____3023 = (

let uu____3024 = (

let uu____3025 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____3025 None))
in (FStar_Syntax_Syntax.as_arg uu____3024))
in (uu____3023)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____3022))
in (uu____3021 None FStar_Range.dummyRange))) ibs1 fml1)
in (

let fml3 = (FStar_List.fold_right (fun b t3 -> (

let uu____3047 = (

let uu____3048 = (

let uu____3049 = (

let uu____3050 = (

let uu____3051 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____3051 None))
in (FStar_Syntax_Syntax.as_arg uu____3050))
in (uu____3049)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____3048))
in (uu____3047 None FStar_Range.dummyRange))) bs2 fml2)
in (FStar_Syntax_Util.mk_conj acc fml3)))))))))))))
end))))
end)))


let unoptimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 tc_assume -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3120, uu____3121, uu____3122, uu____3123, uu____3124, uu____3125) -> begin
lid
end
| uu____3132 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let uu____3133 = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, uu____3141, uu____3142, uu____3143, uu____3144, uu____3145) -> begin
((lid), (us))
end
| uu____3152 -> begin
(failwith "Impossible!")
end))
in (match (uu____3133) with
| (lid, us) -> begin
(

let uu____3158 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____3158) with
| (usubst, us1) -> begin
(

let fml = (FStar_List.fold_left (unoptimized_haseq_ty datas mutuals usubst us1) FStar_Syntax_Util.t_true tcs)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env us1)
in (

let se = (

let uu____3176 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env1 uu____3176 fml [] FStar_Range.dummyRange))
in ((env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
(se)::[];
)));
)))
end))
end))))


let check_inductive_well_typedness : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let uu____3206 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___81_3216 -> (match (uu___81_3216) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____3217); FStar_Syntax_Syntax.sigrng = uu____3218} -> begin
true
end
| uu____3229 -> begin
false
end))))
in (match (uu____3206) with
| (tys, datas) -> begin
((

let uu____3242 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun uu___82_3244 -> (match (uu___82_3244) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____3245); FStar_Syntax_Syntax.sigrng = uu____3246} -> begin
false
end
| uu____3256 -> begin
true
end))))
in (match (uu____3242) with
| true -> begin
(

let uu____3257 = (

let uu____3258 = (

let uu____3261 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (uu____3261)))
in FStar_Errors.Error (uu____3258))
in (Prims.raise uu____3257))
end
| uu____3262 -> begin
()
end));
(

let env0 = env
in (

let uu____3264 = (FStar_List.fold_right (fun tc uu____3278 -> (match (uu____3278) with
| (env1, all_tcs, g) -> begin
(

let uu____3300 = (tc_tycon env1 tc)
in (match (uu____3300) with
| (env2, tc1, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in ((

let uu____3317 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Low)
in (match (uu____3317) with
| true -> begin
(

let uu____3318 = (FStar_Syntax_Print.sigelt_to_string tc1)
in (FStar_Util.print1 "Checked inductive: %s\n" uu____3318))
end
| uu____3319 -> begin
()
end));
(

let uu____3320 = (

let uu____3321 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g uu____3321))
in ((env2), ((((tc1), (tc_u)))::all_tcs), (uu____3320)));
))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____3264) with
| (env1, tcs, g) -> begin
(

let uu____3346 = (FStar_List.fold_right (fun se uu____3354 -> (match (uu____3354) with
| (datas1, g1) -> begin
(

let uu____3365 = (

let uu____3368 = (tc_data env1 tcs)
in (uu____3368 se))
in (match (uu____3365) with
| (data, g') -> begin
(

let uu____3378 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in (((data)::datas1), (uu____3378)))
end))
end)) datas (([]), (g)))
in (match (uu____3346) with
| (datas1, g1) -> begin
(

let uu____3390 = (generalize_and_inst_within env0 g1 tcs datas1)
in (match (uu____3390) with
| (tcs1, datas2) -> begin
(

let sig_bndle = (

let uu____3407 = (FStar_TypeChecker_Env.get_range env0)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((FStar_List.append tcs1 datas2)), (quals), (lids))); FStar_Syntax_Syntax.sigrng = uu____3407})
in ((sig_bndle), (tcs1), (datas2)))
end))
end))
end)));
)
end)))




