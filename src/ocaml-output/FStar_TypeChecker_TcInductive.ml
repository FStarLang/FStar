
open Prims

let tc_tycon : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_TypeChecker_Env.env_t * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let uu____34 = (FStar_Syntax_Subst.open_term tps k)
in (match (uu____34) with
| (tps1, k1) -> begin
(

let uu____43 = (FStar_TypeChecker_TcTerm.tc_binders env tps1)
in (match (uu____43) with
| (tps2, env_tps, guard_params, us) -> begin
(

let uu____56 = (FStar_Syntax_Util.arrow_formals k1)
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

let k2 = (

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

let k3 = (FStar_Syntax_Subst.close tps3 k2)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____142 = (FStar_TypeChecker_Env.push_let_binding env (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((uu____142), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps3), (k3), (mutuals), (data), (quals), (r)))), (u), (guard)))))));
)
end)))
end))
end))
end))
end))
end))
end
| uu____150 -> begin
(failwith "impossible")
end))


let tc_data : FStar_TypeChecker_Env.env_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.guard_t) = (fun env tcs uu___79_175 -> (match (uu___79_175) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let uu____191 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun uu____205 -> (match (uu____205) with
| (se, u_tc) -> begin
(

let uu____214 = (

let uu____215 = (

let uu____216 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must uu____216))
in (FStar_Ident.lid_equals tc_lid uu____215))
in (match (uu____214) with
| true -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____226, uu____227, tps, uu____229, uu____230, uu____231, uu____232, uu____233) -> begin
(

let tps1 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____254 -> (match (uu____254) with
| (x, uu____261) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let tps2 = (FStar_Syntax_Subst.open_binders tps1)
in (

let uu____264 = (

let uu____268 = (FStar_TypeChecker_Env.push_binders env tps2)
in ((uu____268), (tps2), (u_tc)))
in Some (uu____264))))
end
| uu____272 -> begin
(failwith "Impossible")
end)
end
| uu____277 -> begin
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
| uu____302 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected data constructor"), (r)))))
end)
end))
in (match (uu____191) with
| (env1, tps, u_tc) -> begin
(

let uu____311 = (

let uu____319 = (

let uu____320 = (FStar_Syntax_Subst.compress t)
in uu____320.FStar_Syntax_Syntax.n)
in (match (uu____319) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let uu____342 = (FStar_Util.first_N ntps bs)
in (match (uu____342) with
| (uu____360, bs') -> begin
(

let t1 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res))))) None t.FStar_Syntax_Syntax.pos)
in (

let subst1 = (FStar_All.pipe_right tps (FStar_List.mapi (fun i uu____396 -> (match (uu____396) with
| (x, uu____400) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (

let uu____401 = (FStar_Syntax_Subst.subst subst1 t1)
in (FStar_Syntax_Util.arrow_formals uu____401))))
end))
end
| uu____402 -> begin
(([]), (t))
end))
in (match (uu____311) with
| (arguments, result) -> begin
((

let uu____423 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____423) with
| true -> begin
(

let uu____424 = (FStar_Syntax_Print.lid_to_string c)
in (

let uu____425 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (

let uu____426 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" uu____424 uu____425 uu____426))))
end
| uu____427 -> begin
()
end));
(

let uu____428 = (FStar_TypeChecker_TcTerm.tc_tparams env1 arguments)
in (match (uu____428) with
| (arguments1, env', us) -> begin
(

let uu____437 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (uu____437) with
| (result1, res_lcomp) -> begin
((

let uu____445 = (

let uu____446 = (FStar_Syntax_Subst.compress res_lcomp.FStar_Syntax_Syntax.res_typ)
in uu____446.FStar_Syntax_Syntax.n)
in (match (uu____445) with
| FStar_Syntax_Syntax.Tm_type (uu____449) -> begin
()
end
| ty -> begin
(

let uu____451 = (

let uu____452 = (

let uu____455 = (

let uu____456 = (FStar_Syntax_Print.term_to_string result1)
in (

let uu____457 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" uu____456 uu____457)))
in ((uu____455), (r)))
in FStar_Errors.Error (uu____452))
in (Prims.raise uu____451))
end));
(

let uu____458 = (FStar_Syntax_Util.head_and_args result1)
in (match (uu____458) with
| (head1, uu____471) -> begin
((

let uu____487 = (

let uu____488 = (FStar_Syntax_Subst.compress head1)
in uu____488.FStar_Syntax_Syntax.n)
in (match (uu____487) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| uu____492 -> begin
(

let uu____493 = (

let uu____494 = (

let uu____497 = (

let uu____498 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (

let uu____499 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" uu____498 uu____499)))
in ((uu____497), (r)))
in FStar_Errors.Error (uu____494))
in (Prims.raise uu____493))
end));
(

let g = (FStar_List.fold_left2 (fun g uu____504 u_x -> (match (uu____504) with
| (x, uu____509) -> begin
(

let uu____510 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g uu____510))
end)) FStar_TypeChecker_Rel.trivial_guard arguments1 us)
in (

let t1 = (

let uu____514 = (

let uu____518 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____532 -> (match (uu____532) with
| (x, uu____539) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append uu____518 arguments1))
in (

let uu____544 = (FStar_Syntax_Syntax.mk_Total result1)
in (FStar_Syntax_Util.arrow uu____514 uu____544)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t1), (tc_lid), (ntps), (quals), ([]), (r)))), (g))));
)
end));
)
end))
end));
)
end))
end))
end
| uu____552 -> begin
(failwith "impossible")
end))


let generalize_and_inst_within : FStar_TypeChecker_Env.env_t  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env g tcs datas -> (

let tc_universe_vars = (FStar_List.map Prims.snd tcs)
in (

let g1 = (

let uu___85_588 = g
in {FStar_TypeChecker_Env.guard_f = uu___85_588.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___85_588.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((tc_universe_vars), ((Prims.snd g.FStar_TypeChecker_Env.univ_ineqs))); FStar_TypeChecker_Env.implicits = uu___85_588.FStar_TypeChecker_Env.implicits})
in ((

let uu____594 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____594) with
| true -> begin
(

let uu____595 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "@@@@@@Guard before generalization: %s\n" uu____595))
end
| uu____596 -> begin
()
end));
(FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun uu____606 -> (match (uu____606) with
| (se, uu____610) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____611, uu____612, tps, k, uu____615, uu____616, uu____617, uu____618) -> begin
(

let uu____625 = (

let uu____626 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) uu____626))
in (FStar_Syntax_Syntax.null_binder uu____625))
end
| uu____633 -> begin
(failwith "Impossible")
end)
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun uu___80_638 -> (match (uu___80_638) with
| FStar_Syntax_Syntax.Sig_datacon (uu____639, uu____640, t, uu____642, uu____643, uu____644, uu____645, uu____646) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| uu____651 -> begin
(failwith "Impossible")
end))))
in (

let t = (

let uu____655 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') uu____655))
in ((

let uu____659 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____659) with
| true -> begin
(

let uu____660 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" uu____660))
end
| uu____661 -> begin
()
end));
(

let uu____662 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (uu____662) with
| (uvs, t1) -> begin
((

let uu____672 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____672) with
| true -> begin
(

let uu____673 = (

let uu____674 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right uu____674 (FStar_String.concat ", ")))
in (

let uu____680 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" uu____673 uu____680)))
end
| uu____681 -> begin
()
end));
(

let uu____682 = (FStar_Syntax_Subst.open_univ_vars uvs t1)
in (match (uu____682) with
| (uvs1, t2) -> begin
(

let uu____691 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____691) with
| (args, uu____704) -> begin
(

let uu____715 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (uu____715) with
| (tc_types, data_types) -> begin
(

let tcs1 = (FStar_List.map2 (fun uu____752 uu____753 -> (match (((uu____752), (uu____753))) with
| ((x, uu____763), (se, uu____765)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____771, tps, uu____773, mutuals, datas1, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs1 x.FStar_Syntax_Syntax.sort)
in (

let uu____785 = (

let uu____793 = (

let uu____794 = (FStar_Syntax_Subst.compress ty)
in uu____794.FStar_Syntax_Syntax.n)
in (match (uu____793) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c) -> begin
(

let uu____816 = (FStar_Util.first_N (FStar_List.length tps) binders1)
in (match (uu____816) with
| (tps1, rest) -> begin
(

let t3 = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____859 -> begin
(

let uu____863 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c))))) uu____863 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps1), (t3)))
end))
end
| uu____886 -> begin
(([]), (ty))
end))
in (match (uu____785) with
| (tps1, t3) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs1), (tps1), (t3), (mutuals), (datas1), (quals), (r)))
end)))
end
| uu____912 -> begin
(failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas1 = (match (uvs1) with
| [] -> begin
datas
end
| uu____916 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs1 (FStar_List.map (fun _0_28 -> FStar_Syntax_Syntax.U_name (_0_28))))
in (

let tc_insts = (FStar_All.pipe_right tcs1 (FStar_List.map (fun uu___81_933 -> (match (uu___81_933) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____938, uu____939, uu____940, uu____941, uu____942, uu____943, uu____944) -> begin
((tc), (uvs_universes))
end
| uu____952 -> begin
(failwith "Impossible")
end))))
in (FStar_List.map2 (fun uu____958 d -> (match (uu____958) with
| (t3, uu____963) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____965, uu____966, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (

let uu____977 = (FStar_Syntax_InstFV.instantiate tc_insts t3.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____977 (FStar_Syntax_Subst.close_univ_vars uvs1)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs1), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| uu____980 -> begin
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

let uu____989 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Positivity")))
in (match (uu____989) with
| true -> begin
(FStar_Util.print_string (Prims.strcat "Positivity::" (Prims.strcat s "\n")))
end
| uu____990 -> begin
()
end)))


let ty_occurs_in : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun ty_lid t -> (

let uu____997 = (FStar_Syntax_Free.fvars t)
in (FStar_Util.set_mem ty_lid uu____997)))


let try_get_fv : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes) = (fun t -> (

let uu____1006 = (

let uu____1007 = (FStar_Syntax_Subst.compress t)
in uu____1007.FStar_Syntax_Syntax.n)
in (match (uu____1006) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), (us))
end
| uu____1023 -> begin
(failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
end)
end
| uu____1026 -> begin
(failwith "Node is not an fvar or a Tm_uinst")
end)))


type unfolded_memo_elt =
(FStar_Ident.lident * FStar_Syntax_Syntax.args) Prims.list


type unfolded_memo_t =
unfolded_memo_elt FStar_ST.ref


let already_unfolded : FStar_Ident.lident  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ilid arrghs unfolded env -> (

let uu____1045 = (FStar_ST.read unfolded)
in (FStar_List.existsML (fun uu____1057 -> (match (uu____1057) with
| (lid, l) -> begin
((FStar_Ident.lid_equals lid ilid) && (

let args = (

let uu____1077 = (FStar_List.splitAt (FStar_List.length l) arrghs)
in (Prims.fst uu____1077))
in (FStar_List.fold_left2 (fun b a a' -> (b && (FStar_TypeChecker_Rel.teq_nosmt env (Prims.fst a) (Prims.fst a')))) true args l)))
end)) uu____1045)))


let rec ty_strictly_positive_in_type : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid btype unfolded env -> ((

let uu____1172 = (

let uu____1173 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity in type: " uu____1173))
in (debug_log env uu____1172));
(

let btype1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env btype)
in ((

let uu____1176 = (

let uu____1177 = (FStar_Syntax_Print.term_to_string btype1)
in (Prims.strcat "Checking strict positivity in type, after normalization: " uu____1177))
in (debug_log env uu____1176));
((

let uu____1178 = (ty_occurs_in ty_lid btype1)
in (not (uu____1178))) || ((debug_log env "ty does occur in this type, pressing ahead");
(

let uu____1180 = (

let uu____1181 = (FStar_Syntax_Subst.compress btype1)
in uu____1181.FStar_Syntax_Syntax.n)
in (match (uu____1180) with
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1200 = (try_get_fv t)
in (match (uu____1200) with
| (fv, us) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ty_lid)) with
| true -> begin
((debug_log env "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
(FStar_List.for_all (fun uu____1212 -> (match (uu____1212) with
| (t1, uu____1216) -> begin
(

let uu____1217 = (ty_occurs_in ty_lid t1)
in (not (uu____1217)))
end)) args);
)
end
| uu____1218 -> begin
((debug_log env "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
(ty_nested_positive_in_inductive ty_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v us args unfolded env);
)
end)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((debug_log env "Checking strict positivity in Tm_arrow");
(

let uu____1237 = (

let uu____1238 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____1238)))
in (match (uu____1237) with
| true -> begin
((debug_log env "Checking strict positivity , the arrow is impure, so return true");
true;
)
end
| uu____1240 -> begin
((debug_log env "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
((FStar_List.for_all (fun uu____1244 -> (match (uu____1244) with
| (b, uu____1248) -> begin
(

let uu____1249 = (ty_occurs_in ty_lid b.FStar_Syntax_Syntax.sort)
in (not (uu____1249)))
end)) sbs) && (

let uu____1250 = (FStar_Syntax_Subst.open_term sbs (FStar_Syntax_Util.comp_result c))
in (match (uu____1250) with
| (uu____1253, return_type) -> begin
(

let uu____1255 = (FStar_TypeChecker_Env.push_binders env sbs)
in (ty_strictly_positive_in_type ty_lid return_type unfolded uu____1255))
end)));
)
end));
)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1256) -> begin
((debug_log env "Checking strict positivity in an fvar, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_type (uu____1258) -> begin
((debug_log env "Checking strict positivity in an Tm_type, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____1261) -> begin
((debug_log env "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____1268) -> begin
((debug_log env "Checking strict positivity in an Tm_refine, recur in the bv sort)");
(ty_strictly_positive_in_type ty_lid bv.FStar_Syntax_Syntax.sort unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_match (uu____1274, branches) -> begin
((debug_log env "Checking strict positivity in an Tm_match, recur in the branches)");
(FStar_List.for_all (fun uu____1309 -> (match (uu____1309) with
| (p, uu____1317, t) -> begin
(

let bs = (

let uu____1327 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_List.map FStar_Syntax_Syntax.mk_binder uu____1327))
in (

let uu____1329 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____1329) with
| (bs1, t1) -> begin
(

let uu____1334 = (FStar_TypeChecker_Env.push_binders env bs1)
in (ty_strictly_positive_in_type ty_lid t1 unfolded uu____1334))
end)))
end)) branches);
)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____1336, uu____1337) -> begin
((debug_log env "Checking strict positivity in an Tm_ascribed, recur)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| uu____1367 -> begin
((

let uu____1369 = (

let uu____1370 = (

let uu____1371 = (FStar_Syntax_Print.tag_of_term btype1)
in (

let uu____1372 = (

let uu____1373 = (FStar_Syntax_Print.term_to_string btype1)
in (Prims.strcat " and term: " uu____1373))
in (Prims.strcat uu____1371 uu____1372)))
in (Prims.strcat "Checking strict positivity, unexpected tag: " uu____1370))
in (debug_log env uu____1369));
false;
)
end));
));
));
))
and ty_nested_positive_in_inductive : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid ilid us args unfolded env -> ((

let uu____1381 = (

let uu____1382 = (

let uu____1383 = (

let uu____1384 = (FStar_Syntax_Print.args_to_string args)
in (Prims.strcat " applied to arguments: " uu____1384))
in (Prims.strcat ilid.FStar_Ident.str uu____1383))
in (Prims.strcat "Checking nested positivity in the inductive " uu____1382))
in (debug_log env uu____1381));
(

let uu____1385 = (FStar_TypeChecker_Env.datacons_of_typ env ilid)
in (match (uu____1385) with
| (b, idatas) -> begin
(match ((not (b))) with
| true -> begin
((debug_log env "Checking nested positivity, not an inductive, return false");
false;
)
end
| uu____1394 -> begin
(

let uu____1395 = (already_unfolded ilid args unfolded env)
in (match (uu____1395) with
| true -> begin
((debug_log env "Checking nested positivity, we have already unfolded this inductive with these args");
true;
)
end
| uu____1397 -> begin
(

let num_ibs = (FStar_TypeChecker_Env.num_inductive_ty_params env ilid)
in ((

let uu____1400 = (

let uu____1401 = (

let uu____1402 = (FStar_Util.string_of_int num_ibs)
in (Prims.strcat uu____1402 ", also adding to the memo table"))
in (Prims.strcat "Checking nested positivity, number of type parameters is " uu____1401))
in (debug_log env uu____1400));
(

let uu____1404 = (

let uu____1405 = (FStar_ST.read unfolded)
in (

let uu____1409 = (

let uu____1413 = (

let uu____1421 = (

let uu____1427 = (FStar_List.splitAt num_ibs args)
in (Prims.fst uu____1427))
in ((ilid), (uu____1421)))
in (uu____1413)::[])
in (FStar_List.append uu____1405 uu____1409)))
in (FStar_ST.write unfolded uu____1404));
(FStar_List.for_all (fun d -> (ty_nested_positive_in_dlid ty_lid d ilid us args num_ibs unfolded env)) idatas);
))
end))
end)
end));
))
and ty_nested_positive_in_dlid : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  Prims.int  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid dlid ilid us args num_ibs unfolded env -> ((debug_log env (Prims.strcat "Checking nested positivity in data constructor " (Prims.strcat dlid.FStar_Ident.str (Prims.strcat " of the inductive " ilid.FStar_Ident.str))));
(

let uu____1485 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____1485) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____1497 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let dt1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env dt)
in ((

let uu____1500 = (

let uu____1501 = (FStar_Syntax_Print.term_to_string dt1)
in (Prims.strcat "Checking nested positivity in the data constructor type: " uu____1501))
in (debug_log env uu____1500));
(

let uu____1502 = (

let uu____1503 = (FStar_Syntax_Subst.compress dt1)
in uu____1503.FStar_Syntax_Syntax.n)
in (match (uu____1502) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, c) -> begin
((debug_log env "Checked nested positivity in Tm_arrow data constructor type");
(

let uu____1519 = (FStar_List.splitAt num_ibs dbs)
in (match (uu____1519) with
| (ibs, dbs1) -> begin
(

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let dbs2 = (

let uu____1546 = (FStar_Syntax_Subst.opening_of_binders ibs1)
in (FStar_Syntax_Subst.subst_binders uu____1546 dbs1))
in (

let c1 = (

let uu____1549 = (FStar_Syntax_Subst.opening_of_binders ibs1)
in (FStar_Syntax_Subst.subst_comp uu____1549 c))
in (

let uu____1551 = (FStar_List.splitAt num_ibs args)
in (match (uu____1551) with
| (args1, uu____1569) -> begin
(

let subst1 = (FStar_List.fold_left2 (fun subst1 ib arg -> (FStar_List.append subst1 ((FStar_Syntax_Syntax.NT ((((Prims.fst ib)), ((Prims.fst arg)))))::[]))) [] ibs1 args1)
in (

let dbs3 = (FStar_Syntax_Subst.subst_binders subst1 dbs2)
in (

let c2 = (

let uu____1615 = (FStar_Syntax_Subst.shift_subst (FStar_List.length dbs3) subst1)
in (FStar_Syntax_Subst.subst_comp uu____1615 c1))
in ((

let uu____1623 = (

let uu____1624 = (

let uu____1625 = (FStar_Syntax_Print.binders_to_string "; " dbs3)
in (

let uu____1626 = (

let uu____1627 = (FStar_Syntax_Print.comp_to_string c2)
in (Prims.strcat ", and c: " uu____1627))
in (Prims.strcat uu____1625 uu____1626)))
in (Prims.strcat "Checking nested positivity in the unfolded data constructor binders as: " uu____1624))
in (debug_log env uu____1623));
(ty_nested_positive_in_type ty_lid (FStar_Syntax_Syntax.Tm_arrow (((dbs3), (c2)))) ilid num_ibs unfolded env);
))))
end)))))
end));
)
end
| uu____1628 -> begin
((debug_log env "Checking nested positivity in the data constructor type that is not an arrow");
(

let uu____1630 = (

let uu____1631 = (FStar_Syntax_Subst.compress dt1)
in uu____1631.FStar_Syntax_Syntax.n)
in (ty_nested_positive_in_type ty_lid uu____1630 ilid num_ibs unfolded env));
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

let uu____1657 = (try_get_fv t1)
in (match (uu____1657) with
| (fv, uu____1661) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ilid)) with
| true -> begin
true
end
| uu____1666 -> begin
(failwith "Impossible, expected the type to be ilid")
end)
end));
)
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((

let uu____1680 = (

let uu____1681 = (FStar_Syntax_Print.binders_to_string "; " sbs)
in (Prims.strcat "Checking nested positivity in an Tm_arrow node, with binders as: " uu____1681))
in (debug_log env uu____1680));
(

let uu____1682 = (FStar_List.fold_left (fun uu____1689 b -> (match (uu____1689) with
| (r, env1) -> begin
(match ((not (r))) with
| true -> begin
((r), (env1))
end
| uu____1701 -> begin
(

let uu____1702 = (ty_strictly_positive_in_type ty_lid (Prims.fst b).FStar_Syntax_Syntax.sort unfolded env1)
in (

let uu____1703 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((uu____1702), (uu____1703))))
end)
end)) ((true), (env)) sbs)
in (match (uu____1682) with
| (b, uu____1709) -> begin
b
end));
)
end
| uu____1710 -> begin
(failwith "Nested positive check, unhandled case")
end))


let ty_positive_in_datacon : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.universes  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty_lid dlid ty_bs us unfolded env -> (

let uu____1729 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____1729) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____1741 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let uu____1743 = (

let uu____1744 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking data constructor type: " uu____1744))
in (debug_log env uu____1743));
(

let uu____1745 = (

let uu____1746 = (FStar_Syntax_Subst.compress dt)
in uu____1746.FStar_Syntax_Syntax.n)
in (match (uu____1745) with
| FStar_Syntax_Syntax.Tm_fvar (uu____1749) -> begin
((debug_log env "Data constructor type is simply an fvar, returning true");
true;
)
end
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____1752) -> begin
(

let dbs1 = (

let uu____1767 = (FStar_List.splitAt (FStar_List.length ty_bs) dbs)
in (Prims.snd uu____1767))
in (

let dbs2 = (

let uu____1789 = (FStar_Syntax_Subst.opening_of_binders ty_bs)
in (FStar_Syntax_Subst.subst_binders uu____1789 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in ((

let uu____1793 = (

let uu____1794 = (

let uu____1795 = (FStar_Util.string_of_int (FStar_List.length dbs3))
in (Prims.strcat uu____1795 " binders"))
in (Prims.strcat "Data constructor type is an arrow type, so checking strict positivity in " uu____1794))
in (debug_log env uu____1793));
(

let uu____1801 = (FStar_List.fold_left (fun uu____1808 b -> (match (uu____1808) with
| (r, env1) -> begin
(match ((not (r))) with
| true -> begin
((r), (env1))
end
| uu____1820 -> begin
(

let uu____1821 = (ty_strictly_positive_in_type ty_lid (Prims.fst b).FStar_Syntax_Syntax.sort unfolded env1)
in (

let uu____1822 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((uu____1821), (uu____1822))))
end)
end)) ((true), (env)) dbs3)
in (match (uu____1801) with
| (b, uu____1828) -> begin
b
end));
))))
end
| FStar_Syntax_Syntax.Tm_app (uu____1829, uu____1830) -> begin
((debug_log env "Data constructor type is a Tm_app, so returning true");
true;
)
end
| uu____1846 -> begin
(failwith "Unexpected data constructor type when checking positivity")
end));
)
end)))


let check_positivity : FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty env -> (

let unfolded_inductives = (FStar_Util.mk_ref [])
in (

let uu____1864 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, bs, uu____1874, uu____1875, uu____1876, uu____1877, uu____1878) -> begin
((lid), (us), (bs))
end
| uu____1885 -> begin
(failwith "Impossible!")
end)
in (match (uu____1864) with
| (ty_lid, ty_us, ty_bs) -> begin
(

let uu____1892 = (FStar_Syntax_Subst.univ_var_opening ty_us)
in (match (uu____1892) with
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

let uu____1907 = (

let uu____1909 = (FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid)
in (Prims.snd uu____1909))
in (FStar_List.for_all (fun d -> (

let uu____1915 = (FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name (s)) ty_us1)
in (ty_positive_in_datacon ty_lid d ty_bs2 uu____1915 unfolded_inductives env2))) uu____1907))))))
end))
end))))


let datacon_typ : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1922, uu____1923, t, uu____1925, uu____1926, uu____1927, uu____1928, uu____1929) -> begin
t
end
| uu____1934 -> begin
(failwith "Impossible!")
end))


let optimized_haseq_soundness_for_data : FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term = (fun ty_lid data usubst bs -> (

let dt = (datacon_typ data)
in (

let dt1 = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____1951 = (

let uu____1952 = (FStar_Syntax_Subst.compress dt1)
in uu____1952.FStar_Syntax_Syntax.n)
in (match (uu____1951) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____1956) -> begin
(

let dbs1 = (

let uu____1971 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd uu____1971))
in (

let dbs2 = (

let uu____1993 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____1993 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (

let uu____2002 = (

let uu____2003 = (

let uu____2004 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (uu____2004)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2003))
in (uu____2002 None FStar_Range.dummyRange))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b1 = (

let uu____2011 = (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" ty_lid.FStar_Ident.str)
in (FStar_TypeChecker_Util.label uu____2011 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b1))))) FStar_Syntax_Util.t_true dbs3)
in (FStar_List.fold_right (fun b t -> (

let uu____2016 = (

let uu____2017 = (

let uu____2018 = (

let uu____2019 = (

let uu____2020 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2020 None))
in (FStar_Syntax_Syntax.as_arg uu____2019))
in (uu____2018)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2017))
in (uu____2016 None FStar_Range.dummyRange))) dbs3 cond)))))
end
| uu____2037 -> begin
FStar_Syntax_Util.t_true
end)))))


let optimized_haseq_ty = (fun all_datas_in_the_bundle usubst us acc ty -> (

let uu____2096 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2108, bs, t, uu____2111, d_lids, uu____2113, uu____2114) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____2122 -> begin
(failwith "Impossible!")
end)
in (match (uu____2096) with
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

let uu___86_2303 = fml
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
in {FStar_Syntax_Syntax.n = uu____2304; FStar_Syntax_Syntax.tk = uu___86_2303.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___86_2303.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___86_2303.FStar_Syntax_Syntax.vars}))
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

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2416, uu____2417, uu____2418, t_lid, uu____2420, uu____2421, uu____2422, uu____2423) -> begin
(t_lid = lid)
end
| uu____2428 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let cond = (FStar_List.fold_left (fun acc1 d -> (

let uu____2432 = (optimized_haseq_soundness_for_data lid d usubst bs2)
in (FStar_Syntax_Util.mk_conj acc1 uu____2432))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (

let uu____2434 = (FStar_Syntax_Util.mk_conj guard' guard)
in (

let uu____2437 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml3)))::[]))), (env2), (uu____2434), (uu____2437)))))))))
end)))))))))))))))
end))))
end)))


let optimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 tc_assume -> (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2503, us, uu____2505, uu____2506, uu____2507, uu____2508, uu____2509, uu____2510) -> begin
us
end
| uu____2517 -> begin
(failwith "Impossible!")
end))
in (

let uu____2518 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____2518) with
| (usubst, us1) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env us1)
in (

let uu____2534 = (FStar_List.fold_left (optimized_haseq_ty datas usubst us1) (([]), (env1), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (uu____2534) with
| (axioms, env2, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let uu____2566 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi)
in (match (uu____2566) with
| (phi1, uu____2571) -> begin
((

let uu____2573 = (FStar_TypeChecker_Env.should_verify env2)
in (match (uu____2573) with
| true -> begin
(

let uu____2574 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi1)))
in (FStar_TypeChecker_Rel.force_trivial_guard env2 uu____2574))
end
| uu____2575 -> begin
()
end));
(

let ses = (FStar_List.fold_left (fun l uu____2582 -> (match (uu____2582) with
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

let uu____2625 = (

let uu____2626 = (FStar_Syntax_Subst.compress t)
in uu____2626.FStar_Syntax_Syntax.n)
in (match (uu____2625) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', uu____2636) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
(

let uu____2663 = (is_mutual t')
in (match (uu____2663) with
| true -> begin
true
end
| uu____2664 -> begin
(

let uu____2665 = (FStar_List.map Prims.fst args)
in (exists_mutual uu____2665))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t', uu____2678) -> begin
(is_mutual t')
end
| uu____2683 -> begin
false
end)))
and exists_mutual = (fun uu___82_2684 -> (match (uu___82_2684) with
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

let uu____2701 = (

let uu____2702 = (FStar_Syntax_Subst.compress dt1)
in uu____2702.FStar_Syntax_Syntax.n)
in (match (uu____2701) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____2708) -> begin
(

let dbs1 = (

let uu____2723 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd uu____2723))
in (

let dbs2 = (

let uu____2745 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____2745 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (

let uu____2757 = (

let uu____2758 = (

let uu____2759 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (uu____2759)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2758))
in (uu____2757 None FStar_Range.dummyRange))
in (

let haseq_sort1 = (

let uu____2765 = (is_mutual sort)
in (match (uu____2765) with
| true -> begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end
| uu____2766 -> begin
haseq_sort
end))
in (FStar_Syntax_Util.mk_conj t haseq_sort1))))) FStar_Syntax_Util.t_true dbs3)
in (

let cond1 = (FStar_List.fold_right (fun b t -> (

let uu____2772 = (

let uu____2773 = (

let uu____2774 = (

let uu____2775 = (

let uu____2776 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2776 None))
in (FStar_Syntax_Syntax.as_arg uu____2775))
in (uu____2774)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2773))
in (uu____2772 None FStar_Range.dummyRange))) dbs3 cond)
in (FStar_Syntax_Util.mk_conj acc cond1))))))
end
| uu____2793 -> begin
acc
end))))))


let unoptimized_haseq_ty = (fun all_datas_in_the_bundle mutuals usubst us acc ty -> (

let uu____2836 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2848, bs, t, uu____2851, d_lids, uu____2853, uu____2854) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____2862 -> begin
(failwith "Impossible!")
end)
in (match (uu____2836) with
| (lid, bs, t, d_lids) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t1 = (

let uu____2878 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst)
in (FStar_Syntax_Subst.subst uu____2878 t))
in (

let uu____2885 = (FStar_Syntax_Subst.open_term bs1 t1)
in (match (uu____2885) with
| (bs2, t2) -> begin
(

let ibs = (

let uu____2896 = (

let uu____2897 = (FStar_Syntax_Subst.compress t2)
in uu____2897.FStar_Syntax_Syntax.n)
in (match (uu____2896) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____2904) -> begin
ibs
end
| uu____2915 -> begin
[]
end))
in (

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____2920 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____2921 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____2920 uu____2921)))
in (

let ind1 = (

let uu____2926 = (

let uu____2927 = (FStar_List.map (fun uu____2932 -> (match (uu____2932) with
| (bv, aq) -> begin
(

let uu____2939 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2939), (aq)))
end)) bs2)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____2927))
in (uu____2926 None FStar_Range.dummyRange))
in (

let ind2 = (

let uu____2947 = (

let uu____2948 = (FStar_List.map (fun uu____2953 -> (match (uu____2953) with
| (bv, aq) -> begin
(

let uu____2960 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2960), (aq)))
end)) ibs1)
in (FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2948))
in (uu____2947 None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____2968 = (

let uu____2969 = (

let uu____2970 = (FStar_Syntax_Syntax.as_arg ind2)
in (uu____2970)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2969))
in (uu____2968 None FStar_Range.dummyRange))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2978, uu____2979, uu____2980, t_lid, uu____2982, uu____2983, uu____2984, uu____2985) -> begin
(t_lid = lid)
end
| uu____2990 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let data_cond = (FStar_List.fold_left (unoptimized_haseq_data usubst bs2 haseq_ind mutuals) FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml1 = (

let uu___87_2996 = fml
in (

let uu____2997 = (

let uu____2998 = (

let uu____3003 = (

let uu____3004 = (

let uu____3011 = (

let uu____3013 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____3013)::[])
in (uu____3011)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____3004))
in ((fml), (uu____3003)))
in FStar_Syntax_Syntax.Tm_meta (uu____2998))
in {FStar_Syntax_Syntax.n = uu____2997; FStar_Syntax_Syntax.tk = uu___87_2996.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___87_2996.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___87_2996.FStar_Syntax_Syntax.vars}))
in (

let fml2 = (FStar_List.fold_right (fun b t3 -> (

let uu____3025 = (

let uu____3026 = (

let uu____3027 = (

let uu____3028 = (

let uu____3029 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____3029 None))
in (FStar_Syntax_Syntax.as_arg uu____3028))
in (uu____3027)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____3026))
in (uu____3025 None FStar_Range.dummyRange))) ibs1 fml1)
in (

let fml3 = (FStar_List.fold_right (fun b t3 -> (

let uu____3051 = (

let uu____3052 = (

let uu____3053 = (

let uu____3054 = (

let uu____3055 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____3055 None))
in (FStar_Syntax_Syntax.as_arg uu____3054))
in (uu____3053)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____3052))
in (uu____3051 None FStar_Range.dummyRange))) bs2 fml2)
in (FStar_Syntax_Util.mk_conj acc fml3)))))))))))))
end))))
end)))


let unoptimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 tc_assume -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3124, uu____3125, uu____3126, uu____3127, uu____3128, uu____3129, uu____3130) -> begin
lid
end
| uu____3137 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let uu____3138 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, uu____3146, uu____3147, uu____3148, uu____3149, uu____3150, uu____3151) -> begin
((lid), (us))
end
| uu____3158 -> begin
(failwith "Impossible!")
end))
in (match (uu____3138) with
| (lid, us) -> begin
(

let uu____3164 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____3164) with
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

let uu____3182 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env1 uu____3182 fml [] FStar_Range.dummyRange))
in ((env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
(se)::[];
)));
)))
end))
end))))


let check_inductive_well_typedness : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let uu____3212 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___83_3222 -> (match (uu___83_3222) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3223) -> begin
true
end
| uu____3235 -> begin
false
end))))
in (match (uu____3212) with
| (tys, datas) -> begin
((

let uu____3248 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun uu___84_3250 -> (match (uu___84_3250) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3251) -> begin
false
end
| uu____3262 -> begin
true
end))))
in (match (uu____3248) with
| true -> begin
(

let uu____3263 = (

let uu____3264 = (

let uu____3267 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (uu____3267)))
in FStar_Errors.Error (uu____3264))
in (Prims.raise uu____3263))
end
| uu____3268 -> begin
()
end));
(

let env0 = env
in (

let uu____3270 = (FStar_List.fold_right (fun tc uu____3284 -> (match (uu____3284) with
| (env1, all_tcs, g) -> begin
(

let uu____3306 = (tc_tycon env1 tc)
in (match (uu____3306) with
| (env2, tc1, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in ((

let uu____3323 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Low)
in (match (uu____3323) with
| true -> begin
(

let uu____3324 = (FStar_Syntax_Print.sigelt_to_string tc1)
in (FStar_Util.print1 "Checked inductive: %s\n" uu____3324))
end
| uu____3325 -> begin
()
end));
(

let uu____3326 = (

let uu____3327 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g uu____3327))
in ((env2), ((((tc1), (tc_u)))::all_tcs), (uu____3326)));
))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____3270) with
| (env1, tcs, g) -> begin
(

let uu____3352 = (FStar_List.fold_right (fun se uu____3360 -> (match (uu____3360) with
| (datas1, g1) -> begin
(

let uu____3371 = (

let uu____3374 = (tc_data env1 tcs)
in (uu____3374 se))
in (match (uu____3371) with
| (data, g') -> begin
(

let uu____3384 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in (((data)::datas1), (uu____3384)))
end))
end)) datas (([]), (g)))
in (match (uu____3352) with
| (datas1, g1) -> begin
(

let uu____3396 = (generalize_and_inst_within env0 g1 tcs datas1)
in (match (uu____3396) with
| (tcs1, datas2) -> begin
(

let sig_bndle = (

let uu____3413 = (

let uu____3421 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs1 datas2)), (quals), (lids), (uu____3421)))
in FStar_Syntax_Syntax.Sig_bundle (uu____3413))
in ((sig_bndle), (tcs1), (datas2)))
end))
end))
end)));
)
end)))




