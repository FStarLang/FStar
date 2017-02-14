
open Prims

let tc_tycon : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_TypeChecker_Env.env_t * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let uu____34 = (FStar_Syntax_Subst.open_term tps k)
in (match (uu____34) with
| (tps, k) -> begin
(

let uu____43 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (uu____43) with
| (tps, env_tps, guard_params, us) -> begin
(

let uu____56 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____56) with
| (indices, t) -> begin
(

let uu____80 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (uu____80) with
| (indices, env', guard_indices, us') -> begin
(

let uu____93 = (

let uu____96 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (uu____96) with
| (t, uu____103, g) -> begin
(

let uu____105 = (

let uu____106 = (

let uu____107 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params uu____107))
in (FStar_TypeChecker_Rel.discharge_guard env' uu____106))
in ((t), (uu____105)))
end))
in (match (uu____93) with
| (t, guard) -> begin
(

let k = (

let uu____117 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices uu____117))
in (

let uu____120 = (FStar_Syntax_Util.type_u ())
in (match (uu____120) with
| (t_type, u) -> begin
((

let uu____130 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' uu____130));
(

let t_tc = (

let uu____134 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) uu____134))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____142 = (FStar_TypeChecker_Env.push_let_binding env (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((uu____142), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard)))))));
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


let tc_data : FStar_TypeChecker_Env.env_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.guard_t) = (fun env tcs uu___76_175 -> (match (uu___76_175) with
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

let tps = (FStar_All.pipe_right tps (FStar_List.map (fun uu____254 -> (match (uu____254) with
| (x, uu____261) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let tps = (FStar_Syntax_Subst.open_binders tps)
in (

let uu____264 = (

let uu____268 = (FStar_TypeChecker_Env.push_binders env tps)
in ((uu____268), (tps), (u_tc)))
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
| (env, tps, u_tc) -> begin
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

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res))))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i uu____396 -> (match (uu____396) with
| (x, uu____400) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (

let uu____401 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals uu____401))))
end))
end
| uu____402 -> begin
(([]), (t))
end))
in (match (uu____311) with
| (arguments, result) -> begin
((

let uu____423 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
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

let uu____428 = (FStar_TypeChecker_TcTerm.tc_tparams env arguments)
in (match (uu____428) with
| (arguments, env', us) -> begin
(

let uu____437 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (uu____437) with
| (result, res_lcomp) -> begin
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

let uu____456 = (FStar_Syntax_Print.term_to_string result)
in (

let uu____457 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" uu____456 uu____457)))
in ((uu____455), (r)))
in FStar_Errors.Error (uu____452))
in (Prims.raise uu____451))
end));
(

let uu____458 = (FStar_Syntax_Util.head_and_args result)
in (match (uu____458) with
| (head, uu____471) -> begin
((

let uu____487 = (

let uu____488 = (FStar_Syntax_Subst.compress head)
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

let uu____499 = (FStar_Syntax_Print.term_to_string head)
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
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (

let uu____514 = (

let uu____518 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____532 -> (match (uu____532) with
| (x, uu____539) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append uu____518 arguments))
in (

let uu____544 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow uu____514 uu____544)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t), (tc_lid), (ntps), (quals), ([]), (r)))), (g))));
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

let g = (

let uu___82_588 = g
in {FStar_TypeChecker_Env.guard_f = uu___82_588.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___82_588.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((tc_universe_vars), ((Prims.snd g.FStar_TypeChecker_Env.univ_ineqs))); FStar_TypeChecker_Env.implicits = uu___82_588.FStar_TypeChecker_Env.implicits})
in ((

let uu____594 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____594) with
| true -> begin
(

let uu____595 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print1 "@@@@@@Guard before generalization: %s\n" uu____595))
end
| uu____596 -> begin
()
end));
(FStar_TypeChecker_Rel.force_trivial_guard env g);
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

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun uu___77_638 -> (match (uu___77_638) with
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
| (uvs, t) -> begin
((

let uu____672 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____672) with
| true -> begin
(

let uu____673 = (

let uu____674 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right uu____674 (FStar_String.concat ", ")))
in (

let uu____680 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" uu____673 uu____680)))
end
| uu____681 -> begin
()
end));
(

let uu____682 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____682) with
| (uvs, t) -> begin
(

let uu____691 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____691) with
| (args, uu____704) -> begin
(

let uu____715 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (uu____715) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun uu____752 uu____753 -> (match (((uu____752), (uu____753))) with
| ((x, uu____763), (se, uu____765)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____771, tps, uu____773, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let uu____785 = (

let uu____793 = (

let uu____794 = (FStar_Syntax_Subst.compress ty)
in uu____794.FStar_Syntax_Syntax.n)
in (match (uu____793) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____816 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (uu____816) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____859 -> begin
(

let uu____863 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c))))) uu____863 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| uu____886 -> begin
(([]), (ty))
end))
in (match (uu____785) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| uu____912 -> begin
(failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| uu____916 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _0_28 -> FStar_Syntax_Syntax.U_name (_0_28))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun uu___78_933 -> (match (uu___78_933) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____938, uu____939, uu____940, uu____941, uu____942, uu____943, uu____944) -> begin
((tc), (uvs_universes))
end
| uu____952 -> begin
(failwith "Impossible")
end))))
in (FStar_List.map2 (fun uu____958 d -> (match (uu____958) with
| (t, uu____963) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____965, uu____966, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (

let uu____977 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____977 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| uu____980 -> begin
(failwith "Impossible")
end)
end)) data_types datas)))
end)
in ((tcs), (datas))))
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
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(match (t.FStar_Syntax_Syntax.n) with
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

let btype = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env btype)
in ((

let uu____1176 = (

let uu____1177 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity in type, after normalization: " uu____1177))
in (debug_log env uu____1176));
((

let uu____1178 = (ty_occurs_in ty_lid btype)
in (not (uu____1178))) || ((debug_log env "ty does occur in this type, pressing ahead");
(

let uu____1180 = (

let uu____1181 = (FStar_Syntax_Subst.compress btype)
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
| (t, uu____1216) -> begin
(

let uu____1217 = (ty_occurs_in ty_lid t)
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

let bvs = (FStar_Syntax_Syntax.pat_bvs p)
in (

let uu____1327 = (

let uu____1328 = (FStar_List.map (fun bv -> (FStar_Syntax_Syntax.mk_binder bv)) bvs)
in (FStar_TypeChecker_Env.push_binders env uu____1328))
in (ty_strictly_positive_in_type ty_lid t unfolded uu____1327)))
end)) branches);
)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____1331, uu____1332) -> begin
((debug_log env "Checking strict positivity in an Tm_ascribed, recur)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| uu____1352 -> begin
((

let uu____1354 = (

let uu____1355 = (

let uu____1356 = (FStar_Syntax_Print.tag_of_term btype)
in (

let uu____1357 = (

let uu____1358 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat " and term: " uu____1358))
in (Prims.strcat uu____1356 uu____1357)))
in (Prims.strcat "Checking strict positivity, unexpected tag: " uu____1355))
in (debug_log env uu____1354));
false;
)
end));
));
));
))
and ty_nested_positive_in_inductive : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid ilid us args unfolded env -> ((

let uu____1366 = (

let uu____1367 = (

let uu____1368 = (

let uu____1369 = (FStar_Syntax_Print.args_to_string args)
in (Prims.strcat " applied to arguments: " uu____1369))
in (Prims.strcat ilid.FStar_Ident.str uu____1368))
in (Prims.strcat "Checking nested positivity in the inductive " uu____1367))
in (debug_log env uu____1366));
(

let uu____1370 = (FStar_TypeChecker_Env.datacons_of_typ env ilid)
in (match (uu____1370) with
| (b, idatas) -> begin
(match ((not (b))) with
| true -> begin
((debug_log env "Checking nested positivity, not an inductive, return false");
false;
)
end
| uu____1379 -> begin
(

let uu____1380 = (already_unfolded ilid args unfolded env)
in (match (uu____1380) with
| true -> begin
((debug_log env "Checking nested positivity, we have already unfolded this inductive with these args");
true;
)
end
| uu____1382 -> begin
(

let num_ibs = (FStar_TypeChecker_Env.num_inductive_ty_params env ilid)
in ((

let uu____1385 = (

let uu____1386 = (

let uu____1387 = (FStar_Util.string_of_int num_ibs)
in (Prims.strcat uu____1387 ", also adding to the memo table"))
in (Prims.strcat "Checking nested positivity, number of type parameters is " uu____1386))
in (debug_log env uu____1385));
(

let uu____1389 = (

let uu____1390 = (FStar_ST.read unfolded)
in (

let uu____1394 = (

let uu____1398 = (

let uu____1406 = (

let uu____1412 = (FStar_List.splitAt num_ibs args)
in (Prims.fst uu____1412))
in ((ilid), (uu____1406)))
in (uu____1398)::[])
in (FStar_List.append uu____1390 uu____1394)))
in (FStar_ST.write unfolded uu____1389));
(FStar_List.for_all (fun d -> (ty_nested_positive_in_dlid ty_lid d ilid us args num_ibs unfolded env)) idatas);
))
end))
end)
end));
))
and ty_nested_positive_in_dlid : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  Prims.int  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid dlid ilid us args num_ibs unfolded env -> ((debug_log env (Prims.strcat "Checking nested positivity in data constructor " (Prims.strcat dlid.FStar_Ident.str (Prims.strcat " of the inductive " ilid.FStar_Ident.str))));
(

let uu____1470 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____1470) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____1482 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let dt = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env dt)
in ((

let uu____1485 = (

let uu____1486 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking nested positivity in the data constructor type: " uu____1486))
in (debug_log env uu____1485));
(

let uu____1487 = (

let uu____1488 = (FStar_Syntax_Subst.compress dt)
in uu____1488.FStar_Syntax_Syntax.n)
in (match (uu____1487) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, c) -> begin
((debug_log env "Checked nested positivity in Tm_arrow data constructor type");
(

let uu____1504 = (FStar_List.splitAt num_ibs dbs)
in (match (uu____1504) with
| (ibs, dbs) -> begin
(

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let dbs = (

let uu____1531 = (FStar_Syntax_Subst.opening_of_binders ibs)
in (FStar_Syntax_Subst.subst_binders uu____1531 dbs))
in (

let c = (

let uu____1534 = (FStar_Syntax_Subst.opening_of_binders ibs)
in (FStar_Syntax_Subst.subst_comp uu____1534 c))
in (

let uu____1536 = (FStar_List.splitAt num_ibs args)
in (match (uu____1536) with
| (args, uu____1554) -> begin
(

let subst = (FStar_List.fold_left2 (fun subst ib arg -> (FStar_List.append subst ((FStar_Syntax_Syntax.NT ((((Prims.fst ib)), ((Prims.fst arg)))))::[]))) [] ibs args)
in (

let dbs = (FStar_Syntax_Subst.subst_binders subst dbs)
in (

let c = (

let uu____1600 = (FStar_Syntax_Subst.shift_subst (FStar_List.length dbs) subst)
in (FStar_Syntax_Subst.subst_comp uu____1600 c))
in ((

let uu____1608 = (

let uu____1609 = (

let uu____1610 = (FStar_Syntax_Print.binders_to_string "; " dbs)
in (

let uu____1611 = (

let uu____1612 = (FStar_Syntax_Print.comp_to_string c)
in (Prims.strcat ", and c: " uu____1612))
in (Prims.strcat uu____1610 uu____1611)))
in (Prims.strcat "Checking nested positivity in the unfolded data constructor binders as: " uu____1609))
in (debug_log env uu____1608));
(ty_nested_positive_in_type ty_lid (FStar_Syntax_Syntax.Tm_arrow (((dbs), (c)))) ilid num_ibs unfolded env);
))))
end)))))
end));
)
end
| uu____1613 -> begin
((debug_log env "Checking nested positivity in the data constructor type that is not an arrow");
(

let uu____1615 = (

let uu____1616 = (FStar_Syntax_Subst.compress dt)
in uu____1616.FStar_Syntax_Syntax.n)
in (ty_nested_positive_in_type ty_lid uu____1615 ilid num_ibs unfolded env));
)
end));
));
)
end));
))
and ty_nested_positive_in_type : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term'  ->  FStar_Ident.lident  ->  Prims.int  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid t ilid num_ibs unfolded env -> (match (t) with
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
((debug_log env "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself");
(

let uu____1642 = (try_get_fv t)
in (match (uu____1642) with
| (fv, uu____1646) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ilid)) with
| true -> begin
true
end
| uu____1651 -> begin
(failwith "Impossible, expected the type to be ilid")
end)
end));
)
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((

let uu____1665 = (

let uu____1666 = (FStar_Syntax_Print.binders_to_string "; " sbs)
in (Prims.strcat "Checking nested positivity in an Tm_arrow node, with binders as: " uu____1666))
in (debug_log env uu____1665));
(

let uu____1667 = (FStar_List.fold_left (fun uu____1674 b -> (match (uu____1674) with
| (r, env) -> begin
(match ((not (r))) with
| true -> begin
((r), (env))
end
| uu____1686 -> begin
(

let uu____1687 = (ty_strictly_positive_in_type ty_lid (Prims.fst b).FStar_Syntax_Syntax.sort unfolded env)
in (

let uu____1688 = (FStar_TypeChecker_Env.push_binders env ((b)::[]))
in ((uu____1687), (uu____1688))))
end)
end)) ((true), (env)) sbs)
in (match (uu____1667) with
| (b, uu____1694) -> begin
b
end));
)
end
| uu____1695 -> begin
(failwith "Nested positive check, unhandled case")
end))


let ty_positive_in_datacon : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.universes  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty_lid dlid ty_bs us unfolded env -> (

let uu____1714 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____1714) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____1726 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let uu____1728 = (

let uu____1729 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking data constructor type: " uu____1729))
in (debug_log env uu____1728));
(

let uu____1730 = (

let uu____1731 = (FStar_Syntax_Subst.compress dt)
in uu____1731.FStar_Syntax_Syntax.n)
in (match (uu____1730) with
| FStar_Syntax_Syntax.Tm_fvar (uu____1734) -> begin
((debug_log env "Data constructor type is simply an fvar, returning true");
true;
)
end
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____1737) -> begin
(

let dbs = (

let uu____1752 = (FStar_List.splitAt (FStar_List.length ty_bs) dbs)
in (Prims.snd uu____1752))
in (

let dbs = (

let uu____1774 = (FStar_Syntax_Subst.opening_of_binders ty_bs)
in (FStar_Syntax_Subst.subst_binders uu____1774 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in ((

let uu____1778 = (

let uu____1779 = (

let uu____1780 = (FStar_Util.string_of_int (FStar_List.length dbs))
in (Prims.strcat uu____1780 " binders"))
in (Prims.strcat "Data constructor type is an arrow type, so checking strict positivity in " uu____1779))
in (debug_log env uu____1778));
(

let uu____1786 = (FStar_List.fold_left (fun uu____1793 b -> (match (uu____1793) with
| (r, env) -> begin
(match ((not (r))) with
| true -> begin
((r), (env))
end
| uu____1805 -> begin
(

let uu____1806 = (ty_strictly_positive_in_type ty_lid (Prims.fst b).FStar_Syntax_Syntax.sort unfolded env)
in (

let uu____1807 = (FStar_TypeChecker_Env.push_binders env ((b)::[]))
in ((uu____1806), (uu____1807))))
end)
end)) ((true), (env)) dbs)
in (match (uu____1786) with
| (b, uu____1813) -> begin
b
end));
))))
end
| FStar_Syntax_Syntax.Tm_app (uu____1814, uu____1815) -> begin
((debug_log env "Data constructor type is a Tm_app, so returning true");
true;
)
end
| uu____1831 -> begin
(failwith "Unexpected data constructor type when checking positivity")
end));
)
end)))


let check_positivity : FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty env -> (

let unfolded_inductives = (FStar_Util.mk_ref [])
in (

let uu____1849 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, bs, uu____1859, uu____1860, uu____1861, uu____1862, uu____1863) -> begin
((lid), (us), (bs))
end
| uu____1870 -> begin
(failwith "Impossible!")
end)
in (match (uu____1849) with
| (ty_lid, ty_us, ty_bs) -> begin
(

let uu____1877 = (FStar_Syntax_Subst.univ_var_opening ty_us)
in (match (uu____1877) with
| (ty_usubst, ty_us) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env ty_us)
in (

let env = (FStar_TypeChecker_Env.push_binders env ty_bs)
in (

let ty_bs = (FStar_Syntax_Subst.subst_binders ty_usubst ty_bs)
in (

let ty_bs = (FStar_Syntax_Subst.open_binders ty_bs)
in (

let uu____1892 = (

let uu____1894 = (FStar_TypeChecker_Env.datacons_of_typ env ty_lid)
in (Prims.snd uu____1894))
in (FStar_List.for_all (fun d -> (

let uu____1900 = (FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name (s)) ty_us)
in (ty_positive_in_datacon ty_lid d ty_bs uu____1900 unfolded_inductives env))) uu____1892))))))
end))
end))))


let datacon_typ : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1907, uu____1908, t, uu____1910, uu____1911, uu____1912, uu____1913, uu____1914) -> begin
t
end
| uu____1919 -> begin
(failwith "Impossible!")
end))


let optimized_haseq_soundness_for_data : FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term = (fun ty_lid data usubst bs -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____1936 = (

let uu____1937 = (FStar_Syntax_Subst.compress dt)
in uu____1937.FStar_Syntax_Syntax.n)
in (match (uu____1936) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____1941) -> begin
(

let dbs = (

let uu____1956 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd uu____1956))
in (

let dbs = (

let uu____1978 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____1978 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (

let uu____1987 = (

let uu____1988 = (

let uu____1989 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (uu____1989)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____1988))
in (uu____1987 None FStar_Range.dummyRange))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (

let uu____1996 = (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" ty_lid.FStar_Ident.str)
in (FStar_TypeChecker_Util.label uu____1996 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (FStar_List.fold_right (fun b t -> (

let uu____2001 = (

let uu____2002 = (

let uu____2003 = (

let uu____2004 = (

let uu____2005 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2005 None))
in (FStar_Syntax_Syntax.as_arg uu____2004))
in (uu____2003)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2002))
in (uu____2001 None FStar_Range.dummyRange))) dbs cond)))))
end
| uu____2022 -> begin
FStar_Syntax_Util.t_true
end)))))


let optimized_haseq_ty = (fun all_datas_in_the_bundle usubst us acc ty -> (

let uu____2081 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2093, bs, t, uu____2096, d_lids, uu____2098, uu____2099) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____2107 -> begin
(failwith "Impossible!")
end)
in (match (uu____2081) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (

let uu____2132 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst uu____2132 t))
in (

let uu____2139 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____2139) with
| (bs, t) -> begin
(

let ibs = (

let uu____2159 = (

let uu____2160 = (FStar_Syntax_Subst.compress t)
in uu____2160.FStar_Syntax_Syntax.n)
in (match (uu____2159) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____2167) -> begin
ibs
end
| uu____2178 -> begin
[]
end))
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____2183 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____2184 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____2183 uu____2184)))
in (

let ind = (

let uu____2189 = (

let uu____2190 = (FStar_List.map (fun uu____2195 -> (match (uu____2195) with
| (bv, aq) -> begin
(

let uu____2202 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2202), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____2190))
in (uu____2189 None FStar_Range.dummyRange))
in (

let ind = (

let uu____2210 = (

let uu____2211 = (FStar_List.map (fun uu____2216 -> (match (uu____2216) with
| (bv, aq) -> begin
(

let uu____2223 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2223), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____2211))
in (uu____2210 None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____2231 = (

let uu____2232 = (

let uu____2233 = (FStar_Syntax_Syntax.as_arg ind)
in (uu____2233)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2232))
in (uu____2231 None FStar_Range.dummyRange))
in (

let bs' = (FStar_List.filter (fun b -> (

let uu____2247 = acc
in (match (uu____2247) with
| (uu____2255, en, uu____2257, uu____2258) -> begin
(

let opt = (

let uu____2267 = (

let uu____2268 = (FStar_Syntax_Util.type_u ())
in (Prims.fst uu____2268))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort uu____2267 false))
in (match (opt) with
| None -> begin
false
end
| Some (uu____2271) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (

let uu____2275 = (

let uu____2276 = (

let uu____2277 = (

let uu____2278 = (

let uu____2279 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg uu____2279))
in (uu____2278)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2277))
in (uu____2276 None FStar_Range.dummyRange))
in (FStar_Syntax_Util.mk_conj t uu____2275))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let uu___83_2288 = fml
in (

let uu____2289 = (

let uu____2290 = (

let uu____2295 = (

let uu____2296 = (

let uu____2303 = (

let uu____2305 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____2305)::[])
in (uu____2303)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____2296))
in ((fml), (uu____2295)))
in FStar_Syntax_Syntax.Tm_meta (uu____2290))
in {FStar_Syntax_Syntax.n = uu____2289; FStar_Syntax_Syntax.tk = uu___83_2288.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___83_2288.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___83_2288.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (

let uu____2317 = (

let uu____2318 = (

let uu____2319 = (

let uu____2320 = (

let uu____2321 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2321 None))
in (FStar_Syntax_Syntax.as_arg uu____2320))
in (uu____2319)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2318))
in (uu____2317 None FStar_Range.dummyRange))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (

let uu____2343 = (

let uu____2344 = (

let uu____2345 = (

let uu____2346 = (

let uu____2347 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2347 None))
in (FStar_Syntax_Syntax.as_arg uu____2346))
in (uu____2345)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2344))
in (uu____2343 None FStar_Range.dummyRange))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let uu____2367 = acc
in (match (uu____2367) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2401, uu____2402, uu____2403, t_lid, uu____2405, uu____2406, uu____2407, uu____2408) -> begin
(t_lid = lid)
end
| uu____2413 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let cond = (FStar_List.fold_left (fun acc d -> (

let uu____2417 = (optimized_haseq_soundness_for_data lid d usubst bs)
in (FStar_Syntax_Util.mk_conj acc uu____2417))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (

let uu____2419 = (FStar_Syntax_Util.mk_conj guard' guard)
in (

let uu____2422 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (uu____2419), (uu____2422)))))))))
end)))))))))))))))
end))))
end)))


let optimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 tc_assume -> (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2488, us, uu____2490, uu____2491, uu____2492, uu____2493, uu____2494, uu____2495) -> begin
us
end
| uu____2502 -> begin
(failwith "Impossible!")
end))
in (

let uu____2503 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____2503) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let uu____2519 = (FStar_List.fold_left (optimized_haseq_ty datas usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (uu____2519) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let uu____2551 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env phi)
in (match (uu____2551) with
| (phi, uu____2556) -> begin
((

let uu____2558 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____2558) with
| true -> begin
(

let uu____2559 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env uu____2559))
end
| uu____2560 -> begin
()
end));
(

let ses = (FStar_List.fold_left (fun l uu____2567 -> (match (uu____2567) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] FStar_Range.dummyRange)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
ses;
));
)
end)))
end)));
))
end))))


let unoptimized_haseq_data : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun usubst bs haseq_ind mutuals acc data -> (

let rec is_mutual = (fun t -> (

let uu____2610 = (

let uu____2611 = (FStar_Syntax_Subst.compress t)
in uu____2611.FStar_Syntax_Syntax.n)
in (match (uu____2610) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', uu____2621) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
(

let uu____2648 = (is_mutual t')
in (match (uu____2648) with
| true -> begin
true
end
| uu____2649 -> begin
(

let uu____2650 = (FStar_List.map Prims.fst args)
in (exists_mutual uu____2650))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t', uu____2663) -> begin
(is_mutual t')
end
| uu____2668 -> begin
false
end)))
and exists_mutual = (fun uu___79_2669 -> (match (uu___79_2669) with
| [] -> begin
false
end
| (hd)::tl -> begin
((is_mutual hd) || (exists_mutual tl))
end))
in (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____2686 = (

let uu____2687 = (FStar_Syntax_Subst.compress dt)
in uu____2687.FStar_Syntax_Syntax.n)
in (match (uu____2686) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____2693) -> begin
(

let dbs = (

let uu____2708 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd uu____2708))
in (

let dbs = (

let uu____2730 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____2730 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (

let uu____2742 = (

let uu____2743 = (

let uu____2744 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (uu____2744)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2743))
in (uu____2742 None FStar_Range.dummyRange))
in (

let haseq_sort = (

let uu____2750 = (is_mutual sort)
in (match (uu____2750) with
| true -> begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end
| uu____2751 -> begin
haseq_sort
end))
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> (

let uu____2757 = (

let uu____2758 = (

let uu____2759 = (

let uu____2760 = (

let uu____2761 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2761 None))
in (FStar_Syntax_Syntax.as_arg uu____2760))
in (uu____2759)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2758))
in (uu____2757 None FStar_Range.dummyRange))) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| uu____2778 -> begin
acc
end))))))


let unoptimized_haseq_ty = (fun all_datas_in_the_bundle mutuals usubst us acc ty -> (

let uu____2821 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2833, bs, t, uu____2836, d_lids, uu____2838, uu____2839) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____2847 -> begin
(failwith "Impossible!")
end)
in (match (uu____2821) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (

let uu____2863 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst uu____2863 t))
in (

let uu____2870 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____2870) with
| (bs, t) -> begin
(

let ibs = (

let uu____2881 = (

let uu____2882 = (FStar_Syntax_Subst.compress t)
in uu____2882.FStar_Syntax_Syntax.n)
in (match (uu____2881) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____2889) -> begin
ibs
end
| uu____2900 -> begin
[]
end))
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____2905 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____2906 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____2905 uu____2906)))
in (

let ind = (

let uu____2911 = (

let uu____2912 = (FStar_List.map (fun uu____2917 -> (match (uu____2917) with
| (bv, aq) -> begin
(

let uu____2924 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2924), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____2912))
in (uu____2911 None FStar_Range.dummyRange))
in (

let ind = (

let uu____2932 = (

let uu____2933 = (FStar_List.map (fun uu____2938 -> (match (uu____2938) with
| (bv, aq) -> begin
(

let uu____2945 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2945), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____2933))
in (uu____2932 None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____2953 = (

let uu____2954 = (

let uu____2955 = (FStar_Syntax_Syntax.as_arg ind)
in (uu____2955)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2954))
in (uu____2953 None FStar_Range.dummyRange))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2963, uu____2964, uu____2965, t_lid, uu____2967, uu____2968, uu____2969, uu____2970) -> begin
(t_lid = lid)
end
| uu____2975 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let data_cond = (FStar_List.fold_left (unoptimized_haseq_data usubst bs haseq_ind mutuals) FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let uu___84_2981 = fml
in (

let uu____2982 = (

let uu____2983 = (

let uu____2988 = (

let uu____2989 = (

let uu____2996 = (

let uu____2998 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____2998)::[])
in (uu____2996)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____2989))
in ((fml), (uu____2988)))
in FStar_Syntax_Syntax.Tm_meta (uu____2983))
in {FStar_Syntax_Syntax.n = uu____2982; FStar_Syntax_Syntax.tk = uu___84_2981.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___84_2981.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___84_2981.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (

let uu____3010 = (

let uu____3011 = (

let uu____3012 = (

let uu____3013 = (

let uu____3014 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____3014 None))
in (FStar_Syntax_Syntax.as_arg uu____3013))
in (uu____3012)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____3011))
in (uu____3010 None FStar_Range.dummyRange))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (

let uu____3036 = (

let uu____3037 = (

let uu____3038 = (

let uu____3039 = (

let uu____3040 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____3040 None))
in (FStar_Syntax_Syntax.as_arg uu____3039))
in (uu____3038)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____3037))
in (uu____3036 None FStar_Range.dummyRange))) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))
end))))
end)))


let unoptimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 tc_assume -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3109, uu____3110, uu____3111, uu____3112, uu____3113, uu____3114, uu____3115) -> begin
lid
end
| uu____3122 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let uu____3123 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, uu____3131, uu____3132, uu____3133, uu____3134, uu____3135, uu____3136) -> begin
((lid), (us))
end
| uu____3143 -> begin
(failwith "Impossible!")
end))
in (match (uu____3123) with
| (lid, us) -> begin
(

let uu____3149 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____3149) with
| (usubst, us) -> begin
(

let fml = (FStar_List.fold_left (unoptimized_haseq_ty datas mutuals usubst us) FStar_Syntax_Util.t_true tcs)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let se = (

let uu____3167 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env uu____3167 fml [] FStar_Range.dummyRange))
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
(se)::[];
)));
)))
end))
end))))


let check_inductive_well_typedness : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let uu____3197 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___80_3207 -> (match (uu___80_3207) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3208) -> begin
true
end
| uu____3220 -> begin
false
end))))
in (match (uu____3197) with
| (tys, datas) -> begin
((

let uu____3233 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun uu___81_3235 -> (match (uu___81_3235) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3236) -> begin
false
end
| uu____3247 -> begin
true
end))))
in (match (uu____3233) with
| true -> begin
(

let uu____3248 = (

let uu____3249 = (

let uu____3252 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (uu____3252)))
in FStar_Errors.Error (uu____3249))
in (Prims.raise uu____3248))
end
| uu____3253 -> begin
()
end));
(

let env0 = env
in (

let uu____3255 = (FStar_List.fold_right (fun tc uu____3269 -> (match (uu____3269) with
| (env, all_tcs, g) -> begin
(

let uu____3291 = (tc_tycon env tc)
in (match (uu____3291) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in ((

let uu____3308 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____3308) with
| true -> begin
(

let uu____3309 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" uu____3309))
end
| uu____3310 -> begin
()
end));
(

let uu____3311 = (

let uu____3312 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g uu____3312))
in ((env), ((((tc), (tc_u)))::all_tcs), (uu____3311)));
))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____3255) with
| (env, tcs, g) -> begin
(

let uu____3337 = (FStar_List.fold_right (fun se uu____3345 -> (match (uu____3345) with
| (datas, g) -> begin
(

let uu____3356 = (

let uu____3359 = (tc_data env tcs)
in (uu____3359 se))
in (match (uu____3356) with
| (data, g') -> begin
(

let uu____3369 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (uu____3369)))
end))
end)) datas (([]), (g)))
in (match (uu____3337) with
| (datas, g) -> begin
(

let uu____3381 = (generalize_and_inst_within env0 g tcs datas)
in (match (uu____3381) with
| (tcs, datas) -> begin
(

let sig_bndle = (

let uu____3398 = (

let uu____3406 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (uu____3406)))
in FStar_Syntax_Syntax.Sig_bundle (uu____3398))
in ((sig_bndle), (tcs), (datas)))
end))
end))
end)));
)
end)))




