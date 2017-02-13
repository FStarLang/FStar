
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
| uu____1274 -> begin
((

let uu____1276 = (

let uu____1277 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity, unexpected term: " uu____1277))
in (debug_log env uu____1276));
false;
)
end));
));
));
))
and ty_nested_positive_in_inductive : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid ilid us args unfolded env -> ((

let uu____1285 = (

let uu____1286 = (

let uu____1287 = (

let uu____1288 = (FStar_Syntax_Print.args_to_string args)
in (Prims.strcat " applied to arguments: " uu____1288))
in (Prims.strcat ilid.FStar_Ident.str uu____1287))
in (Prims.strcat "Checking nested positivity in the inductive " uu____1286))
in (debug_log env uu____1285));
(

let uu____1289 = (FStar_TypeChecker_Env.datacons_of_typ env ilid)
in (match (uu____1289) with
| (b, idatas) -> begin
(match ((not (b))) with
| true -> begin
((debug_log env "Checking nested positivity, not an inductive, return false");
false;
)
end
| uu____1298 -> begin
(

let uu____1299 = (already_unfolded ilid args unfolded env)
in (match (uu____1299) with
| true -> begin
((debug_log env "Checking nested positivity, we have already unfolded this inductive with these args");
true;
)
end
| uu____1301 -> begin
(

let num_ibs = (FStar_TypeChecker_Env.num_inductive_ty_params env ilid)
in ((

let uu____1304 = (

let uu____1305 = (

let uu____1306 = (FStar_Util.string_of_int num_ibs)
in (Prims.strcat uu____1306 ", also adding to the memo table"))
in (Prims.strcat "Checking nested positivity, number of type parameters is " uu____1305))
in (debug_log env uu____1304));
(

let uu____1308 = (

let uu____1309 = (FStar_ST.read unfolded)
in (

let uu____1313 = (

let uu____1317 = (

let uu____1325 = (

let uu____1331 = (FStar_List.splitAt num_ibs args)
in (Prims.fst uu____1331))
in ((ilid), (uu____1325)))
in (uu____1317)::[])
in (FStar_List.append uu____1309 uu____1313)))
in (FStar_ST.write unfolded uu____1308));
(FStar_List.for_all (fun d -> (ty_nested_positive_in_dlid ty_lid d ilid us args num_ibs unfolded env)) idatas);
))
end))
end)
end));
))
and ty_nested_positive_in_dlid : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  Prims.int  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid dlid ilid us args num_ibs unfolded env -> ((debug_log env (Prims.strcat "Checking nested positivity in data constructor " (Prims.strcat dlid.FStar_Ident.str (Prims.strcat " of the inductive " ilid.FStar_Ident.str))));
(

let uu____1389 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____1389) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____1401 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let dt = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env dt)
in ((

let uu____1404 = (

let uu____1405 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking nested positivity in the data constructor type: " uu____1405))
in (debug_log env uu____1404));
(

let uu____1406 = (

let uu____1407 = (FStar_Syntax_Subst.compress dt)
in uu____1407.FStar_Syntax_Syntax.n)
in (match (uu____1406) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, c) -> begin
((debug_log env "Checked nested positivity in Tm_arrow data constructor type");
(

let uu____1423 = (FStar_List.splitAt num_ibs dbs)
in (match (uu____1423) with
| (ibs, dbs) -> begin
(

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let dbs = (

let uu____1450 = (FStar_Syntax_Subst.opening_of_binders ibs)
in (FStar_Syntax_Subst.subst_binders uu____1450 dbs))
in (

let c = (

let uu____1453 = (FStar_Syntax_Subst.opening_of_binders ibs)
in (FStar_Syntax_Subst.subst_comp uu____1453 c))
in (

let uu____1455 = (FStar_List.splitAt num_ibs args)
in (match (uu____1455) with
| (args, uu____1473) -> begin
(

let subst = (FStar_List.fold_left2 (fun subst ib arg -> (FStar_List.append subst ((FStar_Syntax_Syntax.NT ((((Prims.fst ib)), ((Prims.fst arg)))))::[]))) [] ibs args)
in (

let dbs = (FStar_Syntax_Subst.subst_binders subst dbs)
in (

let c = (

let uu____1519 = (FStar_Syntax_Subst.shift_subst (FStar_List.length dbs) subst)
in (FStar_Syntax_Subst.subst_comp uu____1519 c))
in ((

let uu____1527 = (

let uu____1528 = (

let uu____1529 = (FStar_Syntax_Print.binders_to_string "; " dbs)
in (

let uu____1530 = (

let uu____1531 = (FStar_Syntax_Print.comp_to_string c)
in (Prims.strcat ", and c: " uu____1531))
in (Prims.strcat uu____1529 uu____1530)))
in (Prims.strcat "Checking nested positivity in the unfolded data constructor binders as: " uu____1528))
in (debug_log env uu____1527));
(ty_nested_positive_in_type ty_lid (FStar_Syntax_Syntax.Tm_arrow (((dbs), (c)))) ilid num_ibs unfolded env);
))))
end)))))
end));
)
end
| uu____1532 -> begin
((debug_log env "Checking nested positivity in the data constructor type that is not an arrow");
(

let uu____1534 = (

let uu____1535 = (FStar_Syntax_Subst.compress dt)
in uu____1535.FStar_Syntax_Syntax.n)
in (ty_nested_positive_in_type ty_lid uu____1534 ilid num_ibs unfolded env));
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

let uu____1561 = (try_get_fv t)
in (match (uu____1561) with
| (fv, uu____1565) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ilid)) with
| true -> begin
true
end
| uu____1570 -> begin
(failwith "Impossible, expected the type to be ilid")
end)
end));
)
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((

let uu____1584 = (

let uu____1585 = (FStar_Syntax_Print.binders_to_string "; " sbs)
in (Prims.strcat "Checking nested positivity in an Tm_arrow node, with binders as: " uu____1585))
in (debug_log env uu____1584));
(

let uu____1586 = (FStar_List.fold_left (fun uu____1593 b -> (match (uu____1593) with
| (r, env) -> begin
(match ((not (r))) with
| true -> begin
((r), (env))
end
| uu____1605 -> begin
(

let uu____1606 = (ty_strictly_positive_in_type ty_lid (Prims.fst b).FStar_Syntax_Syntax.sort unfolded env)
in (

let uu____1607 = (FStar_TypeChecker_Env.push_binders env ((b)::[]))
in ((uu____1606), (uu____1607))))
end)
end)) ((true), (env)) sbs)
in (match (uu____1586) with
| (b, uu____1613) -> begin
b
end));
)
end
| uu____1614 -> begin
(failwith "Nested positive check, unhandled case")
end))


let ty_positive_in_datacon : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.universes  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty_lid dlid ty_bs us unfolded env -> (

let uu____1633 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____1633) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____1645 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let uu____1647 = (

let uu____1648 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking data constructor type: " uu____1648))
in (debug_log env uu____1647));
(

let uu____1649 = (

let uu____1650 = (FStar_Syntax_Subst.compress dt)
in uu____1650.FStar_Syntax_Syntax.n)
in (match (uu____1649) with
| FStar_Syntax_Syntax.Tm_fvar (uu____1653) -> begin
((debug_log env "Data constructor type is simply an fvar, returning true");
true;
)
end
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____1656) -> begin
(

let dbs = (

let uu____1671 = (FStar_List.splitAt (FStar_List.length ty_bs) dbs)
in (Prims.snd uu____1671))
in (

let dbs = (

let uu____1693 = (FStar_Syntax_Subst.opening_of_binders ty_bs)
in (FStar_Syntax_Subst.subst_binders uu____1693 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in ((

let uu____1697 = (

let uu____1698 = (

let uu____1699 = (FStar_Util.string_of_int (FStar_List.length dbs))
in (Prims.strcat uu____1699 " binders"))
in (Prims.strcat "Data constructor type is an arrow type, so checking strict positivity in " uu____1698))
in (debug_log env uu____1697));
(

let uu____1705 = (FStar_List.fold_left (fun uu____1712 b -> (match (uu____1712) with
| (r, env) -> begin
(match ((not (r))) with
| true -> begin
((r), (env))
end
| uu____1724 -> begin
(

let uu____1725 = (ty_strictly_positive_in_type ty_lid (Prims.fst b).FStar_Syntax_Syntax.sort unfolded env)
in (

let uu____1726 = (FStar_TypeChecker_Env.push_binders env ((b)::[]))
in ((uu____1725), (uu____1726))))
end)
end)) ((true), (env)) dbs)
in (match (uu____1705) with
| (b, uu____1732) -> begin
b
end));
))))
end
| FStar_Syntax_Syntax.Tm_app (uu____1733, uu____1734) -> begin
((debug_log env "Data constructor type is a Tm_app, so returning true");
true;
)
end
| uu____1750 -> begin
(failwith "Unexpected data constructor type when checking positivity")
end));
)
end)))


let check_positivity : FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty env -> (

let unfolded_inductives = (FStar_Util.mk_ref [])
in (

let uu____1768 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, bs, uu____1778, uu____1779, uu____1780, uu____1781, uu____1782) -> begin
((lid), (us), (bs))
end
| uu____1789 -> begin
(failwith "Impossible!")
end)
in (match (uu____1768) with
| (ty_lid, ty_us, ty_bs) -> begin
(

let uu____1796 = (FStar_Syntax_Subst.univ_var_opening ty_us)
in (match (uu____1796) with
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

let uu____1811 = (

let uu____1813 = (FStar_TypeChecker_Env.datacons_of_typ env ty_lid)
in (Prims.snd uu____1813))
in (FStar_List.for_all (fun d -> (

let uu____1819 = (FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name (s)) ty_us)
in (ty_positive_in_datacon ty_lid d ty_bs uu____1819 unfolded_inductives env))) uu____1811))))))
end))
end))))


let datacon_typ : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1826, uu____1827, t, uu____1829, uu____1830, uu____1831, uu____1832, uu____1833) -> begin
t
end
| uu____1838 -> begin
(failwith "Impossible!")
end))


let optimized_haseq_soundness_for_data : FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term = (fun ty_lid data usubst bs -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____1855 = (

let uu____1856 = (FStar_Syntax_Subst.compress dt)
in uu____1856.FStar_Syntax_Syntax.n)
in (match (uu____1855) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____1860) -> begin
(

let dbs = (

let uu____1875 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd uu____1875))
in (

let dbs = (

let uu____1897 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____1897 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (

let uu____1906 = (

let uu____1907 = (

let uu____1908 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (uu____1908)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____1907))
in (uu____1906 None FStar_Range.dummyRange))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (

let uu____1915 = (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" ty_lid.FStar_Ident.str)
in (FStar_TypeChecker_Util.label uu____1915 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (FStar_List.fold_right (fun b t -> (

let uu____1920 = (

let uu____1921 = (

let uu____1922 = (

let uu____1923 = (

let uu____1924 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____1924 None))
in (FStar_Syntax_Syntax.as_arg uu____1923))
in (uu____1922)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____1921))
in (uu____1920 None FStar_Range.dummyRange))) dbs cond)))))
end
| uu____1941 -> begin
FStar_Syntax_Util.t_true
end)))))


let optimized_haseq_ty = (fun all_datas_in_the_bundle usubst us acc ty -> (

let uu____2000 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2012, bs, t, uu____2015, d_lids, uu____2017, uu____2018) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____2026 -> begin
(failwith "Impossible!")
end)
in (match (uu____2000) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (

let uu____2051 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst uu____2051 t))
in (

let uu____2058 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____2058) with
| (bs, t) -> begin
(

let ibs = (

let uu____2078 = (

let uu____2079 = (FStar_Syntax_Subst.compress t)
in uu____2079.FStar_Syntax_Syntax.n)
in (match (uu____2078) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____2086) -> begin
ibs
end
| uu____2097 -> begin
[]
end))
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____2102 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____2103 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____2102 uu____2103)))
in (

let ind = (

let uu____2108 = (

let uu____2109 = (FStar_List.map (fun uu____2114 -> (match (uu____2114) with
| (bv, aq) -> begin
(

let uu____2121 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2121), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____2109))
in (uu____2108 None FStar_Range.dummyRange))
in (

let ind = (

let uu____2129 = (

let uu____2130 = (FStar_List.map (fun uu____2135 -> (match (uu____2135) with
| (bv, aq) -> begin
(

let uu____2142 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2142), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____2130))
in (uu____2129 None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____2150 = (

let uu____2151 = (

let uu____2152 = (FStar_Syntax_Syntax.as_arg ind)
in (uu____2152)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2151))
in (uu____2150 None FStar_Range.dummyRange))
in (

let bs' = (FStar_List.filter (fun b -> (

let uu____2166 = acc
in (match (uu____2166) with
| (uu____2174, en, uu____2176, uu____2177) -> begin
(

let opt = (

let uu____2186 = (

let uu____2187 = (FStar_Syntax_Util.type_u ())
in (Prims.fst uu____2187))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort uu____2186 false))
in (match (opt) with
| None -> begin
false
end
| Some (uu____2190) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (

let uu____2194 = (

let uu____2195 = (

let uu____2196 = (

let uu____2197 = (

let uu____2198 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg uu____2198))
in (uu____2197)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2196))
in (uu____2195 None FStar_Range.dummyRange))
in (FStar_Syntax_Util.mk_conj t uu____2194))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let uu___83_2207 = fml
in (

let uu____2208 = (

let uu____2209 = (

let uu____2214 = (

let uu____2215 = (

let uu____2222 = (

let uu____2224 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____2224)::[])
in (uu____2222)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____2215))
in ((fml), (uu____2214)))
in FStar_Syntax_Syntax.Tm_meta (uu____2209))
in {FStar_Syntax_Syntax.n = uu____2208; FStar_Syntax_Syntax.tk = uu___83_2207.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___83_2207.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___83_2207.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (

let uu____2236 = (

let uu____2237 = (

let uu____2238 = (

let uu____2239 = (

let uu____2240 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2240 None))
in (FStar_Syntax_Syntax.as_arg uu____2239))
in (uu____2238)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2237))
in (uu____2236 None FStar_Range.dummyRange))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (

let uu____2262 = (

let uu____2263 = (

let uu____2264 = (

let uu____2265 = (

let uu____2266 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2266 None))
in (FStar_Syntax_Syntax.as_arg uu____2265))
in (uu____2264)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2263))
in (uu____2262 None FStar_Range.dummyRange))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let uu____2286 = acc
in (match (uu____2286) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2320, uu____2321, uu____2322, t_lid, uu____2324, uu____2325, uu____2326, uu____2327) -> begin
(t_lid = lid)
end
| uu____2332 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let cond = (FStar_List.fold_left (fun acc d -> (

let uu____2336 = (optimized_haseq_soundness_for_data lid d usubst bs)
in (FStar_Syntax_Util.mk_conj acc uu____2336))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (

let uu____2338 = (FStar_Syntax_Util.mk_conj guard' guard)
in (

let uu____2341 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (uu____2338), (uu____2341)))))))))
end)))))))))))))))
end))))
end)))


let optimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 tc_assume -> (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2407, us, uu____2409, uu____2410, uu____2411, uu____2412, uu____2413, uu____2414) -> begin
us
end
| uu____2421 -> begin
(failwith "Impossible!")
end))
in (

let uu____2422 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____2422) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let uu____2438 = (FStar_List.fold_left (optimized_haseq_ty datas usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (uu____2438) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let uu____2470 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env phi)
in (match (uu____2470) with
| (phi, uu____2475) -> begin
((

let uu____2477 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____2477) with
| true -> begin
(

let uu____2478 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env uu____2478))
end
| uu____2479 -> begin
()
end));
(

let ses = (FStar_List.fold_left (fun l uu____2486 -> (match (uu____2486) with
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

let uu____2529 = (

let uu____2530 = (FStar_Syntax_Subst.compress t)
in uu____2530.FStar_Syntax_Syntax.n)
in (match (uu____2529) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', uu____2540) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
(

let uu____2567 = (is_mutual t')
in (match (uu____2567) with
| true -> begin
true
end
| uu____2568 -> begin
(

let uu____2569 = (FStar_List.map Prims.fst args)
in (exists_mutual uu____2569))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t', uu____2582) -> begin
(is_mutual t')
end
| uu____2587 -> begin
false
end)))
and exists_mutual = (fun uu___79_2588 -> (match (uu___79_2588) with
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

let uu____2605 = (

let uu____2606 = (FStar_Syntax_Subst.compress dt)
in uu____2606.FStar_Syntax_Syntax.n)
in (match (uu____2605) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____2612) -> begin
(

let dbs = (

let uu____2627 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd uu____2627))
in (

let dbs = (

let uu____2649 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____2649 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (

let uu____2661 = (

let uu____2662 = (

let uu____2663 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (uu____2663)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2662))
in (uu____2661 None FStar_Range.dummyRange))
in (

let haseq_sort = (

let uu____2669 = (is_mutual sort)
in (match (uu____2669) with
| true -> begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end
| uu____2670 -> begin
haseq_sort
end))
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> (

let uu____2676 = (

let uu____2677 = (

let uu____2678 = (

let uu____2679 = (

let uu____2680 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2680 None))
in (FStar_Syntax_Syntax.as_arg uu____2679))
in (uu____2678)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2677))
in (uu____2676 None FStar_Range.dummyRange))) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| uu____2697 -> begin
acc
end))))))


let unoptimized_haseq_ty = (fun all_datas_in_the_bundle mutuals usubst us acc ty -> (

let uu____2740 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2752, bs, t, uu____2755, d_lids, uu____2757, uu____2758) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____2766 -> begin
(failwith "Impossible!")
end)
in (match (uu____2740) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (

let uu____2782 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst uu____2782 t))
in (

let uu____2789 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____2789) with
| (bs, t) -> begin
(

let ibs = (

let uu____2800 = (

let uu____2801 = (FStar_Syntax_Subst.compress t)
in uu____2801.FStar_Syntax_Syntax.n)
in (match (uu____2800) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____2808) -> begin
ibs
end
| uu____2819 -> begin
[]
end))
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____2824 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____2825 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____2824 uu____2825)))
in (

let ind = (

let uu____2830 = (

let uu____2831 = (FStar_List.map (fun uu____2836 -> (match (uu____2836) with
| (bv, aq) -> begin
(

let uu____2843 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2843), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____2831))
in (uu____2830 None FStar_Range.dummyRange))
in (

let ind = (

let uu____2851 = (

let uu____2852 = (FStar_List.map (fun uu____2857 -> (match (uu____2857) with
| (bv, aq) -> begin
(

let uu____2864 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2864), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____2852))
in (uu____2851 None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____2872 = (

let uu____2873 = (

let uu____2874 = (FStar_Syntax_Syntax.as_arg ind)
in (uu____2874)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2873))
in (uu____2872 None FStar_Range.dummyRange))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2882, uu____2883, uu____2884, t_lid, uu____2886, uu____2887, uu____2888, uu____2889) -> begin
(t_lid = lid)
end
| uu____2894 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let data_cond = (FStar_List.fold_left (unoptimized_haseq_data usubst bs haseq_ind mutuals) FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let uu___84_2900 = fml
in (

let uu____2901 = (

let uu____2902 = (

let uu____2907 = (

let uu____2908 = (

let uu____2915 = (

let uu____2917 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____2917)::[])
in (uu____2915)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____2908))
in ((fml), (uu____2907)))
in FStar_Syntax_Syntax.Tm_meta (uu____2902))
in {FStar_Syntax_Syntax.n = uu____2901; FStar_Syntax_Syntax.tk = uu___84_2900.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___84_2900.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___84_2900.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (

let uu____2929 = (

let uu____2930 = (

let uu____2931 = (

let uu____2932 = (

let uu____2933 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2933 None))
in (FStar_Syntax_Syntax.as_arg uu____2932))
in (uu____2931)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2930))
in (uu____2929 None FStar_Range.dummyRange))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (

let uu____2955 = (

let uu____2956 = (

let uu____2957 = (

let uu____2958 = (

let uu____2959 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2959 None))
in (FStar_Syntax_Syntax.as_arg uu____2958))
in (uu____2957)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2956))
in (uu____2955 None FStar_Range.dummyRange))) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))
end))))
end)))


let unoptimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 tc_assume -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3028, uu____3029, uu____3030, uu____3031, uu____3032, uu____3033, uu____3034) -> begin
lid
end
| uu____3041 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let uu____3042 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, uu____3050, uu____3051, uu____3052, uu____3053, uu____3054, uu____3055) -> begin
((lid), (us))
end
| uu____3062 -> begin
(failwith "Impossible!")
end))
in (match (uu____3042) with
| (lid, us) -> begin
(

let uu____3068 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____3068) with
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

let uu____3086 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env uu____3086 fml [] FStar_Range.dummyRange))
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
(se)::[];
)));
)))
end))
end))))


let check_inductive_well_typedness : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let uu____3116 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___80_3126 -> (match (uu___80_3126) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3127) -> begin
true
end
| uu____3139 -> begin
false
end))))
in (match (uu____3116) with
| (tys, datas) -> begin
((

let uu____3152 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun uu___81_3154 -> (match (uu___81_3154) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3155) -> begin
false
end
| uu____3166 -> begin
true
end))))
in (match (uu____3152) with
| true -> begin
(

let uu____3167 = (

let uu____3168 = (

let uu____3171 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (uu____3171)))
in FStar_Errors.Error (uu____3168))
in (Prims.raise uu____3167))
end
| uu____3172 -> begin
()
end));
(

let env0 = env
in (

let uu____3174 = (FStar_List.fold_right (fun tc uu____3188 -> (match (uu____3188) with
| (env, all_tcs, g) -> begin
(

let uu____3210 = (tc_tycon env tc)
in (match (uu____3210) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in ((

let uu____3227 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____3227) with
| true -> begin
(

let uu____3228 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" uu____3228))
end
| uu____3229 -> begin
()
end));
(

let uu____3230 = (

let uu____3231 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g uu____3231))
in ((env), ((((tc), (tc_u)))::all_tcs), (uu____3230)));
))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____3174) with
| (env, tcs, g) -> begin
(

let uu____3256 = (FStar_List.fold_right (fun se uu____3264 -> (match (uu____3264) with
| (datas, g) -> begin
(

let uu____3275 = (

let uu____3278 = (tc_data env tcs)
in (uu____3278 se))
in (match (uu____3275) with
| (data, g') -> begin
(

let uu____3288 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (uu____3288)))
end))
end)) datas (([]), (g)))
in (match (uu____3256) with
| (datas, g) -> begin
(

let uu____3300 = (generalize_and_inst_within env0 g tcs datas)
in (match (uu____3300) with
| (tcs, datas) -> begin
(

let sig_bndle = (

let uu____3317 = (

let uu____3325 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (uu____3325)))
in FStar_Syntax_Syntax.Sig_bundle (uu____3317))
in ((sig_bndle), (tcs), (datas)))
end))
end))
end)));
)
end)))




