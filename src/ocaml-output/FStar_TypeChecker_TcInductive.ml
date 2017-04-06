
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

let uu____55 = (FStar_Syntax_Util.arrow_formals k1)
in (match (uu____55) with
| (indices, t) -> begin
(

let uu____79 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (uu____79) with
| (indices1, env', guard_indices, us') -> begin
(

let uu____92 = (

let uu____95 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (uu____95) with
| (t1, uu____102, g) -> begin
(

let uu____104 = (

let uu____105 = (

let uu____106 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params uu____106))
in (FStar_TypeChecker_Rel.discharge_guard env' uu____105))
in ((t1), (uu____104)))
end))
in (match (uu____92) with
| (t1, guard) -> begin
(

let k2 = (

let uu____116 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_Syntax_Util.arrow indices1 uu____116))
in (

let uu____119 = (FStar_Syntax_Util.type_u ())
in (match (uu____119) with
| (t_type, u) -> begin
((

let uu____129 = (FStar_TypeChecker_Rel.teq env' t1 t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' uu____129));
(

let t_tc = (

let uu____133 = (FStar_Syntax_Syntax.mk_Total t1)
in (FStar_Syntax_Util.arrow (FStar_List.append tps2 indices1) uu____133))
in (

let tps3 = (FStar_Syntax_Subst.close_binders tps2)
in (

let k3 = (FStar_Syntax_Subst.close tps3 k2)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____141 = (FStar_TypeChecker_Env.push_let_binding env (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((uu____141), ((

let uu___81_145 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps3), (k3), (mutuals), (data), (quals))); FStar_Syntax_Syntax.sigrng = uu___81_145.FStar_Syntax_Syntax.sigrng})), (u), (guard)))))));
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


let tc_data : FStar_TypeChecker_Env.env_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.guard_t) = (fun env tcs se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs) -> begin
(

let uu____190 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun uu____204 -> (match (uu____204) with
| (se1, u_tc) -> begin
(

let uu____213 = (

let uu____214 = (

let uu____215 = (FStar_Syntax_Util.lid_of_sigelt se1)
in (FStar_Util.must uu____215))
in (FStar_Ident.lid_equals tc_lid uu____214))
in (match (uu____213) with
| true -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____225, uu____226, tps, uu____228, uu____229, uu____230, uu____231) -> begin
(

let tps1 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____252 -> (match (uu____252) with
| (x, uu____259) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let tps2 = (FStar_Syntax_Subst.open_binders tps1)
in (

let uu____262 = (

let uu____266 = (FStar_TypeChecker_Env.push_binders env tps2)
in ((uu____266), (tps2), (u_tc)))
in Some (uu____262))))
end
| uu____270 -> begin
(failwith "Impossible")
end)
end
| uu____275 -> begin
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
| uu____300 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected data constructor"), (se.FStar_Syntax_Syntax.sigrng)))))
end)
end))
in (match (uu____190) with
| (env1, tps, u_tc) -> begin
(

let uu____309 = (

let uu____317 = (

let uu____318 = (FStar_Syntax_Subst.compress t)
in uu____318.FStar_Syntax_Syntax.n)
in (match (uu____317) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let uu____340 = (FStar_Util.first_N ntps bs)
in (match (uu____340) with
| (uu____358, bs') -> begin
(

let t1 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res))))) None t.FStar_Syntax_Syntax.pos)
in (

let subst1 = (FStar_All.pipe_right tps (FStar_List.mapi (fun i uu____394 -> (match (uu____394) with
| (x, uu____398) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (

let uu____399 = (FStar_Syntax_Subst.subst subst1 t1)
in (FStar_Syntax_Util.arrow_formals uu____399))))
end))
end
| uu____400 -> begin
(([]), (t))
end))
in (match (uu____309) with
| (arguments, result) -> begin
((

let uu____421 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____421) with
| true -> begin
(

let uu____422 = (FStar_Syntax_Print.lid_to_string c)
in (

let uu____423 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (

let uu____424 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" uu____422 uu____423 uu____424))))
end
| uu____425 -> begin
()
end));
(

let uu____426 = (FStar_TypeChecker_TcTerm.tc_tparams env1 arguments)
in (match (uu____426) with
| (arguments1, env', us) -> begin
(

let uu____435 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (uu____435) with
| (result1, res_lcomp) -> begin
((

let uu____443 = (

let uu____444 = (FStar_Syntax_Subst.compress res_lcomp.FStar_Syntax_Syntax.res_typ)
in uu____444.FStar_Syntax_Syntax.n)
in (match (uu____443) with
| FStar_Syntax_Syntax.Tm_type (uu____447) -> begin
()
end
| ty -> begin
(

let uu____449 = (

let uu____450 = (

let uu____453 = (

let uu____454 = (FStar_Syntax_Print.term_to_string result1)
in (

let uu____455 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" uu____454 uu____455)))
in ((uu____453), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Errors.Error (uu____450))
in (Prims.raise uu____449))
end));
(

let uu____456 = (FStar_Syntax_Util.head_and_args result1)
in (match (uu____456) with
| (head1, uu____469) -> begin
((

let uu____485 = (

let uu____486 = (FStar_Syntax_Subst.compress head1)
in uu____486.FStar_Syntax_Syntax.n)
in (match (uu____485) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| uu____490 -> begin
(

let uu____491 = (

let uu____492 = (

let uu____495 = (

let uu____496 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (

let uu____497 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" uu____496 uu____497)))
in ((uu____495), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Errors.Error (uu____492))
in (Prims.raise uu____491))
end));
(

let g = (FStar_List.fold_left2 (fun g uu____502 u_x -> (match (uu____502) with
| (x, uu____507) -> begin
(

let uu____508 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g uu____508))
end)) FStar_TypeChecker_Rel.trivial_guard arguments1 us)
in (

let t1 = (

let uu____512 = (

let uu____516 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____530 -> (match (uu____530) with
| (x, uu____537) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append uu____516 arguments1))
in (

let uu____542 = (FStar_Syntax_Syntax.mk_Total result1)
in (FStar_Syntax_Util.arrow uu____512 uu____542)))
in (((

let uu___82_545 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t1), (tc_lid), (ntps), (quals), ([]))); FStar_Syntax_Syntax.sigrng = uu___82_545.FStar_Syntax_Syntax.sigrng})), (g))));
)
end));
)
end))
end));
)
end))
end))
end
| uu____551 -> begin
(failwith "impossible")
end))


let generalize_and_inst_within : FStar_TypeChecker_Env.env_t  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env g tcs datas -> (

let tc_universe_vars = (FStar_List.map Prims.snd tcs)
in (

let g1 = (

let uu___83_587 = g
in {FStar_TypeChecker_Env.guard_f = uu___83_587.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___83_587.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((tc_universe_vars), ((Prims.snd g.FStar_TypeChecker_Env.univ_ineqs))); FStar_TypeChecker_Env.implicits = uu___83_587.FStar_TypeChecker_Env.implicits})
in ((

let uu____593 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____593) with
| true -> begin
(

let uu____594 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "@@@@@@Guard before generalization: %s\n" uu____594))
end
| uu____595 -> begin
()
end));
(FStar_TypeChecker_Rel.force_trivial_guard env g1);
(

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun uu____605 -> (match (uu____605) with
| (se, uu____609) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____610, uu____611, tps, k, uu____614, uu____615, uu____616) -> begin
(

let uu____623 = (

let uu____624 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) uu____624))
in (FStar_Syntax_Syntax.null_binder uu____623))
end
| uu____631 -> begin
(failwith "Impossible")
end)
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____637, uu____638, t, uu____640, uu____641, uu____642, uu____643) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| uu____648 -> begin
(failwith "Impossible")
end))))
in (

let t = (

let uu____652 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') uu____652))
in ((

let uu____656 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____656) with
| true -> begin
(

let uu____657 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" uu____657))
end
| uu____658 -> begin
()
end));
(

let uu____659 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (uu____659) with
| (uvs, t1) -> begin
((

let uu____669 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____669) with
| true -> begin
(

let uu____670 = (

let uu____671 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right uu____671 (FStar_String.concat ", ")))
in (

let uu____677 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" uu____670 uu____677)))
end
| uu____678 -> begin
()
end));
(

let uu____679 = (FStar_Syntax_Subst.open_univ_vars uvs t1)
in (match (uu____679) with
| (uvs1, t2) -> begin
(

let uu____688 = (FStar_Syntax_Util.arrow_formals t2)
in (match (uu____688) with
| (args, uu____701) -> begin
(

let uu____712 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (uu____712) with
| (tc_types, data_types) -> begin
(

let tcs1 = (FStar_List.map2 (fun uu____749 uu____750 -> (match (((uu____749), (uu____750))) with
| ((x, uu____760), (se, uu____762)) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____768, tps, uu____770, mutuals, datas1, quals) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs1 x.FStar_Syntax_Syntax.sort)
in (

let uu____781 = (

let uu____789 = (

let uu____790 = (FStar_Syntax_Subst.compress ty)
in uu____790.FStar_Syntax_Syntax.n)
in (match (uu____789) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c) -> begin
(

let uu____812 = (FStar_Util.first_N (FStar_List.length tps) binders1)
in (match (uu____812) with
| (tps1, rest) -> begin
(

let t3 = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____855 -> begin
(

let uu____859 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c))))) uu____859 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps1), (t3)))
end))
end
| uu____882 -> begin
(([]), (ty))
end))
in (match (uu____781) with
| (tps1, t3) -> begin
(

let uu___84_900 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs1), (tps1), (t3), (mutuals), (datas1), (quals))); FStar_Syntax_Syntax.sigrng = uu___84_900.FStar_Syntax_Syntax.sigrng})
end)))
end
| uu____909 -> begin
(failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas1 = (match (uvs1) with
| [] -> begin
datas
end
| uu____913 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs1 (FStar_List.map (fun _0_28 -> FStar_Syntax_Syntax.U_name (_0_28))))
in (

let tc_insts = (FStar_All.pipe_right tcs1 (FStar_List.map (fun uu___77_930 -> (match (uu___77_930) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____935, uu____936, uu____937, uu____938, uu____939, uu____940); FStar_Syntax_Syntax.sigrng = uu____941} -> begin
((tc), (uvs_universes))
end
| uu____949 -> begin
(failwith "Impossible")
end))))
in (FStar_List.map2 (fun uu____955 d -> (match (uu____955) with
| (t3, uu____960) -> begin
(match (d.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____962, uu____963, tc, ntps, quals, mutuals) -> begin
(

let ty = (

let uu____973 = (FStar_Syntax_InstFV.instantiate tc_insts t3.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____973 (FStar_Syntax_Subst.close_univ_vars uvs1)))
in (

let uu___85_974 = d
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((l), (uvs1), (ty), (tc), (ntps), (quals), (mutuals))); FStar_Syntax_Syntax.sigrng = uu___85_974.FStar_Syntax_Syntax.sigrng}))
end
| uu____977 -> begin
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

let uu____986 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Positivity")))
in (match (uu____986) with
| true -> begin
(FStar_Util.print_string (Prims.strcat "Positivity::" (Prims.strcat s "\n")))
end
| uu____987 -> begin
()
end)))


let ty_occurs_in : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun ty_lid t -> (

let uu____994 = (FStar_Syntax_Free.fvars t)
in (FStar_Util.set_mem ty_lid uu____994)))


let try_get_fv : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes) = (fun t -> (

let uu____1003 = (

let uu____1004 = (FStar_Syntax_Subst.compress t)
in uu____1004.FStar_Syntax_Syntax.n)
in (match (uu____1003) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, us) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), (us))
end
| uu____1020 -> begin
(failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
end)
end
| uu____1023 -> begin
(failwith "Node is not an fvar or a Tm_uinst")
end)))


type unfolded_memo_elt =
(FStar_Ident.lident * FStar_Syntax_Syntax.args) Prims.list


type unfolded_memo_t =
unfolded_memo_elt FStar_ST.ref


let already_unfolded : FStar_Ident.lident  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ilid arrghs unfolded env -> (

let uu____1042 = (FStar_ST.read unfolded)
in (FStar_List.existsML (fun uu____1054 -> (match (uu____1054) with
| (lid, l) -> begin
((FStar_Ident.lid_equals lid ilid) && (

let args = (

let uu____1074 = (FStar_List.splitAt (FStar_List.length l) arrghs)
in (Prims.fst uu____1074))
in (FStar_List.fold_left2 (fun b a a' -> (b && (FStar_TypeChecker_Rel.teq_nosmt env (Prims.fst a) (Prims.fst a')))) true args l)))
end)) uu____1042)))


let rec ty_strictly_positive_in_type : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid btype unfolded env -> ((

let uu____1169 = (

let uu____1170 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity in type: " uu____1170))
in (debug_log env uu____1169));
(

let btype1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env btype)
in ((

let uu____1173 = (

let uu____1174 = (FStar_Syntax_Print.term_to_string btype1)
in (Prims.strcat "Checking strict positivity in type, after normalization: " uu____1174))
in (debug_log env uu____1173));
((

let uu____1175 = (ty_occurs_in ty_lid btype1)
in (not (uu____1175))) || ((debug_log env "ty does occur in this type, pressing ahead");
(

let uu____1177 = (

let uu____1178 = (FStar_Syntax_Subst.compress btype1)
in uu____1178.FStar_Syntax_Syntax.n)
in (match (uu____1177) with
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1197 = (try_get_fv t)
in (match (uu____1197) with
| (fv, us) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ty_lid)) with
| true -> begin
((debug_log env "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
(FStar_List.for_all (fun uu____1209 -> (match (uu____1209) with
| (t1, uu____1213) -> begin
(

let uu____1214 = (ty_occurs_in ty_lid t1)
in (not (uu____1214)))
end)) args);
)
end
| uu____1215 -> begin
((debug_log env "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
(ty_nested_positive_in_inductive ty_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v us args unfolded env);
)
end)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((debug_log env "Checking strict positivity in Tm_arrow");
(

let uu____1234 = (

let uu____1235 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____1235)))
in (match (uu____1234) with
| true -> begin
((debug_log env "Checking strict positivity , the arrow is impure, so return true");
true;
)
end
| uu____1237 -> begin
((debug_log env "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
((FStar_List.for_all (fun uu____1241 -> (match (uu____1241) with
| (b, uu____1245) -> begin
(

let uu____1246 = (ty_occurs_in ty_lid b.FStar_Syntax_Syntax.sort)
in (not (uu____1246)))
end)) sbs) && (

let uu____1247 = (FStar_Syntax_Subst.open_term sbs (FStar_Syntax_Util.comp_result c))
in (match (uu____1247) with
| (uu____1250, return_type) -> begin
(

let uu____1252 = (FStar_TypeChecker_Env.push_binders env sbs)
in (ty_strictly_positive_in_type ty_lid return_type unfolded uu____1252))
end)));
)
end));
)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1253) -> begin
((debug_log env "Checking strict positivity in an fvar, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_type (uu____1255) -> begin
((debug_log env "Checking strict positivity in an Tm_type, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____1258) -> begin
((debug_log env "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____1265) -> begin
((debug_log env "Checking strict positivity in an Tm_refine, recur in the bv sort)");
(ty_strictly_positive_in_type ty_lid bv.FStar_Syntax_Syntax.sort unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_match (uu____1271, branches) -> begin
((debug_log env "Checking strict positivity in an Tm_match, recur in the branches)");
(FStar_List.for_all (fun uu____1306 -> (match (uu____1306) with
| (p, uu____1314, t) -> begin
(

let bs = (

let uu____1324 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_List.map FStar_Syntax_Syntax.mk_binder uu____1324))
in (

let uu____1326 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____1326) with
| (bs1, t1) -> begin
(

let uu____1331 = (FStar_TypeChecker_Env.push_binders env bs1)
in (ty_strictly_positive_in_type ty_lid t1 unfolded uu____1331))
end)))
end)) branches);
)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____1333, uu____1334) -> begin
((debug_log env "Checking strict positivity in an Tm_ascribed, recur)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| uu____1364 -> begin
((

let uu____1366 = (

let uu____1367 = (

let uu____1368 = (FStar_Syntax_Print.tag_of_term btype1)
in (

let uu____1369 = (

let uu____1370 = (FStar_Syntax_Print.term_to_string btype1)
in (Prims.strcat " and term: " uu____1370))
in (Prims.strcat uu____1368 uu____1369)))
in (Prims.strcat "Checking strict positivity, unexpected tag: " uu____1367))
in (debug_log env uu____1366));
false;
)
end));
));
));
))
and ty_nested_positive_in_inductive : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid ilid us args unfolded env -> ((

let uu____1378 = (

let uu____1379 = (

let uu____1380 = (

let uu____1381 = (FStar_Syntax_Print.args_to_string args)
in (Prims.strcat " applied to arguments: " uu____1381))
in (Prims.strcat ilid.FStar_Ident.str uu____1380))
in (Prims.strcat "Checking nested positivity in the inductive " uu____1379))
in (debug_log env uu____1378));
(

let uu____1382 = (FStar_TypeChecker_Env.datacons_of_typ env ilid)
in (match (uu____1382) with
| (b, idatas) -> begin
(match ((not (b))) with
| true -> begin
((debug_log env "Checking nested positivity, not an inductive, return false");
false;
)
end
| uu____1391 -> begin
(

let uu____1392 = (already_unfolded ilid args unfolded env)
in (match (uu____1392) with
| true -> begin
((debug_log env "Checking nested positivity, we have already unfolded this inductive with these args");
true;
)
end
| uu____1394 -> begin
(

let num_ibs = (FStar_TypeChecker_Env.num_inductive_ty_params env ilid)
in ((

let uu____1397 = (

let uu____1398 = (

let uu____1399 = (FStar_Util.string_of_int num_ibs)
in (Prims.strcat uu____1399 ", also adding to the memo table"))
in (Prims.strcat "Checking nested positivity, number of type parameters is " uu____1398))
in (debug_log env uu____1397));
(

let uu____1401 = (

let uu____1402 = (FStar_ST.read unfolded)
in (

let uu____1406 = (

let uu____1410 = (

let uu____1418 = (

let uu____1424 = (FStar_List.splitAt num_ibs args)
in (Prims.fst uu____1424))
in ((ilid), (uu____1418)))
in (uu____1410)::[])
in (FStar_List.append uu____1402 uu____1406)))
in (FStar_ST.write unfolded uu____1401));
(FStar_List.for_all (fun d -> (ty_nested_positive_in_dlid ty_lid d ilid us args num_ibs unfolded env)) idatas);
))
end))
end)
end));
))
and ty_nested_positive_in_dlid : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  Prims.int  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid dlid ilid us args num_ibs unfolded env -> ((debug_log env (Prims.strcat "Checking nested positivity in data constructor " (Prims.strcat dlid.FStar_Ident.str (Prims.strcat " of the inductive " ilid.FStar_Ident.str))));
(

let uu____1482 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____1482) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____1494 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let dt1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env dt)
in ((

let uu____1497 = (

let uu____1498 = (FStar_Syntax_Print.term_to_string dt1)
in (Prims.strcat "Checking nested positivity in the data constructor type: " uu____1498))
in (debug_log env uu____1497));
(

let uu____1499 = (

let uu____1500 = (FStar_Syntax_Subst.compress dt1)
in uu____1500.FStar_Syntax_Syntax.n)
in (match (uu____1499) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, c) -> begin
((debug_log env "Checked nested positivity in Tm_arrow data constructor type");
(

let uu____1516 = (FStar_List.splitAt num_ibs dbs)
in (match (uu____1516) with
| (ibs, dbs1) -> begin
(

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let dbs2 = (

let uu____1543 = (FStar_Syntax_Subst.opening_of_binders ibs1)
in (FStar_Syntax_Subst.subst_binders uu____1543 dbs1))
in (

let c1 = (

let uu____1546 = (FStar_Syntax_Subst.opening_of_binders ibs1)
in (FStar_Syntax_Subst.subst_comp uu____1546 c))
in (

let uu____1548 = (FStar_List.splitAt num_ibs args)
in (match (uu____1548) with
| (args1, uu____1566) -> begin
(

let subst1 = (FStar_List.fold_left2 (fun subst1 ib arg -> (FStar_List.append subst1 ((FStar_Syntax_Syntax.NT ((((Prims.fst ib)), ((Prims.fst arg)))))::[]))) [] ibs1 args1)
in (

let dbs3 = (FStar_Syntax_Subst.subst_binders subst1 dbs2)
in (

let c2 = (

let uu____1612 = (FStar_Syntax_Subst.shift_subst (FStar_List.length dbs3) subst1)
in (FStar_Syntax_Subst.subst_comp uu____1612 c1))
in ((

let uu____1620 = (

let uu____1621 = (

let uu____1622 = (FStar_Syntax_Print.binders_to_string "; " dbs3)
in (

let uu____1623 = (

let uu____1624 = (FStar_Syntax_Print.comp_to_string c2)
in (Prims.strcat ", and c: " uu____1624))
in (Prims.strcat uu____1622 uu____1623)))
in (Prims.strcat "Checking nested positivity in the unfolded data constructor binders as: " uu____1621))
in (debug_log env uu____1620));
(ty_nested_positive_in_type ty_lid (FStar_Syntax_Syntax.Tm_arrow (((dbs3), (c2)))) ilid num_ibs unfolded env);
))))
end)))))
end));
)
end
| uu____1625 -> begin
((debug_log env "Checking nested positivity in the data constructor type that is not an arrow");
(

let uu____1627 = (

let uu____1628 = (FStar_Syntax_Subst.compress dt1)
in uu____1628.FStar_Syntax_Syntax.n)
in (ty_nested_positive_in_type ty_lid uu____1627 ilid num_ibs unfolded env));
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

let uu____1654 = (try_get_fv t1)
in (match (uu____1654) with
| (fv, uu____1658) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ilid)) with
| true -> begin
true
end
| uu____1663 -> begin
(failwith "Impossible, expected the type to be ilid")
end)
end));
)
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((

let uu____1677 = (

let uu____1678 = (FStar_Syntax_Print.binders_to_string "; " sbs)
in (Prims.strcat "Checking nested positivity in an Tm_arrow node, with binders as: " uu____1678))
in (debug_log env uu____1677));
(

let uu____1679 = (FStar_List.fold_left (fun uu____1686 b -> (match (uu____1686) with
| (r, env1) -> begin
(match ((not (r))) with
| true -> begin
((r), (env1))
end
| uu____1698 -> begin
(

let uu____1699 = (ty_strictly_positive_in_type ty_lid (Prims.fst b).FStar_Syntax_Syntax.sort unfolded env1)
in (

let uu____1700 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((uu____1699), (uu____1700))))
end)
end)) ((true), (env)) sbs)
in (match (uu____1679) with
| (b, uu____1706) -> begin
b
end));
)
end
| uu____1707 -> begin
(failwith "Nested positive check, unhandled case")
end))


let ty_positive_in_datacon : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.universes  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty_lid dlid ty_bs us unfolded env -> (

let uu____1726 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____1726) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____1738 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let uu____1740 = (

let uu____1741 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking data constructor type: " uu____1741))
in (debug_log env uu____1740));
(

let uu____1742 = (

let uu____1743 = (FStar_Syntax_Subst.compress dt)
in uu____1743.FStar_Syntax_Syntax.n)
in (match (uu____1742) with
| FStar_Syntax_Syntax.Tm_fvar (uu____1746) -> begin
((debug_log env "Data constructor type is simply an fvar, returning true");
true;
)
end
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____1749) -> begin
(

let dbs1 = (

let uu____1764 = (FStar_List.splitAt (FStar_List.length ty_bs) dbs)
in (Prims.snd uu____1764))
in (

let dbs2 = (

let uu____1786 = (FStar_Syntax_Subst.opening_of_binders ty_bs)
in (FStar_Syntax_Subst.subst_binders uu____1786 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in ((

let uu____1790 = (

let uu____1791 = (

let uu____1792 = (FStar_Util.string_of_int (FStar_List.length dbs3))
in (Prims.strcat uu____1792 " binders"))
in (Prims.strcat "Data constructor type is an arrow type, so checking strict positivity in " uu____1791))
in (debug_log env uu____1790));
(

let uu____1798 = (FStar_List.fold_left (fun uu____1805 b -> (match (uu____1805) with
| (r, env1) -> begin
(match ((not (r))) with
| true -> begin
((r), (env1))
end
| uu____1817 -> begin
(

let uu____1818 = (ty_strictly_positive_in_type ty_lid (Prims.fst b).FStar_Syntax_Syntax.sort unfolded env1)
in (

let uu____1819 = (FStar_TypeChecker_Env.push_binders env1 ((b)::[]))
in ((uu____1818), (uu____1819))))
end)
end)) ((true), (env)) dbs3)
in (match (uu____1798) with
| (b, uu____1825) -> begin
b
end));
))))
end
| FStar_Syntax_Syntax.Tm_app (uu____1826, uu____1827) -> begin
((debug_log env "Data constructor type is a Tm_app, so returning true");
true;
)
end
| uu____1843 -> begin
(failwith "Unexpected data constructor type when checking positivity")
end));
)
end)))


let check_positivity : FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty env -> (

let unfolded_inductives = (FStar_Util.mk_ref [])
in (

let uu____1861 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, bs, uu____1871, uu____1872, uu____1873, uu____1874) -> begin
((lid), (us), (bs))
end
| uu____1881 -> begin
(failwith "Impossible!")
end)
in (match (uu____1861) with
| (ty_lid, ty_us, ty_bs) -> begin
(

let uu____1888 = (FStar_Syntax_Subst.univ_var_opening ty_us)
in (match (uu____1888) with
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

let uu____1903 = (

let uu____1905 = (FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid)
in (Prims.snd uu____1905))
in (FStar_List.for_all (fun d -> (

let uu____1911 = (FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name (s)) ty_us1)
in (ty_positive_in_datacon ty_lid d ty_bs2 uu____1911 unfolded_inductives env2))) uu____1903))))))
end))
end))))


let datacon_typ : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term = (fun data -> (match (data.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1918, uu____1919, t, uu____1921, uu____1922, uu____1923, uu____1924) -> begin
t
end
| uu____1929 -> begin
(failwith "Impossible!")
end))


let optimized_haseq_soundness_for_data : FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term = (fun ty_lid data usubst bs -> (

let dt = (datacon_typ data)
in (

let dt1 = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____1946 = (

let uu____1947 = (FStar_Syntax_Subst.compress dt1)
in uu____1947.FStar_Syntax_Syntax.n)
in (match (uu____1946) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____1951) -> begin
(

let dbs1 = (

let uu____1966 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd uu____1966))
in (

let dbs2 = (

let uu____1988 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____1988 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (

let uu____1997 = (

let uu____1998 = (

let uu____1999 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (uu____1999)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____1998))
in (uu____1997 None FStar_Range.dummyRange))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b1 = (

let uu____2006 = (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" ty_lid.FStar_Ident.str)
in (FStar_TypeChecker_Util.label uu____2006 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b1))))) FStar_Syntax_Util.t_true dbs3)
in (FStar_List.fold_right (fun b t -> (

let uu____2011 = (

let uu____2012 = (

let uu____2013 = (

let uu____2014 = (

let uu____2015 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2015 None))
in (FStar_Syntax_Syntax.as_arg uu____2014))
in (uu____2013)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2012))
in (uu____2011 None FStar_Range.dummyRange))) dbs3 cond)))))
end
| uu____2032 -> begin
FStar_Syntax_Util.t_true
end)))))


let optimized_haseq_ty = (fun all_datas_in_the_bundle usubst us acc ty -> (

let uu____2091 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2103, bs, t, uu____2106, d_lids, uu____2108) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____2116 -> begin
(failwith "Impossible!")
end)
in (match (uu____2091) with
| (lid, bs, t, d_lids) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t1 = (

let uu____2141 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst)
in (FStar_Syntax_Subst.subst uu____2141 t))
in (

let uu____2148 = (FStar_Syntax_Subst.open_term bs1 t1)
in (match (uu____2148) with
| (bs2, t2) -> begin
(

let ibs = (

let uu____2168 = (

let uu____2169 = (FStar_Syntax_Subst.compress t2)
in uu____2169.FStar_Syntax_Syntax.n)
in (match (uu____2168) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____2176) -> begin
ibs
end
| uu____2187 -> begin
[]
end))
in (

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____2192 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____2193 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____2192 uu____2193)))
in (

let ind1 = (

let uu____2198 = (

let uu____2199 = (FStar_List.map (fun uu____2204 -> (match (uu____2204) with
| (bv, aq) -> begin
(

let uu____2211 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2211), (aq)))
end)) bs2)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____2199))
in (uu____2198 None FStar_Range.dummyRange))
in (

let ind2 = (

let uu____2219 = (

let uu____2220 = (FStar_List.map (fun uu____2225 -> (match (uu____2225) with
| (bv, aq) -> begin
(

let uu____2232 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2232), (aq)))
end)) ibs1)
in (FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2220))
in (uu____2219 None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____2240 = (

let uu____2241 = (

let uu____2242 = (FStar_Syntax_Syntax.as_arg ind2)
in (uu____2242)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2241))
in (uu____2240 None FStar_Range.dummyRange))
in (

let bs' = (FStar_List.filter (fun b -> (

let uu____2256 = acc
in (match (uu____2256) with
| (uu____2264, en, uu____2266, uu____2267) -> begin
(

let opt = (

let uu____2276 = (

let uu____2277 = (FStar_Syntax_Util.type_u ())
in (Prims.fst uu____2277))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort uu____2276 false))
in (match (opt) with
| None -> begin
false
end
| Some (uu____2280) -> begin
true
end))
end))) bs2)
in (

let haseq_bs = (FStar_List.fold_left (fun t3 b -> (

let uu____2284 = (

let uu____2285 = (

let uu____2286 = (

let uu____2287 = (

let uu____2288 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg uu____2288))
in (uu____2287)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2286))
in (uu____2285 None FStar_Range.dummyRange))
in (FStar_Syntax_Util.mk_conj t3 uu____2284))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml1 = (

let uu___86_2297 = fml
in (

let uu____2298 = (

let uu____2299 = (

let uu____2304 = (

let uu____2305 = (

let uu____2312 = (

let uu____2314 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____2314)::[])
in (uu____2312)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____2305))
in ((fml), (uu____2304)))
in FStar_Syntax_Syntax.Tm_meta (uu____2299))
in {FStar_Syntax_Syntax.n = uu____2298; FStar_Syntax_Syntax.tk = uu___86_2297.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___86_2297.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___86_2297.FStar_Syntax_Syntax.vars}))
in (

let fml2 = (FStar_List.fold_right (fun b t3 -> (

let uu____2326 = (

let uu____2327 = (

let uu____2328 = (

let uu____2329 = (

let uu____2330 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2330 None))
in (FStar_Syntax_Syntax.as_arg uu____2329))
in (uu____2328)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2327))
in (uu____2326 None FStar_Range.dummyRange))) ibs1 fml1)
in (

let fml3 = (FStar_List.fold_right (fun b t3 -> (

let uu____2352 = (

let uu____2353 = (

let uu____2354 = (

let uu____2355 = (

let uu____2356 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2356 None))
in (FStar_Syntax_Syntax.as_arg uu____2355))
in (uu____2354)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2353))
in (uu____2352 None FStar_Range.dummyRange))) bs2 fml2)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml3)
in (

let uu____2376 = acc
in (match (uu____2376) with
| (l_axioms, env, guard', cond') -> begin
(

let env1 = (FStar_TypeChecker_Env.push_binders env bs2)
in (

let env2 = (FStar_TypeChecker_Env.push_binders env1 ibs1)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2410, uu____2411, uu____2412, t_lid, uu____2414, uu____2415, uu____2416) -> begin
(t_lid = lid)
end
| uu____2421 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let cond = (FStar_List.fold_left (fun acc1 d -> (

let uu____2425 = (optimized_haseq_soundness_for_data lid d usubst bs2)
in (FStar_Syntax_Util.mk_conj acc1 uu____2425))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (

let uu____2427 = (FStar_Syntax_Util.mk_conj guard' guard)
in (

let uu____2430 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml3)))::[]))), (env2), (uu____2427), (uu____2430)))))))))
end)))))))))))))))
end))))
end)))


let optimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 tc_assume -> (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2496, us, uu____2498, uu____2499, uu____2500, uu____2501, uu____2502) -> begin
us
end
| uu____2509 -> begin
(failwith "Impossible!")
end))
in (

let uu____2510 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____2510) with
| (usubst, us1) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env us1)
in (

let uu____2526 = (FStar_List.fold_left (optimized_haseq_ty datas usubst us1) (([]), (env1), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (uu____2526) with
| (axioms, env2, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let uu____2558 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi)
in (match (uu____2558) with
| (phi1, uu____2563) -> begin
((

let uu____2565 = (FStar_TypeChecker_Env.should_verify env2)
in (match (uu____2565) with
| true -> begin
(

let uu____2566 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi1)))
in (FStar_TypeChecker_Rel.force_trivial_guard env2 uu____2566))
end
| uu____2567 -> begin
()
end));
(

let ses = (FStar_List.fold_left (fun l uu____2574 -> (match (uu____2574) with
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

let uu____2617 = (

let uu____2618 = (FStar_Syntax_Subst.compress t)
in uu____2618.FStar_Syntax_Syntax.n)
in (match (uu____2617) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', uu____2628) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
(

let uu____2655 = (is_mutual t')
in (match (uu____2655) with
| true -> begin
true
end
| uu____2656 -> begin
(

let uu____2657 = (FStar_List.map Prims.fst args)
in (exists_mutual uu____2657))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t', uu____2670) -> begin
(is_mutual t')
end
| uu____2675 -> begin
false
end)))
and exists_mutual = (fun uu___78_2676 -> (match (uu___78_2676) with
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

let uu____2693 = (

let uu____2694 = (FStar_Syntax_Subst.compress dt1)
in uu____2694.FStar_Syntax_Syntax.n)
in (match (uu____2693) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____2700) -> begin
(

let dbs1 = (

let uu____2715 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd uu____2715))
in (

let dbs2 = (

let uu____2737 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____2737 dbs1))
in (

let dbs3 = (FStar_Syntax_Subst.open_binders dbs2)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (

let uu____2749 = (

let uu____2750 = (

let uu____2751 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (uu____2751)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2750))
in (uu____2749 None FStar_Range.dummyRange))
in (

let haseq_sort1 = (

let uu____2757 = (is_mutual sort)
in (match (uu____2757) with
| true -> begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end
| uu____2758 -> begin
haseq_sort
end))
in (FStar_Syntax_Util.mk_conj t haseq_sort1))))) FStar_Syntax_Util.t_true dbs3)
in (

let cond1 = (FStar_List.fold_right (fun b t -> (

let uu____2764 = (

let uu____2765 = (

let uu____2766 = (

let uu____2767 = (

let uu____2768 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____2768 None))
in (FStar_Syntax_Syntax.as_arg uu____2767))
in (uu____2766)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____2765))
in (uu____2764 None FStar_Range.dummyRange))) dbs3 cond)
in (FStar_Syntax_Util.mk_conj acc cond1))))))
end
| uu____2785 -> begin
acc
end))))))


let unoptimized_haseq_ty = (fun all_datas_in_the_bundle mutuals usubst us acc ty -> (

let uu____2828 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2840, bs, t, uu____2843, d_lids, uu____2845) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____2853 -> begin
(failwith "Impossible!")
end)
in (match (uu____2828) with
| (lid, bs, t, d_lids) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t1 = (

let uu____2869 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs1) usubst)
in (FStar_Syntax_Subst.subst uu____2869 t))
in (

let uu____2876 = (FStar_Syntax_Subst.open_term bs1 t1)
in (match (uu____2876) with
| (bs2, t2) -> begin
(

let ibs = (

let uu____2887 = (

let uu____2888 = (FStar_Syntax_Subst.compress t2)
in uu____2888.FStar_Syntax_Syntax.n)
in (match (uu____2887) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____2895) -> begin
ibs
end
| uu____2906 -> begin
[]
end))
in (

let ibs1 = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____2911 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____2912 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____2911 uu____2912)))
in (

let ind1 = (

let uu____2917 = (

let uu____2918 = (FStar_List.map (fun uu____2923 -> (match (uu____2923) with
| (bv, aq) -> begin
(

let uu____2930 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2930), (aq)))
end)) bs2)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____2918))
in (uu____2917 None FStar_Range.dummyRange))
in (

let ind2 = (

let uu____2938 = (

let uu____2939 = (FStar_List.map (fun uu____2944 -> (match (uu____2944) with
| (bv, aq) -> begin
(

let uu____2951 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____2951), (aq)))
end)) ibs1)
in (FStar_Syntax_Syntax.mk_Tm_app ind1 uu____2939))
in (uu____2938 None FStar_Range.dummyRange))
in (

let haseq_ind = (

let uu____2959 = (

let uu____2960 = (

let uu____2961 = (FStar_Syntax_Syntax.as_arg ind2)
in (uu____2961)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____2960))
in (uu____2959 None FStar_Range.dummyRange))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2969, uu____2970, uu____2971, t_lid, uu____2973, uu____2974, uu____2975) -> begin
(t_lid = lid)
end
| uu____2980 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let data_cond = (FStar_List.fold_left (unoptimized_haseq_data usubst bs2 haseq_ind mutuals) FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml1 = (

let uu___87_2986 = fml
in (

let uu____2987 = (

let uu____2988 = (

let uu____2993 = (

let uu____2994 = (

let uu____3001 = (

let uu____3003 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____3003)::[])
in (uu____3001)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____2994))
in ((fml), (uu____2993)))
in FStar_Syntax_Syntax.Tm_meta (uu____2988))
in {FStar_Syntax_Syntax.n = uu____2987; FStar_Syntax_Syntax.tk = uu___87_2986.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___87_2986.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___87_2986.FStar_Syntax_Syntax.vars}))
in (

let fml2 = (FStar_List.fold_right (fun b t3 -> (

let uu____3015 = (

let uu____3016 = (

let uu____3017 = (

let uu____3018 = (

let uu____3019 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____3019 None))
in (FStar_Syntax_Syntax.as_arg uu____3018))
in (uu____3017)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____3016))
in (uu____3015 None FStar_Range.dummyRange))) ibs1 fml1)
in (

let fml3 = (FStar_List.fold_right (fun b t3 -> (

let uu____3041 = (

let uu____3042 = (

let uu____3043 = (

let uu____3044 = (

let uu____3045 = (FStar_Syntax_Subst.close ((b)::[]) t3)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____3045 None))
in (FStar_Syntax_Syntax.as_arg uu____3044))
in (uu____3043)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____3042))
in (uu____3041 None FStar_Range.dummyRange))) bs2 fml2)
in (FStar_Syntax_Util.mk_conj acc fml3)))))))))))))
end))))
end)))


let unoptimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 tc_assume -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3114, uu____3115, uu____3116, uu____3117, uu____3118, uu____3119) -> begin
lid
end
| uu____3126 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let uu____3127 = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, uu____3135, uu____3136, uu____3137, uu____3138, uu____3139) -> begin
((lid), (us))
end
| uu____3146 -> begin
(failwith "Impossible!")
end))
in (match (uu____3127) with
| (lid, us) -> begin
(

let uu____3152 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____3152) with
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

let uu____3170 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env1 uu____3170 fml [] FStar_Range.dummyRange))
in ((env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
(se)::[];
)));
)))
end))
end))))


let check_inductive_well_typedness : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let uu____3200 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___79_3210 -> (match (uu___79_3210) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____3211); FStar_Syntax_Syntax.sigrng = uu____3212} -> begin
true
end
| uu____3223 -> begin
false
end))))
in (match (uu____3200) with
| (tys, datas) -> begin
((

let uu____3236 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun uu___80_3238 -> (match (uu___80_3238) with
| {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____3239); FStar_Syntax_Syntax.sigrng = uu____3240} -> begin
false
end
| uu____3250 -> begin
true
end))))
in (match (uu____3236) with
| true -> begin
(

let uu____3251 = (

let uu____3252 = (

let uu____3255 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (uu____3255)))
in FStar_Errors.Error (uu____3252))
in (Prims.raise uu____3251))
end
| uu____3256 -> begin
()
end));
(

let env0 = env
in (

let uu____3258 = (FStar_List.fold_right (fun tc uu____3272 -> (match (uu____3272) with
| (env1, all_tcs, g) -> begin
(

let uu____3294 = (tc_tycon env1 tc)
in (match (uu____3294) with
| (env2, tc1, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in ((

let uu____3311 = (FStar_TypeChecker_Env.debug env2 FStar_Options.Low)
in (match (uu____3311) with
| true -> begin
(

let uu____3312 = (FStar_Syntax_Print.sigelt_to_string tc1)
in (FStar_Util.print1 "Checked inductive: %s\n" uu____3312))
end
| uu____3313 -> begin
()
end));
(

let uu____3314 = (

let uu____3315 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g uu____3315))
in ((env2), ((((tc1), (tc_u)))::all_tcs), (uu____3314)));
))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____3258) with
| (env1, tcs, g) -> begin
(

let uu____3340 = (FStar_List.fold_right (fun se uu____3348 -> (match (uu____3348) with
| (datas1, g1) -> begin
(

let uu____3359 = (

let uu____3362 = (tc_data env1 tcs)
in (uu____3362 se))
in (match (uu____3359) with
| (data, g') -> begin
(

let uu____3372 = (FStar_TypeChecker_Rel.conj_guard g1 g')
in (((data)::datas1), (uu____3372)))
end))
end)) datas (([]), (g)))
in (match (uu____3340) with
| (datas1, g1) -> begin
(

let uu____3384 = (generalize_and_inst_within env0 g1 tcs datas1)
in (match (uu____3384) with
| (tcs1, datas2) -> begin
(

let sig_bndle = (

let uu____3401 = (FStar_TypeChecker_Env.get_range env0)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((FStar_List.append tcs1 datas2)), (quals), (lids))); FStar_Syntax_Syntax.sigrng = uu____3401})
in ((sig_bndle), (tcs1), (datas2)))
end))
end))
end)));
)
end)))




