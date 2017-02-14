
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
(let _0_172 = (let _0_171 = (let _0_170 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _0_170))
in (FStar_TypeChecker_Rel.discharge_guard env' _0_171))
in ((t), (_0_172)))
end))
in (match (uu____93) with
| (t, guard) -> begin
(

let k = (let _0_173 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _0_173))
in (

let uu____114 = (FStar_Syntax_Util.type_u ())
in (match (uu____114) with
| (t_type, u) -> begin
((let _0_174 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _0_174));
(

let t_tc = (let _0_175 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _0_175))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _0_176 = (FStar_TypeChecker_Env.push_let_binding env (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_0_176), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard)))))));
)
end)))
end))
end))
end))
end))
end))
end
| uu____139 -> begin
(failwith "impossible")
end))


let tc_data : FStar_TypeChecker_Env.env_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.guard_t) = (fun env tcs uu___76_164 -> (match (uu___76_164) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let uu____180 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun uu____194 -> (match (uu____194) with
| (se, u_tc) -> begin
(

let uu____203 = (let _0_177 = (FStar_Util.must (FStar_Syntax_Util.lid_of_sigelt se))
in (FStar_Ident.lid_equals tc_lid _0_177))
in (match (uu____203) with
| true -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____212, uu____213, tps, uu____215, uu____216, uu____217, uu____218, uu____219) -> begin
(

let tps = (FStar_All.pipe_right tps (FStar_List.map (fun uu____240 -> (match (uu____240) with
| (x, uu____247) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let tps = (FStar_Syntax_Subst.open_binders tps)
in Some ((let _0_178 = (FStar_TypeChecker_Env.push_binders env tps)
in ((_0_178), (tps), (u_tc))))))
end
| uu____253 -> begin
(failwith "Impossible")
end)
end
| uu____258 -> begin
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
| uu____283 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected data constructor"), (r)))))
end)
end))
in (match (uu____180) with
| (env, tps, u_tc) -> begin
(

let uu____292 = (

let uu____300 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____300) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let uu____320 = (FStar_Util.first_N ntps bs)
in (match (uu____320) with
| (uu____338, bs') -> begin
(

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res))))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i uu____374 -> (match (uu____374) with
| (x, uu____378) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (FStar_Syntax_Util.arrow_formals (FStar_Syntax_Subst.subst subst t))))
end))
end
| uu____379 -> begin
(([]), (t))
end))
in (match (uu____292) with
| (arguments, result) -> begin
((

let uu____400 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____400) with
| true -> begin
(let _0_181 = (FStar_Syntax_Print.lid_to_string c)
in (let _0_180 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _0_179 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _0_181 _0_180 _0_179))))
end
| uu____401 -> begin
()
end));
(

let uu____402 = (FStar_TypeChecker_TcTerm.tc_tparams env arguments)
in (match (uu____402) with
| (arguments, env', us) -> begin
(

let uu____411 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (uu____411) with
| (result, res_lcomp) -> begin
((

let uu____419 = (FStar_Syntax_Subst.compress res_lcomp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n
in (match (uu____419) with
| FStar_Syntax_Syntax.Tm_type (uu____420) -> begin
()
end
| ty -> begin
(Prims.raise (FStar_Errors.Error ((let _0_184 = (let _0_183 = (FStar_Syntax_Print.term_to_string result)
in (let _0_182 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" _0_183 _0_182)))
in ((_0_184), (r))))))
end));
(

let uu____422 = (FStar_Syntax_Util.head_and_args result)
in (match (uu____422) with
| (head, uu____435) -> begin
((

let uu____451 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in (match (uu____451) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| uu____453 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_187 = (let _0_186 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _0_185 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _0_186 _0_185)))
in ((_0_187), (r))))))
end));
(

let g = (FStar_List.fold_left2 (fun g uu____458 u_x -> (match (uu____458) with
| (x, uu____463) -> begin
(let _0_188 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _0_188))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _0_191 = (let _0_189 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____479 -> (match (uu____479) with
| (x, uu____486) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _0_189 arguments))
in (let _0_190 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _0_191 _0_190)))
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
| uu____493 -> begin
(failwith "impossible")
end))


let generalize_and_inst_within : FStar_TypeChecker_Env.env_t  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env g tcs datas -> (

let tc_universe_vars = (FStar_List.map Prims.snd tcs)
in (

let g = (

let uu___82_529 = g
in {FStar_TypeChecker_Env.guard_f = uu___82_529.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___82_529.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((tc_universe_vars), ((Prims.snd g.FStar_TypeChecker_Env.univ_ineqs))); FStar_TypeChecker_Env.implicits = uu___82_529.FStar_TypeChecker_Env.implicits})
in ((

let uu____535 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____535) with
| true -> begin
(let _0_192 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print1 "@@@@@@Guard before generalization: %s\n" _0_192))
end
| uu____536 -> begin
()
end));
(FStar_TypeChecker_Rel.force_trivial_guard env g);
(

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun uu____546 -> (match (uu____546) with
| (se, uu____550) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____551, uu____552, tps, k, uu____555, uu____556, uu____557, uu____558) -> begin
(FStar_Syntax_Syntax.null_binder (let _0_193 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _0_193)))
end
| uu____569 -> begin
(failwith "Impossible")
end)
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun uu___77_574 -> (match (uu___77_574) with
| FStar_Syntax_Syntax.Sig_datacon (uu____575, uu____576, t, uu____578, uu____579, uu____580, uu____581, uu____582) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| uu____587 -> begin
(failwith "Impossible")
end))))
in (

let t = (let _0_194 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _0_194))
in ((

let uu____592 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____592) with
| true -> begin
(let _0_195 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _0_195))
end
| uu____593 -> begin
()
end));
(

let uu____594 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (uu____594) with
| (uvs, t) -> begin
((

let uu____604 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____604) with
| true -> begin
(let _0_198 = (let _0_196 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _0_196 (FStar_String.concat ", ")))
in (let _0_197 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _0_198 _0_197)))
end
| uu____609 -> begin
()
end));
(

let uu____610 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____610) with
| (uvs, t) -> begin
(

let uu____619 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____619) with
| (args, uu____632) -> begin
(

let uu____643 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (uu____643) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun uu____680 uu____681 -> (match (((uu____680), (uu____681))) with
| ((x, uu____691), (se, uu____693)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____699, tps, uu____701, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let uu____713 = (

let uu____721 = (FStar_Syntax_Subst.compress ty).FStar_Syntax_Syntax.n
in (match (uu____721) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____741 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (uu____741) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____784 -> begin
(let _0_199 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c))))) _0_199 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| uu____809 -> begin
(([]), (ty))
end))
in (match (uu____713) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| uu____835 -> begin
(failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| uu____839 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _0_200 -> FStar_Syntax_Syntax.U_name (_0_200))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun uu___78_856 -> (match (uu___78_856) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____861, uu____862, uu____863, uu____864, uu____865, uu____866, uu____867) -> begin
((tc), (uvs_universes))
end
| uu____875 -> begin
(failwith "Impossible")
end))))
in (FStar_List.map2 (fun uu____881 d -> (match (uu____881) with
| (t, uu____886) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____888, uu____889, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _0_201 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _0_201 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| uu____902 -> begin
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

let uu____911 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Positivity")))
in (match (uu____911) with
| true -> begin
(FStar_Util.print_string (Prims.strcat "Positivity::" (Prims.strcat s "\n")))
end
| uu____912 -> begin
()
end)))


let ty_occurs_in : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun ty_lid t -> (let _0_202 = (FStar_Syntax_Free.fvars t)
in (FStar_Util.set_mem ty_lid _0_202)))


let try_get_fv : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes) = (fun t -> (

let uu____926 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____926) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), (us))
end
| uu____940 -> begin
(failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
end)
end
| uu____943 -> begin
(failwith "Node is not an fvar or a Tm_uinst")
end)))


type unfolded_memo_elt =
(FStar_Ident.lident * FStar_Syntax_Syntax.args) Prims.list


type unfolded_memo_t =
unfolded_memo_elt FStar_ST.ref


let already_unfolded : FStar_Ident.lident  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ilid arrghs unfolded env -> (let _0_203 = (FStar_ST.read unfolded)
in (FStar_List.existsML (fun uu____967 -> (match (uu____967) with
| (lid, l) -> begin
((FStar_Ident.lid_equals lid ilid) && (

let args = (Prims.fst (FStar_List.splitAt (FStar_List.length l) arrghs))
in (FStar_List.fold_left2 (fun b a a' -> (b && (FStar_TypeChecker_Rel.teq_nosmt env (Prims.fst a) (Prims.fst a')))) true args l)))
end)) _0_203)))


let rec ty_strictly_positive_in_type : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid btype unfolded env -> ((let _0_205 = (let _0_204 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity in type: " _0_204))
in (debug_log env _0_205));
(

let btype = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env btype)
in ((let _0_207 = (let _0_206 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity in type, after normalization: " _0_206))
in (debug_log env _0_207));
((not ((ty_occurs_in ty_lid btype))) || ((debug_log env "ty does occur in this type, pressing ahead");
(

let uu____1072 = (FStar_Syntax_Subst.compress btype).FStar_Syntax_Syntax.n
in (match (uu____1072) with
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1089 = (try_get_fv t)
in (match (uu____1089) with
| (fv, us) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ty_lid)) with
| true -> begin
((debug_log env "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
(FStar_List.for_all (fun uu____1101 -> (match (uu____1101) with
| (t, uu____1105) -> begin
(not ((ty_occurs_in ty_lid t)))
end)) args);
)
end
| uu____1106 -> begin
((debug_log env "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
(ty_nested_positive_in_inductive ty_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v us args unfolded env);
)
end)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((debug_log env "Checking strict positivity in Tm_arrow");
(

let uu____1125 = (not ((FStar_Syntax_Util.is_pure_or_ghost_comp c)))
in (match (uu____1125) with
| true -> begin
((debug_log env "Checking strict positivity , the arrow is impure, so return true");
true;
)
end
| uu____1127 -> begin
((debug_log env "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
((FStar_List.for_all (fun uu____1131 -> (match (uu____1131) with
| (b, uu____1135) -> begin
(not ((ty_occurs_in ty_lid b.FStar_Syntax_Syntax.sort)))
end)) sbs) && (

let uu____1136 = (FStar_Syntax_Subst.open_term sbs (FStar_Syntax_Util.comp_result c))
in (match (uu____1136) with
| (uu____1139, return_type) -> begin
(let _0_208 = (FStar_TypeChecker_Env.push_binders env sbs)
in (ty_strictly_positive_in_type ty_lid return_type unfolded _0_208))
end)));
)
end));
)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____1141) -> begin
((debug_log env "Checking strict positivity in an fvar, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_type (uu____1143) -> begin
((debug_log env "Checking strict positivity in an Tm_type, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____1146) -> begin
((debug_log env "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____1153) -> begin
((debug_log env "Checking strict positivity in an Tm_refine, recur in the bv sort)");
(ty_strictly_positive_in_type ty_lid bv.FStar_Syntax_Syntax.sort unfolded env);
)
end
| FStar_Syntax_Syntax.Tm_match (uu____1159, branches) -> begin
((debug_log env "Checking strict positivity in an Tm_match, recur in the branches)");
(FStar_List.for_all (fun uu____1194 -> (match (uu____1194) with
| (p, uu____1202, t) -> begin
(

let bs = (let _0_209 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_List.map FStar_Syntax_Syntax.mk_binder _0_209))
in (

let uu____1212 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____1212) with
| (bs, t) -> begin
(let _0_210 = (FStar_TypeChecker_Env.push_binders env bs)
in (ty_strictly_positive_in_type ty_lid t unfolded _0_210))
end)))
end)) branches);
)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____1218, uu____1219) -> begin
((debug_log env "Checking strict positivity in an Tm_ascribed, recur)");
(ty_strictly_positive_in_type ty_lid t unfolded env);
)
end
| uu____1239 -> begin
((let _0_215 = (let _0_214 = (let _0_213 = (FStar_Syntax_Print.tag_of_term btype)
in (let _0_212 = (let _0_211 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat " and term: " _0_211))
in (Prims.strcat _0_213 _0_212)))
in (Prims.strcat "Checking strict positivity, unexpected tag: " _0_214))
in (debug_log env _0_215));
false;
)
end));
));
));
))
and ty_nested_positive_in_inductive : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid ilid us args unfolded env -> ((let _0_219 = (let _0_218 = (let _0_217 = (let _0_216 = (FStar_Syntax_Print.args_to_string args)
in (Prims.strcat " applied to arguments: " _0_216))
in (Prims.strcat ilid.FStar_Ident.str _0_217))
in (Prims.strcat "Checking nested positivity in the inductive " _0_218))
in (debug_log env _0_219));
(

let uu____1248 = (FStar_TypeChecker_Env.datacons_of_typ env ilid)
in (match (uu____1248) with
| (b, idatas) -> begin
(match ((not (b))) with
| true -> begin
((debug_log env "Checking nested positivity, not an inductive, return false");
false;
)
end
| uu____1257 -> begin
(

let uu____1258 = (already_unfolded ilid args unfolded env)
in (match (uu____1258) with
| true -> begin
((debug_log env "Checking nested positivity, we have already unfolded this inductive with these args");
true;
)
end
| uu____1260 -> begin
(

let num_ibs = (FStar_TypeChecker_Env.num_inductive_ty_params env ilid)
in ((let _0_222 = (let _0_221 = (let _0_220 = (FStar_Util.string_of_int num_ibs)
in (Prims.strcat _0_220 ", also adding to the memo table"))
in (Prims.strcat "Checking nested positivity, number of type parameters is " _0_221))
in (debug_log env _0_222));
(let _0_227 = (let _0_226 = (FStar_ST.read unfolded)
in (let _0_225 = (let _0_224 = (let _0_223 = (Prims.fst (FStar_List.splitAt num_ibs args))
in ((ilid), (_0_223)))
in (_0_224)::[])
in (FStar_List.append _0_226 _0_225)))
in (FStar_ST.write unfolded _0_227));
(FStar_List.for_all (fun d -> (ty_nested_positive_in_dlid ty_lid d ilid us args num_ibs unfolded env)) idatas);
))
end))
end)
end));
))
and ty_nested_positive_in_dlid : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universes  ->  FStar_Syntax_Syntax.args  ->  Prims.int  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env_t  ->  Prims.bool = (fun ty_lid dlid ilid us args num_ibs unfolded env -> ((debug_log env (Prims.strcat "Checking nested positivity in data constructor " (Prims.strcat dlid.FStar_Ident.str (Prims.strcat " of the inductive " ilid.FStar_Ident.str))));
(

let uu____1309 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____1309) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____1321 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(

let dt = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env dt)
in ((let _0_229 = (let _0_228 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking nested positivity in the data constructor type: " _0_228))
in (debug_log env _0_229));
(

let uu____1324 = (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
in (match (uu____1324) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, c) -> begin
((debug_log env "Checked nested positivity in Tm_arrow data constructor type");
(

let uu____1338 = (FStar_List.splitAt num_ibs dbs)
in (match (uu____1338) with
| (ibs, dbs) -> begin
(

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let dbs = (let _0_230 = (FStar_Syntax_Subst.opening_of_binders ibs)
in (FStar_Syntax_Subst.subst_binders _0_230 dbs))
in (

let c = (let _0_231 = (FStar_Syntax_Subst.opening_of_binders ibs)
in (FStar_Syntax_Subst.subst_comp _0_231 c))
in (

let uu____1366 = (FStar_List.splitAt num_ibs args)
in (match (uu____1366) with
| (args, uu____1384) -> begin
(

let subst = (FStar_List.fold_left2 (fun subst ib arg -> (FStar_List.append subst ((FStar_Syntax_Syntax.NT ((((Prims.fst ib)), ((Prims.fst arg)))))::[]))) [] ibs args)
in (

let dbs = (FStar_Syntax_Subst.subst_binders subst dbs)
in (

let c = (let _0_232 = (FStar_Syntax_Subst.shift_subst (FStar_List.length dbs) subst)
in (FStar_Syntax_Subst.subst_comp _0_232 c))
in ((let _0_237 = (let _0_236 = (let _0_235 = (FStar_Syntax_Print.binders_to_string "; " dbs)
in (let _0_234 = (let _0_233 = (FStar_Syntax_Print.comp_to_string c)
in (Prims.strcat ", and c: " _0_233))
in (Prims.strcat _0_235 _0_234)))
in (Prims.strcat "Checking nested positivity in the unfolded data constructor binders as: " _0_236))
in (debug_log env _0_237));
(ty_nested_positive_in_type ty_lid (FStar_Syntax_Syntax.Tm_arrow (((dbs), (c)))) ilid num_ibs unfolded env);
))))
end)))))
end));
)
end
| uu____1436 -> begin
((debug_log env "Checking nested positivity in the data constructor type that is not an arrow");
(let _0_238 = (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
in (ty_nested_positive_in_type ty_lid _0_238 ilid num_ibs unfolded env));
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

let uu____1461 = (try_get_fv t)
in (match (uu____1461) with
| (fv, uu____1465) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ilid)) with
| true -> begin
true
end
| uu____1470 -> begin
(failwith "Impossible, expected the type to be ilid")
end)
end));
)
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((let _0_240 = (let _0_239 = (FStar_Syntax_Print.binders_to_string "; " sbs)
in (Prims.strcat "Checking nested positivity in an Tm_arrow node, with binders as: " _0_239))
in (debug_log env _0_240));
(

let uu____1484 = (FStar_List.fold_left (fun uu____1491 b -> (match (uu____1491) with
| (r, env) -> begin
(match ((not (r))) with
| true -> begin
((r), (env))
end
| uu____1503 -> begin
(let _0_242 = (ty_strictly_positive_in_type ty_lid (Prims.fst b).FStar_Syntax_Syntax.sort unfolded env)
in (let _0_241 = (FStar_TypeChecker_Env.push_binders env ((b)::[]))
in ((_0_242), (_0_241))))
end)
end)) ((true), (env)) sbs)
in (match (uu____1484) with
| (b, uu____1509) -> begin
b
end));
)
end
| uu____1510 -> begin
(failwith "Nested positive check, unhandled case")
end))


let ty_positive_in_datacon : FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.universes  ->  unfolded_memo_t  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty_lid dlid ty_bs us unfolded env -> (

let uu____1529 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____1529) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____1541 -> begin
(failwith "Impossible! Expected universe unification variables")
end)) univ_unif_vars us);
(let _0_244 = (let _0_243 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking data constructor type: " _0_243))
in (debug_log env _0_244));
(

let uu____1543 = (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
in (match (uu____1543) with
| FStar_Syntax_Syntax.Tm_fvar (uu____1544) -> begin
((debug_log env "Data constructor type is simply an fvar, returning true");
true;
)
end
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____1547) -> begin
(

let dbs = (Prims.snd (FStar_List.splitAt (FStar_List.length ty_bs) dbs))
in (

let dbs = (let _0_245 = (FStar_Syntax_Subst.opening_of_binders ty_bs)
in (FStar_Syntax_Subst.subst_binders _0_245 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in ((let _0_248 = (let _0_247 = (let _0_246 = (FStar_Util.string_of_int (FStar_List.length dbs))
in (Prims.strcat _0_246 " binders"))
in (Prims.strcat "Data constructor type is an arrow type, so checking strict positivity in " _0_247))
in (debug_log env _0_248));
(

let uu____1582 = (FStar_List.fold_left (fun uu____1589 b -> (match (uu____1589) with
| (r, env) -> begin
(match ((not (r))) with
| true -> begin
((r), (env))
end
| uu____1601 -> begin
(let _0_250 = (ty_strictly_positive_in_type ty_lid (Prims.fst b).FStar_Syntax_Syntax.sort unfolded env)
in (let _0_249 = (FStar_TypeChecker_Env.push_binders env ((b)::[]))
in ((_0_250), (_0_249))))
end)
end)) ((true), (env)) dbs)
in (match (uu____1582) with
| (b, uu____1607) -> begin
b
end));
))))
end
| FStar_Syntax_Syntax.Tm_app (uu____1608, uu____1609) -> begin
((debug_log env "Data constructor type is a Tm_app, so returning true");
true;
)
end
| uu____1625 -> begin
(failwith "Unexpected data constructor type when checking positivity")
end));
)
end)))


let check_positivity : FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env  ->  Prims.bool = (fun ty env -> (

let unfolded_inductives = (FStar_Util.mk_ref [])
in (

let uu____1643 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, bs, uu____1653, uu____1654, uu____1655, uu____1656, uu____1657) -> begin
((lid), (us), (bs))
end
| uu____1664 -> begin
(failwith "Impossible!")
end)
in (match (uu____1643) with
| (ty_lid, ty_us, ty_bs) -> begin
(

let uu____1671 = (FStar_Syntax_Subst.univ_var_opening ty_us)
in (match (uu____1671) with
| (ty_usubst, ty_us) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env ty_us)
in (

let env = (FStar_TypeChecker_Env.push_binders env ty_bs)
in (

let ty_bs = (FStar_Syntax_Subst.subst_binders ty_usubst ty_bs)
in (

let ty_bs = (FStar_Syntax_Subst.open_binders ty_bs)
in (let _0_252 = (Prims.snd (FStar_TypeChecker_Env.datacons_of_typ env ty_lid))
in (FStar_List.for_all (fun d -> (let _0_251 = (FStar_List.map (fun s -> FStar_Syntax_Syntax.U_name (s)) ty_us)
in (ty_positive_in_datacon ty_lid d ty_bs _0_251 unfolded_inductives env))) _0_252))))))
end))
end))))


let datacon_typ : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (uu____1694, uu____1695, t, uu____1697, uu____1698, uu____1699, uu____1700, uu____1701) -> begin
t
end
| uu____1706 -> begin
(failwith "Impossible!")
end))


let optimized_haseq_soundness_for_data : FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term = (fun ty_lid data usubst bs -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____1723 = (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
in (match (uu____1723) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____1725) -> begin
(

let dbs = (Prims.snd (FStar_List.splitAt (FStar_List.length bs) dbs))
in (

let dbs = (let _0_253 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _0_253 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = ((let _0_255 = (let _0_254 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_0_254)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_255)) None FStar_Range.dummyRange)
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (let _0_256 = (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" ty_lid.FStar_Ident.str)
in (FStar_TypeChecker_Util.label _0_256 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (FStar_List.fold_right (fun b t -> ((let _0_259 = (let _0_258 = (FStar_Syntax_Syntax.as_arg (let _0_257 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_257 None)))
in (_0_258)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_259)) None FStar_Range.dummyRange)) dbs cond)))))
end
| uu____1786 -> begin
FStar_Syntax_Util.t_true
end)))))


let optimized_haseq_ty = (fun all_datas_in_the_bundle usubst us acc ty -> (

let uu____1845 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____1857, bs, t, uu____1860, d_lids, uu____1862, uu____1863) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____1871 -> begin
(failwith "Impossible!")
end)
in (match (uu____1845) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _0_260 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _0_260 t))
in (

let uu____1901 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____1901) with
| (bs, t) -> begin
(

let ibs = (

let uu____1921 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____1921) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____1926) -> begin
ibs
end
| uu____1937 -> begin
[]
end))
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _0_262 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _0_261 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_262 _0_261)))
in (

let ind = ((let _0_264 = (FStar_List.map (fun uu____1954 -> (match (uu____1954) with
| (bv, aq) -> begin
(let _0_263 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_0_263), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _0_264)) None FStar_Range.dummyRange)
in (

let ind = ((let _0_266 = (FStar_List.map (fun uu____1972 -> (match (uu____1972) with
| (bv, aq) -> begin
(let _0_265 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_0_265), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _0_266)) None FStar_Range.dummyRange)
in (

let haseq_ind = ((let _0_268 = (let _0_267 = (FStar_Syntax_Syntax.as_arg ind)
in (_0_267)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_268)) None FStar_Range.dummyRange)
in (

let bs' = (FStar_List.filter (fun b -> (

let uu____1995 = acc
in (match (uu____1995) with
| (uu____2003, en, uu____2005, uu____2006) -> begin
(

let opt = (let _0_269 = (Prims.fst (FStar_Syntax_Util.type_u ()))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _0_269 false))
in (match (opt) with
| None -> begin
false
end
| Some (uu____2015) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _0_272 = ((let _0_271 = (let _0_270 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name (Prims.fst b)))
in (_0_270)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_271)) None FStar_Range.dummyRange)
in (FStar_Syntax_Util.mk_conj t _0_272))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let uu___83_2029 = fml
in (let _0_276 = FStar_Syntax_Syntax.Tm_meta ((let _0_275 = FStar_Syntax_Syntax.Meta_pattern ((let _0_274 = (let _0_273 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_0_273)::[])
in (_0_274)::[]))
in ((fml), (_0_275))))
in {FStar_Syntax_Syntax.n = _0_276; FStar_Syntax_Syntax.tk = uu___83_2029.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___83_2029.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___83_2029.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> ((let _0_279 = (let _0_278 = (FStar_Syntax_Syntax.as_arg (let _0_277 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_277 None)))
in (_0_278)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_279)) None FStar_Range.dummyRange)) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> ((let _0_282 = (let _0_281 = (FStar_Syntax_Syntax.as_arg (let _0_280 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_280 None)))
in (_0_281)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_282)) None FStar_Range.dummyRange)) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let uu____2081 = acc
in (match (uu____2081) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2115, uu____2116, uu____2117, t_lid, uu____2119, uu____2120, uu____2121, uu____2122) -> begin
(t_lid = lid)
end
| uu____2127 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let cond = (FStar_List.fold_left (fun acc d -> (let _0_283 = (optimized_haseq_soundness_for_data lid d usubst bs)
in (FStar_Syntax_Util.mk_conj acc _0_283))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _0_285 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _0_284 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_0_285), (_0_284)))))))))
end)))))))))))))))
end))))
end)))


let optimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 tc_assume -> (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2195, us, uu____2197, uu____2198, uu____2199, uu____2200, uu____2201, uu____2202) -> begin
us
end
| uu____2209 -> begin
(failwith "Impossible!")
end))
in (

let uu____2210 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____2210) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let uu____2226 = (FStar_List.fold_left (optimized_haseq_ty datas usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (uu____2226) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let uu____2258 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env phi)
in (match (uu____2258) with
| (phi, uu____2263) -> begin
((

let uu____2265 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____2265) with
| true -> begin
(let _0_286 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _0_286))
end
| uu____2266 -> begin
()
end));
(

let ses = (FStar_List.fold_left (fun l uu____2273 -> (match (uu____2273) with
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

let uu____2316 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____2316) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', uu____2324) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
(

let uu____2351 = (is_mutual t')
in (match (uu____2351) with
| true -> begin
true
end
| uu____2352 -> begin
(exists_mutual (FStar_List.map Prims.fst args))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t', uu____2362) -> begin
(is_mutual t')
end
| uu____2367 -> begin
false
end)))
and exists_mutual = (fun uu___79_2368 -> (match (uu___79_2368) with
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

let uu____2385 = (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
in (match (uu____2385) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____2389) -> begin
(

let dbs = (Prims.snd (FStar_List.splitAt (FStar_List.length bs) dbs))
in (

let dbs = (let _0_287 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _0_287 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = ((let _0_289 = (let _0_288 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_0_288)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_289)) None FStar_Range.dummyRange)
in (

let haseq_sort = (

let uu____2432 = (is_mutual sort)
in (match (uu____2432) with
| true -> begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end
| uu____2433 -> begin
haseq_sort
end))
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> ((let _0_292 = (let _0_291 = (FStar_Syntax_Syntax.as_arg (let _0_290 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_290 None)))
in (_0_291)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_292)) None FStar_Range.dummyRange)) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| uu____2455 -> begin
acc
end))))))


let unoptimized_haseq_ty = (fun all_datas_in_the_bundle mutuals usubst us acc ty -> (

let uu____2498 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2510, bs, t, uu____2513, d_lids, uu____2515, uu____2516) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____2524 -> begin
(failwith "Impossible!")
end)
in (match (uu____2498) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _0_293 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _0_293 t))
in (

let uu____2545 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____2545) with
| (bs, t) -> begin
(

let ibs = (

let uu____2556 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____2556) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____2561) -> begin
ibs
end
| uu____2572 -> begin
[]
end))
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _0_295 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _0_294 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_295 _0_294)))
in (

let ind = ((let _0_297 = (FStar_List.map (fun uu____2589 -> (match (uu____2589) with
| (bv, aq) -> begin
(let _0_296 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_0_296), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _0_297)) None FStar_Range.dummyRange)
in (

let ind = ((let _0_299 = (FStar_List.map (fun uu____2607 -> (match (uu____2607) with
| (bv, aq) -> begin
(let _0_298 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_0_298), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _0_299)) None FStar_Range.dummyRange)
in (

let haseq_ind = ((let _0_301 = (let _0_300 = (FStar_Syntax_Syntax.as_arg ind)
in (_0_300)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_301)) None FStar_Range.dummyRange)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2624, uu____2625, uu____2626, t_lid, uu____2628, uu____2629, uu____2630, uu____2631) -> begin
(t_lid = lid)
end
| uu____2636 -> begin
(failwith "Impossible")
end)) all_datas_in_the_bundle)
in (

let data_cond = (FStar_List.fold_left (unoptimized_haseq_data usubst bs haseq_ind mutuals) FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let uu___84_2642 = fml
in (let _0_305 = FStar_Syntax_Syntax.Tm_meta ((let _0_304 = FStar_Syntax_Syntax.Meta_pattern ((let _0_303 = (let _0_302 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_0_302)::[])
in (_0_303)::[]))
in ((fml), (_0_304))))
in {FStar_Syntax_Syntax.n = _0_305; FStar_Syntax_Syntax.tk = uu___84_2642.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___84_2642.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___84_2642.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> ((let _0_308 = (let _0_307 = (FStar_Syntax_Syntax.as_arg (let _0_306 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_306 None)))
in (_0_307)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_308)) None FStar_Range.dummyRange)) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> ((let _0_311 = (let _0_310 = (FStar_Syntax_Syntax.as_arg (let _0_309 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_309 None)))
in (_0_310)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_311)) None FStar_Range.dummyRange)) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))
end))))
end)))


let unoptimized_haseq_scheme : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun sig_bndle tcs datas env0 tc_assume -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2743, uu____2744, uu____2745, uu____2746, uu____2747, uu____2748, uu____2749) -> begin
lid
end
| uu____2756 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let uu____2757 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, uu____2765, uu____2766, uu____2767, uu____2768, uu____2769, uu____2770) -> begin
((lid), (us))
end
| uu____2777 -> begin
(failwith "Impossible!")
end))
in (match (uu____2757) with
| (lid, us) -> begin
(

let uu____2783 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____2783) with
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

let se = (let _0_312 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env _0_312 fml [] FStar_Range.dummyRange))
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
(se)::[];
)));
)))
end))
end))))


let check_inductive_well_typedness : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let uu____2830 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___80_2840 -> (match (uu___80_2840) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2841) -> begin
true
end
| uu____2853 -> begin
false
end))))
in (match (uu____2830) with
| (tys, datas) -> begin
((

let uu____2866 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun uu___81_2868 -> (match (uu___81_2868) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2869) -> begin
false
end
| uu____2880 -> begin
true
end))))
in (match (uu____2866) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_313 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_0_313))))))
end
| uu____2881 -> begin
()
end));
(

let env0 = env
in (

let uu____2883 = (FStar_List.fold_right (fun tc uu____2897 -> (match (uu____2897) with
| (env, all_tcs, g) -> begin
(

let uu____2919 = (tc_tycon env tc)
in (match (uu____2919) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in ((

let uu____2936 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2936) with
| true -> begin
(let _0_314 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _0_314))
end
| uu____2937 -> begin
()
end));
(let _0_316 = (let _0_315 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _0_315))
in ((env), ((((tc), (tc_u)))::all_tcs), (_0_316)));
))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____2883) with
| (env, tcs, g) -> begin
(

let uu____2962 = (FStar_List.fold_right (fun se uu____2970 -> (match (uu____2970) with
| (datas, g) -> begin
(

let uu____2981 = ((tc_data env tcs) se)
in (match (uu____2981) with
| (data, g') -> begin
(let _0_317 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_0_317)))
end))
end)) datas (([]), (g)))
in (match (uu____2962) with
| (datas, g) -> begin
(

let uu____3000 = (generalize_and_inst_within env0 g tcs datas)
in (match (uu____3000) with
| (tcs, datas) -> begin
(

let sig_bndle = FStar_Syntax_Syntax.Sig_bundle ((let _0_318 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_0_318))))
in ((sig_bndle), (tcs), (datas)))
end))
end))
end)));
)
end)))




