
open Prims

type name =
FStar_Syntax_Syntax.bv


type em_term =
FStar_Syntax_Syntax.term

type goal =
{context : FStar_TypeChecker_Env.env; witness : FStar_Syntax_Syntax.term Prims.option; goal_ty : FStar_Syntax_Syntax.term}

type proofstate =
{main_context : FStar_TypeChecker_Env.env; main_goal : goal; all_implicits : FStar_TypeChecker_Env.implicits; goals : goal Prims.list; smt_goals : goal Prims.list; transaction : FStar_Unionfind.tx}

type 'a result =
| Success of ('a * proofstate)
| Failed of (Prims.string * proofstate)


let uu___is_Success = (fun projectee -> (match (projectee) with
| Success (_0) -> begin
true
end
| uu____100 -> begin
false
end))


let __proj__Success__item___0 = (fun projectee -> (match (projectee) with
| Success (_0) -> begin
_0
end))


let uu___is_Failed = (fun projectee -> (match (projectee) with
| Failed (_0) -> begin
true
end
| uu____131 -> begin
false
end))


let __proj__Failed__item___0 = (fun projectee -> (match (projectee) with
| Failed (_0) -> begin
_0
end))

exception Failure of (Prims.string)


let uu___is_Failure : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Failure (uu____155) -> begin
true
end
| uu____156 -> begin
false
end))


let __proj__Failure__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Failure (uu____163) -> begin
uu____163
end))

type 'a tac =
{tac_f : proofstate  ->  'a result; tac_name : Prims.string; kernel : Prims.bool}


let kernel_tac = (fun n1 t -> {tac_f = t; tac_name = n1; kernel = true})


let user_tac = (fun n1 t -> {tac_f = t; tac_name = n1; kernel = false})


let name_tac = (fun n1 t -> (

let uu___82_275 = t
in {tac_f = uu___82_275.tac_f; tac_name = n1; kernel = false}))


let run = (fun t p -> (t.tac_f p))


let debug : proofstate  ->  Prims.string  ->  Prims.unit = (fun p msg -> (

let uu____298 = (FStar_Util.string_of_int (FStar_List.length p.goals))
in (

let uu____302 = (match (p.goals) with
| [] -> begin
"[]"
end
| uu____303 -> begin
(

let uu____305 = (

let uu____306 = (FStar_List.hd p.goals)
in uu____306.goal_ty)
in (FStar_Syntax_Print.term_to_string uu____305))
end)
in (

let uu____307 = (match (p.goals) with
| [] -> begin
""
end
| uu____308 -> begin
(

let uu____310 = (

let uu____312 = (FStar_List.tl p.goals)
in (FStar_All.pipe_right uu____312 (FStar_List.map (fun x -> (FStar_Syntax_Print.term_to_string x.goal_ty)))))
in (FStar_All.pipe_right uu____310 (FStar_String.concat ";;")))
end)
in (FStar_Util.print4 "TAC (ngoals=%s, maingoal=%s, rest=%s):\n\tTAC>> %s\n" uu____298 uu____302 uu____307 msg)))))


let print_proof_state : Prims.string  ->  Prims.unit tac = (fun msg -> (kernel_tac "print_proof_state" (fun p -> (

let uu____324 = ((debug p msg);
((()), (p));
)
in Success (uu____324)))))


let ret = (fun a -> (kernel_tac "return" (fun p -> Success (((a), (p))))))


let bind = (fun t1 t2 -> (kernel_tac "bind" (fun p -> (

let uu____362 = (t1.tac_f p)
in (match (uu____362) with
| Success (a, q) -> begin
(

let t21 = (t2 a)
in (t21.tac_f q))
end
| Failed (msg, q) -> begin
Failed (((msg), (q)))
end)))))


let get : proofstate tac = (kernel_tac "get" (fun p -> Success (((p), (p)))))


let fail = (fun msg -> (kernel_tac "fail" (fun p -> Failed (((msg), (p))))))


let set : proofstate  ->  Prims.unit tac = (fun p -> (kernel_tac "set" (fun uu____387 -> Success (((()), (p))))))


let solve : goal  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun goal solution -> (match (goal.witness) with
| None -> begin
()
end
| Some (w) -> begin
(

let uu____395 = (FStar_TypeChecker_Rel.teq_nosmt goal.context w solution)
in (match (uu____395) with
| true -> begin
()
end
| uu____396 -> begin
(

let uu____397 = (

let uu____398 = (

let uu____399 = (FStar_Syntax_Print.term_to_string solution)
in (

let uu____400 = (FStar_Syntax_Print.term_to_string w)
in (

let uu____401 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (FStar_Util.format3 "%s does not solve %s : %s" uu____399 uu____400 uu____401))))
in Failure (uu____398))
in (Prims.raise uu____397))
end))
end))


let dismiss : Prims.unit tac = (bind get (fun p -> (

let uu____404 = (

let uu___83_405 = p
in (

let uu____406 = (FStar_List.tl p.goals)
in {main_context = uu___83_405.main_context; main_goal = uu___83_405.main_goal; all_implicits = uu___83_405.all_implicits; goals = uu____406; smt_goals = uu___83_405.smt_goals; transaction = uu___83_405.transaction}))
in (set uu____404))))


let dismiss_all : Prims.unit tac = (bind get (fun p -> (set (

let uu___84_410 = p
in {main_context = uu___84_410.main_context; main_goal = uu___84_410.main_goal; all_implicits = uu___84_410.all_implicits; goals = []; smt_goals = uu___84_410.smt_goals; transaction = uu___84_410.transaction}))))


let add_goals : goal Prims.list  ->  Prims.unit tac = (fun gs -> (bind get (fun p -> (set (

let uu___85_419 = p
in {main_context = uu___85_419.main_context; main_goal = uu___85_419.main_goal; all_implicits = uu___85_419.all_implicits; goals = (FStar_List.append gs p.goals); smt_goals = uu___85_419.smt_goals; transaction = uu___85_419.transaction})))))


let add_smt_goals : goal Prims.list  ->  Prims.unit tac = (fun gs -> (bind get (fun p -> (set (

let uu___86_428 = p
in {main_context = uu___86_428.main_context; main_goal = uu___86_428.main_goal; all_implicits = uu___86_428.all_implicits; goals = uu___86_428.goals; smt_goals = (FStar_List.append gs p.smt_goals); transaction = uu___86_428.transaction})))))


let replace_cur : goal  ->  Prims.unit tac = (fun g -> (bind dismiss (fun uu____434 -> (add_goals ((g)::[])))))


let add_implicits : FStar_TypeChecker_Env.implicits  ->  Prims.unit tac = (fun i -> (bind get (fun p -> (set (

let uu___87_441 = p
in {main_context = uu___87_441.main_context; main_goal = uu___87_441.main_goal; all_implicits = (FStar_List.append i p.all_implicits); goals = uu___87_441.goals; smt_goals = uu___87_441.smt_goals; transaction = uu___87_441.transaction})))))


let is_true : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____451 = (FStar_Syntax_Util.destruct_typ_as_formula t)
in (match (uu____451) with
| Some (FStar_Syntax_Util.BaseConn (l, [])) -> begin
(FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid)
end
| uu____463 -> begin
false
end)))


let is_false : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____468 = (FStar_Syntax_Util.destruct_typ_as_formula t)
in (match (uu____468) with
| Some (FStar_Syntax_Util.BaseConn (l, [])) -> begin
(FStar_Ident.lid_equals l FStar_Syntax_Const.false_lid)
end
| uu____480 -> begin
false
end)))


let conj_goals : goal  ->  goal  ->  goal = (fun g1 g2 -> (

let t1 = g1.goal_ty
in (

let t2 = g2.goal_ty
in (

let uu____490 = ((is_true t1) || (is_false t2))
in (match (uu____490) with
| true -> begin
g2
end
| uu____491 -> begin
(

let uu____492 = ((is_true t2) || (is_false t1))
in (match (uu____492) with
| true -> begin
g1
end
| uu____493 -> begin
(

let uu___88_494 = g1
in (

let uu____495 = (FStar_Syntax_Util.mk_conj t1 t2)
in {context = uu___88_494.context; witness = uu___88_494.witness; goal_ty = uu____495}))
end))
end)))))


let with_cur_goal = (fun nm f -> (

let uu____516 = (bind get (fun p -> (match (p.goals) with
| [] -> begin
(fail "No more goals")
end
| (hd1)::tl1 -> begin
(f hd1)
end)))
in (name_tac nm uu____516)))


let cur_goal : goal tac = (kernel_tac "cur_goal" (fun ps -> (match (ps.goals) with
| (hd1)::uu____527 -> begin
Success (((hd1), (ps)))
end
| uu____529 -> begin
Failed ((("No goals left"), (ps)))
end)))


let set_cur_goal : goal  ->  Prims.unit tac = (fun g -> (kernel_tac "set_cur_goal" (fun ps -> (match (ps.goals) with
| (hd1)::tl1 -> begin
Success (((()), ((

let uu___89_541 = ps
in {main_context = uu___89_541.main_context; main_goal = uu___89_541.main_goal; all_implicits = uu___89_541.all_implicits; goals = (g)::tl1; smt_goals = uu___89_541.smt_goals; transaction = uu___89_541.transaction}))))
end
| uu____542 -> begin
Failed ((("No goals left"), (ps)))
end))))


let replace_point : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e1 e2 t -> (

let uu____553 = (FStar_Syntax_Util.term_eq e1 t)
in (match (uu____553) with
| true -> begin
e2
end
| uu____554 -> begin
t
end)))


let rec replace_in_term : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e1 e2 t -> (FStar_Syntax_Util.bottom_fold (replace_point e1 e2) t))


let treplace = (fun env e1 e2 t -> (replace_in_term e1 e2 t))


let grewrite_impl : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun t1 t2 e1 e2 -> (bind cur_goal (fun g -> (

let env = g.context
in (

let ok = (

let uu____603 = (FStar_TypeChecker_Rel.try_teq true env t1 t2)
in (match (uu____603) with
| None -> begin
false
end
| Some (g1) -> begin
(FStar_TypeChecker_Rel.is_trivial g1)
end))
in (match (ok) with
| true -> begin
(

let goal_ty' = (treplace env e1 e2 g.goal_ty)
in (

let uu____608 = (set_cur_goal (

let uu___90_610 = g
in {context = uu___90_610.context; witness = uu___90_610.witness; goal_ty = goal_ty'}))
in (bind uu____608 (fun uu____611 -> (

let uu____612 = (

let uu____614 = (

let uu____615 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero t1 e1 e2)
in {context = g.context; witness = None; goal_ty = uu____615})
in (uu____614)::[])
in (add_goals uu____612))))))
end
| uu____616 -> begin
((FStar_TypeChecker_Err.add_errors env (((("Ill-type rewriting requested"), (e1.FStar_Syntax_Syntax.pos)))::[]));
(fail "grewrite: Ill-typed rewriting requested");
)
end))))))


let smt : Prims.unit tac = (with_cur_goal "smt" (fun g -> (bind dismiss (fun uu____624 -> (

let uu____625 = (add_goals (((

let uu___91_627 = g
in {context = uu___91_627.context; witness = uu___91_627.witness; goal_ty = FStar_Syntax_Util.t_true}))::[]))
in (bind uu____625 (fun uu____628 -> (add_smt_goals ((g)::[])))))))))


let focus_cur_goal = (fun nm f -> (bind get (fun p -> (match (p.goals) with
| [] -> begin
(fail "No more goals")
end
| (hd1)::tl1 -> begin
(

let q = (

let uu___92_650 = p
in {main_context = uu___92_650.main_context; main_goal = uu___92_650.main_goal; all_implicits = uu___92_650.all_implicits; goals = (hd1)::[]; smt_goals = uu___92_650.smt_goals; transaction = uu___92_650.transaction})
in (

let uu____651 = (set q)
in (bind uu____651 (fun uu____653 -> (bind f (fun a -> (bind get (fun q' -> (

let q2 = (

let uu___93_657 = q'
in {main_context = uu___93_657.main_context; main_goal = uu___93_657.main_goal; all_implicits = uu___93_657.all_implicits; goals = (FStar_List.append q'.goals tl1); smt_goals = uu___93_657.smt_goals; transaction = uu___93_657.transaction})
in (

let uu____658 = (set q2)
in (bind uu____658 (fun uu____660 -> (ret a)))))))))))))
end))))


let cur_goal_and_rest = (fun f g -> (bind get (fun p -> (match (p.goals) with
| [] -> begin
(fail "No more goals")
end
| (uu____694)::[] -> begin
(bind f (fun a -> (ret ((a), (None)))))
end
| (hd1)::tl1 -> begin
(bind dismiss_all (fun uu____709 -> (

let uu____710 = (add_goals ((hd1)::[]))
in (bind uu____710 (fun uu____715 -> (bind f (fun a -> (bind get (fun uu____723 -> (match (uu____723) with
| {main_context = uu____728; main_goal = uu____729; all_implicits = uu____730; goals = sub_goals_f; smt_goals = uu____732; transaction = uu____733} -> begin
(bind dismiss_all (fun uu____739 -> (

let uu____740 = (add_goals tl1)
in (bind uu____740 (fun uu____745 -> (bind g (fun b -> (

let uu____750 = (add_goals sub_goals_f)
in (bind uu____750 (fun uu____755 -> (ret ((a), (Some (b))))))))))))))
end))))))))))
end))))


let or_else = (fun t1 t2 -> (kernel_tac "or_else" (fun p -> (

let uu____778 = (t1.tac_f p)
in (match (uu____778) with
| Failed (uu____781) -> begin
(t2.tac_f p)
end
| q -> begin
q
end)))))


let rec map = (fun t -> (user_tac "map" (fun p -> (

let uu____799 = (

let uu____802 = (

let uu____808 = (map t)
in (cur_goal_and_rest t uu____808))
in (bind uu____802 (fun uu___81_817 -> (match (uu___81_817) with
| (hd1, None) -> begin
(ret ((hd1)::[]))
end
| (hd1, Some (tl1)) -> begin
(ret ((hd1)::tl1))
end))))
in (run uu____799 p)))))


let map_goal_term : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  Prims.unit tac = (fun f -> (

let aux = (with_cur_goal "map_goal" (fun g -> (

let uu____850 = (

let uu___94_851 = g
in (

let uu____852 = (f g.goal_ty)
in {context = uu___94_851.context; witness = uu___94_851.witness; goal_ty = uu____852}))
in (replace_cur uu____850))))
in (

let uu____853 = (map aux)
in (bind uu____853 (fun uu____857 -> (ret ()))))))


let map_meta = (fun t -> (with_cur_goal "map_meta" (fun g -> (

let uu____870 = (

let uu____871 = (FStar_Syntax_Subst.compress g.goal_ty)
in uu____871.FStar_Syntax_Syntax.n)
in (match (uu____870) with
| FStar_Syntax_Syntax.Tm_meta (f, annot) -> begin
(

let uu____881 = (replace_cur (

let uu___95_883 = g
in {context = uu___95_883.context; witness = uu___95_883.witness; goal_ty = f}))
in (bind uu____881 (fun uu____884 -> (bind t (fun a -> (

let uu____886 = (map_goal_term (fun tm -> (

let uu____889 = (is_true tm)
in (match (uu____889) with
| true -> begin
tm
end
| uu____890 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((tm), (annot)))) None tm.FStar_Syntax_Syntax.pos)
end))))
in (bind uu____886 (fun uu____895 -> (ret a)))))))))
end
| uu____896 -> begin
(fail "Not a meta")
end)))))


let seq : Prims.unit tac  ->  Prims.unit tac  ->  Prims.unit tac = (fun t1 t2 -> (

let uu____909 = (bind t1 (fun uu____911 -> (

let uu____912 = (map t2)
in (bind uu____912 (fun uu____916 -> (ret ()))))))
in (focus_cur_goal "seq" uu____909)))


let intros : FStar_Syntax_Syntax.binders tac = (with_cur_goal "intros" (fun goal -> (

let uu____920 = (FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty)
in (match (uu____920) with
| Some (FStar_Syntax_Util.QAll (bs, pats, body)) -> begin
(

let new_context = (FStar_TypeChecker_Env.push_binders goal.context bs)
in (

let new_goal = {context = new_context; witness = None; goal_ty = body}
in (bind dismiss (fun uu____928 -> (

let uu____929 = (add_goals ((new_goal)::[]))
in (bind uu____929 (fun uu____931 -> (ret bs))))))))
end
| uu____932 -> begin
(fail "Cannot intro this goal, expected a forall")
end))))


let intros_no_names : Prims.unit tac = (bind intros (fun uu____935 -> (ret ())))


let mk_squash = (fun p -> (

let sq = (FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid)
in (

let uu____946 = (

let uu____952 = (FStar_Syntax_Syntax.as_arg p)
in (uu____952)::[])
in (FStar_Syntax_Util.mk_app sq uu____946))))


let un_squash : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option = (fun t -> (

let uu____959 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____959) with
| (head1, args) -> begin
(

let uu____988 = (

let uu____996 = (

let uu____997 = (FStar_Syntax_Util.un_uinst head1)
in uu____997.FStar_Syntax_Syntax.n)
in ((uu____996), (args)))
in (match (uu____988) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____1010))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid) -> begin
Some (p)
end
| (FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____1030; FStar_Syntax_Syntax.index = uu____1031; FStar_Syntax_Syntax.sort = {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____1033; FStar_Syntax_Syntax.pos = uu____1034; FStar_Syntax_Syntax.vars = uu____1035}}, p), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) -> begin
Some (p)
end
| uu____1054 -> begin
None
end))
end)))


let imp_intro : FStar_Syntax_Syntax.binder tac = (with_cur_goal "imp_intro" (fun goal -> (

let uu____1066 = (FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty)
in (match (uu____1066) with
| Some (FStar_Syntax_Util.BaseConn (l, ((lhs, uu____1071))::((rhs, uu____1073))::[])) when (FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid) -> begin
(

let name = (FStar_Syntax_Syntax.new_bv None lhs)
in (

let new_goal = (

let uu____1101 = (FStar_TypeChecker_Env.push_bv goal.context name)
in {context = uu____1101; witness = None; goal_ty = rhs})
in (bind dismiss (fun uu____1102 -> (

let uu____1103 = (add_goals ((new_goal)::[]))
in (bind uu____1103 (fun uu____1105 -> (

let uu____1106 = (FStar_Syntax_Syntax.mk_binder name)
in (ret uu____1106)))))))))
end
| uu____1107 -> begin
(fail "Cannot intro this goal, expected an \'==>\'")
end))))


let split : Prims.unit tac = (with_cur_goal "split" (fun goal -> (

let uu____1111 = (FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty)
in (match (uu____1111) with
| Some (FStar_Syntax_Util.BaseConn (l, args)) when (FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid) -> begin
(

let new_goals = (FStar_All.pipe_right args (FStar_List.map (fun uu____1121 -> (match (uu____1121) with
| (a, uu____1125) -> begin
(

let uu___96_1126 = goal
in {context = uu___96_1126.context; witness = None; goal_ty = a})
end))))
in (bind dismiss (fun uu____1127 -> (add_goals new_goals))))
end
| uu____1128 -> begin
(fail "Cannot split this goal; expected a conjunction")
end))))


let trivial : Prims.unit tac = (with_cur_goal "trivial" (fun goal -> (

let steps = (FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Primops)::[]
in (

let t = (FStar_TypeChecker_Normalize.normalize steps goal.context goal.goal_ty)
in (

let uu____1135 = (FStar_Syntax_Util.destruct_typ_as_formula t)
in (match (uu____1135) with
| Some (FStar_Syntax_Util.BaseConn (l, [])) when (FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid) -> begin
(bind dismiss (fun uu____1148 -> (add_goals (((

let uu___97_1149 = goal
in {context = uu___97_1149.context; witness = uu___97_1149.witness; goal_ty = t}))::[]))))
end
| uu____1150 -> begin
(fail "Not a trivial goal")
end))))))


let apply_lemma : FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun tm -> (with_cur_goal "apply_lemma" (fun goal -> try
(match (()) with
| () -> begin
(

let uu____1161 = (goal.context.FStar_TypeChecker_Env.type_of goal.context tm)
in (match (uu____1161) with
| (tm1, t, guard) -> begin
(

let uu____1169 = (

let uu____1170 = (FStar_Syntax_Util.is_lemma t)
in (not (uu____1170)))
in (match (uu____1169) with
| true -> begin
(fail "apply_lemma: not a lemma")
end
| uu____1172 -> begin
(

let uu____1173 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____1173) with
| (bs, comp) -> begin
(

let uu____1188 = (FStar_List.fold_left (fun uu____1205 uu____1206 -> (match (((uu____1205), (uu____1206))) with
| ((uvs, guard1, subst1), (b, aq)) -> begin
(

let b_t = (FStar_Syntax_Subst.subst subst1 b.FStar_Syntax_Syntax.sort)
in (

let uu____1255 = (FStar_TypeChecker_Util.new_implicit_var "apply_lemma" goal.goal_ty.FStar_Syntax_Syntax.pos goal.context b_t)
in (match (uu____1255) with
| (u, uu____1270, g_u) -> begin
(

let uu____1278 = (FStar_TypeChecker_Rel.conj_guard guard1 g_u)
in (((((u), (aq)))::uvs), (uu____1278), ((FStar_Syntax_Syntax.NT (((b), (u))))::subst1)))
end)))
end)) (([]), (guard), ([])) bs)
in (match (uu____1188) with
| (uvs, implicits, subst1) -> begin
(

let uvs1 = (FStar_List.rev uvs)
in (

let comp1 = (FStar_Syntax_Subst.subst_comp subst1 comp)
in (

let uu____1310 = (

let c = (FStar_Syntax_Util.comp_to_comp_typ comp1)
in (match (c.FStar_Syntax_Syntax.effect_args) with
| (pre)::(post)::uu____1326 -> begin
(((Prims.fst pre)), ((Prims.fst post)))
end
| uu____1356 -> begin
(failwith "Impossible: not a lemma")
end))
in (match (uu____1310) with
| (pre, post) -> begin
(

let uu____1379 = (FStar_TypeChecker_Rel.try_teq false goal.context post goal.goal_ty)
in (match (uu____1379) with
| None -> begin
(fail "apply_lemma: does not unify with goal")
end
| Some (g) -> begin
(

let g1 = (

let uu____1384 = (FStar_TypeChecker_Rel.solve_deferred_constraints goal.context g)
in (FStar_All.pipe_right uu____1384 FStar_TypeChecker_Rel.resolve_implicits))
in (

let solution = ((FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1) None goal.context.FStar_TypeChecker_Env.range)
in (

let implicits1 = (FStar_All.pipe_right implicits.FStar_TypeChecker_Env.implicits (FStar_List.filter (fun uu____1420 -> (match (uu____1420) with
| (uu____1427, uu____1428, uu____1429, tm2, uu____1431, uu____1432) -> begin
(

let uu____1433 = (FStar_Syntax_Util.head_and_args tm2)
in (match (uu____1433) with
| (hd1, uu____1444) -> begin
(

let uu____1459 = (

let uu____1460 = (FStar_Syntax_Subst.compress hd1)
in uu____1460.FStar_Syntax_Syntax.n)
in (match (uu____1459) with
| FStar_Syntax_Syntax.Tm_uvar (uu____1463) -> begin
true
end
| uu____1472 -> begin
false
end))
end))
end))))
in ((solve goal solution);
(

let sub_goals = (

let uu____1476 = (FStar_All.pipe_right implicits1 (FStar_List.map (fun uu____1492 -> (match (uu____1492) with
| (_msg, _env, _uvar, term, typ, uu____1504) -> begin
{context = goal.context; witness = Some (term); goal_ty = typ}
end))))
in ((

let uu___100_1505 = goal
in {context = uu___100_1505.context; witness = None; goal_ty = pre}))::uu____1476)
in (

let uu____1506 = (add_implicits g1.FStar_TypeChecker_Env.implicits)
in (bind uu____1506 (fun uu____1508 -> (bind dismiss (fun uu____1509 -> (add_goals sub_goals)))))));
))))
end))
end))))
end))
end))
end))
end))
end)
with
| uu____1512 -> begin
(fail "apply_lemma: ill-typed term")
end)))


let exact : FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun tm -> (with_cur_goal "exact" (fun goal -> try
(match (()) with
| () -> begin
(

let uu____1522 = (goal.context.FStar_TypeChecker_Env.type_of goal.context tm)
in (match (uu____1522) with
| (uu____1527, t, guard) -> begin
(

let uu____1530 = (FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty)
in (match (uu____1530) with
| true -> begin
((solve goal tm);
(replace_cur (

let uu___103_1533 = goal
in {context = uu___103_1533.context; witness = None; goal_ty = FStar_Syntax_Util.t_true}));
)
end
| uu____1534 -> begin
(

let msg = (

let uu____1536 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____1537 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1538 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (FStar_Util.format3 "%s : %s does not exactly solve the goal %s" uu____1536 uu____1537 uu____1538))))
in (fail msg))
end))
end))
end)
with
| e -> begin
(

let uu____1542 = (

let uu____1543 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.format1 "Term is not typeable: %s" uu____1543))
in (fail uu____1542))
end)))


let rewrite : FStar_Syntax_Syntax.binder  ->  Prims.unit tac = (fun h -> (with_cur_goal "rewrite" (fun goal -> (

let uu____1550 = (

let uu____1552 = (

let uu____1553 = (FStar_TypeChecker_Env.lookup_bv goal.context (Prims.fst h))
in (FStar_All.pipe_left Prims.fst uu____1553))
in (FStar_Syntax_Util.destruct_typ_as_formula uu____1552))
in (match (uu____1550) with
| Some (FStar_Syntax_Util.BaseConn (l, (uu____1560)::((x, uu____1562))::((e, uu____1564))::[])) when (FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid) -> begin
(

let uu____1598 = (

let uu____1599 = (FStar_Syntax_Subst.compress x)
in uu____1599.FStar_Syntax_Syntax.n)
in (match (uu____1598) with
| FStar_Syntax_Syntax.Tm_name (x1) -> begin
(

let goal1 = (

let uu___104_1605 = goal
in (

let uu____1606 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x1), (e))))::[]) goal.goal_ty)
in {context = uu___104_1605.context; witness = uu___104_1605.witness; goal_ty = uu____1606}))
in (replace_cur goal1))
end
| uu____1609 -> begin
(fail "Not an equality hypothesis with a variable on the LHS")
end))
end
| uu____1610 -> begin
(fail "Not an equality hypothesis")
end)))))


let clear : Prims.unit tac = (with_cur_goal "clear" (fun goal -> (

let uu____1614 = (FStar_TypeChecker_Env.pop_bv goal.context)
in (match (uu____1614) with
| None -> begin
(fail "Cannot clear; empty context")
end
| Some (x, env') -> begin
(

let fns = (FStar_Syntax_Free.names goal.goal_ty)
in (

let uu____1627 = (FStar_Util.set_mem x fns)
in (match (uu____1627) with
| true -> begin
(fail "Cannot clear; variable appears in goal")
end
| uu____1629 -> begin
(

let new_goal = (

let uu___105_1631 = goal
in {context = env'; witness = uu___105_1631.witness; goal_ty = uu___105_1631.goal_ty})
in (bind dismiss (fun uu____1632 -> (add_goals ((new_goal)::[])))))
end)))
end))))


let clear_hd : name  ->  Prims.unit tac = (fun x -> (with_cur_goal "clear_hd" (fun goal -> (

let uu____1639 = (FStar_TypeChecker_Env.pop_bv goal.context)
in (match (uu____1639) with
| None -> begin
(fail "Cannot clear_hd; empty context")
end
| Some (y, env') -> begin
(match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(fail "Cannot clear_hd; head variable mismatch")
end
| uu____1651 -> begin
clear
end)
end)))))


let revert : Prims.unit tac = (with_cur_goal "revert" (fun goal -> (

let uu____1654 = (FStar_TypeChecker_Env.pop_bv goal.context)
in (match (uu____1654) with
| None -> begin
(fail "Cannot revert; empty context")
end
| Some (x, env') -> begin
(

let fvs = (FStar_Syntax_Free.names goal.goal_ty)
in (

let new_goal = (

let uu____1668 = (FStar_Util.set_mem x fvs)
in (match (uu____1668) with
| true -> begin
(

let uu___106_1669 = goal
in (

let uu____1670 = (

let uu____1671 = (FStar_TypeChecker_TcTerm.universe_of env' x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Util.mk_forall uu____1671 x goal.goal_ty))
in {context = env'; witness = uu___106_1669.witness; goal_ty = uu____1670}))
end
| uu____1672 -> begin
(

let uu___107_1673 = goal
in (

let uu____1674 = (FStar_Syntax_Util.mk_imp x.FStar_Syntax_Syntax.sort goal.goal_ty)
in {context = env'; witness = uu___107_1673.witness; goal_ty = uu____1674}))
end))
in (bind dismiss (fun uu____1675 -> (add_goals ((new_goal)::[]))))))
end))))


let revert_hd : name  ->  Prims.unit tac = (fun x -> (with_cur_goal "revert_hd" (fun goal -> (

let uu____1682 = (FStar_TypeChecker_Env.pop_bv goal.context)
in (match (uu____1682) with
| None -> begin
(fail "Cannot revert_hd; empty context")
end
| Some (y, env') -> begin
(match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(

let uu____1694 = (

let uu____1695 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____1696 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Cannot revert_hd %s; head variable mismatch ... egot %s" uu____1695 uu____1696)))
in (fail uu____1694))
end
| uu____1697 -> begin
revert
end)
end)))))


let rec revert_all_hd : name Prims.list  ->  Prims.unit tac = (fun xs -> (match (xs) with
| [] -> begin
(ret ())
end
| (x)::xs1 -> begin
(

let uu____1709 = (revert_all_hd xs1)
in (bind uu____1709 (fun uu____1711 -> (revert_hd x))))
end))


let is_name : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun x -> (

let uu____1715 = (

let uu____1716 = (FStar_Syntax_Subst.compress x)
in uu____1716.FStar_Syntax_Syntax.n)
in (match (uu____1715) with
| FStar_Syntax_Syntax.Tm_name (uu____1719) -> begin
true
end
| uu____1720 -> begin
false
end)))


let as_name : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let uu____1724 = (

let uu____1725 = (FStar_Syntax_Subst.compress x)
in uu____1725.FStar_Syntax_Syntax.n)
in (match (uu____1724) with
| FStar_Syntax_Syntax.Tm_name (x1) -> begin
x1
end
| uu____1729 -> begin
(failwith "Not a name")
end)))


let destruct_equality_imp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.option = (fun t -> (

let uu____1741 = (FStar_Syntax_Util.destruct_typ_as_formula t)
in (match (uu____1741) with
| Some (FStar_Syntax_Util.BaseConn (l, ((lhs, uu____1753))::((rhs, uu____1755))::[])) when (FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid) -> begin
(

let uu____1781 = (FStar_Syntax_Util.destruct_typ_as_formula lhs)
in (match (uu____1781) with
| (Some (FStar_Syntax_Util.BaseConn (eq1, (_)::((x, _))::((e, _))::[]))) | (Some (FStar_Syntax_Util.BaseConn (eq1, ((x, _))::((e, _))::[]))) when ((FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) && (is_name x)) -> begin
(

let uu____1853 = (

let uu____1861 = (as_name x)
in ((uu____1861), (e), (rhs)))
in Some (uu____1853))
end
| uu____1873 -> begin
None
end))
end
| uu____1882 -> begin
None
end)))


let at_most_one = (fun t -> (bind t (fun a -> (bind get (fun p -> (match (p.goals) with
| ([]) | ((_)::[]) -> begin
(ret a)
end
| uu____1905 -> begin
(fail "expected at most one goal remaining")
end))))))


let goal_to_string : goal  ->  Prims.string = (fun g1 -> (

let g1_binders = (

let uu____1911 = (FStar_TypeChecker_Env.all_binders g1.context)
in (FStar_All.pipe_right uu____1911 (FStar_Syntax_Print.binders_to_string ", ")))
in (

let uu____1912 = (FStar_Syntax_Print.term_to_string g1.goal_ty)
in (FStar_Util.format2 "%s |- %s" g1_binders uu____1912))))


let merge_sub_goals : Prims.unit tac = (

let uu____1914 = (bind get (fun p -> (match (p.goals) with
| (g1)::(g2)::rest -> begin
(

let uu____1922 = (((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) && (FStar_Option.isNone g1.witness)) && (FStar_Option.isNone g2.witness))
in (match (uu____1922) with
| true -> begin
(

let uu____1924 = (

let uu___108_1925 = p
in (

let uu____1926 = (

let uu____1928 = (conj_goals g1 g2)
in (uu____1928)::rest)
in {main_context = uu___108_1925.main_context; main_goal = uu___108_1925.main_goal; all_implicits = uu___108_1925.all_implicits; goals = uu____1926; smt_goals = uu___108_1925.smt_goals; transaction = uu___108_1925.transaction}))
in (set uu____1924))
end
| uu____1929 -> begin
(

let g1_binders = (

let uu____1931 = (FStar_TypeChecker_Env.all_binders g1.context)
in (FStar_All.pipe_right uu____1931 (FStar_Syntax_Print.binders_to_string ", ")))
in (

let g2_binders = (

let uu____1933 = (FStar_TypeChecker_Env.all_binders g2.context)
in (FStar_All.pipe_right uu____1933 (FStar_Syntax_Print.binders_to_string ", ")))
in (

let uu____1934 = (

let uu____1935 = (goal_to_string g1)
in (

let uu____1936 = (goal_to_string g2)
in (

let uu____1937 = (

let uu____1938 = (FStar_TypeChecker_Env.eq_gamma g1.context g2.context)
in (FStar_All.pipe_right uu____1938 FStar_Util.string_of_bool))
in (FStar_Util.format3 "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n" uu____1935 uu____1936 uu____1937))))
in (fail uu____1934))))
end))
end
| uu____1939 -> begin
(

let goals = (

let uu____1942 = (FStar_All.pipe_right p.goals (FStar_List.map (fun x -> (FStar_Syntax_Print.term_to_string x.goal_ty))))
in (FStar_All.pipe_right uu____1942 (FStar_String.concat "\n\t")))
in (

let uu____1948 = (FStar_Util.format1 "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s" goals)
in (fail uu____1948)))
end)))
in (name_tac "merge_sub_goals" uu____1914))


let rec visit : Prims.unit tac  ->  Prims.unit tac = (fun callback -> (

let uu____1956 = (

let uu____1958 = (with_cur_goal "visit_strengthen_else" (fun goal -> (

let uu____1961 = (FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty)
in (match (uu____1961) with
| None -> begin
(

let uu____1964 = (

let uu____1965 = (FStar_Syntax_Subst.compress goal.goal_ty)
in uu____1965.FStar_Syntax_Syntax.n)
in (match (uu____1964) with
| FStar_Syntax_Syntax.Tm_meta (uu____1969) -> begin
(

let uu____1974 = (visit callback)
in (map_meta uu____1974))
end
| uu____1976 -> begin
smt
end))
end
| Some (FStar_Syntax_Util.QEx (uu____1977)) -> begin
(ret ())
end
| Some (FStar_Syntax_Util.QAll (xs, uu____1982, uu____1983)) -> begin
(bind intros (fun binders -> (

let uu____1985 = (visit callback)
in (

let uu____1987 = (

let uu____1989 = (

let uu____1991 = (FStar_List.map Prims.fst binders)
in (revert_all_hd uu____1991))
in (bind uu____1989 (fun uu____1995 -> (with_cur_goal "inner" (fun goal1 -> (ret ()))))))
in (seq uu____1985 uu____1987)))))
end
| Some (FStar_Syntax_Util.BaseConn (l, uu____1998)) when (FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid) -> begin
(

let uu____1999 = (

let uu____2001 = (visit callback)
in (seq split uu____2001))
in (bind uu____1999 (fun uu____2003 -> merge_sub_goals)))
end
| Some (FStar_Syntax_Util.BaseConn (l, uu____2005)) when (FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid) -> begin
(bind imp_intro (fun h -> (

let uu____2007 = (visit callback)
in (seq uu____2007 revert))))
end
| Some (FStar_Syntax_Util.BaseConn (l, uu____2010)) -> begin
(or_else trivial smt)
end))))
in (or_else callback uu____1958))
in (focus_cur_goal "visit_strengthen" uu____1956)))


let proofstate_of_goal_ty : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  proofstate = (fun env g -> (

let g1 = (

let uu____2018 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env g)
in {context = env; witness = None; goal_ty = uu____2018})
in (

let uu____2019 = (FStar_Unionfind.new_transaction ())
in {main_context = env; main_goal = g1; all_implicits = []; goals = (g1)::[]; smt_goals = []; transaction = uu____2019})))




