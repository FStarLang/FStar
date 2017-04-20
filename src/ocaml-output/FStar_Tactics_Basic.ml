
open Prims

type name =
FStar_Syntax_Syntax.bv

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


let as_tac = (fun name b f -> {tac_f = f; tac_name = name; kernel = b})


let kernel_tac = (fun n1 t -> {tac_f = t; tac_name = n1; kernel = true})


let user_tac = (fun n1 t -> {tac_f = t; tac_name = n1; kernel = false})


let name_tac = (fun n1 t -> (

let uu___73_300 = t
in {tac_f = uu___73_300.tac_f; tac_name = n1; kernel = false}))


let run = (fun t p -> (t.tac_f p))


let debug : proofstate  ->  Prims.string  ->  Prims.unit = (fun p msg -> (

let uu____323 = (FStar_Util.string_of_int (FStar_List.length p.goals))
in (

let uu____327 = (match (p.goals) with
| [] -> begin
"[]"
end
| uu____328 -> begin
(

let uu____330 = (

let uu____331 = (FStar_List.hd p.goals)
in uu____331.goal_ty)
in (FStar_Syntax_Print.term_to_string uu____330))
end)
in (

let uu____332 = (match (p.goals) with
| [] -> begin
""
end
| uu____333 -> begin
(

let uu____335 = (

let uu____337 = (FStar_List.tl p.goals)
in (FStar_All.pipe_right uu____337 (FStar_List.map (fun x -> (FStar_Syntax_Print.term_to_string x.goal_ty)))))
in (FStar_All.pipe_right uu____335 (FStar_String.concat ";;")))
end)
in (FStar_Util.print4 "TAC (ngoals=%s, maingoal=%s, rest=%s):\n\tTAC>> %s\n" uu____323 uu____327 uu____332 msg)))))


let ret = (fun a -> (kernel_tac "return" (fun p -> Success (((a), (p))))))


let bind = (fun t1 t2 -> (kernel_tac "bind" (fun p -> ((match ((not (t1.kernel))) with
| true -> begin
(debug p t1.tac_name)
end
| uu____378 -> begin
()
end);
(

let uu____379 = (t1.tac_f p)
in (match (uu____379) with
| Success (a, q) -> begin
(

let t21 = (t2 a)
in ((match ((not (t21.kernel))) with
| true -> begin
(debug q t21.tac_name)
end
| uu____387 -> begin
()
end);
(t21.tac_f q);
))
end
| Failed (msg, q) -> begin
((match ((not (t1.kernel))) with
| true -> begin
(

let uu____391 = (FStar_Util.format1 "%s failed!" t1.tac_name)
in (debug p uu____391))
end
| uu____392 -> begin
()
end);
Failed (((msg), (q)));
)
end));
))))


let get : proofstate tac = (kernel_tac "get" (fun p -> Success (((p), (p)))))


let fail = (fun msg -> (kernel_tac "fail" (fun p -> ((FStar_Util.print1 ">>>>>%s\n" msg);
Failed (((msg), (p)));
))))


let show : Prims.unit tac = (kernel_tac "show" (fun p -> ((debug p "debug");
Success (((()), (p)));
)))


let set : proofstate  ->  Prims.unit tac = (fun p -> (kernel_tac "set" (fun uu____413 -> Success (((()), (p))))))


let solve : goal  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun goal solution -> (match (goal.witness) with
| None -> begin
()
end
| Some (w) -> begin
(

let uu____421 = (FStar_TypeChecker_Rel.teq_nosmt goal.context w solution)
in (match (uu____421) with
| true -> begin
()
end
| uu____422 -> begin
(

let uu____423 = (

let uu____424 = (

let uu____425 = (FStar_Syntax_Print.term_to_string solution)
in (

let uu____426 = (FStar_Syntax_Print.term_to_string w)
in (

let uu____427 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (FStar_Util.format3 "%s does not solve %s : %s" uu____425 uu____426 uu____427))))
in Failure (uu____424))
in (Prims.raise uu____423))
end))
end))


let dismiss : Prims.unit tac = (bind get (fun p -> (

let uu____430 = (

let uu___74_431 = p
in (

let uu____432 = (FStar_List.tl p.goals)
in {main_context = uu___74_431.main_context; main_goal = uu___74_431.main_goal; all_implicits = uu___74_431.all_implicits; goals = uu____432; smt_goals = uu___74_431.smt_goals; transaction = uu___74_431.transaction}))
in (set uu____430))))


let dismiss_all : Prims.unit tac = (bind get (fun p -> (set (

let uu___75_436 = p
in {main_context = uu___75_436.main_context; main_goal = uu___75_436.main_goal; all_implicits = uu___75_436.all_implicits; goals = []; smt_goals = uu___75_436.smt_goals; transaction = uu___75_436.transaction}))))


let add_goals : goal Prims.list  ->  Prims.unit tac = (fun gs -> (bind get (fun p -> (set (

let uu___76_445 = p
in {main_context = uu___76_445.main_context; main_goal = uu___76_445.main_goal; all_implicits = uu___76_445.all_implicits; goals = (FStar_List.append gs p.goals); smt_goals = uu___76_445.smt_goals; transaction = uu___76_445.transaction})))))


let add_smt_goals : goal Prims.list  ->  Prims.unit tac = (fun gs -> (bind get (fun p -> (set (

let uu___77_454 = p
in {main_context = uu___77_454.main_context; main_goal = uu___77_454.main_goal; all_implicits = uu___77_454.all_implicits; goals = uu___77_454.goals; smt_goals = (FStar_List.append gs p.smt_goals); transaction = uu___77_454.transaction})))))


let replace : goal  ->  Prims.unit tac = (fun g -> (bind dismiss (fun uu____460 -> (add_goals ((g)::[])))))


let add_implicits : FStar_TypeChecker_Env.implicits  ->  Prims.unit tac = (fun i -> (bind get (fun p -> (set (

let uu___78_467 = p
in {main_context = uu___78_467.main_context; main_goal = uu___78_467.main_goal; all_implicits = (FStar_List.append i p.all_implicits); goals = uu___78_467.goals; smt_goals = uu___78_467.smt_goals; transaction = uu___78_467.transaction})))))


let is_true : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____477 = (FStar_Syntax_Util.destruct_typ_as_formula t)
in (match (uu____477) with
| Some (FStar_Syntax_Util.BaseConn (l, [])) -> begin
(FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid)
end
| uu____489 -> begin
false
end)))


let is_false : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____494 = (FStar_Syntax_Util.destruct_typ_as_formula t)
in (match (uu____494) with
| Some (FStar_Syntax_Util.BaseConn (l, [])) -> begin
(FStar_Ident.lid_equals l FStar_Syntax_Const.false_lid)
end
| uu____506 -> begin
false
end)))


let conj_goals : goal  ->  goal  ->  goal = (fun g1 g2 -> (

let t1 = g1.goal_ty
in (

let t2 = g2.goal_ty
in (

let uu____516 = ((is_true t1) || (is_false t2))
in (match (uu____516) with
| true -> begin
g2
end
| uu____517 -> begin
(

let uu____518 = ((is_true t2) || (is_false t1))
in (match (uu____518) with
| true -> begin
g1
end
| uu____519 -> begin
(

let uu___79_520 = g1
in (

let uu____521 = (FStar_Syntax_Util.mk_conj t1 t2)
in {context = uu___79_520.context; witness = uu___79_520.witness; goal_ty = uu____521}))
end))
end)))))


let with_cur_goal = (fun nm f -> (

let uu____542 = (bind get (fun p -> (match (p.goals) with
| [] -> begin
(fail "No more goals")
end
| (hd1)::tl1 -> begin
(f hd1)
end)))
in (name_tac nm uu____542)))


let smt : Prims.unit tac = (with_cur_goal "smt" (fun g -> (bind dismiss (fun uu____551 -> (

let uu____552 = (add_goals (((

let uu___80_554 = g
in {context = uu___80_554.context; witness = uu___80_554.witness; goal_ty = FStar_Syntax_Util.t_true}))::[]))
in (bind uu____552 (fun uu____555 -> (add_smt_goals ((g)::[])))))))))


let focus_cur_goal = (fun nm f -> (bind get (fun p -> (match (p.goals) with
| [] -> begin
(fail "No more goals")
end
| (hd1)::tl1 -> begin
(

let q = (

let uu___81_577 = p
in {main_context = uu___81_577.main_context; main_goal = uu___81_577.main_goal; all_implicits = uu___81_577.all_implicits; goals = (hd1)::[]; smt_goals = uu___81_577.smt_goals; transaction = uu___81_577.transaction})
in (

let uu____578 = (set q)
in (bind uu____578 (fun uu____580 -> (bind f (fun a -> (bind get (fun q' -> (

let q2 = (

let uu___82_584 = q'
in {main_context = uu___82_584.main_context; main_goal = uu___82_584.main_goal; all_implicits = uu___82_584.all_implicits; goals = (FStar_List.append q'.goals tl1); smt_goals = uu___82_584.smt_goals; transaction = uu___82_584.transaction})
in (

let uu____585 = (set q2)
in (bind uu____585 (fun uu____587 -> (ret a)))))))))))))
end))))


let cur_goal_and_rest = (fun f g -> (bind get (fun p -> (match (p.goals) with
| [] -> begin
(fail "No more goals")
end
| (uu____621)::[] -> begin
(bind f (fun a -> (ret ((a), (None)))))
end
| (hd1)::tl1 -> begin
(bind dismiss_all (fun uu____636 -> (

let uu____637 = (add_goals ((hd1)::[]))
in (bind uu____637 (fun uu____642 -> (bind f (fun a -> (bind get (fun uu____650 -> (match (uu____650) with
| {main_context = uu____655; main_goal = uu____656; all_implicits = uu____657; goals = sub_goals_f; smt_goals = uu____659; transaction = uu____660} -> begin
(bind dismiss_all (fun uu____666 -> (

let uu____667 = (add_goals tl1)
in (bind uu____667 (fun uu____672 -> (bind g (fun b -> (

let uu____677 = (add_goals sub_goals_f)
in (bind uu____677 (fun uu____682 -> (ret ((a), (Some (b))))))))))))))
end))))))))))
end))))


let or_else = (fun t1 t2 -> (kernel_tac "or_else" (fun p -> ((

let uu____706 = (FStar_Util.format1 "or_else: trying %s" t1.tac_name)
in (debug p uu____706));
(

let uu____707 = (t1.tac_f p)
in (match (uu____707) with
| Failed (uu____710) -> begin
((

let uu____714 = (FStar_Util.format2 "or_else: %s failed; trying %s" t1.tac_name t2.tac_name)
in (debug p uu____714));
(t2.tac_f p);
)
end
| q -> begin
q
end));
))))


let rec map = (fun t -> (user_tac "map" (fun p -> (

let uu____730 = (

let uu____733 = (

let uu____739 = (map t)
in (cur_goal_and_rest t uu____739))
in (bind uu____733 (fun uu___72_748 -> (match (uu___72_748) with
| (hd1, None) -> begin
(ret ((hd1)::[]))
end
| (hd1, Some (tl1)) -> begin
(ret ((hd1)::tl1))
end))))
in (run uu____730 p)))))


let map_goal_term : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  Prims.unit tac = (fun f -> (

let aux = (with_cur_goal "map_goal" (fun g -> (

let uu____781 = (

let uu___83_782 = g
in (

let uu____783 = (f g.goal_ty)
in {context = uu___83_782.context; witness = uu___83_782.witness; goal_ty = uu____783}))
in (replace uu____781))))
in (

let uu____784 = (map aux)
in (bind uu____784 (fun uu____788 -> (ret ()))))))


let map_meta = (fun t -> (with_cur_goal "map_meta" (fun g -> (

let uu____801 = (

let uu____802 = (FStar_Syntax_Subst.compress g.goal_ty)
in uu____802.FStar_Syntax_Syntax.n)
in (match (uu____801) with
| FStar_Syntax_Syntax.Tm_meta (f, annot) -> begin
(

let uu____812 = (replace (

let uu___84_814 = g
in {context = uu___84_814.context; witness = uu___84_814.witness; goal_ty = f}))
in (bind uu____812 (fun uu____815 -> (bind t (fun a -> (

let uu____817 = (map_goal_term (fun tm -> (

let uu____820 = (is_true tm)
in (match (uu____820) with
| true -> begin
tm
end
| uu____821 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((tm), (annot)))) None tm.FStar_Syntax_Syntax.pos)
end))))
in (bind uu____817 (fun uu____826 -> (ret a)))))))))
end
| uu____827 -> begin
(fail "Not a meta")
end)))))


let seq : Prims.unit tac  ->  Prims.unit tac  ->  Prims.unit tac = (fun t1 t2 -> (

let uu____840 = (bind t1 (fun uu____842 -> (

let uu____843 = (map t2)
in (bind uu____843 (fun uu____847 -> (ret ()))))))
in (focus_cur_goal "seq" uu____840)))


let intros : FStar_Syntax_Syntax.binders tac = (with_cur_goal "intros" (fun goal -> (

let uu____851 = (FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty)
in (match (uu____851) with
| Some (FStar_Syntax_Util.QAll (bs, pats, body)) -> begin
(

let new_context = (FStar_TypeChecker_Env.push_binders goal.context bs)
in (

let new_goal = {context = new_context; witness = None; goal_ty = body}
in (bind dismiss (fun uu____859 -> (

let uu____860 = (add_goals ((new_goal)::[]))
in (bind uu____860 (fun uu____862 -> ((

let uu____864 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "intros: %s\n" uu____864));
(ret bs);
))))))))
end
| uu____865 -> begin
(fail "Cannot intro this goal, expected a forall")
end))))


let intros_no_names : Prims.unit tac = (bind intros (fun uu____868 -> (ret ())))


let mk_squash = (fun p -> (

let sq = (FStar_Syntax_Util.fvar_const FStar_Syntax_Const.squash_lid)
in (

let uu____879 = (

let uu____885 = (FStar_Syntax_Syntax.as_arg p)
in (uu____885)::[])
in (FStar_Syntax_Util.mk_app sq uu____879))))


let un_squash : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option = (fun t -> (

let uu____892 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____892) with
| (head1, args) -> begin
(

let uu____921 = (

let uu____929 = (

let uu____930 = (FStar_Syntax_Util.un_uinst head1)
in uu____930.FStar_Syntax_Syntax.n)
in ((uu____929), (args)))
in (match (uu____921) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____943))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid) -> begin
Some (p)
end
| (FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____963; FStar_Syntax_Syntax.index = uu____964; FStar_Syntax_Syntax.sort = {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____966; FStar_Syntax_Syntax.pos = uu____967; FStar_Syntax_Syntax.vars = uu____968}}, p), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) -> begin
Some (p)
end
| uu____987 -> begin
None
end))
end)))


let imp_intro : FStar_Syntax_Syntax.binder tac = (with_cur_goal "imp_intro" (fun goal -> (

let uu____999 = (FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty)
in (match (uu____999) with
| Some (FStar_Syntax_Util.BaseConn (l, ((lhs, uu____1004))::((rhs, uu____1006))::[])) when (FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid) -> begin
(

let name = (FStar_Syntax_Syntax.new_bv None lhs)
in (

let new_goal = (

let uu____1034 = (FStar_TypeChecker_Env.push_bv goal.context name)
in {context = uu____1034; witness = None; goal_ty = rhs})
in (bind dismiss (fun uu____1035 -> (

let uu____1036 = (add_goals ((new_goal)::[]))
in (bind uu____1036 (fun uu____1038 -> ((

let uu____1040 = (FStar_Syntax_Print.bv_to_string name)
in (FStar_Util.print1 "imp_intro: %s\n" uu____1040));
(

let uu____1041 = (FStar_Syntax_Syntax.mk_binder name)
in (ret uu____1041));
))))))))
end
| uu____1042 -> begin
(fail "Cannot intro this goal, expected an \'==>\'")
end))))


let split : Prims.unit tac = (with_cur_goal "split" (fun goal -> (

let uu____1046 = (FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty)
in (match (uu____1046) with
| Some (FStar_Syntax_Util.BaseConn (l, args)) when (FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid) -> begin
(

let new_goals = (FStar_All.pipe_right args (FStar_List.map (fun uu____1056 -> (match (uu____1056) with
| (a, uu____1060) -> begin
(

let uu___85_1061 = goal
in {context = uu___85_1061.context; witness = None; goal_ty = a})
end))))
in (bind dismiss (fun uu____1062 -> (

let uu____1063 = (add_goals new_goals)
in (bind uu____1063 (fun uu____1065 -> show))))))
end
| uu____1066 -> begin
(fail "Cannot split this goal; expected a conjunction")
end))))


let trivial : Prims.unit tac = (with_cur_goal "trivial" (fun goal -> (

let steps = (FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Primops)::[]
in (

let t = (FStar_TypeChecker_Normalize.normalize steps goal.context goal.goal_ty)
in (

let uu____1073 = (FStar_Syntax_Util.destruct_typ_as_formula t)
in (match (uu____1073) with
| Some (FStar_Syntax_Util.BaseConn (l, [])) when (FStar_Ident.lid_equals l FStar_Syntax_Const.true_lid) -> begin
(bind dismiss (fun uu____1086 -> (add_goals (((

let uu___86_1087 = goal
in {context = uu___86_1087.context; witness = uu___86_1087.witness; goal_ty = t}))::[]))))
end
| uu____1088 -> begin
(fail "Not a trivial goal")
end))))))


let apply_lemma : FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun tm -> (with_cur_goal "apply_lemma" (fun goal -> try
(match (()) with
| () -> begin
(

let uu____1099 = (goal.context.FStar_TypeChecker_Env.type_of goal.context tm)
in (match (uu____1099) with
| (tm1, t, guard) -> begin
(

let uu____1107 = (

let uu____1108 = (FStar_Syntax_Util.is_lemma t)
in (not (uu____1108)))
in (match (uu____1107) with
| true -> begin
(fail "apply_lemma: not a lemma")
end
| uu____1110 -> begin
(

let uu____1111 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____1111) with
| (bs, comp) -> begin
(

let uu____1126 = (FStar_List.fold_left (fun uu____1143 uu____1144 -> (match (((uu____1143), (uu____1144))) with
| ((uvs, guard1, subst1), (b, aq)) -> begin
(

let b_t = (FStar_Syntax_Subst.subst subst1 b.FStar_Syntax_Syntax.sort)
in (

let uu____1193 = (FStar_TypeChecker_Util.new_implicit_var "apply_lemma" goal.goal_ty.FStar_Syntax_Syntax.pos goal.context b_t)
in (match (uu____1193) with
| (u, uu____1208, g_u) -> begin
(

let uu____1216 = (FStar_TypeChecker_Rel.conj_guard guard1 g_u)
in (((((u), (aq)))::uvs), (uu____1216), ((FStar_Syntax_Syntax.NT (((b), (u))))::subst1)))
end)))
end)) (([]), (guard), ([])) bs)
in (match (uu____1126) with
| (uvs, implicits, subst1) -> begin
(

let uvs1 = (FStar_List.rev uvs)
in (

let comp1 = (FStar_Syntax_Subst.subst_comp subst1 comp)
in (

let uu____1248 = (

let c = (FStar_Syntax_Util.comp_to_comp_typ comp1)
in (match (c.FStar_Syntax_Syntax.effect_args) with
| (pre)::(post)::uu____1264 -> begin
(((Prims.fst pre)), ((Prims.fst post)))
end
| uu____1294 -> begin
(failwith "Impossible: not a lemma")
end))
in (match (uu____1248) with
| (pre, post) -> begin
(

let uu____1317 = (FStar_TypeChecker_Rel.try_teq false goal.context post goal.goal_ty)
in (match (uu____1317) with
| None -> begin
(fail "apply_lemma: does not unify with goal")
end
| Some (g) -> begin
(

let g1 = (

let uu____1322 = (FStar_TypeChecker_Rel.solve_deferred_constraints goal.context g)
in (FStar_All.pipe_right uu____1322 FStar_TypeChecker_Rel.resolve_implicits))
in (

let solution = ((FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1) None goal.context.FStar_TypeChecker_Env.range)
in (

let implicits1 = (FStar_All.pipe_right implicits.FStar_TypeChecker_Env.implicits (FStar_List.filter (fun uu____1358 -> (match (uu____1358) with
| (uu____1365, uu____1366, uu____1367, tm2, uu____1369, uu____1370) -> begin
(

let uu____1371 = (FStar_Syntax_Util.head_and_args tm2)
in (match (uu____1371) with
| (hd1, uu____1382) -> begin
(

let uu____1397 = (

let uu____1398 = (FStar_Syntax_Subst.compress hd1)
in uu____1398.FStar_Syntax_Syntax.n)
in (match (uu____1397) with
| FStar_Syntax_Syntax.Tm_uvar (uu____1401) -> begin
true
end
| uu____1410 -> begin
false
end))
end))
end))))
in ((solve goal solution);
(

let sub_goals = (

let uu____1414 = (FStar_All.pipe_right implicits1 (FStar_List.map (fun uu____1430 -> (match (uu____1430) with
| (_msg, _env, _uvar, term, typ, uu____1442) -> begin
{context = goal.context; witness = Some (term); goal_ty = typ}
end))))
in ((

let uu___89_1443 = goal
in {context = uu___89_1443.context; witness = None; goal_ty = pre}))::uu____1414)
in (

let uu____1444 = (add_implicits g1.FStar_TypeChecker_Env.implicits)
in (bind uu____1444 (fun uu____1446 -> (bind dismiss (fun uu____1447 -> (add_goals sub_goals)))))));
))))
end))
end))))
end))
end))
end))
end))
end)
with
| uu____1450 -> begin
(fail "apply_lemma: ill-typed term")
end)))


let exact : FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun tm -> (with_cur_goal "exact" (fun goal -> try
(match (()) with
| () -> begin
(

let uu____1460 = (goal.context.FStar_TypeChecker_Env.type_of goal.context tm)
in (match (uu____1460) with
| (uu____1465, t, guard) -> begin
(

let uu____1468 = (FStar_TypeChecker_Rel.teq_nosmt goal.context t goal.goal_ty)
in (match (uu____1468) with
| true -> begin
((solve goal tm);
(replace (

let uu___92_1471 = goal
in {context = uu___92_1471.context; witness = None; goal_ty = FStar_Syntax_Util.t_true}));
)
end
| uu____1472 -> begin
(

let msg = (

let uu____1474 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____1475 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1476 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (FStar_Util.format3 "%s : %s does not exactly solve the goal %s" uu____1474 uu____1475 uu____1476))))
in (fail msg))
end))
end))
end)
with
| e -> begin
(

let uu____1480 = (

let uu____1481 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.format1 "Term is not typeable: %s" uu____1481))
in (fail uu____1480))
end)))


let rewrite : FStar_Syntax_Syntax.binder  ->  Prims.unit tac = (fun h -> (with_cur_goal "rewrite" (fun goal -> ((

let uu____1489 = (FStar_Syntax_Print.bv_to_string (Prims.fst h))
in (

let uu____1490 = (FStar_Syntax_Print.term_to_string (Prims.fst h).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "+++Rewrite %s : %s\n" uu____1489 uu____1490)));
(

let uu____1491 = (

let uu____1493 = (

let uu____1494 = (FStar_TypeChecker_Env.lookup_bv goal.context (Prims.fst h))
in (FStar_All.pipe_left Prims.fst uu____1494))
in (FStar_Syntax_Util.destruct_typ_as_formula uu____1493))
in (match (uu____1491) with
| Some (FStar_Syntax_Util.BaseConn (l, (uu____1501)::((x, uu____1503))::((e, uu____1505))::[])) when (FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid) -> begin
(

let uu____1539 = (

let uu____1540 = (FStar_Syntax_Subst.compress x)
in uu____1540.FStar_Syntax_Syntax.n)
in (match (uu____1539) with
| FStar_Syntax_Syntax.Tm_name (x1) -> begin
(

let goal1 = (

let uu___93_1546 = goal
in (

let uu____1547 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x1), (e))))::[]) goal.goal_ty)
in {context = uu___93_1546.context; witness = uu___93_1546.witness; goal_ty = uu____1547}))
in (replace goal1))
end
| uu____1550 -> begin
(fail "Not an equality hypothesis with a variable on the LHS")
end))
end
| uu____1551 -> begin
(fail "Not an equality hypothesis")
end));
))))


let clear : Prims.unit tac = (with_cur_goal "clear" (fun goal -> (

let uu____1555 = (FStar_TypeChecker_Env.pop_bv goal.context)
in (match (uu____1555) with
| None -> begin
(fail "Cannot clear; empty context")
end
| Some (x, env') -> begin
(

let fns = (FStar_Syntax_Free.names goal.goal_ty)
in (

let uu____1568 = (FStar_Util.set_mem x fns)
in (match (uu____1568) with
| true -> begin
(fail "Cannot clear; variable appears in goal")
end
| uu____1570 -> begin
(

let new_goal = (

let uu___94_1572 = goal
in {context = env'; witness = uu___94_1572.witness; goal_ty = uu___94_1572.goal_ty})
in (bind dismiss (fun uu____1573 -> (add_goals ((new_goal)::[])))))
end)))
end))))


let clear_hd : name  ->  Prims.unit tac = (fun x -> (with_cur_goal "clear_hd" (fun goal -> (

let uu____1580 = (FStar_TypeChecker_Env.pop_bv goal.context)
in (match (uu____1580) with
| None -> begin
(fail "Cannot clear_hd; empty context")
end
| Some (y, env') -> begin
(match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(fail "Cannot clear_hd; head variable mismatch")
end
| uu____1592 -> begin
clear
end)
end)))))


let revert : Prims.unit tac = (with_cur_goal "revert" (fun goal -> (

let uu____1595 = (FStar_TypeChecker_Env.pop_bv goal.context)
in (match (uu____1595) with
| None -> begin
(fail "Cannot clear_hd; empty context")
end
| Some (x, env') -> begin
(

let fns = (FStar_Syntax_Free.names goal.goal_ty)
in ((

let uu____1609 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.print1 "reverting %s\n" uu____1609));
(

let uu____1610 = (

let uu____1611 = (FStar_Util.set_mem x fns)
in (not (uu____1611)))
in (match (uu____1610) with
| true -> begin
(clear_hd x)
end
| uu____1613 -> begin
(

let new_goal = (

let uu____1615 = (

let uu____1624 = (un_squash x.FStar_Syntax_Syntax.sort)
in (

let uu____1628 = (un_squash goal.goal_ty)
in ((uu____1624), (uu____1628))))
in (match (uu____1615) with
| (Some (p), Some (q)) -> begin
(

let uu___95_1654 = goal
in (

let uu____1655 = (FStar_Syntax_Util.mk_imp p q)
in {context = env'; witness = uu___95_1654.witness; goal_ty = uu____1655}))
end
| uu____1656 -> begin
(

let uu___96_1665 = goal
in (

let uu____1666 = (

let uu____1667 = (FStar_TypeChecker_TcTerm.universe_of env' x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Util.mk_forall uu____1667 x goal.goal_ty))
in {context = env'; witness = uu___96_1665.witness; goal_ty = uu____1666}))
end))
in (bind dismiss (fun uu____1668 -> (add_goals ((new_goal)::[])))))
end));
))
end))))


let revert_hd : name  ->  Prims.unit tac = (fun x -> (with_cur_goal "revert_hd" (fun goal -> (

let uu____1675 = (FStar_TypeChecker_Env.pop_bv goal.context)
in (match (uu____1675) with
| None -> begin
(fail "Cannot revert_hd; empty context")
end
| Some (y, env') -> begin
(match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(

let uu____1687 = (

let uu____1688 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____1689 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Cannot revert_hd %s; head variable mismatch ... egot %s" uu____1688 uu____1689)))
in (fail uu____1687))
end
| uu____1690 -> begin
revert
end)
end)))))


let rec revert_all_hd : name Prims.list  ->  Prims.unit tac = (fun xs -> (match (xs) with
| [] -> begin
(ret ())
end
| (x)::xs1 -> begin
(

let uu____1702 = (revert_all_hd xs1)
in (bind uu____1702 (fun uu____1704 -> (revert_hd x))))
end))


let is_name : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun x -> (

let uu____1708 = (

let uu____1709 = (FStar_Syntax_Subst.compress x)
in uu____1709.FStar_Syntax_Syntax.n)
in (match (uu____1708) with
| FStar_Syntax_Syntax.Tm_name (uu____1712) -> begin
true
end
| uu____1713 -> begin
false
end)))


let as_name : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let uu____1717 = (

let uu____1718 = (FStar_Syntax_Subst.compress x)
in uu____1718.FStar_Syntax_Syntax.n)
in (match (uu____1717) with
| FStar_Syntax_Syntax.Tm_name (x1) -> begin
x1
end
| uu____1722 -> begin
(failwith "Not a name")
end)))


let destruct_equality_imp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.option = (fun t -> (

let uu____1734 = (FStar_Syntax_Util.destruct_typ_as_formula t)
in (match (uu____1734) with
| Some (FStar_Syntax_Util.BaseConn (l, ((lhs, uu____1746))::((rhs, uu____1748))::[])) when (FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid) -> begin
(

let uu____1774 = (FStar_Syntax_Util.destruct_typ_as_formula lhs)
in (match (uu____1774) with
| (Some (FStar_Syntax_Util.BaseConn (eq1, (_)::((x, _))::((e, _))::[]))) | (Some (FStar_Syntax_Util.BaseConn (eq1, ((x, _))::((e, _))::[]))) when ((FStar_Ident.lid_equals eq1 FStar_Syntax_Const.eq2_lid) && (is_name x)) -> begin
(

let uu____1846 = (

let uu____1854 = (as_name x)
in ((uu____1854), (e), (rhs)))
in Some (uu____1846))
end
| uu____1866 -> begin
None
end))
end
| uu____1875 -> begin
None
end)))


let at_most_one = (fun t -> (bind t (fun a -> (bind get (fun p -> (match (p.goals) with
| ([]) | ((_)::[]) -> begin
(ret a)
end
| uu____1898 -> begin
(fail "expected at most one goal remaining")
end))))))


let goal_to_string : goal  ->  Prims.string = (fun g1 -> (

let g1_binders = (

let uu____1904 = (FStar_TypeChecker_Env.all_binders g1.context)
in (FStar_All.pipe_right uu____1904 (FStar_Syntax_Print.binders_to_string ", ")))
in (

let uu____1905 = (FStar_Syntax_Print.term_to_string g1.goal_ty)
in (FStar_Util.format2 "%s |- %s" g1_binders uu____1905))))


let merge_sub_goals : Prims.unit tac = (

let uu____1907 = (bind get (fun p -> (match (p.goals) with
| (g1)::(g2)::rest -> begin
(

let uu____1915 = (((FStar_TypeChecker_Env.eq_gamma g1.context g2.context) && (FStar_Option.isNone g1.witness)) && (FStar_Option.isNone g2.witness))
in (match (uu____1915) with
| true -> begin
(

let uu____1917 = (

let uu___97_1918 = p
in (

let uu____1919 = (

let uu____1921 = (conj_goals g1 g2)
in (uu____1921)::rest)
in {main_context = uu___97_1918.main_context; main_goal = uu___97_1918.main_goal; all_implicits = uu___97_1918.all_implicits; goals = uu____1919; smt_goals = uu___97_1918.smt_goals; transaction = uu___97_1918.transaction}))
in (set uu____1917))
end
| uu____1922 -> begin
(

let g1_binders = (

let uu____1924 = (FStar_TypeChecker_Env.all_binders g1.context)
in (FStar_All.pipe_right uu____1924 (FStar_Syntax_Print.binders_to_string ", ")))
in (

let g2_binders = (

let uu____1926 = (FStar_TypeChecker_Env.all_binders g2.context)
in (FStar_All.pipe_right uu____1926 (FStar_Syntax_Print.binders_to_string ", ")))
in (

let uu____1927 = (

let uu____1928 = (goal_to_string g1)
in (

let uu____1929 = (goal_to_string g2)
in (

let uu____1930 = (

let uu____1931 = (FStar_TypeChecker_Env.eq_gamma g1.context g2.context)
in (FStar_All.pipe_right uu____1931 FStar_Util.string_of_bool))
in (FStar_Util.format3 "Cannot merge sub-goals: incompatible contexts:\ng1=%s\ng2=%s\neq_gamma=%s\n" uu____1928 uu____1929 uu____1930))))
in (fail uu____1927))))
end))
end
| uu____1932 -> begin
(

let goals = (

let uu____1935 = (FStar_All.pipe_right p.goals (FStar_List.map (fun x -> (FStar_Syntax_Print.term_to_string x.goal_ty))))
in (FStar_All.pipe_right uu____1935 (FStar_String.concat "\n\t")))
in (

let uu____1941 = (FStar_Util.format1 "Cannot merge sub-goals: not enough sub-goals\n\tGoals are: %s" goals)
in (fail uu____1941)))
end)))
in (name_tac "merge_sub_goals" uu____1907))


let rec visit : Prims.unit tac  ->  Prims.unit tac = (fun callback -> (

let uu____1949 = (

let uu____1951 = (with_cur_goal "visit_strengthen_else" (fun goal -> (

let uu____1954 = (FStar_Syntax_Util.destruct_typ_as_formula goal.goal_ty)
in (match (uu____1954) with
| None -> begin
(

let uu____1957 = (

let uu____1958 = (FStar_Syntax_Subst.compress goal.goal_ty)
in uu____1958.FStar_Syntax_Syntax.n)
in (match (uu____1957) with
| FStar_Syntax_Syntax.Tm_meta (uu____1962) -> begin
(

let uu____1967 = (visit callback)
in (map_meta uu____1967))
end
| uu____1969 -> begin
((

let uu____1971 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (FStar_Util.print1 "Not a formula, split to smt %s\n" uu____1971));
smt;
)
end))
end
| Some (FStar_Syntax_Util.QEx (uu____1972)) -> begin
((

let uu____1977 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (FStar_Util.print1 "Not yet handled: exists\n\tGoal is %s\n" uu____1977));
(ret ());
)
end
| Some (FStar_Syntax_Util.QAll (xs, uu____1979, uu____1980)) -> begin
(bind intros (fun binders -> (

let uu____1982 = (visit callback)
in (bind uu____1982 (fun uu____1984 -> (

let uu____1985 = (

let uu____1987 = (FStar_List.map Prims.fst binders)
in (revert_all_hd uu____1987))
in (bind uu____1985 (fun uu____1991 -> (with_cur_goal "inner" (fun goal1 -> ((

let uu____1994 = (goal_to_string goal1)
in (FStar_Util.print1 "After reverting intros, goal is %s\n" uu____1994));
(ret ());
)))))))))))
end
| Some (FStar_Syntax_Util.BaseConn (l, uu____1996)) when (FStar_Ident.lid_equals l FStar_Syntax_Const.and_lid) -> begin
(

let uu____1997 = (

let uu____1999 = (visit callback)
in (seq split uu____1999))
in (bind uu____1997 (fun uu____2001 -> merge_sub_goals)))
end
| Some (FStar_Syntax_Util.BaseConn (l, uu____2003)) when (FStar_Ident.lid_equals l FStar_Syntax_Const.imp_lid) -> begin
(bind imp_intro (fun h -> (

let uu____2005 = (visit callback)
in (bind uu____2005 (fun uu____2007 -> revert)))))
end
| Some (FStar_Syntax_Util.BaseConn (l, uu____2009)) -> begin
(or_else trivial smt)
end))))
in (or_else callback uu____1951))
in (focus_cur_goal "visit_strengthen" uu____1949)))


let proofstate_of_goal_ty : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  proofstate = (fun env g -> (

let g1 = (

let uu____2017 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env g)
in {context = env; witness = None; goal_ty = uu____2017})
in (

let uu____2018 = (FStar_Unionfind.new_transaction ())
in {main_context = env; main_goal = g1; all_implicits = []; goals = (g1)::[]; smt_goals = []; transaction = uu____2018})))




