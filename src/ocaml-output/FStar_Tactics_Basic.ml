
open Prims
open FStar_Pervasives

type name =
FStar_Syntax_Syntax.bv


type env =
FStar_TypeChecker_Env.env


type implicits =
FStar_TypeChecker_Env.implicits


let normalize : FStar_TypeChecker_Normalize.step Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (FStar_TypeChecker_Normalize.normalize_with_primitive_steps FStar_Reflection_Interpreter.reflection_primops s e t))


let bnorm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e t -> (normalize [] e t))

type goal =
{context : env; witness : FStar_Syntax_Syntax.term; goal_ty : FStar_Syntax_Syntax.typ; opts : FStar_Options.optionstate; is_guard : Prims.bool}


let __proj__Mkgoal__item__context : goal  ->  env = (fun projectee -> (match (projectee) with
| {context = __fname__context; witness = __fname__witness; goal_ty = __fname__goal_ty; opts = __fname__opts; is_guard = __fname__is_guard} -> begin
__fname__context
end))


let __proj__Mkgoal__item__witness : goal  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {context = __fname__context; witness = __fname__witness; goal_ty = __fname__goal_ty; opts = __fname__opts; is_guard = __fname__is_guard} -> begin
__fname__witness
end))


let __proj__Mkgoal__item__goal_ty : goal  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| {context = __fname__context; witness = __fname__witness; goal_ty = __fname__goal_ty; opts = __fname__opts; is_guard = __fname__is_guard} -> begin
__fname__goal_ty
end))


let __proj__Mkgoal__item__opts : goal  ->  FStar_Options.optionstate = (fun projectee -> (match (projectee) with
| {context = __fname__context; witness = __fname__witness; goal_ty = __fname__goal_ty; opts = __fname__opts; is_guard = __fname__is_guard} -> begin
__fname__opts
end))


let __proj__Mkgoal__item__is_guard : goal  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {context = __fname__context; witness = __fname__witness; goal_ty = __fname__goal_ty; opts = __fname__opts; is_guard = __fname__is_guard} -> begin
__fname__is_guard
end))

type proofstate =
{main_context : env; main_goal : goal; all_implicits : implicits; goals : goal Prims.list; smt_goals : goal Prims.list}


let __proj__Mkproofstate__item__main_context : proofstate  ->  env = (fun projectee -> (match (projectee) with
| {main_context = __fname__main_context; main_goal = __fname__main_goal; all_implicits = __fname__all_implicits; goals = __fname__goals; smt_goals = __fname__smt_goals} -> begin
__fname__main_context
end))


let __proj__Mkproofstate__item__main_goal : proofstate  ->  goal = (fun projectee -> (match (projectee) with
| {main_context = __fname__main_context; main_goal = __fname__main_goal; all_implicits = __fname__all_implicits; goals = __fname__goals; smt_goals = __fname__smt_goals} -> begin
__fname__main_goal
end))


let __proj__Mkproofstate__item__all_implicits : proofstate  ->  implicits = (fun projectee -> (match (projectee) with
| {main_context = __fname__main_context; main_goal = __fname__main_goal; all_implicits = __fname__all_implicits; goals = __fname__goals; smt_goals = __fname__smt_goals} -> begin
__fname__all_implicits
end))


let __proj__Mkproofstate__item__goals : proofstate  ->  goal Prims.list = (fun projectee -> (match (projectee) with
| {main_context = __fname__main_context; main_goal = __fname__main_goal; all_implicits = __fname__all_implicits; goals = __fname__goals; smt_goals = __fname__smt_goals} -> begin
__fname__goals
end))


let __proj__Mkproofstate__item__smt_goals : proofstate  ->  goal Prims.list = (fun projectee -> (match (projectee) with
| {main_context = __fname__main_context; main_goal = __fname__main_goal; all_implicits = __fname__all_implicits; goals = __fname__goals; smt_goals = __fname__smt_goals} -> begin
__fname__smt_goals
end))

type 'a result =
| Success of ('a * proofstate)
| Failed of (Prims.string * proofstate)


let uu___is_Success : 'a . 'a result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Success (_0) -> begin
true
end
| uu____228 -> begin
false
end))


let __proj__Success__item___0 : 'a . 'a result  ->  ('a * proofstate) = (fun projectee -> (match (projectee) with
| Success (_0) -> begin
_0
end))


let uu___is_Failed : 'a . 'a result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Failed (_0) -> begin
true
end
| uu____274 -> begin
false
end))


let __proj__Failed__item___0 : 'a . 'a result  ->  (Prims.string * proofstate) = (fun projectee -> (match (projectee) with
| Failed (_0) -> begin
_0
end))

exception TacFailure of (Prims.string)


let uu___is_TacFailure : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TacFailure (uu____309) -> begin
true
end
| uu____310 -> begin
false
end))


let __proj__TacFailure__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| TacFailure (uu____318) -> begin
uu____318
end))

type 'a tac =
{tac_f : proofstate  ->  'a result}


let __proj__Mktac__item__tac_f : 'a . 'a tac  ->  proofstate  ->  'a result = (fun projectee -> (match (projectee) with
| {tac_f = __fname__tac_f} -> begin
__fname__tac_f
end))


let mk_tac : 'a . (proofstate  ->  'a result)  ->  'a tac = (fun f -> {tac_f = f})


let run : 'Auu____382 . 'Auu____382 tac  ->  proofstate  ->  'Auu____382 result = (fun t p -> (t.tac_f p))


let ret : 'a . 'a  ->  'a tac = (fun x -> (mk_tac (fun p -> Success (((x), (p))))))


let bind : 'a 'b . 'a tac  ->  ('a  ->  'b tac)  ->  'b tac = (fun t1 t2 -> (mk_tac (fun p -> (

let uu____449 = (run t1 p)
in (match (uu____449) with
| Success (a, q) -> begin
(

let uu____456 = (t2 a)
in (run uu____456 q))
end
| Failed (msg, q) -> begin
Failed (((msg), (q)))
end)))))


let idtac : Prims.unit tac = (ret ())


let goal_to_string : goal  ->  Prims.string = (fun g -> (

let g_binders = (

let uu____468 = (FStar_TypeChecker_Env.all_binders g.context)
in (FStar_All.pipe_right uu____468 (FStar_Syntax_Print.binders_to_string ", ")))
in (

let w = (bnorm g.context g.witness)
in (

let t = (bnorm g.context g.goal_ty)
in (

let uu____471 = (FStar_Syntax_Print.term_to_string w)
in (

let uu____472 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "%s |- %s : %s" g_binders uu____471 uu____472)))))))


let tacprint : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "TAC>> %s\n" s))


let tacprint1 : Prims.string  ->  Prims.string  ->  Prims.unit = (fun s x -> (

let uu____485 = (FStar_Util.format1 s x)
in (FStar_Util.print1 "TAC>> %s\n" uu____485)))


let tacprint2 : Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.unit = (fun s x y -> (

let uu____498 = (FStar_Util.format2 s x y)
in (FStar_Util.print1 "TAC>> %s\n" uu____498)))


let tacprint3 : Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.unit = (fun s x y z -> (

let uu____515 = (FStar_Util.format3 s x y z)
in (FStar_Util.print1 "TAC>> %s\n" uu____515)))


let comp_to_typ : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____521) -> begin
t
end
| FStar_Syntax_Syntax.GTotal (t, uu____531) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let is_irrelevant : goal  ->  Prims.bool = (fun g -> (

let uu____545 = (

let uu____550 = (FStar_TypeChecker_Normalize.unfold_whnf g.context g.goal_ty)
in (FStar_Syntax_Util.un_squash uu____550))
in (match (uu____545) with
| FStar_Pervasives_Native.Some (t) -> begin
true
end
| uu____556 -> begin
false
end)))


let dump_goal : 'Auu____567 . 'Auu____567  ->  goal  ->  Prims.unit = (fun ps goal -> (

let uu____577 = (goal_to_string goal)
in (tacprint uu____577)))


let dump_cur : proofstate  ->  Prims.string  ->  Prims.unit = (fun ps msg -> (match (ps.goals) with
| [] -> begin
(tacprint1 "No more goals (%s)" msg)
end
| (h)::uu____587 -> begin
((tacprint1 "Current goal (%s):" msg);
(

let uu____591 = (FStar_List.hd ps.goals)
in (dump_goal ps uu____591));
)
end))


let ps_to_string : (Prims.string * proofstate)  ->  Prims.string = (fun uu____599 -> (match (uu____599) with
| (msg, ps) -> begin
(

let uu____606 = (FStar_Util.string_of_int (FStar_List.length ps.goals))
in (

let uu____607 = (

let uu____608 = (FStar_List.map goal_to_string ps.goals)
in (FStar_String.concat "\n" uu____608))
in (

let uu____611 = (FStar_Util.string_of_int (FStar_List.length ps.smt_goals))
in (

let uu____612 = (

let uu____613 = (FStar_List.map goal_to_string ps.smt_goals)
in (FStar_String.concat "\n" uu____613))
in (FStar_Util.format5 "State dump (%s):\nACTIVE goals (%s):\n%s\nSMT goals (%s):\n%s" msg uu____606 uu____607 uu____611 uu____612)))))
end))


let goal_to_json : goal  ->  FStar_Util.json = (fun g -> (

let g_binders = (

let uu____621 = (FStar_TypeChecker_Env.all_binders g.context)
in (FStar_All.pipe_right uu____621 FStar_Syntax_Print.binders_to_json))
in (

let uu____622 = (

let uu____629 = (

let uu____636 = (

let uu____641 = (

let uu____642 = (

let uu____649 = (

let uu____654 = (

let uu____655 = (FStar_Syntax_Print.term_to_string g.witness)
in FStar_Util.JsonStr (uu____655))
in (("witness"), (uu____654)))
in (

let uu____656 = (

let uu____663 = (

let uu____668 = (

let uu____669 = (FStar_Syntax_Print.term_to_string g.goal_ty)
in FStar_Util.JsonStr (uu____669))
in (("type"), (uu____668)))
in (uu____663)::[])
in (uu____649)::uu____656))
in FStar_Util.JsonAssoc (uu____642))
in (("goal"), (uu____641)))
in (uu____636)::[])
in ((("hyps"), (g_binders)))::uu____629)
in FStar_Util.JsonAssoc (uu____622))))


let ps_to_json : (Prims.string * proofstate)  ->  FStar_Util.json = (fun uu____701 -> (match (uu____701) with
| (msg, ps) -> begin
(

let uu____708 = (

let uu____715 = (

let uu____722 = (

let uu____727 = (

let uu____728 = (FStar_List.map goal_to_json ps.goals)
in FStar_Util.JsonList (uu____728))
in (("goals"), (uu____727)))
in (

let uu____731 = (

let uu____738 = (

let uu____743 = (

let uu____744 = (FStar_List.map goal_to_json ps.smt_goals)
in FStar_Util.JsonList (uu____744))
in (("smt-goals"), (uu____743)))
in (uu____738)::[])
in (uu____722)::uu____731))
in ((("label"), (FStar_Util.JsonStr (msg))))::uu____715)
in FStar_Util.JsonAssoc (uu____708))
end))


let dump_proofstate : proofstate  ->  Prims.string  ->  Prims.unit = (fun ps msg -> (FStar_Options.with_saved_options (fun uu____773 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(FStar_Util.print_generic "proof-state" ps_to_string ps_to_json ((msg), (ps)));
))))


let print_proof_state1 : Prims.string  ->  Prims.unit tac = (fun msg -> (mk_tac (fun p -> ((dump_cur p msg);
Success (((()), (p)));
))))


let print_proof_state : Prims.string  ->  Prims.unit tac = (fun msg -> (mk_tac (fun p -> ((dump_proofstate p msg);
Success (((()), (p)));
))))


let get : proofstate tac = (mk_tac (fun p -> Success (((p), (p)))))


let tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let rec log : proofstate  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun ps f -> (

let uu____833 = (FStar_ST.op_Bang tac_verb_dbg)
in (match (uu____833) with
| FStar_Pervasives_Native.None -> begin
((

let uu____855 = (

let uu____858 = (FStar_TypeChecker_Env.debug ps.main_context (FStar_Options.Other ("TacVerbose")))
in FStar_Pervasives_Native.Some (uu____858))
in (FStar_ST.op_Colon_Equals tac_verb_dbg uu____855));
(log ps f);
)
end
| FStar_Pervasives_Native.Some (true) -> begin
(f ())
end
| FStar_Pervasives_Native.Some (false) -> begin
()
end)))


let mlog : (Prims.unit  ->  Prims.unit)  ->  Prims.unit tac = (fun f -> (bind get (fun ps -> ((log ps f);
(ret ());
))))


let fail : 'Auu____898 . Prims.string  ->  'Auu____898 tac = (fun msg -> (mk_tac (fun ps -> ((

let uu____909 = (FStar_TypeChecker_Env.debug ps.main_context (FStar_Options.Other ("TacFail")))
in (match (uu____909) with
| true -> begin
(dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg))
end
| uu____910 -> begin
()
end));
Failed (((msg), (ps)));
))))


let fail1 : 'Auu____917 . Prims.string  ->  Prims.string  ->  'Auu____917 tac = (fun msg x -> (

let uu____928 = (FStar_Util.format1 msg x)
in (fail uu____928)))


let fail2 : 'Auu____937 . Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____937 tac = (fun msg x y -> (

let uu____952 = (FStar_Util.format2 msg x y)
in (fail uu____952)))


let fail3 : 'Auu____963 . Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____963 tac = (fun msg x y z -> (

let uu____982 = (FStar_Util.format3 msg x y z)
in (fail uu____982)))


let trytac : 'a . 'a tac  ->  'a FStar_Pervasives_Native.option tac = (fun t -> (mk_tac (fun ps -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____1010 = (run t ps)
in (match (uu____1010) with
| Success (a, q) -> begin
((FStar_Syntax_Unionfind.commit tx);
Success (((FStar_Pervasives_Native.Some (a)), (q)));
)
end
| Failed (uu____1024, uu____1025) -> begin
((FStar_Syntax_Unionfind.rollback tx);
Success (((FStar_Pervasives_Native.None), (ps)));
)
end))))))


let set : proofstate  ->  Prims.unit tac = (fun p -> (mk_tac (fun uu____1040 -> Success (((()), (p))))))


let do_unify : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t1 t2 -> try
(match (()) with
| () -> begin
(FStar_TypeChecker_Rel.teq_nosmt env t1 t2)
end)
with
| uu____1058 -> begin
false
end)


let trysolve : goal  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun goal solution -> (do_unify goal.context solution goal.witness))


let solve : goal  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun goal solution -> (

let uu____1075 = (trysolve goal solution)
in (match (uu____1075) with
| true -> begin
()
end
| uu____1076 -> begin
(

let uu____1077 = (

let uu____1078 = (

let uu____1079 = (FStar_Syntax_Print.term_to_string solution)
in (

let uu____1080 = (FStar_Syntax_Print.term_to_string goal.witness)
in (

let uu____1081 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (FStar_Util.format3 "%s does not solve %s : %s" uu____1079 uu____1080 uu____1081))))
in TacFailure (uu____1078))
in (FStar_Exn.raise uu____1077))
end)))


let dismiss : Prims.unit tac = (bind get (fun p -> (

let uu____1087 = (

let uu___88_1088 = p
in (

let uu____1089 = (FStar_List.tl p.goals)
in {main_context = uu___88_1088.main_context; main_goal = uu___88_1088.main_goal; all_implicits = uu___88_1088.all_implicits; goals = uu____1089; smt_goals = uu___88_1088.smt_goals}))
in (set uu____1087))))


let dismiss_all : Prims.unit tac = (bind get (fun p -> (set (

let uu___89_1098 = p
in {main_context = uu___89_1098.main_context; main_goal = uu___89_1098.main_goal; all_implicits = uu___89_1098.all_implicits; goals = []; smt_goals = uu___89_1098.smt_goals}))))


let add_goals : goal Prims.list  ->  Prims.unit tac = (fun gs -> (bind get (fun p -> (set (

let uu___90_1115 = p
in {main_context = uu___90_1115.main_context; main_goal = uu___90_1115.main_goal; all_implicits = uu___90_1115.all_implicits; goals = (FStar_List.append gs p.goals); smt_goals = uu___90_1115.smt_goals})))))


let add_smt_goals : goal Prims.list  ->  Prims.unit tac = (fun gs -> (bind get (fun p -> (set (

let uu___91_1132 = p
in {main_context = uu___91_1132.main_context; main_goal = uu___91_1132.main_goal; all_implicits = uu___91_1132.all_implicits; goals = uu___91_1132.goals; smt_goals = (FStar_List.append gs p.smt_goals)})))))


let push_goals : goal Prims.list  ->  Prims.unit tac = (fun gs -> (bind get (fun p -> (set (

let uu___92_1149 = p
in {main_context = uu___92_1149.main_context; main_goal = uu___92_1149.main_goal; all_implicits = uu___92_1149.all_implicits; goals = (FStar_List.append p.goals gs); smt_goals = uu___92_1149.smt_goals})))))


let push_smt_goals : goal Prims.list  ->  Prims.unit tac = (fun gs -> (bind get (fun p -> (set (

let uu___93_1166 = p
in {main_context = uu___93_1166.main_context; main_goal = uu___93_1166.main_goal; all_implicits = uu___93_1166.all_implicits; goals = uu___93_1166.goals; smt_goals = (FStar_List.append p.smt_goals gs)})))))


let replace_cur : goal  ->  Prims.unit tac = (fun g -> (bind dismiss (fun uu____1176 -> (add_goals ((g)::[])))))


let add_implicits : implicits  ->  Prims.unit tac = (fun i -> (bind get (fun p -> (set (

let uu___94_1189 = p
in {main_context = uu___94_1189.main_context; main_goal = uu___94_1189.main_goal; all_implicits = (FStar_List.append i p.all_implicits); goals = uu___94_1189.goals; smt_goals = uu___94_1189.smt_goals})))))


let new_uvar : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term tac = (fun env typ -> (

let uu____1214 = (FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar" typ.FStar_Syntax_Syntax.pos env typ)
in (match (uu____1214) with
| (u, uu____1230, g_u) -> begin
(

let uu____1244 = (add_implicits g_u.FStar_TypeChecker_Env.implicits)
in (bind uu____1244 (fun uu____1248 -> (ret u))))
end)))


let is_true : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1253 = (FStar_Syntax_Util.un_squash t)
in (match (uu____1253) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____1263 = (

let uu____1264 = (FStar_Syntax_Subst.compress t')
in uu____1264.FStar_Syntax_Syntax.n)
in (match (uu____1263) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)
end
| uu____1268 -> begin
false
end))
end
| uu____1269 -> begin
false
end)))


let is_false : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1278 = (FStar_Syntax_Util.un_squash t)
in (match (uu____1278) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____1288 = (

let uu____1289 = (FStar_Syntax_Subst.compress t')
in uu____1289.FStar_Syntax_Syntax.n)
in (match (uu____1288) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid)
end
| uu____1293 -> begin
false
end))
end
| uu____1294 -> begin
false
end)))


let cur_goal : goal tac = (bind get (fun p -> (match (p.goals) with
| [] -> begin
(fail "No more goals (1)")
end
| (hd1)::tl1 -> begin
(ret hd1)
end)))


let mk_irrelevant_goal : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Options.optionstate  ->  goal tac = (fun env phi opts -> (

let typ = (FStar_Syntax_Util.mk_squash phi)
in (

let uu____1328 = (new_uvar env typ)
in (bind uu____1328 (fun u -> (

let goal = {context = env; witness = u; goal_ty = typ; opts = opts; is_guard = false}
in (ret goal)))))))


let add_irrelevant_goal : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Options.optionstate  ->  Prims.unit tac = (fun env phi opts -> (

let uu____1351 = (mk_irrelevant_goal env phi opts)
in (bind uu____1351 (fun goal -> (add_goals ((goal)::[]))))))


let istrivial : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e t -> (

let steps = (FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.UnfoldTac)::(FStar_TypeChecker_Normalize.Unmeta)::[]
in (

let t1 = (normalize steps e t)
in (is_true t1))))


let trivial : Prims.unit tac = (bind cur_goal (fun goal -> (

let uu____1374 = (istrivial goal.context goal.goal_ty)
in (match (uu____1374) with
| true -> begin
((solve goal FStar_Syntax_Util.exp_unit);
dismiss;
)
end
| uu____1378 -> begin
(

let uu____1379 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (fail1 "Not a trivial goal: %s" uu____1379))
end))))


let add_goal_from_guard : env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Options.optionstate  ->  Prims.unit tac = (fun e g opts -> (

let uu____1396 = (

let uu____1397 = (FStar_TypeChecker_Rel.simplify_guard e g)
in uu____1397.FStar_TypeChecker_Env.guard_f)
in (match (uu____1396) with
| FStar_TypeChecker_Common.Trivial -> begin
(ret ())
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____1401 = (istrivial e f)
in (match (uu____1401) with
| true -> begin
(ret ())
end
| uu____1404 -> begin
(

let uu____1405 = (mk_irrelevant_goal e f opts)
in (bind uu____1405 (fun goal -> (

let goal1 = (

let uu___95_1412 = goal
in {context = uu___95_1412.context; witness = uu___95_1412.witness; goal_ty = uu___95_1412.goal_ty; opts = uu___95_1412.opts; is_guard = true})
in (push_goals ((goal1)::[]))))))
end))
end)))


let smt : Prims.unit tac = (bind cur_goal (fun g -> (

let uu____1418 = (is_irrelevant g)
in (match (uu____1418) with
| true -> begin
(bind dismiss (fun uu____1422 -> (add_smt_goals ((g)::[]))))
end
| uu____1423 -> begin
(

let uu____1424 = (FStar_Syntax_Print.term_to_string g.goal_ty)
in (fail1 "goal is not irrelevant: cannot dispatch to smt (%s)" uu____1424))
end))))


let divide : 'a 'b . Prims.int  ->  'a tac  ->  'b tac  ->  ('a * 'b) tac = (fun n1 l r -> (bind get (fun p -> (

let uu____1470 = try
(match (()) with
| () -> begin
(

let uu____1504 = (FStar_List.splitAt n1 p.goals)
in (ret uu____1504))
end)
with
| uu____1534 -> begin
(fail "divide: not enough goals")
end
in (bind uu____1470 (fun uu____1561 -> (match (uu____1561) with
| (lgs, rgs) -> begin
(

let lp = (

let uu___96_1587 = p
in {main_context = uu___96_1587.main_context; main_goal = uu___96_1587.main_goal; all_implicits = uu___96_1587.all_implicits; goals = lgs; smt_goals = []})
in (

let rp = (

let uu___97_1589 = p
in {main_context = uu___97_1589.main_context; main_goal = uu___97_1589.main_goal; all_implicits = uu___97_1589.all_implicits; goals = rgs; smt_goals = []})
in (

let uu____1590 = (set lp)
in (bind uu____1590 (fun uu____1598 -> (bind l (fun a -> (bind get (fun lp' -> (

let uu____1612 = (set rp)
in (bind uu____1612 (fun uu____1620 -> (bind r (fun b -> (bind get (fun rp' -> (

let p' = (

let uu___98_1636 = p
in {main_context = uu___98_1636.main_context; main_goal = uu___98_1636.main_goal; all_implicits = uu___98_1636.all_implicits; goals = (FStar_List.append lp'.goals rp'.goals); smt_goals = (FStar_List.append lp'.smt_goals (FStar_List.append rp'.smt_goals p.smt_goals))})
in (

let uu____1637 = (set p')
in (bind uu____1637 (fun uu____1645 -> (ret ((a), (b)))))))))))))))))))))))
end)))))))


let focus : 'a . 'a tac  ->  'a tac = (fun f -> (

let uu____1665 = (divide (Prims.parse_int "1") f idtac)
in (bind uu____1665 (fun uu____1678 -> (match (uu____1678) with
| (a, ()) -> begin
(ret a)
end)))))


let rec map : 'a . 'a tac  ->  'a Prims.list tac = (fun tau -> (bind get (fun p -> (match (p.goals) with
| [] -> begin
(ret [])
end
| (uu____1713)::uu____1714 -> begin
(

let uu____1717 = (

let uu____1726 = (map tau)
in (divide (Prims.parse_int "1") tau uu____1726))
in (bind uu____1717 (fun uu____1744 -> (match (uu____1744) with
| (h, t) -> begin
(ret ((h)::t))
end))))
end))))


let seq : Prims.unit tac  ->  Prims.unit tac  ->  Prims.unit tac = (fun t1 t2 -> (

let uu____1783 = (bind t1 (fun uu____1788 -> (

let uu____1789 = (map t2)
in (bind uu____1789 (fun uu____1797 -> (ret ()))))))
in (focus uu____1783)))


let intro : FStar_Syntax_Syntax.binder tac = (bind cur_goal (fun goal -> (

let uu____1808 = (FStar_Syntax_Util.arrow_one goal.goal_ty)
in (match (uu____1808) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____1823 = (

let uu____1824 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____1824)))
in (match (uu____1823) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____1827 -> begin
(

let env' = (FStar_TypeChecker_Env.push_binders goal.context ((b)::[]))
in (

let typ' = (comp_to_typ c)
in (

let uu____1830 = (new_uvar env' typ')
in (bind uu____1830 (fun u -> (

let uu____1837 = (

let uu____1838 = (FStar_Syntax_Util.abs ((b)::[]) u FStar_Pervasives_Native.None)
in (trysolve goal uu____1838))
in (match (uu____1837) with
| true -> begin
(

let uu____1841 = (

let uu____1844 = (

let uu___101_1845 = goal
in (

let uu____1846 = (bnorm env' u)
in (

let uu____1847 = (bnorm env' typ')
in {context = env'; witness = uu____1846; goal_ty = uu____1847; opts = uu___101_1845.opts; is_guard = uu___101_1845.is_guard})))
in (replace_cur uu____1844))
in (bind uu____1841 (fun uu____1849 -> (ret b))))
end
| uu____1850 -> begin
(fail "intro: unification failed")
end)))))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1855 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (fail1 "intro: goal is not an arrow (%s)" uu____1855))
end))))


let intro_rec : (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac = (bind cur_goal (fun goal -> ((FStar_Util.print_string "WARNING (intro_rec): calling this is known to cause normalizer loops\n");
(FStar_Util.print_string "WARNING (intro_rec): proceed at your own risk...\n");
(

let uu____1876 = (FStar_Syntax_Util.arrow_one goal.goal_ty)
in (match (uu____1876) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____1895 = (

let uu____1896 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____1896)))
in (match (uu____1895) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____1907 -> begin
(

let bv = (FStar_Syntax_Syntax.gen_bv "__recf" FStar_Pervasives_Native.None goal.goal_ty)
in (

let bs = (

let uu____1912 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____1912)::(b)::[])
in (

let env' = (FStar_TypeChecker_Env.push_binders goal.context bs)
in (

let uu____1914 = (

let uu____1917 = (comp_to_typ c)
in (new_uvar env' uu____1917))
in (bind uu____1914 (fun u -> (

let lb = (

let uu____1933 = (FStar_Syntax_Util.abs ((b)::[]) u FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] goal.goal_ty FStar_Parser_Const.effect_Tot_lid uu____1933))
in (

let body = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____1937 = (FStar_Syntax_Subst.close_let_rec ((lb)::[]) body)
in (match (uu____1937) with
| (lbs, body1) -> begin
(

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body1)))) FStar_Pervasives_Native.None goal.witness.FStar_Syntax_Syntax.pos)
in (

let res = (trysolve goal tm)
in (match (res) with
| true -> begin
(

let uu____1974 = (

let uu____1977 = (

let uu___102_1978 = goal
in (

let uu____1979 = (bnorm env' u)
in (

let uu____1980 = (

let uu____1981 = (comp_to_typ c)
in (bnorm env' uu____1981))
in {context = env'; witness = uu____1979; goal_ty = uu____1980; opts = uu___102_1978.opts; is_guard = uu___102_1978.is_guard})))
in (replace_cur uu____1977))
in (bind uu____1974 (fun uu____1988 -> (

let uu____1989 = (

let uu____1994 = (FStar_Syntax_Syntax.mk_binder bv)
in ((uu____1994), (b)))
in (ret uu____1989)))))
end
| uu____1999 -> begin
(fail "intro_rec: unification failed")
end)))
end))))))))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2008 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (fail1 "intro_rec: goal is not an arrow (%s)" uu____2008))
end));
)))


let norm : FStar_Syntax_Embeddings.norm_step Prims.list  ->  Prims.unit tac = (fun s -> (bind cur_goal (fun goal -> (

let steps = (

let uu____2033 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldTac)::[]) uu____2033))
in (

let w = (normalize steps goal.context goal.witness)
in (

let t = (normalize steps goal.context goal.goal_ty)
in (replace_cur (

let uu___103_2040 = goal
in {context = uu___103_2040.context; witness = w; goal_ty = t; opts = uu___103_2040.opts; is_guard = uu___103_2040.is_guard}))))))))


let norm_term : FStar_Syntax_Embeddings.norm_step Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun s t -> (bind get (fun ps -> (

let steps = (

let uu____2064 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldTac)::[]) uu____2064))
in (

let t1 = (normalize steps ps.main_context t)
in (ret t1))))))


let __exact : FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun t -> (bind cur_goal (fun goal -> (

let uu____2079 = try
(match (()) with
| () -> begin
(

let uu____2107 = (goal.context.FStar_TypeChecker_Env.type_of goal.context t)
in (ret uu____2107))
end)
with
| e -> begin
(

let uu____2134 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____2135 = (FStar_Syntax_Print.tag_of_term t)
in (fail2 "exact: term is not typeable: %s (%s)" uu____2134 uu____2135)))
end
in (bind uu____2079 (fun uu____2153 -> (match (uu____2153) with
| (t1, typ, guard) -> begin
(

let uu____2165 = (

let uu____2166 = (

let uu____2167 = (FStar_TypeChecker_Rel.discharge_guard goal.context guard)
in (FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____2167))
in (not (uu____2166)))
in (match (uu____2165) with
| true -> begin
(fail "exact: got non-trivial guard")
end
| uu____2170 -> begin
(

let uu____2171 = (do_unify goal.context typ goal.goal_ty)
in (match (uu____2171) with
| true -> begin
((solve goal t1);
dismiss;
)
end
| uu____2175 -> begin
(

let uu____2176 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____2177 = (

let uu____2178 = (bnorm goal.context typ)
in (FStar_Syntax_Print.term_to_string uu____2178))
in (

let uu____2179 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (fail3 "%s : %s does not exactly solve the goal %s" uu____2176 uu____2177 uu____2179))))
end))
end))
end)))))))


let exact : FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun t -> (

let uu____2188 = (__exact t)
in (focus uu____2188)))


let exact_lemma : FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun t -> (bind cur_goal (fun goal -> (

let uu____2202 = try
(match (()) with
| () -> begin
(

let uu____2230 = (FStar_TypeChecker_TcTerm.tc_term goal.context t)
in (ret uu____2230))
end)
with
| e -> begin
(

let uu____2257 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____2258 = (FStar_Syntax_Print.tag_of_term t)
in (fail2 "exact_lemma: term is not typeable: %s (%s)" uu____2257 uu____2258)))
end
in (bind uu____2202 (fun uu____2276 -> (match (uu____2276) with
| (t1, lcomp, guard) -> begin
(

let comp = (lcomp.FStar_Syntax_Syntax.comp ())
in (match ((not ((FStar_Syntax_Util.is_lemma_comp comp)))) with
| true -> begin
(fail "exact_lemma: not a lemma")
end
| uu____2293 -> begin
(

let uu____2294 = (

let uu____2295 = (FStar_TypeChecker_Rel.is_trivial guard)
in (not (uu____2295)))
in (match (uu____2294) with
| true -> begin
(fail "exact: got non-trivial guard")
end
| uu____2298 -> begin
(

let uu____2299 = (

let uu____2308 = (

let uu____2317 = (FStar_Syntax_Util.comp_to_comp_typ comp)
in uu____2317.FStar_Syntax_Syntax.effect_args)
in (match (uu____2308) with
| (pre)::(post)::uu____2328 -> begin
(((FStar_Pervasives_Native.fst pre)), ((FStar_Pervasives_Native.fst post)))
end
| uu____2369 -> begin
(failwith "exact_lemma: impossible: not a lemma")
end))
in (match (uu____2299) with
| (pre, post) -> begin
(

let uu____2398 = (do_unify goal.context post goal.goal_ty)
in (match (uu____2398) with
| true -> begin
((solve goal t1);
(bind dismiss (fun uu____2403 -> (add_irrelevant_goal goal.context pre goal.opts)));
)
end
| uu____2404 -> begin
(

let uu____2405 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____2406 = (FStar_Syntax_Print.term_to_string post)
in (

let uu____2407 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (fail3 "%s : %s does not exactly solve the goal %s" uu____2405 uu____2406 uu____2407))))
end))
end))
end))
end))
end)))))))


let uvar_free_in_goal : FStar_Syntax_Syntax.uvar  ->  goal  ->  Prims.bool = (fun u g -> (match (g.is_guard) with
| true -> begin
false
end
| uu____2416 -> begin
(

let free_uvars = (

let uu____2420 = (

let uu____2427 = (FStar_Syntax_Free.uvars g.goal_ty)
in (FStar_Util.set_elements uu____2427))
in (FStar_List.map FStar_Pervasives_Native.fst uu____2420))
in (FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars))
end))


let uvar_free : FStar_Syntax_Syntax.uvar  ->  proofstate  ->  Prims.bool = (fun u ps -> (FStar_List.existsML (uvar_free_in_goal u) ps.goals))

exception NoUnif


let uu___is_NoUnif : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoUnif -> begin
true
end
| uu____2454 -> begin
false
end))


let rec __apply : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit tac = (fun uopt tm typ -> (bind cur_goal (fun goal -> (

let uu____2474 = (

let uu____2479 = (__exact tm)
in (trytac uu____2479))
in (bind uu____2474 (fun r -> (match (r) with
| FStar_Pervasives_Native.Some (r1) -> begin
(ret ())
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2492 = (FStar_Syntax_Util.arrow_one typ)
in (match (uu____2492) with
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise NoUnif)
end
| FStar_Pervasives_Native.Some ((bv, aq), c) -> begin
(

let uu____2522 = (

let uu____2523 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____2523)))
in (match (uu____2522) with
| true -> begin
(fail "apply: not total codomain")
end
| uu____2526 -> begin
(

let uu____2527 = (new_uvar goal.context bv.FStar_Syntax_Syntax.sort)
in (bind uu____2527 (fun u -> (

let tm' = (FStar_Syntax_Syntax.mk_Tm_app tm ((((u), (aq)))::[]) FStar_Pervasives_Native.None goal.context.FStar_TypeChecker_Env.range)
in (

let typ' = (

let uu____2547 = (comp_to_typ c)
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (u))))::[])) uu____2547))
in (

let uu____2548 = (__apply uopt tm' typ')
in (bind uu____2548 (fun uu____2555 -> (

let uu____2556 = (

let uu____2557 = (

let uu____2560 = (

let uu____2561 = (FStar_Syntax_Util.head_and_args u)
in (FStar_Pervasives_Native.fst uu____2561))
in (FStar_Syntax_Subst.compress uu____2560))
in uu____2557.FStar_Syntax_Syntax.n)
in (match (uu____2556) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____2589) -> begin
(bind get (fun ps -> (

let uu____2617 = (uopt && (uvar_free uvar ps))
in (match (uu____2617) with
| true -> begin
(ret ())
end
| uu____2620 -> begin
(

let uu____2621 = (

let uu____2624 = (

let uu___108_2625 = goal
in (

let uu____2626 = (bnorm goal.context u)
in (

let uu____2627 = (bnorm goal.context bv.FStar_Syntax_Syntax.sort)
in {context = uu___108_2625.context; witness = uu____2626; goal_ty = uu____2627; opts = uu___108_2625.opts; is_guard = false})))
in (uu____2624)::[])
in (add_goals uu____2621))
end))))
end
| uu____2628 -> begin
(ret ())
end))))))))))
end))
end))
end)))))))


let try_unif : 'a . 'a tac  ->  'a tac  ->  'a tac = (fun t t' -> (mk_tac (fun ps -> try
(match (()) with
| () -> begin
(run t ps)
end)
with
| NoUnif -> begin
(run t' ps)
end)))


let apply : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun uopt tm -> (bind cur_goal (fun goal -> (

let uu____2686 = (goal.context.FStar_TypeChecker_Env.type_of goal.context tm)
in (match (uu____2686) with
| (tm1, typ, guard) -> begin
(

let uu____2698 = (

let uu____2701 = (

let uu____2704 = (__apply uopt tm1 typ)
in (bind uu____2704 (fun uu____2708 -> (add_goal_from_guard goal.context guard goal.opts))))
in (focus uu____2701))
in (

let uu____2709 = (

let uu____2712 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____2713 = (FStar_Syntax_Print.term_to_string typ)
in (

let uu____2714 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (fail3 "apply: Cannot instantiate %s (of type %s) to match goal (%s)" uu____2712 uu____2713 uu____2714))))
in (try_unif uu____2698 uu____2709)))
end)))))


let apply_lemma : FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun tm -> (

let uu____2723 = (

let is_unit_t = (fun t -> (

let uu____2730 = (

let uu____2731 = (FStar_Syntax_Subst.compress t)
in uu____2731.FStar_Syntax_Syntax.n)
in (match (uu____2730) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
true
end
| uu____2735 -> begin
false
end)))
in (bind cur_goal (fun goal -> (

let uu____2745 = (goal.context.FStar_TypeChecker_Env.type_of goal.context tm)
in (match (uu____2745) with
| (tm1, t, guard) -> begin
(

let uu____2757 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____2757) with
| (bs, comp) -> begin
(match ((not ((FStar_Syntax_Util.is_lemma_comp comp)))) with
| true -> begin
(fail "apply_lemma: not a lemma")
end
| uu____2786 -> begin
(

let uu____2787 = (FStar_List.fold_left (fun uu____2833 uu____2834 -> (match (((uu____2833), (uu____2834))) with
| ((uvs, guard1, subst1), (b, aq)) -> begin
(

let b_t = (FStar_Syntax_Subst.subst subst1 b.FStar_Syntax_Syntax.sort)
in (

let uu____2937 = (is_unit_t b_t)
in (match (uu____2937) with
| true -> begin
(((((FStar_Syntax_Util.exp_unit), (aq)))::uvs), (guard1), ((FStar_Syntax_Syntax.NT (((b), (FStar_Syntax_Util.exp_unit))))::subst1))
end
| uu____2974 -> begin
(

let uu____2975 = (FStar_TypeChecker_Util.new_implicit_var "apply_lemma" goal.goal_ty.FStar_Syntax_Syntax.pos goal.context b_t)
in (match (uu____2975) with
| (u, uu____3005, g_u) -> begin
(

let uu____3019 = (FStar_TypeChecker_Rel.conj_guard guard1 g_u)
in (((((u), (aq)))::uvs), (uu____3019), ((FStar_Syntax_Syntax.NT (((b), (u))))::subst1)))
end))
end)))
end)) (([]), (guard), ([])) bs)
in (match (uu____2787) with
| (uvs, implicits, subst1) -> begin
(

let uvs1 = (FStar_List.rev uvs)
in (

let comp1 = (FStar_Syntax_Subst.subst_comp subst1 comp)
in (

let uu____3089 = (

let uu____3098 = (

let uu____3107 = (FStar_Syntax_Util.comp_to_comp_typ comp1)
in uu____3107.FStar_Syntax_Syntax.effect_args)
in (match (uu____3098) with
| (pre)::(post)::uu____3118 -> begin
(((FStar_Pervasives_Native.fst pre)), ((FStar_Pervasives_Native.fst post)))
end
| uu____3159 -> begin
(failwith "apply_lemma: impossible: not a lemma")
end))
in (match (uu____3089) with
| (pre, post) -> begin
(

let uu____3188 = (

let uu____3189 = (

let uu____3190 = (FStar_Syntax_Util.mk_squash post)
in (do_unify goal.context uu____3190 goal.goal_ty))
in (not (uu____3189)))
in (match (uu____3188) with
| true -> begin
(

let uu____3193 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____3194 = (

let uu____3195 = (FStar_Syntax_Util.mk_squash post)
in (FStar_Syntax_Print.term_to_string uu____3195))
in (

let uu____3196 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (fail3 "apply_lemma: Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)" uu____3193 uu____3194 uu____3196))))
end
| uu____3197 -> begin
(

let solution = (FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1 FStar_Pervasives_Native.None goal.context.FStar_TypeChecker_Env.range)
in (

let implicits1 = (FStar_All.pipe_right implicits.FStar_TypeChecker_Env.implicits (FStar_List.filter (fun uu____3268 -> (match (uu____3268) with
| (uu____3281, uu____3282, uu____3283, tm2, uu____3285, uu____3286) -> begin
(

let uu____3287 = (FStar_Syntax_Util.head_and_args tm2)
in (match (uu____3287) with
| (hd1, uu____3303) -> begin
(

let uu____3324 = (

let uu____3325 = (FStar_Syntax_Subst.compress hd1)
in uu____3325.FStar_Syntax_Syntax.n)
in (match (uu____3324) with
| FStar_Syntax_Syntax.Tm_uvar (uu____3328) -> begin
true
end
| uu____3345 -> begin
false
end))
end))
end))))
in ((solve goal solution);
(

let uu____3347 = (add_implicits implicits1)
in (bind uu____3347 (fun uu____3351 -> (bind dismiss (fun uu____3360 -> (

let is_free_uvar = (fun uv t1 -> (

let free_uvars = (

let uu____3371 = (

let uu____3378 = (FStar_Syntax_Free.uvars t1)
in (FStar_Util.set_elements uu____3378))
in (FStar_List.map FStar_Pervasives_Native.fst uu____3371))
in (FStar_List.existsML (fun u -> (FStar_Syntax_Unionfind.equiv u uv)) free_uvars)))
in (

let appears = (fun uv goals -> (FStar_List.existsML (fun g' -> (is_free_uvar uv g'.goal_ty)) goals))
in (

let checkone = (fun t1 goals -> (

let uu____3419 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____3419) with
| (hd1, uu____3435) -> begin
(match (hd1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____3457) -> begin
(appears uv goals)
end
| uu____3482 -> begin
false
end)
end)))
in (

let sub_goals = (FStar_All.pipe_right implicits1 (FStar_List.map (fun uu____3524 -> (match (uu____3524) with
| (_msg, _env, _uvar, term, typ, uu____3542) -> begin
(

let uu___111_3543 = goal
in (

let uu____3544 = (bnorm goal.context term)
in (

let uu____3545 = (bnorm goal.context typ)
in {context = uu___111_3543.context; witness = uu____3544; goal_ty = uu____3545; opts = uu___111_3543.opts; is_guard = uu___111_3543.is_guard})))
end))))
in (

let rec filter' = (fun f xs -> (match (xs) with
| [] -> begin
[]
end
| (x)::xs1 -> begin
(

let uu____3583 = (f x xs1)
in (match (uu____3583) with
| true -> begin
(

let uu____3586 = (filter' f xs1)
in (x)::uu____3586)
end
| uu____3589 -> begin
(filter' f xs1)
end))
end))
in (

let sub_goals1 = (filter' (fun g goals -> (

let uu____3600 = (checkone g.witness goals)
in (not (uu____3600)))) sub_goals)
in (

let uu____3601 = (add_goal_from_guard goal.context guard goal.opts)
in (bind uu____3601 (fun uu____3606 -> (

let uu____3607 = (add_irrelevant_goal goal.context pre goal.opts)
in (bind uu____3607 (fun uu____3612 -> (

let uu____3613 = (trytac trivial)
in (bind uu____3613 (fun uu____3621 -> (add_goals sub_goals1)))))))))))))))))))));
)))
end))
end))))
end))
end)
end))
end)))))
in (focus uu____2723)))


let destruct_eq' : FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun typ -> (

let uu____3640 = (FStar_Syntax_Util.destruct_typ_as_formula typ)
in (match (uu____3640) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (l, (uu____3650)::((e1, uu____3652))::((e2, uu____3654))::[])) when (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) -> begin
FStar_Pervasives_Native.Some (((e1), (e2)))
end
| uu____3713 -> begin
FStar_Pervasives_Native.None
end)))


let destruct_eq : FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun typ -> (

let uu____3736 = (destruct_eq' typ)
in (match (uu____3736) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3766 = (FStar_Syntax_Util.un_squash typ)
in (match (uu____3766) with
| FStar_Pervasives_Native.Some (typ1) -> begin
(destruct_eq' typ1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end)))


let rewrite : FStar_Syntax_Syntax.binder  ->  Prims.unit tac = (fun h -> (bind cur_goal (fun goal -> (

let uu____3799 = (FStar_All.pipe_left mlog (fun uu____3809 -> (

let uu____3810 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst h))
in (

let uu____3811 = (FStar_Syntax_Print.term_to_string (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "+++Rewrite %s : %s\n" uu____3810 uu____3811)))))
in (bind uu____3799 (fun uu____3819 -> (

let uu____3820 = (

let uu____3827 = (

let uu____3828 = (FStar_TypeChecker_Env.lookup_bv goal.context (FStar_Pervasives_Native.fst h))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3828))
in (destruct_eq uu____3827))
in (match (uu____3820) with
| FStar_Pervasives_Native.Some (x, e) -> begin
(

let uu____3845 = (

let uu____3846 = (FStar_Syntax_Subst.compress x)
in uu____3846.FStar_Syntax_Syntax.n)
in (match (uu____3845) with
| FStar_Syntax_Syntax.Tm_name (x1) -> begin
(

let goal1 = (

let uu___112_3853 = goal
in (

let uu____3854 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x1), (e))))::[]) goal.witness)
in (

let uu____3855 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x1), (e))))::[]) goal.goal_ty)
in {context = uu___112_3853.context; witness = uu____3854; goal_ty = uu____3855; opts = uu___112_3853.opts; is_guard = uu___112_3853.is_guard})))
in (replace_cur goal1))
end
| uu____3856 -> begin
(fail "Not an equality hypothesis with a variable on the LHS")
end))
end
| uu____3857 -> begin
(fail "Not an equality hypothesis")
end))))))))


let subst_goal : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  goal  ->  goal = (fun b1 b2 s g -> (

let rec alpha = (fun e -> (

let uu____3888 = (FStar_TypeChecker_Env.pop_bv e)
in (match (uu____3888) with
| FStar_Pervasives_Native.None -> begin
e
end
| FStar_Pervasives_Native.Some (bv, e') -> begin
(match ((FStar_Syntax_Syntax.bv_eq bv b1)) with
| true -> begin
(FStar_TypeChecker_Env.push_bv e' b2)
end
| uu____3905 -> begin
(

let uu____3906 = (alpha e')
in (

let uu____3907 = (

let uu___113_3908 = bv
in (

let uu____3909 = (FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___113_3908.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___113_3908.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3909}))
in (FStar_TypeChecker_Env.push_bv uu____3906 uu____3907)))
end)
end)))
in (

let c = (alpha g.context)
in (

let w = (FStar_Syntax_Subst.subst s g.witness)
in (

let t = (FStar_Syntax_Subst.subst s g.goal_ty)
in (

let uu___114_3915 = g
in {context = c; witness = w; goal_ty = t; opts = uu___114_3915.opts; is_guard = uu___114_3915.is_guard}))))))


let rename_to : FStar_Syntax_Syntax.binder  ->  Prims.string  ->  Prims.unit tac = (fun b s -> (bind cur_goal (fun goal -> (

let uu____3936 = b
in (match (uu____3936) with
| (bv, uu____3940) -> begin
(

let bv' = (FStar_Syntax_Syntax.freshen_bv (

let uu___115_3944 = bv
in {FStar_Syntax_Syntax.ppname = (FStar_Ident.mk_ident ((s), (bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange))); FStar_Syntax_Syntax.index = uu___115_3944.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___115_3944.FStar_Syntax_Syntax.sort}))
in (

let s1 = (

let uu____3948 = (

let uu____3949 = (

let uu____3956 = (FStar_Syntax_Syntax.bv_to_name bv')
in ((bv), (uu____3956)))
in FStar_Syntax_Syntax.NT (uu____3949))
in (uu____3948)::[])
in (

let uu____3957 = (subst_goal bv bv' s1 goal)
in (replace_cur uu____3957))))
end)))))


let revert : Prims.unit tac = (bind cur_goal (fun goal -> (

let uu____3963 = (FStar_TypeChecker_Env.pop_bv goal.context)
in (match (uu____3963) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot revert; empty context")
end
| FStar_Pervasives_Native.Some (x, env') -> begin
(

let typ' = (

let uu____3985 = (FStar_Syntax_Syntax.mk_Total goal.goal_ty)
in (FStar_Syntax_Util.arrow ((((x), (FStar_Pervasives_Native.None)))::[]) uu____3985))
in (

let w' = (FStar_Syntax_Util.abs ((((x), (FStar_Pervasives_Native.None)))::[]) goal.witness FStar_Pervasives_Native.None)
in (replace_cur (

let uu___116_4019 = goal
in {context = env'; witness = w'; goal_ty = typ'; opts = uu___116_4019.opts; is_guard = uu___116_4019.is_guard}))))
end))))


let revert_hd : name  ->  Prims.unit tac = (fun x -> (bind cur_goal (fun goal -> (

let uu____4031 = (FStar_TypeChecker_Env.pop_bv goal.context)
in (match (uu____4031) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot revert_hd; empty context")
end
| FStar_Pervasives_Native.Some (y, env') -> begin
(match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(

let uu____4052 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____4053 = (FStar_Syntax_Print.bv_to_string y)
in (fail2 "Cannot revert_hd %s; head variable mismatch ... egot %s" uu____4052 uu____4053)))
end
| uu____4054 -> begin
revert
end)
end)))))


let clear_top : Prims.unit tac = (bind cur_goal (fun goal -> (

let uu____4060 = (FStar_TypeChecker_Env.pop_bv goal.context)
in (match (uu____4060) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot clear; empty context")
end
| FStar_Pervasives_Native.Some (x, env') -> begin
(

let fns_ty = (FStar_Syntax_Free.names goal.goal_ty)
in (

let uu____4082 = (FStar_Util.set_mem x fns_ty)
in (match (uu____4082) with
| true -> begin
(fail "Cannot clear; variable appears in goal")
end
| uu____4085 -> begin
(

let uu____4086 = (new_uvar env' goal.goal_ty)
in (bind uu____4086 (fun u -> (

let uu____4092 = (

let uu____4093 = (trysolve goal u)
in (not (uu____4093)))
in (match (uu____4092) with
| true -> begin
(fail "clear: unification failed")
end
| uu____4096 -> begin
(

let new_goal = (

let uu___117_4098 = goal
in (

let uu____4099 = (bnorm env' u)
in {context = env'; witness = uu____4099; goal_ty = uu___117_4098.goal_ty; opts = uu___117_4098.opts; is_guard = uu___117_4098.is_guard}))
in (bind dismiss (fun uu____4101 -> (add_goals ((new_goal)::[])))))
end)))))
end)))
end))))


let rec clear : FStar_Syntax_Syntax.binder  ->  Prims.unit tac = (fun b -> (bind cur_goal (fun goal -> (

let uu____4113 = (FStar_TypeChecker_Env.pop_bv goal.context)
in (match (uu____4113) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot clear; empty context")
end
| FStar_Pervasives_Native.Some (b', env') -> begin
(match ((FStar_Syntax_Syntax.bv_eq (FStar_Pervasives_Native.fst b) b')) with
| true -> begin
clear_top
end
| uu____4134 -> begin
(bind revert (fun uu____4137 -> (

let uu____4138 = (clear b)
in (bind uu____4138 (fun uu____4142 -> (bind intro (fun uu____4144 -> (ret ()))))))))
end)
end)))))


let prune : Prims.string  ->  Prims.unit tac = (fun s -> (bind cur_goal (fun g -> (

let ctx = g.context
in (

let ctx' = (FStar_TypeChecker_Env.rem_proof_ns ctx (FStar_Ident.path_of_text s))
in (

let g' = (

let uu___118_4161 = g
in {context = ctx'; witness = uu___118_4161.witness; goal_ty = uu___118_4161.goal_ty; opts = uu___118_4161.opts; is_guard = uu___118_4161.is_guard})
in (bind dismiss (fun uu____4163 -> (add_goals ((g')::[]))))))))))


let addns : Prims.string  ->  Prims.unit tac = (fun s -> (bind cur_goal (fun g -> (

let ctx = g.context
in (

let ctx' = (FStar_TypeChecker_Env.add_proof_ns ctx (FStar_Ident.path_of_text s))
in (

let g' = (

let uu___119_4180 = g
in {context = ctx'; witness = uu___119_4180.witness; goal_ty = uu___119_4180.goal_ty; opts = uu___119_4180.opts; is_guard = uu___119_4180.is_guard})
in (bind dismiss (fun uu____4182 -> (add_goals ((g')::[]))))))))))


let rec mapM : 'a 'b . ('a  ->  'b tac)  ->  'a Prims.list  ->  'b Prims.list tac = (fun f l -> (match (l) with
| [] -> begin
(ret [])
end
| (x)::xs -> begin
(

let uu____4224 = (f x)
in (bind uu____4224 (fun y -> (

let uu____4232 = (mapM f xs)
in (bind uu____4232 (fun ys -> (ret ((y)::ys))))))))
end))


let rec tac_bottom_fold_env : (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac)  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun f env t -> (

let tn = (

let uu____4278 = (FStar_Syntax_Subst.compress t)
in uu____4278.FStar_Syntax_Syntax.n)
in (

let tn1 = (match (tn) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let ff = (tac_bottom_fold_env f env)
in (

let uu____4313 = (ff hd1)
in (bind uu____4313 (fun hd2 -> (

let fa = (fun uu____4333 -> (match (uu____4333) with
| (a, q) -> begin
(

let uu____4346 = (ff a)
in (bind uu____4346 (fun a1 -> (ret ((a1), (q))))))
end))
in (

let uu____4359 = (mapM fa args)
in (bind uu____4359 (fun args1 -> (ret (FStar_Syntax_Syntax.Tm_app (((hd2), (args1)))))))))))))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, k) -> begin
(

let uu____4419 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____4419) with
| (bs1, t') -> begin
(

let uu____4428 = (

let uu____4431 = (FStar_TypeChecker_Env.push_binders env bs1)
in (tac_bottom_fold_env f uu____4431 t'))
in (bind uu____4428 (fun t'' -> (

let uu____4435 = (

let uu____4436 = (

let uu____4453 = (FStar_Syntax_Subst.close_binders bs1)
in (

let uu____4454 = (FStar_Syntax_Subst.close bs1 t'')
in ((uu____4453), (uu____4454), (k))))
in FStar_Syntax_Syntax.Tm_abs (uu____4436))
in (ret uu____4435)))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(ret tn)
end
| uu____4475 -> begin
(ret tn)
end)
in (bind tn1 (fun tn2 -> (f env (

let uu___120_4479 = t
in {FStar_Syntax_Syntax.n = tn2; FStar_Syntax_Syntax.pos = uu___120_4479.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___120_4479.FStar_Syntax_Syntax.vars})))))))


let pointwise_rec : proofstate  ->  Prims.unit tac  ->  FStar_Options.optionstate  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun ps tau opts env t -> (

let uu____4508 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____4508) with
| (t1, lcomp, g) -> begin
(

let uu____4520 = (

let uu____4521 = (FStar_TypeChecker_Rel.is_trivial g)
in (not (uu____4521)))
in (match (uu____4520) with
| true -> begin
(ret t1)
end
| uu____4524 -> begin
(

let typ = lcomp.FStar_Syntax_Syntax.res_typ
in (

let uu____4528 = (new_uvar env typ)
in (bind uu____4528 (fun ut -> ((log ps (fun uu____4539 -> (

let uu____4540 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____4541 = (FStar_Syntax_Print.term_to_string ut)
in (FStar_Util.print2 "Pointwise_rec: making equality %s = %s\n" uu____4540 uu____4541)))));
(

let uu____4542 = (

let uu____4545 = (

let uu____4546 = (FStar_TypeChecker_TcTerm.universe_of env typ)
in (FStar_Syntax_Util.mk_eq2 uu____4546 typ t1 ut))
in (add_irrelevant_goal env uu____4545 opts))
in (bind uu____4542 (fun uu____4549 -> (

let uu____4550 = (bind tau (fun uu____4555 -> (

let ut1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env ut)
in (ret ut1))))
in (focus uu____4550)))));
)))))
end))
end)))


let pointwise : Prims.unit tac  ->  Prims.unit tac = (fun tau -> (bind get (fun ps -> (

let uu____4576 = (match (ps.goals) with
| (g)::gs -> begin
((g), (gs))
end
| [] -> begin
(failwith "Pointwise: no goals")
end)
in (match (uu____4576) with
| (g, gs) -> begin
(

let gt1 = g.goal_ty
in ((log ps (fun uu____4613 -> (

let uu____4614 = (FStar_Syntax_Print.term_to_string gt1)
in (FStar_Util.print1 "Pointwise starting with %s\n" uu____4614))));
(bind dismiss_all (fun uu____4617 -> (

let uu____4618 = (tac_bottom_fold_env (pointwise_rec ps tau g.opts) g.context gt1)
in (bind uu____4618 (fun gt' -> ((log ps (fun uu____4628 -> (

let uu____4629 = (FStar_Syntax_Print.term_to_string gt')
in (FStar_Util.print1 "Pointwise seems to have succeded with %s\n" uu____4629))));
(

let uu____4630 = (push_goals gs)
in (bind uu____4630 (fun uu____4634 -> (add_goals (((

let uu___121_4636 = g
in {context = uu___121_4636.context; witness = uu___121_4636.witness; goal_ty = gt'; opts = uu___121_4636.opts; is_guard = uu___121_4636.is_guard}))::[])))));
))))));
))
end)))))


let trefl : Prims.unit tac = (bind cur_goal (fun g -> (

let uu____4656 = (FStar_Syntax_Util.un_squash g.goal_ty)
in (match (uu____4656) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____4668 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____4668) with
| (hd1, args) -> begin
(

let uu____4701 = (

let uu____4714 = (

let uu____4715 = (FStar_Syntax_Util.un_uinst hd1)
in uu____4715.FStar_Syntax_Syntax.n)
in ((uu____4714), (args)))
in (match (uu____4701) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4729)::((l, uu____4731))::((r, uu____4733))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid) -> begin
(

let uu____4780 = (

let uu____4781 = (do_unify g.context l r)
in (not (uu____4781)))
in (match (uu____4780) with
| true -> begin
(

let uu____4784 = (FStar_Syntax_Print.term_to_string l)
in (

let uu____4785 = (FStar_Syntax_Print.term_to_string r)
in (fail2 "trefl: not a trivial equality (%s vs %s)" uu____4784 uu____4785)))
end
| uu____4786 -> begin
((solve g FStar_Syntax_Util.exp_unit);
dismiss;
)
end))
end
| (hd2, uu____4789) -> begin
(

let uu____4806 = (FStar_Syntax_Print.term_to_string t)
in (fail1 "trefl: not an equality (%s)" uu____4806))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
(fail "not an irrelevant goal")
end))))


let dup : Prims.unit tac = (bind cur_goal (fun g -> (

let uu____4814 = (new_uvar g.context g.goal_ty)
in (bind uu____4814 (fun u -> (

let g' = (

let uu___122_4821 = g
in {context = uu___122_4821.context; witness = u; goal_ty = uu___122_4821.goal_ty; opts = uu___122_4821.opts; is_guard = uu___122_4821.is_guard})
in (bind dismiss (fun uu____4824 -> (

let uu____4825 = (

let uu____4828 = (

let uu____4829 = (FStar_TypeChecker_TcTerm.universe_of g.context g.goal_ty)
in (FStar_Syntax_Util.mk_eq2 uu____4829 g.goal_ty u g.witness))
in (add_irrelevant_goal g.context uu____4828 g.opts))
in (bind uu____4825 (fun uu____4832 -> (

let uu____4833 = (add_goals ((g')::[]))
in (bind uu____4833 (fun uu____4837 -> (ret ())))))))))))))))


let flip : Prims.unit tac = (bind get (fun ps -> (match (ps.goals) with
| (g1)::(g2)::gs -> begin
(set (

let uu___123_4854 = ps
in {main_context = uu___123_4854.main_context; main_goal = uu___123_4854.main_goal; all_implicits = uu___123_4854.all_implicits; goals = (g2)::(g1)::gs; smt_goals = uu___123_4854.smt_goals}))
end
| uu____4855 -> begin
(fail "flip: less than 2 goals")
end)))


let later : Prims.unit tac = (bind get (fun ps -> (match (ps.goals) with
| [] -> begin
(ret ())
end
| (g)::gs -> begin
(set (

let uu___124_4870 = ps
in {main_context = uu___124_4870.main_context; main_goal = uu___124_4870.main_goal; all_implicits = uu___124_4870.all_implicits; goals = (FStar_List.append gs ((g)::[])); smt_goals = uu___124_4870.smt_goals}))
end)))


let qed : Prims.unit tac = (bind get (fun ps -> (match (ps.goals) with
| [] -> begin
(ret ())
end
| uu____4877 -> begin
(fail "Not done!")
end)))


let cases : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac = (fun t -> (bind cur_goal (fun g -> (

let uu____4919 = (g.context.FStar_TypeChecker_Env.type_of g.context t)
in (match (uu____4919) with
| (t1, typ, guard) -> begin
(

let uu____4935 = (FStar_Syntax_Util.head_and_args typ)
in (match (uu____4935) with
| (hd1, args) -> begin
(

let uu____4978 = (

let uu____4991 = (

let uu____4992 = (FStar_Syntax_Util.un_uinst hd1)
in uu____4992.FStar_Syntax_Syntax.n)
in ((uu____4991), (args)))
in (match (uu____4978) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____5011))::((q, uu____5013))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid) -> begin
(

let v_p = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p)
in (

let v_q = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None q)
in (

let g1 = (

let uu___125_5051 = g
in (

let uu____5052 = (FStar_TypeChecker_Env.push_bv g.context v_p)
in {context = uu____5052; witness = uu___125_5051.witness; goal_ty = uu___125_5051.goal_ty; opts = uu___125_5051.opts; is_guard = uu___125_5051.is_guard}))
in (

let g2 = (

let uu___126_5054 = g
in (

let uu____5055 = (FStar_TypeChecker_Env.push_bv g.context v_q)
in {context = uu____5055; witness = uu___126_5054.witness; goal_ty = uu___126_5054.goal_ty; opts = uu___126_5054.opts; is_guard = uu___126_5054.is_guard}))
in (bind dismiss (fun uu____5062 -> (

let uu____5063 = (add_goals ((g1)::(g2)::[]))
in (bind uu____5063 (fun uu____5072 -> (

let uu____5073 = (

let uu____5078 = (FStar_Syntax_Syntax.bv_to_name v_p)
in (

let uu____5079 = (FStar_Syntax_Syntax.bv_to_name v_q)
in ((uu____5078), (uu____5079))))
in (ret uu____5073)))))))))))
end
| uu____5084 -> begin
(

let uu____5097 = (FStar_Syntax_Print.term_to_string typ)
in (fail1 "Not a disjunction: %s" uu____5097))
end))
end))
end)))))


let set_options : Prims.string  ->  Prims.unit tac = (fun s -> (bind cur_goal (fun g -> ((FStar_Options.push ());
(

let uu____5120 = (FStar_Util.smap_copy g.opts)
in (FStar_Options.set uu____5120));
(

let res = (FStar_Options.set_options FStar_Options.Set s)
in (

let opts' = (FStar_Options.peek ())
in ((FStar_Options.pop ());
(match (res) with
| FStar_Getopt.Success -> begin
(

let g' = (

let uu___127_5127 = g
in {context = uu___127_5127.context; witness = uu___127_5127.witness; goal_ty = uu___127_5127.goal_ty; opts = opts'; is_guard = uu___127_5127.is_guard})
in (replace_cur g'))
end
| FStar_Getopt.Error (err1) -> begin
(fail2 "Setting options `%s` failed: %s" s err1)
end
| FStar_Getopt.Help -> begin
(fail1 "Setting options `%s` failed (got `Help`?)" s)
end);
)));
))))


let cur_env : env tac = (bind cur_goal (fun g -> (FStar_All.pipe_left ret g.context)))


let cur_goal' : FStar_Syntax_Syntax.typ tac = (bind cur_goal (fun g -> (FStar_All.pipe_left ret g.goal_ty)))


let cur_witness : FStar_Syntax_Syntax.term tac = (bind cur_goal (fun g -> (FStar_All.pipe_left ret g.witness)))


let unquote : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun ty tm -> (bind cur_goal (fun goal -> (

let env = (FStar_TypeChecker_Env.set_expected_typ goal.context ty)
in (

let uu____5168 = (goal.context.FStar_TypeChecker_Env.type_of env tm)
in (match (uu____5168) with
| (tm1, typ, guard) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env guard);
(ret tm1);
)
end))))))


let uvar_env : env  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term tac = (fun env ty -> (

let uu____5197 = (match (ty) with
| FStar_Pervasives_Native.Some (ty1) -> begin
(ret ty1)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5203 = (

let uu____5204 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5204))
in (new_uvar env uu____5203))
end)
in (bind uu____5197 (fun typ -> (

let uu____5216 = (new_uvar env typ)
in (bind uu____5216 (fun t -> (ret t))))))))


let unify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun t1 t2 -> (bind get (fun ps -> (

let uu____5236 = (do_unify ps.main_context t1 t2)
in (ret uu____5236)))))


let launch_process : Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string tac = (fun prog args input -> (bind idtac (fun uu____5256 -> (

let uu____5257 = (FStar_Options.unsafe_tactic_exec ())
in (match (uu____5257) with
| true -> begin
(

let s = (FStar_Util.launch_process true "tactic_launch" prog args input (fun uu____5263 uu____5264 -> false))
in (ret s))
end
| uu____5265 -> begin
(fail "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
end)))))


let goal_of_goal_ty : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (goal * FStar_TypeChecker_Env.guard_t) = (fun env typ -> (

let uu____5286 = (FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty" typ.FStar_Syntax_Syntax.pos env typ)
in (match (uu____5286) with
| (u, uu____5304, g_u) -> begin
(

let g = (

let uu____5319 = (FStar_Options.peek ())
in {context = env; witness = u; goal_ty = typ; opts = uu____5319; is_guard = false})
in ((g), (g_u)))
end)))


let proofstate_of_goal_ty : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (proofstate * FStar_Syntax_Syntax.term) = (fun env typ -> (

let uu____5336 = (goal_of_goal_ty env typ)
in (match (uu____5336) with
| (g, g_u) -> begin
(

let ps = {main_context = env; main_goal = g; all_implicits = g_u.FStar_TypeChecker_Env.implicits; goals = (g)::[]; smt_goals = []}
in ((ps), (g.witness)))
end)))




