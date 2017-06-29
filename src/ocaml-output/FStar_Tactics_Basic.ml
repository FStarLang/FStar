
open Prims
open FStar_Pervasives

type name =
FStar_Syntax_Syntax.bv


type env =
FStar_TypeChecker_Env.env


type implicits =
FStar_TypeChecker_Env.implicits


let bnorm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e t -> (FStar_TypeChecker_Normalize.normalize [] e t))

type goal =
{context : env; witness : FStar_Syntax_Syntax.term; goal_ty : FStar_Syntax_Syntax.typ; opts : FStar_Options.optionstate}


let __proj__Mkgoal__item__context : goal  ->  env = (fun projectee -> (match (projectee) with
| {context = __fname__context; witness = __fname__witness; goal_ty = __fname__goal_ty; opts = __fname__opts} -> begin
__fname__context
end))


let __proj__Mkgoal__item__witness : goal  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {context = __fname__context; witness = __fname__witness; goal_ty = __fname__goal_ty; opts = __fname__opts} -> begin
__fname__witness
end))


let __proj__Mkgoal__item__goal_ty : goal  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| {context = __fname__context; witness = __fname__witness; goal_ty = __fname__goal_ty; opts = __fname__opts} -> begin
__fname__goal_ty
end))


let __proj__Mkgoal__item__opts : goal  ->  FStar_Options.optionstate = (fun projectee -> (match (projectee) with
| {context = __fname__context; witness = __fname__witness; goal_ty = __fname__goal_ty; opts = __fname__opts} -> begin
__fname__opts
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


let uu___is_Success = (fun projectee -> (match (projectee) with
| Success (_0) -> begin
true
end
| uu____169 -> begin
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
| uu____204 -> begin
false
end))


let __proj__Failed__item___0 = (fun projectee -> (match (projectee) with
| Failed (_0) -> begin
_0
end))

exception TacFailure of (Prims.string)


let uu___is_TacFailure : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TacFailure (uu____232) -> begin
true
end
| uu____233 -> begin
false
end))


let __proj__TacFailure__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| TacFailure (uu____241) -> begin
uu____241
end))

type 'a tac =
{tac_f : proofstate  ->  'a result}


let __proj__Mktac__item__tac_f = (fun projectee -> (match (projectee) with
| {tac_f = __fname__tac_f} -> begin
__fname__tac_f
end))


let mk_tac = (fun f -> {tac_f = f})


let run = (fun t p -> (t.tac_f p))


let ret = (fun x -> (mk_tac (fun p -> Success (((x), (p))))))


let bind = (fun t1 t2 -> (mk_tac (fun p -> (

let uu____354 = (run t1 p)
in (match (uu____354) with
| Success (a, q) -> begin
(

let uu____359 = (t2 a)
in (run uu____359 q))
end
| Failed (msg, q) -> begin
Failed (((msg), (q)))
end)))))


let idtac : Prims.unit tac = (ret ())


let goal_to_string : goal  ->  Prims.string = (fun g -> (

let g_binders = (

let uu____369 = (FStar_TypeChecker_Env.all_binders g.context)
in (FStar_All.pipe_right uu____369 (FStar_Syntax_Print.binders_to_string ", ")))
in (

let uu____370 = (FStar_Syntax_Print.term_to_string g.witness)
in (

let uu____371 = (FStar_Syntax_Print.term_to_string g.goal_ty)
in (FStar_Util.format3 "%s |- %s : %s" g_binders uu____370 uu____371)))))


let tacprint : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "TAC>> %s\n" s))


let tacprint1 : Prims.string  ->  Prims.string  ->  Prims.unit = (fun s x -> (

let uu____384 = (FStar_Util.format1 s x)
in (FStar_Util.print1 "TAC>> %s\n" uu____384)))


let tacprint2 : Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.unit = (fun s x y -> (

let uu____397 = (FStar_Util.format2 s x y)
in (FStar_Util.print1 "TAC>> %s\n" uu____397)))


let tacprint3 : Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.unit = (fun s x y z -> (

let uu____414 = (FStar_Util.format3 s x y z)
in (FStar_Util.print1 "TAC>> %s\n" uu____414)))


let comp_to_typ : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____420) -> begin
t
end
| FStar_Syntax_Syntax.GTotal (t, uu____428) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let is_irrelevant : goal  ->  Prims.bool = (fun g -> (

let uu____440 = (

let uu____444 = (FStar_TypeChecker_Normalize.unfold_whnf g.context g.goal_ty)
in (FStar_Syntax_Util.un_squash uu____444))
in (match (uu____440) with
| FStar_Pervasives_Native.Some (t) -> begin
true
end
| uu____450 -> begin
false
end)))


let dump_goal = (fun ps goal -> (

let uu____470 = (goal_to_string goal)
in (tacprint uu____470)))


let dump_cur : proofstate  ->  Prims.string  ->  Prims.unit = (fun ps msg -> (match (ps.goals) with
| [] -> begin
(tacprint1 "No more goals (%s)" msg)
end
| (h)::uu____480 -> begin
((tacprint1 "Current goal (%s):" msg);
(

let uu____483 = (FStar_List.hd ps.goals)
in (dump_goal ps uu____483));
)
end))


let dump_proofstate : proofstate  ->  Prims.string  ->  Prims.unit = (fun ps msg -> ((tacprint "");
(tacprint1 "State dump (%s):" msg);
(

let uu____495 = (FStar_Util.string_of_int (FStar_List.length ps.goals))
in (tacprint1 "ACTIVE goals (%s):" uu____495));
(FStar_List.iter (dump_goal ps) ps.goals);
(

let uu____504 = (FStar_Util.string_of_int (FStar_List.length ps.smt_goals))
in (tacprint1 "SMT goals (%s):" uu____504));
(FStar_List.iter (dump_goal ps) ps.smt_goals);
))


let print_proof_state1 : Prims.string  ->  Prims.unit tac = (fun msg -> (mk_tac (fun p -> ((dump_cur p msg);
Success (((()), (p)));
))))


let print_proof_state : Prims.string  ->  Prims.unit tac = (fun msg -> (mk_tac (fun p -> ((dump_proofstate p msg);
Success (((()), (p)));
))))


let get : proofstate tac = (mk_tac (fun p -> Success (((p), (p)))))


let tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let rec log : proofstate  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun ps f -> (

let uu____553 = (FStar_ST.read tac_verb_dbg)
in (match (uu____553) with
| FStar_Pervasives_Native.None -> begin
((

let uu____559 = (

let uu____561 = (FStar_TypeChecker_Env.debug ps.main_context (FStar_Options.Other ("TacVerbose")))
in FStar_Pervasives_Native.Some (uu____561))
in (FStar_ST.write tac_verb_dbg uu____559));
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


let fail = (fun msg -> (mk_tac (fun ps -> ((

let uu____594 = (FStar_TypeChecker_Env.debug ps.main_context (FStar_Options.Other ("TacFail")))
in (match (uu____594) with
| true -> begin
(dump_proofstate ps (Prims.strcat "TACTING FAILING: " msg))
end
| uu____595 -> begin
()
end));
Failed (((msg), (ps)));
))))


let fail1 = (fun msg x -> (

let uu____612 = (FStar_Util.format1 msg x)
in (fail uu____612)))


let fail2 = (fun msg x y -> (

let uu____635 = (FStar_Util.format2 msg x y)
in (fail uu____635)))


let fail3 = (fun msg x y z -> (

let uu____664 = (FStar_Util.format3 msg x y z)
in (fail uu____664)))


let trytac = (fun t -> (mk_tac (fun ps -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____687 = (run t ps)
in (match (uu____687) with
| Success (a, q) -> begin
((FStar_Syntax_Unionfind.commit tx);
Success (((FStar_Pervasives_Native.Some (a)), (q)));
)
end
| Failed (uu____696, uu____697) -> begin
((FStar_Syntax_Unionfind.rollback tx);
Success (((FStar_Pervasives_Native.None), (ps)));
)
end))))))


let set : proofstate  ->  Prims.unit tac = (fun p -> (mk_tac (fun uu____708 -> Success (((()), (p))))))


let solve : goal  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun goal solution -> (

let uu____717 = (FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution)
in (match (uu____717) with
| true -> begin
()
end
| uu____718 -> begin
(

let uu____719 = (

let uu____720 = (

let uu____721 = (FStar_Syntax_Print.term_to_string solution)
in (

let uu____722 = (FStar_Syntax_Print.term_to_string goal.witness)
in (

let uu____723 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (FStar_Util.format3 "%s does not solve %s : %s" uu____721 uu____722 uu____723))))
in TacFailure (uu____720))
in (FStar_Pervasives.raise uu____719))
end)))


let dismiss : Prims.unit tac = (bind get (fun p -> (

let uu____728 = (

let uu___82_729 = p
in (

let uu____730 = (FStar_List.tl p.goals)
in {main_context = uu___82_729.main_context; main_goal = uu___82_729.main_goal; all_implicits = uu___82_729.all_implicits; goals = uu____730; smt_goals = uu___82_729.smt_goals}))
in (set uu____728))))


let dismiss_all : Prims.unit tac = (bind get (fun p -> (set (

let uu___83_737 = p
in {main_context = uu___83_737.main_context; main_goal = uu___83_737.main_goal; all_implicits = uu___83_737.all_implicits; goals = []; smt_goals = uu___83_737.smt_goals}))))


let add_goals : goal Prims.list  ->  Prims.unit tac = (fun gs -> (bind get (fun p -> (set (

let uu___84_750 = p
in {main_context = uu___84_750.main_context; main_goal = uu___84_750.main_goal; all_implicits = uu___84_750.all_implicits; goals = (FStar_List.append gs p.goals); smt_goals = uu___84_750.smt_goals})))))


let add_smt_goals : goal Prims.list  ->  Prims.unit tac = (fun gs -> (bind get (fun p -> (set (

let uu___85_763 = p
in {main_context = uu___85_763.main_context; main_goal = uu___85_763.main_goal; all_implicits = uu___85_763.all_implicits; goals = uu___85_763.goals; smt_goals = (FStar_List.append gs p.smt_goals)})))))


let push_goals : goal Prims.list  ->  Prims.unit tac = (fun gs -> (bind get (fun p -> (set (

let uu___86_776 = p
in {main_context = uu___86_776.main_context; main_goal = uu___86_776.main_goal; all_implicits = uu___86_776.all_implicits; goals = (FStar_List.append p.goals gs); smt_goals = uu___86_776.smt_goals})))))


let push_smt_goals : goal Prims.list  ->  Prims.unit tac = (fun gs -> (bind get (fun p -> (set (

let uu___87_789 = p
in {main_context = uu___87_789.main_context; main_goal = uu___87_789.main_goal; all_implicits = uu___87_789.all_implicits; goals = uu___87_789.goals; smt_goals = (FStar_List.append p.smt_goals gs)})))))


let replace_cur : goal  ->  Prims.unit tac = (fun g -> (bind dismiss (fun uu____797 -> (add_goals ((g)::[])))))


let add_implicits : implicits  ->  Prims.unit tac = (fun i -> (bind get (fun p -> (set (

let uu___88_808 = p
in {main_context = uu___88_808.main_context; main_goal = uu___88_808.main_goal; all_implicits = (FStar_List.append i p.all_implicits); goals = uu___88_808.goals; smt_goals = uu___88_808.smt_goals})))))


let new_uvar : env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) tac = (fun env typ -> (

let uu____829 = (FStar_TypeChecker_Util.new_implicit_var "tactics.new_uvar" typ.FStar_Syntax_Syntax.pos env typ)
in (match (uu____829) with
| (u, uu____840, g_u) -> begin
(

let uu____848 = (add_implicits g_u.FStar_TypeChecker_Env.implicits)
in (bind uu____848 (fun uu____853 -> (ret ((u), (g_u))))))
end)))


let is_true : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____860 = (FStar_Syntax_Util.un_squash t)
in (match (uu____860) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____869 = (

let uu____870 = (FStar_Syntax_Subst.compress t')
in uu____870.FStar_Syntax_Syntax.n)
in (match (uu____869) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)
end
| uu____874 -> begin
false
end))
end
| uu____875 -> begin
false
end)))


let is_false : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____883 = (FStar_Syntax_Util.un_squash t)
in (match (uu____883) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____892 = (

let uu____893 = (FStar_Syntax_Subst.compress t')
in uu____893.FStar_Syntax_Syntax.n)
in (match (uu____892) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid)
end
| uu____897 -> begin
false
end))
end
| uu____898 -> begin
false
end)))


let cur_goal : goal tac = (bind get (fun p -> (match (p.goals) with
| [] -> begin
(fail "No more goals (1)")
end
| (hd1)::tl1 -> begin
(ret hd1)
end)))


let add_irrelevant_goal : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Options.optionstate  ->  Prims.unit tac = (fun env phi opts -> (

let typ = (FStar_Syntax_Util.mk_squash phi)
in (

let uu____926 = (new_uvar env typ)
in (bind uu____926 (fun uu____936 -> (match (uu____936) with
| (u, g_u) -> begin
(

let goal = {context = env; witness = u; goal_ty = typ; opts = opts}
in (add_goals ((goal)::[])))
end))))))


let smt : Prims.unit tac = (bind cur_goal (fun g -> (

let uu____947 = (is_irrelevant g)
in (match (uu____947) with
| true -> begin
(bind dismiss (fun uu____950 -> (add_smt_goals ((g)::[]))))
end
| uu____951 -> begin
(

let uu____952 = (FStar_Syntax_Print.term_to_string g.goal_ty)
in (fail1 "goal is not irrelevant: cannot dispatch to smt (%s)" uu____952))
end))))


let divide = (fun n1 l r -> (bind get (fun p -> (

let uu____989 = try
(match (()) with
| () -> begin
(

let uu____1008 = (FStar_List.splitAt n1 p.goals)
in (ret uu____1008))
end)
with
| uu____1025 -> begin
(fail "divide: not enough goals")
end
in (bind uu____989 (fun uu____1042 -> (match (uu____1042) with
| (lgs, rgs) -> begin
(

let lp = (

let uu___89_1057 = p
in {main_context = uu___89_1057.main_context; main_goal = uu___89_1057.main_goal; all_implicits = uu___89_1057.all_implicits; goals = lgs; smt_goals = []})
in (

let rp = (

let uu___90_1059 = p
in {main_context = uu___90_1059.main_context; main_goal = uu___90_1059.main_goal; all_implicits = uu___90_1059.all_implicits; goals = rgs; smt_goals = []})
in (

let uu____1060 = (set lp)
in (bind uu____1060 (fun uu____1065 -> (bind l (fun a -> (bind get (fun lp' -> (

let uu____1075 = (set rp)
in (bind uu____1075 (fun uu____1080 -> (bind r (fun b -> (bind get (fun rp' -> (

let p' = (

let uu___91_1092 = p
in {main_context = uu___91_1092.main_context; main_goal = uu___91_1092.main_goal; all_implicits = uu___91_1092.all_implicits; goals = (FStar_List.append lp'.goals rp'.goals); smt_goals = (FStar_List.append lp'.smt_goals (FStar_List.append rp'.smt_goals p.smt_goals))})
in (

let uu____1093 = (set p')
in (bind uu____1093 (fun uu____1098 -> (ret ((a), (b)))))))))))))))))))))))
end)))))))


let focus = (fun f -> (

let uu____1113 = (divide (Prims.parse_int "1") f idtac)
in (bind uu____1113 (fun uu____1121 -> (match (uu____1121) with
| (a, ()) -> begin
(ret a)
end)))))


let rec map = (fun tau -> (bind get (fun p -> (match (p.goals) with
| [] -> begin
(ret [])
end
| (uu____1145)::uu____1146 -> begin
(

let uu____1148 = (

let uu____1153 = (map tau)
in (divide (Prims.parse_int "1") tau uu____1153))
in (bind uu____1148 (fun uu____1164 -> (match (uu____1164) with
| (h, t) -> begin
(ret ((h)::t))
end))))
end))))


let seq : Prims.unit tac  ->  Prims.unit tac  ->  Prims.unit tac = (fun t1 t2 -> (

let uu____1189 = (bind t1 (fun uu____1193 -> (

let uu____1194 = (map t2)
in (bind uu____1194 (fun uu____1199 -> (ret ()))))))
in (focus uu____1189)))


let intro : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) tac = (bind cur_goal (fun goal -> (

let uu____1216 = (FStar_Syntax_Util.arrow_one goal.goal_ty)
in (match (uu____1216) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____1227 = (FStar_Syntax_Subst.open_comp ((b)::[]) c)
in (match (uu____1227) with
| (bs, c1) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____1247 -> begin
(failwith "impossible: open_comp returned different amount of binders")
end)
in (

let uu____1250 = (

let uu____1251 = (FStar_Syntax_Util.is_total_comp c1)
in (not (uu____1251)))
in (match (uu____1250) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____1257 -> begin
(

let env' = (FStar_TypeChecker_Env.push_binders goal.context ((b1)::[]))
in (

let typ' = (comp_to_typ c1)
in (

let uu____1264 = (new_uvar env' typ')
in (bind uu____1264 (fun uu____1277 -> (match (uu____1277) with
| (u, g) -> begin
(

let uu____1285 = (

let uu____1286 = (FStar_Syntax_Util.abs ((b1)::[]) u FStar_Pervasives_Native.None)
in (FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness uu____1286))
in (match (uu____1285) with
| true -> begin
(

let uu____1294 = (

let uu____1296 = (

let uu___94_1297 = goal
in (

let uu____1298 = (bnorm env' u)
in (

let uu____1299 = (bnorm env' typ')
in {context = env'; witness = uu____1298; goal_ty = uu____1299; opts = uu___94_1297.opts})))
in (replace_cur uu____1296))
in (bind uu____1294 (fun uu____1303 -> (ret b1))))
end
| uu____1306 -> begin
(fail "intro: unification failed")
end))
end))))))
end)))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1311 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (fail1 "intro: goal is not an arrow (%s)" uu____1311))
end))))


let norm : FStar_Reflection_Data.norm_step Prims.list  ->  Prims.unit tac = (fun s -> (bind cur_goal (fun goal -> (

let tr = (fun s1 -> (match (s1) with
| FStar_Reflection_Data.Simpl -> begin
(FStar_TypeChecker_Normalize.Simplify)::[]
end
| FStar_Reflection_Data.WHNF -> begin
(FStar_TypeChecker_Normalize.WHNF)::[]
end
| FStar_Reflection_Data.Primops -> begin
(FStar_TypeChecker_Normalize.Primops)::[]
end
| FStar_Reflection_Data.Delta -> begin
(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]
end))
in (

let steps = (

let uu____1336 = (

let uu____1338 = (FStar_List.map tr s)
in (FStar_List.flatten uu____1338))
in (FStar_List.append ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldTac)::[]) uu____1336))
in (

let w = (FStar_TypeChecker_Normalize.normalize steps goal.context goal.witness)
in (

let t = (FStar_TypeChecker_Normalize.normalize steps goal.context goal.goal_ty)
in (replace_cur (

let uu___95_1346 = goal
in {context = uu___95_1346.context; witness = w; goal_ty = t; opts = uu___95_1346.opts})))))))))


let istrivial : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e t -> (

let steps = (FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.UnfoldTac)::[]
in (

let t1 = (FStar_TypeChecker_Normalize.normalize steps e t)
in (is_true t1))))


let trivial : Prims.unit tac = (bind cur_goal (fun goal -> (

let uu____1363 = (istrivial goal.context goal.goal_ty)
in (match (uu____1363) with
| true -> begin
((solve goal FStar_Syntax_Util.exp_unit);
dismiss;
)
end
| uu____1366 -> begin
(

let uu____1367 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (fail1 "Not a trivial goal: %s" uu____1367))
end))))


let exact : FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun t -> (bind cur_goal (fun goal -> (

let uu____1377 = try
(match (()) with
| () -> begin
(

let uu____1393 = (goal.context.FStar_TypeChecker_Env.type_of goal.context t)
in (ret uu____1393))
end)
with
| e -> begin
(

let uu____1410 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1411 = (FStar_Syntax_Print.tag_of_term t)
in (fail2 "exact: term is not typeable: %s (%s)" uu____1410 uu____1411)))
end
in (bind uu____1377 (fun uu____1423 -> (match (uu____1423) with
| (t1, typ, guard) -> begin
(

let uu____1431 = (

let uu____1432 = (

let uu____1433 = (FStar_TypeChecker_Rel.discharge_guard goal.context guard)
in (FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1433))
in (not (uu____1432)))
in (match (uu____1431) with
| true -> begin
(fail "exact: got non-trivial guard")
end
| uu____1435 -> begin
(

let uu____1436 = (FStar_TypeChecker_Rel.teq_nosmt goal.context typ goal.goal_ty)
in (match (uu____1436) with
| true -> begin
((solve goal t1);
dismiss;
)
end
| uu____1439 -> begin
(

let uu____1440 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1441 = (

let uu____1442 = (bnorm goal.context typ)
in (FStar_Syntax_Print.term_to_string uu____1442))
in (

let uu____1443 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (fail3 "%s : %s does not exactly solve the goal %s" uu____1440 uu____1441 uu____1443))))
end))
end))
end)))))))


let exact_lemma : FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun t -> (bind cur_goal (fun goal -> (

let uu____1453 = try
(match (()) with
| () -> begin
(

let uu____1469 = (FStar_TypeChecker_TcTerm.tc_term goal.context t)
in (ret uu____1469))
end)
with
| e -> begin
(

let uu____1486 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____1487 = (FStar_Syntax_Print.tag_of_term t)
in (fail2 "exact_lemma: term is not typeable: %s (%s)" uu____1486 uu____1487)))
end
in (bind uu____1453 (fun uu____1499 -> (match (uu____1499) with
| (t1, lcomp, guard) -> begin
(

let comp = (lcomp.FStar_Syntax_Syntax.comp ())
in (match ((not ((FStar_Syntax_Util.is_lemma_comp comp)))) with
| true -> begin
(fail "exact_lemma: not a lemma")
end
| uu____1511 -> begin
(

let uu____1512 = (

let uu____1513 = (FStar_TypeChecker_Rel.is_trivial guard)
in (not (uu____1513)))
in (match (uu____1512) with
| true -> begin
(fail "exact: got non-trivial guard")
end
| uu____1515 -> begin
(

let uu____1516 = (

let uu____1523 = (

let uu____1529 = (FStar_Syntax_Util.comp_to_comp_typ comp)
in uu____1529.FStar_Syntax_Syntax.effect_args)
in (match (uu____1523) with
| (pre)::(post)::uu____1538 -> begin
(((FStar_Pervasives_Native.fst pre)), ((FStar_Pervasives_Native.fst post)))
end
| uu____1568 -> begin
(failwith "exact_lemma: impossible: not a lemma")
end))
in (match (uu____1516) with
| (pre, post) -> begin
(

let uu____1591 = (FStar_TypeChecker_Rel.teq_nosmt goal.context post goal.goal_ty)
in (match (uu____1591) with
| true -> begin
((solve goal t1);
(bind dismiss (fun uu____1595 -> (add_irrelevant_goal goal.context pre goal.opts)));
)
end
| uu____1596 -> begin
(

let uu____1597 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1598 = (FStar_Syntax_Print.term_to_string post)
in (

let uu____1599 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (fail3 "%s : %s does not exactly solve the goal %s" uu____1597 uu____1598 uu____1599))))
end))
end))
end))
end))
end)))))))


let uvar_free_in_goal : FStar_Syntax_Syntax.uvar  ->  goal  ->  Prims.bool = (fun u g -> (

let free_uvars = (

let uu____1610 = (

let uu____1614 = (FStar_Syntax_Free.uvars g.goal_ty)
in (FStar_Util.set_elements uu____1614))
in (FStar_List.map FStar_Pervasives_Native.fst uu____1610))
in (FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)))


let uvar_free : FStar_Syntax_Syntax.uvar  ->  proofstate  ->  Prims.bool = (fun u ps -> (FStar_List.existsML (uvar_free_in_goal u) ps.goals))


let rec __apply : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun uopt tm -> (bind cur_goal (fun goal -> (

let uu____1643 = (

let uu____1646 = (exact tm)
in (trytac uu____1646))
in (bind uu____1643 (fun r -> (match (r) with
| FStar_Pervasives_Native.Some (r1) -> begin
(ret ())
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1655 = (goal.context.FStar_TypeChecker_Env.type_of goal.context tm)
in (match (uu____1655) with
| (tm1, typ, guard) -> begin
(

let uu____1663 = (

let uu____1664 = (

let uu____1665 = (FStar_TypeChecker_Rel.discharge_guard goal.context guard)
in (FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1665))
in (not (uu____1664)))
in (match (uu____1663) with
| true -> begin
(fail "apply: got non-trivial guard")
end
| uu____1667 -> begin
(

let uu____1668 = (FStar_Syntax_Util.arrow_one typ)
in (match (uu____1668) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1675 = (FStar_Syntax_Print.term_to_string typ)
in (fail1 "apply: cannot unify (%s)" uu____1675))
end
| FStar_Pervasives_Native.Some ((bv, aq), c) -> begin
(

let uu____1685 = (

let uu____1686 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____1686)))
in (match (uu____1685) with
| true -> begin
(fail "apply: not total")
end
| uu____1688 -> begin
(

let uu____1689 = (new_uvar goal.context bv.FStar_Syntax_Syntax.sort)
in (bind uu____1689 (fun uu____1700 -> (match (uu____1700) with
| (u, g_u) -> begin
(

let tm' = (FStar_Syntax_Syntax.mk_Tm_app tm1 ((((u), (aq)))::[]) FStar_Pervasives_Native.None goal.context.FStar_TypeChecker_Env.range)
in (

let uu____1715 = (__apply uopt tm')
in (bind uu____1715 (fun uu____1721 -> (

let uu____1722 = (

let uu____1723 = (

let uu____1726 = (

let uu____1727 = (FStar_Syntax_Util.head_and_args u)
in (FStar_Pervasives_Native.fst uu____1727))
in (FStar_Syntax_Subst.compress uu____1726))
in uu____1723.FStar_Syntax_Syntax.n)
in (match (uu____1722) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____1746) -> begin
(bind get (fun ps -> (

let uu____1766 = (uopt && (uvar_free uvar ps))
in (match (uu____1766) with
| true -> begin
(ret ())
end
| uu____1768 -> begin
(

let uu____1769 = (

let uu____1771 = (

let uu____1772 = (bnorm goal.context u)
in (

let uu____1773 = (bnorm goal.context bv.FStar_Syntax_Syntax.sort)
in {context = goal.context; witness = uu____1772; goal_ty = uu____1773; opts = goal.opts}))
in (uu____1771)::[])
in (add_goals uu____1769))
end))))
end
| uu____1774 -> begin
(ret ())
end))))))
end))))
end))
end))
end))
end))
end)))))))


let apply : FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun tm -> (

let uu____1781 = (__apply true tm)
in (focus uu____1781)))


let apply_lemma : FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun tm -> (bind cur_goal (fun goal -> (

let uu____1796 = (goal.context.FStar_TypeChecker_Env.type_of goal.context tm)
in (match (uu____1796) with
| (tm1, t, guard) -> begin
(

let uu____1804 = (

let uu____1805 = (

let uu____1806 = (FStar_TypeChecker_Rel.discharge_guard goal.context guard)
in (FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1806))
in (not (uu____1805)))
in (match (uu____1804) with
| true -> begin
(fail "apply_lemma: got non-trivial guard")
end
| uu____1808 -> begin
(

let uu____1809 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____1809) with
| (bs, comp) -> begin
(match ((not ((FStar_Syntax_Util.is_lemma_comp comp)))) with
| true -> begin
(fail "apply_lemma: not a lemma")
end
| uu____1825 -> begin
(

let uu____1826 = (FStar_List.fold_left (fun uu____1856 uu____1857 -> (match (((uu____1856), (uu____1857))) with
| ((uvs, guard1, subst1), (b, aq)) -> begin
(

let b_t = (FStar_Syntax_Subst.subst subst1 b.FStar_Syntax_Syntax.sort)
in (

let uu____1906 = (FStar_TypeChecker_Util.new_implicit_var "apply_lemma" goal.goal_ty.FStar_Syntax_Syntax.pos goal.context b_t)
in (match (uu____1906) with
| (u, uu____1921, g_u) -> begin
(

let uu____1929 = (FStar_TypeChecker_Rel.conj_guard guard1 g_u)
in (((((u), (aq)))::uvs), (uu____1929), ((FStar_Syntax_Syntax.NT (((b), (u))))::subst1)))
end)))
end)) (([]), (guard), ([])) bs)
in (match (uu____1826) with
| (uvs, implicits, subst1) -> begin
(

let uvs1 = (FStar_List.rev uvs)
in (

let comp1 = (FStar_Syntax_Subst.subst_comp subst1 comp)
in (

let uu____1961 = (

let uu____1968 = (

let uu____1974 = (FStar_Syntax_Util.comp_to_comp_typ comp1)
in uu____1974.FStar_Syntax_Syntax.effect_args)
in (match (uu____1968) with
| (pre)::(post)::uu____1983 -> begin
(((FStar_Pervasives_Native.fst pre)), ((FStar_Pervasives_Native.fst post)))
end
| uu____2013 -> begin
(failwith "apply_lemma: impossible: not a lemma")
end))
in (match (uu____1961) with
| (pre, post) -> begin
(

let uu____2036 = (

let uu____2038 = (FStar_Syntax_Util.mk_squash post)
in (FStar_TypeChecker_Rel.try_teq false goal.context uu____2038 goal.goal_ty))
in (match (uu____2036) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2040 = (

let uu____2041 = (FStar_Syntax_Util.mk_squash post)
in (FStar_Syntax_Print.term_to_string uu____2041))
in (

let uu____2042 = (FStar_Syntax_Print.term_to_string goal.goal_ty)
in (fail2 "apply_lemma: does not unify with goal: %s vs %s" uu____2040 uu____2042)))
end
| FStar_Pervasives_Native.Some (g) -> begin
(

let solution = (FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1 FStar_Pervasives_Native.None goal.context.FStar_TypeChecker_Env.range)
in (

let implicits1 = (FStar_All.pipe_right implicits.FStar_TypeChecker_Env.implicits (FStar_List.filter (fun uu____2089 -> (match (uu____2089) with
| (uu____2096, uu____2097, uu____2098, tm2, uu____2100, uu____2101) -> begin
(

let uu____2102 = (FStar_Syntax_Util.head_and_args tm2)
in (match (uu____2102) with
| (hd1, uu____2113) -> begin
(

let uu____2128 = (

let uu____2129 = (FStar_Syntax_Subst.compress hd1)
in uu____2129.FStar_Syntax_Syntax.n)
in (match (uu____2128) with
| FStar_Syntax_Syntax.Tm_uvar (uu____2132) -> begin
true
end
| uu____2143 -> begin
false
end))
end))
end))))
in ((solve goal solution);
(bind dismiss (fun uu____2153 -> (

let is_free_uvar = (fun uv t1 -> (

let free_uvars = (

let uu____2163 = (

let uu____2167 = (FStar_Syntax_Free.uvars t1)
in (FStar_Util.set_elements uu____2167))
in (FStar_List.map FStar_Pervasives_Native.fst uu____2163))
in (FStar_List.existsML (fun u -> (FStar_Syntax_Unionfind.equiv u uv)) free_uvars)))
in (

let appears = (fun uv goals -> (FStar_List.existsML (fun g' -> (is_free_uvar uv g'.goal_ty)) goals))
in (

let checkone = (fun t1 goals -> (

let uu____2197 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____2197) with
| (hd1, uu____2208) -> begin
(match (hd1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____2224) -> begin
(appears uv goals)
end
| uu____2241 -> begin
false
end)
end)))
in (

let sub_goals = (FStar_All.pipe_right implicits1 (FStar_List.map (fun uu____2267 -> (match (uu____2267) with
| (_msg, _env, _uvar, term, typ, uu____2279) -> begin
(

let uu____2280 = (bnorm goal.context term)
in (

let uu____2281 = (bnorm goal.context typ)
in {context = goal.context; witness = uu____2280; goal_ty = uu____2281; opts = goal.opts}))
end))))
in (

let rec filter' = (fun f xs -> (match (xs) with
| [] -> begin
[]
end
| (x)::xs1 -> begin
(

let uu____2313 = (f x xs1)
in (match (uu____2313) with
| true -> begin
(

let uu____2315 = (filter' f xs1)
in (x)::uu____2315)
end
| uu____2317 -> begin
(filter' f xs1)
end))
end))
in (

let sub_goals1 = (filter' (fun g1 goals -> (

let uu____2326 = (checkone g1.witness goals)
in (not (uu____2326)))) sub_goals)
in (

let uu____2327 = (add_irrelevant_goal goal.context pre goal.opts)
in (bind uu____2327 (fun uu____2331 -> (

let uu____2332 = (trytac trivial)
in (bind uu____2332 (fun uu____2338 -> (

let uu____2340 = (add_implicits g.FStar_TypeChecker_Env.implicits)
in (bind uu____2340 (fun uu____2343 -> (add_goals sub_goals1))))))))))))))))));
)))
end))
end))))
end))
end)
end))
end))
end)))))


let rewrite : FStar_Syntax_Syntax.binder  ->  Prims.unit tac = (fun h -> (bind cur_goal (fun goal -> (

let uu____2353 = (FStar_All.pipe_left mlog (fun uu____2361 -> (

let uu____2362 = (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst h))
in (

let uu____2363 = (FStar_Syntax_Print.term_to_string (FStar_Pervasives_Native.fst h).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2362 uu____2363)))))
in (bind uu____2353 (fun uu____2375 -> (

let uu____2376 = (

let uu____2378 = (

let uu____2379 = (FStar_TypeChecker_Env.lookup_bv goal.context (FStar_Pervasives_Native.fst h))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____2379))
in (FStar_Syntax_Util.destruct_typ_as_formula uu____2378))
in (match (uu____2376) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (l, (uu____2386)::((x, uu____2388))::((e, uu____2390))::[])) when (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) -> begin
(

let uu____2424 = (

let uu____2425 = (FStar_Syntax_Subst.compress x)
in uu____2425.FStar_Syntax_Syntax.n)
in (match (uu____2424) with
| FStar_Syntax_Syntax.Tm_name (x1) -> begin
(

let goal1 = (

let uu___100_2431 = goal
in (

let uu____2432 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x1), (e))))::[]) goal.witness)
in (

let uu____2435 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x1), (e))))::[]) goal.goal_ty)
in {context = uu___100_2431.context; witness = uu____2432; goal_ty = uu____2435; opts = uu___100_2431.opts})))
in (replace_cur goal1))
end
| uu____2438 -> begin
(fail "Not an equality hypothesis with a variable on the LHS")
end))
end
| uu____2439 -> begin
(fail "Not an equality hypothesis")
end))))))))


let clear : Prims.unit tac = (bind cur_goal (fun goal -> (

let uu____2445 = (FStar_TypeChecker_Env.pop_bv goal.context)
in (match (uu____2445) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot clear; empty context")
end
| FStar_Pervasives_Native.Some (x, env') -> begin
(

let fns_ty = (FStar_Syntax_Free.names goal.goal_ty)
in (

let fns_tm = (FStar_Syntax_Free.names goal.witness)
in (

let uu____2460 = (FStar_Util.set_mem x fns_ty)
in (match (uu____2460) with
| true -> begin
(fail "Cannot clear; variable appears in goal")
end
| uu____2462 -> begin
(

let uu____2463 = (new_uvar env' goal.goal_ty)
in (bind uu____2463 (fun uu____2473 -> (match (uu____2473) with
| (u, g) -> begin
(

let uu____2479 = (

let uu____2480 = (FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness u)
in (not (uu____2480)))
in (match (uu____2479) with
| true -> begin
(fail "clear: unification failed")
end
| uu____2482 -> begin
(

let new_goal = (

let uu___101_2484 = goal
in (

let uu____2485 = (bnorm env' u)
in {context = env'; witness = uu____2485; goal_ty = uu___101_2484.goal_ty; opts = uu___101_2484.opts}))
in (bind dismiss (fun uu____2487 -> (add_goals ((new_goal)::[])))))
end))
end))))
end))))
end))))


let clear_hd : name  ->  Prims.unit tac = (fun x -> (bind cur_goal (fun goal -> (

let uu____2497 = (FStar_TypeChecker_Env.pop_bv goal.context)
in (match (uu____2497) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot clear_hd; empty context")
end
| FStar_Pervasives_Native.Some (y, env') -> begin
(match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(fail "Cannot clear_hd; head variable mismatch")
end
| uu____2509 -> begin
clear
end)
end)))))


let revert : Prims.unit tac = (bind cur_goal (fun goal -> (

let uu____2514 = (FStar_TypeChecker_Env.pop_bv goal.context)
in (match (uu____2514) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot revert; empty context")
end
| FStar_Pervasives_Native.Some (x, env') -> begin
(

let typ' = (

let uu____2528 = (FStar_Syntax_Syntax.mk_Total goal.goal_ty)
in (FStar_Syntax_Util.arrow ((((x), (FStar_Pervasives_Native.None)))::[]) uu____2528))
in (

let w' = (FStar_Syntax_Util.abs ((((x), (FStar_Pervasives_Native.None)))::[]) goal.witness FStar_Pervasives_Native.None)
in (replace_cur (

let uu___102_2548 = goal
in {context = env'; witness = w'; goal_ty = typ'; opts = uu___102_2548.opts}))))
end))))


let revert_hd : name  ->  Prims.unit tac = (fun x -> (bind cur_goal (fun goal -> (

let uu____2558 = (FStar_TypeChecker_Env.pop_bv goal.context)
in (match (uu____2558) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot revert_hd; empty context")
end
| FStar_Pervasives_Native.Some (y, env') -> begin
(match ((not ((FStar_Syntax_Syntax.bv_eq x y)))) with
| true -> begin
(

let uu____2570 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2571 = (FStar_Syntax_Print.bv_to_string y)
in (fail2 "Cannot revert_hd %s; head variable mismatch ... egot %s" uu____2570 uu____2571)))
end
| uu____2572 -> begin
revert
end)
end)))))


let rec revert_all_hd : name Prims.list  ->  Prims.unit tac = (fun xs -> (match (xs) with
| [] -> begin
(ret ())
end
| (x)::xs1 -> begin
(

let uu____2584 = (revert_all_hd xs1)
in (bind uu____2584 (fun uu____2587 -> (revert_hd x))))
end))


let prune : Prims.string  ->  Prims.unit tac = (fun s -> (bind cur_goal (fun g -> (

let ctx = g.context
in (

let ctx' = (FStar_TypeChecker_Env.rem_proof_ns ctx (FStar_Ident.path_of_text s))
in (

let g' = (

let uu___103_2602 = g
in {context = ctx'; witness = uu___103_2602.witness; goal_ty = uu___103_2602.goal_ty; opts = uu___103_2602.opts})
in (bind dismiss (fun uu____2604 -> (add_goals ((g')::[]))))))))))


let addns : Prims.string  ->  Prims.unit tac = (fun s -> (bind cur_goal (fun g -> (

let ctx = g.context
in (

let ctx' = (FStar_TypeChecker_Env.add_proof_ns ctx (FStar_Ident.path_of_text s))
in (

let g' = (

let uu___104_2619 = g
in {context = ctx'; witness = uu___104_2619.witness; goal_ty = uu___104_2619.goal_ty; opts = uu___104_2619.opts})
in (bind dismiss (fun uu____2621 -> (add_goals ((g')::[]))))))))))


let rec mapM = (fun f l -> (match (l) with
| [] -> begin
(ret [])
end
| (x)::xs -> begin
(

let uu____2655 = (f x)
in (bind uu____2655 (fun y -> (

let uu____2661 = (mapM f xs)
in (bind uu____2661 (fun ys -> (ret ((y)::ys))))))))
end))


let rec tac_bottom_fold_env : (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac)  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun f env t -> (

let tn = (

let uu____2697 = (FStar_Syntax_Subst.compress t)
in uu____2697.FStar_Syntax_Syntax.n)
in (

let tn1 = (match (tn) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let ff = (tac_bottom_fold_env f env)
in (

let uu____2723 = (ff hd1)
in (bind uu____2723 (fun hd2 -> (

let fa = (fun uu____2737 -> (match (uu____2737) with
| (a, q) -> begin
(

let uu____2745 = (ff a)
in (bind uu____2745 (fun a1 -> (ret ((a1), (q))))))
end))
in (

let uu____2753 = (mapM fa args)
in (bind uu____2753 (fun args1 -> (ret (FStar_Syntax_Syntax.Tm_app (((hd2), (args1)))))))))))))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t1, k) -> begin
(

let uu____2788 = (FStar_Syntax_Subst.open_term bs t1)
in (match (uu____2788) with
| (bs1, t') -> begin
(

let uu____2794 = (

let uu____2796 = (FStar_TypeChecker_Env.push_binders env bs1)
in (tac_bottom_fold_env f uu____2796 t'))
in (bind uu____2794 (fun t'' -> (

let uu____2800 = (

let uu____2801 = (

let uu____2811 = (FStar_Syntax_Subst.close_binders bs1)
in (

let uu____2812 = (FStar_Syntax_Subst.close bs1 t'')
in ((uu____2811), (uu____2812), (k))))
in FStar_Syntax_Syntax.Tm_abs (uu____2801))
in (ret uu____2800)))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(ret tn)
end
| uu____2826 -> begin
(ret tn)
end)
in (bind tn1 (fun tn2 -> (f env (

let uu___105_2830 = t
in {FStar_Syntax_Syntax.n = tn2; FStar_Syntax_Syntax.tk = uu___105_2830.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___105_2830.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___105_2830.FStar_Syntax_Syntax.vars})))))))


let pointwise_rec : proofstate  ->  Prims.unit tac  ->  FStar_Options.optionstate  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun ps tau opts env t -> (

let uu____2859 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____2859) with
| (t1, lcomp, g) -> begin
(

let uu____2867 = ((

let uu____2870 = (FStar_Syntax_Util.is_total_lcomp lcomp)
in (not (uu____2870))) || (

let uu____2872 = (FStar_TypeChecker_Rel.is_trivial g)
in (not (uu____2872))))
in (match (uu____2867) with
| true -> begin
(ret t1)
end
| uu____2874 -> begin
(

let typ = lcomp.FStar_Syntax_Syntax.res_typ
in (

let uu____2878 = (new_uvar env typ)
in (bind uu____2878 (fun uu____2889 -> (match (uu____2889) with
| (ut, guard) -> begin
((log ps (fun uu____2899 -> (

let uu____2900 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____2901 = (FStar_Syntax_Print.term_to_string ut)
in (FStar_Util.print2 "Pointwise_rec: making equality %s = %s\n" uu____2900 uu____2901)))));
(

let uu____2902 = (

let uu____2904 = (

let uu____2905 = (FStar_TypeChecker_TcTerm.universe_of env typ)
in (FStar_Syntax_Util.mk_eq2 uu____2905 typ t1 ut))
in (add_irrelevant_goal env uu____2904 opts))
in (bind uu____2902 (fun uu____2908 -> (

let uu____2909 = (bind tau (fun uu____2914 -> ((FStar_TypeChecker_Rel.force_trivial_guard env guard);
(

let ut1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env ut)
in (ret ut1));
)))
in (focus uu____2909)))));
)
end)))))
end))
end)))


let pointwise : Prims.unit tac  ->  Prims.unit tac = (fun tau -> (bind get (fun ps -> (

let uu____2932 = (match (ps.goals) with
| (g)::gs -> begin
((g), (gs))
end
| [] -> begin
(failwith "Pointwise: no goals")
end)
in (match (uu____2932) with
| (g, gs) -> begin
(

let gt1 = g.goal_ty
in ((log ps (fun uu____2955 -> (

let uu____2956 = (FStar_Syntax_Print.term_to_string gt1)
in (FStar_Util.print1 "Pointwise starting with %s\n" uu____2956))));
(bind dismiss_all (fun uu____2959 -> (

let uu____2960 = (tac_bottom_fold_env (pointwise_rec ps tau g.opts) g.context gt1)
in (bind uu____2960 (fun gt' -> ((log ps (fun uu____2969 -> (

let uu____2970 = (FStar_Syntax_Print.term_to_string gt')
in (FStar_Util.print1 "Pointwise seems to have succeded with %s\n" uu____2970))));
(

let uu____2971 = (push_goals gs)
in (bind uu____2971 (fun uu____2974 -> (add_goals (((

let uu___106_2976 = g
in {context = uu___106_2976.context; witness = uu___106_2976.witness; goal_ty = gt'; opts = uu___106_2976.opts}))::[])))));
))))));
))
end)))))


let trefl : Prims.unit tac = (bind cur_goal (fun g -> (

let uu____2995 = (FStar_Syntax_Util.un_squash g.goal_ty)
in (match (uu____2995) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____3005 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____3005) with
| (hd1, args) -> begin
(

let uu____3026 = (

let uu____3034 = (

let uu____3035 = (FStar_Syntax_Util.un_uinst hd1)
in uu____3035.FStar_Syntax_Syntax.n)
in ((uu____3034), (args)))
in (match (uu____3026) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____3045)::((l, uu____3047))::((r, uu____3049))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid) -> begin
(

let uu____3083 = (

let uu____3084 = (FStar_TypeChecker_Rel.teq_nosmt g.context l r)
in (not (uu____3084)))
in (match (uu____3083) with
| true -> begin
(

let uu____3086 = (FStar_Syntax_Print.term_to_string l)
in (

let uu____3087 = (FStar_Syntax_Print.term_to_string r)
in (fail2 "trefl: not a trivial equality (%s vs %s)" uu____3086 uu____3087)))
end
| uu____3088 -> begin
((solve g FStar_Syntax_Util.exp_unit);
dismiss;
)
end))
end
| (hd2, uu____3091) -> begin
(

let uu____3102 = (FStar_Syntax_Print.term_to_string t)
in (fail1 "trefl: not an equality (%s)" uu____3102))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
(fail "not an irrelevant goal")
end))))


let flip : Prims.unit tac = (bind get (fun ps -> (match (ps.goals) with
| (g1)::(g2)::gs -> begin
(set (

let uu___107_3118 = ps
in {main_context = uu___107_3118.main_context; main_goal = uu___107_3118.main_goal; all_implicits = uu___107_3118.all_implicits; goals = (g2)::(g1)::gs; smt_goals = uu___107_3118.smt_goals}))
end
| uu____3119 -> begin
(fail "flip: less than 2 goals")
end)))


let later : Prims.unit tac = (bind get (fun ps -> (match (ps.goals) with
| [] -> begin
(ret ())
end
| (g)::gs -> begin
(set (

let uu___108_3130 = ps
in {main_context = uu___108_3130.main_context; main_goal = uu___108_3130.main_goal; all_implicits = uu___108_3130.all_implicits; goals = (FStar_List.append gs ((g)::[])); smt_goals = uu___108_3130.smt_goals}))
end)))


let qed : Prims.unit tac = (bind get (fun ps -> (match (ps.goals) with
| [] -> begin
(ret ())
end
| uu____3135 -> begin
(fail "Not done!")
end)))


let cases : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac = (fun t -> (bind cur_goal (fun g -> (

let uu____3168 = (g.context.FStar_TypeChecker_Env.type_of g.context t)
in (match (uu____3168) with
| (t1, typ, guard) -> begin
(

let uu____3178 = (FStar_Syntax_Util.head_and_args typ)
in (match (uu____3178) with
| (hd1, args) -> begin
(

let uu____3207 = (

let uu____3215 = (

let uu____3216 = (FStar_Syntax_Util.un_uinst hd1)
in uu____3216.FStar_Syntax_Syntax.n)
in ((uu____3215), (args)))
in (match (uu____3207) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____3229))::((q, uu____3231))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid) -> begin
(

let v_p = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p)
in (

let v_q = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None q)
in (

let g1 = (

let uu___109_3260 = g
in (

let uu____3261 = (FStar_TypeChecker_Env.push_bv g.context v_p)
in {context = uu____3261; witness = uu___109_3260.witness; goal_ty = uu___109_3260.goal_ty; opts = uu___109_3260.opts}))
in (

let g2 = (

let uu___110_3263 = g
in (

let uu____3264 = (FStar_TypeChecker_Env.push_bv g.context v_q)
in {context = uu____3264; witness = uu___110_3263.witness; goal_ty = uu___110_3263.goal_ty; opts = uu___110_3263.opts}))
in (bind dismiss (fun uu____3269 -> (

let uu____3270 = (add_goals ((g1)::(g2)::[]))
in (bind uu____3270 (fun uu____3276 -> (

let uu____3277 = (

let uu____3280 = (FStar_Syntax_Syntax.bv_to_name v_p)
in (

let uu____3281 = (FStar_Syntax_Syntax.bv_to_name v_q)
in ((uu____3280), (uu____3281))))
in (ret uu____3277)))))))))))
end
| uu____3284 -> begin
(

let uu____3292 = (FStar_Syntax_Print.term_to_string typ)
in (fail1 "Not a disjunction: %s" uu____3292))
end))
end))
end)))))


let set_options : Prims.string  ->  Prims.unit tac = (fun s -> (bind cur_goal (fun g -> ((FStar_Options.push ());
(

let uu____3311 = (FStar_Util.smap_copy g.opts)
in (FStar_Options.set uu____3311));
(

let res = (FStar_Options.set_options FStar_Options.Set s)
in (

let opts' = (FStar_Options.peek ())
in ((FStar_Options.pop ());
(match (res) with
| FStar_Getopt.Success -> begin
(

let g' = (

let uu___111_3317 = g
in {context = uu___111_3317.context; witness = uu___111_3317.witness; goal_ty = uu___111_3317.goal_ty; opts = opts'})
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


let proofstate_of_goal_ty : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (proofstate * FStar_Syntax_Syntax.term) = (fun env typ -> (

let uu____3345 = (FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty" typ.FStar_Syntax_Syntax.pos env typ)
in (match (uu____3345) with
| (u, uu____3355, g_u) -> begin
(

let g = (

let uu____3364 = (FStar_Options.peek ())
in {context = env; witness = u; goal_ty = typ; opts = uu____3364})
in (

let ps = {main_context = env; main_goal = g; all_implicits = g_u.FStar_TypeChecker_Env.implicits; goals = (g)::[]; smt_goals = []}
in ((ps), (u))))
end)))




