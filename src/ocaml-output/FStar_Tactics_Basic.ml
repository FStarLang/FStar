
open Prims
open FStar_Pervasives

type goal =
FStar_Tactics_Types.goal


type name =
FStar_Syntax_Syntax.bv


type env =
FStar_TypeChecker_Env.env


type implicits =
FStar_TypeChecker_Env.implicits


let normalize : FStar_TypeChecker_Normalize.step Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (FStar_TypeChecker_Normalize.normalize_with_primitive_steps FStar_Reflection_Interpreter.reflection_primops s e t))


let bnorm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e t -> (normalize [] e t))


let tts : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = FStar_TypeChecker_Normalize.term_to_string

type 'a tac =
{tac_f : FStar_Tactics_Types.proofstate  ->  'a FStar_Tactics_Result.__result}


let __proj__Mktac__item__tac_f : 'a . 'a tac  ->  FStar_Tactics_Types.proofstate  ->  'a FStar_Tactics_Result.__result = (fun projectee -> (match (projectee) with
| {tac_f = __fname__tac_f} -> begin
__fname__tac_f
end))


let mk_tac : 'a . (FStar_Tactics_Types.proofstate  ->  'a FStar_Tactics_Result.__result)  ->  'a tac = (fun f -> {tac_f = f})


let run : 'a . 'a tac  ->  FStar_Tactics_Types.proofstate  ->  'a FStar_Tactics_Result.__result = (fun t p -> (t.tac_f p))


let ret : 'a . 'a  ->  'a tac = (fun x -> (mk_tac (fun p -> FStar_Tactics_Result.Success (((x), (p))))))


let bind : 'a 'b . 'a tac  ->  ('a  ->  'b tac)  ->  'b tac = (fun t1 t2 -> (mk_tac (fun p -> (

let uu____140 = (run t1 p)
in (match (uu____140) with
| FStar_Tactics_Result.Success (a, q) -> begin
(

let uu____147 = (t2 a)
in (run uu____147 q))
end
| FStar_Tactics_Result.Failed (msg, q) -> begin
FStar_Tactics_Result.Failed (((msg), (q)))
end)))))


let idtac : Prims.unit tac = (ret ())


let goal_to_string : FStar_Tactics_Types.goal  ->  Prims.string = (fun g -> (

let g_binders = (

let uu____158 = (FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context)
in (FStar_All.pipe_right uu____158 (FStar_Syntax_Print.binders_to_string ", ")))
in (

let w = (bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness)
in (

let t = (bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (

let uu____161 = (tts g.FStar_Tactics_Types.context w)
in (

let uu____162 = (tts g.FStar_Tactics_Types.context t)
in (FStar_Util.format3 "%s |- %s : %s" g_binders uu____161 uu____162)))))))


let tacprint : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "TAC>> %s\n" s))


let tacprint1 : Prims.string  ->  Prims.string  ->  Prims.unit = (fun s x -> (

let uu____172 = (FStar_Util.format1 s x)
in (FStar_Util.print1 "TAC>> %s\n" uu____172)))


let tacprint2 : Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.unit = (fun s x y -> (

let uu____182 = (FStar_Util.format2 s x y)
in (FStar_Util.print1 "TAC>> %s\n" uu____182)))


let tacprint3 : Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.unit = (fun s x y z -> (

let uu____195 = (FStar_Util.format3 s x y z)
in (FStar_Util.print1 "TAC>> %s\n" uu____195)))


let comp_to_typ : FStar_Syntax_Syntax.comp  ->  FStar_Reflection_Data.typ = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____200) -> begin
t
end
| FStar_Syntax_Syntax.GTotal (t, uu____210) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let is_irrelevant : FStar_Tactics_Types.goal  ->  Prims.bool = (fun g -> (

let uu____223 = (

let uu____228 = (FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (FStar_Syntax_Util.un_squash uu____228))
in (match (uu____223) with
| FStar_Pervasives_Native.Some (t) -> begin
true
end
| uu____234 -> begin
false
end)))


let print : Prims.string  ->  Prims.unit tac = (fun msg -> ((tacprint msg);
(ret ());
))


let dump_goal : 'Auu____250 . 'Auu____250  ->  FStar_Tactics_Types.goal  ->  Prims.unit = (fun ps goal -> (

let uu____260 = (goal_to_string goal)
in (tacprint uu____260)))


let dump_cur : FStar_Tactics_Types.proofstate  ->  Prims.string  ->  Prims.unit = (fun ps msg -> (match (ps.FStar_Tactics_Types.goals) with
| [] -> begin
(tacprint1 "No more goals (%s)" msg)
end
| (h)::uu____268 -> begin
((tacprint1 "Current goal (%s):" msg);
(

let uu____272 = (FStar_List.hd ps.FStar_Tactics_Types.goals)
in (dump_goal ps uu____272));
)
end))


let ps_to_string : (Prims.string * FStar_Tactics_Types.proofstate)  ->  Prims.string = (fun uu____279 -> (match (uu____279) with
| (msg, ps) -> begin
(

let uu____286 = (

let uu____289 = (

let uu____290 = (FStar_Util.string_of_int ps.FStar_Tactics_Types.depth)
in (FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____290 msg))
in (

let uu____291 = (

let uu____294 = (

let uu____295 = (FStar_Range.string_of_range ps.FStar_Tactics_Types.entry_range)
in (FStar_Util.format1 "Location: %s\n" uu____295))
in (

let uu____296 = (

let uu____299 = (

let uu____300 = (FStar_Util.string_of_int (FStar_List.length ps.FStar_Tactics_Types.goals))
in (

let uu____301 = (

let uu____302 = (FStar_List.map goal_to_string ps.FStar_Tactics_Types.goals)
in (FStar_String.concat "\n" uu____302))
in (FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____300 uu____301)))
in (

let uu____305 = (

let uu____308 = (

let uu____309 = (FStar_Util.string_of_int (FStar_List.length ps.FStar_Tactics_Types.smt_goals))
in (

let uu____310 = (

let uu____311 = (FStar_List.map goal_to_string ps.FStar_Tactics_Types.smt_goals)
in (FStar_String.concat "\n" uu____311))
in (FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____309 uu____310)))
in (uu____308)::[])
in (uu____299)::uu____305))
in (uu____294)::uu____296))
in (uu____289)::uu____291))
in (FStar_String.concat "" uu____286))
end))


let goal_to_json : FStar_Tactics_Types.goal  ->  FStar_Util.json = (fun g -> (

let g_binders = (

let uu____318 = (FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context)
in (

let uu____319 = (

let uu____322 = (FStar_TypeChecker_Env.dsenv g.FStar_Tactics_Types.context)
in (FStar_Syntax_Print.binders_to_json uu____322))
in (FStar_All.pipe_right uu____318 uu____319)))
in (

let uu____323 = (

let uu____330 = (

let uu____337 = (

let uu____342 = (

let uu____343 = (

let uu____350 = (

let uu____355 = (

let uu____356 = (tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness)
in FStar_Util.JsonStr (uu____356))
in (("witness"), (uu____355)))
in (

let uu____357 = (

let uu____364 = (

let uu____369 = (

let uu____370 = (tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in FStar_Util.JsonStr (uu____370))
in (("type"), (uu____369)))
in (uu____364)::[])
in (uu____350)::uu____357))
in FStar_Util.JsonAssoc (uu____343))
in (("goal"), (uu____342)))
in (uu____337)::[])
in ((("hyps"), (g_binders)))::uu____330)
in FStar_Util.JsonAssoc (uu____323))))


let ps_to_json : (Prims.string * FStar_Tactics_Types.proofstate)  ->  FStar_Util.json = (fun uu____401 -> (match (uu____401) with
| (msg, ps) -> begin
(

let uu____408 = (

let uu____415 = (

let uu____422 = (

let uu____429 = (

let uu____436 = (

let uu____441 = (

let uu____442 = (FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals)
in FStar_Util.JsonList (uu____442))
in (("goals"), (uu____441)))
in (

let uu____445 = (

let uu____452 = (

let uu____457 = (

let uu____458 = (FStar_List.map goal_to_json ps.FStar_Tactics_Types.smt_goals)
in FStar_Util.JsonList (uu____458))
in (("smt-goals"), (uu____457)))
in (uu____452)::[])
in (uu____436)::uu____445))
in ((("depth"), (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth))))::uu____429)
in ((("label"), (FStar_Util.JsonStr (msg))))::uu____422)
in (

let uu____481 = (match ((Prims.op_disEquality ps.FStar_Tactics_Types.entry_range FStar_Range.dummyRange)) with
| true -> begin
(

let uu____494 = (

let uu____499 = (FStar_Range.json_of_def_range ps.FStar_Tactics_Types.entry_range)
in (("location"), (uu____499)))
in (uu____494)::[])
end
| uu____508 -> begin
[]
end)
in (FStar_List.append uu____415 uu____481)))
in FStar_Util.JsonAssoc (uu____408))
end))


let dump_proofstate : FStar_Tactics_Types.proofstate  ->  Prims.string  ->  Prims.unit = (fun ps msg -> (FStar_Options.with_saved_options (fun uu____525 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(FStar_Util.print_generic "proof-state" ps_to_string ps_to_json ((msg), (ps)));
))))


let print_proof_state1 : Prims.string  ->  Prims.unit tac = (fun msg -> (mk_tac (fun ps -> (

let psc = ps.FStar_Tactics_Types.psc
in (

let subst1 = (FStar_TypeChecker_Normalize.psc_subst psc)
in ((

let uu____546 = (FStar_Tactics_Types.subst_proof_state subst1 ps)
in (dump_cur uu____546 msg));
FStar_Tactics_Result.Success (((()), (ps)));
))))))


let print_proof_state : Prims.string  ->  Prims.unit tac = (fun msg -> (mk_tac (fun ps -> (

let psc = ps.FStar_Tactics_Types.psc
in (

let subst1 = (FStar_TypeChecker_Normalize.psc_subst psc)
in ((

let uu____562 = (FStar_Tactics_Types.subst_proof_state subst1 ps)
in (dump_proofstate uu____562 msg));
FStar_Tactics_Result.Success (((()), (ps)));
))))))


let get : FStar_Tactics_Types.proofstate tac = (mk_tac (fun p -> FStar_Tactics_Result.Success (((p), (p)))))


let tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let rec log : FStar_Tactics_Types.proofstate  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun ps f -> (

let uu____621 = (FStar_ST.op_Bang tac_verb_dbg)
in (match (uu____621) with
| FStar_Pervasives_Native.None -> begin
((

let uu____654 = (

let uu____657 = (FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context (FStar_Options.Other ("TacVerbose")))
in FStar_Pervasives_Native.Some (uu____657))
in (FStar_ST.op_Colon_Equals tac_verb_dbg uu____654));
(log ps f);
)
end
| FStar_Pervasives_Native.Some (true) -> begin
(f ())
end
| FStar_Pervasives_Native.Some (false) -> begin
()
end)))


let mlog : 'a . (Prims.unit  ->  Prims.unit)  ->  (Prims.unit  ->  'a tac)  ->  'a tac = (fun f cont -> (bind get (fun ps -> ((log ps f);
(cont ());
))))


let fail : 'a . Prims.string  ->  'a tac = (fun msg -> (mk_tac (fun ps -> ((

let uu____732 = (FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context (FStar_Options.Other ("TacFail")))
in (match (uu____732) with
| true -> begin
(dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg))
end
| uu____733 -> begin
()
end));
FStar_Tactics_Result.Failed (((msg), (ps)));
))))


let fail1 : 'Auu____737 . Prims.string  ->  Prims.string  ->  'Auu____737 tac = (fun msg x -> (

let uu____748 = (FStar_Util.format1 msg x)
in (fail uu____748)))


let fail2 : 'Auu____753 . Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____753 tac = (fun msg x y -> (

let uu____768 = (FStar_Util.format2 msg x y)
in (fail uu____768)))


let fail3 : 'Auu____774 . Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____774 tac = (fun msg x y z -> (

let uu____793 = (FStar_Util.format3 msg x y z)
in (fail uu____793)))


let fail4 : 'Auu____800 . Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____800 tac = (fun msg x y z w -> (

let uu____823 = (FStar_Util.format4 msg x y z w)
in (fail uu____823)))


let trytac' : 'a . 'a tac  ->  (Prims.string, 'a) FStar_Util.either tac = (fun t -> (mk_tac (fun ps -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____853 = (run t ps)
in (match (uu____853) with
| FStar_Tactics_Result.Success (a, q) -> begin
((FStar_Syntax_Unionfind.commit tx);
FStar_Tactics_Result.Success (((FStar_Util.Inr (a)), (q)));
)
end
| FStar_Tactics_Result.Failed (m, q) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(

let ps1 = (

let uu___66_877 = ps
in {FStar_Tactics_Types.main_context = uu___66_877.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___66_877.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___66_877.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___66_877.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___66_877.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___66_877.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___66_877.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___66_877.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___66_877.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___66_877.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = q.FStar_Tactics_Types.freshness})
in FStar_Tactics_Result.Success (((FStar_Util.Inl (m)), (ps1))));
)
end))))))


let trytac : 'a . 'a tac  ->  'a FStar_Pervasives_Native.option tac = (fun t -> (

let uu____901 = (trytac' t)
in (bind uu____901 (fun r -> (match (r) with
| FStar_Util.Inr (v1) -> begin
(ret (FStar_Pervasives_Native.Some (v1)))
end
| FStar_Util.Inl (uu____928) -> begin
(ret FStar_Pervasives_Native.None)
end)))))


let trytac_exn : 'a . 'a tac  ->  'a FStar_Pervasives_Native.option tac = (fun t -> (mk_tac (fun ps -> (FStar_All.try_with (fun uu___68_956 -> (match (()) with
| () -> begin
(

let uu____961 = (trytac t)
in (run uu____961 ps))
end)) (fun uu___67_972 -> (match (uu___67_972) with
| FStar_Errors.Err (uu____977, msg) -> begin
((log ps (fun uu____981 -> (FStar_Util.print1 "trytac_exn error: (%s)" msg)));
FStar_Tactics_Result.Success (((FStar_Pervasives_Native.None), (ps)));
)
end
| FStar_Errors.Error (uu____986, msg, uu____988) -> begin
((log ps (fun uu____991 -> (FStar_Util.print1 "trytac_exn error: (%s)" msg)));
FStar_Tactics_Result.Success (((FStar_Pervasives_Native.None), (ps)));
)
end))))))


let wrap_err : 'a . Prims.string  ->  'a tac  ->  'a tac = (fun pref t -> (mk_tac (fun ps -> (

let uu____1019 = (run t ps)
in (match (uu____1019) with
| FStar_Tactics_Result.Success (a, q) -> begin
FStar_Tactics_Result.Success (((a), (q)))
end
| FStar_Tactics_Result.Failed (msg, q) -> begin
FStar_Tactics_Result.Failed ((((Prims.strcat pref (Prims.strcat ": " msg))), (q)))
end)))))


let set : FStar_Tactics_Types.proofstate  ->  Prims.unit tac = (fun p -> (mk_tac (fun uu____1036 -> FStar_Tactics_Result.Success (((()), (p))))))


let __do_unify : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun env t1 t2 -> (

let debug_on = (fun uu____1053 -> (

let uu____1054 = (FStar_Options.set_options FStar_Options.Set "--debug_level Rel --debug_level RelCheck")
in ()))
in (

let debug_off = (fun uu____1058 -> (

let uu____1059 = (FStar_Options.set_options FStar_Options.Reset "")
in ()))
in ((

let uu____1061 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1061) with
| true -> begin
((debug_on ());
(

let uu____1063 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1064 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1063 uu____1064)));
)
end
| uu____1065 -> begin
()
end));
(FStar_All.try_with (fun uu___70_1072 -> (match (()) with
| () -> begin
(

let res = (FStar_TypeChecker_Rel.teq_nosmt env t1 t2)
in ((debug_off ());
(

let uu____1078 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1078) with
| true -> begin
(

let uu____1079 = (FStar_Util.string_of_bool res)
in (

let uu____1080 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1081 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1079 uu____1080 uu____1081))))
end
| uu____1082 -> begin
()
end));
(ret res);
))
end)) (fun uu___69_1087 -> (match (uu___69_1087) with
| FStar_Errors.Err (uu____1090, msg) -> begin
((debug_off ());
(mlog (fun uu____1094 -> (FStar_Util.print1 ">> do_unify error, (%s)\n" msg)) (fun uu____1096 -> (ret false)));
)
end
| FStar_Errors.Error (uu____1097, msg, r) -> begin
((debug_off ());
(mlog (fun uu____1103 -> (

let uu____1104 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg uu____1104))) (fun uu____1106 -> (ret false)));
)
end)));
))))


let do_unify : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun env t1 t2 -> (

let uu____1120 = (__do_unify env t1 t2)
in (bind uu____1120 (fun b -> (match ((not (b))) with
| true -> begin
(

let t11 = (FStar_TypeChecker_Normalize.normalize [] env t1)
in (

let t21 = (FStar_TypeChecker_Normalize.normalize [] env t2)
in (__do_unify env t11 t21)))
end
| uu____1131 -> begin
(ret b)
end)))))


let trysolve : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun goal solution -> (do_unify goal.FStar_Tactics_Types.context solution goal.FStar_Tactics_Types.witness))


let __dismiss : Prims.unit tac = (bind get (fun p -> (

let uu____1147 = (

let uu___71_1148 = p
in (

let uu____1149 = (FStar_List.tl p.FStar_Tactics_Types.goals)
in {FStar_Tactics_Types.main_context = uu___71_1148.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___71_1148.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___71_1148.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu____1149; FStar_Tactics_Types.smt_goals = uu___71_1148.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___71_1148.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___71_1148.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___71_1148.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___71_1148.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___71_1148.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___71_1148.FStar_Tactics_Types.freshness}))
in (set uu____1147))))


let dismiss : Prims.unit  ->  Prims.unit tac = (fun uu____1156 -> (bind get (fun p -> (match (p.FStar_Tactics_Types.goals) with
| [] -> begin
(fail "dismiss: no more goals")
end
| uu____1163 -> begin
__dismiss
end))))


let solve : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun goal solution -> (

let uu____1176 = (trysolve goal solution)
in (bind uu____1176 (fun b -> (match (b) with
| true -> begin
__dismiss
end
| uu____1183 -> begin
(

let uu____1184 = (

let uu____1185 = (tts goal.FStar_Tactics_Types.context solution)
in (

let uu____1186 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.witness)
in (

let uu____1187 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (FStar_Util.format3 "%s does not solve %s : %s" uu____1185 uu____1186 uu____1187))))
in (fail uu____1184))
end)))))


let dismiss_all : Prims.unit tac = (bind get (fun p -> (set (

let uu___72_1194 = p
in {FStar_Tactics_Types.main_context = uu___72_1194.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___72_1194.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___72_1194.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = []; FStar_Tactics_Types.smt_goals = uu___72_1194.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___72_1194.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___72_1194.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___72_1194.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___72_1194.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___72_1194.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___72_1194.FStar_Tactics_Types.freshness}))))


let nwarn : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let check_valid_goal : FStar_Tactics_Types.goal  ->  Prims.unit = (fun g -> (

let uu____1235 = (FStar_Options.defensive ())
in (match (uu____1235) with
| true -> begin
(

let b = true
in (

let env = g.FStar_Tactics_Types.context
in (

let b1 = (b && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.witness))
in (

let b2 = (b1 && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.goal_ty))
in (

let rec aux = (fun b3 e -> (

let uu____1247 = (FStar_TypeChecker_Env.pop_bv e)
in (match (uu____1247) with
| FStar_Pervasives_Native.None -> begin
b3
end
| FStar_Pervasives_Native.Some (bv, e1) -> begin
(

let b4 = (b3 && (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort))
in (aux b4 e1))
end)))
in (

let uu____1265 = ((

let uu____1268 = (aux b2 env)
in (not (uu____1268))) && (

let uu____1270 = (FStar_ST.op_Bang nwarn)
in (uu____1270 < (Prims.parse_int "5"))))
in (match (uu____1265) with
| true -> begin
((

let uu____1297 = (

let uu____1302 = (

let uu____1303 = (goal_to_string g)
in (FStar_Util.format1 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n" uu____1303))
in ((FStar_Errors.Warning_IllFormedGoal), (uu____1302)))
in (FStar_Errors.log_issue g.FStar_Tactics_Types.goal_ty.FStar_Syntax_Syntax.pos uu____1297));
(

let uu____1304 = (

let uu____1305 = (FStar_ST.op_Bang nwarn)
in (uu____1305 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals nwarn uu____1304));
)
end
| uu____1356 -> begin
()
end)))))))
end
| uu____1357 -> begin
()
end)))


let add_goals : FStar_Tactics_Types.goal Prims.list  ->  Prims.unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___73_1375 = p
in {FStar_Tactics_Types.main_context = uu___73_1375.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___73_1375.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___73_1375.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append gs p.FStar_Tactics_Types.goals); FStar_Tactics_Types.smt_goals = uu___73_1375.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___73_1375.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___73_1375.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___73_1375.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___73_1375.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___73_1375.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___73_1375.FStar_Tactics_Types.freshness}));
))))


let add_smt_goals : FStar_Tactics_Types.goal Prims.list  ->  Prims.unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___74_1393 = p
in {FStar_Tactics_Types.main_context = uu___74_1393.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___74_1393.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___74_1393.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___74_1393.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = (FStar_List.append gs p.FStar_Tactics_Types.smt_goals); FStar_Tactics_Types.depth = uu___74_1393.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___74_1393.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___74_1393.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___74_1393.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___74_1393.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___74_1393.FStar_Tactics_Types.freshness}));
))))


let push_goals : FStar_Tactics_Types.goal Prims.list  ->  Prims.unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___75_1411 = p
in {FStar_Tactics_Types.main_context = uu___75_1411.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___75_1411.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___75_1411.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append p.FStar_Tactics_Types.goals gs); FStar_Tactics_Types.smt_goals = uu___75_1411.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___75_1411.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___75_1411.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___75_1411.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___75_1411.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___75_1411.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___75_1411.FStar_Tactics_Types.freshness}));
))))


let push_smt_goals : FStar_Tactics_Types.goal Prims.list  ->  Prims.unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___76_1429 = p
in {FStar_Tactics_Types.main_context = uu___76_1429.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___76_1429.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___76_1429.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___76_1429.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = (FStar_List.append p.FStar_Tactics_Types.smt_goals gs); FStar_Tactics_Types.depth = uu___76_1429.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___76_1429.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___76_1429.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___76_1429.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___76_1429.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___76_1429.FStar_Tactics_Types.freshness}));
))))


let replace_cur : FStar_Tactics_Types.goal  ->  Prims.unit tac = (fun g -> (bind __dismiss (fun uu____1438 -> (add_goals ((g)::[])))))


let add_implicits : implicits  ->  Prims.unit tac = (fun i -> (bind get (fun p -> (set (

let uu___77_1450 = p
in {FStar_Tactics_Types.main_context = uu___77_1450.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___77_1450.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = (FStar_List.append i p.FStar_Tactics_Types.all_implicits); FStar_Tactics_Types.goals = uu___77_1450.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___77_1450.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___77_1450.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___77_1450.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___77_1450.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___77_1450.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___77_1450.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___77_1450.FStar_Tactics_Types.freshness})))))


let new_uvar : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  FStar_Syntax_Syntax.term tac = (fun reason env typ -> (

let uu____1476 = (FStar_TypeChecker_Util.new_implicit_var reason typ.FStar_Syntax_Syntax.pos env typ)
in (match (uu____1476) with
| (u, uu____1492, g_u) -> begin
(

let uu____1506 = (add_implicits g_u.FStar_TypeChecker_Env.implicits)
in (bind uu____1506 (fun uu____1510 -> (ret u))))
end)))


let is_true : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1514 = (FStar_Syntax_Util.un_squash t)
in (match (uu____1514) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____1524 = (

let uu____1525 = (FStar_Syntax_Subst.compress t')
in uu____1525.FStar_Syntax_Syntax.n)
in (match (uu____1524) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)
end
| uu____1529 -> begin
false
end))
end
| uu____1530 -> begin
false
end)))


let is_false : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1538 = (FStar_Syntax_Util.un_squash t)
in (match (uu____1538) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____1548 = (

let uu____1549 = (FStar_Syntax_Subst.compress t')
in uu____1549.FStar_Syntax_Syntax.n)
in (match (uu____1548) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid)
end
| uu____1553 -> begin
false
end))
end
| uu____1554 -> begin
false
end)))


let cur_goal : Prims.unit  ->  FStar_Tactics_Types.goal tac = (fun uu____1563 -> (bind get (fun p -> (match (p.FStar_Tactics_Types.goals) with
| [] -> begin
(fail "No more goals (1)")
end
| (hd1)::tl1 -> begin
(ret hd1)
end))))


let tadmit : Prims.unit  ->  Prims.unit tac = (fun uu____1578 -> (

let uu____1581 = (

let uu____1584 = (cur_goal ())
in (bind uu____1584 (fun g -> ((

let uu____1591 = (

let uu____1596 = (

let uu____1597 = (goal_to_string g)
in (FStar_Util.format1 "Tactics admitted goal <%s>\n\n" uu____1597))
in ((FStar_Errors.Warning_TacAdmit), (uu____1596)))
in (FStar_Errors.log_issue g.FStar_Tactics_Types.goal_ty.FStar_Syntax_Syntax.pos uu____1591));
(solve g FStar_Syntax_Util.exp_unit);
))))
in (FStar_All.pipe_left (wrap_err "tadmit") uu____1581)))


let fresh : Prims.unit  ->  FStar_BigInt.t tac = (fun uu____1606 -> (bind get (fun ps -> (

let n1 = ps.FStar_Tactics_Types.freshness
in (

let ps1 = (

let uu___78_1616 = ps
in {FStar_Tactics_Types.main_context = uu___78_1616.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___78_1616.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___78_1616.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___78_1616.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___78_1616.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___78_1616.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___78_1616.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___78_1616.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___78_1616.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___78_1616.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))})
in (

let uu____1617 = (set ps1)
in (bind uu____1617 (fun uu____1622 -> (

let uu____1623 = (FStar_BigInt.of_int_fs n1)
in (ret uu____1623))))))))))


let ngoals : Prims.unit  ->  FStar_BigInt.t tac = (fun uu____1628 -> (bind get (fun ps -> (

let n1 = (FStar_List.length ps.FStar_Tactics_Types.goals)
in (

let uu____1636 = (FStar_BigInt.of_int_fs n1)
in (ret uu____1636))))))


let ngoals_smt : Prims.unit  ->  FStar_BigInt.t tac = (fun uu____1647 -> (bind get (fun ps -> (

let n1 = (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
in (

let uu____1655 = (FStar_BigInt.of_int_fs n1)
in (ret uu____1655))))))


let is_guard : Prims.unit  ->  Prims.bool tac = (fun uu____1666 -> (

let uu____1669 = (cur_goal ())
in (bind uu____1669 (fun g -> (ret g.FStar_Tactics_Types.is_guard)))))


let mk_irrelevant_goal : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  FStar_Options.optionstate  ->  FStar_Tactics_Types.goal tac = (fun reason env phi opts -> (

let typ = (

let uu____1693 = (env.FStar_TypeChecker_Env.universe_of env phi)
in (FStar_Syntax_Util.mk_squash uu____1693 phi))
in (

let uu____1694 = (new_uvar reason env typ)
in (bind uu____1694 (fun u -> (

let goal = {FStar_Tactics_Types.context = env; FStar_Tactics_Types.witness = u; FStar_Tactics_Types.goal_ty = typ; FStar_Tactics_Types.opts = opts; FStar_Tactics_Types.is_guard = false}
in (ret goal)))))))


let __tc : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ * FStar_TypeChecker_Env.guard_t) tac = (fun e t -> (bind get (fun ps -> (mlog (fun uu____1739 -> (

let uu____1740 = (tts e t)
in (FStar_Util.print1 "Tac> __tc(%s)\n" uu____1740))) (fun uu____1742 -> (FStar_All.try_with (fun uu___80_1753 -> (match (()) with
| () -> begin
(

let uu____1762 = (ps.FStar_Tactics_Types.main_context.FStar_TypeChecker_Env.type_of e t)
in (ret uu____1762))
end)) (fun uu___79_1780 -> (match (uu___79_1780) with
| FStar_Errors.Err (uu____1789, msg) -> begin
(

let uu____1791 = (tts e t)
in (

let uu____1792 = (

let uu____1793 = (FStar_TypeChecker_Env.all_binders e)
in (FStar_All.pipe_right uu____1793 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____1791 uu____1792 msg)))
end
| FStar_Errors.Error (uu____1800, msg, uu____1802) -> begin
(

let uu____1803 = (tts e t)
in (

let uu____1804 = (

let uu____1805 = (FStar_TypeChecker_Env.all_binders e)
in (FStar_All.pipe_right uu____1805 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____1803 uu____1804 msg)))
end))))))))


let istrivial : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e t -> (

let steps = (FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.UnfoldTac)::(FStar_TypeChecker_Normalize.Unmeta)::[]
in (

let t1 = (normalize steps e t)
in (is_true t1))))


let get_guard_policy : Prims.unit  ->  FStar_Tactics_Types.guard_policy tac = (fun uu____1826 -> (bind get (fun ps -> (ret ps.FStar_Tactics_Types.guard_policy))))


let set_guard_policy : FStar_Tactics_Types.guard_policy  ->  Prims.unit tac = (fun pol -> (bind get (fun ps -> (set (

let uu___81_1842 = ps
in {FStar_Tactics_Types.main_context = uu___81_1842.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___81_1842.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___81_1842.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___81_1842.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___81_1842.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___81_1842.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___81_1842.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___81_1842.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___81_1842.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = pol; FStar_Tactics_Types.freshness = uu___81_1842.FStar_Tactics_Types.freshness})))))


let with_policy : 'a . FStar_Tactics_Types.guard_policy  ->  'a tac  ->  'a tac = (fun pol t -> (

let uu____1861 = (get_guard_policy ())
in (bind uu____1861 (fun old_pol -> (

let uu____1867 = (set_guard_policy pol)
in (bind uu____1867 (fun uu____1871 -> (bind t (fun r -> (

let uu____1875 = (set_guard_policy old_pol)
in (bind uu____1875 (fun uu____1879 -> (ret r)))))))))))))


let proc_guard : Prims.string  ->  env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Options.optionstate  ->  Prims.unit tac = (fun reason e g opts -> (

let uu____1896 = (

let uu____1897 = (FStar_TypeChecker_Rel.simplify_guard e g)
in uu____1897.FStar_TypeChecker_Env.guard_f)
in (match (uu____1896) with
| FStar_TypeChecker_Common.Trivial -> begin
(ret ())
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____1901 = (istrivial e f)
in (match (uu____1901) with
| true -> begin
(ret ())
end
| uu____1904 -> begin
(bind get (fun ps -> (match (ps.FStar_Tactics_Types.guard_policy) with
| FStar_Tactics_Types.Drop -> begin
(ret ())
end
| FStar_Tactics_Types.Goal -> begin
(

let uu____1909 = (mk_irrelevant_goal reason e f opts)
in (bind uu____1909 (fun goal -> (

let goal1 = (

let uu___82_1916 = goal
in {FStar_Tactics_Types.context = uu___82_1916.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___82_1916.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___82_1916.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___82_1916.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = true})
in (push_goals ((goal1)::[]))))))
end
| FStar_Tactics_Types.SMT -> begin
(

let uu____1917 = (mk_irrelevant_goal reason e f opts)
in (bind uu____1917 (fun goal -> (

let goal1 = (

let uu___83_1924 = goal
in {FStar_Tactics_Types.context = uu___83_1924.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___83_1924.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___83_1924.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___83_1924.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = true})
in (push_smt_goals ((goal1)::[]))))))
end
| FStar_Tactics_Types.Force -> begin
(FStar_All.try_with (fun uu___85_1929 -> (match (()) with
| () -> begin
(

let uu____1932 = (

let uu____1933 = (

let uu____1934 = (FStar_TypeChecker_Rel.discharge_guard_no_smt e g)
in (FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____1934))
in (not (uu____1933)))
in (match (uu____1932) with
| true -> begin
(mlog (fun uu____1939 -> (

let uu____1940 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print1 "guard = %s\n" uu____1940))) (fun uu____1942 -> (fail1 "Forcing the guard failed %s)" reason)))
end
| uu____1943 -> begin
(ret ())
end))
end)) (fun uu___84_1946 -> (match (uu___84_1946) with
| uu____1949 -> begin
(mlog (fun uu____1952 -> (

let uu____1953 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print1 "guard = %s\n" uu____1953))) (fun uu____1955 -> (fail1 "Forcing the guard failed (%s)" reason)))
end)))
end)))
end))
end)))


let tc : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.typ tac = (fun t -> (

let uu____1963 = (

let uu____1966 = (cur_goal ())
in (bind uu____1966 (fun goal -> (

let uu____1972 = (__tc goal.FStar_Tactics_Types.context t)
in (bind uu____1972 (fun uu____1992 -> (match (uu____1992) with
| (t1, typ, guard) -> begin
(

let uu____2004 = (proc_guard "tc" goal.FStar_Tactics_Types.context guard goal.FStar_Tactics_Types.opts)
in (bind uu____2004 (fun uu____2008 -> (ret typ))))
end)))))))
in (FStar_All.pipe_left (wrap_err "tc") uu____1963)))


let add_irrelevant_goal : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  FStar_Options.optionstate  ->  Prims.unit tac = (fun reason env phi opts -> (

let uu____2029 = (mk_irrelevant_goal reason env phi opts)
in (bind uu____2029 (fun goal -> (add_goals ((goal)::[]))))))


let trivial : Prims.unit  ->  Prims.unit tac = (fun uu____2038 -> (

let uu____2041 = (cur_goal ())
in (bind uu____2041 (fun goal -> (

let uu____2047 = (istrivial goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (match (uu____2047) with
| true -> begin
(solve goal FStar_Syntax_Util.exp_unit)
end
| uu____2050 -> begin
(

let uu____2051 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail1 "Not a trivial goal: %s" uu____2051))
end))))))


let goal_from_guard : Prims.string  ->  env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Options.optionstate  ->  FStar_Tactics_Types.goal FStar_Pervasives_Native.option tac = (fun reason e g opts -> (

let uu____2072 = (

let uu____2073 = (FStar_TypeChecker_Rel.simplify_guard e g)
in uu____2073.FStar_TypeChecker_Env.guard_f)
in (match (uu____2072) with
| FStar_TypeChecker_Common.Trivial -> begin
(ret FStar_Pervasives_Native.None)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____2081 = (istrivial e f)
in (match (uu____2081) with
| true -> begin
(ret FStar_Pervasives_Native.None)
end
| uu____2088 -> begin
(

let uu____2089 = (mk_irrelevant_goal reason e f opts)
in (bind uu____2089 (fun goal -> (ret (FStar_Pervasives_Native.Some ((

let uu___86_2099 = goal
in {FStar_Tactics_Types.context = uu___86_2099.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___86_2099.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___86_2099.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___86_2099.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = true})))))))
end))
end)))


let smt : Prims.unit  ->  Prims.unit tac = (fun uu____2104 -> (

let uu____2107 = (cur_goal ())
in (bind uu____2107 (fun g -> (

let uu____2113 = (is_irrelevant g)
in (match (uu____2113) with
| true -> begin
(bind __dismiss (fun uu____2117 -> (add_smt_goals ((g)::[]))))
end
| uu____2118 -> begin
(

let uu____2119 = (tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (fail1 "goal is not irrelevant: cannot dispatch to smt (%s)" uu____2119))
end))))))


let divide : 'a 'b . FStar_BigInt.t  ->  'a tac  ->  'b tac  ->  ('a * 'b) tac = (fun n1 l r -> (bind get (fun p -> (

let uu____2160 = (FStar_All.try_with (fun uu___91_2183 -> (match (()) with
| () -> begin
(

let uu____2194 = (

let uu____2203 = (FStar_BigInt.to_int_fs n1)
in (FStar_List.splitAt uu____2203 p.FStar_Tactics_Types.goals))
in (ret uu____2194))
end)) (fun uu___90_2214 -> (match (uu___90_2214) with
| uu____2225 -> begin
(fail "divide: not enough goals")
end)))
in (bind uu____2160 (fun uu____2252 -> (match (uu____2252) with
| (lgs, rgs) -> begin
(

let lp = (

let uu___87_2278 = p
in {FStar_Tactics_Types.main_context = uu___87_2278.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___87_2278.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___87_2278.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = lgs; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = uu___87_2278.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___87_2278.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___87_2278.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___87_2278.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___87_2278.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___87_2278.FStar_Tactics_Types.freshness})
in (

let rp = (

let uu___88_2280 = p
in {FStar_Tactics_Types.main_context = uu___88_2280.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___88_2280.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___88_2280.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = rgs; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = uu___88_2280.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___88_2280.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___88_2280.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___88_2280.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___88_2280.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___88_2280.FStar_Tactics_Types.freshness})
in (

let uu____2281 = (set lp)
in (bind uu____2281 (fun uu____2289 -> (bind l (fun a -> (bind get (fun lp' -> (

let uu____2303 = (set rp)
in (bind uu____2303 (fun uu____2311 -> (bind r (fun b -> (bind get (fun rp' -> (

let p' = (

let uu___89_2327 = p
in {FStar_Tactics_Types.main_context = uu___89_2327.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___89_2327.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___89_2327.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append lp'.FStar_Tactics_Types.goals rp'.FStar_Tactics_Types.goals); FStar_Tactics_Types.smt_goals = (FStar_List.append lp'.FStar_Tactics_Types.smt_goals (FStar_List.append rp'.FStar_Tactics_Types.smt_goals p.FStar_Tactics_Types.smt_goals)); FStar_Tactics_Types.depth = uu___89_2327.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___89_2327.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___89_2327.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___89_2327.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___89_2327.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___89_2327.FStar_Tactics_Types.freshness})
in (

let uu____2328 = (set p')
in (bind uu____2328 (fun uu____2336 -> (ret ((a), (b)))))))))))))))))))))))
end)))))))


let focus : 'a . 'a tac  ->  'a tac = (fun f -> (

let uu____2354 = (divide FStar_BigInt.one f idtac)
in (bind uu____2354 (fun uu____2367 -> (match (uu____2367) with
| (a, ()) -> begin
(ret a)
end)))))


let rec map : 'a . 'a tac  ->  'a Prims.list tac = (fun tau -> (bind get (fun p -> (match (p.FStar_Tactics_Types.goals) with
| [] -> begin
(ret [])
end
| (uu____2401)::uu____2402 -> begin
(

let uu____2405 = (

let uu____2414 = (map tau)
in (divide FStar_BigInt.one tau uu____2414))
in (bind uu____2405 (fun uu____2432 -> (match (uu____2432) with
| (h, t) -> begin
(ret ((h)::t))
end))))
end))))


let seq : Prims.unit tac  ->  Prims.unit tac  ->  Prims.unit tac = (fun t1 t2 -> (

let uu____2469 = (bind t1 (fun uu____2474 -> (

let uu____2475 = (map t2)
in (bind uu____2475 (fun uu____2483 -> (ret ()))))))
in (focus uu____2469)))


let intro : Prims.unit  ->  FStar_Syntax_Syntax.binder tac = (fun uu____2490 -> (

let uu____2493 = (

let uu____2496 = (cur_goal ())
in (bind uu____2496 (fun goal -> (

let uu____2505 = (FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty)
in (match (uu____2505) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____2520 = (

let uu____2521 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____2521)))
in (match (uu____2520) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____2524 -> begin
(

let env' = (FStar_TypeChecker_Env.push_binders goal.FStar_Tactics_Types.context ((b)::[]))
in (

let typ' = (comp_to_typ c)
in (

let uu____2527 = (new_uvar "intro" env' typ')
in (bind uu____2527 (fun u -> (

let uu____2533 = (

let uu____2536 = (FStar_Syntax_Util.abs ((b)::[]) u FStar_Pervasives_Native.None)
in (trysolve goal uu____2536))
in (bind uu____2533 (fun bb -> (match (bb) with
| true -> begin
(

let uu____2542 = (

let uu____2545 = (

let uu___92_2546 = goal
in (

let uu____2547 = (bnorm env' u)
in (

let uu____2548 = (bnorm env' typ')
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = uu____2547; FStar_Tactics_Types.goal_ty = uu____2548; FStar_Tactics_Types.opts = uu___92_2546.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___92_2546.FStar_Tactics_Types.is_guard})))
in (replace_cur uu____2545))
in (bind uu____2542 (fun uu____2550 -> (ret b))))
end
| uu____2551 -> begin
(fail "unification failed")
end)))))))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2556 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail1 "goal is not an arrow (%s)" uu____2556))
end)))))
in (FStar_All.pipe_left (wrap_err "intro") uu____2493)))


let intro_rec : Prims.unit  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac = (fun uu____2569 -> (

let uu____2576 = (cur_goal ())
in (bind uu____2576 (fun goal -> ((FStar_Util.print_string "WARNING (intro_rec): calling this is known to cause normalizer loops\n");
(FStar_Util.print_string "WARNING (intro_rec): proceed at your own risk...\n");
(

let uu____2593 = (FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty)
in (match (uu____2593) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____2612 = (

let uu____2613 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____2613)))
in (match (uu____2612) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____2624 -> begin
(

let bv = (FStar_Syntax_Syntax.gen_bv "__recf" FStar_Pervasives_Native.None goal.FStar_Tactics_Types.goal_ty)
in (

let bs = (

let uu____2629 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____2629)::(b)::[])
in (

let env' = (FStar_TypeChecker_Env.push_binders goal.FStar_Tactics_Types.context bs)
in (

let uu____2631 = (

let uu____2634 = (comp_to_typ c)
in (new_uvar "intro_rec" env' uu____2634))
in (bind uu____2631 (fun u -> (

let lb = (

let uu____2649 = (FStar_Syntax_Util.abs ((b)::[]) u FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] goal.FStar_Tactics_Types.goal_ty FStar_Parser_Const.effect_Tot_lid uu____2649 [] FStar_Range.dummyRange))
in (

let body = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____2655 = (FStar_Syntax_Subst.close_let_rec ((lb)::[]) body)
in (match (uu____2655) with
| (lbs, body1) -> begin
(

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body1)))) FStar_Pervasives_Native.None goal.FStar_Tactics_Types.witness.FStar_Syntax_Syntax.pos)
in (

let uu____2685 = (trysolve goal tm)
in (bind uu____2685 (fun bb -> (match (bb) with
| true -> begin
(

let uu____2701 = (

let uu____2704 = (

let uu___93_2705 = goal
in (

let uu____2706 = (bnorm env' u)
in (

let uu____2707 = (

let uu____2708 = (comp_to_typ c)
in (bnorm env' uu____2708))
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = uu____2706; FStar_Tactics_Types.goal_ty = uu____2707; FStar_Tactics_Types.opts = uu___93_2705.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___93_2705.FStar_Tactics_Types.is_guard})))
in (replace_cur uu____2704))
in (bind uu____2701 (fun uu____2715 -> (

let uu____2716 = (

let uu____2721 = (FStar_Syntax_Syntax.mk_binder bv)
in ((uu____2721), (b)))
in (ret uu____2716)))))
end
| uu____2726 -> begin
(fail "intro_rec: unification failed")
end)))))
end))))))))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2735 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail1 "intro_rec: goal is not an arrow (%s)" uu____2735))
end));
)))))


let norm : FStar_Syntax_Embeddings.norm_step Prims.list  ->  Prims.unit tac = (fun s -> (

let uu____2751 = (cur_goal ())
in (bind uu____2751 (fun goal -> (mlog (fun uu____2758 -> (

let uu____2759 = (FStar_Syntax_Print.term_to_string goal.FStar_Tactics_Types.witness)
in (FStar_Util.print1 "norm: witness = %s\n" uu____2759))) (fun uu____2764 -> (

let steps = (

let uu____2768 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldTac)::[]) uu____2768))
in (

let w = (normalize steps goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.witness)
in (

let t = (normalize steps goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (replace_cur (

let uu___94_2775 = goal
in {FStar_Tactics_Types.context = uu___94_2775.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = w; FStar_Tactics_Types.goal_ty = t; FStar_Tactics_Types.opts = uu___94_2775.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___94_2775.FStar_Tactics_Types.is_guard})))))))))))


let norm_term_env : env  ->  FStar_Syntax_Embeddings.norm_step Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun e s t -> (

let uu____2793 = (mlog (fun uu____2798 -> (

let uu____2799 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "norm_term: tm = %s\n" uu____2799))) (fun uu____2801 -> (bind get (fun ps -> (

let opts = (match (ps.FStar_Tactics_Types.goals) with
| (g)::uu____2807 -> begin
g.FStar_Tactics_Types.opts
end
| uu____2810 -> begin
(FStar_Options.peek ())
end)
in (mlog (fun uu____2815 -> (

let uu____2816 = (tts ps.FStar_Tactics_Types.main_context t)
in (FStar_Util.print1 "norm_term_env: t = %s\n" uu____2816))) (fun uu____2819 -> (

let uu____2820 = (__tc e t)
in (bind uu____2820 (fun uu____2841 -> (match (uu____2841) with
| (t1, uu____2851, uu____2852) -> begin
(

let steps = (

let uu____2856 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldTac)::[]) uu____2856))
in (

let t2 = (normalize steps ps.FStar_Tactics_Types.main_context t1)
in (ret t2)))
end)))))))))))
in (FStar_All.pipe_left (wrap_err "norm_term") uu____2793)))


let refine_intro : Prims.unit  ->  Prims.unit tac = (fun uu____2868 -> (

let uu____2871 = (

let uu____2874 = (cur_goal ())
in (bind uu____2874 (fun g -> (

let uu____2881 = (FStar_TypeChecker_Rel.base_and_refinement g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (match (uu____2881) with
| (uu____2894, FStar_Pervasives_Native.None) -> begin
(fail "not a refinement")
end
| (t, FStar_Pervasives_Native.Some (bv, phi)) -> begin
(

let g1 = (

let uu___95_2919 = g
in {FStar_Tactics_Types.context = uu___95_2919.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___95_2919.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = t; FStar_Tactics_Types.opts = uu___95_2919.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___95_2919.FStar_Tactics_Types.is_guard})
in (

let uu____2920 = (

let uu____2925 = (

let uu____2930 = (

let uu____2931 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____2931)::[])
in (FStar_Syntax_Subst.open_term uu____2930 phi))
in (match (uu____2925) with
| (bvs, phi1) -> begin
(

let uu____2938 = (

let uu____2939 = (FStar_List.hd bvs)
in (FStar_Pervasives_Native.fst uu____2939))
in ((uu____2938), (phi1)))
end))
in (match (uu____2920) with
| (bv1, phi1) -> begin
(

let uu____2952 = (

let uu____2955 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv1), (g.FStar_Tactics_Types.witness))))::[]) phi1)
in (mk_irrelevant_goal "refine_intro refinement" g.FStar_Tactics_Types.context uu____2955 g.FStar_Tactics_Types.opts))
in (bind uu____2952 (fun g2 -> (bind __dismiss (fun uu____2959 -> (add_goals ((g1)::(g2)::[])))))))
end)))
end)))))
in (FStar_All.pipe_left (wrap_err "refine_intro") uu____2871)))


let __exact_now : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun set_expected_typ1 t -> (

let uu____2974 = (cur_goal ())
in (bind uu____2974 (fun goal -> (

let env = (match (set_expected_typ1) with
| true -> begin
(FStar_TypeChecker_Env.set_expected_typ goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
end
| uu____2982 -> begin
goal.FStar_Tactics_Types.context
end)
in (

let uu____2983 = (__tc env t)
in (bind uu____2983 (fun uu____3002 -> (match (uu____3002) with
| (t1, typ, guard) -> begin
(mlog (fun uu____3017 -> (

let uu____3018 = (tts goal.FStar_Tactics_Types.context typ)
in (

let uu____3019 = (FStar_TypeChecker_Rel.guard_to_string goal.FStar_Tactics_Types.context guard)
in (FStar_Util.print2 "__exact_now: got type %s\n__exact_now and guard %s\n" uu____3018 uu____3019)))) (fun uu____3022 -> (

let uu____3023 = (proc_guard "__exact typing" goal.FStar_Tactics_Types.context guard goal.FStar_Tactics_Types.opts)
in (bind uu____3023 (fun uu____3027 -> (mlog (fun uu____3031 -> (

let uu____3032 = (tts goal.FStar_Tactics_Types.context typ)
in (

let uu____3033 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (FStar_Util.print2 "__exact_now: unifying %s and %s\n" uu____3032 uu____3033)))) (fun uu____3036 -> (

let uu____3037 = (do_unify goal.FStar_Tactics_Types.context typ goal.FStar_Tactics_Types.goal_ty)
in (bind uu____3037 (fun b -> (match (b) with
| true -> begin
(solve goal t1)
end
| uu____3044 -> begin
(

let uu____3045 = (tts goal.FStar_Tactics_Types.context t1)
in (

let uu____3046 = (tts goal.FStar_Tactics_Types.context typ)
in (

let uu____3047 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (

let uu____3048 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.witness)
in (fail4 "%s : %s does not exactly solve the goal %s (witness = %s)" uu____3045 uu____3046 uu____3047 uu____3048)))))
end)))))))))))
end)))))))))


let t_exact : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun set_expected_typ1 tm -> (

let uu____3059 = (mlog (fun uu____3064 -> (

let uu____3065 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "t_exact: tm = %s\n" uu____3065))) (fun uu____3068 -> (

let uu____3069 = (

let uu____3076 = (__exact_now set_expected_typ1 tm)
in (trytac' uu____3076))
in (bind uu____3069 (fun uu___61_3085 -> (match (uu___61_3085) with
| FStar_Util.Inr (r) -> begin
(ret ())
end
| FStar_Util.Inl (e) -> begin
(

let uu____3094 = (

let uu____3101 = (

let uu____3104 = (norm ((FStar_Syntax_Embeddings.Delta)::[]))
in (bind uu____3104 (fun uu____3109 -> (

let uu____3110 = (refine_intro ())
in (bind uu____3110 (fun uu____3114 -> (__exact_now set_expected_typ1 tm)))))))
in (trytac' uu____3101))
in (bind uu____3094 (fun uu___60_3121 -> (match (uu___60_3121) with
| FStar_Util.Inr (r) -> begin
(ret ())
end
| FStar_Util.Inl (uu____3129) -> begin
(fail e)
end))))
end))))))
in (FStar_All.pipe_left (wrap_err "exact") uu____3059)))


let uvar_free_in_goal : FStar_Syntax_Syntax.uvar  ->  FStar_Tactics_Types.goal  ->  Prims.bool = (fun u g -> (match (g.FStar_Tactics_Types.is_guard) with
| true -> begin
false
end
| uu____3140 -> begin
(

let free_uvars = (

let uu____3144 = (

let uu____3151 = (FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty)
in (FStar_Util.set_elements uu____3151))
in (FStar_List.map FStar_Pervasives_Native.fst uu____3144))
in (FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars))
end))


let uvar_free : FStar_Syntax_Syntax.uvar  ->  FStar_Tactics_Types.proofstate  ->  Prims.bool = (fun u ps -> (FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals))


let rec mapM : 'a 'b . ('a  ->  'b tac)  ->  'a Prims.list  ->  'b Prims.list tac = (fun f l -> (match (l) with
| [] -> begin
(ret [])
end
| (x)::xs -> begin
(

let uu____3211 = (f x)
in (bind uu____3211 (fun y -> (

let uu____3219 = (mapM f xs)
in (bind uu____3219 (fun ys -> (ret ((y)::ys))))))))
end))

exception NoUnif


let uu___is_NoUnif : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoUnif -> begin
true
end
| uu____3237 -> begin
false
end))


let rec __apply : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.typ  ->  Prims.unit tac = (fun uopt tm typ -> (

let uu____3251 = (cur_goal ())
in (bind uu____3251 (fun goal -> (mlog (fun uu____3258 -> (

let uu____3259 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3259))) (fun uu____3262 -> (

let uu____3263 = (

let uu____3268 = (

let uu____3271 = (t_exact false tm)
in (with_policy FStar_Tactics_Types.Force uu____3271))
in (trytac_exn uu____3268))
in (bind uu____3263 (fun uu___62_3278 -> (match (uu___62_3278) with
| FStar_Pervasives_Native.Some (r) -> begin
(ret ())
end
| FStar_Pervasives_Native.None -> begin
(mlog (fun uu____3286 -> (

let uu____3287 = (FStar_Syntax_Print.term_to_string typ)
in (FStar_Util.print1 ">>> typ = %s\n" uu____3287))) (fun uu____3290 -> (

let uu____3291 = (FStar_Syntax_Util.arrow_one typ)
in (match (uu____3291) with
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise NoUnif)
end
| FStar_Pervasives_Native.Some ((bv, aq), c) -> begin
(mlog (fun uu____3323 -> (

let uu____3324 = (FStar_Syntax_Print.binder_to_string ((bv), (aq)))
in (FStar_Util.print1 "__apply: pushing binder %s\n" uu____3324))) (fun uu____3327 -> (

let uu____3328 = (

let uu____3329 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____3329)))
in (match (uu____3328) with
| true -> begin
(fail "apply: not total codomain")
end
| uu____3332 -> begin
(

let uu____3333 = (new_uvar "apply" goal.FStar_Tactics_Types.context bv.FStar_Syntax_Syntax.sort)
in (bind uu____3333 (fun u -> (

let tm' = (FStar_Syntax_Syntax.mk_Tm_app tm ((((u), (aq)))::[]) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
in (

let typ' = (

let uu____3353 = (comp_to_typ c)
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (u))))::[])) uu____3353))
in (

let uu____3354 = (__apply uopt tm' typ')
in (bind uu____3354 (fun uu____3362 -> (

let u1 = (bnorm goal.FStar_Tactics_Types.context u)
in (

let uu____3364 = (

let uu____3365 = (

let uu____3368 = (

let uu____3369 = (FStar_Syntax_Util.head_and_args u1)
in (FStar_Pervasives_Native.fst uu____3369))
in (FStar_Syntax_Subst.compress uu____3368))
in uu____3365.FStar_Syntax_Syntax.n)
in (match (uu____3364) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____3397) -> begin
(bind get (fun ps -> (

let uu____3425 = (uopt && (uvar_free uvar ps))
in (match (uu____3425) with
| true -> begin
(ret ())
end
| uu____3428 -> begin
(

let uu____3429 = (

let uu____3432 = (

let uu___96_3433 = goal
in (

let uu____3434 = (bnorm goal.FStar_Tactics_Types.context u1)
in (

let uu____3435 = (bnorm goal.FStar_Tactics_Types.context bv.FStar_Syntax_Syntax.sort)
in {FStar_Tactics_Types.context = uu___96_3433.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu____3434; FStar_Tactics_Types.goal_ty = uu____3435; FStar_Tactics_Types.opts = uu___96_3433.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = false})))
in (uu____3432)::[])
in (add_goals uu____3429))
end))))
end
| t -> begin
(ret ())
end)))))))))))
end))))
end))))
end))))))))))


let try_unif : 'a . 'a tac  ->  'a tac  ->  'a tac = (fun t t' -> (mk_tac (fun ps -> (FStar_All.try_with (fun uu___98_3464 -> (match (()) with
| () -> begin
(run t ps)
end)) (fun uu___97_3468 -> (match (uu___97_3468) with
| NoUnif -> begin
(run t' ps)
end))))))


let apply : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun uopt tm -> (

let uu____3481 = (mlog (fun uu____3486 -> (

let uu____3487 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "apply: tm = %s\n" uu____3487))) (fun uu____3490 -> (

let uu____3491 = (cur_goal ())
in (bind uu____3491 (fun goal -> (

let uu____3497 = (__tc goal.FStar_Tactics_Types.context tm)
in (bind uu____3497 (fun uu____3519 -> (match (uu____3519) with
| (tm1, typ, guard) -> begin
(

let typ1 = (bnorm goal.FStar_Tactics_Types.context typ)
in (

let uu____3532 = (

let uu____3535 = (

let uu____3538 = (__apply uopt tm1 typ1)
in (bind uu____3538 (fun uu____3542 -> (proc_guard "apply guard" goal.FStar_Tactics_Types.context guard goal.FStar_Tactics_Types.opts))))
in (focus uu____3535))
in (

let uu____3543 = (

let uu____3546 = (tts goal.FStar_Tactics_Types.context tm1)
in (

let uu____3547 = (tts goal.FStar_Tactics_Types.context typ1)
in (

let uu____3548 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail3 "Cannot instantiate %s (of type %s) to match goal (%s)" uu____3546 uu____3547 uu____3548))))
in (try_unif uu____3532 uu____3543))))
end)))))))))
in (FStar_All.pipe_left (wrap_err "apply") uu____3481)))


let lemma_or_sq : FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun c -> (

let ct = (FStar_Syntax_Util.comp_to_comp_typ_nouniv c)
in (match ((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)) with
| true -> begin
(

let uu____3575 = (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre)::(post)::uu____3594 -> begin
(((FStar_Pervasives_Native.fst pre)), ((FStar_Pervasives_Native.fst post)))
end
| uu____3635 -> begin
(failwith "apply_lemma: impossible: not a lemma")
end)
in (match (uu____3575) with
| (pre, post) -> begin
(

let post1 = (

let uu____3671 = (

let uu____3680 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit)
in (uu____3680)::[])
in (FStar_Syntax_Util.mk_app post uu____3671))
in FStar_Pervasives_Native.Some (((pre), (post1))))
end))
end
| uu____3693 -> begin
(match ((FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) with
| true -> begin
(

let uu____3700 = (FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.map_opt uu____3700 (fun post -> ((FStar_Syntax_Util.t_true), (post)))))
end
| uu____3719 -> begin
FStar_Pervasives_Native.None
end)
end)))


let apply_lemma : FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun tm -> (

let uu____3731 = (

let uu____3734 = (mlog (fun uu____3739 -> (

let uu____3740 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3740))) (fun uu____3744 -> (

let is_unit_t = (fun t -> (

let uu____3749 = (

let uu____3750 = (FStar_Syntax_Subst.compress t)
in uu____3750.FStar_Syntax_Syntax.n)
in (match (uu____3749) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
true
end
| uu____3754 -> begin
false
end)))
in (

let uu____3755 = (cur_goal ())
in (bind uu____3755 (fun goal -> (

let uu____3761 = (__tc goal.FStar_Tactics_Types.context tm)
in (bind uu____3761 (fun uu____3784 -> (match (uu____3784) with
| (tm1, t, guard) -> begin
(

let uu____3796 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____3796) with
| (bs, comp) -> begin
(

let uu____3823 = (lemma_or_sq comp)
in (match (uu____3823) with
| FStar_Pervasives_Native.None -> begin
(fail "not a lemma or squashed function")
end
| FStar_Pervasives_Native.Some (pre, post) -> begin
(

let uu____3842 = (FStar_List.fold_left (fun uu____3888 uu____3889 -> (match (((uu____3888), (uu____3889))) with
| ((uvs, guard1, subst1), (b, aq)) -> begin
(

let b_t = (FStar_Syntax_Subst.subst subst1 b.FStar_Syntax_Syntax.sort)
in (

let uu____3992 = (is_unit_t b_t)
in (match (uu____3992) with
| true -> begin
(((((FStar_Syntax_Util.exp_unit), (aq)))::uvs), (guard1), ((FStar_Syntax_Syntax.NT (((b), (FStar_Syntax_Util.exp_unit))))::subst1))
end
| uu____4029 -> begin
(

let uu____4030 = (FStar_TypeChecker_Util.new_implicit_var "apply_lemma" goal.FStar_Tactics_Types.goal_ty.FStar_Syntax_Syntax.pos goal.FStar_Tactics_Types.context b_t)
in (match (uu____4030) with
| (u, uu____4060, g_u) -> begin
(

let uu____4074 = (FStar_TypeChecker_Rel.conj_guard guard1 g_u)
in (((((u), (aq)))::uvs), (uu____4074), ((FStar_Syntax_Syntax.NT (((b), (u))))::subst1)))
end))
end)))
end)) (([]), (guard), ([])) bs)
in (match (uu____3842) with
| (uvs, implicits, subst1) -> begin
(

let uvs1 = (FStar_List.rev uvs)
in (

let pre1 = (FStar_Syntax_Subst.subst subst1 pre)
in (

let post1 = (FStar_Syntax_Subst.subst subst1 post)
in (

let uu____4145 = (

let uu____4148 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero post1)
in (do_unify goal.FStar_Tactics_Types.context uu____4148 goal.FStar_Tactics_Types.goal_ty))
in (bind uu____4145 (fun b -> (match ((not (b))) with
| true -> begin
(

let uu____4156 = (tts goal.FStar_Tactics_Types.context tm1)
in (

let uu____4157 = (

let uu____4158 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero post1)
in (tts goal.FStar_Tactics_Types.context uu____4158))
in (

let uu____4159 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail3 "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)" uu____4156 uu____4157 uu____4159))))
end
| uu____4160 -> begin
(

let uu____4161 = (add_implicits implicits.FStar_TypeChecker_Env.implicits)
in (bind uu____4161 (fun uu____4166 -> (

let uu____4167 = (solve goal FStar_Syntax_Util.exp_unit)
in (bind uu____4167 (fun uu____4175 -> (

let is_free_uvar = (fun uv t1 -> (

let free_uvars = (

let uu____4186 = (

let uu____4193 = (FStar_Syntax_Free.uvars t1)
in (FStar_Util.set_elements uu____4193))
in (FStar_List.map FStar_Pervasives_Native.fst uu____4186))
in (FStar_List.existsML (fun u -> (FStar_Syntax_Unionfind.equiv u uv)) free_uvars)))
in (

let appears = (fun uv goals -> (FStar_List.existsML (fun g' -> (is_free_uvar uv g'.FStar_Tactics_Types.goal_ty)) goals))
in (

let checkone = (fun t1 goals -> (

let uu____4234 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____4234) with
| (hd1, uu____4250) -> begin
(match (hd1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____4272) -> begin
(appears uv goals)
end
| uu____4297 -> begin
false
end)
end)))
in (

let uu____4298 = (FStar_All.pipe_right implicits.FStar_TypeChecker_Env.implicits (mapM (fun uu____4370 -> (match (uu____4370) with
| (_msg, env, _uvar, term, typ, uu____4398) -> begin
(

let uu____4399 = (FStar_Syntax_Util.head_and_args term)
in (match (uu____4399) with
| (hd1, uu____4425) -> begin
(

let uu____4446 = (

let uu____4447 = (FStar_Syntax_Subst.compress hd1)
in uu____4447.FStar_Syntax_Syntax.n)
in (match (uu____4446) with
| FStar_Syntax_Syntax.Tm_uvar (uu____4460) -> begin
(

let uu____4477 = (

let uu____4486 = (

let uu____4489 = (

let uu___99_4490 = goal
in (

let uu____4491 = (bnorm goal.FStar_Tactics_Types.context term)
in (

let uu____4492 = (bnorm goal.FStar_Tactics_Types.context typ)
in {FStar_Tactics_Types.context = uu___99_4490.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu____4491; FStar_Tactics_Types.goal_ty = uu____4492; FStar_Tactics_Types.opts = uu___99_4490.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___99_4490.FStar_Tactics_Types.is_guard})))
in (uu____4489)::[])
in ((uu____4486), ([])))
in (ret uu____4477))
end
| uu____4505 -> begin
(

let g_typ = (

let uu____4507 = (FStar_Options.__temp_fast_implicits ())
in (match (uu____4507) with
| true -> begin
(FStar_TypeChecker_TcTerm.check_type_of_well_typed_term false env term typ)
end
| uu____4508 -> begin
(

let term1 = (bnorm env term)
in (

let uu____4510 = (

let uu____4517 = (FStar_TypeChecker_Env.set_expected_typ env typ)
in (env.FStar_TypeChecker_Env.type_of uu____4517 term1))
in (match (uu____4510) with
| (uu____4518, uu____4519, g_typ) -> begin
g_typ
end)))
end))
in (

let uu____4521 = (goal_from_guard "apply_lemma solved arg" goal.FStar_Tactics_Types.context g_typ goal.FStar_Tactics_Types.opts)
in (bind uu____4521 (fun uu___63_4537 -> (match (uu___63_4537) with
| FStar_Pervasives_Native.None -> begin
(ret (([]), ([])))
end
| FStar_Pervasives_Native.Some (g) -> begin
(ret (([]), ((g)::[])))
end)))))
end))
end))
end))))
in (bind uu____4298 (fun goals_ -> (

let sub_goals = (

let uu____4605 = (FStar_List.map FStar_Pervasives_Native.fst goals_)
in (FStar_List.flatten uu____4605))
in (

let smt_goals = (

let uu____4627 = (FStar_List.map FStar_Pervasives_Native.snd goals_)
in (FStar_List.flatten uu____4627))
in (

let rec filter' = (fun a f xs -> (match (xs) with
| [] -> begin
[]
end
| (x)::xs1 -> begin
(

let uu____4682 = (f x xs1)
in (match (uu____4682) with
| true -> begin
(

let uu____4685 = (filter' () f xs1)
in (x)::uu____4685)
end
| uu____4688 -> begin
(filter' () f xs1)
end))
end))
in (

let sub_goals1 = (Obj.magic ((filter' () (fun a438 a439 -> ((Obj.magic ((fun g goals -> (

let uu____4699 = (checkone g.FStar_Tactics_Types.witness goals)
in (not (uu____4699)))))) a438 a439)) (Obj.magic (sub_goals)))))
in (

let uu____4700 = (proc_guard "apply_lemma guard" goal.FStar_Tactics_Types.context guard goal.FStar_Tactics_Types.opts)
in (bind uu____4700 (fun uu____4705 -> (

let uu____4706 = (

let uu____4709 = (

let uu____4710 = (

let uu____4711 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero pre1)
in (istrivial goal.FStar_Tactics_Types.context uu____4711))
in (not (uu____4710)))
in (match (uu____4709) with
| true -> begin
(add_irrelevant_goal "apply_lemma precondition" goal.FStar_Tactics_Types.context pre1 goal.FStar_Tactics_Types.opts)
end
| uu____4714 -> begin
(ret ())
end))
in (bind uu____4706 (fun uu____4717 -> (

let uu____4718 = (add_smt_goals smt_goals)
in (bind uu____4718 (fun uu____4722 -> (add_goals sub_goals1))))))))))))))))))))))))))
end)))))))
end))
end))
end))
end))))))))))
in (focus uu____3734))
in (FStar_All.pipe_left (wrap_err "apply_lemma") uu____3731)))


let destruct_eq' : FStar_Reflection_Data.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun typ -> (

let uu____4742 = (FStar_Syntax_Util.destruct_typ_as_formula typ)
in (match (uu____4742) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (l, (uu____4752)::((e1, uu____4754))::((e2, uu____4756))::[])) when (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) -> begin
FStar_Pervasives_Native.Some (((e1), (e2)))
end
| uu____4815 -> begin
FStar_Pervasives_Native.None
end)))


let destruct_eq : FStar_Reflection_Data.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun typ -> (

let uu____4837 = (destruct_eq' typ)
in (match (uu____4837) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4867 = (FStar_Syntax_Util.un_squash typ)
in (match (uu____4867) with
| FStar_Pervasives_Native.Some (typ1) -> begin
(destruct_eq' typ1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end)))


let split_env : FStar_Syntax_Syntax.bv  ->  env  ->  (env * FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.option = (fun bvar e -> (

let rec aux = (fun e1 -> (

let uu____4923 = (FStar_TypeChecker_Env.pop_bv e1)
in (match (uu____4923) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (bv', e') -> begin
(match ((FStar_Syntax_Syntax.bv_eq bvar bv')) with
| true -> begin
FStar_Pervasives_Native.Some (((e'), ([])))
end
| uu____4970 -> begin
(

let uu____4971 = (aux e')
in (FStar_Util.map_opt uu____4971 (fun uu____4995 -> (match (uu____4995) with
| (e'', bvs) -> begin
((e''), ((bv')::bvs))
end))))
end)
end)))
in (

let uu____5016 = (aux e)
in (FStar_Util.map_opt uu____5016 (fun uu____5040 -> (match (uu____5040) with
| (e', bvs) -> begin
((e'), ((FStar_List.rev bvs)))
end))))))


let push_bvs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_TypeChecker_Env.env = (fun e bvs -> (FStar_List.fold_left (fun e1 b -> (FStar_TypeChecker_Env.push_bv e1 b)) e bvs))


let subst_goal : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Tactics_Types.goal  ->  FStar_Tactics_Types.goal FStar_Pervasives_Native.option = (fun b1 b2 s g -> (

let uu____5095 = (split_env b1 g.FStar_Tactics_Types.context)
in (FStar_Util.map_opt uu____5095 (fun uu____5119 -> (match (uu____5119) with
| (e0, bvs) -> begin
(

let s1 = (fun bv -> (

let uu___100_5136 = bv
in (

let uu____5137 = (FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___100_5136.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___100_5136.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5137})))
in (

let bvs1 = (FStar_List.map s1 bvs)
in (

let c = (push_bvs e0 ((b2)::bvs1))
in (

let w = (FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness)
in (

let t = (FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty)
in (

let uu___101_5146 = g
in {FStar_Tactics_Types.context = c; FStar_Tactics_Types.witness = w; FStar_Tactics_Types.goal_ty = t; FStar_Tactics_Types.opts = uu___101_5146.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___101_5146.FStar_Tactics_Types.is_guard}))))))
end)))))


let rewrite : FStar_Syntax_Syntax.binder  ->  Prims.unit tac = (fun h -> (

let uu____5154 = (cur_goal ())
in (bind uu____5154 (fun goal -> (

let uu____5162 = h
in (match (uu____5162) with
| (bv, uu____5166) -> begin
(mlog (fun uu____5170 -> (

let uu____5171 = (FStar_Syntax_Print.bv_to_string bv)
in (

let uu____5172 = (tts goal.FStar_Tactics_Types.context bv.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5171 uu____5172)))) (fun uu____5175 -> (

let uu____5176 = (split_env bv goal.FStar_Tactics_Types.context)
in (match (uu____5176) with
| FStar_Pervasives_Native.None -> begin
(fail "rewrite: binder not found in environment")
end
| FStar_Pervasives_Native.Some (e0, bvs) -> begin
(

let uu____5205 = (destruct_eq bv.FStar_Syntax_Syntax.sort)
in (match (uu____5205) with
| FStar_Pervasives_Native.Some (x, e) -> begin
(

let uu____5220 = (

let uu____5221 = (FStar_Syntax_Subst.compress x)
in uu____5221.FStar_Syntax_Syntax.n)
in (match (uu____5220) with
| FStar_Syntax_Syntax.Tm_name (x1) -> begin
(

let s = (FStar_Syntax_Syntax.NT (((x1), (e))))::[]
in (

let s1 = (fun bv1 -> (

let uu___102_5234 = bv1
in (

let uu____5235 = (FStar_Syntax_Subst.subst s bv1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___102_5234.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___102_5234.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5235})))
in (

let bvs1 = (FStar_List.map s1 bvs)
in (

let uu____5241 = (

let uu___103_5242 = goal
in (

let uu____5243 = (push_bvs e0 ((bv)::bvs1))
in (

let uu____5244 = (FStar_Syntax_Subst.subst s goal.FStar_Tactics_Types.witness)
in (

let uu____5245 = (FStar_Syntax_Subst.subst s goal.FStar_Tactics_Types.goal_ty)
in {FStar_Tactics_Types.context = uu____5243; FStar_Tactics_Types.witness = uu____5244; FStar_Tactics_Types.goal_ty = uu____5245; FStar_Tactics_Types.opts = uu___103_5242.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___103_5242.FStar_Tactics_Types.is_guard}))))
in (replace_cur uu____5241)))))
end
| uu____5246 -> begin
(fail "rewrite: Not an equality hypothesis with a variable on the LHS")
end))
end
| uu____5247 -> begin
(fail "rewrite: Not an equality hypothesis")
end))
end))))
end))))))


let rename_to : FStar_Syntax_Syntax.binder  ->  Prims.string  ->  Prims.unit tac = (fun b s -> (

let uu____5264 = (cur_goal ())
in (bind uu____5264 (fun goal -> (

let uu____5275 = b
in (match (uu____5275) with
| (bv, uu____5279) -> begin
(

let bv' = (FStar_Syntax_Syntax.freshen_bv (

let uu___104_5283 = bv
in {FStar_Syntax_Syntax.ppname = (FStar_Ident.mk_ident ((s), (bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange))); FStar_Syntax_Syntax.index = uu___104_5283.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___104_5283.FStar_Syntax_Syntax.sort}))
in (

let s1 = (

let uu____5287 = (

let uu____5288 = (

let uu____5295 = (FStar_Syntax_Syntax.bv_to_name bv')
in ((bv), (uu____5295)))
in FStar_Syntax_Syntax.NT (uu____5288))
in (uu____5287)::[])
in (

let uu____5296 = (subst_goal bv bv' s1 goal)
in (match (uu____5296) with
| FStar_Pervasives_Native.None -> begin
(fail "rename_to: binder not found in environment")
end
| FStar_Pervasives_Native.Some (goal1) -> begin
(replace_cur goal1)
end))))
end))))))


let binder_retype : FStar_Syntax_Syntax.binder  ->  Prims.unit tac = (fun b -> (

let uu____5309 = (cur_goal ())
in (bind uu____5309 (fun goal -> (

let uu____5318 = b
in (match (uu____5318) with
| (bv, uu____5322) -> begin
(

let uu____5323 = (split_env bv goal.FStar_Tactics_Types.context)
in (match (uu____5323) with
| FStar_Pervasives_Native.None -> begin
(fail "binder_retype: binder is not present in environment")
end
| FStar_Pervasives_Native.Some (e0, bvs) -> begin
(

let uu____5352 = (FStar_Syntax_Util.type_u ())
in (match (uu____5352) with
| (ty, u) -> begin
(

let uu____5361 = (new_uvar "binder_retype" e0 ty)
in (bind uu____5361 (fun t' -> (

let bv'' = (

let uu___105_5371 = bv
in {FStar_Syntax_Syntax.ppname = uu___105_5371.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___105_5371.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t'})
in (

let s = (

let uu____5375 = (

let uu____5376 = (

let uu____5383 = (FStar_Syntax_Syntax.bv_to_name bv'')
in ((bv), (uu____5383)))
in FStar_Syntax_Syntax.NT (uu____5376))
in (uu____5375)::[])
in (

let bvs1 = (FStar_List.map (fun b1 -> (

let uu___106_5391 = b1
in (

let uu____5392 = (FStar_Syntax_Subst.subst s b1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___106_5391.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___106_5391.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5392}))) bvs)
in (

let env' = (push_bvs e0 ((bv'')::bvs1))
in (bind __dismiss (fun uu____5398 -> (

let uu____5399 = (

let uu____5402 = (

let uu____5405 = (

let uu___107_5406 = goal
in (

let uu____5407 = (FStar_Syntax_Subst.subst s goal.FStar_Tactics_Types.witness)
in (

let uu____5408 = (FStar_Syntax_Subst.subst s goal.FStar_Tactics_Types.goal_ty)
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = uu____5407; FStar_Tactics_Types.goal_ty = uu____5408; FStar_Tactics_Types.opts = uu___107_5406.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___107_5406.FStar_Tactics_Types.is_guard})))
in (uu____5405)::[])
in (add_goals uu____5402))
in (bind uu____5399 (fun uu____5411 -> (

let uu____5412 = (FStar_Syntax_Util.mk_eq2 (FStar_Syntax_Syntax.U_succ (u)) ty bv.FStar_Syntax_Syntax.sort t')
in (add_irrelevant_goal "binder_retype equation" e0 uu____5412 goal.FStar_Tactics_Types.opts))))))))))))))
end))
end))
end))))))


let norm_binder_type : FStar_Syntax_Embeddings.norm_step Prims.list  ->  FStar_Syntax_Syntax.binder  ->  Prims.unit tac = (fun s b -> (

let uu____5427 = (cur_goal ())
in (bind uu____5427 (fun goal -> (

let uu____5436 = b
in (match (uu____5436) with
| (bv, uu____5440) -> begin
(

let uu____5441 = (split_env bv goal.FStar_Tactics_Types.context)
in (match (uu____5441) with
| FStar_Pervasives_Native.None -> begin
(fail "binder_retype: binder is not present in environment")
end
| FStar_Pervasives_Native.Some (e0, bvs) -> begin
(

let steps = (

let uu____5473 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldTac)::[]) uu____5473))
in (

let sort' = (normalize steps e0 bv.FStar_Syntax_Syntax.sort)
in (

let bv' = (

let uu___108_5478 = bv
in {FStar_Syntax_Syntax.ppname = uu___108_5478.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___108_5478.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort'})
in (

let env' = (push_bvs e0 ((bv')::bvs))
in (replace_cur (

let uu___109_5482 = goal
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = uu___109_5482.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___109_5482.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___109_5482.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___109_5482.FStar_Tactics_Types.is_guard}))))))
end))
end))))))


let revert : Prims.unit  ->  Prims.unit tac = (fun uu____5487 -> (

let uu____5490 = (cur_goal ())
in (bind uu____5490 (fun goal -> (

let uu____5496 = (FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context)
in (match (uu____5496) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot revert; empty context")
end
| FStar_Pervasives_Native.Some (x, env') -> begin
(

let typ' = (

let uu____5518 = (FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty)
in (FStar_Syntax_Util.arrow ((((x), (FStar_Pervasives_Native.None)))::[]) uu____5518))
in (

let w' = (FStar_Syntax_Util.abs ((((x), (FStar_Pervasives_Native.None)))::[]) goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None)
in (replace_cur (

let uu___110_5552 = goal
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = w'; FStar_Tactics_Types.goal_ty = typ'; FStar_Tactics_Types.opts = uu___110_5552.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___110_5552.FStar_Tactics_Types.is_guard}))))
end))))))


let free_in : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun bv t -> (

let uu____5559 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_mem bv uu____5559)))


let rec clear : FStar_Syntax_Syntax.binder  ->  Prims.unit tac = (fun b -> (

let bv = (FStar_Pervasives_Native.fst b)
in (

let uu____5570 = (cur_goal ())
in (bind uu____5570 (fun goal -> (mlog (fun uu____5578 -> (

let uu____5579 = (FStar_Syntax_Print.binder_to_string b)
in (

let uu____5580 = (

let uu____5581 = (

let uu____5582 = (FStar_TypeChecker_Env.all_binders goal.FStar_Tactics_Types.context)
in (FStar_All.pipe_right uu____5582 FStar_List.length))
in (FStar_All.pipe_right uu____5581 FStar_Util.string_of_int))
in (FStar_Util.print2 "Clear of (%s), env has %s binders\n" uu____5579 uu____5580)))) (fun uu____5593 -> (

let uu____5594 = (split_env bv goal.FStar_Tactics_Types.context)
in (match (uu____5594) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot clear; binder not in environment")
end
| FStar_Pervasives_Native.Some (e', bvs) -> begin
(

let rec check1 = (fun bvs1 -> (match (bvs1) with
| [] -> begin
(ret ())
end
| (bv')::bvs2 -> begin
(

let uu____5639 = (free_in bv bv'.FStar_Syntax_Syntax.sort)
in (match (uu____5639) with
| true -> begin
(

let uu____5642 = (

let uu____5643 = (FStar_Syntax_Print.bv_to_string bv')
in (FStar_Util.format1 "Cannot clear; binder present in the type of %s" uu____5643))
in (fail uu____5642))
end
| uu____5644 -> begin
(check1 bvs2)
end))
end))
in (

let uu____5645 = (free_in bv goal.FStar_Tactics_Types.goal_ty)
in (match (uu____5645) with
| true -> begin
(fail "Cannot clear; binder present in goal")
end
| uu____5648 -> begin
(

let uu____5649 = (check1 bvs)
in (bind uu____5649 (fun uu____5655 -> (

let env' = (push_bvs e' bvs)
in (

let uu____5657 = (new_uvar "clear.witness" env' goal.FStar_Tactics_Types.goal_ty)
in (bind uu____5657 (fun ut -> (

let uu____5663 = (do_unify goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.witness ut)
in (bind uu____5663 (fun b1 -> (match (b1) with
| true -> begin
(replace_cur (

let uu___111_5672 = goal
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = ut; FStar_Tactics_Types.goal_ty = uu___111_5672.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___111_5672.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___111_5672.FStar_Tactics_Types.is_guard}))
end
| uu____5673 -> begin
(fail "Cannot clear; binder appears in witness")
end)))))))))))
end)))
end)))))))))


let clear_top : Prims.unit  ->  Prims.unit tac = (fun uu____5678 -> (

let uu____5681 = (cur_goal ())
in (bind uu____5681 (fun goal -> (

let uu____5687 = (FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context)
in (match (uu____5687) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot clear; empty context")
end
| FStar_Pervasives_Native.Some (x, uu____5701) -> begin
(

let uu____5706 = (FStar_Syntax_Syntax.mk_binder x)
in (clear uu____5706))
end))))))


let prune : Prims.string  ->  Prims.unit tac = (fun s -> (

let uu____5714 = (cur_goal ())
in (bind uu____5714 (fun g -> (

let ctx = g.FStar_Tactics_Types.context
in (

let ctx' = (FStar_TypeChecker_Env.rem_proof_ns ctx (FStar_Ident.path_of_text s))
in (

let g' = (

let uu___112_5725 = g
in {FStar_Tactics_Types.context = ctx'; FStar_Tactics_Types.witness = uu___112_5725.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___112_5725.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___112_5725.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___112_5725.FStar_Tactics_Types.is_guard})
in (bind __dismiss (fun uu____5727 -> (add_goals ((g')::[])))))))))))


let addns : Prims.string  ->  Prims.unit tac = (fun s -> (

let uu____5735 = (cur_goal ())
in (bind uu____5735 (fun g -> (

let ctx = g.FStar_Tactics_Types.context
in (

let ctx' = (FStar_TypeChecker_Env.add_proof_ns ctx (FStar_Ident.path_of_text s))
in (

let g' = (

let uu___113_5746 = g
in {FStar_Tactics_Types.context = ctx'; FStar_Tactics_Types.witness = uu___113_5746.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___113_5746.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___113_5746.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___113_5746.FStar_Tactics_Types.is_guard})
in (bind __dismiss (fun uu____5748 -> (add_goals ((g')::[])))))))))))


let rec tac_fold_env : FStar_Tactics_Types.direction  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac)  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun d f env t -> (

let tn = (

let uu____5780 = (FStar_Syntax_Subst.compress t)
in uu____5780.FStar_Syntax_Syntax.n)
in (

let uu____5783 = (match ((Prims.op_Equality d FStar_Tactics_Types.TopDown)) with
| true -> begin
(f env (

let uu___117_5789 = t
in {FStar_Syntax_Syntax.n = tn; FStar_Syntax_Syntax.pos = uu___117_5789.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___117_5789.FStar_Syntax_Syntax.vars}))
end
| uu____5790 -> begin
(ret t)
end)
in (bind uu____5783 (fun t1 -> (

let ff = (tac_fold_env d f env)
in (

let tn1 = (

let uu____5803 = (

let uu____5804 = (FStar_Syntax_Subst.compress t1)
in uu____5804.FStar_Syntax_Syntax.n)
in (match (uu____5803) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____5831 = (ff hd1)
in (bind uu____5831 (fun hd2 -> (

let fa = (fun uu____5851 -> (match (uu____5851) with
| (a, q) -> begin
(

let uu____5864 = (ff a)
in (bind uu____5864 (fun a1 -> (ret ((a1), (q))))))
end))
in (

let uu____5877 = (mapM fa args)
in (bind uu____5877 (fun args1 -> (ret (FStar_Syntax_Syntax.Tm_app (((hd2), (args1))))))))))))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, k) -> begin
(

let uu____5937 = (FStar_Syntax_Subst.open_term bs t2)
in (match (uu____5937) with
| (bs1, t') -> begin
(

let uu____5946 = (

let uu____5949 = (FStar_TypeChecker_Env.push_binders env bs1)
in (tac_fold_env d f uu____5949 t'))
in (bind uu____5946 (fun t'' -> (

let uu____5953 = (

let uu____5954 = (

let uu____5971 = (FStar_Syntax_Subst.close_binders bs1)
in (

let uu____5972 = (FStar_Syntax_Subst.close bs1 t'')
in ((uu____5971), (uu____5972), (k))))
in FStar_Syntax_Syntax.Tm_abs (uu____5954))
in (ret uu____5953)))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(ret tn)
end
| FStar_Syntax_Syntax.Tm_match (hd1, brs) -> begin
(

let uu____6031 = (ff hd1)
in (bind uu____6031 (fun hd2 -> (

let ffb = (fun br -> (

let uu____6044 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____6044) with
| (pat, w, e) -> begin
(

let uu____6066 = (ff e)
in (bind uu____6066 (fun e1 -> (

let br1 = (FStar_Syntax_Subst.close_branch ((pat), (w), (e1)))
in (ret br1)))))
end)))
in (

let uu____6079 = (mapM ffb brs)
in (bind uu____6079 (fun brs1 -> (ret (FStar_Syntax_Syntax.Tm_match (((hd2), (brs1))))))))))))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (bv); FStar_Syntax_Syntax.lbunivs = uu____6093; FStar_Syntax_Syntax.lbtyp = uu____6094; FStar_Syntax_Syntax.lbeff = uu____6095; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu____6097; FStar_Syntax_Syntax.lbpos = uu____6098})::[]), e) -> begin
(

let lb = (

let uu____6123 = (

let uu____6124 = (FStar_Syntax_Subst.compress t1)
in uu____6124.FStar_Syntax_Syntax.n)
in (match (uu____6123) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), uu____6128) -> begin
lb
end
| uu____6141 -> begin
(failwith "impossible")
end))
in (

let fflb = (fun lb1 -> (

let uu____6148 = (ff lb1.FStar_Syntax_Syntax.lbdef)
in (bind uu____6148 (fun def1 -> (ret (

let uu___114_6154 = lb1
in {FStar_Syntax_Syntax.lbname = uu___114_6154.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___114_6154.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___114_6154.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___114_6154.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def1; FStar_Syntax_Syntax.lbattrs = uu___114_6154.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___114_6154.FStar_Syntax_Syntax.lbpos}))))))
in (

let uu____6155 = (fflb lb)
in (bind uu____6155 (fun lb1 -> (

let uu____6164 = (

let uu____6169 = (

let uu____6170 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____6170)::[])
in (FStar_Syntax_Subst.open_term uu____6169 e))
in (match (uu____6164) with
| (bs, e1) -> begin
(

let uu____6175 = (ff e1)
in (bind uu____6175 (fun e2 -> (

let e3 = (FStar_Syntax_Subst.close bs e2)
in (ret (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e3)))))))))
end)))))))
end
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e) -> begin
(

let fflb = (fun lb -> (

let uu____6212 = (ff lb.FStar_Syntax_Syntax.lbdef)
in (bind uu____6212 (fun def -> (ret (

let uu___115_6218 = lb
in {FStar_Syntax_Syntax.lbname = uu___115_6218.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___115_6218.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___115_6218.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___115_6218.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu___115_6218.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___115_6218.FStar_Syntax_Syntax.lbpos}))))))
in (

let uu____6219 = (FStar_Syntax_Subst.open_let_rec lbs e)
in (match (uu____6219) with
| (lbs1, e1) -> begin
(

let uu____6234 = (mapM fflb lbs1)
in (bind uu____6234 (fun lbs2 -> (

let uu____6246 = (ff e1)
in (bind uu____6246 (fun e2 -> (

let uu____6254 = (FStar_Syntax_Subst.close_let_rec lbs2 e2)
in (match (uu____6254) with
| (lbs3, e3) -> begin
(ret (FStar_Syntax_Syntax.Tm_let (((((true), (lbs3))), (e3)))))
end))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, asc, eff) -> begin
(

let uu____6320 = (ff t2)
in (bind uu____6320 (fun t3 -> (ret (FStar_Syntax_Syntax.Tm_ascribed (((t3), (asc), (eff))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t2, m) -> begin
(

let uu____6349 = (ff t2)
in (bind uu____6349 (fun t3 -> (ret (FStar_Syntax_Syntax.Tm_meta (((t3), (m))))))))
end
| uu____6354 -> begin
(ret tn)
end))
in (bind tn1 (fun tn2 -> (

let t' = (

let uu___116_6361 = t1
in {FStar_Syntax_Syntax.n = tn2; FStar_Syntax_Syntax.pos = uu___116_6361.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___116_6361.FStar_Syntax_Syntax.vars})
in (match ((Prims.op_Equality d FStar_Tactics_Types.BottomUp)) with
| true -> begin
(f env t')
end
| uu____6364 -> begin
(ret t')
end)))))))))))


let pointwise_rec : FStar_Tactics_Types.proofstate  ->  Prims.unit tac  ->  FStar_Options.optionstate  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun ps tau opts env t -> (

let uu____6390 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____6390) with
| (t1, lcomp, g) -> begin
(

let uu____6402 = ((

let uu____6405 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp)
in (not (uu____6405))) || (

let uu____6407 = (FStar_TypeChecker_Rel.is_trivial g)
in (not (uu____6407))))
in (match (uu____6402) with
| true -> begin
(ret t1)
end
| uu____6410 -> begin
(

let rewrite_eq = (

let typ = lcomp.FStar_Syntax_Syntax.res_typ
in (

let uu____6417 = (new_uvar "pointwise_rec" env typ)
in (bind uu____6417 (fun ut -> ((log ps (fun uu____6428 -> (

let uu____6429 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6430 = (FStar_Syntax_Print.term_to_string ut)
in (FStar_Util.print2 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n" uu____6429 uu____6430)))));
(

let uu____6431 = (

let uu____6434 = (

let uu____6435 = (FStar_TypeChecker_TcTerm.universe_of env typ)
in (FStar_Syntax_Util.mk_eq2 uu____6435 typ t1 ut))
in (add_irrelevant_goal "pointwise_rec equation" env uu____6434 opts))
in (bind uu____6431 (fun uu____6438 -> (

let uu____6439 = (bind tau (fun uu____6445 -> (

let ut1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env ut)
in ((log ps (fun uu____6451 -> (

let uu____6452 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6453 = (FStar_Syntax_Print.term_to_string ut1)
in (FStar_Util.print2 "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n" uu____6452 uu____6453)))));
(ret ut1);
))))
in (focus uu____6439)))));
)))))
in (

let uu____6454 = (trytac' rewrite_eq)
in (bind uu____6454 (fun x -> (match (x) with
| FStar_Util.Inl ("SKIP") -> begin
(ret t1)
end
| FStar_Util.Inl (e) -> begin
(fail e)
end
| FStar_Util.Inr (x1) -> begin
(ret x1)
end)))))
end))
end)))


type ctrl =
FStar_BigInt.t


let keepGoing : ctrl = FStar_BigInt.zero


let proceedToNextSubtree : FStar_BigInt.bigint = FStar_BigInt.one


let globalStop : FStar_BigInt.bigint = (FStar_BigInt.succ_big_int FStar_BigInt.one)


type rewrite_result =
Prims.bool


let skipThisTerm : Prims.bool = false


let rewroteThisTerm : Prims.bool = true


type 'a ctrl_tac =
('a * ctrl) tac


let rec ctrl_tac_fold : (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term ctrl_tac)  ->  env  ->  ctrl  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term ctrl_tac = (fun f env ctrl t -> (

let keep_going = (fun c -> (match ((Prims.op_Equality c proceedToNextSubtree)) with
| true -> begin
keepGoing
end
| uu____6546 -> begin
c
end))
in (

let maybe_continue = (fun ctrl1 t1 k -> (match ((Prims.op_Equality ctrl1 globalStop)) with
| true -> begin
(ret ((t1), (globalStop)))
end
| uu____6590 -> begin
(match ((Prims.op_Equality ctrl1 proceedToNextSubtree)) with
| true -> begin
(ret ((t1), (keepGoing)))
end
| uu____6601 -> begin
(k t1)
end)
end))
in (

let uu____6602 = (FStar_Syntax_Subst.compress t)
in (maybe_continue ctrl uu____6602 (fun t1 -> (

let uu____6606 = (f env (

let uu___120_6615 = t1
in {FStar_Syntax_Syntax.n = t1.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = uu___120_6615.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___120_6615.FStar_Syntax_Syntax.vars}))
in (bind uu____6606 (fun uu____6627 -> (match (uu____6627) with
| (t2, ctrl1) -> begin
(maybe_continue ctrl1 t2 (fun t3 -> (

let uu____6646 = (

let uu____6647 = (FStar_Syntax_Subst.compress t3)
in uu____6647.FStar_Syntax_Syntax.n)
in (match (uu____6646) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____6680 = (ctrl_tac_fold f env ctrl1 hd1)
in (bind uu____6680 (fun uu____6705 -> (match (uu____6705) with
| (hd2, ctrl2) -> begin
(

let ctrl3 = (keep_going ctrl2)
in (

let uu____6721 = (ctrl_tac_fold_args f env ctrl3 args)
in (bind uu____6721 (fun uu____6748 -> (match (uu____6748) with
| (args1, ctrl4) -> begin
(ret (((

let uu___118_6778 = t3
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app (((hd2), (args1))); FStar_Syntax_Syntax.pos = uu___118_6778.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___118_6778.FStar_Syntax_Syntax.vars})), (ctrl4)))
end)))))
end))))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t4, k) -> begin
(

let uu____6804 = (FStar_Syntax_Subst.open_term bs t4)
in (match (uu____6804) with
| (bs1, t') -> begin
(

let uu____6819 = (

let uu____6826 = (FStar_TypeChecker_Env.push_binders env bs1)
in (ctrl_tac_fold f uu____6826 ctrl1 t'))
in (bind uu____6819 (fun uu____6844 -> (match (uu____6844) with
| (t'', ctrl2) -> begin
(

let uu____6859 = (

let uu____6866 = (

let uu___119_6869 = t4
in (

let uu____6872 = (

let uu____6873 = (

let uu____6890 = (FStar_Syntax_Subst.close_binders bs1)
in (

let uu____6891 = (FStar_Syntax_Subst.close bs1 t'')
in ((uu____6890), (uu____6891), (k))))
in FStar_Syntax_Syntax.Tm_abs (uu____6873))
in {FStar_Syntax_Syntax.n = uu____6872; FStar_Syntax_Syntax.pos = uu___119_6869.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___119_6869.FStar_Syntax_Syntax.vars}))
in ((uu____6866), (ctrl2)))
in (ret uu____6859))
end))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(ret ((t3), (ctrl1)))
end
| uu____6924 -> begin
(ret ((t3), (ctrl1)))
end))))
end))))))))))
and ctrl_tac_fold_args : (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term ctrl_tac)  ->  env  ->  ctrl  ->  FStar_Syntax_Syntax.arg Prims.list  ->  FStar_Syntax_Syntax.arg Prims.list ctrl_tac = (fun f env ctrl ts -> (match (ts) with
| [] -> begin
(ret (([]), (ctrl)))
end
| ((t, q))::ts1 -> begin
(

let uu____6975 = (ctrl_tac_fold f env ctrl t)
in (bind uu____6975 (fun uu____7003 -> (match (uu____7003) with
| (t1, ctrl1) -> begin
(

let uu____7022 = (ctrl_tac_fold_args f env ctrl1 ts1)
in (bind uu____7022 (fun uu____7053 -> (match (uu____7053) with
| (ts2, ctrl2) -> begin
(ret (((((t1), (q)))::ts2), (ctrl2)))
end))))
end))))
end))


let rewrite_rec : FStar_Tactics_Types.proofstate  ->  (FStar_Syntax_Syntax.term  ->  rewrite_result ctrl_tac)  ->  Prims.unit tac  ->  FStar_Options.optionstate  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term ctrl_tac = (fun ps ctrl rewriter opts env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let uu____7137 = (

let uu____7144 = (add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true opts)
in (bind uu____7144 (fun uu____7153 -> (

let uu____7154 = (ctrl t1)
in (bind uu____7154 (fun res -> (

let uu____7177 = (trivial ())
in (bind uu____7177 (fun uu____7185 -> (ret res))))))))))
in (bind uu____7137 (fun uu____7201 -> (match (uu____7201) with
| (should_rewrite, ctrl1) -> begin
(match ((not (should_rewrite))) with
| true -> begin
(ret ((t1), (ctrl1)))
end
| uu____7224 -> begin
(

let uu____7225 = (FStar_TypeChecker_TcTerm.tc_term env t1)
in (match (uu____7225) with
| (t2, lcomp, g) -> begin
(

let uu____7241 = ((

let uu____7244 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp)
in (not (uu____7244))) || (

let uu____7246 = (FStar_TypeChecker_Rel.is_trivial g)
in (not (uu____7246))))
in (match (uu____7241) with
| true -> begin
(ret ((t2), (globalStop)))
end
| uu____7257 -> begin
(

let typ = lcomp.FStar_Syntax_Syntax.res_typ
in (

let uu____7261 = (new_uvar "pointwise_rec" env typ)
in (bind uu____7261 (fun ut -> ((log ps (fun uu____7276 -> (

let uu____7277 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____7278 = (FStar_Syntax_Print.term_to_string ut)
in (FStar_Util.print2 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n" uu____7277 uu____7278)))));
(

let uu____7279 = (

let uu____7282 = (

let uu____7283 = (FStar_TypeChecker_TcTerm.universe_of env typ)
in (FStar_Syntax_Util.mk_eq2 uu____7283 typ t2 ut))
in (add_irrelevant_goal "rewrite_rec equation" env uu____7282 opts))
in (bind uu____7279 (fun uu____7290 -> (

let uu____7291 = (bind rewriter (fun uu____7305 -> (

let ut1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env ut)
in ((log ps (fun uu____7311 -> (

let uu____7312 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____7313 = (FStar_Syntax_Print.term_to_string ut1)
in (FStar_Util.print2 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n" uu____7312 uu____7313)))));
(ret ((ut1), (ctrl1)));
))))
in (focus uu____7291)))));
)))))
end))
end))
end)
end))))))


let topdown_rewrite : (FStar_Syntax_Syntax.term  ->  (Prims.bool * FStar_BigInt.t) tac)  ->  Prims.unit tac  ->  Prims.unit tac = (fun ctrl rewriter -> (bind get (fun ps -> (

let uu____7357 = (match (ps.FStar_Tactics_Types.goals) with
| (g)::gs -> begin
((g), (gs))
end
| [] -> begin
(failwith "Pointwise: no goals")
end)
in (match (uu____7357) with
| (g, gs) -> begin
(

let gt1 = g.FStar_Tactics_Types.goal_ty
in ((log ps (fun uu____7394 -> (

let uu____7395 = (FStar_Syntax_Print.term_to_string gt1)
in (FStar_Util.print1 "Pointwise starting with %s\n" uu____7395))));
(bind dismiss_all (fun uu____7398 -> (

let uu____7399 = (ctrl_tac_fold (rewrite_rec ps ctrl rewriter g.FStar_Tactics_Types.opts) g.FStar_Tactics_Types.context keepGoing gt1)
in (bind uu____7399 (fun uu____7417 -> (match (uu____7417) with
| (gt', uu____7425) -> begin
((log ps (fun uu____7429 -> (

let uu____7430 = (FStar_Syntax_Print.term_to_string gt')
in (FStar_Util.print1 "Pointwise seems to have succeded with %s\n" uu____7430))));
(

let uu____7431 = (push_goals gs)
in (bind uu____7431 (fun uu____7435 -> (add_goals (((

let uu___121_7437 = g
in {FStar_Tactics_Types.context = uu___121_7437.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___121_7437.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = gt'; FStar_Tactics_Types.opts = uu___121_7437.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___121_7437.FStar_Tactics_Types.is_guard}))::[])))));
)
end))))));
))
end)))))


let pointwise : FStar_Tactics_Types.direction  ->  Prims.unit tac  ->  Prims.unit tac = (fun d tau -> (bind get (fun ps -> (

let uu____7459 = (match (ps.FStar_Tactics_Types.goals) with
| (g)::gs -> begin
((g), (gs))
end
| [] -> begin
(failwith "Pointwise: no goals")
end)
in (match (uu____7459) with
| (g, gs) -> begin
(

let gt1 = g.FStar_Tactics_Types.goal_ty
in ((log ps (fun uu____7496 -> (

let uu____7497 = (FStar_Syntax_Print.term_to_string gt1)
in (FStar_Util.print1 "Pointwise starting with %s\n" uu____7497))));
(bind dismiss_all (fun uu____7500 -> (

let uu____7501 = (tac_fold_env d (pointwise_rec ps tau g.FStar_Tactics_Types.opts) g.FStar_Tactics_Types.context gt1)
in (bind uu____7501 (fun gt' -> ((log ps (fun uu____7511 -> (

let uu____7512 = (FStar_Syntax_Print.term_to_string gt')
in (FStar_Util.print1 "Pointwise seems to have succeded with %s\n" uu____7512))));
(

let uu____7513 = (push_goals gs)
in (bind uu____7513 (fun uu____7517 -> (add_goals (((

let uu___122_7519 = g
in {FStar_Tactics_Types.context = uu___122_7519.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___122_7519.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = gt'; FStar_Tactics_Types.opts = uu___122_7519.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___122_7519.FStar_Tactics_Types.is_guard}))::[])))));
))))));
))
end)))))


let trefl : Prims.unit  ->  Prims.unit tac = (fun uu____7524 -> (

let uu____7527 = (cur_goal ())
in (bind uu____7527 (fun g -> (

let uu____7545 = (FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty)
in (match (uu____7545) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____7557 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____7557) with
| (hd1, args) -> begin
(

let uu____7590 = (

let uu____7603 = (

let uu____7604 = (FStar_Syntax_Util.un_uinst hd1)
in uu____7604.FStar_Syntax_Syntax.n)
in ((uu____7603), (args)))
in (match (uu____7590) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____7618)::((l, uu____7620))::((r, uu____7622))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid) -> begin
(

let uu____7669 = (do_unify g.FStar_Tactics_Types.context l r)
in (bind uu____7669 (fun b -> (match ((not (b))) with
| true -> begin
(

let uu____7678 = (tts g.FStar_Tactics_Types.context l)
in (

let uu____7679 = (tts g.FStar_Tactics_Types.context r)
in (fail2 "trefl: not a trivial equality (%s vs %s)" uu____7678 uu____7679)))
end
| uu____7680 -> begin
(solve g FStar_Syntax_Util.exp_unit)
end))))
end
| (hd2, uu____7682) -> begin
(

let uu____7699 = (tts g.FStar_Tactics_Types.context t)
in (fail1 "trefl: not an equality (%s)" uu____7699))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
(fail "not an irrelevant goal")
end))))))


let dup : Prims.unit  ->  Prims.unit tac = (fun uu____7706 -> (

let uu____7709 = (cur_goal ())
in (bind uu____7709 (fun g -> (

let uu____7715 = (new_uvar "dup" g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (bind uu____7715 (fun u -> (

let g' = (

let uu___123_7722 = g
in {FStar_Tactics_Types.context = uu___123_7722.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = u; FStar_Tactics_Types.goal_ty = uu___123_7722.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___123_7722.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___123_7722.FStar_Tactics_Types.is_guard})
in (bind __dismiss (fun uu____7725 -> (

let uu____7726 = (

let uu____7729 = (

let uu____7730 = (FStar_TypeChecker_TcTerm.universe_of g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (FStar_Syntax_Util.mk_eq2 uu____7730 g.FStar_Tactics_Types.goal_ty u g.FStar_Tactics_Types.witness))
in (add_irrelevant_goal "dup equation" g.FStar_Tactics_Types.context uu____7729 g.FStar_Tactics_Types.opts))
in (bind uu____7726 (fun uu____7733 -> (

let uu____7734 = (add_goals ((g')::[]))
in (bind uu____7734 (fun uu____7738 -> (ret ())))))))))))))))))


let flip : Prims.unit  ->  Prims.unit tac = (fun uu____7743 -> (bind get (fun ps -> (match (ps.FStar_Tactics_Types.goals) with
| (g1)::(g2)::gs -> begin
(set (

let uu___124_7760 = ps
in {FStar_Tactics_Types.main_context = uu___124_7760.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___124_7760.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___124_7760.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (g2)::(g1)::gs; FStar_Tactics_Types.smt_goals = uu___124_7760.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___124_7760.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___124_7760.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___124_7760.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___124_7760.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___124_7760.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___124_7760.FStar_Tactics_Types.freshness}))
end
| uu____7761 -> begin
(fail "flip: less than 2 goals")
end))))


let later : Prims.unit  ->  Prims.unit tac = (fun uu____7768 -> (bind get (fun ps -> (match (ps.FStar_Tactics_Types.goals) with
| [] -> begin
(ret ())
end
| (g)::gs -> begin
(set (

let uu___125_7781 = ps
in {FStar_Tactics_Types.main_context = uu___125_7781.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___125_7781.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___125_7781.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append gs ((g)::[])); FStar_Tactics_Types.smt_goals = uu___125_7781.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___125_7781.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___125_7781.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___125_7781.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___125_7781.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___125_7781.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___125_7781.FStar_Tactics_Types.freshness}))
end))))


let qed : Prims.unit  ->  Prims.unit tac = (fun uu____7786 -> (bind get (fun ps -> (match (ps.FStar_Tactics_Types.goals) with
| [] -> begin
(ret ())
end
| uu____7793 -> begin
(fail "Not done!")
end))))


let cases : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac = (fun t -> (

let uu____7811 = (

let uu____7818 = (cur_goal ())
in (bind uu____7818 (fun g -> (

let uu____7828 = (__tc g.FStar_Tactics_Types.context t)
in (bind uu____7828 (fun uu____7864 -> (match (uu____7864) with
| (t1, typ, guard) -> begin
(

let uu____7880 = (FStar_Syntax_Util.head_and_args typ)
in (match (uu____7880) with
| (hd1, args) -> begin
(

let uu____7923 = (

let uu____7936 = (

let uu____7937 = (FStar_Syntax_Util.un_uinst hd1)
in uu____7937.FStar_Syntax_Syntax.n)
in ((uu____7936), (args)))
in (match (uu____7923) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____7956))::((q, uu____7958))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid) -> begin
(

let v_p = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p)
in (

let v_q = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None q)
in (

let g1 = (

let uu___126_7996 = g
in (

let uu____7997 = (FStar_TypeChecker_Env.push_bv g.FStar_Tactics_Types.context v_p)
in {FStar_Tactics_Types.context = uu____7997; FStar_Tactics_Types.witness = uu___126_7996.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___126_7996.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___126_7996.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___126_7996.FStar_Tactics_Types.is_guard}))
in (

let g2 = (

let uu___127_7999 = g
in (

let uu____8000 = (FStar_TypeChecker_Env.push_bv g.FStar_Tactics_Types.context v_q)
in {FStar_Tactics_Types.context = uu____8000; FStar_Tactics_Types.witness = uu___127_7999.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___127_7999.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___127_7999.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___127_7999.FStar_Tactics_Types.is_guard}))
in (bind __dismiss (fun uu____8007 -> (

let uu____8008 = (add_goals ((g1)::(g2)::[]))
in (bind uu____8008 (fun uu____8017 -> (

let uu____8018 = (

let uu____8023 = (FStar_Syntax_Syntax.bv_to_name v_p)
in (

let uu____8024 = (FStar_Syntax_Syntax.bv_to_name v_q)
in ((uu____8023), (uu____8024))))
in (ret uu____8018)))))))))))
end
| uu____8029 -> begin
(

let uu____8042 = (tts g.FStar_Tactics_Types.context typ)
in (fail1 "Not a disjunction: %s" uu____8042))
end))
end))
end)))))))
in (FStar_All.pipe_left (wrap_err "cases") uu____7811)))


let set_options : Prims.string  ->  Prims.unit tac = (fun s -> (

let uu____8070 = (cur_goal ())
in (bind uu____8070 (fun g -> ((FStar_Options.push ());
(

let uu____8083 = (FStar_Util.smap_copy g.FStar_Tactics_Types.opts)
in (FStar_Options.set uu____8083));
(

let res = (FStar_Options.set_options FStar_Options.Set s)
in (

let opts' = (FStar_Options.peek ())
in ((FStar_Options.pop ());
(match (res) with
| FStar_Getopt.Success -> begin
(

let g' = (

let uu___128_8090 = g
in {FStar_Tactics_Types.context = uu___128_8090.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___128_8090.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___128_8090.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = opts'; FStar_Tactics_Types.is_guard = uu___128_8090.FStar_Tactics_Types.is_guard})
in (replace_cur g'))
end
| FStar_Getopt.Error (err) -> begin
(fail2 "Setting options `%s` failed: %s" s err)
end
| FStar_Getopt.Help -> begin
(fail1 "Setting options `%s` failed (got `Help`?)" s)
end);
)));
)))))


let top_env : Prims.unit  ->  env tac = (fun uu____8096 -> (bind get (fun ps -> (FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context))))


let cur_env : Prims.unit  ->  env tac = (fun uu____8107 -> (

let uu____8110 = (cur_goal ())
in (bind uu____8110 (fun g -> (FStar_All.pipe_left ret g.FStar_Tactics_Types.context)))))


let cur_goal' : Prims.unit  ->  FStar_Syntax_Syntax.term tac = (fun uu____8121 -> (

let uu____8124 = (cur_goal ())
in (bind uu____8124 (fun g -> (FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)))))


let cur_witness : Prims.unit  ->  FStar_Syntax_Syntax.term tac = (fun uu____8135 -> (

let uu____8138 = (cur_goal ())
in (bind uu____8138 (fun g -> (FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)))))


let unquote : FStar_Reflection_Data.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun ty tm -> (

let uu____8155 = (

let uu____8158 = (cur_goal ())
in (bind uu____8158 (fun goal -> (

let env = (FStar_TypeChecker_Env.set_expected_typ goal.FStar_Tactics_Types.context ty)
in (

let uu____8166 = (__tc env tm)
in (bind uu____8166 (fun uu____8186 -> (match (uu____8186) with
| (tm1, typ, guard) -> begin
(

let uu____8198 = (proc_guard "unquote" env guard goal.FStar_Tactics_Types.opts)
in (bind uu____8198 (fun uu____8202 -> (ret tm1))))
end))))))))
in (FStar_All.pipe_left (wrap_err "unquote") uu____8155)))


let uvar_env : env  ->  FStar_Reflection_Data.typ FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term tac = (fun env ty -> (

let uu____8221 = (match (ty) with
| FStar_Pervasives_Native.Some (ty1) -> begin
(ret ty1)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8227 = (

let uu____8228 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8228))
in (new_uvar "uvar_env.2" env uu____8227))
end)
in (bind uu____8221 (fun typ -> (

let uu____8240 = (new_uvar "uvar_env" env typ)
in (bind uu____8240 (fun t -> (ret t))))))))


let unshelve : FStar_Syntax_Syntax.term  ->  Prims.unit tac = (fun t -> (

let uu____8252 = (bind get (fun ps -> (

let env = ps.FStar_Tactics_Types.main_context
in (

let opts = (match (ps.FStar_Tactics_Types.goals) with
| (g)::uu____8269 -> begin
g.FStar_Tactics_Types.opts
end
| uu____8272 -> begin
(FStar_Options.peek ())
end)
in (

let uu____8275 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____8275) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____8292, typ); FStar_Syntax_Syntax.pos = uu____8294; FStar_Syntax_Syntax.vars = uu____8295}, uu____8296) -> begin
(

let uu____8341 = (

let uu____8344 = (

let uu____8345 = (bnorm env t)
in (

let uu____8346 = (bnorm env typ)
in {FStar_Tactics_Types.context = env; FStar_Tactics_Types.witness = uu____8345; FStar_Tactics_Types.goal_ty = uu____8346; FStar_Tactics_Types.opts = opts; FStar_Tactics_Types.is_guard = false}))
in (uu____8344)::[])
in (add_goals uu____8341))
end
| uu____8347 -> begin
(fail "not a uvar")
end))))))
in (FStar_All.pipe_left (wrap_err "unshelve") uu____8252)))


let unify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun t1 t2 -> (bind get (fun ps -> (do_unify ps.FStar_Tactics_Types.main_context t1 t2))))


let launch_process : Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string tac = (fun prog args input -> (bind idtac (fun uu____8394 -> (

let uu____8395 = (FStar_Options.unsafe_tactic_exec ())
in (match (uu____8395) with
| true -> begin
(

let s = (FStar_Util.launch_process true "tactic_launch" prog args input (fun uu____8401 uu____8402 -> false))
in (ret s))
end
| uu____8403 -> begin
(fail "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
end)))))


let fresh_bv_named : Prims.string  ->  FStar_Reflection_Data.typ  ->  FStar_Syntax_Syntax.bv tac = (fun nm t -> (bind idtac (fun uu____8416 -> (

let uu____8417 = (FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t)
in (ret uu____8417)))))


let change : FStar_Reflection_Data.typ  ->  Prims.unit tac = (fun ty -> (

let uu____8425 = (mlog (fun uu____8430 -> (

let uu____8431 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.print1 "change: ty = %s\n" uu____8431))) (fun uu____8434 -> (

let uu____8435 = (cur_goal ())
in (bind uu____8435 (fun g -> (

let uu____8441 = (__tc g.FStar_Tactics_Types.context ty)
in (bind uu____8441 (fun uu____8461 -> (match (uu____8461) with
| (ty1, uu____8471, guard) -> begin
(

let uu____8473 = (proc_guard "change" g.FStar_Tactics_Types.context guard g.FStar_Tactics_Types.opts)
in (bind uu____8473 (fun uu____8478 -> (

let uu____8479 = (do_unify g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty ty1)
in (bind uu____8479 (fun bb -> (match (bb) with
| true -> begin
(replace_cur (

let uu___129_8488 = g
in {FStar_Tactics_Types.context = uu___129_8488.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___129_8488.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = ty1; FStar_Tactics_Types.opts = uu___129_8488.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___129_8488.FStar_Tactics_Types.is_guard}))
end
| uu____8489 -> begin
(

let steps = (FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.UnfoldTac)::(FStar_TypeChecker_Normalize.Unmeta)::[]
in (

let ng = (normalize steps g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (

let nty = (normalize steps g.FStar_Tactics_Types.context ty1)
in (

let uu____8495 = (do_unify g.FStar_Tactics_Types.context ng nty)
in (bind uu____8495 (fun b -> (match (b) with
| true -> begin
(replace_cur (

let uu___130_8504 = g
in {FStar_Tactics_Types.context = uu___130_8504.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___130_8504.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = ty1; FStar_Tactics_Types.opts = uu___130_8504.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___130_8504.FStar_Tactics_Types.is_guard}))
end
| uu____8505 -> begin
(fail "not convertible")
end)))))))
end)))))))
end)))))))))
in (FStar_All.pipe_left (wrap_err "change") uu____8425)))


let rec last : 'a . 'a Prims.list  ->  'a = (fun l -> (match (l) with
| [] -> begin
(failwith "last: empty list")
end
| (x)::[] -> begin
x
end
| (uu____8523)::xs -> begin
(last xs)
end))


let rec init : 'a . 'a Prims.list  ->  'a Prims.list = (fun l -> (match (l) with
| [] -> begin
(failwith "init: empty list")
end
| (x)::[] -> begin
[]
end
| (x)::xs -> begin
(

let uu____8548 = (init xs)
in (x)::uu____8548)
end))


let rec inspect : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.term_view tac = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let t2 = (FStar_Syntax_Util.un_uinst t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t3, uu____8563) -> begin
(inspect t3)
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var (bv)))
end
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar (bv)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar (fv)))
end
| FStar_Syntax_Syntax.Tm_app (hd1, []) -> begin
(failwith "inspect: empty arguments on Tm_app")
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____8620 = (last args)
in (match (uu____8620) with
| (a, q) -> begin
(

let q' = (FStar_Reflection_Basic.inspect_aqual q)
in (

let uu____8642 = (

let uu____8643 = (

let uu____8648 = (

let uu____8651 = (

let uu____8652 = (init args)
in (FStar_Syntax_Syntax.mk_Tm_app hd1 uu____8652))
in (uu____8651 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in ((uu____8648), (((a), (q')))))
in FStar_Reflection_Data.Tv_App (uu____8643))
in (FStar_All.pipe_left ret uu____8642)))
end))
end
| FStar_Syntax_Syntax.Tm_abs ([], uu____8673, uu____8674) -> begin
(failwith "inspect: empty arguments on Tm_abs")
end
| FStar_Syntax_Syntax.Tm_abs (bs, t3, k) -> begin
(

let uu____8718 = (FStar_Syntax_Subst.open_term bs t3)
in (match (uu____8718) with
| (bs1, t4) -> begin
(match (bs1) with
| [] -> begin
(failwith "impossible")
end
| (b)::bs2 -> begin
(

let uu____8751 = (

let uu____8752 = (

let uu____8757 = (FStar_Syntax_Util.abs bs2 t4 k)
in ((b), (uu____8757)))
in FStar_Reflection_Data.Tv_Abs (uu____8752))
in (FStar_All.pipe_left ret uu____8751))
end)
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____8764) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type (())))
end
| FStar_Syntax_Syntax.Tm_arrow ([], k) -> begin
(failwith "inspect: empty binders on arrow")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____8784) -> begin
(

let uu____8797 = (FStar_Syntax_Util.arrow_one t2)
in (match (uu____8797) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (((b), (c)))))
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t3) -> begin
(

let b = (FStar_Syntax_Syntax.mk_binder bv)
in (

let uu____8827 = (FStar_Syntax_Subst.open_term ((b)::[]) t3)
in (match (uu____8827) with
| (b', t4) -> begin
(

let b1 = (match (b') with
| (b'1)::[] -> begin
b'1
end
| uu____8858 -> begin
(failwith "impossible")
end)
in (FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Refine ((((FStar_Pervasives_Native.fst b1)), (t4))))))
end)))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____8866 = (

let uu____8867 = (FStar_Reflection_Basic.inspect_const c)
in FStar_Reflection_Data.Tv_Const (uu____8867))
in (FStar_All.pipe_left ret uu____8866))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t3) -> begin
(

let uu____8896 = (

let uu____8897 = (

let uu____8902 = (

let uu____8903 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_BigInt.of_int_fs uu____8903))
in ((uu____8902), (t3)))
in FStar_Reflection_Data.Tv_Uvar (uu____8897))
in (FStar_All.pipe_left ret uu____8896))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), t21) -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| uu____8928 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____8931) -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv) -> begin
(

let b = (FStar_Syntax_Syntax.mk_binder bv)
in (

let uu____8936 = (FStar_Syntax_Subst.open_term ((b)::[]) t21)
in (match (uu____8936) with
| (bs, t22) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____8967 -> begin
(failwith "impossible: open_term returned different amount of binders")
end)
in (FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Let (((false), ((FStar_Pervasives_Native.fst b1)), (lb.FStar_Syntax_Syntax.lbdef), (t22))))))
end)))
end)
end)
end
| FStar_Syntax_Syntax.Tm_let ((true, (lb)::[]), t21) -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| uu____8996 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____8999) -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv) -> begin
(

let uu____9003 = (FStar_Syntax_Subst.open_let_rec ((lb)::[]) t21)
in (match (uu____9003) with
| (lbs, t22) -> begin
(match (lbs) with
| (lb1)::[] -> begin
(match (lb1.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____9023) -> begin
(ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv1) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Let (((true), (bv1), (lb1.FStar_Syntax_Syntax.lbdef), (t22)))))
end)
end
| uu____9029 -> begin
(failwith "impossible: open_term returned different amount of binders")
end)
end))
end)
end)
end
| FStar_Syntax_Syntax.Tm_match (t3, brs) -> begin
(

let rec inspect_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____9081 = (FStar_Reflection_Basic.inspect_const c)
in FStar_Reflection_Data.Pat_Constant (uu____9081))
end
| FStar_Syntax_Syntax.Pat_cons (fv, ps) -> begin
(

let uu____9100 = (

let uu____9107 = (FStar_List.map (fun uu____9119 -> (match (uu____9119) with
| (p1, uu____9127) -> begin
(inspect_pat p1)
end)) ps)
in ((fv), (uu____9107)))
in FStar_Reflection_Data.Pat_Cons (uu____9100))
end
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
FStar_Reflection_Data.Pat_Var (bv)
end
| FStar_Syntax_Syntax.Pat_wild (bv) -> begin
FStar_Reflection_Data.Pat_Wild (bv)
end
| FStar_Syntax_Syntax.Pat_dot_term (bv, t4) -> begin
FStar_Reflection_Data.Pat_Dot_Term (((bv), (t4)))
end))
in (

let brs1 = (FStar_List.map FStar_Syntax_Subst.open_branch brs)
in (

let brs2 = (FStar_List.map (fun uu___64_9181 -> (match (uu___64_9181) with
| (pat, uu____9203, t4) -> begin
(

let uu____9221 = (inspect_pat pat)
in ((uu____9221), (t4)))
end)) brs1)
in (FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (((t3), (brs2))))))))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| uu____9238 -> begin
((

let uu____9240 = (

let uu____9245 = (

let uu____9246 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____9247 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "inspect: outside of expected syntax (%s, %s)\n" uu____9246 uu____9247)))
in ((FStar_Errors.Warning_CantInspect), (uu____9245)))
in (FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9240));
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown);
)
end))))


let pack : FStar_Reflection_Data.term_view  ->  FStar_Syntax_Syntax.term tac = (fun tv -> (match (tv) with
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____9258 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_left ret uu____9258))
end
| FStar_Reflection_Data.Tv_BVar (bv) -> begin
(

let uu____9262 = (FStar_Syntax_Syntax.bv_to_tm bv)
in (FStar_All.pipe_left ret uu____9262))
end
| FStar_Reflection_Data.Tv_FVar (fv) -> begin
(

let uu____9266 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (FStar_All.pipe_left ret uu____9266))
end
| FStar_Reflection_Data.Tv_App (l, (r, q)) -> begin
(

let q' = (FStar_Reflection_Basic.pack_aqual q)
in (

let uu____9277 = (FStar_Syntax_Util.mk_app l ((((r), (q')))::[]))
in (FStar_All.pipe_left ret uu____9277)))
end
| FStar_Reflection_Data.Tv_Abs (b, t) -> begin
(

let uu____9298 = (FStar_Syntax_Util.abs ((b)::[]) t FStar_Pervasives_Native.None)
in (FStar_All.pipe_left ret uu____9298))
end
| FStar_Reflection_Data.Tv_Arrow (b, c) -> begin
(

let uu____9303 = (FStar_Syntax_Util.arrow ((b)::[]) c)
in (FStar_All.pipe_left ret uu____9303))
end
| FStar_Reflection_Data.Tv_Type (()) -> begin
(FStar_All.pipe_left ret FStar_Syntax_Util.ktype)
end
| FStar_Reflection_Data.Tv_Refine (bv, t) -> begin
(

let uu____9324 = (FStar_Syntax_Util.refine bv t)
in (FStar_All.pipe_left ret uu____9324))
end
| FStar_Reflection_Data.Tv_Const (c) -> begin
(

let uu____9336 = (

let uu____9339 = (

let uu____9342 = (

let uu____9343 = (FStar_Reflection_Basic.pack_const c)
in FStar_Syntax_Syntax.Tm_constant (uu____9343))
in (FStar_Syntax_Syntax.mk uu____9342))
in (uu____9339 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_All.pipe_left ret uu____9336))
end
| FStar_Reflection_Data.Tv_Uvar (u, t) -> begin
(

let uu____9357 = (

let uu____9360 = (FStar_BigInt.to_int_fs u)
in (FStar_Syntax_Util.uvar_from_id uu____9360 t))
in (FStar_All.pipe_left ret uu____9357))
end
| FStar_Reflection_Data.Tv_Let (false, bv, t1, t2) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 [] FStar_Range.dummyRange)
in (

let uu____9375 = (

let uu____9378 = (

let uu____9381 = (

let uu____9382 = (

let uu____9395 = (

let uu____9396 = (

let uu____9397 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____9397)::[])
in (FStar_Syntax_Subst.close uu____9396 t2))
in ((((false), ((lb)::[]))), (uu____9395)))
in FStar_Syntax_Syntax.Tm_let (uu____9382))
in (FStar_Syntax_Syntax.mk uu____9381))
in (uu____9378 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_All.pipe_left ret uu____9375)))
end
| FStar_Reflection_Data.Tv_Let (true, bv, t1, t2) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 [] FStar_Range.dummyRange)
in (

let uu____9423 = (FStar_Syntax_Subst.close_let_rec ((lb)::[]) t2)
in (match (uu____9423) with
| (lbs, body) -> begin
(

let uu____9438 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____9438))
end)))
end
| FStar_Reflection_Data.Tv_Match (t, brs) -> begin
(

let wrap = (fun v1 -> {FStar_Syntax_Syntax.v = v1; FStar_Syntax_Syntax.p = FStar_Range.dummyRange})
in (

let rec pack_pat = (fun p -> (match (p) with
| FStar_Reflection_Data.Pat_Constant (c) -> begin
(

let uu____9474 = (

let uu____9475 = (FStar_Reflection_Basic.pack_const c)
in FStar_Syntax_Syntax.Pat_constant (uu____9475))
in (FStar_All.pipe_left wrap uu____9474))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____9484 = (

let uu____9485 = (

let uu____9498 = (FStar_List.map (fun p1 -> (

let uu____9512 = (pack_pat p1)
in ((uu____9512), (false)))) ps)
in ((fv), (uu____9498)))
in FStar_Syntax_Syntax.Pat_cons (uu____9485))
in (FStar_All.pipe_left wrap uu____9484))
end
| FStar_Reflection_Data.Pat_Var (bv) -> begin
(FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var (bv)))
end
| FStar_Reflection_Data.Pat_Wild (bv) -> begin
(FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild (bv)))
end
| FStar_Reflection_Data.Pat_Dot_Term (bv, t1) -> begin
(FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_dot_term (((bv), (t1)))))
end))
in (

let brs1 = (FStar_List.map (fun uu___65_9562 -> (match (uu___65_9562) with
| (pat, t1) -> begin
(

let uu____9579 = (pack_pat pat)
in ((uu____9579), (FStar_Pervasives_Native.None), (t1)))
end)) brs)
in (

let brs2 = (FStar_List.map FStar_Syntax_Subst.close_branch brs1)
in (

let uu____9589 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((t), (brs2)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____9589))))))
end
| FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) -> begin
(

let uu____9609 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (((FStar_Util.Inl (t)), (tacopt))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____9609))
end
| FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) -> begin
(

let uu____9651 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (((FStar_Util.Inr (c)), (tacopt))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____9651))
end
| FStar_Reflection_Data.Tv_Unknown -> begin
(

let uu____9686 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____9686))
end))


let goal_of_goal_ty : env  ->  FStar_Reflection_Data.typ  ->  (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t) = (fun env typ -> (

let uu____9711 = (FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty" typ.FStar_Syntax_Syntax.pos env typ)
in (match (uu____9711) with
| (u, uu____9729, g_u) -> begin
(

let g = (

let uu____9744 = (FStar_Options.peek ())
in {FStar_Tactics_Types.context = env; FStar_Tactics_Types.witness = u; FStar_Tactics_Types.goal_ty = typ; FStar_Tactics_Types.opts = uu____9744; FStar_Tactics_Types.is_guard = false})
in ((g), (g_u)))
end)))


let proofstate_of_goal_ty : env  ->  FStar_Reflection_Data.typ  ->  (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term) = (fun env typ -> (

let uu____9755 = (goal_of_goal_ty env typ)
in (match (uu____9755) with
| (g, g_u) -> begin
(

let ps = {FStar_Tactics_Types.main_context = env; FStar_Tactics_Types.main_goal = g; FStar_Tactics_Types.all_implicits = g_u.FStar_TypeChecker_Env.implicits; FStar_Tactics_Types.goals = (g)::[]; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = (Prims.parse_int "0"); FStar_Tactics_Types.__dump = (fun ps msg -> (dump_proofstate ps msg)); FStar_Tactics_Types.psc = FStar_TypeChecker_Normalize.null_psc; FStar_Tactics_Types.entry_range = FStar_Range.dummyRange; FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT; FStar_Tactics_Types.freshness = (Prims.parse_int "0")}
in ((ps), (g.FStar_Tactics_Types.witness)))
end)))




