
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

let uu____179 = (run t1 p)
in (match (uu____179) with
| FStar_Tactics_Result.Success (a, q) -> begin
(

let uu____186 = (t2 a)
in (run uu____186 q))
end
| FStar_Tactics_Result.Failed (msg, q) -> begin
FStar_Tactics_Result.Failed (((msg), (q)))
end)))))


let get : FStar_Tactics_Types.proofstate tac = (mk_tac (fun p -> FStar_Tactics_Result.Success (((p), (p)))))


let idtac : unit tac = (ret ())


let goal_to_string : FStar_Tactics_Types.goal  ->  Prims.string = (fun g -> (

let g_binders = (

let uu____205 = (FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context)
in (FStar_All.pipe_right uu____205 (FStar_Syntax_Print.binders_to_string ", ")))
in (

let w = (bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness)
in (

let t = (bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (

let uu____208 = (tts g.FStar_Tactics_Types.context w)
in (

let uu____209 = (tts g.FStar_Tactics_Types.context t)
in (FStar_Util.format3 "%s |- %s : %s" g_binders uu____208 uu____209)))))))


let tacprint : Prims.string  ->  unit = (fun s -> (FStar_Util.print1 "TAC>> %s\n" s))


let tacprint1 : Prims.string  ->  Prims.string  ->  unit = (fun s x -> (

let uu____225 = (FStar_Util.format1 s x)
in (FStar_Util.print1 "TAC>> %s\n" uu____225)))


let tacprint2 : Prims.string  ->  Prims.string  ->  Prims.string  ->  unit = (fun s x y -> (

let uu____241 = (FStar_Util.format2 s x y)
in (FStar_Util.print1 "TAC>> %s\n" uu____241)))


let tacprint3 : Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  unit = (fun s x y z -> (

let uu____262 = (FStar_Util.format3 s x y z)
in (FStar_Util.print1 "TAC>> %s\n" uu____262)))


let comp_to_typ : FStar_Syntax_Syntax.comp  ->  FStar_Reflection_Data.typ = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____269) -> begin
t
end
| FStar_Syntax_Syntax.GTotal (t, uu____279) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let is_irrelevant : FStar_Tactics_Types.goal  ->  Prims.bool = (fun g -> (

let uu____294 = (

let uu____299 = (FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (FStar_Syntax_Util.un_squash uu____299))
in (match (uu____294) with
| FStar_Pervasives_Native.Some (t) -> begin
true
end
| uu____305 -> begin
false
end)))


let print : Prims.string  ->  unit tac = (fun msg -> ((tacprint msg);
(ret ());
))


let debug : Prims.string  ->  unit tac = (fun msg -> (bind get (fun ps -> ((

let uu____333 = (

let uu____334 = (FStar_Ident.string_of_lid ps.FStar_Tactics_Types.main_context.FStar_TypeChecker_Env.curmodule)
in (FStar_Options.debug_module uu____334))
in (match (uu____333) with
| true -> begin
(tacprint msg)
end
| uu____335 -> begin
()
end));
(ret ());
))))


let dump_goal : 'Auu____342 . 'Auu____342  ->  FStar_Tactics_Types.goal  ->  unit = (fun ps goal -> (

let uu____354 = (goal_to_string goal)
in (tacprint uu____354)))


let dump_cur : FStar_Tactics_Types.proofstate  ->  Prims.string  ->  unit = (fun ps msg -> (match (ps.FStar_Tactics_Types.goals) with
| [] -> begin
(tacprint1 "No more goals (%s)" msg)
end
| (h)::uu____366 -> begin
((tacprint1 "Current goal (%s):" msg);
(

let uu____370 = (FStar_List.hd ps.FStar_Tactics_Types.goals)
in (dump_goal ps uu____370));
)
end))


let ps_to_string : (Prims.string * FStar_Tactics_Types.proofstate)  ->  Prims.string = (fun uu____379 -> (match (uu____379) with
| (msg, ps) -> begin
(

let uu____386 = (

let uu____389 = (

let uu____390 = (FStar_Util.string_of_int ps.FStar_Tactics_Types.depth)
in (FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____390 msg))
in (

let uu____391 = (

let uu____394 = (

let uu____395 = (FStar_Range.string_of_range ps.FStar_Tactics_Types.entry_range)
in (FStar_Util.format1 "Location: %s\n" uu____395))
in (

let uu____396 = (

let uu____399 = (

let uu____400 = (FStar_Util.string_of_int (FStar_List.length ps.FStar_Tactics_Types.goals))
in (

let uu____401 = (

let uu____402 = (FStar_List.map goal_to_string ps.FStar_Tactics_Types.goals)
in (FStar_String.concat "\n" uu____402))
in (FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____400 uu____401)))
in (

let uu____405 = (

let uu____408 = (

let uu____409 = (FStar_Util.string_of_int (FStar_List.length ps.FStar_Tactics_Types.smt_goals))
in (

let uu____410 = (

let uu____411 = (FStar_List.map goal_to_string ps.FStar_Tactics_Types.smt_goals)
in (FStar_String.concat "\n" uu____411))
in (FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____409 uu____410)))
in (uu____408)::[])
in (uu____399)::uu____405))
in (uu____394)::uu____396))
in (uu____389)::uu____391))
in (FStar_String.concat "" uu____386))
end))


let goal_to_json : FStar_Tactics_Types.goal  ->  FStar_Util.json = (fun g -> (

let g_binders = (

let uu____420 = (FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context)
in (

let uu____421 = (

let uu____426 = (FStar_TypeChecker_Env.dsenv g.FStar_Tactics_Types.context)
in (FStar_Syntax_Print.binders_to_json uu____426))
in (FStar_All.pipe_right uu____420 uu____421)))
in (

let uu____427 = (

let uu____434 = (

let uu____441 = (

let uu____446 = (

let uu____447 = (

let uu____454 = (

let uu____459 = (

let uu____460 = (tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness)
in FStar_Util.JsonStr (uu____460))
in (("witness"), (uu____459)))
in (

let uu____461 = (

let uu____468 = (

let uu____473 = (

let uu____474 = (tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in FStar_Util.JsonStr (uu____474))
in (("type"), (uu____473)))
in (uu____468)::[])
in (uu____454)::uu____461))
in FStar_Util.JsonAssoc (uu____447))
in (("goal"), (uu____446)))
in (uu____441)::[])
in ((("hyps"), (g_binders)))::uu____434)
in FStar_Util.JsonAssoc (uu____427))))


let ps_to_json : (Prims.string * FStar_Tactics_Types.proofstate)  ->  FStar_Util.json = (fun uu____507 -> (match (uu____507) with
| (msg, ps) -> begin
(

let uu____514 = (

let uu____521 = (

let uu____528 = (

let uu____535 = (

let uu____542 = (

let uu____547 = (

let uu____548 = (FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals)
in FStar_Util.JsonList (uu____548))
in (("goals"), (uu____547)))
in (

let uu____551 = (

let uu____558 = (

let uu____563 = (

let uu____564 = (FStar_List.map goal_to_json ps.FStar_Tactics_Types.smt_goals)
in FStar_Util.JsonList (uu____564))
in (("smt-goals"), (uu____563)))
in (uu____558)::[])
in (uu____542)::uu____551))
in ((("depth"), (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth))))::uu____535)
in ((("label"), (FStar_Util.JsonStr (msg))))::uu____528)
in (

let uu____587 = (match ((Prims.op_disEquality ps.FStar_Tactics_Types.entry_range FStar_Range.dummyRange)) with
| true -> begin
(

let uu____600 = (

let uu____605 = (FStar_Range.json_of_def_range ps.FStar_Tactics_Types.entry_range)
in (("location"), (uu____605)))
in (uu____600)::[])
end
| uu____614 -> begin
[]
end)
in (FStar_List.append uu____521 uu____587)))
in FStar_Util.JsonAssoc (uu____514))
end))


let dump_proofstate : FStar_Tactics_Types.proofstate  ->  Prims.string  ->  unit = (fun ps msg -> (FStar_Options.with_saved_options (fun uu____635 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(FStar_Util.print_generic "proof-state" ps_to_string ps_to_json ((msg), (ps)));
))))


let print_proof_state1 : Prims.string  ->  unit tac = (fun msg -> (mk_tac (fun ps -> (

let psc = ps.FStar_Tactics_Types.psc
in (

let subst1 = (FStar_TypeChecker_Normalize.psc_subst psc)
in ((

let uu____658 = (FStar_Tactics_Types.subst_proof_state subst1 ps)
in (dump_cur uu____658 msg));
FStar_Tactics_Result.Success (((()), (ps)));
))))))


let print_proof_state : Prims.string  ->  unit tac = (fun msg -> (mk_tac (fun ps -> (

let psc = ps.FStar_Tactics_Types.psc
in (

let subst1 = (FStar_TypeChecker_Normalize.psc_subst psc)
in ((

let uu____676 = (FStar_Tactics_Types.subst_proof_state subst1 ps)
in (dump_proofstate uu____676 msg));
FStar_Tactics_Result.Success (((()), (ps)));
))))))


let tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let rec log : FStar_Tactics_Types.proofstate  ->  (unit  ->  unit)  ->  unit = (fun ps f -> (

let uu____733 = (FStar_ST.op_Bang tac_verb_dbg)
in (match (uu____733) with
| FStar_Pervasives_Native.None -> begin
((

let uu____770 = (

let uu____773 = (FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context (FStar_Options.Other ("TacVerbose")))
in FStar_Pervasives_Native.Some (uu____773))
in (FStar_ST.op_Colon_Equals tac_verb_dbg uu____770));
(log ps f);
)
end
| FStar_Pervasives_Native.Some (true) -> begin
(f ())
end
| FStar_Pervasives_Native.Some (false) -> begin
()
end)))


let mlog : 'a . (unit  ->  unit)  ->  (unit  ->  'a tac)  ->  'a tac = (fun f cont -> (bind get (fun ps -> ((log ps f);
(cont ());
))))


let fail : 'a . Prims.string  ->  'a tac = (fun msg -> (mk_tac (fun ps -> ((

let uu____860 = (FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context (FStar_Options.Other ("TacFail")))
in (match (uu____860) with
| true -> begin
(dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg))
end
| uu____861 -> begin
()
end));
FStar_Tactics_Result.Failed (((msg), (ps)));
))))


let fail1 : 'Auu____868 . Prims.string  ->  Prims.string  ->  'Auu____868 tac = (fun msg x -> (

let uu____881 = (FStar_Util.format1 msg x)
in (fail uu____881)))


let fail2 : 'Auu____890 . Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____890 tac = (fun msg x y -> (

let uu____908 = (FStar_Util.format2 msg x y)
in (fail uu____908)))


let fail3 : 'Auu____919 . Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____919 tac = (fun msg x y z -> (

let uu____942 = (FStar_Util.format3 msg x y z)
in (fail uu____942)))


let fail4 : 'Auu____955 . Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____955 tac = (fun msg x y z w -> (

let uu____983 = (FStar_Util.format4 msg x y z w)
in (fail uu____983)))


let trytac' : 'a . 'a tac  ->  (Prims.string, 'a) FStar_Util.either tac = (fun t -> (mk_tac (fun ps -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____1016 = (run t ps)
in (match (uu____1016) with
| FStar_Tactics_Result.Success (a, q) -> begin
((FStar_Syntax_Unionfind.commit tx);
FStar_Tactics_Result.Success (((FStar_Util.Inr (a)), (q)));
)
end
| FStar_Tactics_Result.Failed (m, q) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(

let ps1 = (

let uu___68_1040 = ps
in {FStar_Tactics_Types.main_context = uu___68_1040.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___68_1040.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___68_1040.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___68_1040.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___68_1040.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___68_1040.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___68_1040.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___68_1040.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___68_1040.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___68_1040.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = q.FStar_Tactics_Types.freshness})
in FStar_Tactics_Result.Success (((FStar_Util.Inl (m)), (ps1))));
)
end))))))


let trytac : 'a . 'a tac  ->  'a FStar_Pervasives_Native.option tac = (fun t -> (

let uu____1067 = (trytac' t)
in (bind uu____1067 (fun r -> (match (r) with
| FStar_Util.Inr (v1) -> begin
(ret (FStar_Pervasives_Native.Some (v1)))
end
| FStar_Util.Inl (uu____1094) -> begin
(ret FStar_Pervasives_Native.None)
end)))))


let trytac_exn : 'a . 'a tac  ->  'a FStar_Pervasives_Native.option tac = (fun t -> (mk_tac (fun ps -> (FStar_All.try_with (fun uu___70_1125 -> (match (()) with
| () -> begin
(

let uu____1130 = (trytac t)
in (run uu____1130 ps))
end)) (fun uu___69_1141 -> (match (uu___69_1141) with
| FStar_Errors.Err (uu____1146, msg) -> begin
((log ps (fun uu____1150 -> (FStar_Util.print1 "trytac_exn error: (%s)" msg)));
FStar_Tactics_Result.Success (((FStar_Pervasives_Native.None), (ps)));
)
end
| FStar_Errors.Error (uu____1155, msg, uu____1157) -> begin
((log ps (fun uu____1160 -> (FStar_Util.print1 "trytac_exn error: (%s)" msg)));
FStar_Tactics_Result.Success (((FStar_Pervasives_Native.None), (ps)));
)
end))))))


let wrap_err : 'a . Prims.string  ->  'a tac  ->  'a tac = (fun pref t -> (mk_tac (fun ps -> (

let uu____1193 = (run t ps)
in (match (uu____1193) with
| FStar_Tactics_Result.Success (a, q) -> begin
FStar_Tactics_Result.Success (((a), (q)))
end
| FStar_Tactics_Result.Failed (msg, q) -> begin
FStar_Tactics_Result.Failed ((((Prims.strcat pref (Prims.strcat ": " msg))), (q)))
end)))))


let set : FStar_Tactics_Types.proofstate  ->  unit tac = (fun p -> (mk_tac (fun uu____1212 -> FStar_Tactics_Result.Success (((()), (p))))))


let __do_unify : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun env t1 t2 -> ((

let uu____1233 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1233) with
| true -> begin
(

let uu____1234 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1235 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1234 uu____1235)))
end
| uu____1236 -> begin
()
end));
(FStar_All.try_with (fun uu___72_1242 -> (match (()) with
| () -> begin
(

let res = (FStar_TypeChecker_Rel.teq_nosmt env t1 t2)
in ((

let uu____1247 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1247) with
| true -> begin
(

let uu____1248 = (FStar_Util.string_of_bool res)
in (

let uu____1249 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1250 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1248 uu____1249 uu____1250))))
end
| uu____1251 -> begin
()
end));
(ret res);
))
end)) (fun uu___71_1255 -> (match (uu___71_1255) with
| FStar_Errors.Err (uu____1258, msg) -> begin
(mlog (fun uu____1261 -> (FStar_Util.print1 ">> do_unify error, (%s)\n" msg)) (fun uu____1263 -> (ret false)))
end
| FStar_Errors.Error (uu____1264, msg, r) -> begin
(mlog (fun uu____1269 -> (

let uu____1270 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg uu____1270))) (fun uu____1272 -> (ret false)))
end)));
))


let do_unify : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun env t1 t2 -> (bind idtac (fun uu____1295 -> ((

let uu____1297 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1297) with
| true -> begin
((FStar_Options.push ());
(

let uu____1299 = (FStar_Options.set_options FStar_Options.Set "--debug_level Rel --debug_level RelCheck")
in ());
)
end
| uu____1300 -> begin
()
end));
(

let uu____1301 = (

let uu____1304 = (__do_unify env t1 t2)
in (bind uu____1304 (fun b -> (match ((not (b))) with
| true -> begin
(

let t11 = (FStar_TypeChecker_Normalize.normalize [] env t1)
in (

let t21 = (FStar_TypeChecker_Normalize.normalize [] env t2)
in (__do_unify env t11 t21)))
end
| uu____1315 -> begin
(ret b)
end))))
in (bind uu____1301 (fun r -> ((

let uu____1320 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1320) with
| true -> begin
(FStar_Options.pop ())
end
| uu____1321 -> begin
()
end));
(ret r);
))));
))))


let trysolve : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun goal solution -> (do_unify goal.FStar_Tactics_Types.context solution goal.FStar_Tactics_Types.witness))


let __dismiss : unit tac = (bind get (fun p -> (

let uu____1341 = (

let uu___73_1342 = p
in (

let uu____1343 = (FStar_List.tl p.FStar_Tactics_Types.goals)
in {FStar_Tactics_Types.main_context = uu___73_1342.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___73_1342.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___73_1342.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu____1343; FStar_Tactics_Types.smt_goals = uu___73_1342.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___73_1342.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___73_1342.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___73_1342.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___73_1342.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___73_1342.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___73_1342.FStar_Tactics_Types.freshness}))
in (set uu____1341))))


let dismiss : unit  ->  unit tac = (fun uu____1352 -> (bind get (fun p -> (match (p.FStar_Tactics_Types.goals) with
| [] -> begin
(fail "dismiss: no more goals")
end
| uu____1359 -> begin
__dismiss
end))))


let solve : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun goal solution -> (

let uu____1376 = (trysolve goal solution)
in (bind uu____1376 (fun b -> (match (b) with
| true -> begin
__dismiss
end
| uu____1383 -> begin
(

let uu____1384 = (

let uu____1385 = (tts goal.FStar_Tactics_Types.context solution)
in (

let uu____1386 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.witness)
in (

let uu____1387 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (FStar_Util.format3 "%s does not solve %s : %s" uu____1385 uu____1386 uu____1387))))
in (fail uu____1384))
end)))))


let dismiss_all : unit tac = (bind get (fun p -> (set (

let uu___74_1394 = p
in {FStar_Tactics_Types.main_context = uu___74_1394.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___74_1394.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___74_1394.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = []; FStar_Tactics_Types.smt_goals = uu___74_1394.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___74_1394.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___74_1394.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___74_1394.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___74_1394.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___74_1394.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___74_1394.FStar_Tactics_Types.freshness}))))


let nwarn : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let check_valid_goal : FStar_Tactics_Types.goal  ->  unit = (fun g -> (

let uu____1437 = (FStar_Options.defensive ())
in (match (uu____1437) with
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

let uu____1453 = (FStar_TypeChecker_Env.pop_bv e)
in (match (uu____1453) with
| FStar_Pervasives_Native.None -> begin
b3
end
| FStar_Pervasives_Native.Some (bv, e1) -> begin
(

let b4 = (b3 && (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort))
in (aux b4 e1))
end)))
in (

let uu____1471 = ((

let uu____1474 = (aux b2 env)
in (not (uu____1474))) && (

let uu____1476 = (FStar_ST.op_Bang nwarn)
in (uu____1476 < (Prims.parse_int "5"))))
in (match (uu____1471) with
| true -> begin
((

let uu____1507 = (

let uu____1512 = (

let uu____1513 = (goal_to_string g)
in (FStar_Util.format1 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n" uu____1513))
in ((FStar_Errors.Warning_IllFormedGoal), (uu____1512)))
in (FStar_Errors.log_issue g.FStar_Tactics_Types.goal_ty.FStar_Syntax_Syntax.pos uu____1507));
(

let uu____1514 = (

let uu____1515 = (FStar_ST.op_Bang nwarn)
in (uu____1515 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals nwarn uu____1514));
)
end
| uu____1574 -> begin
()
end)))))))
end
| uu____1575 -> begin
()
end)))


let add_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___75_1595 = p
in {FStar_Tactics_Types.main_context = uu___75_1595.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___75_1595.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___75_1595.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append gs p.FStar_Tactics_Types.goals); FStar_Tactics_Types.smt_goals = uu___75_1595.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___75_1595.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___75_1595.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___75_1595.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___75_1595.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___75_1595.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___75_1595.FStar_Tactics_Types.freshness}));
))))


let add_smt_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___76_1615 = p
in {FStar_Tactics_Types.main_context = uu___76_1615.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___76_1615.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___76_1615.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___76_1615.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = (FStar_List.append gs p.FStar_Tactics_Types.smt_goals); FStar_Tactics_Types.depth = uu___76_1615.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___76_1615.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___76_1615.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___76_1615.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___76_1615.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___76_1615.FStar_Tactics_Types.freshness}));
))))


let push_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___77_1635 = p
in {FStar_Tactics_Types.main_context = uu___77_1635.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___77_1635.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___77_1635.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append p.FStar_Tactics_Types.goals gs); FStar_Tactics_Types.smt_goals = uu___77_1635.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___77_1635.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___77_1635.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___77_1635.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___77_1635.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___77_1635.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___77_1635.FStar_Tactics_Types.freshness}));
))))


let push_smt_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___78_1655 = p
in {FStar_Tactics_Types.main_context = uu___78_1655.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___78_1655.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___78_1655.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___78_1655.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = (FStar_List.append p.FStar_Tactics_Types.smt_goals gs); FStar_Tactics_Types.depth = uu___78_1655.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___78_1655.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___78_1655.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___78_1655.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___78_1655.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___78_1655.FStar_Tactics_Types.freshness}));
))))


let replace_cur : FStar_Tactics_Types.goal  ->  unit tac = (fun g -> (bind __dismiss (fun uu____1666 -> (add_goals ((g)::[])))))


let add_implicits : implicits  ->  unit tac = (fun i -> (bind get (fun p -> (set (

let uu___79_1680 = p
in {FStar_Tactics_Types.main_context = uu___79_1680.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___79_1680.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = (FStar_List.append i p.FStar_Tactics_Types.all_implicits); FStar_Tactics_Types.goals = uu___79_1680.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___79_1680.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___79_1680.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___79_1680.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___79_1680.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___79_1680.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___79_1680.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___79_1680.FStar_Tactics_Types.freshness})))))


let new_uvar : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  FStar_Syntax_Syntax.term tac = (fun reason env typ -> (

let uu____1712 = (FStar_TypeChecker_Util.new_implicit_var reason typ.FStar_Syntax_Syntax.pos env typ)
in (match (uu____1712) with
| (u, uu____1728, g_u) -> begin
(

let uu____1742 = (add_implicits g_u.FStar_TypeChecker_Env.implicits)
in (bind uu____1742 (fun uu____1746 -> (ret u))))
end)))


let is_true : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1752 = (FStar_Syntax_Util.un_squash t)
in (match (uu____1752) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____1762 = (

let uu____1763 = (FStar_Syntax_Subst.compress t')
in uu____1763.FStar_Syntax_Syntax.n)
in (match (uu____1762) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)
end
| uu____1767 -> begin
false
end))
end
| uu____1768 -> begin
false
end)))


let is_false : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1778 = (FStar_Syntax_Util.un_squash t)
in (match (uu____1778) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____1788 = (

let uu____1789 = (FStar_Syntax_Subst.compress t')
in uu____1789.FStar_Syntax_Syntax.n)
in (match (uu____1788) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid)
end
| uu____1793 -> begin
false
end))
end
| uu____1794 -> begin
false
end)))


let cur_goal : unit  ->  FStar_Tactics_Types.goal tac = (fun uu____1805 -> (bind get (fun p -> (match (p.FStar_Tactics_Types.goals) with
| [] -> begin
(fail "No more goals (1)")
end
| (hd1)::tl1 -> begin
(ret hd1)
end))))


let tadmit : unit  ->  unit tac = (fun uu____1822 -> (

let uu____1825 = (

let uu____1828 = (cur_goal ())
in (bind uu____1828 (fun g -> ((

let uu____1835 = (

let uu____1840 = (

let uu____1841 = (goal_to_string g)
in (FStar_Util.format1 "Tactics admitted goal <%s>\n\n" uu____1841))
in ((FStar_Errors.Warning_TacAdmit), (uu____1840)))
in (FStar_Errors.log_issue g.FStar_Tactics_Types.goal_ty.FStar_Syntax_Syntax.pos uu____1835));
(solve g FStar_Syntax_Util.exp_unit);
))))
in (FStar_All.pipe_left (wrap_err "tadmit") uu____1825)))


let fresh : unit  ->  FStar_BigInt.t tac = (fun uu____1852 -> (bind get (fun ps -> (

let n1 = ps.FStar_Tactics_Types.freshness
in (

let ps1 = (

let uu___80_1862 = ps
in {FStar_Tactics_Types.main_context = uu___80_1862.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___80_1862.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___80_1862.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___80_1862.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___80_1862.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___80_1862.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___80_1862.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___80_1862.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___80_1862.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___80_1862.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))})
in (

let uu____1863 = (set ps1)
in (bind uu____1863 (fun uu____1868 -> (

let uu____1869 = (FStar_BigInt.of_int_fs n1)
in (ret uu____1869))))))))))


let ngoals : unit  ->  FStar_BigInt.t tac = (fun uu____1876 -> (bind get (fun ps -> (

let n1 = (FStar_List.length ps.FStar_Tactics_Types.goals)
in (

let uu____1884 = (FStar_BigInt.of_int_fs n1)
in (ret uu____1884))))))


let ngoals_smt : unit  ->  FStar_BigInt.t tac = (fun uu____1897 -> (bind get (fun ps -> (

let n1 = (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
in (

let uu____1905 = (FStar_BigInt.of_int_fs n1)
in (ret uu____1905))))))


let is_guard : unit  ->  Prims.bool tac = (fun uu____1918 -> (

let uu____1921 = (cur_goal ())
in (bind uu____1921 (fun g -> (ret g.FStar_Tactics_Types.is_guard)))))


let mk_irrelevant_goal : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  FStar_Options.optionstate  ->  FStar_Tactics_Types.goal tac = (fun reason env phi opts -> (

let typ = (

let uu____1953 = (env.FStar_TypeChecker_Env.universe_of env phi)
in (FStar_Syntax_Util.mk_squash uu____1953 phi))
in (

let uu____1954 = (new_uvar reason env typ)
in (bind uu____1954 (fun u -> (

let goal = {FStar_Tactics_Types.context = env; FStar_Tactics_Types.witness = u; FStar_Tactics_Types.goal_ty = typ; FStar_Tactics_Types.opts = opts; FStar_Tactics_Types.is_guard = false}
in (ret goal)))))))


let __tc : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ * FStar_TypeChecker_Env.guard_t) tac = (fun e t -> (bind get (fun ps -> (mlog (fun uu____2003 -> (

let uu____2004 = (tts e t)
in (FStar_Util.print1 "Tac> __tc(%s)\n" uu____2004))) (fun uu____2006 -> (FStar_All.try_with (fun uu___82_2017 -> (match (()) with
| () -> begin
(

let uu____2026 = (ps.FStar_Tactics_Types.main_context.FStar_TypeChecker_Env.type_of e t)
in (ret uu____2026))
end)) (fun uu___81_2044 -> (match (uu___81_2044) with
| FStar_Errors.Err (uu____2053, msg) -> begin
(

let uu____2055 = (tts e t)
in (

let uu____2056 = (

let uu____2057 = (FStar_TypeChecker_Env.all_binders e)
in (FStar_All.pipe_right uu____2057 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____2055 uu____2056 msg)))
end
| FStar_Errors.Error (uu____2064, msg, uu____2066) -> begin
(

let uu____2067 = (tts e t)
in (

let uu____2068 = (

let uu____2069 = (FStar_TypeChecker_Env.all_binders e)
in (FStar_All.pipe_right uu____2069 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____2067 uu____2068 msg)))
end))))))))


let istrivial : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e t -> (

let steps = (FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.UnfoldTac)::(FStar_TypeChecker_Normalize.Unmeta)::[]
in (

let t1 = (normalize steps e t)
in (is_true t1))))


let get_guard_policy : unit  ->  FStar_Tactics_Types.guard_policy tac = (fun uu____2096 -> (bind get (fun ps -> (ret ps.FStar_Tactics_Types.guard_policy))))


let set_guard_policy : FStar_Tactics_Types.guard_policy  ->  unit tac = (fun pol -> (bind get (fun ps -> (set (

let uu___83_2114 = ps
in {FStar_Tactics_Types.main_context = uu___83_2114.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___83_2114.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___83_2114.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___83_2114.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___83_2114.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___83_2114.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___83_2114.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___83_2114.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___83_2114.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = pol; FStar_Tactics_Types.freshness = uu___83_2114.FStar_Tactics_Types.freshness})))))


let with_policy : 'a . FStar_Tactics_Types.guard_policy  ->  'a tac  ->  'a tac = (fun pol t -> (

let uu____2138 = (get_guard_policy ())
in (bind uu____2138 (fun old_pol -> (

let uu____2144 = (set_guard_policy pol)
in (bind uu____2144 (fun uu____2148 -> (bind t (fun r -> (

let uu____2152 = (set_guard_policy old_pol)
in (bind uu____2152 (fun uu____2156 -> (ret r)))))))))))))


let proc_guard : Prims.string  ->  env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Options.optionstate  ->  unit tac = (fun reason e g opts -> (

let uu____2181 = (

let uu____2182 = (FStar_TypeChecker_Rel.simplify_guard e g)
in uu____2182.FStar_TypeChecker_Env.guard_f)
in (match (uu____2181) with
| FStar_TypeChecker_Common.Trivial -> begin
(ret ())
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____2186 = (istrivial e f)
in (match (uu____2186) with
| true -> begin
(ret ())
end
| uu____2189 -> begin
(bind get (fun ps -> (match (ps.FStar_Tactics_Types.guard_policy) with
| FStar_Tactics_Types.Drop -> begin
(ret ())
end
| FStar_Tactics_Types.Goal -> begin
(

let uu____2194 = (mk_irrelevant_goal reason e f opts)
in (bind uu____2194 (fun goal -> (

let goal1 = (

let uu___84_2201 = goal
in {FStar_Tactics_Types.context = uu___84_2201.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___84_2201.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___84_2201.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___84_2201.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = true})
in (push_goals ((goal1)::[]))))))
end
| FStar_Tactics_Types.SMT -> begin
(

let uu____2202 = (mk_irrelevant_goal reason e f opts)
in (bind uu____2202 (fun goal -> (

let goal1 = (

let uu___85_2209 = goal
in {FStar_Tactics_Types.context = uu___85_2209.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___85_2209.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___85_2209.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___85_2209.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = true})
in (push_smt_goals ((goal1)::[]))))))
end
| FStar_Tactics_Types.Force -> begin
(FStar_All.try_with (fun uu___87_2214 -> (match (()) with
| () -> begin
(

let uu____2217 = (

let uu____2218 = (

let uu____2219 = (FStar_TypeChecker_Rel.discharge_guard_no_smt e g)
in (FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____2219))
in (not (uu____2218)))
in (match (uu____2217) with
| true -> begin
(mlog (fun uu____2224 -> (

let uu____2225 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print1 "guard = %s\n" uu____2225))) (fun uu____2227 -> (fail1 "Forcing the guard failed %s)" reason)))
end
| uu____2228 -> begin
(ret ())
end))
end)) (fun uu___86_2231 -> (match (uu___86_2231) with
| uu____2234 -> begin
(mlog (fun uu____2237 -> (

let uu____2238 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print1 "guard = %s\n" uu____2238))) (fun uu____2240 -> (fail1 "Forcing the guard failed (%s)" reason)))
end)))
end)))
end))
end)))


let tc : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.typ tac = (fun t -> (

let uu____2250 = (

let uu____2253 = (cur_goal ())
in (bind uu____2253 (fun goal -> (

let uu____2259 = (__tc goal.FStar_Tactics_Types.context t)
in (bind uu____2259 (fun uu____2279 -> (match (uu____2279) with
| (t1, typ, guard) -> begin
(

let uu____2291 = (proc_guard "tc" goal.FStar_Tactics_Types.context guard goal.FStar_Tactics_Types.opts)
in (bind uu____2291 (fun uu____2295 -> (ret typ))))
end)))))))
in (FStar_All.pipe_left (wrap_err "tc") uu____2250)))


let add_irrelevant_goal : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  FStar_Options.optionstate  ->  unit tac = (fun reason env phi opts -> (

let uu____2324 = (mk_irrelevant_goal reason env phi opts)
in (bind uu____2324 (fun goal -> (add_goals ((goal)::[]))))))


let trivial : unit  ->  unit tac = (fun uu____2335 -> (

let uu____2338 = (cur_goal ())
in (bind uu____2338 (fun goal -> (

let uu____2344 = (istrivial goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (match (uu____2344) with
| true -> begin
(solve goal FStar_Syntax_Util.exp_unit)
end
| uu____2347 -> begin
(

let uu____2348 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail1 "Not a trivial goal: %s" uu____2348))
end))))))


let goal_from_guard : Prims.string  ->  env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Options.optionstate  ->  FStar_Tactics_Types.goal FStar_Pervasives_Native.option tac = (fun reason e g opts -> (

let uu____2377 = (

let uu____2378 = (FStar_TypeChecker_Rel.simplify_guard e g)
in uu____2378.FStar_TypeChecker_Env.guard_f)
in (match (uu____2377) with
| FStar_TypeChecker_Common.Trivial -> begin
(ret FStar_Pervasives_Native.None)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____2386 = (istrivial e f)
in (match (uu____2386) with
| true -> begin
(ret FStar_Pervasives_Native.None)
end
| uu____2393 -> begin
(

let uu____2394 = (mk_irrelevant_goal reason e f opts)
in (bind uu____2394 (fun goal -> (ret (FStar_Pervasives_Native.Some ((

let uu___88_2404 = goal
in {FStar_Tactics_Types.context = uu___88_2404.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___88_2404.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___88_2404.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___88_2404.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = true})))))))
end))
end)))


let smt : unit  ->  unit tac = (fun uu____2411 -> (

let uu____2414 = (cur_goal ())
in (bind uu____2414 (fun g -> (

let uu____2420 = (is_irrelevant g)
in (match (uu____2420) with
| true -> begin
(bind __dismiss (fun uu____2424 -> (add_smt_goals ((g)::[]))))
end
| uu____2425 -> begin
(

let uu____2426 = (tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (fail1 "goal is not irrelevant: cannot dispatch to smt (%s)" uu____2426))
end))))))


let divide : 'a 'b . FStar_BigInt.t  ->  'a tac  ->  'b tac  ->  ('a * 'b) tac = (fun n1 l r -> (bind get (fun p -> (

let uu____2475 = (FStar_All.try_with (fun uu___93_2498 -> (match (()) with
| () -> begin
(

let uu____2509 = (

let uu____2518 = (FStar_BigInt.to_int_fs n1)
in (FStar_List.splitAt uu____2518 p.FStar_Tactics_Types.goals))
in (ret uu____2509))
end)) (fun uu___92_2529 -> (match (uu___92_2529) with
| uu____2540 -> begin
(fail "divide: not enough goals")
end)))
in (bind uu____2475 (fun uu____2567 -> (match (uu____2567) with
| (lgs, rgs) -> begin
(

let lp = (

let uu___89_2593 = p
in {FStar_Tactics_Types.main_context = uu___89_2593.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___89_2593.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___89_2593.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = lgs; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = uu___89_2593.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___89_2593.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___89_2593.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___89_2593.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___89_2593.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___89_2593.FStar_Tactics_Types.freshness})
in (

let rp = (

let uu___90_2595 = p
in {FStar_Tactics_Types.main_context = uu___90_2595.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___90_2595.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___90_2595.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = rgs; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = uu___90_2595.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___90_2595.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___90_2595.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___90_2595.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___90_2595.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___90_2595.FStar_Tactics_Types.freshness})
in (

let uu____2596 = (set lp)
in (bind uu____2596 (fun uu____2604 -> (bind l (fun a -> (bind get (fun lp' -> (

let uu____2618 = (set rp)
in (bind uu____2618 (fun uu____2626 -> (bind r (fun b -> (bind get (fun rp' -> (

let p' = (

let uu___91_2642 = p
in {FStar_Tactics_Types.main_context = uu___91_2642.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___91_2642.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___91_2642.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append lp'.FStar_Tactics_Types.goals rp'.FStar_Tactics_Types.goals); FStar_Tactics_Types.smt_goals = (FStar_List.append lp'.FStar_Tactics_Types.smt_goals (FStar_List.append rp'.FStar_Tactics_Types.smt_goals p.FStar_Tactics_Types.smt_goals)); FStar_Tactics_Types.depth = uu___91_2642.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___91_2642.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___91_2642.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___91_2642.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___91_2642.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___91_2642.FStar_Tactics_Types.freshness})
in (

let uu____2643 = (set p')
in (bind uu____2643 (fun uu____2651 -> (ret ((a), (b)))))))))))))))))))))))
end)))))))


let focus : 'a . 'a tac  ->  'a tac = (fun f -> (

let uu____2672 = (divide FStar_BigInt.one f idtac)
in (bind uu____2672 (fun uu____2685 -> (match (uu____2685) with
| (a, ()) -> begin
(ret a)
end)))))


let rec map : 'a . 'a tac  ->  'a Prims.list tac = (fun tau -> (bind get (fun p -> (match (p.FStar_Tactics_Types.goals) with
| [] -> begin
(ret [])
end
| (uu____2722)::uu____2723 -> begin
(

let uu____2726 = (

let uu____2735 = (map tau)
in (divide FStar_BigInt.one tau uu____2735))
in (bind uu____2726 (fun uu____2753 -> (match (uu____2753) with
| (h, t) -> begin
(ret ((h)::t))
end))))
end))))


let seq : unit tac  ->  unit tac  ->  unit tac = (fun t1 t2 -> (

let uu____2794 = (bind t1 (fun uu____2799 -> (

let uu____2800 = (map t2)
in (bind uu____2800 (fun uu____2808 -> (ret ()))))))
in (focus uu____2794)))


let intro : unit  ->  FStar_Syntax_Syntax.binder tac = (fun uu____2817 -> (

let uu____2820 = (

let uu____2823 = (cur_goal ())
in (bind uu____2823 (fun goal -> (

let uu____2832 = (FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty)
in (match (uu____2832) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____2847 = (

let uu____2848 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____2848)))
in (match (uu____2847) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____2851 -> begin
(

let env' = (FStar_TypeChecker_Env.push_binders goal.FStar_Tactics_Types.context ((b)::[]))
in (

let typ' = (comp_to_typ c)
in (

let uu____2854 = (new_uvar "intro" env' typ')
in (bind uu____2854 (fun u -> (

let uu____2860 = (

let uu____2863 = (FStar_Syntax_Util.abs ((b)::[]) u FStar_Pervasives_Native.None)
in (trysolve goal uu____2863))
in (bind uu____2860 (fun bb -> (match (bb) with
| true -> begin
(

let uu____2869 = (

let uu____2872 = (

let uu___94_2873 = goal
in (

let uu____2874 = (bnorm env' u)
in (

let uu____2875 = (bnorm env' typ')
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = uu____2874; FStar_Tactics_Types.goal_ty = uu____2875; FStar_Tactics_Types.opts = uu___94_2873.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___94_2873.FStar_Tactics_Types.is_guard})))
in (replace_cur uu____2872))
in (bind uu____2869 (fun uu____2877 -> (ret b))))
end
| uu____2878 -> begin
(fail "unification failed")
end)))))))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2883 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail1 "goal is not an arrow (%s)" uu____2883))
end)))))
in (FStar_All.pipe_left (wrap_err "intro") uu____2820)))


let intro_rec : unit  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac = (fun uu____2898 -> (

let uu____2905 = (cur_goal ())
in (bind uu____2905 (fun goal -> ((FStar_Util.print_string "WARNING (intro_rec): calling this is known to cause normalizer loops\n");
(FStar_Util.print_string "WARNING (intro_rec): proceed at your own risk...\n");
(

let uu____2922 = (FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty)
in (match (uu____2922) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____2941 = (

let uu____2942 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____2942)))
in (match (uu____2941) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____2953 -> begin
(

let bv = (FStar_Syntax_Syntax.gen_bv "__recf" FStar_Pervasives_Native.None goal.FStar_Tactics_Types.goal_ty)
in (

let bs = (

let uu____2958 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____2958)::(b)::[])
in (

let env' = (FStar_TypeChecker_Env.push_binders goal.FStar_Tactics_Types.context bs)
in (

let uu____2960 = (

let uu____2963 = (comp_to_typ c)
in (new_uvar "intro_rec" env' uu____2963))
in (bind uu____2960 (fun u -> (

let lb = (

let uu____2978 = (FStar_Syntax_Util.abs ((b)::[]) u FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] goal.FStar_Tactics_Types.goal_ty FStar_Parser_Const.effect_Tot_lid uu____2978 [] FStar_Range.dummyRange))
in (

let body = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____2984 = (FStar_Syntax_Subst.close_let_rec ((lb)::[]) body)
in (match (uu____2984) with
| (lbs, body1) -> begin
(

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body1)))) FStar_Pervasives_Native.None goal.FStar_Tactics_Types.witness.FStar_Syntax_Syntax.pos)
in (

let uu____3014 = (trysolve goal tm)
in (bind uu____3014 (fun bb -> (match (bb) with
| true -> begin
(

let uu____3030 = (

let uu____3033 = (

let uu___95_3034 = goal
in (

let uu____3035 = (bnorm env' u)
in (

let uu____3036 = (

let uu____3037 = (comp_to_typ c)
in (bnorm env' uu____3037))
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = uu____3035; FStar_Tactics_Types.goal_ty = uu____3036; FStar_Tactics_Types.opts = uu___95_3034.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___95_3034.FStar_Tactics_Types.is_guard})))
in (replace_cur uu____3033))
in (bind uu____3030 (fun uu____3044 -> (

let uu____3045 = (

let uu____3050 = (FStar_Syntax_Syntax.mk_binder bv)
in ((uu____3050), (b)))
in (ret uu____3045)))))
end
| uu____3055 -> begin
(fail "intro_rec: unification failed")
end)))))
end))))))))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3064 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail1 "intro_rec: goal is not an arrow (%s)" uu____3064))
end));
)))))


let norm : FStar_Syntax_Embeddings.norm_step Prims.list  ->  unit tac = (fun s -> (

let uu____3082 = (cur_goal ())
in (bind uu____3082 (fun goal -> (mlog (fun uu____3089 -> (

let uu____3090 = (FStar_Syntax_Print.term_to_string goal.FStar_Tactics_Types.witness)
in (FStar_Util.print1 "norm: witness = %s\n" uu____3090))) (fun uu____3095 -> (

let steps = (

let uu____3099 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldTac)::[]) uu____3099))
in (

let w = (normalize steps goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.witness)
in (

let t = (normalize steps goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (replace_cur (

let uu___96_3106 = goal
in {FStar_Tactics_Types.context = uu___96_3106.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = w; FStar_Tactics_Types.goal_ty = t; FStar_Tactics_Types.opts = uu___96_3106.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___96_3106.FStar_Tactics_Types.is_guard})))))))))))


let norm_term_env : env  ->  FStar_Syntax_Embeddings.norm_step Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun e s t -> (

let uu____3130 = (mlog (fun uu____3135 -> (

let uu____3136 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "norm_term: tm = %s\n" uu____3136))) (fun uu____3138 -> (bind get (fun ps -> (

let opts = (match (ps.FStar_Tactics_Types.goals) with
| (g)::uu____3144 -> begin
g.FStar_Tactics_Types.opts
end
| uu____3147 -> begin
(FStar_Options.peek ())
end)
in (mlog (fun uu____3152 -> (

let uu____3153 = (tts ps.FStar_Tactics_Types.main_context t)
in (FStar_Util.print1 "norm_term_env: t = %s\n" uu____3153))) (fun uu____3156 -> (

let uu____3157 = (__tc e t)
in (bind uu____3157 (fun uu____3178 -> (match (uu____3178) with
| (t1, uu____3188, uu____3189) -> begin
(

let steps = (

let uu____3193 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldTac)::[]) uu____3193))
in (

let t2 = (normalize steps ps.FStar_Tactics_Types.main_context t1)
in (ret t2)))
end)))))))))))
in (FStar_All.pipe_left (wrap_err "norm_term") uu____3130)))


let refine_intro : unit  ->  unit tac = (fun uu____3207 -> (

let uu____3210 = (

let uu____3213 = (cur_goal ())
in (bind uu____3213 (fun g -> (

let uu____3220 = (FStar_TypeChecker_Rel.base_and_refinement g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (match (uu____3220) with
| (uu____3233, FStar_Pervasives_Native.None) -> begin
(fail "not a refinement")
end
| (t, FStar_Pervasives_Native.Some (bv, phi)) -> begin
(

let g1 = (

let uu___97_3258 = g
in {FStar_Tactics_Types.context = uu___97_3258.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___97_3258.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = t; FStar_Tactics_Types.opts = uu___97_3258.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___97_3258.FStar_Tactics_Types.is_guard})
in (

let uu____3259 = (

let uu____3264 = (

let uu____3269 = (

let uu____3270 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____3270)::[])
in (FStar_Syntax_Subst.open_term uu____3269 phi))
in (match (uu____3264) with
| (bvs, phi1) -> begin
(

let uu____3277 = (

let uu____3278 = (FStar_List.hd bvs)
in (FStar_Pervasives_Native.fst uu____3278))
in ((uu____3277), (phi1)))
end))
in (match (uu____3259) with
| (bv1, phi1) -> begin
(

let uu____3291 = (

let uu____3294 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv1), (g.FStar_Tactics_Types.witness))))::[]) phi1)
in (mk_irrelevant_goal "refine_intro refinement" g.FStar_Tactics_Types.context uu____3294 g.FStar_Tactics_Types.opts))
in (bind uu____3291 (fun g2 -> (bind __dismiss (fun uu____3298 -> (add_goals ((g1)::(g2)::[])))))))
end)))
end)))))
in (FStar_All.pipe_left (wrap_err "refine_intro") uu____3210)))


let __exact_now : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun set_expected_typ1 t -> (

let uu____3317 = (cur_goal ())
in (bind uu____3317 (fun goal -> (

let env = (match (set_expected_typ1) with
| true -> begin
(FStar_TypeChecker_Env.set_expected_typ goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
end
| uu____3325 -> begin
goal.FStar_Tactics_Types.context
end)
in (

let uu____3326 = (__tc env t)
in (bind uu____3326 (fun uu____3345 -> (match (uu____3345) with
| (t1, typ, guard) -> begin
(mlog (fun uu____3360 -> (

let uu____3361 = (tts goal.FStar_Tactics_Types.context typ)
in (

let uu____3362 = (FStar_TypeChecker_Rel.guard_to_string goal.FStar_Tactics_Types.context guard)
in (FStar_Util.print2 "__exact_now: got type %s\n__exact_now and guard %s\n" uu____3361 uu____3362)))) (fun uu____3365 -> (

let uu____3366 = (proc_guard "__exact typing" goal.FStar_Tactics_Types.context guard goal.FStar_Tactics_Types.opts)
in (bind uu____3366 (fun uu____3370 -> (mlog (fun uu____3374 -> (

let uu____3375 = (tts goal.FStar_Tactics_Types.context typ)
in (

let uu____3376 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (FStar_Util.print2 "__exact_now: unifying %s and %s\n" uu____3375 uu____3376)))) (fun uu____3379 -> (

let uu____3380 = (do_unify goal.FStar_Tactics_Types.context typ goal.FStar_Tactics_Types.goal_ty)
in (bind uu____3380 (fun b -> (match (b) with
| true -> begin
(solve goal t1)
end
| uu____3387 -> begin
(

let uu____3388 = (tts goal.FStar_Tactics_Types.context t1)
in (

let uu____3389 = (tts goal.FStar_Tactics_Types.context typ)
in (

let uu____3390 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (

let uu____3391 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.witness)
in (fail4 "%s : %s does not exactly solve the goal %s (witness = %s)" uu____3388 uu____3389 uu____3390 uu____3391)))))
end)))))))))))
end)))))))))


let t_exact : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun set_expected_typ1 tm -> (

let uu____3406 = (mlog (fun uu____3411 -> (

let uu____3412 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "t_exact: tm = %s\n" uu____3412))) (fun uu____3415 -> (

let uu____3416 = (

let uu____3423 = (__exact_now set_expected_typ1 tm)
in (trytac' uu____3423))
in (bind uu____3416 (fun uu___63_3432 -> (match (uu___63_3432) with
| FStar_Util.Inr (r) -> begin
(ret ())
end
| FStar_Util.Inl (e) -> begin
(

let uu____3441 = (

let uu____3448 = (

let uu____3451 = (norm ((FStar_Syntax_Embeddings.Delta)::[]))
in (bind uu____3451 (fun uu____3456 -> (

let uu____3457 = (refine_intro ())
in (bind uu____3457 (fun uu____3461 -> (__exact_now set_expected_typ1 tm)))))))
in (trytac' uu____3448))
in (bind uu____3441 (fun uu___62_3468 -> (match (uu___62_3468) with
| FStar_Util.Inr (r) -> begin
(ret ())
end
| FStar_Util.Inl (uu____3476) -> begin
(fail e)
end))))
end))))))
in (FStar_All.pipe_left (wrap_err "exact") uu____3406)))


let uvar_free_in_goal : FStar_Syntax_Syntax.uvar  ->  FStar_Tactics_Types.goal  ->  Prims.bool = (fun u g -> (match (g.FStar_Tactics_Types.is_guard) with
| true -> begin
false
end
| uu____3491 -> begin
(

let free_uvars = (

let uu____3495 = (

let uu____3502 = (FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty)
in (FStar_Util.set_elements uu____3502))
in (FStar_List.map FStar_Pervasives_Native.fst uu____3495))
in (FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars))
end))


let uvar_free : FStar_Syntax_Syntax.uvar  ->  FStar_Tactics_Types.proofstate  ->  Prims.bool = (fun u ps -> (FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals))


let rec mapM : 'a 'b . ('a  ->  'b tac)  ->  'a Prims.list  ->  'b Prims.list tac = (fun f l -> (match (l) with
| [] -> begin
(ret [])
end
| (x)::xs -> begin
(

let uu____3572 = (f x)
in (bind uu____3572 (fun y -> (

let uu____3580 = (mapM f xs)
in (bind uu____3580 (fun ys -> (ret ((y)::ys))))))))
end))

exception NoUnif


let uu___is_NoUnif : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoUnif -> begin
true
end
| uu____3600 -> begin
false
end))


let rec __apply : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.typ  ->  unit tac = (fun uopt tm typ -> (

let uu____3620 = (cur_goal ())
in (bind uu____3620 (fun goal -> (mlog (fun uu____3627 -> (

let uu____3628 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3628))) (fun uu____3631 -> (

let uu____3632 = (

let uu____3637 = (

let uu____3640 = (t_exact false tm)
in (with_policy FStar_Tactics_Types.Force uu____3640))
in (trytac_exn uu____3637))
in (bind uu____3632 (fun uu___64_3647 -> (match (uu___64_3647) with
| FStar_Pervasives_Native.Some (r) -> begin
(ret ())
end
| FStar_Pervasives_Native.None -> begin
(mlog (fun uu____3655 -> (

let uu____3656 = (FStar_Syntax_Print.term_to_string typ)
in (FStar_Util.print1 ">>> typ = %s\n" uu____3656))) (fun uu____3659 -> (

let uu____3660 = (FStar_Syntax_Util.arrow_one typ)
in (match (uu____3660) with
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise NoUnif)
end
| FStar_Pervasives_Native.Some ((bv, aq), c) -> begin
(mlog (fun uu____3692 -> (

let uu____3693 = (FStar_Syntax_Print.binder_to_string ((bv), (aq)))
in (FStar_Util.print1 "__apply: pushing binder %s\n" uu____3693))) (fun uu____3696 -> (

let uu____3697 = (

let uu____3698 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____3698)))
in (match (uu____3697) with
| true -> begin
(fail "apply: not total codomain")
end
| uu____3701 -> begin
(

let uu____3702 = (new_uvar "apply" goal.FStar_Tactics_Types.context bv.FStar_Syntax_Syntax.sort)
in (bind uu____3702 (fun u -> (

let tm' = (FStar_Syntax_Syntax.mk_Tm_app tm ((((u), (aq)))::[]) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
in (

let typ' = (

let uu____3722 = (comp_to_typ c)
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (u))))::[])) uu____3722))
in (

let uu____3723 = (__apply uopt tm' typ')
in (bind uu____3723 (fun uu____3731 -> (

let u1 = (bnorm goal.FStar_Tactics_Types.context u)
in (

let uu____3733 = (

let uu____3734 = (

let uu____3737 = (

let uu____3738 = (FStar_Syntax_Util.head_and_args u1)
in (FStar_Pervasives_Native.fst uu____3738))
in (FStar_Syntax_Subst.compress uu____3737))
in uu____3734.FStar_Syntax_Syntax.n)
in (match (uu____3733) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, uu____3766) -> begin
(bind get (fun ps -> (

let uu____3794 = (uopt && (uvar_free uvar ps))
in (match (uu____3794) with
| true -> begin
(ret ())
end
| uu____3797 -> begin
(

let uu____3798 = (

let uu____3801 = (

let uu___98_3802 = goal
in (

let uu____3803 = (bnorm goal.FStar_Tactics_Types.context u1)
in (

let uu____3804 = (bnorm goal.FStar_Tactics_Types.context bv.FStar_Syntax_Syntax.sort)
in {FStar_Tactics_Types.context = uu___98_3802.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu____3803; FStar_Tactics_Types.goal_ty = uu____3804; FStar_Tactics_Types.opts = uu___98_3802.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = false})))
in (uu____3801)::[])
in (add_goals uu____3798))
end))))
end
| t -> begin
(ret ())
end)))))))))))
end))))
end))))
end))))))))))


let try_unif : 'a . 'a tac  ->  'a tac  ->  'a tac = (fun t t' -> (mk_tac (fun ps -> (FStar_All.try_with (fun uu___100_3838 -> (match (()) with
| () -> begin
(run t ps)
end)) (fun uu___99_3842 -> (match (uu___99_3842) with
| NoUnif -> begin
(run t' ps)
end))))))


let apply : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun uopt tm -> (

let uu____3859 = (mlog (fun uu____3864 -> (

let uu____3865 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "apply: tm = %s\n" uu____3865))) (fun uu____3868 -> (

let uu____3869 = (cur_goal ())
in (bind uu____3869 (fun goal -> (

let uu____3875 = (__tc goal.FStar_Tactics_Types.context tm)
in (bind uu____3875 (fun uu____3897 -> (match (uu____3897) with
| (tm1, typ, guard) -> begin
(

let typ1 = (bnorm goal.FStar_Tactics_Types.context typ)
in (

let uu____3910 = (

let uu____3913 = (

let uu____3916 = (__apply uopt tm1 typ1)
in (bind uu____3916 (fun uu____3920 -> (proc_guard "apply guard" goal.FStar_Tactics_Types.context guard goal.FStar_Tactics_Types.opts))))
in (focus uu____3913))
in (

let uu____3921 = (

let uu____3924 = (tts goal.FStar_Tactics_Types.context tm1)
in (

let uu____3925 = (tts goal.FStar_Tactics_Types.context typ1)
in (

let uu____3926 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail3 "Cannot instantiate %s (of type %s) to match goal (%s)" uu____3924 uu____3925 uu____3926))))
in (try_unif uu____3910 uu____3921))))
end)))))))))
in (FStar_All.pipe_left (wrap_err "apply") uu____3859)))


let lemma_or_sq : FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun c -> (

let ct = (FStar_Syntax_Util.comp_to_comp_typ_nouniv c)
in (

let uu____3949 = (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____3949) with
| true -> begin
(

let uu____3956 = (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre)::(post)::uu____3975 -> begin
(((FStar_Pervasives_Native.fst pre)), ((FStar_Pervasives_Native.fst post)))
end
| uu____4016 -> begin
(failwith "apply_lemma: impossible: not a lemma")
end)
in (match (uu____3956) with
| (pre, post) -> begin
(

let post1 = (

let uu____4052 = (

let uu____4061 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit)
in (uu____4061)::[])
in (FStar_Syntax_Util.mk_app post uu____4052))
in FStar_Pervasives_Native.Some (((pre), (post1))))
end))
end
| uu____4074 -> begin
(

let uu____4075 = (FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name)
in (match (uu____4075) with
| true -> begin
(

let uu____4082 = (FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.map_opt uu____4082 (fun post -> ((FStar_Syntax_Util.t_true), (post)))))
end
| uu____4101 -> begin
FStar_Pervasives_Native.None
end))
end))))


let apply_lemma : FStar_Syntax_Syntax.term  ->  unit tac = (fun tm -> (

let uu____4115 = (

let uu____4118 = (mlog (fun uu____4123 -> (

let uu____4124 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4124))) (fun uu____4128 -> (

let is_unit_t = (fun t -> (

let uu____4135 = (

let uu____4136 = (FStar_Syntax_Subst.compress t)
in uu____4136.FStar_Syntax_Syntax.n)
in (match (uu____4135) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
true
end
| uu____4140 -> begin
false
end)))
in (

let uu____4141 = (cur_goal ())
in (bind uu____4141 (fun goal -> (

let uu____4147 = (__tc goal.FStar_Tactics_Types.context tm)
in (bind uu____4147 (fun uu____4170 -> (match (uu____4170) with
| (tm1, t, guard) -> begin
(

let uu____4182 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____4182) with
| (bs, comp) -> begin
(

let uu____4209 = (lemma_or_sq comp)
in (match (uu____4209) with
| FStar_Pervasives_Native.None -> begin
(fail "not a lemma or squashed function")
end
| FStar_Pervasives_Native.Some (pre, post) -> begin
(

let uu____4228 = (FStar_List.fold_left (fun uu____4274 uu____4275 -> (match (((uu____4274), (uu____4275))) with
| ((uvs, guard1, subst1), (b, aq)) -> begin
(

let b_t = (FStar_Syntax_Subst.subst subst1 b.FStar_Syntax_Syntax.sort)
in (

let uu____4378 = (is_unit_t b_t)
in (match (uu____4378) with
| true -> begin
(((((FStar_Syntax_Util.exp_unit), (aq)))::uvs), (guard1), ((FStar_Syntax_Syntax.NT (((b), (FStar_Syntax_Util.exp_unit))))::subst1))
end
| uu____4415 -> begin
(

let uu____4416 = (FStar_TypeChecker_Util.new_implicit_var "apply_lemma" goal.FStar_Tactics_Types.goal_ty.FStar_Syntax_Syntax.pos goal.FStar_Tactics_Types.context b_t)
in (match (uu____4416) with
| (u, uu____4446, g_u) -> begin
(

let uu____4460 = (FStar_TypeChecker_Rel.conj_guard guard1 g_u)
in (((((u), (aq)))::uvs), (uu____4460), ((FStar_Syntax_Syntax.NT (((b), (u))))::subst1)))
end))
end)))
end)) (([]), (guard), ([])) bs)
in (match (uu____4228) with
| (uvs, implicits, subst1) -> begin
(

let uvs1 = (FStar_List.rev uvs)
in (

let pre1 = (FStar_Syntax_Subst.subst subst1 pre)
in (

let post1 = (FStar_Syntax_Subst.subst subst1 post)
in (

let uu____4531 = (

let uu____4534 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero post1)
in (do_unify goal.FStar_Tactics_Types.context uu____4534 goal.FStar_Tactics_Types.goal_ty))
in (bind uu____4531 (fun b -> (match ((not (b))) with
| true -> begin
(

let uu____4542 = (tts goal.FStar_Tactics_Types.context tm1)
in (

let uu____4543 = (

let uu____4544 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero post1)
in (tts goal.FStar_Tactics_Types.context uu____4544))
in (

let uu____4545 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail3 "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)" uu____4542 uu____4543 uu____4545))))
end
| uu____4546 -> begin
(

let uu____4547 = (add_implicits implicits.FStar_TypeChecker_Env.implicits)
in (bind uu____4547 (fun uu____4552 -> (

let uu____4553 = (solve goal FStar_Syntax_Util.exp_unit)
in (bind uu____4553 (fun uu____4561 -> (

let is_free_uvar = (fun uv t1 -> (

let free_uvars = (

let uu____4576 = (

let uu____4583 = (FStar_Syntax_Free.uvars t1)
in (FStar_Util.set_elements uu____4583))
in (FStar_List.map FStar_Pervasives_Native.fst uu____4576))
in (FStar_List.existsML (fun u -> (FStar_Syntax_Unionfind.equiv u uv)) free_uvars)))
in (

let appears = (fun uv goals -> (FStar_List.existsML (fun g' -> (is_free_uvar uv g'.FStar_Tactics_Types.goal_ty)) goals))
in (

let checkone = (fun t1 goals -> (

let uu____4632 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____4632) with
| (hd1, uu____4648) -> begin
(match (hd1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____4670) -> begin
(appears uv goals)
end
| uu____4695 -> begin
false
end)
end)))
in (

let uu____4696 = (FStar_All.pipe_right implicits.FStar_TypeChecker_Env.implicits (mapM (fun uu____4768 -> (match (uu____4768) with
| (_msg, env, _uvar, term, typ, uu____4796) -> begin
(

let uu____4797 = (FStar_Syntax_Util.head_and_args term)
in (match (uu____4797) with
| (hd1, uu____4823) -> begin
(

let uu____4844 = (

let uu____4845 = (FStar_Syntax_Subst.compress hd1)
in uu____4845.FStar_Syntax_Syntax.n)
in (match (uu____4844) with
| FStar_Syntax_Syntax.Tm_uvar (uu____4858) -> begin
(

let uu____4875 = (

let uu____4884 = (

let uu____4887 = (

let uu___101_4888 = goal
in (

let uu____4889 = (bnorm goal.FStar_Tactics_Types.context term)
in (

let uu____4890 = (bnorm goal.FStar_Tactics_Types.context typ)
in {FStar_Tactics_Types.context = uu___101_4888.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu____4889; FStar_Tactics_Types.goal_ty = uu____4890; FStar_Tactics_Types.opts = uu___101_4888.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___101_4888.FStar_Tactics_Types.is_guard})))
in (uu____4887)::[])
in ((uu____4884), ([])))
in (ret uu____4875))
end
| uu____4903 -> begin
(

let g_typ = (

let uu____4905 = (FStar_Options.__temp_fast_implicits ())
in (match (uu____4905) with
| true -> begin
(FStar_TypeChecker_TcTerm.check_type_of_well_typed_term false env term typ)
end
| uu____4906 -> begin
(

let term1 = (bnorm env term)
in (

let uu____4908 = (

let uu____4915 = (FStar_TypeChecker_Env.set_expected_typ env typ)
in (env.FStar_TypeChecker_Env.type_of uu____4915 term1))
in (match (uu____4908) with
| (uu____4916, uu____4917, g_typ) -> begin
g_typ
end)))
end))
in (

let uu____4919 = (goal_from_guard "apply_lemma solved arg" goal.FStar_Tactics_Types.context g_typ goal.FStar_Tactics_Types.opts)
in (bind uu____4919 (fun uu___65_4935 -> (match (uu___65_4935) with
| FStar_Pervasives_Native.None -> begin
(ret (([]), ([])))
end
| FStar_Pervasives_Native.Some (g) -> begin
(ret (([]), ((g)::[])))
end)))))
end))
end))
end))))
in (bind uu____4696 (fun goals_ -> (

let sub_goals = (

let uu____5003 = (FStar_List.map FStar_Pervasives_Native.fst goals_)
in (FStar_List.flatten uu____5003))
in (

let smt_goals = (

let uu____5025 = (FStar_List.map FStar_Pervasives_Native.snd goals_)
in (FStar_List.flatten uu____5025))
in (

let rec filter' = (fun f xs -> (match (xs) with
| [] -> begin
[]
end
| (x)::xs1 -> begin
(

let uu____5086 = (f x xs1)
in (match (uu____5086) with
| true -> begin
(

let uu____5089 = (filter' f xs1)
in (x)::uu____5089)
end
| uu____5092 -> begin
(filter' f xs1)
end))
end))
in (

let sub_goals1 = (filter' (fun g goals -> (

let uu____5103 = (checkone g.FStar_Tactics_Types.witness goals)
in (not (uu____5103)))) sub_goals)
in (

let uu____5104 = (proc_guard "apply_lemma guard" goal.FStar_Tactics_Types.context guard goal.FStar_Tactics_Types.opts)
in (bind uu____5104 (fun uu____5109 -> (

let uu____5110 = (

let uu____5113 = (

let uu____5114 = (

let uu____5115 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero pre1)
in (istrivial goal.FStar_Tactics_Types.context uu____5115))
in (not (uu____5114)))
in (match (uu____5113) with
| true -> begin
(add_irrelevant_goal "apply_lemma precondition" goal.FStar_Tactics_Types.context pre1 goal.FStar_Tactics_Types.opts)
end
| uu____5118 -> begin
(ret ())
end))
in (bind uu____5110 (fun uu____5121 -> (

let uu____5122 = (add_smt_goals smt_goals)
in (bind uu____5122 (fun uu____5126 -> (add_goals sub_goals1))))))))))))))))))))))))))
end)))))))
end))
end))
end))
end))))))))))
in (focus uu____4118))
in (FStar_All.pipe_left (wrap_err "apply_lemma") uu____4115)))


let destruct_eq' : FStar_Reflection_Data.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun typ -> (

let uu____5148 = (FStar_Syntax_Util.destruct_typ_as_formula typ)
in (match (uu____5148) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (l, (uu____5158)::((e1, uu____5160))::((e2, uu____5162))::[])) when (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) -> begin
FStar_Pervasives_Native.Some (((e1), (e2)))
end
| uu____5221 -> begin
FStar_Pervasives_Native.None
end)))


let destruct_eq : FStar_Reflection_Data.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun typ -> (

let uu____5245 = (destruct_eq' typ)
in (match (uu____5245) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5275 = (FStar_Syntax_Util.un_squash typ)
in (match (uu____5275) with
| FStar_Pervasives_Native.Some (typ1) -> begin
(destruct_eq' typ1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end)))


let split_env : FStar_Syntax_Syntax.bv  ->  env  ->  (env * FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.option = (fun bvar e -> (

let rec aux = (fun e1 -> (

let uu____5337 = (FStar_TypeChecker_Env.pop_bv e1)
in (match (uu____5337) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (bv', e') -> begin
(match ((FStar_Syntax_Syntax.bv_eq bvar bv')) with
| true -> begin
FStar_Pervasives_Native.Some (((e'), ([])))
end
| uu____5384 -> begin
(

let uu____5385 = (aux e')
in (FStar_Util.map_opt uu____5385 (fun uu____5409 -> (match (uu____5409) with
| (e'', bvs) -> begin
((e''), ((bv')::bvs))
end))))
end)
end)))
in (

let uu____5430 = (aux e)
in (FStar_Util.map_opt uu____5430 (fun uu____5454 -> (match (uu____5454) with
| (e', bvs) -> begin
((e'), ((FStar_List.rev bvs)))
end))))))


let push_bvs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_TypeChecker_Env.env = (fun e bvs -> (FStar_List.fold_left (fun e1 b -> (FStar_TypeChecker_Env.push_bv e1 b)) e bvs))


let subst_goal : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Tactics_Types.goal  ->  FStar_Tactics_Types.goal FStar_Pervasives_Native.option = (fun b1 b2 s g -> (

let uu____5521 = (split_env b1 g.FStar_Tactics_Types.context)
in (FStar_Util.map_opt uu____5521 (fun uu____5545 -> (match (uu____5545) with
| (e0, bvs) -> begin
(

let s1 = (fun bv -> (

let uu___102_5564 = bv
in (

let uu____5565 = (FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___102_5564.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___102_5564.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5565})))
in (

let bvs1 = (FStar_List.map s1 bvs)
in (

let c = (push_bvs e0 ((b2)::bvs1))
in (

let w = (FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness)
in (

let t = (FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty)
in (

let uu___103_5574 = g
in {FStar_Tactics_Types.context = c; FStar_Tactics_Types.witness = w; FStar_Tactics_Types.goal_ty = t; FStar_Tactics_Types.opts = uu___103_5574.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___103_5574.FStar_Tactics_Types.is_guard}))))))
end)))))


let rewrite : FStar_Syntax_Syntax.binder  ->  unit tac = (fun h -> (

let uu____5584 = (cur_goal ())
in (bind uu____5584 (fun goal -> (

let uu____5592 = h
in (match (uu____5592) with
| (bv, uu____5596) -> begin
(mlog (fun uu____5600 -> (

let uu____5601 = (FStar_Syntax_Print.bv_to_string bv)
in (

let uu____5602 = (tts goal.FStar_Tactics_Types.context bv.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5601 uu____5602)))) (fun uu____5605 -> (

let uu____5606 = (split_env bv goal.FStar_Tactics_Types.context)
in (match (uu____5606) with
| FStar_Pervasives_Native.None -> begin
(fail "rewrite: binder not found in environment")
end
| FStar_Pervasives_Native.Some (e0, bvs) -> begin
(

let uu____5635 = (destruct_eq bv.FStar_Syntax_Syntax.sort)
in (match (uu____5635) with
| FStar_Pervasives_Native.Some (x, e) -> begin
(

let uu____5650 = (

let uu____5651 = (FStar_Syntax_Subst.compress x)
in uu____5651.FStar_Syntax_Syntax.n)
in (match (uu____5650) with
| FStar_Syntax_Syntax.Tm_name (x1) -> begin
(

let s = (FStar_Syntax_Syntax.NT (((x1), (e))))::[]
in (

let s1 = (fun bv1 -> (

let uu___104_5666 = bv1
in (

let uu____5667 = (FStar_Syntax_Subst.subst s bv1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___104_5666.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___104_5666.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5667})))
in (

let bvs1 = (FStar_List.map s1 bvs)
in (

let uu____5673 = (

let uu___105_5674 = goal
in (

let uu____5675 = (push_bvs e0 ((bv)::bvs1))
in (

let uu____5676 = (FStar_Syntax_Subst.subst s goal.FStar_Tactics_Types.witness)
in (

let uu____5677 = (FStar_Syntax_Subst.subst s goal.FStar_Tactics_Types.goal_ty)
in {FStar_Tactics_Types.context = uu____5675; FStar_Tactics_Types.witness = uu____5676; FStar_Tactics_Types.goal_ty = uu____5677; FStar_Tactics_Types.opts = uu___105_5674.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___105_5674.FStar_Tactics_Types.is_guard}))))
in (replace_cur uu____5673)))))
end
| uu____5678 -> begin
(fail "rewrite: Not an equality hypothesis with a variable on the LHS")
end))
end
| uu____5679 -> begin
(fail "rewrite: Not an equality hypothesis")
end))
end))))
end))))))


let rename_to : FStar_Syntax_Syntax.binder  ->  Prims.string  ->  unit tac = (fun b s -> (

let uu____5700 = (cur_goal ())
in (bind uu____5700 (fun goal -> (

let uu____5711 = b
in (match (uu____5711) with
| (bv, uu____5715) -> begin
(

let bv' = (

let uu____5717 = (

let uu___106_5718 = bv
in (

let uu____5719 = (FStar_Ident.mk_ident ((s), (bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
in {FStar_Syntax_Syntax.ppname = uu____5719; FStar_Syntax_Syntax.index = uu___106_5718.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___106_5718.FStar_Syntax_Syntax.sort}))
in (FStar_Syntax_Syntax.freshen_bv uu____5717))
in (

let s1 = (

let uu____5723 = (

let uu____5724 = (

let uu____5731 = (FStar_Syntax_Syntax.bv_to_name bv')
in ((bv), (uu____5731)))
in FStar_Syntax_Syntax.NT (uu____5724))
in (uu____5723)::[])
in (

let uu____5732 = (subst_goal bv bv' s1 goal)
in (match (uu____5732) with
| FStar_Pervasives_Native.None -> begin
(fail "rename_to: binder not found in environment")
end
| FStar_Pervasives_Native.Some (goal1) -> begin
(replace_cur goal1)
end))))
end))))))


let binder_retype : FStar_Syntax_Syntax.binder  ->  unit tac = (fun b -> (

let uu____5747 = (cur_goal ())
in (bind uu____5747 (fun goal -> (

let uu____5756 = b
in (match (uu____5756) with
| (bv, uu____5760) -> begin
(

let uu____5761 = (split_env bv goal.FStar_Tactics_Types.context)
in (match (uu____5761) with
| FStar_Pervasives_Native.None -> begin
(fail "binder_retype: binder is not present in environment")
end
| FStar_Pervasives_Native.Some (e0, bvs) -> begin
(

let uu____5790 = (FStar_Syntax_Util.type_u ())
in (match (uu____5790) with
| (ty, u) -> begin
(

let uu____5799 = (new_uvar "binder_retype" e0 ty)
in (bind uu____5799 (fun t' -> (

let bv'' = (

let uu___107_5809 = bv
in {FStar_Syntax_Syntax.ppname = uu___107_5809.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___107_5809.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t'})
in (

let s = (

let uu____5813 = (

let uu____5814 = (

let uu____5821 = (FStar_Syntax_Syntax.bv_to_name bv'')
in ((bv), (uu____5821)))
in FStar_Syntax_Syntax.NT (uu____5814))
in (uu____5813)::[])
in (

let bvs1 = (FStar_List.map (fun b1 -> (

let uu___108_5829 = b1
in (

let uu____5830 = (FStar_Syntax_Subst.subst s b1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___108_5829.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___108_5829.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5830}))) bvs)
in (

let env' = (push_bvs e0 ((bv'')::bvs1))
in (bind __dismiss (fun uu____5836 -> (

let uu____5837 = (

let uu____5840 = (

let uu____5843 = (

let uu___109_5844 = goal
in (

let uu____5845 = (FStar_Syntax_Subst.subst s goal.FStar_Tactics_Types.witness)
in (

let uu____5846 = (FStar_Syntax_Subst.subst s goal.FStar_Tactics_Types.goal_ty)
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = uu____5845; FStar_Tactics_Types.goal_ty = uu____5846; FStar_Tactics_Types.opts = uu___109_5844.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___109_5844.FStar_Tactics_Types.is_guard})))
in (uu____5843)::[])
in (add_goals uu____5840))
in (bind uu____5837 (fun uu____5849 -> (

let uu____5850 = (FStar_Syntax_Util.mk_eq2 (FStar_Syntax_Syntax.U_succ (u)) ty bv.FStar_Syntax_Syntax.sort t')
in (add_irrelevant_goal "binder_retype equation" e0 uu____5850 goal.FStar_Tactics_Types.opts))))))))))))))
end))
end))
end))))))


let norm_binder_type : FStar_Syntax_Embeddings.norm_step Prims.list  ->  FStar_Syntax_Syntax.binder  ->  unit tac = (fun s b -> (

let uu____5869 = (cur_goal ())
in (bind uu____5869 (fun goal -> (

let uu____5878 = b
in (match (uu____5878) with
| (bv, uu____5882) -> begin
(

let uu____5883 = (split_env bv goal.FStar_Tactics_Types.context)
in (match (uu____5883) with
| FStar_Pervasives_Native.None -> begin
(fail "binder_retype: binder is not present in environment")
end
| FStar_Pervasives_Native.Some (e0, bvs) -> begin
(

let steps = (

let uu____5915 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldTac)::[]) uu____5915))
in (

let sort' = (normalize steps e0 bv.FStar_Syntax_Syntax.sort)
in (

let bv' = (

let uu___110_5920 = bv
in {FStar_Syntax_Syntax.ppname = uu___110_5920.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___110_5920.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort'})
in (

let env' = (push_bvs e0 ((bv')::bvs))
in (replace_cur (

let uu___111_5924 = goal
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = uu___111_5924.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___111_5924.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___111_5924.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___111_5924.FStar_Tactics_Types.is_guard}))))))
end))
end))))))


let revert : unit  ->  unit tac = (fun uu____5931 -> (

let uu____5934 = (cur_goal ())
in (bind uu____5934 (fun goal -> (

let uu____5940 = (FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context)
in (match (uu____5940) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot revert; empty context")
end
| FStar_Pervasives_Native.Some (x, env') -> begin
(

let typ' = (

let uu____5962 = (FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty)
in (FStar_Syntax_Util.arrow ((((x), (FStar_Pervasives_Native.None)))::[]) uu____5962))
in (

let w' = (FStar_Syntax_Util.abs ((((x), (FStar_Pervasives_Native.None)))::[]) goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None)
in (replace_cur (

let uu___112_5996 = goal
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = w'; FStar_Tactics_Types.goal_ty = typ'; FStar_Tactics_Types.opts = uu___112_5996.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___112_5996.FStar_Tactics_Types.is_guard}))))
end))))))


let free_in : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun bv t -> (

let uu____6007 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_mem bv uu____6007)))


let rec clear : FStar_Syntax_Syntax.binder  ->  unit tac = (fun b -> (

let bv = (FStar_Pervasives_Native.fst b)
in (

let uu____6020 = (cur_goal ())
in (bind uu____6020 (fun goal -> (mlog (fun uu____6028 -> (

let uu____6029 = (FStar_Syntax_Print.binder_to_string b)
in (

let uu____6030 = (

let uu____6031 = (

let uu____6032 = (FStar_TypeChecker_Env.all_binders goal.FStar_Tactics_Types.context)
in (FStar_All.pipe_right uu____6032 FStar_List.length))
in (FStar_All.pipe_right uu____6031 FStar_Util.string_of_int))
in (FStar_Util.print2 "Clear of (%s), env has %s binders\n" uu____6029 uu____6030)))) (fun uu____6043 -> (

let uu____6044 = (split_env bv goal.FStar_Tactics_Types.context)
in (match (uu____6044) with
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

let uu____6091 = (free_in bv bv'.FStar_Syntax_Syntax.sort)
in (match (uu____6091) with
| true -> begin
(

let uu____6094 = (

let uu____6095 = (FStar_Syntax_Print.bv_to_string bv')
in (FStar_Util.format1 "Cannot clear; binder present in the type of %s" uu____6095))
in (fail uu____6094))
end
| uu____6096 -> begin
(check1 bvs2)
end))
end))
in (

let uu____6097 = (free_in bv goal.FStar_Tactics_Types.goal_ty)
in (match (uu____6097) with
| true -> begin
(fail "Cannot clear; binder present in goal")
end
| uu____6100 -> begin
(

let uu____6101 = (check1 bvs)
in (bind uu____6101 (fun uu____6107 -> (

let env' = (push_bvs e' bvs)
in (

let uu____6109 = (new_uvar "clear.witness" env' goal.FStar_Tactics_Types.goal_ty)
in (bind uu____6109 (fun ut -> (

let uu____6115 = (do_unify goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.witness ut)
in (bind uu____6115 (fun b1 -> (match (b1) with
| true -> begin
(replace_cur (

let uu___113_6124 = goal
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = ut; FStar_Tactics_Types.goal_ty = uu___113_6124.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___113_6124.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___113_6124.FStar_Tactics_Types.is_guard}))
end
| uu____6125 -> begin
(fail "Cannot clear; binder appears in witness")
end)))))))))))
end)))
end)))))))))


let clear_top : unit  ->  unit tac = (fun uu____6132 -> (

let uu____6135 = (cur_goal ())
in (bind uu____6135 (fun goal -> (

let uu____6141 = (FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context)
in (match (uu____6141) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot clear; empty context")
end
| FStar_Pervasives_Native.Some (x, uu____6155) -> begin
(

let uu____6160 = (FStar_Syntax_Syntax.mk_binder x)
in (clear uu____6160))
end))))))


let prune : Prims.string  ->  unit tac = (fun s -> (

let uu____6170 = (cur_goal ())
in (bind uu____6170 (fun g -> (

let ctx = g.FStar_Tactics_Types.context
in (

let ctx' = (

let uu____6180 = (FStar_Ident.path_of_text s)
in (FStar_TypeChecker_Env.rem_proof_ns ctx uu____6180))
in (

let g' = (

let uu___114_6182 = g
in {FStar_Tactics_Types.context = ctx'; FStar_Tactics_Types.witness = uu___114_6182.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___114_6182.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___114_6182.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___114_6182.FStar_Tactics_Types.is_guard})
in (bind __dismiss (fun uu____6184 -> (add_goals ((g')::[])))))))))))


let addns : Prims.string  ->  unit tac = (fun s -> (

let uu____6194 = (cur_goal ())
in (bind uu____6194 (fun g -> (

let ctx = g.FStar_Tactics_Types.context
in (

let ctx' = (

let uu____6204 = (FStar_Ident.path_of_text s)
in (FStar_TypeChecker_Env.add_proof_ns ctx uu____6204))
in (

let g' = (

let uu___115_6206 = g
in {FStar_Tactics_Types.context = ctx'; FStar_Tactics_Types.witness = uu___115_6206.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___115_6206.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___115_6206.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___115_6206.FStar_Tactics_Types.is_guard})
in (bind __dismiss (fun uu____6208 -> (add_goals ((g')::[])))))))))))


let rec tac_fold_env : FStar_Tactics_Types.direction  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac)  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun d f env t -> (

let tn = (

let uu____6248 = (FStar_Syntax_Subst.compress t)
in uu____6248.FStar_Syntax_Syntax.n)
in (

let uu____6251 = (match ((Prims.op_Equality d FStar_Tactics_Types.TopDown)) with
| true -> begin
(f env (

let uu___119_6257 = t
in {FStar_Syntax_Syntax.n = tn; FStar_Syntax_Syntax.pos = uu___119_6257.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___119_6257.FStar_Syntax_Syntax.vars}))
end
| uu____6258 -> begin
(ret t)
end)
in (bind uu____6251 (fun t1 -> (

let ff = (tac_fold_env d f env)
in (

let tn1 = (

let uu____6273 = (

let uu____6274 = (FStar_Syntax_Subst.compress t1)
in uu____6274.FStar_Syntax_Syntax.n)
in (match (uu____6273) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____6301 = (ff hd1)
in (bind uu____6301 (fun hd2 -> (

let fa = (fun uu____6323 -> (match (uu____6323) with
| (a, q) -> begin
(

let uu____6336 = (ff a)
in (bind uu____6336 (fun a1 -> (ret ((a1), (q))))))
end))
in (

let uu____6349 = (mapM fa args)
in (bind uu____6349 (fun args1 -> (ret (FStar_Syntax_Syntax.Tm_app (((hd2), (args1))))))))))))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, k) -> begin
(

let uu____6409 = (FStar_Syntax_Subst.open_term bs t2)
in (match (uu____6409) with
| (bs1, t') -> begin
(

let uu____6418 = (

let uu____6421 = (FStar_TypeChecker_Env.push_binders env bs1)
in (tac_fold_env d f uu____6421 t'))
in (bind uu____6418 (fun t'' -> (

let uu____6425 = (

let uu____6426 = (

let uu____6443 = (FStar_Syntax_Subst.close_binders bs1)
in (

let uu____6444 = (FStar_Syntax_Subst.close bs1 t'')
in ((uu____6443), (uu____6444), (k))))
in FStar_Syntax_Syntax.Tm_abs (uu____6426))
in (ret uu____6425)))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(ret tn)
end
| FStar_Syntax_Syntax.Tm_match (hd1, brs) -> begin
(

let uu____6503 = (ff hd1)
in (bind uu____6503 (fun hd2 -> (

let ffb = (fun br -> (

let uu____6518 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____6518) with
| (pat, w, e) -> begin
(

let bvs = (FStar_Syntax_Syntax.pat_bvs pat)
in (

let ff1 = (

let uu____6550 = (FStar_TypeChecker_Env.push_bvs env bvs)
in (tac_fold_env d f uu____6550))
in (

let uu____6551 = (ff1 e)
in (bind uu____6551 (fun e1 -> (

let br1 = (FStar_Syntax_Subst.close_branch ((pat), (w), (e1)))
in (ret br1)))))))
end)))
in (

let uu____6564 = (mapM ffb brs)
in (bind uu____6564 (fun brs1 -> (ret (FStar_Syntax_Syntax.Tm_match (((hd2), (brs1))))))))))))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (bv); FStar_Syntax_Syntax.lbunivs = uu____6578; FStar_Syntax_Syntax.lbtyp = uu____6579; FStar_Syntax_Syntax.lbeff = uu____6580; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu____6582; FStar_Syntax_Syntax.lbpos = uu____6583})::[]), e) -> begin
(

let lb = (

let uu____6608 = (

let uu____6609 = (FStar_Syntax_Subst.compress t1)
in uu____6609.FStar_Syntax_Syntax.n)
in (match (uu____6608) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), uu____6613) -> begin
lb
end
| uu____6626 -> begin
(failwith "impossible")
end))
in (

let fflb = (fun lb1 -> (

let uu____6635 = (ff lb1.FStar_Syntax_Syntax.lbdef)
in (bind uu____6635 (fun def1 -> (ret (

let uu___116_6641 = lb1
in {FStar_Syntax_Syntax.lbname = uu___116_6641.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___116_6641.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___116_6641.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___116_6641.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def1; FStar_Syntax_Syntax.lbattrs = uu___116_6641.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___116_6641.FStar_Syntax_Syntax.lbpos}))))))
in (

let uu____6642 = (fflb lb)
in (bind uu____6642 (fun lb1 -> (

let uu____6652 = (

let uu____6657 = (

let uu____6658 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____6658)::[])
in (FStar_Syntax_Subst.open_term uu____6657 e))
in (match (uu____6652) with
| (bs, e1) -> begin
(

let ff1 = (

let uu____6670 = (FStar_TypeChecker_Env.push_binders env bs)
in (tac_fold_env d f uu____6670))
in (

let uu____6671 = (ff1 e1)
in (bind uu____6671 (fun e2 -> (

let e3 = (FStar_Syntax_Subst.close bs e2)
in (ret (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e3))))))))))
end)))))))
end
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e) -> begin
(

let fflb = (fun lb -> (

let uu____6710 = (ff lb.FStar_Syntax_Syntax.lbdef)
in (bind uu____6710 (fun def -> (ret (

let uu___117_6716 = lb
in {FStar_Syntax_Syntax.lbname = uu___117_6716.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___117_6716.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___117_6716.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___117_6716.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu___117_6716.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___117_6716.FStar_Syntax_Syntax.lbpos}))))))
in (

let uu____6717 = (FStar_Syntax_Subst.open_let_rec lbs e)
in (match (uu____6717) with
| (lbs1, e1) -> begin
(

let uu____6732 = (mapM fflb lbs1)
in (bind uu____6732 (fun lbs2 -> (

let uu____6744 = (ff e1)
in (bind uu____6744 (fun e2 -> (

let uu____6752 = (FStar_Syntax_Subst.close_let_rec lbs2 e2)
in (match (uu____6752) with
| (lbs3, e3) -> begin
(ret (FStar_Syntax_Syntax.Tm_let (((((true), (lbs3))), (e3)))))
end))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, asc, eff) -> begin
(

let uu____6818 = (ff t2)
in (bind uu____6818 (fun t3 -> (ret (FStar_Syntax_Syntax.Tm_ascribed (((t3), (asc), (eff))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t2, m) -> begin
(

let uu____6847 = (ff t2)
in (bind uu____6847 (fun t3 -> (ret (FStar_Syntax_Syntax.Tm_meta (((t3), (m))))))))
end
| uu____6852 -> begin
(ret tn)
end))
in (bind tn1 (fun tn2 -> (

let t' = (

let uu___118_6859 = t1
in {FStar_Syntax_Syntax.n = tn2; FStar_Syntax_Syntax.pos = uu___118_6859.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___118_6859.FStar_Syntax_Syntax.vars})
in (match ((Prims.op_Equality d FStar_Tactics_Types.BottomUp)) with
| true -> begin
(f env t')
end
| uu____6862 -> begin
(ret t')
end)))))))))))


let pointwise_rec : FStar_Tactics_Types.proofstate  ->  unit tac  ->  FStar_Options.optionstate  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun ps tau opts env t -> (

let uu____6898 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____6898) with
| (t1, lcomp, g) -> begin
(

let uu____6910 = ((

let uu____6913 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp)
in (not (uu____6913))) || (

let uu____6915 = (FStar_TypeChecker_Rel.is_trivial g)
in (not (uu____6915))))
in (match (uu____6910) with
| true -> begin
(ret t1)
end
| uu____6918 -> begin
(

let rewrite_eq = (

let typ = lcomp.FStar_Syntax_Syntax.res_typ
in (

let uu____6925 = (new_uvar "pointwise_rec" env typ)
in (bind uu____6925 (fun ut -> ((log ps (fun uu____6936 -> (

let uu____6937 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6938 = (FStar_Syntax_Print.term_to_string ut)
in (FStar_Util.print2 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n" uu____6937 uu____6938)))));
(

let uu____6939 = (

let uu____6942 = (

let uu____6943 = (FStar_TypeChecker_TcTerm.universe_of env typ)
in (FStar_Syntax_Util.mk_eq2 uu____6943 typ t1 ut))
in (add_irrelevant_goal "pointwise_rec equation" env uu____6942 opts))
in (bind uu____6939 (fun uu____6946 -> (

let uu____6947 = (bind tau (fun uu____6953 -> (

let ut1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env ut)
in ((log ps (fun uu____6959 -> (

let uu____6960 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6961 = (FStar_Syntax_Print.term_to_string ut1)
in (FStar_Util.print2 "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n" uu____6960 uu____6961)))));
(ret ut1);
))))
in (focus uu____6947)))));
)))))
in (

let uu____6962 = (trytac' rewrite_eq)
in (bind uu____6962 (fun x -> (match (x) with
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
| uu____7072 -> begin
c
end))
in (

let maybe_continue = (fun ctrl1 t1 k -> (match ((Prims.op_Equality ctrl1 globalStop)) with
| true -> begin
(ret ((t1), (globalStop)))
end
| uu____7122 -> begin
(match ((Prims.op_Equality ctrl1 proceedToNextSubtree)) with
| true -> begin
(ret ((t1), (keepGoing)))
end
| uu____7133 -> begin
(k t1)
end)
end))
in (

let uu____7134 = (FStar_Syntax_Subst.compress t)
in (maybe_continue ctrl uu____7134 (fun t1 -> (

let uu____7138 = (f env (

let uu___122_7147 = t1
in {FStar_Syntax_Syntax.n = t1.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = uu___122_7147.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___122_7147.FStar_Syntax_Syntax.vars}))
in (bind uu____7138 (fun uu____7159 -> (match (uu____7159) with
| (t2, ctrl1) -> begin
(maybe_continue ctrl1 t2 (fun t3 -> (

let uu____7178 = (

let uu____7179 = (FStar_Syntax_Subst.compress t3)
in uu____7179.FStar_Syntax_Syntax.n)
in (match (uu____7178) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____7212 = (ctrl_tac_fold f env ctrl1 hd1)
in (bind uu____7212 (fun uu____7237 -> (match (uu____7237) with
| (hd2, ctrl2) -> begin
(

let ctrl3 = (keep_going ctrl2)
in (

let uu____7253 = (ctrl_tac_fold_args f env ctrl3 args)
in (bind uu____7253 (fun uu____7280 -> (match (uu____7280) with
| (args1, ctrl4) -> begin
(ret (((

let uu___120_7310 = t3
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app (((hd2), (args1))); FStar_Syntax_Syntax.pos = uu___120_7310.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___120_7310.FStar_Syntax_Syntax.vars})), (ctrl4)))
end)))))
end))))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t4, k) -> begin
(

let uu____7336 = (FStar_Syntax_Subst.open_term bs t4)
in (match (uu____7336) with
| (bs1, t') -> begin
(

let uu____7351 = (

let uu____7358 = (FStar_TypeChecker_Env.push_binders env bs1)
in (ctrl_tac_fold f uu____7358 ctrl1 t'))
in (bind uu____7351 (fun uu____7376 -> (match (uu____7376) with
| (t'', ctrl2) -> begin
(

let uu____7391 = (

let uu____7398 = (

let uu___121_7401 = t4
in (

let uu____7404 = (

let uu____7405 = (

let uu____7422 = (FStar_Syntax_Subst.close_binders bs1)
in (

let uu____7423 = (FStar_Syntax_Subst.close bs1 t'')
in ((uu____7422), (uu____7423), (k))))
in FStar_Syntax_Syntax.Tm_abs (uu____7405))
in {FStar_Syntax_Syntax.n = uu____7404; FStar_Syntax_Syntax.pos = uu___121_7401.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___121_7401.FStar_Syntax_Syntax.vars}))
in ((uu____7398), (ctrl2)))
in (ret uu____7391))
end))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(ret ((t3), (ctrl1)))
end
| uu____7456 -> begin
(ret ((t3), (ctrl1)))
end))))
end))))))))))
and ctrl_tac_fold_args : (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term ctrl_tac)  ->  env  ->  ctrl  ->  FStar_Syntax_Syntax.arg Prims.list  ->  FStar_Syntax_Syntax.arg Prims.list ctrl_tac = (fun f env ctrl ts -> (match (ts) with
| [] -> begin
(ret (([]), (ctrl)))
end
| ((t, q))::ts1 -> begin
(

let uu____7507 = (ctrl_tac_fold f env ctrl t)
in (bind uu____7507 (fun uu____7535 -> (match (uu____7535) with
| (t1, ctrl1) -> begin
(

let uu____7554 = (ctrl_tac_fold_args f env ctrl1 ts1)
in (bind uu____7554 (fun uu____7585 -> (match (uu____7585) with
| (ts2, ctrl2) -> begin
(ret (((((t1), (q)))::ts2), (ctrl2)))
end))))
end))))
end))


let rewrite_rec : FStar_Tactics_Types.proofstate  ->  (FStar_Syntax_Syntax.term  ->  rewrite_result ctrl_tac)  ->  unit tac  ->  FStar_Options.optionstate  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term ctrl_tac = (fun ps ctrl rewriter opts env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let uu____7681 = (

let uu____7688 = (add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true opts)
in (bind uu____7688 (fun uu____7697 -> (

let uu____7698 = (ctrl t1)
in (bind uu____7698 (fun res -> (

let uu____7721 = (trivial ())
in (bind uu____7721 (fun uu____7729 -> (ret res))))))))))
in (bind uu____7681 (fun uu____7745 -> (match (uu____7745) with
| (should_rewrite, ctrl1) -> begin
(match ((not (should_rewrite))) with
| true -> begin
(ret ((t1), (ctrl1)))
end
| uu____7768 -> begin
(

let uu____7769 = (FStar_TypeChecker_TcTerm.tc_term env t1)
in (match (uu____7769) with
| (t2, lcomp, g) -> begin
(

let uu____7785 = ((

let uu____7788 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp)
in (not (uu____7788))) || (

let uu____7790 = (FStar_TypeChecker_Rel.is_trivial g)
in (not (uu____7790))))
in (match (uu____7785) with
| true -> begin
(ret ((t2), (globalStop)))
end
| uu____7801 -> begin
(

let typ = lcomp.FStar_Syntax_Syntax.res_typ
in (

let uu____7805 = (new_uvar "pointwise_rec" env typ)
in (bind uu____7805 (fun ut -> ((log ps (fun uu____7820 -> (

let uu____7821 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____7822 = (FStar_Syntax_Print.term_to_string ut)
in (FStar_Util.print2 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n" uu____7821 uu____7822)))));
(

let uu____7823 = (

let uu____7826 = (

let uu____7827 = (FStar_TypeChecker_TcTerm.universe_of env typ)
in (FStar_Syntax_Util.mk_eq2 uu____7827 typ t2 ut))
in (add_irrelevant_goal "rewrite_rec equation" env uu____7826 opts))
in (bind uu____7823 (fun uu____7834 -> (

let uu____7835 = (bind rewriter (fun uu____7849 -> (

let ut1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env ut)
in ((log ps (fun uu____7855 -> (

let uu____7856 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____7857 = (FStar_Syntax_Print.term_to_string ut1)
in (FStar_Util.print2 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n" uu____7856 uu____7857)))));
(ret ((ut1), (ctrl1)));
))))
in (focus uu____7835)))));
)))))
end))
end))
end)
end))))))


let topdown_rewrite : (FStar_Syntax_Syntax.term  ->  (Prims.bool * FStar_BigInt.t) tac)  ->  unit tac  ->  unit tac = (fun ctrl rewriter -> (bind get (fun ps -> (

let uu____7905 = (match (ps.FStar_Tactics_Types.goals) with
| (g)::gs -> begin
((g), (gs))
end
| [] -> begin
(failwith "Pointwise: no goals")
end)
in (match (uu____7905) with
| (g, gs) -> begin
(

let gt1 = g.FStar_Tactics_Types.goal_ty
in ((log ps (fun uu____7942 -> (

let uu____7943 = (FStar_Syntax_Print.term_to_string gt1)
in (FStar_Util.print1 "Topdown_rewrite starting with %s\n" uu____7943))));
(bind dismiss_all (fun uu____7946 -> (

let uu____7947 = (ctrl_tac_fold (rewrite_rec ps ctrl rewriter g.FStar_Tactics_Types.opts) g.FStar_Tactics_Types.context keepGoing gt1)
in (bind uu____7947 (fun uu____7965 -> (match (uu____7965) with
| (gt', uu____7973) -> begin
((log ps (fun uu____7977 -> (

let uu____7978 = (FStar_Syntax_Print.term_to_string gt')
in (FStar_Util.print1 "Topdown_rewrite seems to have succeded with %s\n" uu____7978))));
(

let uu____7979 = (push_goals gs)
in (bind uu____7979 (fun uu____7983 -> (add_goals (((

let uu___123_7985 = g
in {FStar_Tactics_Types.context = uu___123_7985.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___123_7985.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = gt'; FStar_Tactics_Types.opts = uu___123_7985.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___123_7985.FStar_Tactics_Types.is_guard}))::[])))));
)
end))))));
))
end)))))


let pointwise : FStar_Tactics_Types.direction  ->  unit tac  ->  unit tac = (fun d tau -> (bind get (fun ps -> (

let uu____8011 = (match (ps.FStar_Tactics_Types.goals) with
| (g)::gs -> begin
((g), (gs))
end
| [] -> begin
(failwith "Pointwise: no goals")
end)
in (match (uu____8011) with
| (g, gs) -> begin
(

let gt1 = g.FStar_Tactics_Types.goal_ty
in ((log ps (fun uu____8048 -> (

let uu____8049 = (FStar_Syntax_Print.term_to_string gt1)
in (FStar_Util.print1 "Pointwise starting with %s\n" uu____8049))));
(bind dismiss_all (fun uu____8052 -> (

let uu____8053 = (tac_fold_env d (pointwise_rec ps tau g.FStar_Tactics_Types.opts) g.FStar_Tactics_Types.context gt1)
in (bind uu____8053 (fun gt' -> ((log ps (fun uu____8063 -> (

let uu____8064 = (FStar_Syntax_Print.term_to_string gt')
in (FStar_Util.print1 "Pointwise seems to have succeded with %s\n" uu____8064))));
(

let uu____8065 = (push_goals gs)
in (bind uu____8065 (fun uu____8069 -> (add_goals (((

let uu___124_8071 = g
in {FStar_Tactics_Types.context = uu___124_8071.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___124_8071.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = gt'; FStar_Tactics_Types.opts = uu___124_8071.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___124_8071.FStar_Tactics_Types.is_guard}))::[])))));
))))));
))
end)))))


let trefl : unit  ->  unit tac = (fun uu____8078 -> (

let uu____8081 = (cur_goal ())
in (bind uu____8081 (fun g -> (

let uu____8099 = (FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty)
in (match (uu____8099) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____8111 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____8111) with
| (hd1, args) -> begin
(

let uu____8144 = (

let uu____8157 = (

let uu____8158 = (FStar_Syntax_Util.un_uinst hd1)
in uu____8158.FStar_Syntax_Syntax.n)
in ((uu____8157), (args)))
in (match (uu____8144) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____8172)::((l, uu____8174))::((r, uu____8176))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid) -> begin
(

let uu____8223 = (do_unify g.FStar_Tactics_Types.context l r)
in (bind uu____8223 (fun b -> (match ((not (b))) with
| true -> begin
(

let uu____8232 = (tts g.FStar_Tactics_Types.context l)
in (

let uu____8233 = (tts g.FStar_Tactics_Types.context r)
in (fail2 "trefl: not a trivial equality (%s vs %s)" uu____8232 uu____8233)))
end
| uu____8234 -> begin
(solve g FStar_Syntax_Util.exp_unit)
end))))
end
| (hd2, uu____8236) -> begin
(

let uu____8253 = (tts g.FStar_Tactics_Types.context t)
in (fail1 "trefl: not an equality (%s)" uu____8253))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
(fail "not an irrelevant goal")
end))))))


let dup : unit  ->  unit tac = (fun uu____8262 -> (

let uu____8265 = (cur_goal ())
in (bind uu____8265 (fun g -> (

let uu____8271 = (new_uvar "dup" g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (bind uu____8271 (fun u -> (

let g' = (

let uu___125_8278 = g
in {FStar_Tactics_Types.context = uu___125_8278.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = u; FStar_Tactics_Types.goal_ty = uu___125_8278.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___125_8278.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___125_8278.FStar_Tactics_Types.is_guard})
in (bind __dismiss (fun uu____8281 -> (

let uu____8282 = (

let uu____8285 = (

let uu____8286 = (FStar_TypeChecker_TcTerm.universe_of g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (FStar_Syntax_Util.mk_eq2 uu____8286 g.FStar_Tactics_Types.goal_ty u g.FStar_Tactics_Types.witness))
in (add_irrelevant_goal "dup equation" g.FStar_Tactics_Types.context uu____8285 g.FStar_Tactics_Types.opts))
in (bind uu____8282 (fun uu____8289 -> (

let uu____8290 = (add_goals ((g')::[]))
in (bind uu____8290 (fun uu____8294 -> (ret ())))))))))))))))))


let flip : unit  ->  unit tac = (fun uu____8301 -> (bind get (fun ps -> (match (ps.FStar_Tactics_Types.goals) with
| (g1)::(g2)::gs -> begin
(set (

let uu___126_8318 = ps
in {FStar_Tactics_Types.main_context = uu___126_8318.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___126_8318.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___126_8318.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (g2)::(g1)::gs; FStar_Tactics_Types.smt_goals = uu___126_8318.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___126_8318.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___126_8318.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___126_8318.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___126_8318.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___126_8318.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___126_8318.FStar_Tactics_Types.freshness}))
end
| uu____8319 -> begin
(fail "flip: less than 2 goals")
end))))


let later : unit  ->  unit tac = (fun uu____8328 -> (bind get (fun ps -> (match (ps.FStar_Tactics_Types.goals) with
| [] -> begin
(ret ())
end
| (g)::gs -> begin
(set (

let uu___127_8341 = ps
in {FStar_Tactics_Types.main_context = uu___127_8341.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___127_8341.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___127_8341.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append gs ((g)::[])); FStar_Tactics_Types.smt_goals = uu___127_8341.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___127_8341.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___127_8341.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___127_8341.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___127_8341.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___127_8341.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___127_8341.FStar_Tactics_Types.freshness}))
end))))


let qed : unit  ->  unit tac = (fun uu____8348 -> (bind get (fun ps -> (match (ps.FStar_Tactics_Types.goals) with
| [] -> begin
(ret ())
end
| uu____8355 -> begin
(fail "Not done!")
end))))


let cases : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac = (fun t -> (

let uu____8375 = (

let uu____8382 = (cur_goal ())
in (bind uu____8382 (fun g -> (

let uu____8392 = (__tc g.FStar_Tactics_Types.context t)
in (bind uu____8392 (fun uu____8428 -> (match (uu____8428) with
| (t1, typ, guard) -> begin
(

let uu____8444 = (FStar_Syntax_Util.head_and_args typ)
in (match (uu____8444) with
| (hd1, args) -> begin
(

let uu____8487 = (

let uu____8500 = (

let uu____8501 = (FStar_Syntax_Util.un_uinst hd1)
in uu____8501.FStar_Syntax_Syntax.n)
in ((uu____8500), (args)))
in (match (uu____8487) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____8520))::((q, uu____8522))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid) -> begin
(

let v_p = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p)
in (

let v_q = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None q)
in (

let g1 = (

let uu___128_8560 = g
in (

let uu____8561 = (FStar_TypeChecker_Env.push_bv g.FStar_Tactics_Types.context v_p)
in {FStar_Tactics_Types.context = uu____8561; FStar_Tactics_Types.witness = uu___128_8560.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___128_8560.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___128_8560.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___128_8560.FStar_Tactics_Types.is_guard}))
in (

let g2 = (

let uu___129_8563 = g
in (

let uu____8564 = (FStar_TypeChecker_Env.push_bv g.FStar_Tactics_Types.context v_q)
in {FStar_Tactics_Types.context = uu____8564; FStar_Tactics_Types.witness = uu___129_8563.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___129_8563.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___129_8563.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___129_8563.FStar_Tactics_Types.is_guard}))
in (bind __dismiss (fun uu____8571 -> (

let uu____8572 = (add_goals ((g1)::(g2)::[]))
in (bind uu____8572 (fun uu____8581 -> (

let uu____8582 = (

let uu____8587 = (FStar_Syntax_Syntax.bv_to_name v_p)
in (

let uu____8588 = (FStar_Syntax_Syntax.bv_to_name v_q)
in ((uu____8587), (uu____8588))))
in (ret uu____8582)))))))))))
end
| uu____8593 -> begin
(

let uu____8606 = (tts g.FStar_Tactics_Types.context typ)
in (fail1 "Not a disjunction: %s" uu____8606))
end))
end))
end)))))))
in (FStar_All.pipe_left (wrap_err "cases") uu____8375)))


let set_options : Prims.string  ->  unit tac = (fun s -> (

let uu____8636 = (cur_goal ())
in (bind uu____8636 (fun g -> ((FStar_Options.push ());
(

let uu____8649 = (FStar_Util.smap_copy g.FStar_Tactics_Types.opts)
in (FStar_Options.set uu____8649));
(

let res = (FStar_Options.set_options FStar_Options.Set s)
in (

let opts' = (FStar_Options.peek ())
in ((FStar_Options.pop ());
(match (res) with
| FStar_Getopt.Success -> begin
(

let g' = (

let uu___130_8656 = g
in {FStar_Tactics_Types.context = uu___130_8656.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___130_8656.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___130_8656.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = opts'; FStar_Tactics_Types.is_guard = uu___130_8656.FStar_Tactics_Types.is_guard})
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


let top_env : unit  ->  env tac = (fun uu____8664 -> (bind get (fun ps -> (FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context))))


let cur_env : unit  ->  env tac = (fun uu____8677 -> (

let uu____8680 = (cur_goal ())
in (bind uu____8680 (fun g -> (FStar_All.pipe_left ret g.FStar_Tactics_Types.context)))))


let cur_goal' : unit  ->  FStar_Syntax_Syntax.term tac = (fun uu____8693 -> (

let uu____8696 = (cur_goal ())
in (bind uu____8696 (fun g -> (FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)))))


let cur_witness : unit  ->  FStar_Syntax_Syntax.term tac = (fun uu____8709 -> (

let uu____8712 = (cur_goal ())
in (bind uu____8712 (fun g -> (FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)))))


let unquote : FStar_Reflection_Data.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun ty tm -> (

let uu____8733 = (

let uu____8736 = (cur_goal ())
in (bind uu____8736 (fun goal -> (

let env = (FStar_TypeChecker_Env.set_expected_typ goal.FStar_Tactics_Types.context ty)
in (

let uu____8744 = (__tc env tm)
in (bind uu____8744 (fun uu____8764 -> (match (uu____8764) with
| (tm1, typ, guard) -> begin
(

let uu____8776 = (proc_guard "unquote" env guard goal.FStar_Tactics_Types.opts)
in (bind uu____8776 (fun uu____8780 -> (ret tm1))))
end))))))))
in (FStar_All.pipe_left (wrap_err "unquote") uu____8733)))


let uvar_env : env  ->  FStar_Reflection_Data.typ FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term tac = (fun env ty -> (

let uu____8803 = (match (ty) with
| FStar_Pervasives_Native.Some (ty1) -> begin
(ret ty1)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8809 = (

let uu____8810 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8810))
in (new_uvar "uvar_env.2" env uu____8809))
end)
in (bind uu____8803 (fun typ -> (

let uu____8822 = (new_uvar "uvar_env" env typ)
in (bind uu____8822 (fun t -> (ret t))))))))


let unshelve : FStar_Syntax_Syntax.term  ->  unit tac = (fun t -> (

let uu____8836 = (bind get (fun ps -> (

let env = ps.FStar_Tactics_Types.main_context
in (

let opts = (match (ps.FStar_Tactics_Types.goals) with
| (g)::uu____8853 -> begin
g.FStar_Tactics_Types.opts
end
| uu____8856 -> begin
(FStar_Options.peek ())
end)
in (

let uu____8859 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____8859) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uu____8876, typ); FStar_Syntax_Syntax.pos = uu____8878; FStar_Syntax_Syntax.vars = uu____8879}, uu____8880) -> begin
(

let uu____8925 = (

let uu____8928 = (

let uu____8929 = (bnorm env t)
in (

let uu____8930 = (bnorm env typ)
in {FStar_Tactics_Types.context = env; FStar_Tactics_Types.witness = uu____8929; FStar_Tactics_Types.goal_ty = uu____8930; FStar_Tactics_Types.opts = opts; FStar_Tactics_Types.is_guard = false}))
in (uu____8928)::[])
in (add_goals uu____8925))
end
| uu____8931 -> begin
(fail "not a uvar")
end))))))
in (FStar_All.pipe_left (wrap_err "unshelve") uu____8836)))


let unify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun t1 t2 -> (bind get (fun ps -> (do_unify ps.FStar_Tactics_Types.main_context t1 t2))))


let launch_process : Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string tac = (fun prog args input -> (bind idtac (fun uu____8988 -> (

let uu____8989 = (FStar_Options.unsafe_tactic_exec ())
in (match (uu____8989) with
| true -> begin
(

let s = (FStar_Util.launch_process true "tactic_launch" prog args input (fun uu____8995 uu____8996 -> false))
in (ret s))
end
| uu____8997 -> begin
(fail "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
end)))))


let fresh_bv_named : Prims.string  ->  FStar_Reflection_Data.typ  ->  FStar_Syntax_Syntax.bv tac = (fun nm t -> (bind idtac (fun uu____9014 -> (

let uu____9015 = (FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t)
in (ret uu____9015)))))


let change : FStar_Reflection_Data.typ  ->  unit tac = (fun ty -> (

let uu____9025 = (mlog (fun uu____9030 -> (

let uu____9031 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.print1 "change: ty = %s\n" uu____9031))) (fun uu____9034 -> (

let uu____9035 = (cur_goal ())
in (bind uu____9035 (fun g -> (

let uu____9041 = (__tc g.FStar_Tactics_Types.context ty)
in (bind uu____9041 (fun uu____9061 -> (match (uu____9061) with
| (ty1, uu____9071, guard) -> begin
(

let uu____9073 = (proc_guard "change" g.FStar_Tactics_Types.context guard g.FStar_Tactics_Types.opts)
in (bind uu____9073 (fun uu____9078 -> (

let uu____9079 = (do_unify g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty ty1)
in (bind uu____9079 (fun bb -> (match (bb) with
| true -> begin
(replace_cur (

let uu___131_9088 = g
in {FStar_Tactics_Types.context = uu___131_9088.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___131_9088.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = ty1; FStar_Tactics_Types.opts = uu___131_9088.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___131_9088.FStar_Tactics_Types.is_guard}))
end
| uu____9089 -> begin
(

let steps = (FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.UnfoldTac)::(FStar_TypeChecker_Normalize.Unmeta)::[]
in (

let ng = (normalize steps g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (

let nty = (normalize steps g.FStar_Tactics_Types.context ty1)
in (

let uu____9095 = (do_unify g.FStar_Tactics_Types.context ng nty)
in (bind uu____9095 (fun b -> (match (b) with
| true -> begin
(replace_cur (

let uu___132_9104 = g
in {FStar_Tactics_Types.context = uu___132_9104.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___132_9104.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = ty1; FStar_Tactics_Types.opts = uu___132_9104.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___132_9104.FStar_Tactics_Types.is_guard}))
end
| uu____9105 -> begin
(fail "not convertible")
end)))))))
end)))))))
end)))))))))
in (FStar_All.pipe_left (wrap_err "change") uu____9025)))


let rec last : 'a . 'a Prims.list  ->  'a = (fun l -> (match (l) with
| [] -> begin
(failwith "last: empty list")
end
| (x)::[] -> begin
x
end
| (uu____9126)::xs -> begin
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

let uu____9154 = (init xs)
in (x)::uu____9154)
end))


let rec inspect : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.term_view tac = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let t2 = (FStar_Syntax_Util.un_uinst t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t3, uu____9171) -> begin
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

let uu____9228 = (last args)
in (match (uu____9228) with
| (a, q) -> begin
(

let q' = (FStar_Reflection_Basic.inspect_aqual q)
in (

let uu____9250 = (

let uu____9251 = (

let uu____9256 = (

let uu____9259 = (

let uu____9264 = (init args)
in (FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9264))
in (uu____9259 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in ((uu____9256), (((a), (q')))))
in FStar_Reflection_Data.Tv_App (uu____9251))
in (FStar_All.pipe_left ret uu____9250)))
end))
end
| FStar_Syntax_Syntax.Tm_abs ([], uu____9285, uu____9286) -> begin
(failwith "inspect: empty arguments on Tm_abs")
end
| FStar_Syntax_Syntax.Tm_abs (bs, t3, k) -> begin
(

let uu____9330 = (FStar_Syntax_Subst.open_term bs t3)
in (match (uu____9330) with
| (bs1, t4) -> begin
(match (bs1) with
| [] -> begin
(failwith "impossible")
end
| (b)::bs2 -> begin
(

let uu____9363 = (

let uu____9364 = (

let uu____9369 = (FStar_Syntax_Util.abs bs2 t4 k)
in ((b), (uu____9369)))
in FStar_Reflection_Data.Tv_Abs (uu____9364))
in (FStar_All.pipe_left ret uu____9363))
end)
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____9376) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type (())))
end
| FStar_Syntax_Syntax.Tm_arrow ([], k) -> begin
(failwith "inspect: empty binders on arrow")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____9396) -> begin
(

let uu____9409 = (FStar_Syntax_Util.arrow_one t2)
in (match (uu____9409) with
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

let uu____9439 = (FStar_Syntax_Subst.open_term ((b)::[]) t3)
in (match (uu____9439) with
| (b', t4) -> begin
(

let b1 = (match (b') with
| (b'1)::[] -> begin
b'1
end
| uu____9470 -> begin
(failwith "impossible")
end)
in (FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Refine ((((FStar_Pervasives_Native.fst b1)), (t4))))))
end)))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____9478 = (

let uu____9479 = (FStar_Reflection_Basic.inspect_const c)
in FStar_Reflection_Data.Tv_Const (uu____9479))
in (FStar_All.pipe_left ret uu____9478))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t3) -> begin
(

let uu____9508 = (

let uu____9509 = (

let uu____9514 = (

let uu____9515 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_BigInt.of_int_fs uu____9515))
in ((uu____9514), (t3)))
in FStar_Reflection_Data.Tv_Uvar (uu____9509))
in (FStar_All.pipe_left ret uu____9508))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), t21) -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| uu____9540 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____9543) -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv) -> begin
(

let b = (FStar_Syntax_Syntax.mk_binder bv)
in (

let uu____9548 = (FStar_Syntax_Subst.open_term ((b)::[]) t21)
in (match (uu____9548) with
| (bs, t22) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____9579 -> begin
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
| uu____9608 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____9611) -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv) -> begin
(

let uu____9615 = (FStar_Syntax_Subst.open_let_rec ((lb)::[]) t21)
in (match (uu____9615) with
| (lbs, t22) -> begin
(match (lbs) with
| (lb1)::[] -> begin
(match (lb1.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____9635) -> begin
(ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv1) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Let (((true), (bv1), (lb1.FStar_Syntax_Syntax.lbdef), (t22)))))
end)
end
| uu____9641 -> begin
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

let uu____9695 = (FStar_Reflection_Basic.inspect_const c)
in FStar_Reflection_Data.Pat_Constant (uu____9695))
end
| FStar_Syntax_Syntax.Pat_cons (fv, ps) -> begin
(

let uu____9714 = (

let uu____9721 = (FStar_List.map (fun uu____9733 -> (match (uu____9733) with
| (p1, uu____9741) -> begin
(inspect_pat p1)
end)) ps)
in ((fv), (uu____9721)))
in FStar_Reflection_Data.Pat_Cons (uu____9714))
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

let brs2 = (FStar_List.map (fun uu___66_9795 -> (match (uu___66_9795) with
| (pat, uu____9817, t4) -> begin
(

let uu____9835 = (inspect_pat pat)
in ((uu____9835), (t4)))
end)) brs1)
in (FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (((t3), (brs2))))))))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| uu____9852 -> begin
((

let uu____9854 = (

let uu____9859 = (

let uu____9860 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____9861 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "inspect: outside of expected syntax (%s, %s)\n" uu____9860 uu____9861)))
in ((FStar_Errors.Warning_CantInspect), (uu____9859)))
in (FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9854));
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown);
)
end))))


let pack : FStar_Reflection_Data.term_view  ->  FStar_Syntax_Syntax.term tac = (fun tv -> (match (tv) with
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____9874 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_left ret uu____9874))
end
| FStar_Reflection_Data.Tv_BVar (bv) -> begin
(

let uu____9878 = (FStar_Syntax_Syntax.bv_to_tm bv)
in (FStar_All.pipe_left ret uu____9878))
end
| FStar_Reflection_Data.Tv_FVar (fv) -> begin
(

let uu____9882 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (FStar_All.pipe_left ret uu____9882))
end
| FStar_Reflection_Data.Tv_App (l, (r, q)) -> begin
(

let q' = (FStar_Reflection_Basic.pack_aqual q)
in (

let uu____9893 = (FStar_Syntax_Util.mk_app l ((((r), (q')))::[]))
in (FStar_All.pipe_left ret uu____9893)))
end
| FStar_Reflection_Data.Tv_Abs (b, t) -> begin
(

let uu____9914 = (FStar_Syntax_Util.abs ((b)::[]) t FStar_Pervasives_Native.None)
in (FStar_All.pipe_left ret uu____9914))
end
| FStar_Reflection_Data.Tv_Arrow (b, c) -> begin
(

let uu____9919 = (FStar_Syntax_Util.arrow ((b)::[]) c)
in (FStar_All.pipe_left ret uu____9919))
end
| FStar_Reflection_Data.Tv_Type (()) -> begin
(FStar_All.pipe_left ret FStar_Syntax_Util.ktype)
end
| FStar_Reflection_Data.Tv_Refine (bv, t) -> begin
(

let uu____9940 = (FStar_Syntax_Util.refine bv t)
in (FStar_All.pipe_left ret uu____9940))
end
| FStar_Reflection_Data.Tv_Const (c) -> begin
(

let uu____9952 = (

let uu____9955 = (

let uu____9962 = (

let uu____9963 = (FStar_Reflection_Basic.pack_const c)
in FStar_Syntax_Syntax.Tm_constant (uu____9963))
in (FStar_Syntax_Syntax.mk uu____9962))
in (uu____9955 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_All.pipe_left ret uu____9952))
end
| FStar_Reflection_Data.Tv_Uvar (u, t) -> begin
(

let uu____9977 = (

let uu____9980 = (FStar_BigInt.to_int_fs u)
in (FStar_Syntax_Util.uvar_from_id uu____9980 t))
in (FStar_All.pipe_left ret uu____9977))
end
| FStar_Reflection_Data.Tv_Let (false, bv, t1, t2) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 [] FStar_Range.dummyRange)
in (

let uu____9995 = (

let uu____9998 = (

let uu____10005 = (

let uu____10006 = (

let uu____10019 = (

let uu____10020 = (

let uu____10021 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____10021)::[])
in (FStar_Syntax_Subst.close uu____10020 t2))
in ((((false), ((lb)::[]))), (uu____10019)))
in FStar_Syntax_Syntax.Tm_let (uu____10006))
in (FStar_Syntax_Syntax.mk uu____10005))
in (uu____9998 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_All.pipe_left ret uu____9995)))
end
| FStar_Reflection_Data.Tv_Let (true, bv, t1, t2) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 [] FStar_Range.dummyRange)
in (

let uu____10047 = (FStar_Syntax_Subst.close_let_rec ((lb)::[]) t2)
in (match (uu____10047) with
| (lbs, body) -> begin
(

let uu____10062 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____10062))
end)))
end
| FStar_Reflection_Data.Tv_Match (t, brs) -> begin
(

let wrap = (fun v1 -> {FStar_Syntax_Syntax.v = v1; FStar_Syntax_Syntax.p = FStar_Range.dummyRange})
in (

let rec pack_pat = (fun p -> (match (p) with
| FStar_Reflection_Data.Pat_Constant (c) -> begin
(

let uu____10102 = (

let uu____10103 = (FStar_Reflection_Basic.pack_const c)
in FStar_Syntax_Syntax.Pat_constant (uu____10103))
in (FStar_All.pipe_left wrap uu____10102))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____10112 = (

let uu____10113 = (

let uu____10126 = (FStar_List.map (fun p1 -> (

let uu____10140 = (pack_pat p1)
in ((uu____10140), (false)))) ps)
in ((fv), (uu____10126)))
in FStar_Syntax_Syntax.Pat_cons (uu____10113))
in (FStar_All.pipe_left wrap uu____10112))
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

let brs1 = (FStar_List.map (fun uu___67_10190 -> (match (uu___67_10190) with
| (pat, t1) -> begin
(

let uu____10207 = (pack_pat pat)
in ((uu____10207), (FStar_Pervasives_Native.None), (t1)))
end)) brs)
in (

let brs2 = (FStar_List.map FStar_Syntax_Subst.close_branch brs1)
in (

let uu____10217 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((t), (brs2)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____10217))))))
end
| FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) -> begin
(

let uu____10237 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (((FStar_Util.Inl (t)), (tacopt))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____10237))
end
| FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) -> begin
(

let uu____10279 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (((FStar_Util.Inr (c)), (tacopt))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____10279))
end
| FStar_Reflection_Data.Tv_Unknown -> begin
(

let uu____10314 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____10314))
end))


let goal_of_goal_ty : env  ->  FStar_Reflection_Data.typ  ->  (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t) = (fun env typ -> (

let uu____10343 = (FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty" typ.FStar_Syntax_Syntax.pos env typ)
in (match (uu____10343) with
| (u, uu____10361, g_u) -> begin
(

let g = (

let uu____10376 = (FStar_Options.peek ())
in {FStar_Tactics_Types.context = env; FStar_Tactics_Types.witness = u; FStar_Tactics_Types.goal_ty = typ; FStar_Tactics_Types.opts = uu____10376; FStar_Tactics_Types.is_guard = false})
in ((g), (g_u)))
end)))


let proofstate_of_goal_ty : env  ->  FStar_Reflection_Data.typ  ->  (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term) = (fun env typ -> (

let uu____10391 = (goal_of_goal_ty env typ)
in (match (uu____10391) with
| (g, g_u) -> begin
(

let ps = {FStar_Tactics_Types.main_context = env; FStar_Tactics_Types.main_goal = g; FStar_Tactics_Types.all_implicits = g_u.FStar_TypeChecker_Env.implicits; FStar_Tactics_Types.goals = (g)::[]; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = (Prims.parse_int "0"); FStar_Tactics_Types.__dump = (fun ps msg -> (dump_proofstate ps msg)); FStar_Tactics_Types.psc = FStar_TypeChecker_Normalize.null_psc; FStar_Tactics_Types.entry_range = FStar_Range.dummyRange; FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT; FStar_Tactics_Types.freshness = (Prims.parse_int "0")}
in ((ps), (g.FStar_Tactics_Types.witness)))
end)))




