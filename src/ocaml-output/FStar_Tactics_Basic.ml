
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

let uu____709 = (FStar_ST.op_Bang tac_verb_dbg)
in (match (uu____709) with
| FStar_Pervasives_Native.None -> begin
((

let uu____740 = (

let uu____743 = (FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context (FStar_Options.Other ("TacVerbose")))
in FStar_Pervasives_Native.Some (uu____743))
in (FStar_ST.op_Colon_Equals tac_verb_dbg uu____740));
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

let uu____824 = (FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context (FStar_Options.Other ("TacFail")))
in (match (uu____824) with
| true -> begin
(dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg))
end
| uu____825 -> begin
()
end));
FStar_Tactics_Result.Failed (((msg), (ps)));
))))


let fail1 : 'Auu____832 . Prims.string  ->  Prims.string  ->  'Auu____832 tac = (fun msg x -> (

let uu____845 = (FStar_Util.format1 msg x)
in (fail uu____845)))


let fail2 : 'Auu____854 . Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____854 tac = (fun msg x y -> (

let uu____872 = (FStar_Util.format2 msg x y)
in (fail uu____872)))


let fail3 : 'Auu____883 . Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____883 tac = (fun msg x y z -> (

let uu____906 = (FStar_Util.format3 msg x y z)
in (fail uu____906)))


let fail4 : 'Auu____919 . Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____919 tac = (fun msg x y z w -> (

let uu____947 = (FStar_Util.format4 msg x y z w)
in (fail uu____947)))


let trytac' : 'a . 'a tac  ->  (Prims.string, 'a) FStar_Util.either tac = (fun t -> (mk_tac (fun ps -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____980 = (run t ps)
in (match (uu____980) with
| FStar_Tactics_Result.Success (a, q) -> begin
((FStar_Syntax_Unionfind.commit tx);
FStar_Tactics_Result.Success (((FStar_Util.Inr (a)), (q)));
)
end
| FStar_Tactics_Result.Failed (m, q) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(

let ps1 = (

let uu___67_1004 = ps
in {FStar_Tactics_Types.main_context = uu___67_1004.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___67_1004.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___67_1004.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___67_1004.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___67_1004.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___67_1004.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___67_1004.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___67_1004.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___67_1004.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___67_1004.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = q.FStar_Tactics_Types.freshness})
in FStar_Tactics_Result.Success (((FStar_Util.Inl (m)), (ps1))));
)
end))))))


let trytac : 'a . 'a tac  ->  'a FStar_Pervasives_Native.option tac = (fun t -> (

let uu____1031 = (trytac' t)
in (bind uu____1031 (fun r -> (match (r) with
| FStar_Util.Inr (v1) -> begin
(ret (FStar_Pervasives_Native.Some (v1)))
end
| FStar_Util.Inl (uu____1058) -> begin
(ret FStar_Pervasives_Native.None)
end)))))


let trytac_exn : 'a . 'a tac  ->  'a FStar_Pervasives_Native.option tac = (fun t -> (mk_tac (fun ps -> (FStar_All.try_with (fun uu___69_1089 -> (match (()) with
| () -> begin
(

let uu____1094 = (trytac t)
in (run uu____1094 ps))
end)) (fun uu___68_1105 -> (match (uu___68_1105) with
| FStar_Errors.Err (uu____1110, msg) -> begin
((log ps (fun uu____1114 -> (FStar_Util.print1 "trytac_exn error: (%s)" msg)));
FStar_Tactics_Result.Success (((FStar_Pervasives_Native.None), (ps)));
)
end
| FStar_Errors.Error (uu____1119, msg, uu____1121) -> begin
((log ps (fun uu____1124 -> (FStar_Util.print1 "trytac_exn error: (%s)" msg)));
FStar_Tactics_Result.Success (((FStar_Pervasives_Native.None), (ps)));
)
end))))))


let wrap_err : 'a . Prims.string  ->  'a tac  ->  'a tac = (fun pref t -> (mk_tac (fun ps -> (

let uu____1157 = (run t ps)
in (match (uu____1157) with
| FStar_Tactics_Result.Success (a, q) -> begin
FStar_Tactics_Result.Success (((a), (q)))
end
| FStar_Tactics_Result.Failed (msg, q) -> begin
FStar_Tactics_Result.Failed ((((Prims.strcat pref (Prims.strcat ": " msg))), (q)))
end)))))


let set : FStar_Tactics_Types.proofstate  ->  unit tac = (fun p -> (mk_tac (fun uu____1176 -> FStar_Tactics_Result.Success (((()), (p))))))


let __do_unify : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun env t1 t2 -> ((

let uu____1197 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1197) with
| true -> begin
(

let uu____1198 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1199 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1198 uu____1199)))
end
| uu____1200 -> begin
()
end));
(FStar_All.try_with (fun uu___71_1206 -> (match (()) with
| () -> begin
(

let res = (FStar_TypeChecker_Rel.teq_nosmt env t1 t2)
in ((

let uu____1211 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1211) with
| true -> begin
(

let uu____1212 = (FStar_Util.string_of_bool res)
in (

let uu____1213 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1214 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1212 uu____1213 uu____1214))))
end
| uu____1215 -> begin
()
end));
(ret res);
))
end)) (fun uu___70_1219 -> (match (uu___70_1219) with
| FStar_Errors.Err (uu____1222, msg) -> begin
(mlog (fun uu____1225 -> (FStar_Util.print1 ">> do_unify error, (%s)\n" msg)) (fun uu____1227 -> (ret false)))
end
| FStar_Errors.Error (uu____1228, msg, r) -> begin
(mlog (fun uu____1233 -> (

let uu____1234 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg uu____1234))) (fun uu____1236 -> (ret false)))
end)));
))


let do_unify : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun env t1 t2 -> (bind idtac (fun uu____1259 -> ((

let uu____1261 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1261) with
| true -> begin
((FStar_Options.push ());
(

let uu____1263 = (FStar_Options.set_options FStar_Options.Set "--debug_level Rel --debug_level RelCheck")
in ());
)
end
| uu____1264 -> begin
()
end));
(

let uu____1265 = (

let uu____1268 = (__do_unify env t1 t2)
in (bind uu____1268 (fun b -> (match ((not (b))) with
| true -> begin
(

let t11 = (FStar_TypeChecker_Normalize.normalize [] env t1)
in (

let t21 = (FStar_TypeChecker_Normalize.normalize [] env t2)
in (__do_unify env t11 t21)))
end
| uu____1279 -> begin
(ret b)
end))))
in (bind uu____1265 (fun r -> ((

let uu____1284 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1284) with
| true -> begin
(FStar_Options.pop ())
end
| uu____1285 -> begin
()
end));
(ret r);
))));
))))


let trysolve : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun goal solution -> (do_unify goal.FStar_Tactics_Types.context solution goal.FStar_Tactics_Types.witness))


let __dismiss : unit tac = (bind get (fun p -> (

let uu____1305 = (

let uu___72_1306 = p
in (

let uu____1307 = (FStar_List.tl p.FStar_Tactics_Types.goals)
in {FStar_Tactics_Types.main_context = uu___72_1306.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___72_1306.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___72_1306.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu____1307; FStar_Tactics_Types.smt_goals = uu___72_1306.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___72_1306.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___72_1306.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___72_1306.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___72_1306.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___72_1306.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___72_1306.FStar_Tactics_Types.freshness}))
in (set uu____1305))))


let dismiss : unit  ->  unit tac = (fun uu____1316 -> (bind get (fun p -> (match (p.FStar_Tactics_Types.goals) with
| [] -> begin
(fail "dismiss: no more goals")
end
| uu____1323 -> begin
__dismiss
end))))


let solve : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun goal solution -> (

let uu____1340 = (trysolve goal solution)
in (bind uu____1340 (fun b -> (match (b) with
| true -> begin
__dismiss
end
| uu____1347 -> begin
(

let uu____1348 = (

let uu____1349 = (tts goal.FStar_Tactics_Types.context solution)
in (

let uu____1350 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.witness)
in (

let uu____1351 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (FStar_Util.format3 "%s does not solve %s : %s" uu____1349 uu____1350 uu____1351))))
in (fail uu____1348))
end)))))


let dismiss_all : unit tac = (bind get (fun p -> (set (

let uu___73_1358 = p
in {FStar_Tactics_Types.main_context = uu___73_1358.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___73_1358.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___73_1358.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = []; FStar_Tactics_Types.smt_goals = uu___73_1358.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___73_1358.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___73_1358.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___73_1358.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___73_1358.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___73_1358.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___73_1358.FStar_Tactics_Types.freshness}))))


let nwarn : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let check_valid_goal : FStar_Tactics_Types.goal  ->  unit = (fun g -> (

let uu____1377 = (FStar_Options.defensive ())
in (match (uu____1377) with
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

let uu____1393 = (FStar_TypeChecker_Env.pop_bv e)
in (match (uu____1393) with
| FStar_Pervasives_Native.None -> begin
b3
end
| FStar_Pervasives_Native.Some (bv, e1) -> begin
(

let b4 = (b3 && (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort))
in (aux b4 e1))
end)))
in (

let uu____1411 = ((

let uu____1414 = (aux b2 env)
in (not (uu____1414))) && (

let uu____1416 = (FStar_ST.op_Bang nwarn)
in (uu____1416 < (Prims.parse_int "5"))))
in (match (uu____1411) with
| true -> begin
((

let uu____1441 = (

let uu____1446 = (

let uu____1447 = (goal_to_string g)
in (FStar_Util.format1 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n" uu____1447))
in ((FStar_Errors.Warning_IllFormedGoal), (uu____1446)))
in (FStar_Errors.log_issue g.FStar_Tactics_Types.goal_ty.FStar_Syntax_Syntax.pos uu____1441));
(

let uu____1448 = (

let uu____1449 = (FStar_ST.op_Bang nwarn)
in (uu____1449 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals nwarn uu____1448));
)
end
| uu____1496 -> begin
()
end)))))))
end
| uu____1497 -> begin
()
end)))


let add_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___74_1517 = p
in {FStar_Tactics_Types.main_context = uu___74_1517.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___74_1517.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___74_1517.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append gs p.FStar_Tactics_Types.goals); FStar_Tactics_Types.smt_goals = uu___74_1517.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___74_1517.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___74_1517.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___74_1517.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___74_1517.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___74_1517.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___74_1517.FStar_Tactics_Types.freshness}));
))))


let add_smt_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___75_1537 = p
in {FStar_Tactics_Types.main_context = uu___75_1537.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___75_1537.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___75_1537.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___75_1537.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = (FStar_List.append gs p.FStar_Tactics_Types.smt_goals); FStar_Tactics_Types.depth = uu___75_1537.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___75_1537.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___75_1537.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___75_1537.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___75_1537.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___75_1537.FStar_Tactics_Types.freshness}));
))))


let push_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___76_1557 = p
in {FStar_Tactics_Types.main_context = uu___76_1557.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___76_1557.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___76_1557.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append p.FStar_Tactics_Types.goals gs); FStar_Tactics_Types.smt_goals = uu___76_1557.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___76_1557.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___76_1557.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___76_1557.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___76_1557.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___76_1557.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___76_1557.FStar_Tactics_Types.freshness}));
))))


let push_smt_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___77_1577 = p
in {FStar_Tactics_Types.main_context = uu___77_1577.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___77_1577.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___77_1577.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___77_1577.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = (FStar_List.append p.FStar_Tactics_Types.smt_goals gs); FStar_Tactics_Types.depth = uu___77_1577.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___77_1577.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___77_1577.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___77_1577.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___77_1577.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___77_1577.FStar_Tactics_Types.freshness}));
))))


let replace_cur : FStar_Tactics_Types.goal  ->  unit tac = (fun g -> (bind __dismiss (fun uu____1588 -> (add_goals ((g)::[])))))


let add_implicits : implicits  ->  unit tac = (fun i -> (bind get (fun p -> (set (

let uu___78_1602 = p
in {FStar_Tactics_Types.main_context = uu___78_1602.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___78_1602.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = (FStar_List.append i p.FStar_Tactics_Types.all_implicits); FStar_Tactics_Types.goals = uu___78_1602.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___78_1602.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___78_1602.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___78_1602.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___78_1602.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___78_1602.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___78_1602.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___78_1602.FStar_Tactics_Types.freshness})))))


let new_uvar : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  FStar_Syntax_Syntax.term tac = (fun reason env typ -> (

let uu____1632 = (FStar_TypeChecker_Util.new_implicit_var reason typ.FStar_Syntax_Syntax.pos env typ)
in (match (uu____1632) with
| (u, uu____1648, g_u) -> begin
(

let uu____1662 = (add_implicits g_u.FStar_TypeChecker_Env.implicits)
in (bind uu____1662 (fun uu____1666 -> (ret u))))
end)))


let is_true : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1672 = (FStar_Syntax_Util.un_squash t)
in (match (uu____1672) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____1682 = (

let uu____1683 = (FStar_Syntax_Subst.compress t')
in uu____1683.FStar_Syntax_Syntax.n)
in (match (uu____1682) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)
end
| uu____1687 -> begin
false
end))
end
| uu____1688 -> begin
false
end)))


let is_false : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1698 = (FStar_Syntax_Util.un_squash t)
in (match (uu____1698) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____1708 = (

let uu____1709 = (FStar_Syntax_Subst.compress t')
in uu____1709.FStar_Syntax_Syntax.n)
in (match (uu____1708) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid)
end
| uu____1713 -> begin
false
end))
end
| uu____1714 -> begin
false
end)))


let cur_goal : unit  ->  FStar_Tactics_Types.goal tac = (fun uu____1725 -> (bind get (fun p -> (match (p.FStar_Tactics_Types.goals) with
| [] -> begin
(fail "No more goals (1)")
end
| (hd1)::tl1 -> begin
(ret hd1)
end))))


let tadmit : unit  ->  unit tac = (fun uu____1742 -> (

let uu____1745 = (

let uu____1748 = (cur_goal ())
in (bind uu____1748 (fun g -> ((

let uu____1755 = (

let uu____1760 = (

let uu____1761 = (goal_to_string g)
in (FStar_Util.format1 "Tactics admitted goal <%s>\n\n" uu____1761))
in ((FStar_Errors.Warning_TacAdmit), (uu____1760)))
in (FStar_Errors.log_issue g.FStar_Tactics_Types.goal_ty.FStar_Syntax_Syntax.pos uu____1755));
(solve g FStar_Syntax_Util.exp_unit);
))))
in (FStar_All.pipe_left (wrap_err "tadmit") uu____1745)))


let fresh : unit  ->  FStar_BigInt.t tac = (fun uu____1772 -> (bind get (fun ps -> (

let n1 = ps.FStar_Tactics_Types.freshness
in (

let ps1 = (

let uu___79_1782 = ps
in {FStar_Tactics_Types.main_context = uu___79_1782.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___79_1782.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___79_1782.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___79_1782.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___79_1782.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___79_1782.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___79_1782.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___79_1782.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___79_1782.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___79_1782.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))})
in (

let uu____1783 = (set ps1)
in (bind uu____1783 (fun uu____1788 -> (

let uu____1789 = (FStar_BigInt.of_int_fs n1)
in (ret uu____1789))))))))))


let ngoals : unit  ->  FStar_BigInt.t tac = (fun uu____1796 -> (bind get (fun ps -> (

let n1 = (FStar_List.length ps.FStar_Tactics_Types.goals)
in (

let uu____1804 = (FStar_BigInt.of_int_fs n1)
in (ret uu____1804))))))


let ngoals_smt : unit  ->  FStar_BigInt.t tac = (fun uu____1817 -> (bind get (fun ps -> (

let n1 = (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
in (

let uu____1825 = (FStar_BigInt.of_int_fs n1)
in (ret uu____1825))))))


let is_guard : unit  ->  Prims.bool tac = (fun uu____1838 -> (

let uu____1841 = (cur_goal ())
in (bind uu____1841 (fun g -> (ret g.FStar_Tactics_Types.is_guard)))))


let mk_irrelevant_goal : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  FStar_Options.optionstate  ->  FStar_Tactics_Types.goal tac = (fun reason env phi opts -> (

let typ = (

let uu____1873 = (env.FStar_TypeChecker_Env.universe_of env phi)
in (FStar_Syntax_Util.mk_squash uu____1873 phi))
in (

let uu____1874 = (new_uvar reason env typ)
in (bind uu____1874 (fun u -> (

let goal = {FStar_Tactics_Types.context = env; FStar_Tactics_Types.witness = u; FStar_Tactics_Types.goal_ty = typ; FStar_Tactics_Types.opts = opts; FStar_Tactics_Types.is_guard = false}
in (ret goal)))))))


let __tc : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ * FStar_TypeChecker_Env.guard_t) tac = (fun e t -> (bind get (fun ps -> (mlog (fun uu____1923 -> (

let uu____1924 = (tts e t)
in (FStar_Util.print1 "Tac> __tc(%s)\n" uu____1924))) (fun uu____1926 -> (FStar_All.try_with (fun uu___81_1937 -> (match (()) with
| () -> begin
(

let uu____1946 = (ps.FStar_Tactics_Types.main_context.FStar_TypeChecker_Env.type_of e t)
in (ret uu____1946))
end)) (fun uu___80_1964 -> (match (uu___80_1964) with
| FStar_Errors.Err (uu____1973, msg) -> begin
(

let uu____1975 = (tts e t)
in (

let uu____1976 = (

let uu____1977 = (FStar_TypeChecker_Env.all_binders e)
in (FStar_All.pipe_right uu____1977 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____1975 uu____1976 msg)))
end
| FStar_Errors.Error (uu____1984, msg, uu____1986) -> begin
(

let uu____1987 = (tts e t)
in (

let uu____1988 = (

let uu____1989 = (FStar_TypeChecker_Env.all_binders e)
in (FStar_All.pipe_right uu____1989 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____1987 uu____1988 msg)))
end))))))))


let istrivial : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e t -> (

let steps = (FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.UnfoldTac)::(FStar_TypeChecker_Normalize.Unmeta)::[]
in (

let t1 = (normalize steps e t)
in (is_true t1))))


let get_guard_policy : unit  ->  FStar_Tactics_Types.guard_policy tac = (fun uu____2016 -> (bind get (fun ps -> (ret ps.FStar_Tactics_Types.guard_policy))))


let set_guard_policy : FStar_Tactics_Types.guard_policy  ->  unit tac = (fun pol -> (bind get (fun ps -> (set (

let uu___82_2034 = ps
in {FStar_Tactics_Types.main_context = uu___82_2034.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___82_2034.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___82_2034.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___82_2034.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___82_2034.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___82_2034.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___82_2034.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___82_2034.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___82_2034.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = pol; FStar_Tactics_Types.freshness = uu___82_2034.FStar_Tactics_Types.freshness})))))


let with_policy : 'a . FStar_Tactics_Types.guard_policy  ->  'a tac  ->  'a tac = (fun pol t -> (

let uu____2058 = (get_guard_policy ())
in (bind uu____2058 (fun old_pol -> (

let uu____2064 = (set_guard_policy pol)
in (bind uu____2064 (fun uu____2068 -> (bind t (fun r -> (

let uu____2072 = (set_guard_policy old_pol)
in (bind uu____2072 (fun uu____2076 -> (ret r)))))))))))))


let proc_guard : Prims.string  ->  env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Options.optionstate  ->  unit tac = (fun reason e g opts -> (

let uu____2101 = (

let uu____2102 = (FStar_TypeChecker_Rel.simplify_guard e g)
in uu____2102.FStar_TypeChecker_Env.guard_f)
in (match (uu____2101) with
| FStar_TypeChecker_Common.Trivial -> begin
(ret ())
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____2106 = (istrivial e f)
in (match (uu____2106) with
| true -> begin
(ret ())
end
| uu____2109 -> begin
(bind get (fun ps -> (match (ps.FStar_Tactics_Types.guard_policy) with
| FStar_Tactics_Types.Drop -> begin
(ret ())
end
| FStar_Tactics_Types.Goal -> begin
(

let uu____2114 = (mk_irrelevant_goal reason e f opts)
in (bind uu____2114 (fun goal -> (

let goal1 = (

let uu___83_2121 = goal
in {FStar_Tactics_Types.context = uu___83_2121.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___83_2121.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___83_2121.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___83_2121.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = true})
in (push_goals ((goal1)::[]))))))
end
| FStar_Tactics_Types.SMT -> begin
(

let uu____2122 = (mk_irrelevant_goal reason e f opts)
in (bind uu____2122 (fun goal -> (

let goal1 = (

let uu___84_2129 = goal
in {FStar_Tactics_Types.context = uu___84_2129.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___84_2129.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___84_2129.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___84_2129.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = true})
in (push_smt_goals ((goal1)::[]))))))
end
| FStar_Tactics_Types.Force -> begin
(FStar_All.try_with (fun uu___86_2134 -> (match (()) with
| () -> begin
(

let uu____2137 = (

let uu____2138 = (

let uu____2139 = (FStar_TypeChecker_Rel.discharge_guard_no_smt e g)
in (FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____2139))
in (not (uu____2138)))
in (match (uu____2137) with
| true -> begin
(mlog (fun uu____2144 -> (

let uu____2145 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print1 "guard = %s\n" uu____2145))) (fun uu____2147 -> (fail1 "Forcing the guard failed %s)" reason)))
end
| uu____2148 -> begin
(ret ())
end))
end)) (fun uu___85_2151 -> (match (uu___85_2151) with
| uu____2154 -> begin
(mlog (fun uu____2157 -> (

let uu____2158 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print1 "guard = %s\n" uu____2158))) (fun uu____2160 -> (fail1 "Forcing the guard failed (%s)" reason)))
end)))
end)))
end))
end)))


let tc : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.typ tac = (fun t -> (

let uu____2170 = (

let uu____2173 = (cur_goal ())
in (bind uu____2173 (fun goal -> (

let uu____2179 = (__tc goal.FStar_Tactics_Types.context t)
in (bind uu____2179 (fun uu____2199 -> (match (uu____2199) with
| (t1, typ, guard) -> begin
(

let uu____2211 = (proc_guard "tc" goal.FStar_Tactics_Types.context guard goal.FStar_Tactics_Types.opts)
in (bind uu____2211 (fun uu____2215 -> (ret typ))))
end)))))))
in (FStar_All.pipe_left (wrap_err "tc") uu____2170)))


let add_irrelevant_goal : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  FStar_Options.optionstate  ->  unit tac = (fun reason env phi opts -> (

let uu____2244 = (mk_irrelevant_goal reason env phi opts)
in (bind uu____2244 (fun goal -> (add_goals ((goal)::[]))))))


let trivial : unit  ->  unit tac = (fun uu____2255 -> (

let uu____2258 = (cur_goal ())
in (bind uu____2258 (fun goal -> (

let uu____2264 = (istrivial goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (match (uu____2264) with
| true -> begin
(solve goal FStar_Syntax_Util.exp_unit)
end
| uu____2267 -> begin
(

let uu____2268 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail1 "Not a trivial goal: %s" uu____2268))
end))))))


let goal_from_guard : Prims.string  ->  env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Options.optionstate  ->  FStar_Tactics_Types.goal FStar_Pervasives_Native.option tac = (fun reason e g opts -> (

let uu____2297 = (

let uu____2298 = (FStar_TypeChecker_Rel.simplify_guard e g)
in uu____2298.FStar_TypeChecker_Env.guard_f)
in (match (uu____2297) with
| FStar_TypeChecker_Common.Trivial -> begin
(ret FStar_Pervasives_Native.None)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____2306 = (istrivial e f)
in (match (uu____2306) with
| true -> begin
(ret FStar_Pervasives_Native.None)
end
| uu____2313 -> begin
(

let uu____2314 = (mk_irrelevant_goal reason e f opts)
in (bind uu____2314 (fun goal -> (ret (FStar_Pervasives_Native.Some ((

let uu___87_2324 = goal
in {FStar_Tactics_Types.context = uu___87_2324.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___87_2324.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___87_2324.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___87_2324.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = true})))))))
end))
end)))


let smt : unit  ->  unit tac = (fun uu____2331 -> (

let uu____2334 = (cur_goal ())
in (bind uu____2334 (fun g -> (

let uu____2340 = (is_irrelevant g)
in (match (uu____2340) with
| true -> begin
(bind __dismiss (fun uu____2344 -> (add_smt_goals ((g)::[]))))
end
| uu____2345 -> begin
(

let uu____2346 = (tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (fail1 "goal is not irrelevant: cannot dispatch to smt (%s)" uu____2346))
end))))))


let divide : 'a 'b . FStar_BigInt.t  ->  'a tac  ->  'b tac  ->  ('a * 'b) tac = (fun n1 l r -> (bind get (fun p -> (

let uu____2395 = (FStar_All.try_with (fun uu___92_2418 -> (match (()) with
| () -> begin
(

let uu____2429 = (

let uu____2438 = (FStar_BigInt.to_int_fs n1)
in (FStar_List.splitAt uu____2438 p.FStar_Tactics_Types.goals))
in (ret uu____2429))
end)) (fun uu___91_2449 -> (match (uu___91_2449) with
| uu____2460 -> begin
(fail "divide: not enough goals")
end)))
in (bind uu____2395 (fun uu____2487 -> (match (uu____2487) with
| (lgs, rgs) -> begin
(

let lp = (

let uu___88_2513 = p
in {FStar_Tactics_Types.main_context = uu___88_2513.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___88_2513.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___88_2513.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = lgs; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = uu___88_2513.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___88_2513.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___88_2513.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___88_2513.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___88_2513.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___88_2513.FStar_Tactics_Types.freshness})
in (

let rp = (

let uu___89_2515 = p
in {FStar_Tactics_Types.main_context = uu___89_2515.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___89_2515.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___89_2515.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = rgs; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = uu___89_2515.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___89_2515.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___89_2515.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___89_2515.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___89_2515.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___89_2515.FStar_Tactics_Types.freshness})
in (

let uu____2516 = (set lp)
in (bind uu____2516 (fun uu____2524 -> (bind l (fun a -> (bind get (fun lp' -> (

let uu____2538 = (set rp)
in (bind uu____2538 (fun uu____2546 -> (bind r (fun b -> (bind get (fun rp' -> (

let p' = (

let uu___90_2562 = p
in {FStar_Tactics_Types.main_context = uu___90_2562.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___90_2562.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___90_2562.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append lp'.FStar_Tactics_Types.goals rp'.FStar_Tactics_Types.goals); FStar_Tactics_Types.smt_goals = (FStar_List.append lp'.FStar_Tactics_Types.smt_goals (FStar_List.append rp'.FStar_Tactics_Types.smt_goals p.FStar_Tactics_Types.smt_goals)); FStar_Tactics_Types.depth = uu___90_2562.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___90_2562.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___90_2562.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___90_2562.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___90_2562.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___90_2562.FStar_Tactics_Types.freshness})
in (

let uu____2563 = (set p')
in (bind uu____2563 (fun uu____2571 -> (ret ((a), (b)))))))))))))))))))))))
end)))))))


let focus : 'a . 'a tac  ->  'a tac = (fun f -> (

let uu____2592 = (divide FStar_BigInt.one f idtac)
in (bind uu____2592 (fun uu____2605 -> (match (uu____2605) with
| (a, ()) -> begin
(ret a)
end)))))


let rec map : 'a . 'a tac  ->  'a Prims.list tac = (fun tau -> (bind get (fun p -> (match (p.FStar_Tactics_Types.goals) with
| [] -> begin
(ret [])
end
| (uu____2642)::uu____2643 -> begin
(

let uu____2646 = (

let uu____2655 = (map tau)
in (divide FStar_BigInt.one tau uu____2655))
in (bind uu____2646 (fun uu____2673 -> (match (uu____2673) with
| (h, t) -> begin
(ret ((h)::t))
end))))
end))))


let seq : unit tac  ->  unit tac  ->  unit tac = (fun t1 t2 -> (

let uu____2714 = (bind t1 (fun uu____2719 -> (

let uu____2720 = (map t2)
in (bind uu____2720 (fun uu____2728 -> (ret ()))))))
in (focus uu____2714)))


let intro : unit  ->  FStar_Syntax_Syntax.binder tac = (fun uu____2737 -> (

let uu____2740 = (

let uu____2743 = (cur_goal ())
in (bind uu____2743 (fun goal -> (

let uu____2752 = (FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty)
in (match (uu____2752) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____2767 = (

let uu____2768 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____2768)))
in (match (uu____2767) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____2771 -> begin
(

let env' = (FStar_TypeChecker_Env.push_binders goal.FStar_Tactics_Types.context ((b)::[]))
in (

let typ' = (comp_to_typ c)
in (

let uu____2782 = (new_uvar "intro" env' typ')
in (bind uu____2782 (fun u -> (

let uu____2788 = (

let uu____2791 = (FStar_Syntax_Util.abs ((b)::[]) u FStar_Pervasives_Native.None)
in (trysolve goal uu____2791))
in (bind uu____2788 (fun bb -> (match (bb) with
| true -> begin
(

let uu____2805 = (

let uu____2808 = (

let uu___93_2809 = goal
in (

let uu____2810 = (bnorm env' u)
in (

let uu____2811 = (bnorm env' typ')
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = uu____2810; FStar_Tactics_Types.goal_ty = uu____2811; FStar_Tactics_Types.opts = uu___93_2809.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___93_2809.FStar_Tactics_Types.is_guard})))
in (replace_cur uu____2808))
in (bind uu____2805 (fun uu____2813 -> (ret b))))
end
| uu____2814 -> begin
(fail "unification failed")
end)))))))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2819 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail1 "goal is not an arrow (%s)" uu____2819))
end)))))
in (FStar_All.pipe_left (wrap_err "intro") uu____2740)))


let intro_rec : unit  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac = (fun uu____2834 -> (

let uu____2841 = (cur_goal ())
in (bind uu____2841 (fun goal -> ((FStar_Util.print_string "WARNING (intro_rec): calling this is known to cause normalizer loops\n");
(FStar_Util.print_string "WARNING (intro_rec): proceed at your own risk...\n");
(

let uu____2858 = (FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty)
in (match (uu____2858) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____2877 = (

let uu____2878 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____2878)))
in (match (uu____2877) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____2889 -> begin
(

let bv = (FStar_Syntax_Syntax.gen_bv "__recf" FStar_Pervasives_Native.None goal.FStar_Tactics_Types.goal_ty)
in (

let bs = (

let uu____2898 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____2898)::(b)::[])
in (

let env' = (FStar_TypeChecker_Env.push_binders goal.FStar_Tactics_Types.context bs)
in (

let uu____2916 = (

let uu____2919 = (comp_to_typ c)
in (new_uvar "intro_rec" env' uu____2919))
in (bind uu____2916 (fun u -> (

let lb = (

let uu____2934 = (FStar_Syntax_Util.abs ((b)::[]) u FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] goal.FStar_Tactics_Types.goal_ty FStar_Parser_Const.effect_Tot_lid uu____2934 [] FStar_Range.dummyRange))
in (

let body = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____2948 = (FStar_Syntax_Subst.close_let_rec ((lb)::[]) body)
in (match (uu____2948) with
| (lbs, body1) -> begin
(

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body1)))) FStar_Pervasives_Native.None goal.FStar_Tactics_Types.witness.FStar_Syntax_Syntax.pos)
in (

let uu____2980 = (trysolve goal tm)
in (bind uu____2980 (fun bb -> (match (bb) with
| true -> begin
(

let uu____2996 = (

let uu____2999 = (

let uu___94_3000 = goal
in (

let uu____3001 = (bnorm env' u)
in (

let uu____3002 = (

let uu____3003 = (comp_to_typ c)
in (bnorm env' uu____3003))
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = uu____3001; FStar_Tactics_Types.goal_ty = uu____3002; FStar_Tactics_Types.opts = uu___94_3000.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___94_3000.FStar_Tactics_Types.is_guard})))
in (replace_cur uu____2999))
in (bind uu____2996 (fun uu____3010 -> (

let uu____3011 = (

let uu____3016 = (FStar_Syntax_Syntax.mk_binder bv)
in ((uu____3016), (b)))
in (ret uu____3011)))))
end
| uu____3021 -> begin
(fail "intro_rec: unification failed")
end)))))
end))))))))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3030 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail1 "intro_rec: goal is not an arrow (%s)" uu____3030))
end));
)))))


let norm : FStar_Syntax_Embeddings.norm_step Prims.list  ->  unit tac = (fun s -> (

let uu____3048 = (cur_goal ())
in (bind uu____3048 (fun goal -> (mlog (fun uu____3055 -> (

let uu____3056 = (FStar_Syntax_Print.term_to_string goal.FStar_Tactics_Types.witness)
in (FStar_Util.print1 "norm: witness = %s\n" uu____3056))) (fun uu____3061 -> (

let steps = (

let uu____3065 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldTac)::[]) uu____3065))
in (

let w = (normalize steps goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.witness)
in (

let t = (normalize steps goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (replace_cur (

let uu___95_3072 = goal
in {FStar_Tactics_Types.context = uu___95_3072.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = w; FStar_Tactics_Types.goal_ty = t; FStar_Tactics_Types.opts = uu___95_3072.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___95_3072.FStar_Tactics_Types.is_guard})))))))))))


let norm_term_env : env  ->  FStar_Syntax_Embeddings.norm_step Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun e s t -> (

let uu____3096 = (mlog (fun uu____3101 -> (

let uu____3102 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "norm_term: tm = %s\n" uu____3102))) (fun uu____3104 -> (bind get (fun ps -> (

let opts = (match (ps.FStar_Tactics_Types.goals) with
| (g)::uu____3110 -> begin
g.FStar_Tactics_Types.opts
end
| uu____3113 -> begin
(FStar_Options.peek ())
end)
in (mlog (fun uu____3118 -> (

let uu____3119 = (tts ps.FStar_Tactics_Types.main_context t)
in (FStar_Util.print1 "norm_term_env: t = %s\n" uu____3119))) (fun uu____3122 -> (

let uu____3123 = (__tc e t)
in (bind uu____3123 (fun uu____3144 -> (match (uu____3144) with
| (t1, uu____3154, uu____3155) -> begin
(

let steps = (

let uu____3159 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldTac)::[]) uu____3159))
in (

let t2 = (normalize steps ps.FStar_Tactics_Types.main_context t1)
in (ret t2)))
end)))))))))))
in (FStar_All.pipe_left (wrap_err "norm_term") uu____3096)))


let refine_intro : unit  ->  unit tac = (fun uu____3173 -> (

let uu____3176 = (

let uu____3179 = (cur_goal ())
in (bind uu____3179 (fun g -> (

let uu____3186 = (FStar_TypeChecker_Rel.base_and_refinement g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (match (uu____3186) with
| (uu____3199, FStar_Pervasives_Native.None) -> begin
(fail "not a refinement")
end
| (t, FStar_Pervasives_Native.Some (bv, phi)) -> begin
(

let g1 = (

let uu___96_3224 = g
in {FStar_Tactics_Types.context = uu___96_3224.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___96_3224.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = t; FStar_Tactics_Types.opts = uu___96_3224.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___96_3224.FStar_Tactics_Types.is_guard})
in (

let uu____3225 = (

let uu____3230 = (

let uu____3235 = (

let uu____3236 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____3236)::[])
in (FStar_Syntax_Subst.open_term uu____3235 phi))
in (match (uu____3230) with
| (bvs, phi1) -> begin
(

let uu____3255 = (

let uu____3256 = (FStar_List.hd bvs)
in (FStar_Pervasives_Native.fst uu____3256))
in ((uu____3255), (phi1)))
end))
in (match (uu____3225) with
| (bv1, phi1) -> begin
(

let uu____3269 = (

let uu____3272 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv1), (g.FStar_Tactics_Types.witness))))::[]) phi1)
in (mk_irrelevant_goal "refine_intro refinement" g.FStar_Tactics_Types.context uu____3272 g.FStar_Tactics_Types.opts))
in (bind uu____3269 (fun g2 -> (bind __dismiss (fun uu____3278 -> (add_goals ((g1)::(g2)::[])))))))
end)))
end)))))
in (FStar_All.pipe_left (wrap_err "refine_intro") uu____3176)))


let __exact_now : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun set_expected_typ1 t -> (

let uu____3297 = (cur_goal ())
in (bind uu____3297 (fun goal -> (

let env = (match (set_expected_typ1) with
| true -> begin
(FStar_TypeChecker_Env.set_expected_typ goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
end
| uu____3305 -> begin
goal.FStar_Tactics_Types.context
end)
in (

let uu____3306 = (__tc env t)
in (bind uu____3306 (fun uu____3325 -> (match (uu____3325) with
| (t1, typ, guard) -> begin
(mlog (fun uu____3340 -> (

let uu____3341 = (tts goal.FStar_Tactics_Types.context typ)
in (

let uu____3342 = (FStar_TypeChecker_Rel.guard_to_string goal.FStar_Tactics_Types.context guard)
in (FStar_Util.print2 "__exact_now: got type %s\n__exact_now and guard %s\n" uu____3341 uu____3342)))) (fun uu____3345 -> (

let uu____3346 = (proc_guard "__exact typing" goal.FStar_Tactics_Types.context guard goal.FStar_Tactics_Types.opts)
in (bind uu____3346 (fun uu____3350 -> (mlog (fun uu____3354 -> (

let uu____3355 = (tts goal.FStar_Tactics_Types.context typ)
in (

let uu____3356 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (FStar_Util.print2 "__exact_now: unifying %s and %s\n" uu____3355 uu____3356)))) (fun uu____3359 -> (

let uu____3360 = (do_unify goal.FStar_Tactics_Types.context typ goal.FStar_Tactics_Types.goal_ty)
in (bind uu____3360 (fun b -> (match (b) with
| true -> begin
(solve goal t1)
end
| uu____3367 -> begin
(

let uu____3368 = (tts goal.FStar_Tactics_Types.context t1)
in (

let uu____3369 = (tts goal.FStar_Tactics_Types.context typ)
in (

let uu____3370 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (

let uu____3371 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.witness)
in (fail4 "%s : %s does not exactly solve the goal %s (witness = %s)" uu____3368 uu____3369 uu____3370 uu____3371)))))
end)))))))))))
end)))))))))


let t_exact : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun set_expected_typ1 tm -> (

let uu____3386 = (mlog (fun uu____3391 -> (

let uu____3392 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "t_exact: tm = %s\n" uu____3392))) (fun uu____3395 -> (

let uu____3396 = (

let uu____3403 = (__exact_now set_expected_typ1 tm)
in (trytac' uu____3403))
in (bind uu____3396 (fun uu___62_3412 -> (match (uu___62_3412) with
| FStar_Util.Inr (r) -> begin
(ret ())
end
| FStar_Util.Inl (e) -> begin
(

let uu____3421 = (

let uu____3428 = (

let uu____3431 = (norm ((FStar_Syntax_Embeddings.Delta)::[]))
in (bind uu____3431 (fun uu____3436 -> (

let uu____3437 = (refine_intro ())
in (bind uu____3437 (fun uu____3441 -> (__exact_now set_expected_typ1 tm)))))))
in (trytac' uu____3428))
in (bind uu____3421 (fun uu___61_3448 -> (match (uu___61_3448) with
| FStar_Util.Inr (r) -> begin
(ret ())
end
| FStar_Util.Inl (uu____3456) -> begin
(fail e)
end))))
end))))))
in (FStar_All.pipe_left (wrap_err "exact") uu____3386)))


let uvar_free_in_goal : FStar_Syntax_Syntax.uvar  ->  FStar_Tactics_Types.goal  ->  Prims.bool = (fun u g -> (match (g.FStar_Tactics_Types.is_guard) with
| true -> begin
false
end
| uu____3471 -> begin
(

let free_uvars = (

let uu____3485 = (

let uu____3488 = (FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty)
in (FStar_Util.set_elements uu____3488))
in (FStar_List.map (fun u1 -> u1.FStar_Syntax_Syntax.ctx_uvar_head) uu____3485))
in (FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars))
end))


let uvar_free : FStar_Syntax_Syntax.uvar  ->  FStar_Tactics_Types.proofstate  ->  Prims.bool = (fun u ps -> (FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals))


let rec mapM : 'a 'b . ('a  ->  'b tac)  ->  'a Prims.list  ->  'b Prims.list tac = (fun f l -> (match (l) with
| [] -> begin
(ret [])
end
| (x)::xs -> begin
(

let uu____3568 = (f x)
in (bind uu____3568 (fun y -> (

let uu____3576 = (mapM f xs)
in (bind uu____3576 (fun ys -> (ret ((y)::ys))))))))
end))

exception NoUnif


let uu___is_NoUnif : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoUnif -> begin
true
end
| uu____3596 -> begin
false
end))


let rec __apply : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.typ  ->  unit tac = (fun uopt tm typ -> (

let uu____3616 = (cur_goal ())
in (bind uu____3616 (fun goal -> (mlog (fun uu____3623 -> (

let uu____3624 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3624))) (fun uu____3627 -> (

let uu____3628 = (

let uu____3633 = (

let uu____3636 = (t_exact false tm)
in (with_policy FStar_Tactics_Types.Force uu____3636))
in (trytac_exn uu____3633))
in (bind uu____3628 (fun uu___63_3643 -> (match (uu___63_3643) with
| FStar_Pervasives_Native.Some (r) -> begin
(ret ())
end
| FStar_Pervasives_Native.None -> begin
(mlog (fun uu____3651 -> (

let uu____3652 = (FStar_Syntax_Print.term_to_string typ)
in (FStar_Util.print1 ">>> typ = %s\n" uu____3652))) (fun uu____3655 -> (

let uu____3656 = (FStar_Syntax_Util.arrow_one typ)
in (match (uu____3656) with
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise NoUnif)
end
| FStar_Pervasives_Native.Some ((bv, aq), c) -> begin
(mlog (fun uu____3680 -> (

let uu____3681 = (FStar_Syntax_Print.binder_to_string ((bv), (aq)))
in (FStar_Util.print1 "__apply: pushing binder %s\n" uu____3681))) (fun uu____3684 -> (

let uu____3685 = (

let uu____3686 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____3686)))
in (match (uu____3685) with
| true -> begin
(fail "apply: not total codomain")
end
| uu____3689 -> begin
(

let uu____3690 = (new_uvar "apply" goal.FStar_Tactics_Types.context bv.FStar_Syntax_Syntax.sort)
in (bind uu____3690 (fun u -> (

let tm' = (FStar_Syntax_Syntax.mk_Tm_app tm ((((u), (aq)))::[]) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
in (

let typ' = (

let uu____3716 = (comp_to_typ c)
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (u))))::[])) uu____3716))
in (

let uu____3719 = (__apply uopt tm' typ')
in (bind uu____3719 (fun uu____3732 -> (

let u1 = (bnorm goal.FStar_Tactics_Types.context u)
in (

let uu____3734 = (

let uu____3735 = (

let uu____3738 = (

let uu____3739 = (FStar_Syntax_Util.head_and_args u1)
in (FStar_Pervasives_Native.fst uu____3739))
in (FStar_Syntax_Subst.compress uu____3738))
in uu____3735.FStar_Syntax_Syntax.n)
in (match (uu____3734) with
| FStar_Syntax_Syntax.Tm_uvar ({FStar_Syntax_Syntax.ctx_uvar_head = uvar; FStar_Syntax_Syntax.ctx_uvar_gamma = uu____3767; FStar_Syntax_Syntax.ctx_uvar_binders = uu____3768; FStar_Syntax_Syntax.ctx_uvar_typ = uu____3769; FStar_Syntax_Syntax.ctx_uvar_reason = uu____3770; FStar_Syntax_Syntax.ctx_uvar_should_check = uu____3771; FStar_Syntax_Syntax.ctx_uvar_range = uu____3772}) -> begin
(bind get (fun ps -> (

let uu____3796 = (uopt && (uvar_free uvar ps))
in (match (uu____3796) with
| true -> begin
(ret ())
end
| uu____3799 -> begin
(

let uu____3800 = (

let uu____3803 = (

let uu___97_3804 = goal
in (

let uu____3805 = (bnorm goal.FStar_Tactics_Types.context u1)
in (

let uu____3806 = (bnorm goal.FStar_Tactics_Types.context bv.FStar_Syntax_Syntax.sort)
in {FStar_Tactics_Types.context = uu___97_3804.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu____3805; FStar_Tactics_Types.goal_ty = uu____3806; FStar_Tactics_Types.opts = uu___97_3804.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = false})))
in (uu____3803)::[])
in (add_goals uu____3800))
end))))
end
| t -> begin
(ret ())
end)))))))))))
end))))
end))))
end))))))))))


let try_unif : 'a . 'a tac  ->  'a tac  ->  'a tac = (fun t t' -> (mk_tac (fun ps -> (FStar_All.try_with (fun uu___99_3840 -> (match (()) with
| () -> begin
(run t ps)
end)) (fun uu___98_3844 -> (match (uu___98_3844) with
| NoUnif -> begin
(run t' ps)
end))))))


let apply : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun uopt tm -> (

let uu____3861 = (mlog (fun uu____3866 -> (

let uu____3867 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "apply: tm = %s\n" uu____3867))) (fun uu____3870 -> (

let uu____3871 = (cur_goal ())
in (bind uu____3871 (fun goal -> (

let uu____3877 = (__tc goal.FStar_Tactics_Types.context tm)
in (bind uu____3877 (fun uu____3899 -> (match (uu____3899) with
| (tm1, typ, guard) -> begin
(

let typ1 = (bnorm goal.FStar_Tactics_Types.context typ)
in (

let uu____3912 = (

let uu____3915 = (

let uu____3918 = (__apply uopt tm1 typ1)
in (bind uu____3918 (fun uu____3922 -> (proc_guard "apply guard" goal.FStar_Tactics_Types.context guard goal.FStar_Tactics_Types.opts))))
in (focus uu____3915))
in (

let uu____3923 = (

let uu____3926 = (tts goal.FStar_Tactics_Types.context tm1)
in (

let uu____3927 = (tts goal.FStar_Tactics_Types.context typ1)
in (

let uu____3928 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail3 "Cannot instantiate %s (of type %s) to match goal (%s)" uu____3926 uu____3927 uu____3928))))
in (try_unif uu____3912 uu____3923))))
end)))))))))
in (FStar_All.pipe_left (wrap_err "apply") uu____3861)))


let lemma_or_sq : FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun c -> (

let ct = (FStar_Syntax_Util.comp_to_comp_typ_nouniv c)
in (

let uu____3951 = (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____3951) with
| true -> begin
(

let uu____3958 = (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre)::(post)::uu____3973 -> begin
(((FStar_Pervasives_Native.fst pre)), ((FStar_Pervasives_Native.fst post)))
end
| uu____4014 -> begin
(failwith "apply_lemma: impossible: not a lemma")
end)
in (match (uu____3958) with
| (pre, post) -> begin
(

let post1 = (

let uu____4044 = (

let uu____4053 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit)
in (uu____4053)::[])
in (FStar_Syntax_Util.mk_app post uu____4044))
in FStar_Pervasives_Native.Some (((pre), (post1))))
end))
end
| uu____4076 -> begin
(

let uu____4077 = (FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name)
in (match (uu____4077) with
| true -> begin
(

let uu____4084 = (FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.map_opt uu____4084 (fun post -> ((FStar_Syntax_Util.t_true), (post)))))
end
| uu____4103 -> begin
FStar_Pervasives_Native.None
end))
end))))


let apply_lemma : FStar_Syntax_Syntax.term  ->  unit tac = (fun tm -> (

let uu____4117 = (

let uu____4120 = (mlog (fun uu____4125 -> (

let uu____4126 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4126))) (fun uu____4130 -> (

let is_unit_t = (fun t -> (

let uu____4137 = (

let uu____4138 = (FStar_Syntax_Subst.compress t)
in uu____4138.FStar_Syntax_Syntax.n)
in (match (uu____4137) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
true
end
| uu____4142 -> begin
false
end)))
in (

let uu____4143 = (cur_goal ())
in (bind uu____4143 (fun goal -> (

let uu____4149 = (__tc goal.FStar_Tactics_Types.context tm)
in (bind uu____4149 (fun uu____4172 -> (match (uu____4172) with
| (tm1, t, guard) -> begin
(

let uu____4184 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____4184) with
| (bs, comp) -> begin
(

let uu____4211 = (lemma_or_sq comp)
in (match (uu____4211) with
| FStar_Pervasives_Native.None -> begin
(fail "not a lemma or squashed function")
end
| FStar_Pervasives_Native.Some (pre, post) -> begin
(

let uu____4230 = (FStar_List.fold_left (fun uu____4272 uu____4273 -> (match (((uu____4272), (uu____4273))) with
| ((uvs, guard1, subst1), (b, aq)) -> begin
(

let b_t = (FStar_Syntax_Subst.subst subst1 b.FStar_Syntax_Syntax.sort)
in (

let uu____4364 = (is_unit_t b_t)
in (match (uu____4364) with
| true -> begin
(((((FStar_Syntax_Util.exp_unit), (aq)))::uvs), (guard1), ((FStar_Syntax_Syntax.NT (((b), (FStar_Syntax_Util.exp_unit))))::subst1))
end
| uu____4399 -> begin
(

let uu____4400 = (FStar_TypeChecker_Util.new_implicit_var "apply_lemma" goal.FStar_Tactics_Types.goal_ty.FStar_Syntax_Syntax.pos goal.FStar_Tactics_Types.context b_t)
in (match (uu____4400) with
| (u, uu____4428, g_u) -> begin
(

let uu____4442 = (FStar_TypeChecker_Rel.conj_guard guard1 g_u)
in (((((u), (aq)))::uvs), (uu____4442), ((FStar_Syntax_Syntax.NT (((b), (u))))::subst1)))
end))
end)))
end)) (([]), (guard), ([])) bs)
in (match (uu____4230) with
| (uvs, implicits, subst1) -> begin
(

let uvs1 = (FStar_List.rev uvs)
in (

let pre1 = (FStar_Syntax_Subst.subst subst1 pre)
in (

let post1 = (FStar_Syntax_Subst.subst subst1 post)
in (

let uu____4503 = (

let uu____4506 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero post1)
in (do_unify goal.FStar_Tactics_Types.context uu____4506 goal.FStar_Tactics_Types.goal_ty))
in (bind uu____4503 (fun b -> (match ((not (b))) with
| true -> begin
(

let uu____4514 = (tts goal.FStar_Tactics_Types.context tm1)
in (

let uu____4515 = (

let uu____4516 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero post1)
in (tts goal.FStar_Tactics_Types.context uu____4516))
in (

let uu____4517 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail3 "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)" uu____4514 uu____4515 uu____4517))))
end
| uu____4518 -> begin
(

let uu____4519 = (add_implicits implicits.FStar_TypeChecker_Env.implicits)
in (bind uu____4519 (fun uu____4524 -> (

let uu____4525 = (solve goal FStar_Syntax_Util.exp_unit)
in (bind uu____4525 (fun uu____4533 -> (

let is_free_uvar = (fun uv t1 -> (

let free_uvars = (

let uu____4558 = (

let uu____4561 = (FStar_Syntax_Free.uvars t1)
in (FStar_Util.set_elements uu____4561))
in (FStar_List.map (fun x -> x.FStar_Syntax_Syntax.ctx_uvar_head) uu____4558))
in (FStar_List.existsML (fun u -> (FStar_Syntax_Unionfind.equiv u uv)) free_uvars)))
in (

let appears = (fun uv goals -> (FStar_List.existsML (fun g' -> (is_free_uvar uv g'.FStar_Tactics_Types.goal_ty)) goals))
in (

let checkone = (fun t1 goals -> (

let uu____4610 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____4610) with
| (hd1, uu____4626) -> begin
(match (hd1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv) -> begin
(appears uv.FStar_Syntax_Syntax.ctx_uvar_head goals)
end
| uu____4648 -> begin
false
end)
end)))
in (

let uu____4649 = (FStar_All.pipe_right implicits.FStar_TypeChecker_Env.implicits (mapM (fun uu____4717 -> (match (uu____4717) with
| (_msg, term, ctx_uvar, _range, uu____4742) -> begin
(

let uu____4743 = (FStar_Syntax_Util.head_and_args term)
in (match (uu____4743) with
| (hd1, uu____4769) -> begin
(

let env = (

let uu___100_4791 = goal.FStar_Tactics_Types.context
in {FStar_TypeChecker_Env.solver = uu___100_4791.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___100_4791.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___100_4791.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_TypeChecker_Env.gamma_sig = uu___100_4791.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___100_4791.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___100_4791.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___100_4791.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___100_4791.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___100_4791.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___100_4791.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___100_4791.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___100_4791.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___100_4791.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___100_4791.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___100_4791.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___100_4791.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___100_4791.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___100_4791.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___100_4791.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___100_4791.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___100_4791.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___100_4791.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___100_4791.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___100_4791.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___100_4791.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___100_4791.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___100_4791.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___100_4791.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___100_4791.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___100_4791.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___100_4791.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___100_4791.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___100_4791.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___100_4791.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___100_4791.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___100_4791.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___100_4791.FStar_TypeChecker_Env.dep_graph})
in (

let uu____4792 = (

let uu____4793 = (FStar_Syntax_Subst.compress hd1)
in uu____4793.FStar_Syntax_Syntax.n)
in (match (uu____4792) with
| FStar_Syntax_Syntax.Tm_uvar (uu____4806) -> begin
(

let uu____4807 = (

let uu____4816 = (

let uu____4819 = (

let uu___101_4820 = goal
in (

let uu____4821 = (bnorm env term)
in (

let uu____4822 = (bnorm env ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in {FStar_Tactics_Types.context = env; FStar_Tactics_Types.witness = uu____4821; FStar_Tactics_Types.goal_ty = uu____4822; FStar_Tactics_Types.opts = uu___101_4820.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___101_4820.FStar_Tactics_Types.is_guard})))
in (uu____4819)::[])
in ((uu____4816), ([])))
in (ret uu____4807))
end
| uu____4835 -> begin
(

let g_typ = (

let uu____4837 = (FStar_Options.__temp_fast_implicits ())
in (match (uu____4837) with
| true -> begin
(FStar_TypeChecker_TcTerm.check_type_of_well_typed_term false env term ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
end
| uu____4838 -> begin
(

let term1 = (bnorm env term)
in (

let uu____4840 = (

let uu____4847 = (FStar_TypeChecker_Env.set_expected_typ env ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in (env.FStar_TypeChecker_Env.type_of uu____4847 term1))
in (match (uu____4840) with
| (uu____4848, uu____4849, g_typ) -> begin
g_typ
end)))
end))
in (

let uu____4851 = (goal_from_guard "apply_lemma solved arg" goal.FStar_Tactics_Types.context g_typ goal.FStar_Tactics_Types.opts)
in (bind uu____4851 (fun uu___64_4867 -> (match (uu___64_4867) with
| FStar_Pervasives_Native.None -> begin
(ret (([]), ([])))
end
| FStar_Pervasives_Native.Some (g) -> begin
(ret (([]), ((g)::[])))
end)))))
end)))
end))
end))))
in (bind uu____4649 (fun goals_ -> (

let sub_goals = (

let uu____4935 = (FStar_List.map FStar_Pervasives_Native.fst goals_)
in (FStar_List.flatten uu____4935))
in (

let smt_goals = (

let uu____4957 = (FStar_List.map FStar_Pervasives_Native.snd goals_)
in (FStar_List.flatten uu____4957))
in (

let rec filter' = (fun f xs -> (match (xs) with
| [] -> begin
[]
end
| (x)::xs1 -> begin
(

let uu____5018 = (f x xs1)
in (match (uu____5018) with
| true -> begin
(

let uu____5021 = (filter' f xs1)
in (x)::uu____5021)
end
| uu____5024 -> begin
(filter' f xs1)
end))
end))
in (

let sub_goals1 = (filter' (fun g goals -> (

let uu____5035 = (checkone g.FStar_Tactics_Types.witness goals)
in (not (uu____5035)))) sub_goals)
in (

let uu____5036 = (proc_guard "apply_lemma guard" goal.FStar_Tactics_Types.context guard goal.FStar_Tactics_Types.opts)
in (bind uu____5036 (fun uu____5041 -> (

let uu____5042 = (

let uu____5045 = (

let uu____5046 = (

let uu____5047 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero pre1)
in (istrivial goal.FStar_Tactics_Types.context uu____5047))
in (not (uu____5046)))
in (match (uu____5045) with
| true -> begin
(add_irrelevant_goal "apply_lemma precondition" goal.FStar_Tactics_Types.context pre1 goal.FStar_Tactics_Types.opts)
end
| uu____5050 -> begin
(ret ())
end))
in (bind uu____5042 (fun uu____5053 -> (

let uu____5054 = (add_smt_goals smt_goals)
in (bind uu____5054 (fun uu____5058 -> (add_goals sub_goals1))))))))))))))))))))))))))
end)))))))
end))
end))
end))
end))))))))))
in (focus uu____4120))
in (FStar_All.pipe_left (wrap_err "apply_lemma") uu____4117)))


let destruct_eq' : FStar_Reflection_Data.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun typ -> (

let uu____5080 = (FStar_Syntax_Util.destruct_typ_as_formula typ)
in (match (uu____5080) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (l, (uu____5090)::((e1, uu____5092))::((e2, uu____5094))::[])) when (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) -> begin
FStar_Pervasives_Native.Some (((e1), (e2)))
end
| uu____5137 -> begin
FStar_Pervasives_Native.None
end)))


let destruct_eq : FStar_Reflection_Data.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun typ -> (

let uu____5161 = (destruct_eq' typ)
in (match (uu____5161) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5191 = (FStar_Syntax_Util.un_squash typ)
in (match (uu____5191) with
| FStar_Pervasives_Native.Some (typ1) -> begin
(destruct_eq' typ1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end)))


let split_env : FStar_Syntax_Syntax.bv  ->  env  ->  (env * FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.option = (fun bvar e -> (

let rec aux = (fun e1 -> (

let uu____5253 = (FStar_TypeChecker_Env.pop_bv e1)
in (match (uu____5253) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (bv', e') -> begin
(match ((FStar_Syntax_Syntax.bv_eq bvar bv')) with
| true -> begin
FStar_Pervasives_Native.Some (((e'), ([])))
end
| uu____5300 -> begin
(

let uu____5301 = (aux e')
in (FStar_Util.map_opt uu____5301 (fun uu____5325 -> (match (uu____5325) with
| (e'', bvs) -> begin
((e''), ((bv')::bvs))
end))))
end)
end)))
in (

let uu____5346 = (aux e)
in (FStar_Util.map_opt uu____5346 (fun uu____5370 -> (match (uu____5370) with
| (e', bvs) -> begin
((e'), ((FStar_List.rev bvs)))
end))))))


let push_bvs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_TypeChecker_Env.env = (fun e bvs -> (FStar_List.fold_left (fun e1 b -> (FStar_TypeChecker_Env.push_bv e1 b)) e bvs))


let subst_goal : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Tactics_Types.goal  ->  FStar_Tactics_Types.goal FStar_Pervasives_Native.option = (fun b1 b2 s g -> (

let uu____5437 = (split_env b1 g.FStar_Tactics_Types.context)
in (FStar_Util.map_opt uu____5437 (fun uu____5461 -> (match (uu____5461) with
| (e0, bvs) -> begin
(

let s1 = (fun bv -> (

let uu___102_5480 = bv
in (

let uu____5481 = (FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___102_5480.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___102_5480.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5481})))
in (

let bvs1 = (FStar_List.map s1 bvs)
in (

let c = (push_bvs e0 ((b2)::bvs1))
in (

let w = (FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness)
in (

let t = (FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty)
in (

let uu___103_5490 = g
in {FStar_Tactics_Types.context = c; FStar_Tactics_Types.witness = w; FStar_Tactics_Types.goal_ty = t; FStar_Tactics_Types.opts = uu___103_5490.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___103_5490.FStar_Tactics_Types.is_guard}))))))
end)))))


let rewrite : FStar_Syntax_Syntax.binder  ->  unit tac = (fun h -> (

let uu____5500 = (cur_goal ())
in (bind uu____5500 (fun goal -> (

let uu____5508 = h
in (match (uu____5508) with
| (bv, uu____5512) -> begin
(mlog (fun uu____5516 -> (

let uu____5517 = (FStar_Syntax_Print.bv_to_string bv)
in (

let uu____5518 = (tts goal.FStar_Tactics_Types.context bv.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5517 uu____5518)))) (fun uu____5521 -> (

let uu____5522 = (split_env bv goal.FStar_Tactics_Types.context)
in (match (uu____5522) with
| FStar_Pervasives_Native.None -> begin
(fail "rewrite: binder not found in environment")
end
| FStar_Pervasives_Native.Some (e0, bvs) -> begin
(

let uu____5551 = (destruct_eq bv.FStar_Syntax_Syntax.sort)
in (match (uu____5551) with
| FStar_Pervasives_Native.Some (x, e) -> begin
(

let uu____5566 = (

let uu____5567 = (FStar_Syntax_Subst.compress x)
in uu____5567.FStar_Syntax_Syntax.n)
in (match (uu____5566) with
| FStar_Syntax_Syntax.Tm_name (x1) -> begin
(

let s = (FStar_Syntax_Syntax.NT (((x1), (e))))::[]
in (

let s1 = (fun bv1 -> (

let uu___104_5584 = bv1
in (

let uu____5585 = (FStar_Syntax_Subst.subst s bv1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___104_5584.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___104_5584.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5585})))
in (

let bvs1 = (FStar_List.map s1 bvs)
in (

let uu____5591 = (

let uu___105_5592 = goal
in (

let uu____5593 = (push_bvs e0 ((bv)::bvs1))
in (

let uu____5594 = (FStar_Syntax_Subst.subst s goal.FStar_Tactics_Types.witness)
in (

let uu____5595 = (FStar_Syntax_Subst.subst s goal.FStar_Tactics_Types.goal_ty)
in {FStar_Tactics_Types.context = uu____5593; FStar_Tactics_Types.witness = uu____5594; FStar_Tactics_Types.goal_ty = uu____5595; FStar_Tactics_Types.opts = uu___105_5592.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___105_5592.FStar_Tactics_Types.is_guard}))))
in (replace_cur uu____5591)))))
end
| uu____5596 -> begin
(fail "rewrite: Not an equality hypothesis with a variable on the LHS")
end))
end
| uu____5597 -> begin
(fail "rewrite: Not an equality hypothesis")
end))
end))))
end))))))


let rename_to : FStar_Syntax_Syntax.binder  ->  Prims.string  ->  unit tac = (fun b s -> (

let uu____5618 = (cur_goal ())
in (bind uu____5618 (fun goal -> (

let uu____5629 = b
in (match (uu____5629) with
| (bv, uu____5633) -> begin
(

let bv' = (

let uu____5635 = (

let uu___106_5636 = bv
in (

let uu____5637 = (FStar_Ident.mk_ident ((s), (bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
in {FStar_Syntax_Syntax.ppname = uu____5637; FStar_Syntax_Syntax.index = uu___106_5636.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___106_5636.FStar_Syntax_Syntax.sort}))
in (FStar_Syntax_Syntax.freshen_bv uu____5635))
in (

let s1 = (

let uu____5641 = (

let uu____5642 = (

let uu____5649 = (FStar_Syntax_Syntax.bv_to_name bv')
in ((bv), (uu____5649)))
in FStar_Syntax_Syntax.NT (uu____5642))
in (uu____5641)::[])
in (

let uu____5654 = (subst_goal bv bv' s1 goal)
in (match (uu____5654) with
| FStar_Pervasives_Native.None -> begin
(fail "rename_to: binder not found in environment")
end
| FStar_Pervasives_Native.Some (goal1) -> begin
(replace_cur goal1)
end))))
end))))))


let binder_retype : FStar_Syntax_Syntax.binder  ->  unit tac = (fun b -> (

let uu____5669 = (cur_goal ())
in (bind uu____5669 (fun goal -> (

let uu____5678 = b
in (match (uu____5678) with
| (bv, uu____5682) -> begin
(

let uu____5683 = (split_env bv goal.FStar_Tactics_Types.context)
in (match (uu____5683) with
| FStar_Pervasives_Native.None -> begin
(fail "binder_retype: binder is not present in environment")
end
| FStar_Pervasives_Native.Some (e0, bvs) -> begin
(

let uu____5712 = (FStar_Syntax_Util.type_u ())
in (match (uu____5712) with
| (ty, u) -> begin
(

let uu____5721 = (new_uvar "binder_retype" e0 ty)
in (bind uu____5721 (fun t' -> (

let bv'' = (

let uu___107_5731 = bv
in {FStar_Syntax_Syntax.ppname = uu___107_5731.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___107_5731.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t'})
in (

let s = (

let uu____5735 = (

let uu____5736 = (

let uu____5743 = (FStar_Syntax_Syntax.bv_to_name bv'')
in ((bv), (uu____5743)))
in FStar_Syntax_Syntax.NT (uu____5736))
in (uu____5735)::[])
in (

let bvs1 = (FStar_List.map (fun b1 -> (

let uu___108_5755 = b1
in (

let uu____5756 = (FStar_Syntax_Subst.subst s b1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___108_5755.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___108_5755.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5756}))) bvs)
in (

let env' = (push_bvs e0 ((bv'')::bvs1))
in (bind __dismiss (fun uu____5762 -> (

let uu____5763 = (

let uu____5766 = (

let uu____5769 = (

let uu___109_5770 = goal
in (

let uu____5771 = (FStar_Syntax_Subst.subst s goal.FStar_Tactics_Types.witness)
in (

let uu____5772 = (FStar_Syntax_Subst.subst s goal.FStar_Tactics_Types.goal_ty)
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = uu____5771; FStar_Tactics_Types.goal_ty = uu____5772; FStar_Tactics_Types.opts = uu___109_5770.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___109_5770.FStar_Tactics_Types.is_guard})))
in (uu____5769)::[])
in (add_goals uu____5766))
in (bind uu____5763 (fun uu____5775 -> (

let uu____5776 = (FStar_Syntax_Util.mk_eq2 (FStar_Syntax_Syntax.U_succ (u)) ty bv.FStar_Syntax_Syntax.sort t')
in (add_irrelevant_goal "binder_retype equation" e0 uu____5776 goal.FStar_Tactics_Types.opts))))))))))))))
end))
end))
end))))))


let norm_binder_type : FStar_Syntax_Embeddings.norm_step Prims.list  ->  FStar_Syntax_Syntax.binder  ->  unit tac = (fun s b -> (

let uu____5795 = (cur_goal ())
in (bind uu____5795 (fun goal -> (

let uu____5804 = b
in (match (uu____5804) with
| (bv, uu____5808) -> begin
(

let uu____5809 = (split_env bv goal.FStar_Tactics_Types.context)
in (match (uu____5809) with
| FStar_Pervasives_Native.None -> begin
(fail "binder_retype: binder is not present in environment")
end
| FStar_Pervasives_Native.Some (e0, bvs) -> begin
(

let steps = (

let uu____5841 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldTac)::[]) uu____5841))
in (

let sort' = (normalize steps e0 bv.FStar_Syntax_Syntax.sort)
in (

let bv' = (

let uu___110_5846 = bv
in {FStar_Syntax_Syntax.ppname = uu___110_5846.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___110_5846.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort'})
in (

let env' = (push_bvs e0 ((bv')::bvs))
in (replace_cur (

let uu___111_5850 = goal
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = uu___111_5850.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___111_5850.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___111_5850.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___111_5850.FStar_Tactics_Types.is_guard}))))))
end))
end))))))


let revert : unit  ->  unit tac = (fun uu____5857 -> (

let uu____5860 = (cur_goal ())
in (bind uu____5860 (fun goal -> (

let uu____5866 = (FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context)
in (match (uu____5866) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot revert; empty context")
end
| FStar_Pervasives_Native.Some (x, env') -> begin
(

let typ' = (

let uu____5888 = (FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty)
in (FStar_Syntax_Util.arrow ((((x), (FStar_Pervasives_Native.None)))::[]) uu____5888))
in (

let w' = (FStar_Syntax_Util.abs ((((x), (FStar_Pervasives_Native.None)))::[]) goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None)
in (replace_cur (

let uu___112_5912 = goal
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = w'; FStar_Tactics_Types.goal_ty = typ'; FStar_Tactics_Types.opts = uu___112_5912.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___112_5912.FStar_Tactics_Types.is_guard}))))
end))))))


let free_in : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun bv t -> (

let uu____5923 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_mem bv uu____5923)))


let rec clear : FStar_Syntax_Syntax.binder  ->  unit tac = (fun b -> (

let bv = (FStar_Pervasives_Native.fst b)
in (

let uu____5936 = (cur_goal ())
in (bind uu____5936 (fun goal -> (mlog (fun uu____5944 -> (

let uu____5945 = (FStar_Syntax_Print.binder_to_string b)
in (

let uu____5946 = (

let uu____5947 = (

let uu____5948 = (FStar_TypeChecker_Env.all_binders goal.FStar_Tactics_Types.context)
in (FStar_All.pipe_right uu____5948 FStar_List.length))
in (FStar_All.pipe_right uu____5947 FStar_Util.string_of_int))
in (FStar_Util.print2 "Clear of (%s), env has %s binders\n" uu____5945 uu____5946)))) (fun uu____5967 -> (

let uu____5968 = (split_env bv goal.FStar_Tactics_Types.context)
in (match (uu____5968) with
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

let uu____6015 = (free_in bv bv'.FStar_Syntax_Syntax.sort)
in (match (uu____6015) with
| true -> begin
(

let uu____6018 = (

let uu____6019 = (FStar_Syntax_Print.bv_to_string bv')
in (FStar_Util.format1 "Cannot clear; binder present in the type of %s" uu____6019))
in (fail uu____6018))
end
| uu____6020 -> begin
(check1 bvs2)
end))
end))
in (

let uu____6021 = (free_in bv goal.FStar_Tactics_Types.goal_ty)
in (match (uu____6021) with
| true -> begin
(fail "Cannot clear; binder present in goal")
end
| uu____6024 -> begin
(

let uu____6025 = (check1 bvs)
in (bind uu____6025 (fun uu____6031 -> (

let env' = (push_bvs e' bvs)
in (

let uu____6033 = (new_uvar "clear.witness" env' goal.FStar_Tactics_Types.goal_ty)
in (bind uu____6033 (fun ut -> (

let uu____6039 = (do_unify goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.witness ut)
in (bind uu____6039 (fun b1 -> (match (b1) with
| true -> begin
(replace_cur (

let uu___113_6048 = goal
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = ut; FStar_Tactics_Types.goal_ty = uu___113_6048.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___113_6048.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___113_6048.FStar_Tactics_Types.is_guard}))
end
| uu____6049 -> begin
(fail "Cannot clear; binder appears in witness")
end)))))))))))
end)))
end)))))))))


let clear_top : unit  ->  unit tac = (fun uu____6056 -> (

let uu____6059 = (cur_goal ())
in (bind uu____6059 (fun goal -> (

let uu____6065 = (FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context)
in (match (uu____6065) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot clear; empty context")
end
| FStar_Pervasives_Native.Some (x, uu____6079) -> begin
(

let uu____6084 = (FStar_Syntax_Syntax.mk_binder x)
in (clear uu____6084))
end))))))


let prune : Prims.string  ->  unit tac = (fun s -> (

let uu____6094 = (cur_goal ())
in (bind uu____6094 (fun g -> (

let ctx = g.FStar_Tactics_Types.context
in (

let ctx' = (

let uu____6104 = (FStar_Ident.path_of_text s)
in (FStar_TypeChecker_Env.rem_proof_ns ctx uu____6104))
in (

let g' = (

let uu___114_6106 = g
in {FStar_Tactics_Types.context = ctx'; FStar_Tactics_Types.witness = uu___114_6106.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___114_6106.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___114_6106.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___114_6106.FStar_Tactics_Types.is_guard})
in (bind __dismiss (fun uu____6108 -> (add_goals ((g')::[])))))))))))


let addns : Prims.string  ->  unit tac = (fun s -> (

let uu____6118 = (cur_goal ())
in (bind uu____6118 (fun g -> (

let ctx = g.FStar_Tactics_Types.context
in (

let ctx' = (

let uu____6128 = (FStar_Ident.path_of_text s)
in (FStar_TypeChecker_Env.add_proof_ns ctx uu____6128))
in (

let g' = (

let uu___115_6130 = g
in {FStar_Tactics_Types.context = ctx'; FStar_Tactics_Types.witness = uu___115_6130.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___115_6130.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___115_6130.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___115_6130.FStar_Tactics_Types.is_guard})
in (bind __dismiss (fun uu____6132 -> (add_goals ((g')::[])))))))))))


let rec tac_fold_env : FStar_Tactics_Types.direction  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac)  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun d f env t -> (

let tn = (

let uu____6172 = (FStar_Syntax_Subst.compress t)
in uu____6172.FStar_Syntax_Syntax.n)
in (

let uu____6175 = (match ((Prims.op_Equality d FStar_Tactics_Types.TopDown)) with
| true -> begin
(f env (

let uu___119_6181 = t
in {FStar_Syntax_Syntax.n = tn; FStar_Syntax_Syntax.pos = uu___119_6181.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___119_6181.FStar_Syntax_Syntax.vars}))
end
| uu____6182 -> begin
(ret t)
end)
in (bind uu____6175 (fun t1 -> (

let ff = (tac_fold_env d f env)
in (

let tn1 = (

let uu____6197 = (

let uu____6198 = (FStar_Syntax_Subst.compress t1)
in uu____6198.FStar_Syntax_Syntax.n)
in (match (uu____6197) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____6225 = (ff hd1)
in (bind uu____6225 (fun hd2 -> (

let fa = (fun uu____6247 -> (match (uu____6247) with
| (a, q) -> begin
(

let uu____6260 = (ff a)
in (bind uu____6260 (fun a1 -> (ret ((a1), (q))))))
end))
in (

let uu____6273 = (mapM fa args)
in (bind uu____6273 (fun args1 -> (ret (FStar_Syntax_Syntax.Tm_app (((hd2), (args1))))))))))))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, k) -> begin
(

let uu____6339 = (FStar_Syntax_Subst.open_term bs t2)
in (match (uu____6339) with
| (bs1, t') -> begin
(

let uu____6348 = (

let uu____6351 = (FStar_TypeChecker_Env.push_binders env bs1)
in (tac_fold_env d f uu____6351 t'))
in (bind uu____6348 (fun t'' -> (

let uu____6355 = (

let uu____6356 = (

let uu____6373 = (FStar_Syntax_Subst.close_binders bs1)
in (

let uu____6380 = (FStar_Syntax_Subst.close bs1 t'')
in ((uu____6373), (uu____6380), (k))))
in FStar_Syntax_Syntax.Tm_abs (uu____6356))
in (ret uu____6355)))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(ret tn)
end
| FStar_Syntax_Syntax.Tm_match (hd1, brs) -> begin
(

let uu____6449 = (ff hd1)
in (bind uu____6449 (fun hd2 -> (

let ffb = (fun br -> (

let uu____6464 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____6464) with
| (pat, w, e) -> begin
(

let bvs = (FStar_Syntax_Syntax.pat_bvs pat)
in (

let ff1 = (

let uu____6496 = (FStar_TypeChecker_Env.push_bvs env bvs)
in (tac_fold_env d f uu____6496))
in (

let uu____6497 = (ff1 e)
in (bind uu____6497 (fun e1 -> (

let br1 = (FStar_Syntax_Subst.close_branch ((pat), (w), (e1)))
in (ret br1)))))))
end)))
in (

let uu____6512 = (mapM ffb brs)
in (bind uu____6512 (fun brs1 -> (ret (FStar_Syntax_Syntax.Tm_match (((hd2), (brs1))))))))))))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (bv); FStar_Syntax_Syntax.lbunivs = uu____6556; FStar_Syntax_Syntax.lbtyp = uu____6557; FStar_Syntax_Syntax.lbeff = uu____6558; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu____6560; FStar_Syntax_Syntax.lbpos = uu____6561})::[]), e) -> begin
(

let lb = (

let uu____6586 = (

let uu____6587 = (FStar_Syntax_Subst.compress t1)
in uu____6587.FStar_Syntax_Syntax.n)
in (match (uu____6586) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), uu____6591) -> begin
lb
end
| uu____6604 -> begin
(failwith "impossible")
end))
in (

let fflb = (fun lb1 -> (

let uu____6613 = (ff lb1.FStar_Syntax_Syntax.lbdef)
in (bind uu____6613 (fun def1 -> (ret (

let uu___116_6619 = lb1
in {FStar_Syntax_Syntax.lbname = uu___116_6619.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___116_6619.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___116_6619.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___116_6619.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def1; FStar_Syntax_Syntax.lbattrs = uu___116_6619.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___116_6619.FStar_Syntax_Syntax.lbpos}))))))
in (

let uu____6620 = (fflb lb)
in (bind uu____6620 (fun lb1 -> (

let uu____6630 = (

let uu____6635 = (

let uu____6636 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____6636)::[])
in (FStar_Syntax_Subst.open_term uu____6635 e))
in (match (uu____6630) with
| (bs, e1) -> begin
(

let ff1 = (

let uu____6660 = (FStar_TypeChecker_Env.push_binders env bs)
in (tac_fold_env d f uu____6660))
in (

let uu____6661 = (ff1 e1)
in (bind uu____6661 (fun e2 -> (

let e3 = (FStar_Syntax_Subst.close bs e2)
in (ret (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e3))))))))))
end)))))))
end
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e) -> begin
(

let fflb = (fun lb -> (

let uu____6702 = (ff lb.FStar_Syntax_Syntax.lbdef)
in (bind uu____6702 (fun def -> (ret (

let uu___117_6708 = lb
in {FStar_Syntax_Syntax.lbname = uu___117_6708.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___117_6708.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___117_6708.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___117_6708.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu___117_6708.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___117_6708.FStar_Syntax_Syntax.lbpos}))))))
in (

let uu____6709 = (FStar_Syntax_Subst.open_let_rec lbs e)
in (match (uu____6709) with
| (lbs1, e1) -> begin
(

let uu____6724 = (mapM fflb lbs1)
in (bind uu____6724 (fun lbs2 -> (

let uu____6736 = (ff e1)
in (bind uu____6736 (fun e2 -> (

let uu____6744 = (FStar_Syntax_Subst.close_let_rec lbs2 e2)
in (match (uu____6744) with
| (lbs3, e3) -> begin
(ret (FStar_Syntax_Syntax.Tm_let (((((true), (lbs3))), (e3)))))
end))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, asc, eff) -> begin
(

let uu____6812 = (ff t2)
in (bind uu____6812 (fun t3 -> (ret (FStar_Syntax_Syntax.Tm_ascribed (((t3), (asc), (eff))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t2, m) -> begin
(

let uu____6843 = (ff t2)
in (bind uu____6843 (fun t3 -> (ret (FStar_Syntax_Syntax.Tm_meta (((t3), (m))))))))
end
| uu____6850 -> begin
(ret tn)
end))
in (bind tn1 (fun tn2 -> (

let t' = (

let uu___118_6857 = t1
in {FStar_Syntax_Syntax.n = tn2; FStar_Syntax_Syntax.pos = uu___118_6857.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___118_6857.FStar_Syntax_Syntax.vars})
in (match ((Prims.op_Equality d FStar_Tactics_Types.BottomUp)) with
| true -> begin
(f env t')
end
| uu____6860 -> begin
(ret t')
end)))))))))))


let pointwise_rec : FStar_Tactics_Types.proofstate  ->  unit tac  ->  FStar_Options.optionstate  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun ps tau opts env t -> (

let uu____6894 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____6894) with
| (t1, lcomp, g) -> begin
(

let uu____6906 = ((

let uu____6909 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp)
in (not (uu____6909))) || (

let uu____6911 = (FStar_TypeChecker_Rel.is_trivial g)
in (not (uu____6911))))
in (match (uu____6906) with
| true -> begin
(ret t1)
end
| uu____6914 -> begin
(

let rewrite_eq = (

let typ = lcomp.FStar_Syntax_Syntax.res_typ
in (

let uu____6921 = (new_uvar "pointwise_rec" env typ)
in (bind uu____6921 (fun ut -> ((log ps (fun uu____6932 -> (

let uu____6933 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6934 = (FStar_Syntax_Print.term_to_string ut)
in (FStar_Util.print2 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n" uu____6933 uu____6934)))));
(

let uu____6935 = (

let uu____6938 = (

let uu____6939 = (FStar_TypeChecker_TcTerm.universe_of env typ)
in (FStar_Syntax_Util.mk_eq2 uu____6939 typ t1 ut))
in (add_irrelevant_goal "pointwise_rec equation" env uu____6938 opts))
in (bind uu____6935 (fun uu____6942 -> (

let uu____6943 = (bind tau (fun uu____6949 -> (

let ut1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env ut)
in ((log ps (fun uu____6955 -> (

let uu____6956 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6957 = (FStar_Syntax_Print.term_to_string ut1)
in (FStar_Util.print2 "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n" uu____6956 uu____6957)))));
(ret ut1);
))))
in (focus uu____6943)))));
)))))
in (

let uu____6958 = (trytac' rewrite_eq)
in (bind uu____6958 (fun x -> (match (x) with
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
| uu____7068 -> begin
c
end))
in (

let maybe_continue = (fun ctrl1 t1 k -> (match ((Prims.op_Equality ctrl1 globalStop)) with
| true -> begin
(ret ((t1), (globalStop)))
end
| uu____7138 -> begin
(match ((Prims.op_Equality ctrl1 proceedToNextSubtree)) with
| true -> begin
(ret ((t1), (keepGoing)))
end
| uu____7155 -> begin
(k t1)
end)
end))
in (

let uu____7156 = (FStar_Syntax_Subst.compress t)
in (maybe_continue ctrl uu____7156 (fun t1 -> (

let uu____7164 = (f env (

let uu___122_7173 = t1
in {FStar_Syntax_Syntax.n = t1.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = uu___122_7173.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___122_7173.FStar_Syntax_Syntax.vars}))
in (bind uu____7164 (fun uu____7189 -> (match (uu____7189) with
| (t2, ctrl1) -> begin
(maybe_continue ctrl1 t2 (fun t3 -> (

let uu____7212 = (

let uu____7213 = (FStar_Syntax_Subst.compress t3)
in uu____7213.FStar_Syntax_Syntax.n)
in (match (uu____7212) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____7246 = (ctrl_tac_fold f env ctrl1 hd1)
in (bind uu____7246 (fun uu____7271 -> (match (uu____7271) with
| (hd2, ctrl2) -> begin
(

let ctrl3 = (keep_going ctrl2)
in (

let uu____7287 = (ctrl_tac_fold_args f env ctrl3 args)
in (bind uu____7287 (fun uu____7314 -> (match (uu____7314) with
| (args1, ctrl4) -> begin
(ret (((

let uu___120_7344 = t3
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app (((hd2), (args1))); FStar_Syntax_Syntax.pos = uu___120_7344.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___120_7344.FStar_Syntax_Syntax.vars})), (ctrl4)))
end)))))
end))))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t4, k) -> begin
(

let uu____7380 = (FStar_Syntax_Subst.open_term bs t4)
in (match (uu____7380) with
| (bs1, t') -> begin
(

let uu____7395 = (

let uu____7402 = (FStar_TypeChecker_Env.push_binders env bs1)
in (ctrl_tac_fold f uu____7402 ctrl1 t'))
in (bind uu____7395 (fun uu____7420 -> (match (uu____7420) with
| (t'', ctrl2) -> begin
(

let uu____7435 = (

let uu____7442 = (

let uu___121_7445 = t4
in (

let uu____7448 = (

let uu____7449 = (

let uu____7466 = (FStar_Syntax_Subst.close_binders bs1)
in (

let uu____7473 = (FStar_Syntax_Subst.close bs1 t'')
in ((uu____7466), (uu____7473), (k))))
in FStar_Syntax_Syntax.Tm_abs (uu____7449))
in {FStar_Syntax_Syntax.n = uu____7448; FStar_Syntax_Syntax.pos = uu___121_7445.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___121_7445.FStar_Syntax_Syntax.vars}))
in ((uu____7442), (ctrl2)))
in (ret uu____7435))
end))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(ret ((t3), (ctrl1)))
end
| uu____7520 -> begin
(ret ((t3), (ctrl1)))
end))))
end))))))))))
and ctrl_tac_fold_args : (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term ctrl_tac)  ->  env  ->  ctrl  ->  FStar_Syntax_Syntax.arg Prims.list  ->  FStar_Syntax_Syntax.arg Prims.list ctrl_tac = (fun f env ctrl ts -> (match (ts) with
| [] -> begin
(ret (([]), (ctrl)))
end
| ((t, q))::ts1 -> begin
(

let uu____7563 = (ctrl_tac_fold f env ctrl t)
in (bind uu____7563 (fun uu____7587 -> (match (uu____7587) with
| (t1, ctrl1) -> begin
(

let uu____7602 = (ctrl_tac_fold_args f env ctrl1 ts1)
in (bind uu____7602 (fun uu____7629 -> (match (uu____7629) with
| (ts2, ctrl2) -> begin
(ret (((((t1), (q)))::ts2), (ctrl2)))
end))))
end))))
end))


let rewrite_rec : FStar_Tactics_Types.proofstate  ->  (FStar_Syntax_Syntax.term  ->  rewrite_result ctrl_tac)  ->  unit tac  ->  FStar_Options.optionstate  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term ctrl_tac = (fun ps ctrl rewriter opts env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let uu____7711 = (

let uu____7718 = (add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true opts)
in (bind uu____7718 (fun uu____7727 -> (

let uu____7728 = (ctrl t1)
in (bind uu____7728 (fun res -> (

let uu____7751 = (trivial ())
in (bind uu____7751 (fun uu____7759 -> (ret res))))))))))
in (bind uu____7711 (fun uu____7775 -> (match (uu____7775) with
| (should_rewrite, ctrl1) -> begin
(match ((not (should_rewrite))) with
| true -> begin
(ret ((t1), (ctrl1)))
end
| uu____7798 -> begin
(

let uu____7799 = (FStar_TypeChecker_TcTerm.tc_term env t1)
in (match (uu____7799) with
| (t2, lcomp, g) -> begin
(

let uu____7815 = ((

let uu____7818 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp)
in (not (uu____7818))) || (

let uu____7820 = (FStar_TypeChecker_Rel.is_trivial g)
in (not (uu____7820))))
in (match (uu____7815) with
| true -> begin
(ret ((t2), (globalStop)))
end
| uu____7831 -> begin
(

let typ = lcomp.FStar_Syntax_Syntax.res_typ
in (

let uu____7835 = (new_uvar "pointwise_rec" env typ)
in (bind uu____7835 (fun ut -> ((log ps (fun uu____7850 -> (

let uu____7851 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____7852 = (FStar_Syntax_Print.term_to_string ut)
in (FStar_Util.print2 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n" uu____7851 uu____7852)))));
(

let uu____7853 = (

let uu____7856 = (

let uu____7857 = (FStar_TypeChecker_TcTerm.universe_of env typ)
in (FStar_Syntax_Util.mk_eq2 uu____7857 typ t2 ut))
in (add_irrelevant_goal "rewrite_rec equation" env uu____7856 opts))
in (bind uu____7853 (fun uu____7864 -> (

let uu____7865 = (bind rewriter (fun uu____7879 -> (

let ut1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env ut)
in ((log ps (fun uu____7885 -> (

let uu____7886 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____7887 = (FStar_Syntax_Print.term_to_string ut1)
in (FStar_Util.print2 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n" uu____7886 uu____7887)))));
(ret ((ut1), (ctrl1)));
))))
in (focus uu____7865)))));
)))))
end))
end))
end)
end))))))


let topdown_rewrite : (FStar_Syntax_Syntax.term  ->  (Prims.bool * FStar_BigInt.t) tac)  ->  unit tac  ->  unit tac = (fun ctrl rewriter -> (bind get (fun ps -> (

let uu____7935 = (match (ps.FStar_Tactics_Types.goals) with
| (g)::gs -> begin
((g), (gs))
end
| [] -> begin
(failwith "Pointwise: no goals")
end)
in (match (uu____7935) with
| (g, gs) -> begin
(

let gt1 = g.FStar_Tactics_Types.goal_ty
in ((log ps (fun uu____7972 -> (

let uu____7973 = (FStar_Syntax_Print.term_to_string gt1)
in (FStar_Util.print1 "Topdown_rewrite starting with %s\n" uu____7973))));
(bind dismiss_all (fun uu____7976 -> (

let uu____7977 = (ctrl_tac_fold (rewrite_rec ps ctrl rewriter g.FStar_Tactics_Types.opts) g.FStar_Tactics_Types.context keepGoing gt1)
in (bind uu____7977 (fun uu____7995 -> (match (uu____7995) with
| (gt', uu____8003) -> begin
((log ps (fun uu____8007 -> (

let uu____8008 = (FStar_Syntax_Print.term_to_string gt')
in (FStar_Util.print1 "Topdown_rewrite seems to have succeded with %s\n" uu____8008))));
(

let uu____8009 = (push_goals gs)
in (bind uu____8009 (fun uu____8013 -> (add_goals (((

let uu___123_8015 = g
in {FStar_Tactics_Types.context = uu___123_8015.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___123_8015.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = gt'; FStar_Tactics_Types.opts = uu___123_8015.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___123_8015.FStar_Tactics_Types.is_guard}))::[])))));
)
end))))));
))
end)))))


let pointwise : FStar_Tactics_Types.direction  ->  unit tac  ->  unit tac = (fun d tau -> (bind get (fun ps -> (

let uu____8041 = (match (ps.FStar_Tactics_Types.goals) with
| (g)::gs -> begin
((g), (gs))
end
| [] -> begin
(failwith "Pointwise: no goals")
end)
in (match (uu____8041) with
| (g, gs) -> begin
(

let gt1 = g.FStar_Tactics_Types.goal_ty
in ((log ps (fun uu____8078 -> (

let uu____8079 = (FStar_Syntax_Print.term_to_string gt1)
in (FStar_Util.print1 "Pointwise starting with %s\n" uu____8079))));
(bind dismiss_all (fun uu____8082 -> (

let uu____8083 = (tac_fold_env d (pointwise_rec ps tau g.FStar_Tactics_Types.opts) g.FStar_Tactics_Types.context gt1)
in (bind uu____8083 (fun gt' -> ((log ps (fun uu____8093 -> (

let uu____8094 = (FStar_Syntax_Print.term_to_string gt')
in (FStar_Util.print1 "Pointwise seems to have succeded with %s\n" uu____8094))));
(

let uu____8095 = (push_goals gs)
in (bind uu____8095 (fun uu____8099 -> (add_goals (((

let uu___124_8101 = g
in {FStar_Tactics_Types.context = uu___124_8101.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___124_8101.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = gt'; FStar_Tactics_Types.opts = uu___124_8101.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___124_8101.FStar_Tactics_Types.is_guard}))::[])))));
))))));
))
end)))))


let trefl : unit  ->  unit tac = (fun uu____8108 -> (

let uu____8111 = (cur_goal ())
in (bind uu____8111 (fun g -> (

let uu____8129 = (FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty)
in (match (uu____8129) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____8141 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____8141) with
| (hd1, args) -> begin
(

let uu____8174 = (

let uu____8185 = (

let uu____8186 = (FStar_Syntax_Util.un_uinst hd1)
in uu____8186.FStar_Syntax_Syntax.n)
in ((uu____8185), (args)))
in (match (uu____8174) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____8198)::((l, uu____8200))::((r, uu____8202))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid) -> begin
(

let uu____8229 = (do_unify g.FStar_Tactics_Types.context l r)
in (bind uu____8229 (fun b -> (match ((not (b))) with
| true -> begin
(

let uu____8238 = (tts g.FStar_Tactics_Types.context l)
in (

let uu____8239 = (tts g.FStar_Tactics_Types.context r)
in (fail2 "trefl: not a trivial equality (%s vs %s)" uu____8238 uu____8239)))
end
| uu____8240 -> begin
(solve g FStar_Syntax_Util.exp_unit)
end))))
end
| (hd2, uu____8242) -> begin
(

let uu____8255 = (tts g.FStar_Tactics_Types.context t)
in (fail1 "trefl: not an equality (%s)" uu____8255))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
(fail "not an irrelevant goal")
end))))))


let dup : unit  ->  unit tac = (fun uu____8264 -> (

let uu____8267 = (cur_goal ())
in (bind uu____8267 (fun g -> (

let uu____8273 = (new_uvar "dup" g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (bind uu____8273 (fun u -> (

let g' = (

let uu___125_8280 = g
in {FStar_Tactics_Types.context = uu___125_8280.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = u; FStar_Tactics_Types.goal_ty = uu___125_8280.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___125_8280.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___125_8280.FStar_Tactics_Types.is_guard})
in (bind __dismiss (fun uu____8283 -> (

let uu____8284 = (

let uu____8287 = (

let uu____8288 = (FStar_TypeChecker_TcTerm.universe_of g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (FStar_Syntax_Util.mk_eq2 uu____8288 g.FStar_Tactics_Types.goal_ty u g.FStar_Tactics_Types.witness))
in (add_irrelevant_goal "dup equation" g.FStar_Tactics_Types.context uu____8287 g.FStar_Tactics_Types.opts))
in (bind uu____8284 (fun uu____8291 -> (

let uu____8292 = (add_goals ((g')::[]))
in (bind uu____8292 (fun uu____8296 -> (ret ())))))))))))))))))


let flip : unit  ->  unit tac = (fun uu____8303 -> (bind get (fun ps -> (match (ps.FStar_Tactics_Types.goals) with
| (g1)::(g2)::gs -> begin
(set (

let uu___126_8320 = ps
in {FStar_Tactics_Types.main_context = uu___126_8320.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___126_8320.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___126_8320.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (g2)::(g1)::gs; FStar_Tactics_Types.smt_goals = uu___126_8320.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___126_8320.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___126_8320.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___126_8320.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___126_8320.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___126_8320.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___126_8320.FStar_Tactics_Types.freshness}))
end
| uu____8321 -> begin
(fail "flip: less than 2 goals")
end))))


let later : unit  ->  unit tac = (fun uu____8330 -> (bind get (fun ps -> (match (ps.FStar_Tactics_Types.goals) with
| [] -> begin
(ret ())
end
| (g)::gs -> begin
(set (

let uu___127_8343 = ps
in {FStar_Tactics_Types.main_context = uu___127_8343.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___127_8343.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___127_8343.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append gs ((g)::[])); FStar_Tactics_Types.smt_goals = uu___127_8343.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___127_8343.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___127_8343.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___127_8343.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___127_8343.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___127_8343.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___127_8343.FStar_Tactics_Types.freshness}))
end))))


let qed : unit  ->  unit tac = (fun uu____8350 -> (bind get (fun ps -> (match (ps.FStar_Tactics_Types.goals) with
| [] -> begin
(ret ())
end
| uu____8357 -> begin
(fail "Not done!")
end))))


let cases : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac = (fun t -> (

let uu____8377 = (

let uu____8384 = (cur_goal ())
in (bind uu____8384 (fun g -> (

let uu____8394 = (__tc g.FStar_Tactics_Types.context t)
in (bind uu____8394 (fun uu____8430 -> (match (uu____8430) with
| (t1, typ, guard) -> begin
(

let uu____8446 = (FStar_Syntax_Util.head_and_args typ)
in (match (uu____8446) with
| (hd1, args) -> begin
(

let uu____8489 = (

let uu____8502 = (

let uu____8503 = (FStar_Syntax_Util.un_uinst hd1)
in uu____8503.FStar_Syntax_Syntax.n)
in ((uu____8502), (args)))
in (match (uu____8489) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____8522))::((q, uu____8524))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid) -> begin
(

let v_p = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p)
in (

let v_q = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None q)
in (

let g1 = (

let uu___128_8562 = g
in (

let uu____8563 = (FStar_TypeChecker_Env.push_bv g.FStar_Tactics_Types.context v_p)
in {FStar_Tactics_Types.context = uu____8563; FStar_Tactics_Types.witness = uu___128_8562.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___128_8562.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___128_8562.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___128_8562.FStar_Tactics_Types.is_guard}))
in (

let g2 = (

let uu___129_8565 = g
in (

let uu____8566 = (FStar_TypeChecker_Env.push_bv g.FStar_Tactics_Types.context v_q)
in {FStar_Tactics_Types.context = uu____8566; FStar_Tactics_Types.witness = uu___129_8565.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___129_8565.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___129_8565.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___129_8565.FStar_Tactics_Types.is_guard}))
in (bind __dismiss (fun uu____8573 -> (

let uu____8574 = (add_goals ((g1)::(g2)::[]))
in (bind uu____8574 (fun uu____8583 -> (

let uu____8584 = (

let uu____8589 = (FStar_Syntax_Syntax.bv_to_name v_p)
in (

let uu____8590 = (FStar_Syntax_Syntax.bv_to_name v_q)
in ((uu____8589), (uu____8590))))
in (ret uu____8584)))))))))))
end
| uu____8595 -> begin
(

let uu____8608 = (tts g.FStar_Tactics_Types.context typ)
in (fail1 "Not a disjunction: %s" uu____8608))
end))
end))
end)))))))
in (FStar_All.pipe_left (wrap_err "cases") uu____8377)))


let set_options : Prims.string  ->  unit tac = (fun s -> (

let uu____8638 = (cur_goal ())
in (bind uu____8638 (fun g -> ((FStar_Options.push ());
(

let uu____8651 = (FStar_Util.smap_copy g.FStar_Tactics_Types.opts)
in (FStar_Options.set uu____8651));
(

let res = (FStar_Options.set_options FStar_Options.Set s)
in (

let opts' = (FStar_Options.peek ())
in ((FStar_Options.pop ());
(match (res) with
| FStar_Getopt.Success -> begin
(

let g' = (

let uu___130_8658 = g
in {FStar_Tactics_Types.context = uu___130_8658.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___130_8658.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___130_8658.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = opts'; FStar_Tactics_Types.is_guard = uu___130_8658.FStar_Tactics_Types.is_guard})
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


let top_env : unit  ->  env tac = (fun uu____8666 -> (bind get (fun ps -> (FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context))))


let cur_env : unit  ->  env tac = (fun uu____8679 -> (

let uu____8682 = (cur_goal ())
in (bind uu____8682 (fun g -> (FStar_All.pipe_left ret g.FStar_Tactics_Types.context)))))


let cur_goal' : unit  ->  FStar_Syntax_Syntax.term tac = (fun uu____8695 -> (

let uu____8698 = (cur_goal ())
in (bind uu____8698 (fun g -> (FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)))))


let cur_witness : unit  ->  FStar_Syntax_Syntax.term tac = (fun uu____8711 -> (

let uu____8714 = (cur_goal ())
in (bind uu____8714 (fun g -> (FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)))))


let unquote : FStar_Reflection_Data.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun ty tm -> (

let uu____8735 = (

let uu____8738 = (cur_goal ())
in (bind uu____8738 (fun goal -> (

let env = (FStar_TypeChecker_Env.set_expected_typ goal.FStar_Tactics_Types.context ty)
in (

let uu____8746 = (__tc env tm)
in (bind uu____8746 (fun uu____8766 -> (match (uu____8766) with
| (tm1, typ, guard) -> begin
(

let uu____8778 = (proc_guard "unquote" env guard goal.FStar_Tactics_Types.opts)
in (bind uu____8778 (fun uu____8782 -> (ret tm1))))
end))))))))
in (FStar_All.pipe_left (wrap_err "unquote") uu____8735)))


let uvar_env : env  ->  FStar_Reflection_Data.typ FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term tac = (fun env ty -> (

let uu____8805 = (match (ty) with
| FStar_Pervasives_Native.Some (ty1) -> begin
(ret ty1)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8811 = (

let uu____8812 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8812))
in (new_uvar "uvar_env.2" env uu____8811))
end)
in (bind uu____8805 (fun typ -> (

let uu____8824 = (new_uvar "uvar_env" env typ)
in (bind uu____8824 (fun t -> (ret t))))))))


let unshelve : FStar_Syntax_Syntax.term  ->  unit tac = (fun t -> (

let uu____8838 = (bind get (fun ps -> (

let env = ps.FStar_Tactics_Types.main_context
in (

let opts = (match (ps.FStar_Tactics_Types.goals) with
| (g)::uu____8855 -> begin
g.FStar_Tactics_Types.opts
end
| uu____8858 -> begin
(FStar_Options.peek ())
end)
in (

let uu____8861 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____8861) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (ctx_uvar); FStar_Syntax_Syntax.pos = uu____8879; FStar_Syntax_Syntax.vars = uu____8880}, uu____8881) -> begin
(

let env1 = (

let uu___131_8903 = env
in {FStar_TypeChecker_Env.solver = uu___131_8903.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___131_8903.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___131_8903.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_TypeChecker_Env.gamma_sig = uu___131_8903.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___131_8903.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___131_8903.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___131_8903.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___131_8903.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___131_8903.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___131_8903.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___131_8903.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___131_8903.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___131_8903.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___131_8903.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___131_8903.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___131_8903.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___131_8903.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___131_8903.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___131_8903.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___131_8903.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___131_8903.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___131_8903.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___131_8903.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___131_8903.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___131_8903.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___131_8903.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___131_8903.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___131_8903.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___131_8903.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___131_8903.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___131_8903.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___131_8903.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___131_8903.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___131_8903.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___131_8903.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___131_8903.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___131_8903.FStar_TypeChecker_Env.dep_graph})
in (

let uu____8904 = (

let uu____8907 = (

let uu____8908 = (bnorm env1 t)
in (

let uu____8909 = (bnorm env1 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in {FStar_Tactics_Types.context = env1; FStar_Tactics_Types.witness = uu____8908; FStar_Tactics_Types.goal_ty = uu____8909; FStar_Tactics_Types.opts = opts; FStar_Tactics_Types.is_guard = false}))
in (uu____8907)::[])
in (add_goals uu____8904)))
end
| uu____8910 -> begin
(fail "not a uvar")
end))))))
in (FStar_All.pipe_left (wrap_err "unshelve") uu____8838)))


let unify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun t1 t2 -> (bind get (fun ps -> (do_unify ps.FStar_Tactics_Types.main_context t1 t2))))


let launch_process : Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string tac = (fun prog args input -> (bind idtac (fun uu____8967 -> (

let uu____8968 = (FStar_Options.unsafe_tactic_exec ())
in (match (uu____8968) with
| true -> begin
(

let s = (FStar_Util.launch_process true "tactic_launch" prog args input (fun uu____8974 uu____8975 -> false))
in (ret s))
end
| uu____8976 -> begin
(fail "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
end)))))


let fresh_bv_named : Prims.string  ->  FStar_Reflection_Data.typ  ->  FStar_Syntax_Syntax.bv tac = (fun nm t -> (bind idtac (fun uu____8993 -> (

let uu____8994 = (FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t)
in (ret uu____8994)))))


let change : FStar_Reflection_Data.typ  ->  unit tac = (fun ty -> (

let uu____9004 = (mlog (fun uu____9009 -> (

let uu____9010 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.print1 "change: ty = %s\n" uu____9010))) (fun uu____9013 -> (

let uu____9014 = (cur_goal ())
in (bind uu____9014 (fun g -> (

let uu____9020 = (__tc g.FStar_Tactics_Types.context ty)
in (bind uu____9020 (fun uu____9040 -> (match (uu____9040) with
| (ty1, uu____9050, guard) -> begin
(

let uu____9052 = (proc_guard "change" g.FStar_Tactics_Types.context guard g.FStar_Tactics_Types.opts)
in (bind uu____9052 (fun uu____9057 -> (

let uu____9058 = (do_unify g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty ty1)
in (bind uu____9058 (fun bb -> (match (bb) with
| true -> begin
(replace_cur (

let uu___132_9067 = g
in {FStar_Tactics_Types.context = uu___132_9067.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___132_9067.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = ty1; FStar_Tactics_Types.opts = uu___132_9067.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___132_9067.FStar_Tactics_Types.is_guard}))
end
| uu____9068 -> begin
(

let steps = (FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.UnfoldTac)::(FStar_TypeChecker_Normalize.Unmeta)::[]
in (

let ng = (normalize steps g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (

let nty = (normalize steps g.FStar_Tactics_Types.context ty1)
in (

let uu____9074 = (do_unify g.FStar_Tactics_Types.context ng nty)
in (bind uu____9074 (fun b -> (match (b) with
| true -> begin
(replace_cur (

let uu___133_9083 = g
in {FStar_Tactics_Types.context = uu___133_9083.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___133_9083.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = ty1; FStar_Tactics_Types.opts = uu___133_9083.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___133_9083.FStar_Tactics_Types.is_guard}))
end
| uu____9084 -> begin
(fail "not convertible")
end)))))))
end)))))))
end)))))))))
in (FStar_All.pipe_left (wrap_err "change") uu____9004)))


let rec last : 'a . 'a Prims.list  ->  'a = (fun l -> (match (l) with
| [] -> begin
(failwith "last: empty list")
end
| (x)::[] -> begin
x
end
| (uu____9105)::xs -> begin
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

let uu____9133 = (init xs)
in (x)::uu____9133)
end))


let rec inspect : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.term_view tac = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let t2 = (FStar_Syntax_Util.un_uinst t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t3, uu____9150) -> begin
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

let uu____9207 = (last args)
in (match (uu____9207) with
| (a, q) -> begin
(

let q' = (FStar_Reflection_Basic.inspect_aqual q)
in (

let uu____9229 = (

let uu____9230 = (

let uu____9235 = (

let uu____9236 = (

let uu____9241 = (init args)
in (FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9241))
in (uu____9236 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in ((uu____9235), (((a), (q')))))
in FStar_Reflection_Data.Tv_App (uu____9230))
in (FStar_All.pipe_left ret uu____9229)))
end))
end
| FStar_Syntax_Syntax.Tm_abs ([], uu____9252, uu____9253) -> begin
(failwith "inspect: empty arguments on Tm_abs")
end
| FStar_Syntax_Syntax.Tm_abs (bs, t3, k) -> begin
(

let uu____9297 = (FStar_Syntax_Subst.open_term bs t3)
in (match (uu____9297) with
| (bs1, t4) -> begin
(match (bs1) with
| [] -> begin
(failwith "impossible")
end
| (b)::bs2 -> begin
(

let uu____9330 = (

let uu____9331 = (

let uu____9336 = (FStar_Syntax_Util.abs bs2 t4 k)
in ((b), (uu____9336)))
in FStar_Reflection_Data.Tv_Abs (uu____9331))
in (FStar_All.pipe_left ret uu____9330))
end)
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____9339) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type (())))
end
| FStar_Syntax_Syntax.Tm_arrow ([], k) -> begin
(failwith "inspect: empty binders on arrow")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____9359) -> begin
(

let uu____9372 = (FStar_Syntax_Util.arrow_one t2)
in (match (uu____9372) with
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

let uu____9402 = (FStar_Syntax_Subst.open_term ((b)::[]) t3)
in (match (uu____9402) with
| (b', t4) -> begin
(

let b1 = (match (b') with
| (b'1)::[] -> begin
b'1
end
| uu____9441 -> begin
(failwith "impossible")
end)
in (FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Refine ((((FStar_Pervasives_Native.fst b1)), (t4))))))
end)))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____9449 = (

let uu____9450 = (FStar_Reflection_Basic.inspect_const c)
in FStar_Reflection_Data.Tv_Const (uu____9450))
in (FStar_All.pipe_left ret uu____9449))
end
| FStar_Syntax_Syntax.Tm_uvar (ctx_u) -> begin
(

let uu____9454 = (

let uu____9455 = (

let uu____9464 = (

let uu____9465 = (FStar_Syntax_Unionfind.uvar_id ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_BigInt.of_int_fs uu____9465))
in ((uu____9464), (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma), (ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders), (ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)))
in FStar_Reflection_Data.Tv_Uvar (uu____9455))
in (FStar_All.pipe_left ret uu____9454))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), t21) -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| uu____9488 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____9491) -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv) -> begin
(

let b = (FStar_Syntax_Syntax.mk_binder bv)
in (

let uu____9496 = (FStar_Syntax_Subst.open_term ((b)::[]) t21)
in (match (uu____9496) with
| (bs, t22) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____9535 -> begin
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
| uu____9562 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____9565) -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv) -> begin
(

let uu____9569 = (FStar_Syntax_Subst.open_let_rec ((lb)::[]) t21)
in (match (uu____9569) with
| (lbs, t22) -> begin
(match (lbs) with
| (lb1)::[] -> begin
(match (lb1.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____9589) -> begin
(ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv1) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Let (((true), (bv1), (lb1.FStar_Syntax_Syntax.lbdef), (t22)))))
end)
end
| uu____9593 -> begin
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

let uu____9647 = (FStar_Reflection_Basic.inspect_const c)
in FStar_Reflection_Data.Pat_Constant (uu____9647))
end
| FStar_Syntax_Syntax.Pat_cons (fv, ps) -> begin
(

let uu____9666 = (

let uu____9673 = (FStar_List.map (fun uu____9685 -> (match (uu____9685) with
| (p1, uu____9693) -> begin
(inspect_pat p1)
end)) ps)
in ((fv), (uu____9673)))
in FStar_Reflection_Data.Pat_Cons (uu____9666))
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

let brs2 = (FStar_List.map (fun uu___65_9777 -> (match (uu___65_9777) with
| (pat, uu____9795, t4) -> begin
(

let uu____9809 = (inspect_pat pat)
in ((uu____9809), (t4)))
end)) brs1)
in (FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (((t3), (brs2))))))))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| uu____9816 -> begin
((

let uu____9818 = (

let uu____9823 = (

let uu____9824 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____9825 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "inspect: outside of expected syntax (%s, %s)\n" uu____9824 uu____9825)))
in ((FStar_Errors.Warning_CantInspect), (uu____9823)))
in (FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9818));
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown);
)
end))))


let pack : FStar_Reflection_Data.term_view  ->  FStar_Syntax_Syntax.term tac = (fun tv -> (match (tv) with
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____9838 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_left ret uu____9838))
end
| FStar_Reflection_Data.Tv_BVar (bv) -> begin
(

let uu____9842 = (FStar_Syntax_Syntax.bv_to_tm bv)
in (FStar_All.pipe_left ret uu____9842))
end
| FStar_Reflection_Data.Tv_FVar (fv) -> begin
(

let uu____9846 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (FStar_All.pipe_left ret uu____9846))
end
| FStar_Reflection_Data.Tv_App (l, (r, q)) -> begin
(

let q' = (FStar_Reflection_Basic.pack_aqual q)
in (

let uu____9853 = (FStar_Syntax_Util.mk_app l ((((r), (q')))::[]))
in (FStar_All.pipe_left ret uu____9853)))
end
| FStar_Reflection_Data.Tv_Abs (b, t) -> begin
(

let uu____9872 = (FStar_Syntax_Util.abs ((b)::[]) t FStar_Pervasives_Native.None)
in (FStar_All.pipe_left ret uu____9872))
end
| FStar_Reflection_Data.Tv_Arrow (b, c) -> begin
(

let uu____9885 = (FStar_Syntax_Util.arrow ((b)::[]) c)
in (FStar_All.pipe_left ret uu____9885))
end
| FStar_Reflection_Data.Tv_Type (()) -> begin
(FStar_All.pipe_left ret FStar_Syntax_Util.ktype)
end
| FStar_Reflection_Data.Tv_Refine (bv, t) -> begin
(

let uu____9900 = (FStar_Syntax_Util.refine bv t)
in (FStar_All.pipe_left ret uu____9900))
end
| FStar_Reflection_Data.Tv_Const (c) -> begin
(

let uu____9904 = (

let uu____9905 = (

let uu____9912 = (

let uu____9913 = (FStar_Reflection_Basic.pack_const c)
in FStar_Syntax_Syntax.Tm_constant (uu____9913))
in (FStar_Syntax_Syntax.mk uu____9912))
in (uu____9905 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_All.pipe_left ret uu____9904))
end
| FStar_Reflection_Data.Tv_Uvar (u, g, bs, t) -> begin
(

let uu____9923 = (

let uu____9924 = (FStar_BigInt.to_int_fs u)
in (FStar_Syntax_Util.uvar_from_id uu____9924 ((g), (bs), (t))))
in (FStar_All.pipe_left ret uu____9923))
end
| FStar_Reflection_Data.Tv_Let (false, bv, t1, t2) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 [] FStar_Range.dummyRange)
in (

let uu____9943 = (

let uu____9944 = (

let uu____9951 = (

let uu____9952 = (

let uu____9965 = (

let uu____9968 = (

let uu____9969 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____9969)::[])
in (FStar_Syntax_Subst.close uu____9968 t2))
in ((((false), ((lb)::[]))), (uu____9965)))
in FStar_Syntax_Syntax.Tm_let (uu____9952))
in (FStar_Syntax_Syntax.mk uu____9951))
in (uu____9944 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_All.pipe_left ret uu____9943)))
end
| FStar_Reflection_Data.Tv_Let (true, bv, t1, t2) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 [] FStar_Range.dummyRange)
in (

let uu____10003 = (FStar_Syntax_Subst.close_let_rec ((lb)::[]) t2)
in (match (uu____10003) with
| (lbs, body) -> begin
(

let uu____10018 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____10018))
end)))
end
| FStar_Reflection_Data.Tv_Match (t, brs) -> begin
(

let wrap = (fun v1 -> {FStar_Syntax_Syntax.v = v1; FStar_Syntax_Syntax.p = FStar_Range.dummyRange})
in (

let rec pack_pat = (fun p -> (match (p) with
| FStar_Reflection_Data.Pat_Constant (c) -> begin
(

let uu____10052 = (

let uu____10053 = (FStar_Reflection_Basic.pack_const c)
in FStar_Syntax_Syntax.Pat_constant (uu____10053))
in (FStar_All.pipe_left wrap uu____10052))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____10060 = (

let uu____10061 = (

let uu____10074 = (FStar_List.map (fun p1 -> (

let uu____10090 = (pack_pat p1)
in ((uu____10090), (false)))) ps)
in ((fv), (uu____10074)))
in FStar_Syntax_Syntax.Pat_cons (uu____10061))
in (FStar_All.pipe_left wrap uu____10060))
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

let brs1 = (FStar_List.map (fun uu___66_10136 -> (match (uu___66_10136) with
| (pat, t1) -> begin
(

let uu____10153 = (pack_pat pat)
in ((uu____10153), (FStar_Pervasives_Native.None), (t1)))
end)) brs)
in (

let brs2 = (FStar_List.map FStar_Syntax_Subst.close_branch brs1)
in (

let uu____10201 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((t), (brs2)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____10201))))))
end
| FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) -> begin
(

let uu____10229 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (((FStar_Util.Inl (t)), (tacopt))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____10229))
end
| FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) -> begin
(

let uu____10275 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (((FStar_Util.Inr (c)), (tacopt))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____10275))
end
| FStar_Reflection_Data.Tv_Unknown -> begin
(

let uu____10314 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____10314))
end))


let goal_of_goal_ty : env  ->  FStar_Reflection_Data.typ  ->  (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t) = (fun env typ -> (

let uu____10335 = (FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty" typ.FStar_Syntax_Syntax.pos env typ)
in (match (uu____10335) with
| (u, uu____10353, g_u) -> begin
(

let g = (

let uu____10368 = (FStar_Options.peek ())
in {FStar_Tactics_Types.context = env; FStar_Tactics_Types.witness = u; FStar_Tactics_Types.goal_ty = typ; FStar_Tactics_Types.opts = uu____10368; FStar_Tactics_Types.is_guard = false})
in ((g), (g_u)))
end)))


let proofstate_of_goal_ty : env  ->  FStar_Reflection_Data.typ  ->  (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term) = (fun env typ -> (

let uu____10383 = (goal_of_goal_ty env typ)
in (match (uu____10383) with
| (g, g_u) -> begin
(

let ps = {FStar_Tactics_Types.main_context = env; FStar_Tactics_Types.main_goal = g; FStar_Tactics_Types.all_implicits = g_u.FStar_TypeChecker_Env.implicits; FStar_Tactics_Types.goals = (g)::[]; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = (Prims.parse_int "0"); FStar_Tactics_Types.__dump = (fun ps msg -> (dump_proofstate ps msg)); FStar_Tactics_Types.psc = FStar_TypeChecker_Normalize.null_psc; FStar_Tactics_Types.entry_range = FStar_Range.dummyRange; FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT; FStar_Tactics_Types.freshness = (Prims.parse_int "0")}
in ((ps), (g.FStar_Tactics_Types.witness)))
end)))




