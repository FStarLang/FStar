
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

let uu____297 = (FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (FStar_Syntax_Util.un_squash uu____297))
in (match (uu____294) with
| FStar_Pervasives_Native.Some (t) -> begin
true
end
| uu____299 -> begin
false
end)))


let print : Prims.string  ->  unit tac = (fun msg -> ((tacprint msg);
(ret ());
))


let debug : Prims.string  ->  unit tac = (fun msg -> (bind get (fun ps -> ((

let uu____325 = (

let uu____326 = (FStar_Ident.string_of_lid ps.FStar_Tactics_Types.main_context.FStar_TypeChecker_Env.curmodule)
in (FStar_Options.debug_module uu____326))
in (match (uu____325) with
| true -> begin
(tacprint msg)
end
| uu____327 -> begin
()
end));
(ret ());
))))


let dump_goal : 'Auu____334 . 'Auu____334  ->  FStar_Tactics_Types.goal  ->  unit = (fun ps goal -> (

let uu____346 = (goal_to_string goal)
in (tacprint uu____346)))


let dump_cur : FStar_Tactics_Types.proofstate  ->  Prims.string  ->  unit = (fun ps msg -> (match (ps.FStar_Tactics_Types.goals) with
| [] -> begin
(tacprint1 "No more goals (%s)" msg)
end
| (h)::uu____358 -> begin
((tacprint1 "Current goal (%s):" msg);
(

let uu____362 = (FStar_List.hd ps.FStar_Tactics_Types.goals)
in (dump_goal ps uu____362));
)
end))


let ps_to_string : (Prims.string * FStar_Tactics_Types.proofstate)  ->  Prims.string = (fun uu____371 -> (match (uu____371) with
| (msg, ps) -> begin
(

let uu____378 = (

let uu____381 = (

let uu____382 = (FStar_Util.string_of_int ps.FStar_Tactics_Types.depth)
in (FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____382 msg))
in (

let uu____383 = (

let uu____386 = (

let uu____387 = (FStar_Range.string_of_range ps.FStar_Tactics_Types.entry_range)
in (FStar_Util.format1 "Location: %s\n" uu____387))
in (

let uu____388 = (

let uu____391 = (

let uu____392 = (FStar_Util.string_of_int (FStar_List.length ps.FStar_Tactics_Types.goals))
in (

let uu____393 = (

let uu____394 = (FStar_List.map goal_to_string ps.FStar_Tactics_Types.goals)
in (FStar_String.concat "\n" uu____394))
in (FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____392 uu____393)))
in (

let uu____397 = (

let uu____400 = (

let uu____401 = (FStar_Util.string_of_int (FStar_List.length ps.FStar_Tactics_Types.smt_goals))
in (

let uu____402 = (

let uu____403 = (FStar_List.map goal_to_string ps.FStar_Tactics_Types.smt_goals)
in (FStar_String.concat "\n" uu____403))
in (FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____401 uu____402)))
in (uu____400)::[])
in (uu____391)::uu____397))
in (uu____386)::uu____388))
in (uu____381)::uu____383))
in (FStar_String.concat "" uu____378))
end))


let goal_to_json : FStar_Tactics_Types.goal  ->  FStar_Util.json = (fun g -> (

let g_binders = (

let uu____412 = (FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context)
in (

let uu____413 = (

let uu____418 = (FStar_TypeChecker_Env.dsenv g.FStar_Tactics_Types.context)
in (FStar_Syntax_Print.binders_to_json uu____418))
in (FStar_All.pipe_right uu____412 uu____413)))
in (

let uu____419 = (

let uu____426 = (

let uu____433 = (

let uu____438 = (

let uu____439 = (

let uu____446 = (

let uu____451 = (

let uu____452 = (tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness)
in FStar_Util.JsonStr (uu____452))
in (("witness"), (uu____451)))
in (

let uu____453 = (

let uu____460 = (

let uu____465 = (

let uu____466 = (tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in FStar_Util.JsonStr (uu____466))
in (("type"), (uu____465)))
in (uu____460)::[])
in (uu____446)::uu____453))
in FStar_Util.JsonAssoc (uu____439))
in (("goal"), (uu____438)))
in (uu____433)::[])
in ((("hyps"), (g_binders)))::uu____426)
in FStar_Util.JsonAssoc (uu____419))))


let ps_to_json : (Prims.string * FStar_Tactics_Types.proofstate)  ->  FStar_Util.json = (fun uu____499 -> (match (uu____499) with
| (msg, ps) -> begin
(

let uu____506 = (

let uu____513 = (

let uu____520 = (

let uu____527 = (

let uu____534 = (

let uu____539 = (

let uu____540 = (FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals)
in FStar_Util.JsonList (uu____540))
in (("goals"), (uu____539)))
in (

let uu____543 = (

let uu____550 = (

let uu____555 = (

let uu____556 = (FStar_List.map goal_to_json ps.FStar_Tactics_Types.smt_goals)
in FStar_Util.JsonList (uu____556))
in (("smt-goals"), (uu____555)))
in (uu____550)::[])
in (uu____534)::uu____543))
in ((("depth"), (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth))))::uu____527)
in ((("label"), (FStar_Util.JsonStr (msg))))::uu____520)
in (

let uu____579 = (match ((Prims.op_disEquality ps.FStar_Tactics_Types.entry_range FStar_Range.dummyRange)) with
| true -> begin
(

let uu____592 = (

let uu____597 = (FStar_Range.json_of_def_range ps.FStar_Tactics_Types.entry_range)
in (("location"), (uu____597)))
in (uu____592)::[])
end
| uu____606 -> begin
[]
end)
in (FStar_List.append uu____513 uu____579)))
in FStar_Util.JsonAssoc (uu____506))
end))


let dump_proofstate : FStar_Tactics_Types.proofstate  ->  Prims.string  ->  unit = (fun ps msg -> (FStar_Options.with_saved_options (fun uu____627 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(FStar_Util.print_generic "proof-state" ps_to_string ps_to_json ((msg), (ps)));
))))


let print_proof_state1 : Prims.string  ->  unit tac = (fun msg -> (mk_tac (fun ps -> (

let psc = ps.FStar_Tactics_Types.psc
in (

let subst1 = (FStar_TypeChecker_Normalize.psc_subst psc)
in ((

let uu____650 = (FStar_Tactics_Types.subst_proof_state subst1 ps)
in (dump_cur uu____650 msg));
FStar_Tactics_Result.Success (((()), (ps)));
))))))


let print_proof_state : Prims.string  ->  unit tac = (fun msg -> (mk_tac (fun ps -> (

let psc = ps.FStar_Tactics_Types.psc
in (

let subst1 = (FStar_TypeChecker_Normalize.psc_subst psc)
in ((

let uu____668 = (FStar_Tactics_Types.subst_proof_state subst1 ps)
in (dump_proofstate uu____668 msg));
FStar_Tactics_Result.Success (((()), (ps)));
))))))


let tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let rec log : FStar_Tactics_Types.proofstate  ->  (unit  ->  unit)  ->  unit = (fun ps f -> (

let uu____701 = (FStar_ST.op_Bang tac_verb_dbg)
in (match (uu____701) with
| FStar_Pervasives_Native.None -> begin
((

let uu____732 = (

let uu____735 = (FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context (FStar_Options.Other ("TacVerbose")))
in FStar_Pervasives_Native.Some (uu____735))
in (FStar_ST.op_Colon_Equals tac_verb_dbg uu____732));
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

let uu____816 = (FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context (FStar_Options.Other ("TacFail")))
in (match (uu____816) with
| true -> begin
(dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg))
end
| uu____817 -> begin
()
end));
FStar_Tactics_Result.Failed (((msg), (ps)));
))))


let fail1 : 'Auu____824 . Prims.string  ->  Prims.string  ->  'Auu____824 tac = (fun msg x -> (

let uu____837 = (FStar_Util.format1 msg x)
in (fail uu____837)))


let fail2 : 'Auu____846 . Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____846 tac = (fun msg x y -> (

let uu____864 = (FStar_Util.format2 msg x y)
in (fail uu____864)))


let fail3 : 'Auu____875 . Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____875 tac = (fun msg x y z -> (

let uu____898 = (FStar_Util.format3 msg x y z)
in (fail uu____898)))


let fail4 : 'Auu____911 . Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____911 tac = (fun msg x y z w -> (

let uu____939 = (FStar_Util.format4 msg x y z w)
in (fail uu____939)))


let trytac' : 'a . 'a tac  ->  (Prims.string, 'a) FStar_Util.either tac = (fun t -> (mk_tac (fun ps -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____972 = (run t ps)
in (match (uu____972) with
| FStar_Tactics_Result.Success (a, q) -> begin
((FStar_Syntax_Unionfind.commit tx);
FStar_Tactics_Result.Success (((FStar_Util.Inr (a)), (q)));
)
end
| FStar_Tactics_Result.Failed (m, q) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(

let ps1 = (

let uu___67_996 = ps
in {FStar_Tactics_Types.main_context = uu___67_996.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___67_996.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___67_996.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___67_996.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___67_996.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___67_996.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___67_996.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___67_996.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___67_996.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___67_996.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = q.FStar_Tactics_Types.freshness})
in FStar_Tactics_Result.Success (((FStar_Util.Inl (m)), (ps1))));
)
end))))))


let trytac : 'a . 'a tac  ->  'a FStar_Pervasives_Native.option tac = (fun t -> (

let uu____1023 = (trytac' t)
in (bind uu____1023 (fun r -> (match (r) with
| FStar_Util.Inr (v1) -> begin
(ret (FStar_Pervasives_Native.Some (v1)))
end
| FStar_Util.Inl (uu____1050) -> begin
(ret FStar_Pervasives_Native.None)
end)))))


let trytac_exn : 'a . 'a tac  ->  'a FStar_Pervasives_Native.option tac = (fun t -> (mk_tac (fun ps -> (FStar_All.try_with (fun uu___69_1081 -> (match (()) with
| () -> begin
(

let uu____1086 = (trytac t)
in (run uu____1086 ps))
end)) (fun uu___68_1097 -> (match (uu___68_1097) with
| FStar_Errors.Err (uu____1102, msg) -> begin
((log ps (fun uu____1106 -> (FStar_Util.print1 "trytac_exn error: (%s)" msg)));
FStar_Tactics_Result.Success (((FStar_Pervasives_Native.None), (ps)));
)
end
| FStar_Errors.Error (uu____1111, msg, uu____1113) -> begin
((log ps (fun uu____1116 -> (FStar_Util.print1 "trytac_exn error: (%s)" msg)));
FStar_Tactics_Result.Success (((FStar_Pervasives_Native.None), (ps)));
)
end))))))


let wrap_err : 'a . Prims.string  ->  'a tac  ->  'a tac = (fun pref t -> (mk_tac (fun ps -> (

let uu____1149 = (run t ps)
in (match (uu____1149) with
| FStar_Tactics_Result.Success (a, q) -> begin
FStar_Tactics_Result.Success (((a), (q)))
end
| FStar_Tactics_Result.Failed (msg, q) -> begin
FStar_Tactics_Result.Failed ((((Prims.strcat pref (Prims.strcat ": " msg))), (q)))
end)))))


let set : FStar_Tactics_Types.proofstate  ->  unit tac = (fun p -> (mk_tac (fun uu____1168 -> FStar_Tactics_Result.Success (((()), (p))))))


let __do_unify : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun env t1 t2 -> ((

let uu____1189 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1189) with
| true -> begin
(

let uu____1190 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1191 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1190 uu____1191)))
end
| uu____1192 -> begin
()
end));
(FStar_All.try_with (fun uu___71_1198 -> (match (()) with
| () -> begin
(

let res = (FStar_TypeChecker_Rel.teq_nosmt env t1 t2)
in ((

let uu____1203 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1203) with
| true -> begin
(

let uu____1204 = (FStar_Util.string_of_bool res)
in (

let uu____1205 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1206 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1204 uu____1205 uu____1206))))
end
| uu____1207 -> begin
()
end));
(ret res);
))
end)) (fun uu___70_1211 -> (match (uu___70_1211) with
| FStar_Errors.Err (uu____1214, msg) -> begin
(mlog (fun uu____1217 -> (FStar_Util.print1 ">> do_unify error, (%s)\n" msg)) (fun uu____1219 -> (ret false)))
end
| FStar_Errors.Error (uu____1220, msg, r) -> begin
(mlog (fun uu____1225 -> (

let uu____1226 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg uu____1226))) (fun uu____1228 -> (ret false)))
end)));
))


let do_unify : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun env t1 t2 -> (bind idtac (fun uu____1251 -> ((

let uu____1253 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1253) with
| true -> begin
((FStar_Options.push ());
(

let uu____1255 = (FStar_Options.set_options FStar_Options.Set "--debug_level Rel --debug_level RelCheck")
in ());
)
end
| uu____1256 -> begin
()
end));
(

let uu____1257 = (

let uu____1260 = (__do_unify env t1 t2)
in (bind uu____1260 (fun b -> (match ((not (b))) with
| true -> begin
(

let t11 = (FStar_TypeChecker_Normalize.normalize [] env t1)
in (

let t21 = (FStar_TypeChecker_Normalize.normalize [] env t2)
in (__do_unify env t11 t21)))
end
| uu____1271 -> begin
(ret b)
end))))
in (bind uu____1257 (fun r -> ((

let uu____1276 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1276) with
| true -> begin
(FStar_Options.pop ())
end
| uu____1277 -> begin
()
end));
(ret r);
))));
))))


let trysolve : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun goal solution -> (do_unify goal.FStar_Tactics_Types.context solution goal.FStar_Tactics_Types.witness))


let __dismiss : unit tac = (bind get (fun p -> (

let uu____1297 = (

let uu___72_1298 = p
in (

let uu____1299 = (FStar_List.tl p.FStar_Tactics_Types.goals)
in {FStar_Tactics_Types.main_context = uu___72_1298.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___72_1298.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___72_1298.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu____1299; FStar_Tactics_Types.smt_goals = uu___72_1298.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___72_1298.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___72_1298.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___72_1298.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___72_1298.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___72_1298.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___72_1298.FStar_Tactics_Types.freshness}))
in (set uu____1297))))


let dismiss : unit  ->  unit tac = (fun uu____1308 -> (bind get (fun p -> (match (p.FStar_Tactics_Types.goals) with
| [] -> begin
(fail "dismiss: no more goals")
end
| uu____1315 -> begin
__dismiss
end))))


let solve : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun goal solution -> (

let uu____1332 = (trysolve goal solution)
in (bind uu____1332 (fun b -> (match (b) with
| true -> begin
__dismiss
end
| uu____1339 -> begin
(

let uu____1340 = (

let uu____1341 = (tts goal.FStar_Tactics_Types.context solution)
in (

let uu____1342 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.witness)
in (

let uu____1343 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (FStar_Util.format3 "%s does not solve %s : %s" uu____1341 uu____1342 uu____1343))))
in (fail uu____1340))
end)))))


let dismiss_all : unit tac = (bind get (fun p -> (set (

let uu___73_1350 = p
in {FStar_Tactics_Types.main_context = uu___73_1350.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___73_1350.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___73_1350.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = []; FStar_Tactics_Types.smt_goals = uu___73_1350.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___73_1350.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___73_1350.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___73_1350.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___73_1350.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___73_1350.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___73_1350.FStar_Tactics_Types.freshness}))))


let nwarn : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let check_valid_goal : FStar_Tactics_Types.goal  ->  unit = (fun g -> (

let uu____1369 = (FStar_Options.defensive ())
in (match (uu____1369) with
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

let uu____1385 = (FStar_TypeChecker_Env.pop_bv e)
in (match (uu____1385) with
| FStar_Pervasives_Native.None -> begin
b3
end
| FStar_Pervasives_Native.Some (bv, e1) -> begin
(

let b4 = (b3 && (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort))
in (aux b4 e1))
end)))
in (

let uu____1403 = ((

let uu____1406 = (aux b2 env)
in (not (uu____1406))) && (

let uu____1408 = (FStar_ST.op_Bang nwarn)
in (uu____1408 < (Prims.parse_int "5"))))
in (match (uu____1403) with
| true -> begin
((

let uu____1433 = (

let uu____1438 = (

let uu____1439 = (goal_to_string g)
in (FStar_Util.format1 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n" uu____1439))
in ((FStar_Errors.Warning_IllFormedGoal), (uu____1438)))
in (FStar_Errors.log_issue g.FStar_Tactics_Types.goal_ty.FStar_Syntax_Syntax.pos uu____1433));
(

let uu____1440 = (

let uu____1441 = (FStar_ST.op_Bang nwarn)
in (uu____1441 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals nwarn uu____1440));
)
end
| uu____1488 -> begin
()
end)))))))
end
| uu____1489 -> begin
()
end)))


let add_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___74_1509 = p
in {FStar_Tactics_Types.main_context = uu___74_1509.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___74_1509.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___74_1509.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append gs p.FStar_Tactics_Types.goals); FStar_Tactics_Types.smt_goals = uu___74_1509.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___74_1509.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___74_1509.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___74_1509.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___74_1509.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___74_1509.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___74_1509.FStar_Tactics_Types.freshness}));
))))


let add_smt_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___75_1529 = p
in {FStar_Tactics_Types.main_context = uu___75_1529.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___75_1529.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___75_1529.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___75_1529.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = (FStar_List.append gs p.FStar_Tactics_Types.smt_goals); FStar_Tactics_Types.depth = uu___75_1529.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___75_1529.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___75_1529.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___75_1529.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___75_1529.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___75_1529.FStar_Tactics_Types.freshness}));
))))


let push_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___76_1549 = p
in {FStar_Tactics_Types.main_context = uu___76_1549.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___76_1549.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___76_1549.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append p.FStar_Tactics_Types.goals gs); FStar_Tactics_Types.smt_goals = uu___76_1549.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___76_1549.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___76_1549.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___76_1549.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___76_1549.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___76_1549.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___76_1549.FStar_Tactics_Types.freshness}));
))))


let push_smt_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___77_1569 = p
in {FStar_Tactics_Types.main_context = uu___77_1569.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___77_1569.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___77_1569.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___77_1569.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = (FStar_List.append p.FStar_Tactics_Types.smt_goals gs); FStar_Tactics_Types.depth = uu___77_1569.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___77_1569.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___77_1569.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___77_1569.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___77_1569.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___77_1569.FStar_Tactics_Types.freshness}));
))))


let replace_cur : FStar_Tactics_Types.goal  ->  unit tac = (fun g -> (bind __dismiss (fun uu____1580 -> (add_goals ((g)::[])))))


let add_implicits : implicits  ->  unit tac = (fun i -> (bind get (fun p -> (set (

let uu___78_1594 = p
in {FStar_Tactics_Types.main_context = uu___78_1594.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___78_1594.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = (FStar_List.append i p.FStar_Tactics_Types.all_implicits); FStar_Tactics_Types.goals = uu___78_1594.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___78_1594.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___78_1594.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___78_1594.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___78_1594.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___78_1594.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___78_1594.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___78_1594.FStar_Tactics_Types.freshness})))))


let new_uvar : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  FStar_Syntax_Syntax.term tac = (fun reason env typ -> (

let uu____1624 = (FStar_TypeChecker_Util.new_implicit_var reason typ.FStar_Syntax_Syntax.pos env typ)
in (match (uu____1624) with
| (u, uu____1640, g_u) -> begin
(

let uu____1654 = (add_implicits g_u.FStar_TypeChecker_Env.implicits)
in (bind uu____1654 (fun uu____1658 -> (ret u))))
end)))


let is_true : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1664 = (FStar_Syntax_Util.un_squash t)
in (match (uu____1664) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____1668 = (

let uu____1669 = (FStar_Syntax_Subst.compress t')
in uu____1669.FStar_Syntax_Syntax.n)
in (match (uu____1668) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)
end
| uu____1673 -> begin
false
end))
end
| uu____1674 -> begin
false
end)))


let is_false : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1682 = (FStar_Syntax_Util.un_squash t)
in (match (uu____1682) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____1686 = (

let uu____1687 = (FStar_Syntax_Subst.compress t')
in uu____1687.FStar_Syntax_Syntax.n)
in (match (uu____1686) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid)
end
| uu____1691 -> begin
false
end))
end
| uu____1692 -> begin
false
end)))


let cur_goal : unit  ->  FStar_Tactics_Types.goal tac = (fun uu____1701 -> (bind get (fun p -> (match (p.FStar_Tactics_Types.goals) with
| [] -> begin
(fail "No more goals (1)")
end
| (hd1)::tl1 -> begin
(ret hd1)
end))))


let tadmit : unit  ->  unit tac = (fun uu____1718 -> (

let uu____1721 = (

let uu____1724 = (cur_goal ())
in (bind uu____1724 (fun g -> ((

let uu____1731 = (

let uu____1736 = (

let uu____1737 = (goal_to_string g)
in (FStar_Util.format1 "Tactics admitted goal <%s>\n\n" uu____1737))
in ((FStar_Errors.Warning_TacAdmit), (uu____1736)))
in (FStar_Errors.log_issue g.FStar_Tactics_Types.goal_ty.FStar_Syntax_Syntax.pos uu____1731));
(solve g FStar_Syntax_Util.exp_unit);
))))
in (FStar_All.pipe_left (wrap_err "tadmit") uu____1721)))


let fresh : unit  ->  FStar_BigInt.t tac = (fun uu____1748 -> (bind get (fun ps -> (

let n1 = ps.FStar_Tactics_Types.freshness
in (

let ps1 = (

let uu___79_1758 = ps
in {FStar_Tactics_Types.main_context = uu___79_1758.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___79_1758.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___79_1758.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___79_1758.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___79_1758.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___79_1758.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___79_1758.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___79_1758.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___79_1758.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___79_1758.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))})
in (

let uu____1759 = (set ps1)
in (bind uu____1759 (fun uu____1764 -> (

let uu____1765 = (FStar_BigInt.of_int_fs n1)
in (ret uu____1765))))))))))


let ngoals : unit  ->  FStar_BigInt.t tac = (fun uu____1772 -> (bind get (fun ps -> (

let n1 = (FStar_List.length ps.FStar_Tactics_Types.goals)
in (

let uu____1780 = (FStar_BigInt.of_int_fs n1)
in (ret uu____1780))))))


let ngoals_smt : unit  ->  FStar_BigInt.t tac = (fun uu____1793 -> (bind get (fun ps -> (

let n1 = (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
in (

let uu____1801 = (FStar_BigInt.of_int_fs n1)
in (ret uu____1801))))))


let is_guard : unit  ->  Prims.bool tac = (fun uu____1814 -> (

let uu____1817 = (cur_goal ())
in (bind uu____1817 (fun g -> (ret g.FStar_Tactics_Types.is_guard)))))


let mk_irrelevant_goal : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  FStar_Options.optionstate  ->  FStar_Tactics_Types.goal tac = (fun reason env phi opts -> (

let typ = (

let uu____1849 = (env.FStar_TypeChecker_Env.universe_of env phi)
in (FStar_Syntax_Util.mk_squash uu____1849 phi))
in (

let uu____1850 = (new_uvar reason env typ)
in (bind uu____1850 (fun u -> (

let goal = {FStar_Tactics_Types.context = env; FStar_Tactics_Types.witness = u; FStar_Tactics_Types.goal_ty = typ; FStar_Tactics_Types.opts = opts; FStar_Tactics_Types.is_guard = false}
in (ret goal)))))))


let __tc : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ * FStar_TypeChecker_Env.guard_t) tac = (fun e t -> (bind get (fun ps -> (mlog (fun uu____1899 -> (

let uu____1900 = (tts e t)
in (FStar_Util.print1 "Tac> __tc(%s)\n" uu____1900))) (fun uu____1902 -> (FStar_All.try_with (fun uu___81_1913 -> (match (()) with
| () -> begin
(

let uu____1922 = (ps.FStar_Tactics_Types.main_context.FStar_TypeChecker_Env.type_of e t)
in (ret uu____1922))
end)) (fun uu___80_1940 -> (match (uu___80_1940) with
| FStar_Errors.Err (uu____1949, msg) -> begin
(

let uu____1951 = (tts e t)
in (

let uu____1952 = (

let uu____1953 = (FStar_TypeChecker_Env.all_binders e)
in (FStar_All.pipe_right uu____1953 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____1951 uu____1952 msg)))
end
| FStar_Errors.Error (uu____1960, msg, uu____1962) -> begin
(

let uu____1963 = (tts e t)
in (

let uu____1964 = (

let uu____1965 = (FStar_TypeChecker_Env.all_binders e)
in (FStar_All.pipe_right uu____1965 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____1963 uu____1964 msg)))
end))))))))


let istrivial : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e t -> (

let steps = (FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.UnfoldTac)::(FStar_TypeChecker_Normalize.Unmeta)::[]
in (

let t1 = (normalize steps e t)
in (is_true t1))))


let get_guard_policy : unit  ->  FStar_Tactics_Types.guard_policy tac = (fun uu____1992 -> (bind get (fun ps -> (ret ps.FStar_Tactics_Types.guard_policy))))


let set_guard_policy : FStar_Tactics_Types.guard_policy  ->  unit tac = (fun pol -> (bind get (fun ps -> (set (

let uu___82_2010 = ps
in {FStar_Tactics_Types.main_context = uu___82_2010.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___82_2010.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___82_2010.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___82_2010.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___82_2010.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___82_2010.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___82_2010.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___82_2010.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___82_2010.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = pol; FStar_Tactics_Types.freshness = uu___82_2010.FStar_Tactics_Types.freshness})))))


let with_policy : 'a . FStar_Tactics_Types.guard_policy  ->  'a tac  ->  'a tac = (fun pol t -> (

let uu____2034 = (get_guard_policy ())
in (bind uu____2034 (fun old_pol -> (

let uu____2040 = (set_guard_policy pol)
in (bind uu____2040 (fun uu____2044 -> (bind t (fun r -> (

let uu____2048 = (set_guard_policy old_pol)
in (bind uu____2048 (fun uu____2052 -> (ret r)))))))))))))


let proc_guard : Prims.string  ->  env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Options.optionstate  ->  unit tac = (fun reason e g opts -> (

let uu____2077 = (

let uu____2078 = (FStar_TypeChecker_Rel.simplify_guard e g)
in uu____2078.FStar_TypeChecker_Env.guard_f)
in (match (uu____2077) with
| FStar_TypeChecker_Common.Trivial -> begin
(ret ())
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____2082 = (istrivial e f)
in (match (uu____2082) with
| true -> begin
(ret ())
end
| uu____2085 -> begin
(bind get (fun ps -> (match (ps.FStar_Tactics_Types.guard_policy) with
| FStar_Tactics_Types.Drop -> begin
(ret ())
end
| FStar_Tactics_Types.Goal -> begin
(

let uu____2090 = (mk_irrelevant_goal reason e f opts)
in (bind uu____2090 (fun goal -> (

let goal1 = (

let uu___83_2097 = goal
in {FStar_Tactics_Types.context = uu___83_2097.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___83_2097.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___83_2097.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___83_2097.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = true})
in (push_goals ((goal1)::[]))))))
end
| FStar_Tactics_Types.SMT -> begin
(

let uu____2098 = (mk_irrelevant_goal reason e f opts)
in (bind uu____2098 (fun goal -> (

let goal1 = (

let uu___84_2105 = goal
in {FStar_Tactics_Types.context = uu___84_2105.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___84_2105.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___84_2105.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___84_2105.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = true})
in (push_smt_goals ((goal1)::[]))))))
end
| FStar_Tactics_Types.Force -> begin
(FStar_All.try_with (fun uu___86_2110 -> (match (()) with
| () -> begin
(

let uu____2113 = (

let uu____2114 = (

let uu____2115 = (FStar_TypeChecker_Rel.discharge_guard_no_smt e g)
in (FStar_All.pipe_left FStar_TypeChecker_Rel.is_trivial uu____2115))
in (not (uu____2114)))
in (match (uu____2113) with
| true -> begin
(mlog (fun uu____2120 -> (

let uu____2121 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print1 "guard = %s\n" uu____2121))) (fun uu____2123 -> (fail1 "Forcing the guard failed %s)" reason)))
end
| uu____2124 -> begin
(ret ())
end))
end)) (fun uu___85_2127 -> (match (uu___85_2127) with
| uu____2130 -> begin
(mlog (fun uu____2133 -> (

let uu____2134 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print1 "guard = %s\n" uu____2134))) (fun uu____2136 -> (fail1 "Forcing the guard failed (%s)" reason)))
end)))
end)))
end))
end)))


let tc : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.typ tac = (fun t -> (

let uu____2146 = (

let uu____2149 = (cur_goal ())
in (bind uu____2149 (fun goal -> (

let uu____2155 = (__tc goal.FStar_Tactics_Types.context t)
in (bind uu____2155 (fun uu____2175 -> (match (uu____2175) with
| (t1, typ, guard) -> begin
(

let uu____2187 = (proc_guard "tc" goal.FStar_Tactics_Types.context guard goal.FStar_Tactics_Types.opts)
in (bind uu____2187 (fun uu____2191 -> (ret typ))))
end)))))))
in (FStar_All.pipe_left (wrap_err "tc") uu____2146)))


let add_irrelevant_goal : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  FStar_Options.optionstate  ->  unit tac = (fun reason env phi opts -> (

let uu____2220 = (mk_irrelevant_goal reason env phi opts)
in (bind uu____2220 (fun goal -> (add_goals ((goal)::[]))))))


let trivial : unit  ->  unit tac = (fun uu____2231 -> (

let uu____2234 = (cur_goal ())
in (bind uu____2234 (fun goal -> (

let uu____2240 = (istrivial goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (match (uu____2240) with
| true -> begin
(solve goal FStar_Syntax_Util.exp_unit)
end
| uu____2243 -> begin
(

let uu____2244 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail1 "Not a trivial goal: %s" uu____2244))
end))))))


let goal_from_guard : Prims.string  ->  env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Options.optionstate  ->  FStar_Tactics_Types.goal FStar_Pervasives_Native.option tac = (fun reason e g opts -> (

let uu____2273 = (

let uu____2274 = (FStar_TypeChecker_Rel.simplify_guard e g)
in uu____2274.FStar_TypeChecker_Env.guard_f)
in (match (uu____2273) with
| FStar_TypeChecker_Common.Trivial -> begin
(ret FStar_Pervasives_Native.None)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____2282 = (istrivial e f)
in (match (uu____2282) with
| true -> begin
(ret FStar_Pervasives_Native.None)
end
| uu____2289 -> begin
(

let uu____2290 = (mk_irrelevant_goal reason e f opts)
in (bind uu____2290 (fun goal -> (ret (FStar_Pervasives_Native.Some ((

let uu___87_2300 = goal
in {FStar_Tactics_Types.context = uu___87_2300.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___87_2300.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___87_2300.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___87_2300.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = true})))))))
end))
end)))


let smt : unit  ->  unit tac = (fun uu____2307 -> (

let uu____2310 = (cur_goal ())
in (bind uu____2310 (fun g -> (

let uu____2316 = (is_irrelevant g)
in (match (uu____2316) with
| true -> begin
(bind __dismiss (fun uu____2320 -> (add_smt_goals ((g)::[]))))
end
| uu____2321 -> begin
(

let uu____2322 = (tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (fail1 "goal is not irrelevant: cannot dispatch to smt (%s)" uu____2322))
end))))))


let divide : 'a 'b . FStar_BigInt.t  ->  'a tac  ->  'b tac  ->  ('a * 'b) tac = (fun n1 l r -> (bind get (fun p -> (

let uu____2371 = (FStar_All.try_with (fun uu___92_2394 -> (match (()) with
| () -> begin
(

let uu____2405 = (

let uu____2414 = (FStar_BigInt.to_int_fs n1)
in (FStar_List.splitAt uu____2414 p.FStar_Tactics_Types.goals))
in (ret uu____2405))
end)) (fun uu___91_2425 -> (match (uu___91_2425) with
| uu____2436 -> begin
(fail "divide: not enough goals")
end)))
in (bind uu____2371 (fun uu____2463 -> (match (uu____2463) with
| (lgs, rgs) -> begin
(

let lp = (

let uu___88_2489 = p
in {FStar_Tactics_Types.main_context = uu___88_2489.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___88_2489.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___88_2489.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = lgs; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = uu___88_2489.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___88_2489.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___88_2489.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___88_2489.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___88_2489.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___88_2489.FStar_Tactics_Types.freshness})
in (

let rp = (

let uu___89_2491 = p
in {FStar_Tactics_Types.main_context = uu___89_2491.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___89_2491.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___89_2491.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = rgs; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = uu___89_2491.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___89_2491.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___89_2491.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___89_2491.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___89_2491.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___89_2491.FStar_Tactics_Types.freshness})
in (

let uu____2492 = (set lp)
in (bind uu____2492 (fun uu____2500 -> (bind l (fun a -> (bind get (fun lp' -> (

let uu____2514 = (set rp)
in (bind uu____2514 (fun uu____2522 -> (bind r (fun b -> (bind get (fun rp' -> (

let p' = (

let uu___90_2538 = p
in {FStar_Tactics_Types.main_context = uu___90_2538.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___90_2538.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___90_2538.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append lp'.FStar_Tactics_Types.goals rp'.FStar_Tactics_Types.goals); FStar_Tactics_Types.smt_goals = (FStar_List.append lp'.FStar_Tactics_Types.smt_goals (FStar_List.append rp'.FStar_Tactics_Types.smt_goals p.FStar_Tactics_Types.smt_goals)); FStar_Tactics_Types.depth = uu___90_2538.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___90_2538.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___90_2538.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___90_2538.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___90_2538.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___90_2538.FStar_Tactics_Types.freshness})
in (

let uu____2539 = (set p')
in (bind uu____2539 (fun uu____2547 -> (ret ((a), (b)))))))))))))))))))))))
end)))))))


let focus : 'a . 'a tac  ->  'a tac = (fun f -> (

let uu____2568 = (divide FStar_BigInt.one f idtac)
in (bind uu____2568 (fun uu____2581 -> (match (uu____2581) with
| (a, ()) -> begin
(ret a)
end)))))


let rec map : 'a . 'a tac  ->  'a Prims.list tac = (fun tau -> (bind get (fun p -> (match (p.FStar_Tactics_Types.goals) with
| [] -> begin
(ret [])
end
| (uu____2618)::uu____2619 -> begin
(

let uu____2622 = (

let uu____2631 = (map tau)
in (divide FStar_BigInt.one tau uu____2631))
in (bind uu____2622 (fun uu____2649 -> (match (uu____2649) with
| (h, t) -> begin
(ret ((h)::t))
end))))
end))))


let seq : unit tac  ->  unit tac  ->  unit tac = (fun t1 t2 -> (

let uu____2690 = (bind t1 (fun uu____2695 -> (

let uu____2696 = (map t2)
in (bind uu____2696 (fun uu____2704 -> (ret ()))))))
in (focus uu____2690)))


let intro : unit  ->  FStar_Syntax_Syntax.binder tac = (fun uu____2713 -> (

let uu____2716 = (

let uu____2719 = (cur_goal ())
in (bind uu____2719 (fun goal -> (

let uu____2728 = (FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty)
in (match (uu____2728) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____2743 = (

let uu____2744 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____2744)))
in (match (uu____2743) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____2747 -> begin
(

let env' = (FStar_TypeChecker_Env.push_binders goal.FStar_Tactics_Types.context ((b)::[]))
in (

let typ' = (comp_to_typ c)
in (

let uu____2758 = (new_uvar "intro" env' typ')
in (bind uu____2758 (fun u -> (

let uu____2764 = (

let uu____2767 = (FStar_Syntax_Util.abs ((b)::[]) u FStar_Pervasives_Native.None)
in (trysolve goal uu____2767))
in (bind uu____2764 (fun bb -> (match (bb) with
| true -> begin
(

let uu____2781 = (

let uu____2784 = (

let uu___93_2785 = goal
in (

let uu____2786 = (bnorm env' u)
in (

let uu____2787 = (bnorm env' typ')
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = uu____2786; FStar_Tactics_Types.goal_ty = uu____2787; FStar_Tactics_Types.opts = uu___93_2785.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___93_2785.FStar_Tactics_Types.is_guard})))
in (replace_cur uu____2784))
in (bind uu____2781 (fun uu____2789 -> (ret b))))
end
| uu____2790 -> begin
(fail "unification failed")
end)))))))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2795 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail1 "goal is not an arrow (%s)" uu____2795))
end)))))
in (FStar_All.pipe_left (wrap_err "intro") uu____2716)))


let intro_rec : unit  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac = (fun uu____2810 -> (

let uu____2817 = (cur_goal ())
in (bind uu____2817 (fun goal -> ((FStar_Util.print_string "WARNING (intro_rec): calling this is known to cause normalizer loops\n");
(FStar_Util.print_string "WARNING (intro_rec): proceed at your own risk...\n");
(

let uu____2834 = (FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty)
in (match (uu____2834) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____2853 = (

let uu____2854 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____2854)))
in (match (uu____2853) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____2865 -> begin
(

let bv = (FStar_Syntax_Syntax.gen_bv "__recf" FStar_Pervasives_Native.None goal.FStar_Tactics_Types.goal_ty)
in (

let bs = (

let uu____2874 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____2874)::(b)::[])
in (

let env' = (FStar_TypeChecker_Env.push_binders goal.FStar_Tactics_Types.context bs)
in (

let uu____2892 = (

let uu____2895 = (comp_to_typ c)
in (new_uvar "intro_rec" env' uu____2895))
in (bind uu____2892 (fun u -> (

let lb = (

let uu____2910 = (FStar_Syntax_Util.abs ((b)::[]) u FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] goal.FStar_Tactics_Types.goal_ty FStar_Parser_Const.effect_Tot_lid uu____2910 [] FStar_Range.dummyRange))
in (

let body = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____2924 = (FStar_Syntax_Subst.close_let_rec ((lb)::[]) body)
in (match (uu____2924) with
| (lbs, body1) -> begin
(

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body1)))) FStar_Pervasives_Native.None goal.FStar_Tactics_Types.witness.FStar_Syntax_Syntax.pos)
in (

let uu____2956 = (trysolve goal tm)
in (bind uu____2956 (fun bb -> (match (bb) with
| true -> begin
(

let uu____2972 = (

let uu____2975 = (

let uu___94_2976 = goal
in (

let uu____2977 = (bnorm env' u)
in (

let uu____2978 = (

let uu____2979 = (comp_to_typ c)
in (bnorm env' uu____2979))
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = uu____2977; FStar_Tactics_Types.goal_ty = uu____2978; FStar_Tactics_Types.opts = uu___94_2976.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___94_2976.FStar_Tactics_Types.is_guard})))
in (replace_cur uu____2975))
in (bind uu____2972 (fun uu____2986 -> (

let uu____2987 = (

let uu____2992 = (FStar_Syntax_Syntax.mk_binder bv)
in ((uu____2992), (b)))
in (ret uu____2987)))))
end
| uu____2997 -> begin
(fail "intro_rec: unification failed")
end)))))
end))))))))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3006 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail1 "intro_rec: goal is not an arrow (%s)" uu____3006))
end));
)))))


let norm : FStar_Syntax_Embeddings.norm_step Prims.list  ->  unit tac = (fun s -> (

let uu____3024 = (cur_goal ())
in (bind uu____3024 (fun goal -> (mlog (fun uu____3031 -> (

let uu____3032 = (FStar_Syntax_Print.term_to_string goal.FStar_Tactics_Types.witness)
in (FStar_Util.print1 "norm: witness = %s\n" uu____3032))) (fun uu____3037 -> (

let steps = (

let uu____3041 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldTac)::[]) uu____3041))
in (

let w = (normalize steps goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.witness)
in (

let t = (normalize steps goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (replace_cur (

let uu___95_3048 = goal
in {FStar_Tactics_Types.context = uu___95_3048.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = w; FStar_Tactics_Types.goal_ty = t; FStar_Tactics_Types.opts = uu___95_3048.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___95_3048.FStar_Tactics_Types.is_guard})))))))))))


let norm_term_env : env  ->  FStar_Syntax_Embeddings.norm_step Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun e s t -> (

let uu____3072 = (mlog (fun uu____3077 -> (

let uu____3078 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "norm_term: tm = %s\n" uu____3078))) (fun uu____3080 -> (bind get (fun ps -> (

let opts = (match (ps.FStar_Tactics_Types.goals) with
| (g)::uu____3086 -> begin
g.FStar_Tactics_Types.opts
end
| uu____3089 -> begin
(FStar_Options.peek ())
end)
in (mlog (fun uu____3094 -> (

let uu____3095 = (tts ps.FStar_Tactics_Types.main_context t)
in (FStar_Util.print1 "norm_term_env: t = %s\n" uu____3095))) (fun uu____3098 -> (

let uu____3099 = (__tc e t)
in (bind uu____3099 (fun uu____3120 -> (match (uu____3120) with
| (t1, uu____3130, uu____3131) -> begin
(

let steps = (

let uu____3135 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldTac)::[]) uu____3135))
in (

let t2 = (normalize steps ps.FStar_Tactics_Types.main_context t1)
in (ret t2)))
end)))))))))))
in (FStar_All.pipe_left (wrap_err "norm_term") uu____3072)))


let refine_intro : unit  ->  unit tac = (fun uu____3149 -> (

let uu____3152 = (

let uu____3155 = (cur_goal ())
in (bind uu____3155 (fun g -> (

let uu____3162 = (FStar_TypeChecker_Rel.base_and_refinement g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (match (uu____3162) with
| (uu____3175, FStar_Pervasives_Native.None) -> begin
(fail "not a refinement")
end
| (t, FStar_Pervasives_Native.Some (bv, phi)) -> begin
(

let g1 = (

let uu___96_3200 = g
in {FStar_Tactics_Types.context = uu___96_3200.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___96_3200.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = t; FStar_Tactics_Types.opts = uu___96_3200.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___96_3200.FStar_Tactics_Types.is_guard})
in (

let uu____3201 = (

let uu____3206 = (

let uu____3211 = (

let uu____3212 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____3212)::[])
in (FStar_Syntax_Subst.open_term uu____3211 phi))
in (match (uu____3206) with
| (bvs, phi1) -> begin
(

let uu____3231 = (

let uu____3232 = (FStar_List.hd bvs)
in (FStar_Pervasives_Native.fst uu____3232))
in ((uu____3231), (phi1)))
end))
in (match (uu____3201) with
| (bv1, phi1) -> begin
(

let uu____3245 = (

let uu____3248 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv1), (g.FStar_Tactics_Types.witness))))::[]) phi1)
in (mk_irrelevant_goal "refine_intro refinement" g.FStar_Tactics_Types.context uu____3248 g.FStar_Tactics_Types.opts))
in (bind uu____3245 (fun g2 -> (bind __dismiss (fun uu____3254 -> (add_goals ((g1)::(g2)::[])))))))
end)))
end)))))
in (FStar_All.pipe_left (wrap_err "refine_intro") uu____3152)))


let __exact_now : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun set_expected_typ1 t -> (

let uu____3273 = (cur_goal ())
in (bind uu____3273 (fun goal -> (

let env = (match (set_expected_typ1) with
| true -> begin
(FStar_TypeChecker_Env.set_expected_typ goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
end
| uu____3281 -> begin
goal.FStar_Tactics_Types.context
end)
in (

let uu____3282 = (__tc env t)
in (bind uu____3282 (fun uu____3301 -> (match (uu____3301) with
| (t1, typ, guard) -> begin
(mlog (fun uu____3316 -> (

let uu____3317 = (tts goal.FStar_Tactics_Types.context typ)
in (

let uu____3318 = (FStar_TypeChecker_Rel.guard_to_string goal.FStar_Tactics_Types.context guard)
in (FStar_Util.print2 "__exact_now: got type %s\n__exact_now and guard %s\n" uu____3317 uu____3318)))) (fun uu____3321 -> (

let uu____3322 = (proc_guard "__exact typing" goal.FStar_Tactics_Types.context guard goal.FStar_Tactics_Types.opts)
in (bind uu____3322 (fun uu____3326 -> (mlog (fun uu____3330 -> (

let uu____3331 = (tts goal.FStar_Tactics_Types.context typ)
in (

let uu____3332 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (FStar_Util.print2 "__exact_now: unifying %s and %s\n" uu____3331 uu____3332)))) (fun uu____3335 -> (

let uu____3336 = (do_unify goal.FStar_Tactics_Types.context typ goal.FStar_Tactics_Types.goal_ty)
in (bind uu____3336 (fun b -> (match (b) with
| true -> begin
(solve goal t1)
end
| uu____3343 -> begin
(

let uu____3344 = (tts goal.FStar_Tactics_Types.context t1)
in (

let uu____3345 = (tts goal.FStar_Tactics_Types.context typ)
in (

let uu____3346 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (

let uu____3347 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.witness)
in (fail4 "%s : %s does not exactly solve the goal %s (witness = %s)" uu____3344 uu____3345 uu____3346 uu____3347)))))
end)))))))))))
end)))))))))


let t_exact : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun set_expected_typ1 tm -> (

let uu____3362 = (mlog (fun uu____3367 -> (

let uu____3368 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "t_exact: tm = %s\n" uu____3368))) (fun uu____3371 -> (

let uu____3372 = (

let uu____3379 = (__exact_now set_expected_typ1 tm)
in (trytac' uu____3379))
in (bind uu____3372 (fun uu___62_3388 -> (match (uu___62_3388) with
| FStar_Util.Inr (r) -> begin
(ret ())
end
| FStar_Util.Inl (e) -> begin
(

let uu____3397 = (

let uu____3404 = (

let uu____3407 = (norm ((FStar_Syntax_Embeddings.Delta)::[]))
in (bind uu____3407 (fun uu____3412 -> (

let uu____3413 = (refine_intro ())
in (bind uu____3413 (fun uu____3417 -> (__exact_now set_expected_typ1 tm)))))))
in (trytac' uu____3404))
in (bind uu____3397 (fun uu___61_3424 -> (match (uu___61_3424) with
| FStar_Util.Inr (r) -> begin
(ret ())
end
| FStar_Util.Inl (uu____3432) -> begin
(fail e)
end))))
end))))))
in (FStar_All.pipe_left (wrap_err "exact") uu____3362)))


let uvar_free_in_goal : FStar_Syntax_Syntax.uvar  ->  FStar_Tactics_Types.goal  ->  Prims.bool = (fun u g -> (match (g.FStar_Tactics_Types.is_guard) with
| true -> begin
false
end
| uu____3447 -> begin
(

let free_uvars = (

let uu____3461 = (

let uu____3464 = (FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty)
in (FStar_Util.set_elements uu____3464))
in (FStar_List.map (fun u1 -> u1.FStar_Syntax_Syntax.ctx_uvar_head) uu____3461))
in (FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars))
end))


let uvar_free : FStar_Syntax_Syntax.uvar  ->  FStar_Tactics_Types.proofstate  ->  Prims.bool = (fun u ps -> (FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals))


let rec mapM : 'a 'b . ('a  ->  'b tac)  ->  'a Prims.list  ->  'b Prims.list tac = (fun f l -> (match (l) with
| [] -> begin
(ret [])
end
| (x)::xs -> begin
(

let uu____3544 = (f x)
in (bind uu____3544 (fun y -> (

let uu____3552 = (mapM f xs)
in (bind uu____3552 (fun ys -> (ret ((y)::ys))))))))
end))

exception NoUnif


let uu___is_NoUnif : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoUnif -> begin
true
end
| uu____3572 -> begin
false
end))


let rec __apply : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.typ  ->  unit tac = (fun uopt tm typ -> (

let uu____3592 = (cur_goal ())
in (bind uu____3592 (fun goal -> (mlog (fun uu____3599 -> (

let uu____3600 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3600))) (fun uu____3603 -> (

let uu____3604 = (

let uu____3609 = (

let uu____3612 = (t_exact false tm)
in (with_policy FStar_Tactics_Types.Force uu____3612))
in (trytac_exn uu____3609))
in (bind uu____3604 (fun uu___63_3619 -> (match (uu___63_3619) with
| FStar_Pervasives_Native.Some (r) -> begin
(ret ())
end
| FStar_Pervasives_Native.None -> begin
(mlog (fun uu____3627 -> (

let uu____3628 = (FStar_Syntax_Print.term_to_string typ)
in (FStar_Util.print1 ">>> typ = %s\n" uu____3628))) (fun uu____3631 -> (

let uu____3632 = (FStar_Syntax_Util.arrow_one typ)
in (match (uu____3632) with
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise NoUnif)
end
| FStar_Pervasives_Native.Some ((bv, aq), c) -> begin
(mlog (fun uu____3656 -> (

let uu____3657 = (FStar_Syntax_Print.binder_to_string ((bv), (aq)))
in (FStar_Util.print1 "__apply: pushing binder %s\n" uu____3657))) (fun uu____3660 -> (

let uu____3661 = (

let uu____3662 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____3662)))
in (match (uu____3661) with
| true -> begin
(fail "apply: not total codomain")
end
| uu____3665 -> begin
(

let uu____3666 = (new_uvar "apply" goal.FStar_Tactics_Types.context bv.FStar_Syntax_Syntax.sort)
in (bind uu____3666 (fun u -> (

let tm' = (FStar_Syntax_Syntax.mk_Tm_app tm ((((u), (aq)))::[]) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
in (

let typ' = (

let uu____3692 = (comp_to_typ c)
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (u))))::[])) uu____3692))
in (

let uu____3695 = (__apply uopt tm' typ')
in (bind uu____3695 (fun uu____3708 -> (

let u1 = (bnorm goal.FStar_Tactics_Types.context u)
in (

let uu____3710 = (

let uu____3711 = (

let uu____3714 = (

let uu____3715 = (FStar_Syntax_Util.head_and_args u1)
in (FStar_Pervasives_Native.fst uu____3715))
in (FStar_Syntax_Subst.compress uu____3714))
in uu____3711.FStar_Syntax_Syntax.n)
in (match (uu____3710) with
| FStar_Syntax_Syntax.Tm_uvar ({FStar_Syntax_Syntax.ctx_uvar_head = uvar; FStar_Syntax_Syntax.ctx_uvar_gamma = uu____3743; FStar_Syntax_Syntax.ctx_uvar_binders = uu____3744; FStar_Syntax_Syntax.ctx_uvar_typ = uu____3745; FStar_Syntax_Syntax.ctx_uvar_reason = uu____3746; FStar_Syntax_Syntax.ctx_uvar_should_check = uu____3747; FStar_Syntax_Syntax.ctx_uvar_range = uu____3748}) -> begin
(bind get (fun ps -> (

let uu____3772 = (uopt && (uvar_free uvar ps))
in (match (uu____3772) with
| true -> begin
(ret ())
end
| uu____3775 -> begin
(

let uu____3776 = (

let uu____3779 = (

let uu___97_3780 = goal
in (

let uu____3781 = (bnorm goal.FStar_Tactics_Types.context u1)
in (

let uu____3782 = (bnorm goal.FStar_Tactics_Types.context bv.FStar_Syntax_Syntax.sort)
in {FStar_Tactics_Types.context = uu___97_3780.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu____3781; FStar_Tactics_Types.goal_ty = uu____3782; FStar_Tactics_Types.opts = uu___97_3780.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = false})))
in (uu____3779)::[])
in (add_goals uu____3776))
end))))
end
| t -> begin
(ret ())
end)))))))))))
end))))
end))))
end))))))))))


let try_unif : 'a . 'a tac  ->  'a tac  ->  'a tac = (fun t t' -> (mk_tac (fun ps -> (FStar_All.try_with (fun uu___99_3816 -> (match (()) with
| () -> begin
(run t ps)
end)) (fun uu___98_3820 -> (match (uu___98_3820) with
| NoUnif -> begin
(run t' ps)
end))))))


let apply : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun uopt tm -> (

let uu____3837 = (mlog (fun uu____3842 -> (

let uu____3843 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "apply: tm = %s\n" uu____3843))) (fun uu____3846 -> (

let uu____3847 = (cur_goal ())
in (bind uu____3847 (fun goal -> (

let uu____3853 = (__tc goal.FStar_Tactics_Types.context tm)
in (bind uu____3853 (fun uu____3875 -> (match (uu____3875) with
| (tm1, typ, guard) -> begin
(

let typ1 = (bnorm goal.FStar_Tactics_Types.context typ)
in (

let uu____3888 = (

let uu____3891 = (

let uu____3894 = (__apply uopt tm1 typ1)
in (bind uu____3894 (fun uu____3898 -> (proc_guard "apply guard" goal.FStar_Tactics_Types.context guard goal.FStar_Tactics_Types.opts))))
in (focus uu____3891))
in (

let uu____3899 = (

let uu____3902 = (tts goal.FStar_Tactics_Types.context tm1)
in (

let uu____3903 = (tts goal.FStar_Tactics_Types.context typ1)
in (

let uu____3904 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail3 "Cannot instantiate %s (of type %s) to match goal (%s)" uu____3902 uu____3903 uu____3904))))
in (try_unif uu____3888 uu____3899))))
end)))))))))
in (FStar_All.pipe_left (wrap_err "apply") uu____3837)))


let lemma_or_sq : FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun c -> (

let ct = (FStar_Syntax_Util.comp_to_comp_typ_nouniv c)
in (

let uu____3927 = (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____3927) with
| true -> begin
(

let uu____3934 = (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre)::(post)::uu____3953 -> begin
(((FStar_Pervasives_Native.fst pre)), ((FStar_Pervasives_Native.fst post)))
end
| uu____3994 -> begin
(failwith "apply_lemma: impossible: not a lemma")
end)
in (match (uu____3934) with
| (pre, post) -> begin
(

let post1 = (

let uu____4030 = (

let uu____4039 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit)
in (uu____4039)::[])
in (FStar_Syntax_Util.mk_app post uu____4030))
in FStar_Pervasives_Native.Some (((pre), (post1))))
end))
end
| uu____4066 -> begin
(

let uu____4067 = (FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name)
in (match (uu____4067) with
| true -> begin
(

let uu____4074 = (FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.map_opt uu____4074 (fun post -> ((FStar_Syntax_Util.t_true), (post)))))
end
| uu____4083 -> begin
FStar_Pervasives_Native.None
end))
end))))


let apply_lemma : FStar_Syntax_Syntax.term  ->  unit tac = (fun tm -> (

let uu____4097 = (

let uu____4100 = (mlog (fun uu____4105 -> (

let uu____4106 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4106))) (fun uu____4110 -> (

let is_unit_t = (fun t -> (

let uu____4117 = (

let uu____4118 = (FStar_Syntax_Subst.compress t)
in uu____4118.FStar_Syntax_Syntax.n)
in (match (uu____4117) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
true
end
| uu____4122 -> begin
false
end)))
in (

let uu____4123 = (cur_goal ())
in (bind uu____4123 (fun goal -> (

let uu____4129 = (__tc goal.FStar_Tactics_Types.context tm)
in (bind uu____4129 (fun uu____4152 -> (match (uu____4152) with
| (tm1, t, guard) -> begin
(

let uu____4164 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____4164) with
| (bs, comp) -> begin
(

let uu____4191 = (lemma_or_sq comp)
in (match (uu____4191) with
| FStar_Pervasives_Native.None -> begin
(fail "not a lemma or squashed function")
end
| FStar_Pervasives_Native.Some (pre, post) -> begin
(

let uu____4210 = (FStar_List.fold_left (fun uu____4256 uu____4257 -> (match (((uu____4256), (uu____4257))) with
| ((uvs, guard1, subst1), (b, aq)) -> begin
(

let b_t = (FStar_Syntax_Subst.subst subst1 b.FStar_Syntax_Syntax.sort)
in (

let uu____4360 = (is_unit_t b_t)
in (match (uu____4360) with
| true -> begin
(((((FStar_Syntax_Util.exp_unit), (aq)))::uvs), (guard1), ((FStar_Syntax_Syntax.NT (((b), (FStar_Syntax_Util.exp_unit))))::subst1))
end
| uu____4397 -> begin
(

let uu____4398 = (FStar_TypeChecker_Util.new_implicit_var "apply_lemma" goal.FStar_Tactics_Types.goal_ty.FStar_Syntax_Syntax.pos goal.FStar_Tactics_Types.context b_t)
in (match (uu____4398) with
| (u, uu____4428, g_u) -> begin
(

let uu____4442 = (FStar_TypeChecker_Rel.conj_guard guard1 g_u)
in (((((u), (aq)))::uvs), (uu____4442), ((FStar_Syntax_Syntax.NT (((b), (u))))::subst1)))
end))
end)))
end)) (([]), (guard), ([])) bs)
in (match (uu____4210) with
| (uvs, implicits, subst1) -> begin
(

let uvs1 = (FStar_List.rev uvs)
in (

let pre1 = (FStar_Syntax_Subst.subst subst1 pre)
in (

let post1 = (FStar_Syntax_Subst.subst subst1 post)
in (

let uu____4515 = (

let uu____4518 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero post1)
in (do_unify goal.FStar_Tactics_Types.context uu____4518 goal.FStar_Tactics_Types.goal_ty))
in (bind uu____4515 (fun b -> (match ((not (b))) with
| true -> begin
(

let uu____4526 = (tts goal.FStar_Tactics_Types.context tm1)
in (

let uu____4527 = (

let uu____4528 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero post1)
in (tts goal.FStar_Tactics_Types.context uu____4528))
in (

let uu____4529 = (tts goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.goal_ty)
in (fail3 "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)" uu____4526 uu____4527 uu____4529))))
end
| uu____4530 -> begin
(

let uu____4531 = (add_implicits implicits.FStar_TypeChecker_Env.implicits)
in (bind uu____4531 (fun uu____4536 -> (

let uu____4537 = (solve goal FStar_Syntax_Util.exp_unit)
in (bind uu____4537 (fun uu____4545 -> (

let is_free_uvar = (fun uv t1 -> (

let free_uvars = (

let uu____4570 = (

let uu____4573 = (FStar_Syntax_Free.uvars t1)
in (FStar_Util.set_elements uu____4573))
in (FStar_List.map (fun x -> x.FStar_Syntax_Syntax.ctx_uvar_head) uu____4570))
in (FStar_List.existsML (fun u -> (FStar_Syntax_Unionfind.equiv u uv)) free_uvars)))
in (

let appears = (fun uv goals -> (FStar_List.existsML (fun g' -> (is_free_uvar uv g'.FStar_Tactics_Types.goal_ty)) goals))
in (

let checkone = (fun t1 goals -> (

let uu____4622 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____4622) with
| (hd1, uu____4638) -> begin
(match (hd1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv) -> begin
(appears uv.FStar_Syntax_Syntax.ctx_uvar_head goals)
end
| uu____4660 -> begin
false
end)
end)))
in (

let uu____4661 = (FStar_All.pipe_right implicits.FStar_TypeChecker_Env.implicits (mapM (fun uu____4729 -> (match (uu____4729) with
| (_msg, term, ctx_uvar, _range, uu____4754) -> begin
(

let uu____4755 = (FStar_Syntax_Util.head_and_args term)
in (match (uu____4755) with
| (hd1, uu____4781) -> begin
(

let env = (

let uu___100_4803 = goal.FStar_Tactics_Types.context
in {FStar_TypeChecker_Env.solver = uu___100_4803.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___100_4803.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___100_4803.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_TypeChecker_Env.gamma_sig = uu___100_4803.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___100_4803.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___100_4803.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___100_4803.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___100_4803.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___100_4803.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___100_4803.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___100_4803.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___100_4803.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___100_4803.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___100_4803.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___100_4803.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___100_4803.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___100_4803.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___100_4803.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___100_4803.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___100_4803.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___100_4803.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___100_4803.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___100_4803.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___100_4803.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___100_4803.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___100_4803.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___100_4803.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___100_4803.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___100_4803.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___100_4803.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___100_4803.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___100_4803.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___100_4803.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___100_4803.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___100_4803.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___100_4803.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___100_4803.FStar_TypeChecker_Env.dep_graph})
in (

let uu____4804 = (

let uu____4805 = (FStar_Syntax_Subst.compress hd1)
in uu____4805.FStar_Syntax_Syntax.n)
in (match (uu____4804) with
| FStar_Syntax_Syntax.Tm_uvar (uu____4818) -> begin
(

let uu____4819 = (

let uu____4828 = (

let uu____4831 = (

let uu___101_4832 = goal
in (

let uu____4833 = (bnorm env term)
in (

let uu____4834 = (bnorm env ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in {FStar_Tactics_Types.context = env; FStar_Tactics_Types.witness = uu____4833; FStar_Tactics_Types.goal_ty = uu____4834; FStar_Tactics_Types.opts = uu___101_4832.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___101_4832.FStar_Tactics_Types.is_guard})))
in (uu____4831)::[])
in ((uu____4828), ([])))
in (ret uu____4819))
end
| uu____4847 -> begin
(

let g_typ = (

let uu____4849 = (FStar_Options.__temp_fast_implicits ())
in (match (uu____4849) with
| true -> begin
(FStar_TypeChecker_TcTerm.check_type_of_well_typed_term false env term ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
end
| uu____4850 -> begin
(

let term1 = (bnorm env term)
in (

let uu____4852 = (

let uu____4859 = (FStar_TypeChecker_Env.set_expected_typ env ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in (env.FStar_TypeChecker_Env.type_of uu____4859 term1))
in (match (uu____4852) with
| (uu____4860, uu____4861, g_typ) -> begin
g_typ
end)))
end))
in (

let uu____4863 = (goal_from_guard "apply_lemma solved arg" goal.FStar_Tactics_Types.context g_typ goal.FStar_Tactics_Types.opts)
in (bind uu____4863 (fun uu___64_4879 -> (match (uu___64_4879) with
| FStar_Pervasives_Native.None -> begin
(ret (([]), ([])))
end
| FStar_Pervasives_Native.Some (g) -> begin
(ret (([]), ((g)::[])))
end)))))
end)))
end))
end))))
in (bind uu____4661 (fun goals_ -> (

let sub_goals = (

let uu____4947 = (FStar_List.map FStar_Pervasives_Native.fst goals_)
in (FStar_List.flatten uu____4947))
in (

let smt_goals = (

let uu____4969 = (FStar_List.map FStar_Pervasives_Native.snd goals_)
in (FStar_List.flatten uu____4969))
in (

let rec filter' = (fun f xs -> (match (xs) with
| [] -> begin
[]
end
| (x)::xs1 -> begin
(

let uu____5030 = (f x xs1)
in (match (uu____5030) with
| true -> begin
(

let uu____5033 = (filter' f xs1)
in (x)::uu____5033)
end
| uu____5036 -> begin
(filter' f xs1)
end))
end))
in (

let sub_goals1 = (filter' (fun g goals -> (

let uu____5047 = (checkone g.FStar_Tactics_Types.witness goals)
in (not (uu____5047)))) sub_goals)
in (

let uu____5048 = (proc_guard "apply_lemma guard" goal.FStar_Tactics_Types.context guard goal.FStar_Tactics_Types.opts)
in (bind uu____5048 (fun uu____5053 -> (

let uu____5054 = (

let uu____5057 = (

let uu____5058 = (

let uu____5059 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero pre1)
in (istrivial goal.FStar_Tactics_Types.context uu____5059))
in (not (uu____5058)))
in (match (uu____5057) with
| true -> begin
(add_irrelevant_goal "apply_lemma precondition" goal.FStar_Tactics_Types.context pre1 goal.FStar_Tactics_Types.opts)
end
| uu____5062 -> begin
(ret ())
end))
in (bind uu____5054 (fun uu____5065 -> (

let uu____5066 = (add_smt_goals smt_goals)
in (bind uu____5066 (fun uu____5070 -> (add_goals sub_goals1))))))))))))))))))))))))))
end)))))))
end))
end))
end))
end))))))))))
in (focus uu____4100))
in (FStar_All.pipe_left (wrap_err "apply_lemma") uu____4097)))


let destruct_eq' : FStar_Reflection_Data.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun typ -> (

let uu____5092 = (FStar_Syntax_Util.destruct_typ_as_formula typ)
in (match (uu____5092) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (l, (uu____5102)::((e1, uu____5104))::((e2, uu____5106))::[])) when (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) -> begin
FStar_Pervasives_Native.Some (((e1), (e2)))
end
| uu____5153 -> begin
FStar_Pervasives_Native.None
end)))


let destruct_eq : FStar_Reflection_Data.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun typ -> (

let uu____5177 = (destruct_eq' typ)
in (match (uu____5177) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5207 = (FStar_Syntax_Util.un_squash typ)
in (match (uu____5207) with
| FStar_Pervasives_Native.Some (typ1) -> begin
(destruct_eq' typ1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end)))


let split_env : FStar_Syntax_Syntax.bv  ->  env  ->  (env * FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.option = (fun bvar e -> (

let rec aux = (fun e1 -> (

let uu____5261 = (FStar_TypeChecker_Env.pop_bv e1)
in (match (uu____5261) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (bv', e') -> begin
(match ((FStar_Syntax_Syntax.bv_eq bvar bv')) with
| true -> begin
FStar_Pervasives_Native.Some (((e'), ([])))
end
| uu____5308 -> begin
(

let uu____5309 = (aux e')
in (FStar_Util.map_opt uu____5309 (fun uu____5333 -> (match (uu____5333) with
| (e'', bvs) -> begin
((e''), ((bv')::bvs))
end))))
end)
end)))
in (

let uu____5354 = (aux e)
in (FStar_Util.map_opt uu____5354 (fun uu____5378 -> (match (uu____5378) with
| (e', bvs) -> begin
((e'), ((FStar_List.rev bvs)))
end))))))


let push_bvs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_TypeChecker_Env.env = (fun e bvs -> (FStar_List.fold_left (fun e1 b -> (FStar_TypeChecker_Env.push_bv e1 b)) e bvs))


let subst_goal : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Tactics_Types.goal  ->  FStar_Tactics_Types.goal FStar_Pervasives_Native.option = (fun b1 b2 s g -> (

let uu____5445 = (split_env b1 g.FStar_Tactics_Types.context)
in (FStar_Util.map_opt uu____5445 (fun uu____5469 -> (match (uu____5469) with
| (e0, bvs) -> begin
(

let s1 = (fun bv -> (

let uu___102_5488 = bv
in (

let uu____5489 = (FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___102_5488.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___102_5488.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5489})))
in (

let bvs1 = (FStar_List.map s1 bvs)
in (

let c = (push_bvs e0 ((b2)::bvs1))
in (

let w = (FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness)
in (

let t = (FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty)
in (

let uu___103_5498 = g
in {FStar_Tactics_Types.context = c; FStar_Tactics_Types.witness = w; FStar_Tactics_Types.goal_ty = t; FStar_Tactics_Types.opts = uu___103_5498.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___103_5498.FStar_Tactics_Types.is_guard}))))))
end)))))


let rewrite : FStar_Syntax_Syntax.binder  ->  unit tac = (fun h -> (

let uu____5508 = (cur_goal ())
in (bind uu____5508 (fun goal -> (

let uu____5516 = h
in (match (uu____5516) with
| (bv, uu____5520) -> begin
(mlog (fun uu____5524 -> (

let uu____5525 = (FStar_Syntax_Print.bv_to_string bv)
in (

let uu____5526 = (tts goal.FStar_Tactics_Types.context bv.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5525 uu____5526)))) (fun uu____5529 -> (

let uu____5530 = (split_env bv goal.FStar_Tactics_Types.context)
in (match (uu____5530) with
| FStar_Pervasives_Native.None -> begin
(fail "rewrite: binder not found in environment")
end
| FStar_Pervasives_Native.Some (e0, bvs) -> begin
(

let uu____5559 = (destruct_eq bv.FStar_Syntax_Syntax.sort)
in (match (uu____5559) with
| FStar_Pervasives_Native.Some (x, e) -> begin
(

let uu____5574 = (

let uu____5575 = (FStar_Syntax_Subst.compress x)
in uu____5575.FStar_Syntax_Syntax.n)
in (match (uu____5574) with
| FStar_Syntax_Syntax.Tm_name (x1) -> begin
(

let s = (FStar_Syntax_Syntax.NT (((x1), (e))))::[]
in (

let s1 = (fun bv1 -> (

let uu___104_5592 = bv1
in (

let uu____5593 = (FStar_Syntax_Subst.subst s bv1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___104_5592.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___104_5592.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5593})))
in (

let bvs1 = (FStar_List.map s1 bvs)
in (

let uu____5599 = (

let uu___105_5600 = goal
in (

let uu____5601 = (push_bvs e0 ((bv)::bvs1))
in (

let uu____5602 = (FStar_Syntax_Subst.subst s goal.FStar_Tactics_Types.witness)
in (

let uu____5603 = (FStar_Syntax_Subst.subst s goal.FStar_Tactics_Types.goal_ty)
in {FStar_Tactics_Types.context = uu____5601; FStar_Tactics_Types.witness = uu____5602; FStar_Tactics_Types.goal_ty = uu____5603; FStar_Tactics_Types.opts = uu___105_5600.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___105_5600.FStar_Tactics_Types.is_guard}))))
in (replace_cur uu____5599)))))
end
| uu____5604 -> begin
(fail "rewrite: Not an equality hypothesis with a variable on the LHS")
end))
end
| uu____5605 -> begin
(fail "rewrite: Not an equality hypothesis")
end))
end))))
end))))))


let rename_to : FStar_Syntax_Syntax.binder  ->  Prims.string  ->  unit tac = (fun b s -> (

let uu____5626 = (cur_goal ())
in (bind uu____5626 (fun goal -> (

let uu____5637 = b
in (match (uu____5637) with
| (bv, uu____5641) -> begin
(

let bv' = (

let uu____5643 = (

let uu___106_5644 = bv
in (

let uu____5645 = (FStar_Ident.mk_ident ((s), (bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
in {FStar_Syntax_Syntax.ppname = uu____5645; FStar_Syntax_Syntax.index = uu___106_5644.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___106_5644.FStar_Syntax_Syntax.sort}))
in (FStar_Syntax_Syntax.freshen_bv uu____5643))
in (

let s1 = (

let uu____5649 = (

let uu____5650 = (

let uu____5657 = (FStar_Syntax_Syntax.bv_to_name bv')
in ((bv), (uu____5657)))
in FStar_Syntax_Syntax.NT (uu____5650))
in (uu____5649)::[])
in (

let uu____5662 = (subst_goal bv bv' s1 goal)
in (match (uu____5662) with
| FStar_Pervasives_Native.None -> begin
(fail "rename_to: binder not found in environment")
end
| FStar_Pervasives_Native.Some (goal1) -> begin
(replace_cur goal1)
end))))
end))))))


let binder_retype : FStar_Syntax_Syntax.binder  ->  unit tac = (fun b -> (

let uu____5677 = (cur_goal ())
in (bind uu____5677 (fun goal -> (

let uu____5686 = b
in (match (uu____5686) with
| (bv, uu____5690) -> begin
(

let uu____5691 = (split_env bv goal.FStar_Tactics_Types.context)
in (match (uu____5691) with
| FStar_Pervasives_Native.None -> begin
(fail "binder_retype: binder is not present in environment")
end
| FStar_Pervasives_Native.Some (e0, bvs) -> begin
(

let uu____5720 = (FStar_Syntax_Util.type_u ())
in (match (uu____5720) with
| (ty, u) -> begin
(

let uu____5729 = (new_uvar "binder_retype" e0 ty)
in (bind uu____5729 (fun t' -> (

let bv'' = (

let uu___107_5739 = bv
in {FStar_Syntax_Syntax.ppname = uu___107_5739.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___107_5739.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t'})
in (

let s = (

let uu____5743 = (

let uu____5744 = (

let uu____5751 = (FStar_Syntax_Syntax.bv_to_name bv'')
in ((bv), (uu____5751)))
in FStar_Syntax_Syntax.NT (uu____5744))
in (uu____5743)::[])
in (

let bvs1 = (FStar_List.map (fun b1 -> (

let uu___108_5763 = b1
in (

let uu____5764 = (FStar_Syntax_Subst.subst s b1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___108_5763.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___108_5763.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5764}))) bvs)
in (

let env' = (push_bvs e0 ((bv'')::bvs1))
in (bind __dismiss (fun uu____5770 -> (

let uu____5771 = (

let uu____5774 = (

let uu____5777 = (

let uu___109_5778 = goal
in (

let uu____5779 = (FStar_Syntax_Subst.subst s goal.FStar_Tactics_Types.witness)
in (

let uu____5780 = (FStar_Syntax_Subst.subst s goal.FStar_Tactics_Types.goal_ty)
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = uu____5779; FStar_Tactics_Types.goal_ty = uu____5780; FStar_Tactics_Types.opts = uu___109_5778.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___109_5778.FStar_Tactics_Types.is_guard})))
in (uu____5777)::[])
in (add_goals uu____5774))
in (bind uu____5771 (fun uu____5783 -> (

let uu____5784 = (FStar_Syntax_Util.mk_eq2 (FStar_Syntax_Syntax.U_succ (u)) ty bv.FStar_Syntax_Syntax.sort t')
in (add_irrelevant_goal "binder_retype equation" e0 uu____5784 goal.FStar_Tactics_Types.opts))))))))))))))
end))
end))
end))))))


let norm_binder_type : FStar_Syntax_Embeddings.norm_step Prims.list  ->  FStar_Syntax_Syntax.binder  ->  unit tac = (fun s b -> (

let uu____5803 = (cur_goal ())
in (bind uu____5803 (fun goal -> (

let uu____5812 = b
in (match (uu____5812) with
| (bv, uu____5816) -> begin
(

let uu____5817 = (split_env bv goal.FStar_Tactics_Types.context)
in (match (uu____5817) with
| FStar_Pervasives_Native.None -> begin
(fail "binder_retype: binder is not present in environment")
end
| FStar_Pervasives_Native.Some (e0, bvs) -> begin
(

let steps = (

let uu____5849 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldTac)::[]) uu____5849))
in (

let sort' = (normalize steps e0 bv.FStar_Syntax_Syntax.sort)
in (

let bv' = (

let uu___110_5854 = bv
in {FStar_Syntax_Syntax.ppname = uu___110_5854.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___110_5854.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort'})
in (

let env' = (push_bvs e0 ((bv')::bvs))
in (replace_cur (

let uu___111_5858 = goal
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = uu___111_5858.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___111_5858.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___111_5858.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___111_5858.FStar_Tactics_Types.is_guard}))))))
end))
end))))))


let revert : unit  ->  unit tac = (fun uu____5865 -> (

let uu____5868 = (cur_goal ())
in (bind uu____5868 (fun goal -> (

let uu____5874 = (FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context)
in (match (uu____5874) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot revert; empty context")
end
| FStar_Pervasives_Native.Some (x, env') -> begin
(

let typ' = (

let uu____5896 = (FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty)
in (FStar_Syntax_Util.arrow ((((x), (FStar_Pervasives_Native.None)))::[]) uu____5896))
in (

let w' = (FStar_Syntax_Util.abs ((((x), (FStar_Pervasives_Native.None)))::[]) goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None)
in (replace_cur (

let uu___112_5924 = goal
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = w'; FStar_Tactics_Types.goal_ty = typ'; FStar_Tactics_Types.opts = uu___112_5924.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___112_5924.FStar_Tactics_Types.is_guard}))))
end))))))


let free_in : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun bv t -> (

let uu____5935 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_mem bv uu____5935)))


let rec clear : FStar_Syntax_Syntax.binder  ->  unit tac = (fun b -> (

let bv = (FStar_Pervasives_Native.fst b)
in (

let uu____5948 = (cur_goal ())
in (bind uu____5948 (fun goal -> (mlog (fun uu____5956 -> (

let uu____5957 = (FStar_Syntax_Print.binder_to_string b)
in (

let uu____5958 = (

let uu____5959 = (

let uu____5960 = (FStar_TypeChecker_Env.all_binders goal.FStar_Tactics_Types.context)
in (FStar_All.pipe_right uu____5960 FStar_List.length))
in (FStar_All.pipe_right uu____5959 FStar_Util.string_of_int))
in (FStar_Util.print2 "Clear of (%s), env has %s binders\n" uu____5957 uu____5958)))) (fun uu____5979 -> (

let uu____5980 = (split_env bv goal.FStar_Tactics_Types.context)
in (match (uu____5980) with
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

let uu____6027 = (free_in bv bv'.FStar_Syntax_Syntax.sort)
in (match (uu____6027) with
| true -> begin
(

let uu____6030 = (

let uu____6031 = (FStar_Syntax_Print.bv_to_string bv')
in (FStar_Util.format1 "Cannot clear; binder present in the type of %s" uu____6031))
in (fail uu____6030))
end
| uu____6032 -> begin
(check1 bvs2)
end))
end))
in (

let uu____6033 = (free_in bv goal.FStar_Tactics_Types.goal_ty)
in (match (uu____6033) with
| true -> begin
(fail "Cannot clear; binder present in goal")
end
| uu____6036 -> begin
(

let uu____6037 = (check1 bvs)
in (bind uu____6037 (fun uu____6043 -> (

let env' = (push_bvs e' bvs)
in (

let uu____6045 = (new_uvar "clear.witness" env' goal.FStar_Tactics_Types.goal_ty)
in (bind uu____6045 (fun ut -> (

let uu____6051 = (do_unify goal.FStar_Tactics_Types.context goal.FStar_Tactics_Types.witness ut)
in (bind uu____6051 (fun b1 -> (match (b1) with
| true -> begin
(replace_cur (

let uu___113_6060 = goal
in {FStar_Tactics_Types.context = env'; FStar_Tactics_Types.witness = ut; FStar_Tactics_Types.goal_ty = uu___113_6060.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___113_6060.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___113_6060.FStar_Tactics_Types.is_guard}))
end
| uu____6061 -> begin
(fail "Cannot clear; binder appears in witness")
end)))))))))))
end)))
end)))))))))


let clear_top : unit  ->  unit tac = (fun uu____6068 -> (

let uu____6071 = (cur_goal ())
in (bind uu____6071 (fun goal -> (

let uu____6077 = (FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context)
in (match (uu____6077) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot clear; empty context")
end
| FStar_Pervasives_Native.Some (x, uu____6091) -> begin
(

let uu____6096 = (FStar_Syntax_Syntax.mk_binder x)
in (clear uu____6096))
end))))))


let prune : Prims.string  ->  unit tac = (fun s -> (

let uu____6106 = (cur_goal ())
in (bind uu____6106 (fun g -> (

let ctx = g.FStar_Tactics_Types.context
in (

let ctx' = (

let uu____6116 = (FStar_Ident.path_of_text s)
in (FStar_TypeChecker_Env.rem_proof_ns ctx uu____6116))
in (

let g' = (

let uu___114_6118 = g
in {FStar_Tactics_Types.context = ctx'; FStar_Tactics_Types.witness = uu___114_6118.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___114_6118.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___114_6118.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___114_6118.FStar_Tactics_Types.is_guard})
in (bind __dismiss (fun uu____6120 -> (add_goals ((g')::[])))))))))))


let addns : Prims.string  ->  unit tac = (fun s -> (

let uu____6130 = (cur_goal ())
in (bind uu____6130 (fun g -> (

let ctx = g.FStar_Tactics_Types.context
in (

let ctx' = (

let uu____6140 = (FStar_Ident.path_of_text s)
in (FStar_TypeChecker_Env.add_proof_ns ctx uu____6140))
in (

let g' = (

let uu___115_6142 = g
in {FStar_Tactics_Types.context = ctx'; FStar_Tactics_Types.witness = uu___115_6142.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___115_6142.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___115_6142.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___115_6142.FStar_Tactics_Types.is_guard})
in (bind __dismiss (fun uu____6144 -> (add_goals ((g')::[])))))))))))


let rec tac_fold_env : FStar_Tactics_Types.direction  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac)  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun d f env t -> (

let tn = (

let uu____6184 = (FStar_Syntax_Subst.compress t)
in uu____6184.FStar_Syntax_Syntax.n)
in (

let uu____6187 = (match ((Prims.op_Equality d FStar_Tactics_Types.TopDown)) with
| true -> begin
(f env (

let uu___119_6193 = t
in {FStar_Syntax_Syntax.n = tn; FStar_Syntax_Syntax.pos = uu___119_6193.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___119_6193.FStar_Syntax_Syntax.vars}))
end
| uu____6194 -> begin
(ret t)
end)
in (bind uu____6187 (fun t1 -> (

let ff = (tac_fold_env d f env)
in (

let tn1 = (

let uu____6209 = (

let uu____6210 = (FStar_Syntax_Subst.compress t1)
in uu____6210.FStar_Syntax_Syntax.n)
in (match (uu____6209) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____6237 = (ff hd1)
in (bind uu____6237 (fun hd2 -> (

let fa = (fun uu____6259 -> (match (uu____6259) with
| (a, q) -> begin
(

let uu____6272 = (ff a)
in (bind uu____6272 (fun a1 -> (ret ((a1), (q))))))
end))
in (

let uu____6285 = (mapM fa args)
in (bind uu____6285 (fun args1 -> (ret (FStar_Syntax_Syntax.Tm_app (((hd2), (args1))))))))))))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, k) -> begin
(

let uu____6351 = (FStar_Syntax_Subst.open_term bs t2)
in (match (uu____6351) with
| (bs1, t') -> begin
(

let uu____6360 = (

let uu____6363 = (FStar_TypeChecker_Env.push_binders env bs1)
in (tac_fold_env d f uu____6363 t'))
in (bind uu____6360 (fun t'' -> (

let uu____6367 = (

let uu____6368 = (

let uu____6385 = (FStar_Syntax_Subst.close_binders bs1)
in (

let uu____6392 = (FStar_Syntax_Subst.close bs1 t'')
in ((uu____6385), (uu____6392), (k))))
in FStar_Syntax_Syntax.Tm_abs (uu____6368))
in (ret uu____6367)))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(ret tn)
end
| FStar_Syntax_Syntax.Tm_match (hd1, brs) -> begin
(

let uu____6461 = (ff hd1)
in (bind uu____6461 (fun hd2 -> (

let ffb = (fun br -> (

let uu____6476 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____6476) with
| (pat, w, e) -> begin
(

let bvs = (FStar_Syntax_Syntax.pat_bvs pat)
in (

let ff1 = (

let uu____6508 = (FStar_TypeChecker_Env.push_bvs env bvs)
in (tac_fold_env d f uu____6508))
in (

let uu____6509 = (ff1 e)
in (bind uu____6509 (fun e1 -> (

let br1 = (FStar_Syntax_Subst.close_branch ((pat), (w), (e1)))
in (ret br1)))))))
end)))
in (

let uu____6524 = (mapM ffb brs)
in (bind uu____6524 (fun brs1 -> (ret (FStar_Syntax_Syntax.Tm_match (((hd2), (brs1))))))))))))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (bv); FStar_Syntax_Syntax.lbunivs = uu____6568; FStar_Syntax_Syntax.lbtyp = uu____6569; FStar_Syntax_Syntax.lbeff = uu____6570; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu____6572; FStar_Syntax_Syntax.lbpos = uu____6573})::[]), e) -> begin
(

let lb = (

let uu____6598 = (

let uu____6599 = (FStar_Syntax_Subst.compress t1)
in uu____6599.FStar_Syntax_Syntax.n)
in (match (uu____6598) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), uu____6603) -> begin
lb
end
| uu____6616 -> begin
(failwith "impossible")
end))
in (

let fflb = (fun lb1 -> (

let uu____6625 = (ff lb1.FStar_Syntax_Syntax.lbdef)
in (bind uu____6625 (fun def1 -> (ret (

let uu___116_6631 = lb1
in {FStar_Syntax_Syntax.lbname = uu___116_6631.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___116_6631.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___116_6631.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___116_6631.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def1; FStar_Syntax_Syntax.lbattrs = uu___116_6631.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___116_6631.FStar_Syntax_Syntax.lbpos}))))))
in (

let uu____6632 = (fflb lb)
in (bind uu____6632 (fun lb1 -> (

let uu____6642 = (

let uu____6647 = (

let uu____6648 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____6648)::[])
in (FStar_Syntax_Subst.open_term uu____6647 e))
in (match (uu____6642) with
| (bs, e1) -> begin
(

let ff1 = (

let uu____6672 = (FStar_TypeChecker_Env.push_binders env bs)
in (tac_fold_env d f uu____6672))
in (

let uu____6673 = (ff1 e1)
in (bind uu____6673 (fun e2 -> (

let e3 = (FStar_Syntax_Subst.close bs e2)
in (ret (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e3))))))))))
end)))))))
end
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e) -> begin
(

let fflb = (fun lb -> (

let uu____6714 = (ff lb.FStar_Syntax_Syntax.lbdef)
in (bind uu____6714 (fun def -> (ret (

let uu___117_6720 = lb
in {FStar_Syntax_Syntax.lbname = uu___117_6720.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___117_6720.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___117_6720.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___117_6720.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu___117_6720.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___117_6720.FStar_Syntax_Syntax.lbpos}))))))
in (

let uu____6721 = (FStar_Syntax_Subst.open_let_rec lbs e)
in (match (uu____6721) with
| (lbs1, e1) -> begin
(

let uu____6736 = (mapM fflb lbs1)
in (bind uu____6736 (fun lbs2 -> (

let uu____6748 = (ff e1)
in (bind uu____6748 (fun e2 -> (

let uu____6756 = (FStar_Syntax_Subst.close_let_rec lbs2 e2)
in (match (uu____6756) with
| (lbs3, e3) -> begin
(ret (FStar_Syntax_Syntax.Tm_let (((((true), (lbs3))), (e3)))))
end))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, asc, eff) -> begin
(

let uu____6824 = (ff t2)
in (bind uu____6824 (fun t3 -> (ret (FStar_Syntax_Syntax.Tm_ascribed (((t3), (asc), (eff))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t2, m) -> begin
(

let uu____6855 = (ff t2)
in (bind uu____6855 (fun t3 -> (ret (FStar_Syntax_Syntax.Tm_meta (((t3), (m))))))))
end
| uu____6862 -> begin
(ret tn)
end))
in (bind tn1 (fun tn2 -> (

let t' = (

let uu___118_6869 = t1
in {FStar_Syntax_Syntax.n = tn2; FStar_Syntax_Syntax.pos = uu___118_6869.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___118_6869.FStar_Syntax_Syntax.vars})
in (match ((Prims.op_Equality d FStar_Tactics_Types.BottomUp)) with
| true -> begin
(f env t')
end
| uu____6872 -> begin
(ret t')
end)))))))))))


let pointwise_rec : FStar_Tactics_Types.proofstate  ->  unit tac  ->  FStar_Options.optionstate  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun ps tau opts env t -> (

let uu____6906 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____6906) with
| (t1, lcomp, g) -> begin
(

let uu____6918 = ((

let uu____6921 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp)
in (not (uu____6921))) || (

let uu____6923 = (FStar_TypeChecker_Rel.is_trivial g)
in (not (uu____6923))))
in (match (uu____6918) with
| true -> begin
(ret t1)
end
| uu____6926 -> begin
(

let rewrite_eq = (

let typ = lcomp.FStar_Syntax_Syntax.res_typ
in (

let uu____6933 = (new_uvar "pointwise_rec" env typ)
in (bind uu____6933 (fun ut -> ((log ps (fun uu____6944 -> (

let uu____6945 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6946 = (FStar_Syntax_Print.term_to_string ut)
in (FStar_Util.print2 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n" uu____6945 uu____6946)))));
(

let uu____6947 = (

let uu____6950 = (

let uu____6951 = (FStar_TypeChecker_TcTerm.universe_of env typ)
in (FStar_Syntax_Util.mk_eq2 uu____6951 typ t1 ut))
in (add_irrelevant_goal "pointwise_rec equation" env uu____6950 opts))
in (bind uu____6947 (fun uu____6954 -> (

let uu____6955 = (bind tau (fun uu____6961 -> (

let ut1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env ut)
in ((log ps (fun uu____6967 -> (

let uu____6968 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____6969 = (FStar_Syntax_Print.term_to_string ut1)
in (FStar_Util.print2 "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n" uu____6968 uu____6969)))));
(ret ut1);
))))
in (focus uu____6955)))));
)))))
in (

let uu____6970 = (trytac' rewrite_eq)
in (bind uu____6970 (fun x -> (match (x) with
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
| uu____7080 -> begin
c
end))
in (

let maybe_continue = (fun ctrl1 t1 k -> (match ((Prims.op_Equality ctrl1 globalStop)) with
| true -> begin
(ret ((t1), (globalStop)))
end
| uu____7150 -> begin
(match ((Prims.op_Equality ctrl1 proceedToNextSubtree)) with
| true -> begin
(ret ((t1), (keepGoing)))
end
| uu____7167 -> begin
(k t1)
end)
end))
in (

let uu____7168 = (FStar_Syntax_Subst.compress t)
in (maybe_continue ctrl uu____7168 (fun t1 -> (

let uu____7176 = (f env (

let uu___122_7185 = t1
in {FStar_Syntax_Syntax.n = t1.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = uu___122_7185.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___122_7185.FStar_Syntax_Syntax.vars}))
in (bind uu____7176 (fun uu____7201 -> (match (uu____7201) with
| (t2, ctrl1) -> begin
(maybe_continue ctrl1 t2 (fun t3 -> (

let uu____7224 = (

let uu____7225 = (FStar_Syntax_Subst.compress t3)
in uu____7225.FStar_Syntax_Syntax.n)
in (match (uu____7224) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____7258 = (ctrl_tac_fold f env ctrl1 hd1)
in (bind uu____7258 (fun uu____7283 -> (match (uu____7283) with
| (hd2, ctrl2) -> begin
(

let ctrl3 = (keep_going ctrl2)
in (

let uu____7299 = (ctrl_tac_fold_args f env ctrl3 args)
in (bind uu____7299 (fun uu____7326 -> (match (uu____7326) with
| (args1, ctrl4) -> begin
(ret (((

let uu___120_7356 = t3
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app (((hd2), (args1))); FStar_Syntax_Syntax.pos = uu___120_7356.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___120_7356.FStar_Syntax_Syntax.vars})), (ctrl4)))
end)))))
end))))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t4, k) -> begin
(

let uu____7392 = (FStar_Syntax_Subst.open_term bs t4)
in (match (uu____7392) with
| (bs1, t') -> begin
(

let uu____7407 = (

let uu____7414 = (FStar_TypeChecker_Env.push_binders env bs1)
in (ctrl_tac_fold f uu____7414 ctrl1 t'))
in (bind uu____7407 (fun uu____7432 -> (match (uu____7432) with
| (t'', ctrl2) -> begin
(

let uu____7447 = (

let uu____7454 = (

let uu___121_7457 = t4
in (

let uu____7460 = (

let uu____7461 = (

let uu____7478 = (FStar_Syntax_Subst.close_binders bs1)
in (

let uu____7485 = (FStar_Syntax_Subst.close bs1 t'')
in ((uu____7478), (uu____7485), (k))))
in FStar_Syntax_Syntax.Tm_abs (uu____7461))
in {FStar_Syntax_Syntax.n = uu____7460; FStar_Syntax_Syntax.pos = uu___121_7457.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___121_7457.FStar_Syntax_Syntax.vars}))
in ((uu____7454), (ctrl2)))
in (ret uu____7447))
end))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(ret ((t3), (ctrl1)))
end
| uu____7532 -> begin
(ret ((t3), (ctrl1)))
end))))
end))))))))))
and ctrl_tac_fold_args : (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term ctrl_tac)  ->  env  ->  ctrl  ->  FStar_Syntax_Syntax.arg Prims.list  ->  FStar_Syntax_Syntax.arg Prims.list ctrl_tac = (fun f env ctrl ts -> (match (ts) with
| [] -> begin
(ret (([]), (ctrl)))
end
| ((t, q))::ts1 -> begin
(

let uu____7575 = (ctrl_tac_fold f env ctrl t)
in (bind uu____7575 (fun uu____7599 -> (match (uu____7599) with
| (t1, ctrl1) -> begin
(

let uu____7614 = (ctrl_tac_fold_args f env ctrl1 ts1)
in (bind uu____7614 (fun uu____7641 -> (match (uu____7641) with
| (ts2, ctrl2) -> begin
(ret (((((t1), (q)))::ts2), (ctrl2)))
end))))
end))))
end))


let rewrite_rec : FStar_Tactics_Types.proofstate  ->  (FStar_Syntax_Syntax.term  ->  rewrite_result ctrl_tac)  ->  unit tac  ->  FStar_Options.optionstate  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term ctrl_tac = (fun ps ctrl rewriter opts env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let uu____7721 = (

let uu____7728 = (add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true opts)
in (bind uu____7728 (fun uu____7737 -> (

let uu____7738 = (ctrl t1)
in (bind uu____7738 (fun res -> (

let uu____7761 = (trivial ())
in (bind uu____7761 (fun uu____7769 -> (ret res))))))))))
in (bind uu____7721 (fun uu____7785 -> (match (uu____7785) with
| (should_rewrite, ctrl1) -> begin
(match ((not (should_rewrite))) with
| true -> begin
(ret ((t1), (ctrl1)))
end
| uu____7808 -> begin
(

let uu____7809 = (FStar_TypeChecker_TcTerm.tc_term env t1)
in (match (uu____7809) with
| (t2, lcomp, g) -> begin
(

let uu____7825 = ((

let uu____7828 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp)
in (not (uu____7828))) || (

let uu____7830 = (FStar_TypeChecker_Rel.is_trivial g)
in (not (uu____7830))))
in (match (uu____7825) with
| true -> begin
(ret ((t2), (globalStop)))
end
| uu____7841 -> begin
(

let typ = lcomp.FStar_Syntax_Syntax.res_typ
in (

let uu____7845 = (new_uvar "pointwise_rec" env typ)
in (bind uu____7845 (fun ut -> ((log ps (fun uu____7860 -> (

let uu____7861 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____7862 = (FStar_Syntax_Print.term_to_string ut)
in (FStar_Util.print2 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n" uu____7861 uu____7862)))));
(

let uu____7863 = (

let uu____7866 = (

let uu____7867 = (FStar_TypeChecker_TcTerm.universe_of env typ)
in (FStar_Syntax_Util.mk_eq2 uu____7867 typ t2 ut))
in (add_irrelevant_goal "rewrite_rec equation" env uu____7866 opts))
in (bind uu____7863 (fun uu____7874 -> (

let uu____7875 = (bind rewriter (fun uu____7889 -> (

let ut1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env ut)
in ((log ps (fun uu____7895 -> (

let uu____7896 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____7897 = (FStar_Syntax_Print.term_to_string ut1)
in (FStar_Util.print2 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n" uu____7896 uu____7897)))));
(ret ((ut1), (ctrl1)));
))))
in (focus uu____7875)))));
)))))
end))
end))
end)
end))))))


let topdown_rewrite : (FStar_Syntax_Syntax.term  ->  (Prims.bool * FStar_BigInt.t) tac)  ->  unit tac  ->  unit tac = (fun ctrl rewriter -> (bind get (fun ps -> (

let uu____7945 = (match (ps.FStar_Tactics_Types.goals) with
| (g)::gs -> begin
((g), (gs))
end
| [] -> begin
(failwith "Pointwise: no goals")
end)
in (match (uu____7945) with
| (g, gs) -> begin
(

let gt1 = g.FStar_Tactics_Types.goal_ty
in ((log ps (fun uu____7982 -> (

let uu____7983 = (FStar_Syntax_Print.term_to_string gt1)
in (FStar_Util.print1 "Topdown_rewrite starting with %s\n" uu____7983))));
(bind dismiss_all (fun uu____7986 -> (

let uu____7987 = (ctrl_tac_fold (rewrite_rec ps ctrl rewriter g.FStar_Tactics_Types.opts) g.FStar_Tactics_Types.context keepGoing gt1)
in (bind uu____7987 (fun uu____8005 -> (match (uu____8005) with
| (gt', uu____8013) -> begin
((log ps (fun uu____8017 -> (

let uu____8018 = (FStar_Syntax_Print.term_to_string gt')
in (FStar_Util.print1 "Topdown_rewrite seems to have succeded with %s\n" uu____8018))));
(

let uu____8019 = (push_goals gs)
in (bind uu____8019 (fun uu____8023 -> (add_goals (((

let uu___123_8025 = g
in {FStar_Tactics_Types.context = uu___123_8025.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___123_8025.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = gt'; FStar_Tactics_Types.opts = uu___123_8025.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___123_8025.FStar_Tactics_Types.is_guard}))::[])))));
)
end))))));
))
end)))))


let pointwise : FStar_Tactics_Types.direction  ->  unit tac  ->  unit tac = (fun d tau -> (bind get (fun ps -> (

let uu____8051 = (match (ps.FStar_Tactics_Types.goals) with
| (g)::gs -> begin
((g), (gs))
end
| [] -> begin
(failwith "Pointwise: no goals")
end)
in (match (uu____8051) with
| (g, gs) -> begin
(

let gt1 = g.FStar_Tactics_Types.goal_ty
in ((log ps (fun uu____8088 -> (

let uu____8089 = (FStar_Syntax_Print.term_to_string gt1)
in (FStar_Util.print1 "Pointwise starting with %s\n" uu____8089))));
(bind dismiss_all (fun uu____8092 -> (

let uu____8093 = (tac_fold_env d (pointwise_rec ps tau g.FStar_Tactics_Types.opts) g.FStar_Tactics_Types.context gt1)
in (bind uu____8093 (fun gt' -> ((log ps (fun uu____8103 -> (

let uu____8104 = (FStar_Syntax_Print.term_to_string gt')
in (FStar_Util.print1 "Pointwise seems to have succeded with %s\n" uu____8104))));
(

let uu____8105 = (push_goals gs)
in (bind uu____8105 (fun uu____8109 -> (add_goals (((

let uu___124_8111 = g
in {FStar_Tactics_Types.context = uu___124_8111.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___124_8111.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = gt'; FStar_Tactics_Types.opts = uu___124_8111.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___124_8111.FStar_Tactics_Types.is_guard}))::[])))));
))))));
))
end)))))


let trefl : unit  ->  unit tac = (fun uu____8118 -> (

let uu____8121 = (cur_goal ())
in (bind uu____8121 (fun g -> (

let uu____8139 = (FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty)
in (match (uu____8139) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____8145 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____8145) with
| (hd1, args) -> begin
(

let uu____8178 = (

let uu____8189 = (

let uu____8190 = (FStar_Syntax_Util.un_uinst hd1)
in uu____8190.FStar_Syntax_Syntax.n)
in ((uu____8189), (args)))
in (match (uu____8178) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____8202)::((l, uu____8204))::((r, uu____8206))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid) -> begin
(

let uu____8233 = (do_unify g.FStar_Tactics_Types.context l r)
in (bind uu____8233 (fun b -> (match ((not (b))) with
| true -> begin
(

let uu____8242 = (tts g.FStar_Tactics_Types.context l)
in (

let uu____8243 = (tts g.FStar_Tactics_Types.context r)
in (fail2 "trefl: not a trivial equality (%s vs %s)" uu____8242 uu____8243)))
end
| uu____8244 -> begin
(solve g FStar_Syntax_Util.exp_unit)
end))))
end
| (hd2, uu____8246) -> begin
(

let uu____8259 = (tts g.FStar_Tactics_Types.context t)
in (fail1 "trefl: not an equality (%s)" uu____8259))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
(fail "not an irrelevant goal")
end))))))


let dup : unit  ->  unit tac = (fun uu____8266 -> (

let uu____8269 = (cur_goal ())
in (bind uu____8269 (fun g -> (

let uu____8275 = (new_uvar "dup" g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (bind uu____8275 (fun u -> (

let g' = (

let uu___125_8282 = g
in {FStar_Tactics_Types.context = uu___125_8282.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = u; FStar_Tactics_Types.goal_ty = uu___125_8282.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___125_8282.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___125_8282.FStar_Tactics_Types.is_guard})
in (bind __dismiss (fun uu____8285 -> (

let uu____8286 = (

let uu____8289 = (

let uu____8290 = (FStar_TypeChecker_TcTerm.universe_of g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (FStar_Syntax_Util.mk_eq2 uu____8290 g.FStar_Tactics_Types.goal_ty u g.FStar_Tactics_Types.witness))
in (add_irrelevant_goal "dup equation" g.FStar_Tactics_Types.context uu____8289 g.FStar_Tactics_Types.opts))
in (bind uu____8286 (fun uu____8293 -> (

let uu____8294 = (add_goals ((g')::[]))
in (bind uu____8294 (fun uu____8298 -> (ret ())))))))))))))))))


let flip : unit  ->  unit tac = (fun uu____8305 -> (bind get (fun ps -> (match (ps.FStar_Tactics_Types.goals) with
| (g1)::(g2)::gs -> begin
(set (

let uu___126_8322 = ps
in {FStar_Tactics_Types.main_context = uu___126_8322.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___126_8322.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___126_8322.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (g2)::(g1)::gs; FStar_Tactics_Types.smt_goals = uu___126_8322.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___126_8322.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___126_8322.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___126_8322.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___126_8322.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___126_8322.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___126_8322.FStar_Tactics_Types.freshness}))
end
| uu____8323 -> begin
(fail "flip: less than 2 goals")
end))))


let later : unit  ->  unit tac = (fun uu____8332 -> (bind get (fun ps -> (match (ps.FStar_Tactics_Types.goals) with
| [] -> begin
(ret ())
end
| (g)::gs -> begin
(set (

let uu___127_8345 = ps
in {FStar_Tactics_Types.main_context = uu___127_8345.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___127_8345.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___127_8345.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append gs ((g)::[])); FStar_Tactics_Types.smt_goals = uu___127_8345.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___127_8345.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___127_8345.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___127_8345.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___127_8345.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___127_8345.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___127_8345.FStar_Tactics_Types.freshness}))
end))))


let qed : unit  ->  unit tac = (fun uu____8352 -> (bind get (fun ps -> (match (ps.FStar_Tactics_Types.goals) with
| [] -> begin
(ret ())
end
| uu____8359 -> begin
(fail "Not done!")
end))))


let cases : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac = (fun t -> (

let uu____8379 = (

let uu____8386 = (cur_goal ())
in (bind uu____8386 (fun g -> (

let uu____8396 = (__tc g.FStar_Tactics_Types.context t)
in (bind uu____8396 (fun uu____8432 -> (match (uu____8432) with
| (t1, typ, guard) -> begin
(

let uu____8448 = (FStar_Syntax_Util.head_and_args typ)
in (match (uu____8448) with
| (hd1, args) -> begin
(

let uu____8491 = (

let uu____8502 = (

let uu____8503 = (FStar_Syntax_Util.un_uinst hd1)
in uu____8503.FStar_Syntax_Syntax.n)
in ((uu____8502), (args)))
in (match (uu____8491) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____8520))::((q, uu____8522))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid) -> begin
(

let v_p = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p)
in (

let v_q = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None q)
in (

let g1 = (

let uu___128_8544 = g
in (

let uu____8545 = (FStar_TypeChecker_Env.push_bv g.FStar_Tactics_Types.context v_p)
in {FStar_Tactics_Types.context = uu____8545; FStar_Tactics_Types.witness = uu___128_8544.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___128_8544.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___128_8544.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___128_8544.FStar_Tactics_Types.is_guard}))
in (

let g2 = (

let uu___129_8547 = g
in (

let uu____8548 = (FStar_TypeChecker_Env.push_bv g.FStar_Tactics_Types.context v_q)
in {FStar_Tactics_Types.context = uu____8548; FStar_Tactics_Types.witness = uu___129_8547.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___129_8547.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = uu___129_8547.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___129_8547.FStar_Tactics_Types.is_guard}))
in (bind __dismiss (fun uu____8555 -> (

let uu____8556 = (add_goals ((g1)::(g2)::[]))
in (bind uu____8556 (fun uu____8565 -> (

let uu____8566 = (

let uu____8571 = (FStar_Syntax_Syntax.bv_to_name v_p)
in (

let uu____8572 = (FStar_Syntax_Syntax.bv_to_name v_q)
in ((uu____8571), (uu____8572))))
in (ret uu____8566)))))))))))
end
| uu____8577 -> begin
(

let uu____8588 = (tts g.FStar_Tactics_Types.context typ)
in (fail1 "Not a disjunction: %s" uu____8588))
end))
end))
end)))))))
in (FStar_All.pipe_left (wrap_err "cases") uu____8379)))


let set_options : Prims.string  ->  unit tac = (fun s -> (

let uu____8618 = (cur_goal ())
in (bind uu____8618 (fun g -> ((FStar_Options.push ());
(

let uu____8631 = (FStar_Util.smap_copy g.FStar_Tactics_Types.opts)
in (FStar_Options.set uu____8631));
(

let res = (FStar_Options.set_options FStar_Options.Set s)
in (

let opts' = (FStar_Options.peek ())
in ((FStar_Options.pop ());
(match (res) with
| FStar_Getopt.Success -> begin
(

let g' = (

let uu___130_8638 = g
in {FStar_Tactics_Types.context = uu___130_8638.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___130_8638.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = uu___130_8638.FStar_Tactics_Types.goal_ty; FStar_Tactics_Types.opts = opts'; FStar_Tactics_Types.is_guard = uu___130_8638.FStar_Tactics_Types.is_guard})
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


let top_env : unit  ->  env tac = (fun uu____8646 -> (bind get (fun ps -> (FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context))))


let cur_env : unit  ->  env tac = (fun uu____8659 -> (

let uu____8662 = (cur_goal ())
in (bind uu____8662 (fun g -> (FStar_All.pipe_left ret g.FStar_Tactics_Types.context)))))


let cur_goal' : unit  ->  FStar_Syntax_Syntax.term tac = (fun uu____8675 -> (

let uu____8678 = (cur_goal ())
in (bind uu____8678 (fun g -> (FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)))))


let cur_witness : unit  ->  FStar_Syntax_Syntax.term tac = (fun uu____8691 -> (

let uu____8694 = (cur_goal ())
in (bind uu____8694 (fun g -> (FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)))))


let unquote : FStar_Reflection_Data.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun ty tm -> (

let uu____8715 = (

let uu____8718 = (cur_goal ())
in (bind uu____8718 (fun goal -> (

let env = (FStar_TypeChecker_Env.set_expected_typ goal.FStar_Tactics_Types.context ty)
in (

let uu____8726 = (__tc env tm)
in (bind uu____8726 (fun uu____8746 -> (match (uu____8746) with
| (tm1, typ, guard) -> begin
(

let uu____8758 = (proc_guard "unquote" env guard goal.FStar_Tactics_Types.opts)
in (bind uu____8758 (fun uu____8762 -> (ret tm1))))
end))))))))
in (FStar_All.pipe_left (wrap_err "unquote") uu____8715)))


let uvar_env : env  ->  FStar_Reflection_Data.typ FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term tac = (fun env ty -> (

let uu____8785 = (match (ty) with
| FStar_Pervasives_Native.Some (ty1) -> begin
(ret ty1)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8791 = (

let uu____8792 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8792))
in (new_uvar "uvar_env.2" env uu____8791))
end)
in (bind uu____8785 (fun typ -> (

let uu____8804 = (new_uvar "uvar_env" env typ)
in (bind uu____8804 (fun t -> (ret t))))))))


let unshelve : FStar_Syntax_Syntax.term  ->  unit tac = (fun t -> (

let uu____8818 = (bind get (fun ps -> (

let env = ps.FStar_Tactics_Types.main_context
in (

let opts = (match (ps.FStar_Tactics_Types.goals) with
| (g)::uu____8835 -> begin
g.FStar_Tactics_Types.opts
end
| uu____8838 -> begin
(FStar_Options.peek ())
end)
in (

let uu____8841 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____8841) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (ctx_uvar); FStar_Syntax_Syntax.pos = uu____8859; FStar_Syntax_Syntax.vars = uu____8860}, uu____8861) -> begin
(

let env1 = (

let uu___131_8883 = env
in {FStar_TypeChecker_Env.solver = uu___131_8883.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___131_8883.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___131_8883.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_TypeChecker_Env.gamma_sig = uu___131_8883.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___131_8883.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___131_8883.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___131_8883.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___131_8883.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___131_8883.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___131_8883.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___131_8883.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___131_8883.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___131_8883.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___131_8883.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___131_8883.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___131_8883.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___131_8883.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___131_8883.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___131_8883.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___131_8883.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___131_8883.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___131_8883.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___131_8883.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___131_8883.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___131_8883.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___131_8883.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___131_8883.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___131_8883.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___131_8883.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___131_8883.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___131_8883.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___131_8883.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___131_8883.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___131_8883.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___131_8883.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___131_8883.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___131_8883.FStar_TypeChecker_Env.dep_graph})
in (

let uu____8884 = (

let uu____8887 = (

let uu____8888 = (bnorm env1 t)
in (

let uu____8889 = (bnorm env1 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in {FStar_Tactics_Types.context = env1; FStar_Tactics_Types.witness = uu____8888; FStar_Tactics_Types.goal_ty = uu____8889; FStar_Tactics_Types.opts = opts; FStar_Tactics_Types.is_guard = false}))
in (uu____8887)::[])
in (add_goals uu____8884)))
end
| uu____8890 -> begin
(fail "not a uvar")
end))))))
in (FStar_All.pipe_left (wrap_err "unshelve") uu____8818)))


let unify : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun t1 t2 -> (bind get (fun ps -> (do_unify ps.FStar_Tactics_Types.main_context t1 t2))))


let launch_process : Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string tac = (fun prog args input -> (bind idtac (fun uu____8947 -> (

let uu____8948 = (FStar_Options.unsafe_tactic_exec ())
in (match (uu____8948) with
| true -> begin
(

let s = (FStar_Util.launch_process true "tactic_launch" prog args input (fun uu____8954 uu____8955 -> false))
in (ret s))
end
| uu____8956 -> begin
(fail "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
end)))))


let fresh_bv_named : Prims.string  ->  FStar_Reflection_Data.typ  ->  FStar_Syntax_Syntax.bv tac = (fun nm t -> (bind idtac (fun uu____8973 -> (

let uu____8974 = (FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t)
in (ret uu____8974)))))


let change : FStar_Reflection_Data.typ  ->  unit tac = (fun ty -> (

let uu____8984 = (mlog (fun uu____8989 -> (

let uu____8990 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.print1 "change: ty = %s\n" uu____8990))) (fun uu____8993 -> (

let uu____8994 = (cur_goal ())
in (bind uu____8994 (fun g -> (

let uu____9000 = (__tc g.FStar_Tactics_Types.context ty)
in (bind uu____9000 (fun uu____9020 -> (match (uu____9020) with
| (ty1, uu____9030, guard) -> begin
(

let uu____9032 = (proc_guard "change" g.FStar_Tactics_Types.context guard g.FStar_Tactics_Types.opts)
in (bind uu____9032 (fun uu____9037 -> (

let uu____9038 = (do_unify g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty ty1)
in (bind uu____9038 (fun bb -> (match (bb) with
| true -> begin
(replace_cur (

let uu___132_9047 = g
in {FStar_Tactics_Types.context = uu___132_9047.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___132_9047.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = ty1; FStar_Tactics_Types.opts = uu___132_9047.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___132_9047.FStar_Tactics_Types.is_guard}))
end
| uu____9048 -> begin
(

let steps = (FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.UnfoldTac)::(FStar_TypeChecker_Normalize.Unmeta)::[]
in (

let ng = (normalize steps g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty)
in (

let nty = (normalize steps g.FStar_Tactics_Types.context ty1)
in (

let uu____9054 = (do_unify g.FStar_Tactics_Types.context ng nty)
in (bind uu____9054 (fun b -> (match (b) with
| true -> begin
(replace_cur (

let uu___133_9063 = g
in {FStar_Tactics_Types.context = uu___133_9063.FStar_Tactics_Types.context; FStar_Tactics_Types.witness = uu___133_9063.FStar_Tactics_Types.witness; FStar_Tactics_Types.goal_ty = ty1; FStar_Tactics_Types.opts = uu___133_9063.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___133_9063.FStar_Tactics_Types.is_guard}))
end
| uu____9064 -> begin
(fail "not convertible")
end)))))))
end)))))))
end)))))))))
in (FStar_All.pipe_left (wrap_err "change") uu____8984)))


let rec last : 'a . 'a Prims.list  ->  'a = (fun l -> (match (l) with
| [] -> begin
(failwith "last: empty list")
end
| (x)::[] -> begin
x
end
| (uu____9085)::xs -> begin
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

let uu____9113 = (init xs)
in (x)::uu____9113)
end))


let rec inspect : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.term_view tac = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let t2 = (FStar_Syntax_Util.un_uinst t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t3, uu____9130) -> begin
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

let uu____9187 = (last args)
in (match (uu____9187) with
| (a, q) -> begin
(

let q' = (FStar_Reflection_Basic.inspect_aqual q)
in (

let uu____9209 = (

let uu____9210 = (

let uu____9215 = (

let uu____9216 = (

let uu____9221 = (init args)
in (FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9221))
in (uu____9216 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in ((uu____9215), (((a), (q')))))
in FStar_Reflection_Data.Tv_App (uu____9210))
in (FStar_All.pipe_left ret uu____9209)))
end))
end
| FStar_Syntax_Syntax.Tm_abs ([], uu____9234, uu____9235) -> begin
(failwith "inspect: empty arguments on Tm_abs")
end
| FStar_Syntax_Syntax.Tm_abs (bs, t3, k) -> begin
(

let uu____9279 = (FStar_Syntax_Subst.open_term bs t3)
in (match (uu____9279) with
| (bs1, t4) -> begin
(match (bs1) with
| [] -> begin
(failwith "impossible")
end
| (b)::bs2 -> begin
(

let uu____9312 = (

let uu____9313 = (

let uu____9318 = (FStar_Syntax_Util.abs bs2 t4 k)
in ((b), (uu____9318)))
in FStar_Reflection_Data.Tv_Abs (uu____9313))
in (FStar_All.pipe_left ret uu____9312))
end)
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____9321) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type (())))
end
| FStar_Syntax_Syntax.Tm_arrow ([], k) -> begin
(failwith "inspect: empty binders on arrow")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____9341) -> begin
(

let uu____9354 = (FStar_Syntax_Util.arrow_one t2)
in (match (uu____9354) with
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

let uu____9384 = (FStar_Syntax_Subst.open_term ((b)::[]) t3)
in (match (uu____9384) with
| (b', t4) -> begin
(

let b1 = (match (b') with
| (b'1)::[] -> begin
b'1
end
| uu____9423 -> begin
(failwith "impossible")
end)
in (FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Refine ((((FStar_Pervasives_Native.fst b1)), (t4))))))
end)))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____9431 = (

let uu____9432 = (FStar_Reflection_Basic.inspect_const c)
in FStar_Reflection_Data.Tv_Const (uu____9432))
in (FStar_All.pipe_left ret uu____9431))
end
| FStar_Syntax_Syntax.Tm_uvar (ctx_u) -> begin
(

let uu____9436 = (

let uu____9437 = (

let uu____9446 = (

let uu____9447 = (FStar_Syntax_Unionfind.uvar_id ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_BigInt.of_int_fs uu____9447))
in ((uu____9446), (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma), (ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders), (ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)))
in FStar_Reflection_Data.Tv_Uvar (uu____9437))
in (FStar_All.pipe_left ret uu____9436))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), t21) -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| uu____9470 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____9473) -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv) -> begin
(

let b = (FStar_Syntax_Syntax.mk_binder bv)
in (

let uu____9478 = (FStar_Syntax_Subst.open_term ((b)::[]) t21)
in (match (uu____9478) with
| (bs, t22) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____9517 -> begin
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
| uu____9544 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____9547) -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv) -> begin
(

let uu____9551 = (FStar_Syntax_Subst.open_let_rec ((lb)::[]) t21)
in (match (uu____9551) with
| (lbs, t22) -> begin
(match (lbs) with
| (lb1)::[] -> begin
(match (lb1.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____9571) -> begin
(ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv1) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Let (((true), (bv1), (lb1.FStar_Syntax_Syntax.lbdef), (t22)))))
end)
end
| uu____9575 -> begin
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

let uu____9629 = (FStar_Reflection_Basic.inspect_const c)
in FStar_Reflection_Data.Pat_Constant (uu____9629))
end
| FStar_Syntax_Syntax.Pat_cons (fv, ps) -> begin
(

let uu____9648 = (

let uu____9655 = (FStar_List.map (fun uu____9667 -> (match (uu____9667) with
| (p1, uu____9675) -> begin
(inspect_pat p1)
end)) ps)
in ((fv), (uu____9655)))
in FStar_Reflection_Data.Pat_Cons (uu____9648))
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

let brs2 = (FStar_List.map (fun uu___65_9769 -> (match (uu___65_9769) with
| (pat, uu____9791, t4) -> begin
(

let uu____9809 = (inspect_pat pat)
in ((uu____9809), (t4)))
end)) brs1)
in (FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (((t3), (brs2))))))))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| uu____9818 -> begin
((

let uu____9820 = (

let uu____9825 = (

let uu____9826 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____9827 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "inspect: outside of expected syntax (%s, %s)\n" uu____9826 uu____9827)))
in ((FStar_Errors.Warning_CantInspect), (uu____9825)))
in (FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9820));
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown);
)
end))))


let pack : FStar_Reflection_Data.term_view  ->  FStar_Syntax_Syntax.term tac = (fun tv -> (match (tv) with
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____9840 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_left ret uu____9840))
end
| FStar_Reflection_Data.Tv_BVar (bv) -> begin
(

let uu____9844 = (FStar_Syntax_Syntax.bv_to_tm bv)
in (FStar_All.pipe_left ret uu____9844))
end
| FStar_Reflection_Data.Tv_FVar (fv) -> begin
(

let uu____9848 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (FStar_All.pipe_left ret uu____9848))
end
| FStar_Reflection_Data.Tv_App (l, (r, q)) -> begin
(

let q' = (FStar_Reflection_Basic.pack_aqual q)
in (

let uu____9855 = (FStar_Syntax_Util.mk_app l ((((r), (q')))::[]))
in (FStar_All.pipe_left ret uu____9855)))
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

let uu____10173 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((t), (brs2)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____10173))))))
end
| FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) -> begin
(

let uu____10201 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (((FStar_Util.Inl (t)), (tacopt))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____10201))
end
| FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) -> begin
(

let uu____10241 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (((FStar_Util.Inr (c)), (tacopt))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____10241))
end
| FStar_Reflection_Data.Tv_Unknown -> begin
(

let uu____10274 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____10274))
end))


let goal_of_goal_ty : env  ->  FStar_Reflection_Data.typ  ->  (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t) = (fun env typ -> (

let uu____10295 = (FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty" typ.FStar_Syntax_Syntax.pos env typ)
in (match (uu____10295) with
| (u, uu____10313, g_u) -> begin
(

let g = (

let uu____10328 = (FStar_Options.peek ())
in {FStar_Tactics_Types.context = env; FStar_Tactics_Types.witness = u; FStar_Tactics_Types.goal_ty = typ; FStar_Tactics_Types.opts = uu____10328; FStar_Tactics_Types.is_guard = false})
in ((g), (g_u)))
end)))


let proofstate_of_goal_ty : env  ->  FStar_Reflection_Data.typ  ->  (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term) = (fun env typ -> (

let uu____10343 = (goal_of_goal_ty env typ)
in (match (uu____10343) with
| (g, g_u) -> begin
(

let ps = {FStar_Tactics_Types.main_context = env; FStar_Tactics_Types.main_goal = g; FStar_Tactics_Types.all_implicits = g_u.FStar_TypeChecker_Env.implicits; FStar_Tactics_Types.goals = (g)::[]; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = (Prims.parse_int "0"); FStar_Tactics_Types.__dump = (fun ps msg -> (dump_proofstate ps msg)); FStar_Tactics_Types.psc = FStar_TypeChecker_Normalize.null_psc; FStar_Tactics_Types.entry_range = FStar_Range.dummyRange; FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT; FStar_Tactics_Types.freshness = (Prims.parse_int "0")}
in ((ps), (g.FStar_Tactics_Types.witness)))
end)))




