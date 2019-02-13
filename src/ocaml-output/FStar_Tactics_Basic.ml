
open Prims
open FStar_Pervasives

type name =
FStar_Syntax_Syntax.bv


type env =
FStar_TypeChecker_Env.env


type implicits =
FStar_TypeChecker_Env.implicits


let normalize : FStar_TypeChecker_Env.steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (FStar_TypeChecker_Normalize.normalize_with_primitive_steps FStar_Reflection_Interpreter.reflection_primops s e t))


let bnorm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e t -> (normalize [] e t))


let tts : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = FStar_TypeChecker_Normalize.term_to_string


let bnorm_goal : FStar_Tactics_Types.goal  ->  FStar_Tactics_Types.goal = (fun g -> (

let uu____43 = (

let uu____44 = (FStar_Tactics_Types.goal_env g)
in (

let uu____45 = (FStar_Tactics_Types.goal_type g)
in (bnorm uu____44 uu____45)))
in (FStar_Tactics_Types.goal_with_type g uu____43)))

type 'a tac =
{tac_f : FStar_Tactics_Types.proofstate  ->  'a FStar_Tactics_Result.__result}


let __proj__Mktac__item__tac_f : 'a . 'a tac  ->  FStar_Tactics_Types.proofstate  ->  'a FStar_Tactics_Result.__result = (fun projectee -> (match (projectee) with
| {tac_f = tac_f} -> begin
tac_f
end))


let mk_tac : 'a . (FStar_Tactics_Types.proofstate  ->  'a FStar_Tactics_Result.__result)  ->  'a tac = (fun f -> {tac_f = f})


let run : 'a . 'a tac  ->  FStar_Tactics_Types.proofstate  ->  'a FStar_Tactics_Result.__result = (fun t p -> (t.tac_f p))


let run_safe : 'a . 'a tac  ->  FStar_Tactics_Types.proofstate  ->  'a FStar_Tactics_Result.__result = (fun t p -> (

let uu____159 = (FStar_Options.tactics_failhard ())
in (match (uu____159) with
| true -> begin
(run t p)
end
| uu____164 -> begin
(FStar_All.try_with (fun uu___370_169 -> (match (()) with
| () -> begin
(run t p)
end)) (fun uu___369_175 -> (match (uu___369_175) with
| FStar_Errors.Err (uu____178, msg) -> begin
FStar_Tactics_Result.Failed (((FStar_Tactics_Types.TacticFailure (msg)), (p)))
end
| FStar_Errors.Error (uu____182, msg, uu____184) -> begin
FStar_Tactics_Result.Failed (((FStar_Tactics_Types.TacticFailure (msg)), (p)))
end
| e -> begin
FStar_Tactics_Result.Failed (((e), (p)))
end)))
end)))


let rec log : FStar_Tactics_Types.proofstate  ->  (unit  ->  unit)  ->  unit = (fun ps f -> (match (ps.FStar_Tactics_Types.tac_verb_dbg) with
| true -> begin
(f ())
end
| uu____205 -> begin
()
end))


let ret : 'a . 'a  ->  'a tac = (fun x -> (mk_tac (fun p -> FStar_Tactics_Result.Success (((x), (p))))))


let bind : 'a 'b . 'a tac  ->  ('a  ->  'b tac)  ->  'b tac = (fun t1 t2 -> (mk_tac (fun p -> (

let uu____264 = (run t1 p)
in (match (uu____264) with
| FStar_Tactics_Result.Success (a, q) -> begin
(

let uu____271 = (t2 a)
in (run uu____271 q))
end
| FStar_Tactics_Result.Failed (msg, q) -> begin
FStar_Tactics_Result.Failed (((msg), (q)))
end)))))


let get : FStar_Tactics_Types.proofstate tac = (mk_tac (fun p -> FStar_Tactics_Result.Success (((p), (p)))))


let idtac : unit tac = (ret ())


let get_uvar_solved : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun uv -> (

let uu____294 = (FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____294) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))


let check_goal_solved : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun goal -> (get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar))


let goal_to_string_verbose : FStar_Tactics_Types.goal  ->  Prims.string = (fun g -> (

let uu____316 = (FStar_Syntax_Print.ctx_uvar_to_string g.FStar_Tactics_Types.goal_ctx_uvar)
in (

let uu____318 = (

let uu____320 = (check_goal_solved g)
in (match (uu____320) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____326 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____326))
end))
in (FStar_Util.format2 "%s%s\n" uu____316 uu____318))))


let goal_to_string : Prims.string  ->  (Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  FStar_Tactics_Types.proofstate  ->  FStar_Tactics_Types.goal  ->  Prims.string = (fun kind maybe_num ps g -> (

let w = (

let uu____373 = (FStar_Options.print_implicits ())
in (match (uu____373) with
| true -> begin
(

let uu____377 = (FStar_Tactics_Types.goal_env g)
in (

let uu____378 = (FStar_Tactics_Types.goal_witness g)
in (tts uu____377 uu____378)))
end
| uu____379 -> begin
(

let uu____381 = (get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar)
in (match (uu____381) with
| FStar_Pervasives_Native.None -> begin
"_"
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____387 = (FStar_Tactics_Types.goal_env g)
in (

let uu____388 = (FStar_Tactics_Types.goal_witness g)
in (tts uu____387 uu____388)))
end))
end))
in (

let num = (match (maybe_num) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (i, n1) -> begin
(

let uu____411 = (FStar_Util.string_of_int i)
in (

let uu____413 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 " %s/%s" uu____411 uu____413)))
end)
in (

let maybe_label = (match (g.FStar_Tactics_Types.label) with
| "" -> begin
""
end
| l -> begin
(Prims.strcat " (" (Prims.strcat l ")"))
end)
in (

let actual_goal = (match (ps.FStar_Tactics_Types.tac_verb_dbg) with
| true -> begin
(goal_to_string_verbose g)
end
| uu____429 -> begin
(

let uu____431 = (FStar_Syntax_Print.binders_to_string ", " g.FStar_Tactics_Types.goal_ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders)
in (

let uu____434 = (

let uu____436 = (FStar_Tactics_Types.goal_env g)
in (tts uu____436 g.FStar_Tactics_Types.goal_ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ))
in (FStar_Util.format3 "%s |- %s : %s\n" uu____431 w uu____434)))
end)
in (FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal))))))


let tacprint : Prims.string  ->  unit = (fun s -> (FStar_Util.print1 "TAC>> %s\n" s))


let tacprint1 : Prims.string  ->  Prims.string  ->  unit = (fun s x -> (

let uu____463 = (FStar_Util.format1 s x)
in (FStar_Util.print1 "TAC>> %s\n" uu____463)))


let tacprint2 : Prims.string  ->  Prims.string  ->  Prims.string  ->  unit = (fun s x y -> (

let uu____488 = (FStar_Util.format2 s x y)
in (FStar_Util.print1 "TAC>> %s\n" uu____488)))


let tacprint3 : Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  unit = (fun s x y z -> (

let uu____520 = (FStar_Util.format3 s x y z)
in (FStar_Util.print1 "TAC>> %s\n" uu____520)))


let comp_to_typ : FStar_Syntax_Syntax.comp  ->  FStar_Reflection_Data.typ = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____530) -> begin
t
end
| FStar_Syntax_Syntax.GTotal (t, uu____540) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let get_phi : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun g -> (

let uu____560 = (

let uu____561 = (FStar_Tactics_Types.goal_env g)
in (

let uu____562 = (FStar_Tactics_Types.goal_type g)
in (FStar_TypeChecker_Normalize.unfold_whnf uu____561 uu____562)))
in (FStar_Syntax_Util.un_squash uu____560)))


let is_irrelevant : FStar_Tactics_Types.goal  ->  Prims.bool = (fun g -> (

let uu____571 = (get_phi g)
in (FStar_Option.isSome uu____571)))


let print : Prims.string  ->  unit tac = (fun msg -> ((tacprint msg);
(ret ());
))


let debugging : unit  ->  Prims.bool tac = (fun uu____595 -> (bind get (fun ps -> (

let uu____603 = (FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context (FStar_Options.Other ("Tac")))
in (ret uu____603)))))


let ps_to_string : (Prims.string * FStar_Tactics_Types.proofstate)  ->  Prims.string = (fun uu____618 -> (match (uu____618) with
| (msg, ps) -> begin
(

let p_imp = (fun imp -> (FStar_Syntax_Print.uvar_to_string imp.FStar_TypeChecker_Env.imp_uvar.FStar_Syntax_Syntax.ctx_uvar_head))
in (

let n_active = (FStar_List.length ps.FStar_Tactics_Types.goals)
in (

let n_smt = (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
in (

let n1 = (n_active + n_smt)
in (

let uu____650 = (

let uu____654 = (

let uu____658 = (

let uu____660 = (FStar_Util.string_of_int ps.FStar_Tactics_Types.depth)
in (FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____660 msg))
in (

let uu____663 = (

let uu____667 = (match ((Prims.op_disEquality ps.FStar_Tactics_Types.entry_range FStar_Range.dummyRange)) with
| true -> begin
(

let uu____671 = (FStar_Range.string_of_def_range ps.FStar_Tactics_Types.entry_range)
in (FStar_Util.format1 "Location: %s\n" uu____671))
end
| uu____674 -> begin
""
end)
in (

let uu____677 = (

let uu____681 = (

let uu____683 = (FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context (FStar_Options.Other ("Imp")))
in (match (uu____683) with
| true -> begin
(

let uu____688 = (FStar_Common.string_of_list p_imp ps.FStar_Tactics_Types.all_implicits)
in (FStar_Util.format1 "Imps: %s\n" uu____688))
end
| uu____691 -> begin
""
end))
in (uu____681)::[])
in (uu____667)::uu____677))
in (uu____658)::uu____663))
in (

let uu____698 = (

let uu____702 = (FStar_List.mapi (fun i g -> (goal_to_string "Goal" (FStar_Pervasives_Native.Some (((((Prims.parse_int "1") + i)), (n1)))) ps g)) ps.FStar_Tactics_Types.goals)
in (

let uu____722 = (FStar_List.mapi (fun i g -> (goal_to_string "SMT Goal" (FStar_Pervasives_Native.Some ((((((Prims.parse_int "1") + n_active) + i)), (n1)))) ps g)) ps.FStar_Tactics_Types.smt_goals)
in (FStar_List.append uu____702 uu____722)))
in (FStar_List.append uu____654 uu____698)))
in (FStar_String.concat "" uu____650))))))
end))


let goal_to_json : FStar_Tactics_Types.goal  ->  FStar_Util.json = (fun g -> (

let g_binders = (

let uu____756 = (

let uu____757 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Env.all_binders uu____757))
in (

let uu____758 = (

let uu____763 = (

let uu____764 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Env.dsenv uu____764))
in (FStar_Syntax_Print.binders_to_json uu____763))
in (FStar_All.pipe_right uu____756 uu____758)))
in (

let uu____765 = (

let uu____773 = (

let uu____781 = (

let uu____787 = (

let uu____788 = (

let uu____796 = (

let uu____802 = (

let uu____803 = (

let uu____805 = (FStar_Tactics_Types.goal_env g)
in (

let uu____806 = (FStar_Tactics_Types.goal_witness g)
in (tts uu____805 uu____806)))
in FStar_Util.JsonStr (uu____803))
in (("witness"), (uu____802)))
in (

let uu____809 = (

let uu____817 = (

let uu____823 = (

let uu____824 = (

let uu____826 = (FStar_Tactics_Types.goal_env g)
in (

let uu____827 = (FStar_Tactics_Types.goal_type g)
in (tts uu____826 uu____827)))
in FStar_Util.JsonStr (uu____824))
in (("type"), (uu____823)))
in (uu____817)::((("label"), (FStar_Util.JsonStr (g.FStar_Tactics_Types.label))))::[])
in (uu____796)::uu____809))
in FStar_Util.JsonAssoc (uu____788))
in (("goal"), (uu____787)))
in (uu____781)::[])
in ((("hyps"), (g_binders)))::uu____773)
in FStar_Util.JsonAssoc (uu____765))))


let ps_to_json : (Prims.string * FStar_Tactics_Types.proofstate)  ->  FStar_Util.json = (fun uu____881 -> (match (uu____881) with
| (msg, ps) -> begin
(

let uu____891 = (

let uu____899 = (

let uu____907 = (

let uu____915 = (

let uu____923 = (

let uu____929 = (

let uu____930 = (FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals)
in FStar_Util.JsonList (uu____930))
in (("goals"), (uu____929)))
in (

let uu____935 = (

let uu____943 = (

let uu____949 = (

let uu____950 = (FStar_List.map goal_to_json ps.FStar_Tactics_Types.smt_goals)
in FStar_Util.JsonList (uu____950))
in (("smt-goals"), (uu____949)))
in (uu____943)::[])
in (uu____923)::uu____935))
in ((("depth"), (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth))))::uu____915)
in ((("label"), (FStar_Util.JsonStr (msg))))::uu____907)
in (

let uu____984 = (match ((Prims.op_disEquality ps.FStar_Tactics_Types.entry_range FStar_Range.dummyRange)) with
| true -> begin
(

let uu____1000 = (

let uu____1006 = (FStar_Range.json_of_def_range ps.FStar_Tactics_Types.entry_range)
in (("location"), (uu____1006)))
in (uu____1000)::[])
end
| uu____1019 -> begin
[]
end)
in (FStar_List.append uu____899 uu____984)))
in FStar_Util.JsonAssoc (uu____891))
end))


let dump_proofstate : FStar_Tactics_Types.proofstate  ->  Prims.string  ->  unit = (fun ps msg -> (FStar_Options.with_saved_options (fun uu____1046 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(FStar_Util.print_generic "proof-state" ps_to_string ps_to_json ((msg), (ps)));
))))


let print_proof_state : Prims.string  ->  unit tac = (fun msg -> (mk_tac (fun ps -> (

let psc = ps.FStar_Tactics_Types.psc
in (

let subst1 = (FStar_TypeChecker_Cfg.psc_subst psc)
in ((

let uu____1077 = (FStar_Tactics_Types.subst_proof_state subst1 ps)
in (dump_proofstate uu____1077 msg));
FStar_Tactics_Result.Success (((()), (ps)));
))))))


let mlog : 'a . (unit  ->  unit)  ->  (unit  ->  'a tac)  ->  'a tac = (fun f cont -> (bind get (fun ps -> ((log ps f);
(cont ());
))))


let traise : 'a . Prims.exn  ->  'a tac = (fun e -> (mk_tac (fun ps -> FStar_Tactics_Result.Failed (((e), (ps))))))


let fail : 'a . Prims.string  ->  'a tac = (fun msg -> (mk_tac (fun ps -> ((

let uu____1150 = (FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context (FStar_Options.Other ("TacFail")))
in (match (uu____1150) with
| true -> begin
(dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg))
end
| uu____1155 -> begin
()
end));
FStar_Tactics_Result.Failed (((FStar_Tactics_Types.TacticFailure (msg)), (ps)));
))))


let fail1 : 'Auu____1164 . Prims.string  ->  Prims.string  ->  'Auu____1164 tac = (fun msg x -> (

let uu____1181 = (FStar_Util.format1 msg x)
in (fail uu____1181)))


let fail2 : 'Auu____1192 . Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____1192 tac = (fun msg x y -> (

let uu____1216 = (FStar_Util.format2 msg x y)
in (fail uu____1216)))


let fail3 : 'Auu____1229 . Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____1229 tac = (fun msg x y z -> (

let uu____1260 = (FStar_Util.format3 msg x y z)
in (fail uu____1260)))


let fail4 : 'Auu____1275 . Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____1275 tac = (fun msg x y z w -> (

let uu____1313 = (FStar_Util.format4 msg x y z w)
in (fail uu____1313)))


let catch : 'a . 'a tac  ->  (Prims.exn, 'a) FStar_Util.either tac = (fun t -> (mk_tac (fun ps -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____1348 = (run t ps)
in (match (uu____1348) with
| FStar_Tactics_Result.Success (a, q) -> begin
((FStar_Syntax_Unionfind.commit tx);
FStar_Tactics_Result.Success (((FStar_Util.Inr (a)), (q)));
)
end
| FStar_Tactics_Result.Failed (m, q) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(

let ps1 = (

let uu___371_1372 = ps
in {FStar_Tactics_Types.main_context = uu___371_1372.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___371_1372.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___371_1372.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___371_1372.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___371_1372.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___371_1372.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___371_1372.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___371_1372.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___371_1372.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___371_1372.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = q.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___371_1372.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___371_1372.FStar_Tactics_Types.local_state})
in FStar_Tactics_Result.Success (((FStar_Util.Inl (m)), (ps1))));
)
end))))))


let recover : 'a . 'a tac  ->  (Prims.exn, 'a) FStar_Util.either tac = (fun t -> (mk_tac (fun ps -> (

let uu____1411 = (run t ps)
in (match (uu____1411) with
| FStar_Tactics_Result.Success (a, q) -> begin
FStar_Tactics_Result.Success (((FStar_Util.Inr (a)), (q)))
end
| FStar_Tactics_Result.Failed (m, q) -> begin
FStar_Tactics_Result.Success (((FStar_Util.Inl (m)), (q)))
end)))))


let trytac : 'a . 'a tac  ->  'a FStar_Pervasives_Native.option tac = (fun t -> (

let uu____1459 = (catch t)
in (bind uu____1459 (fun r -> (match (r) with
| FStar_Util.Inr (v1) -> begin
(ret (FStar_Pervasives_Native.Some (v1)))
end
| FStar_Util.Inl (uu____1486) -> begin
(ret FStar_Pervasives_Native.None)
end)))))


let trytac_exn : 'a . 'a tac  ->  'a FStar_Pervasives_Native.option tac = (fun t -> (mk_tac (fun ps -> (FStar_All.try_with (fun uu___373_1518 -> (match (()) with
| () -> begin
(

let uu____1523 = (trytac t)
in (run uu____1523 ps))
end)) (fun uu___372_1534 -> (match (uu___372_1534) with
| FStar_Errors.Err (uu____1539, msg) -> begin
((log ps (fun uu____1545 -> (FStar_Util.print1 "trytac_exn error: (%s)" msg)));
FStar_Tactics_Result.Success (((FStar_Pervasives_Native.None), (ps)));
)
end
| FStar_Errors.Error (uu____1551, msg, uu____1553) -> begin
((log ps (fun uu____1558 -> (FStar_Util.print1 "trytac_exn error: (%s)" msg)));
FStar_Tactics_Result.Success (((FStar_Pervasives_Native.None), (ps)));
)
end))))))


let wrap_err : 'a . Prims.string  ->  'a tac  ->  'a tac = (fun pref t -> (mk_tac (fun ps -> (

let uu____1595 = (run t ps)
in (match (uu____1595) with
| FStar_Tactics_Result.Success (a, q) -> begin
FStar_Tactics_Result.Success (((a), (q)))
end
| FStar_Tactics_Result.Failed (FStar_Tactics_Types.TacticFailure (msg), q) -> begin
FStar_Tactics_Result.Failed (((FStar_Tactics_Types.TacticFailure ((Prims.strcat pref (Prims.strcat ": " msg)))), (q)))
end
| FStar_Tactics_Result.Failed (e, q) -> begin
FStar_Tactics_Result.Failed (((e), (q)))
end)))))


let set : FStar_Tactics_Types.proofstate  ->  unit tac = (fun p -> (mk_tac (fun uu____1619 -> FStar_Tactics_Result.Success (((()), (p))))))


let add_implicits : implicits  ->  unit tac = (fun i -> (bind get (fun p -> (set (

let uu___374_1634 = p
in {FStar_Tactics_Types.main_context = uu___374_1634.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___374_1634.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = (FStar_List.append i p.FStar_Tactics_Types.all_implicits); FStar_Tactics_Types.goals = uu___374_1634.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___374_1634.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___374_1634.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___374_1634.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___374_1634.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___374_1634.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___374_1634.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___374_1634.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___374_1634.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___374_1634.FStar_Tactics_Types.local_state})))))


let __do_unify : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun env t1 t2 -> ((

let uu____1658 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1658) with
| true -> begin
(

let uu____1662 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1664 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1662 uu____1664)))
end
| uu____1667 -> begin
()
end));
(FStar_All.try_with (fun uu___376_1675 -> (match (()) with
| () -> begin
(

let res = (FStar_TypeChecker_Rel.teq_nosmt env t1 t2)
in ((

let uu____1683 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1683) with
| true -> begin
(

let uu____1687 = (FStar_Common.string_of_option (FStar_TypeChecker_Rel.guard_to_string env) res)
in (

let uu____1689 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1691 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1687 uu____1689 uu____1691))))
end
| uu____1694 -> begin
()
end));
(match (res) with
| FStar_Pervasives_Native.None -> begin
(ret false)
end
| FStar_Pervasives_Native.Some (g) -> begin
(

let uu____1702 = (add_implicits g.FStar_TypeChecker_Env.implicits)
in (bind uu____1702 (fun uu____1707 -> (ret true))))
end);
))
end)) (fun uu___375_1713 -> (match (uu___375_1713) with
| FStar_Errors.Err (uu____1717, msg) -> begin
(mlog (fun uu____1723 -> (FStar_Util.print1 ">> do_unify error, (%s)\n" msg)) (fun uu____1726 -> (ret false)))
end
| FStar_Errors.Error (uu____1729, msg, r) -> begin
(mlog (fun uu____1737 -> (

let uu____1738 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg uu____1738))) (fun uu____1742 -> (ret false)))
end)));
))


let compress_implicits : unit tac = (bind get (fun ps -> (

let imps = ps.FStar_Tactics_Types.all_implicits
in (

let g = (

let uu___377_1756 = FStar_TypeChecker_Env.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___377_1756.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___377_1756.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___377_1756.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = imps})
in (

let g1 = (FStar_TypeChecker_Rel.resolve_implicits_tac ps.FStar_Tactics_Types.main_context g)
in (

let ps' = (

let uu___378_1759 = ps
in {FStar_Tactics_Types.main_context = uu___378_1759.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___378_1759.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = g1.FStar_TypeChecker_Env.implicits; FStar_Tactics_Types.goals = uu___378_1759.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___378_1759.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___378_1759.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___378_1759.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___378_1759.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___378_1759.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___378_1759.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___378_1759.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___378_1759.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___378_1759.FStar_Tactics_Types.local_state})
in (set ps')))))))


let do_unify : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun env t1 t2 -> (bind idtac (fun uu____1786 -> ((

let uu____1788 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1788) with
| true -> begin
((FStar_Options.push ());
(

let uu____1793 = (FStar_Options.set_options FStar_Options.Set "--debug_level Rel --debug_level RelCheck")
in ());
)
end
| uu____1795 -> begin
()
end));
(

let uu____1797 = (__do_unify env t1 t2)
in (bind uu____1797 (fun r -> ((

let uu____1808 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1808) with
| true -> begin
(FStar_Options.pop ())
end
| uu____1812 -> begin
()
end));
(ret r);
))));
))))


let remove_solved_goals : unit tac = (bind get (fun ps -> (

let ps' = (

let uu___379_1822 = ps
in (

let uu____1823 = (FStar_List.filter (fun g -> (

let uu____1829 = (check_goal_solved g)
in (FStar_Option.isNone uu____1829))) ps.FStar_Tactics_Types.goals)
in {FStar_Tactics_Types.main_context = uu___379_1822.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___379_1822.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___379_1822.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu____1823; FStar_Tactics_Types.smt_goals = uu___379_1822.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___379_1822.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___379_1822.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___379_1822.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___379_1822.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___379_1822.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___379_1822.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___379_1822.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___379_1822.FStar_Tactics_Types.local_state}))
in (set ps'))))


let set_solution : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun goal solution -> (

let uu____1847 = (FStar_Syntax_Unionfind.find goal.FStar_Tactics_Types.goal_ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____1847) with
| FStar_Pervasives_Native.Some (uu____1852) -> begin
(

let uu____1853 = (

let uu____1855 = (goal_to_string_verbose goal)
in (FStar_Util.format1 "Goal %s is already solved" uu____1855))
in (fail uu____1853))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Syntax_Unionfind.change goal.FStar_Tactics_Types.goal_ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head solution);
(ret ());
)
end)))


let trysolve : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun goal solution -> (

let uu____1876 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____1877 = (FStar_Tactics_Types.goal_witness goal)
in (do_unify uu____1876 solution uu____1877))))


let __dismiss : unit tac = (bind get (fun p -> (

let uu____1884 = (

let uu___380_1885 = p
in (

let uu____1886 = (FStar_List.tl p.FStar_Tactics_Types.goals)
in {FStar_Tactics_Types.main_context = uu___380_1885.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___380_1885.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___380_1885.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu____1886; FStar_Tactics_Types.smt_goals = uu___380_1885.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___380_1885.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___380_1885.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___380_1885.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___380_1885.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___380_1885.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___380_1885.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___380_1885.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___380_1885.FStar_Tactics_Types.local_state}))
in (set uu____1884))))


let solve : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun goal solution -> (

let e = (FStar_Tactics_Types.goal_env goal)
in (mlog (fun uu____1908 -> (

let uu____1909 = (

let uu____1911 = (FStar_Tactics_Types.goal_witness goal)
in (FStar_Syntax_Print.term_to_string uu____1911))
in (

let uu____1912 = (FStar_Syntax_Print.term_to_string solution)
in (FStar_Util.print2 "solve %s := %s\n" uu____1909 uu____1912)))) (fun uu____1917 -> (

let uu____1918 = (trysolve goal solution)
in (bind uu____1918 (fun b -> (match (b) with
| true -> begin
(bind __dismiss (fun uu____1930 -> remove_solved_goals))
end
| uu____1931 -> begin
(

let uu____1933 = (

let uu____1935 = (

let uu____1937 = (FStar_Tactics_Types.goal_env goal)
in (tts uu____1937 solution))
in (

let uu____1938 = (

let uu____1940 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____1941 = (FStar_Tactics_Types.goal_witness goal)
in (tts uu____1940 uu____1941)))
in (

let uu____1942 = (

let uu____1944 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____1945 = (FStar_Tactics_Types.goal_type goal)
in (tts uu____1944 uu____1945)))
in (FStar_Util.format3 "%s does not solve %s : %s" uu____1935 uu____1938 uu____1942))))
in (fail uu____1933))
end))))))))


let solve' : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun goal solution -> (

let uu____1962 = (set_solution goal solution)
in (bind uu____1962 (fun uu____1966 -> (bind __dismiss (fun uu____1968 -> remove_solved_goals))))))


let set_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun ps -> (set (

let uu___381_1987 = ps
in {FStar_Tactics_Types.main_context = uu___381_1987.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___381_1987.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___381_1987.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = gs; FStar_Tactics_Types.smt_goals = uu___381_1987.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___381_1987.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___381_1987.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___381_1987.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___381_1987.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___381_1987.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___381_1987.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___381_1987.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___381_1987.FStar_Tactics_Types.local_state})))))


let set_smt_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun ps -> (set (

let uu___382_2006 = ps
in {FStar_Tactics_Types.main_context = uu___382_2006.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___382_2006.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___382_2006.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___382_2006.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = gs; FStar_Tactics_Types.depth = uu___382_2006.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___382_2006.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___382_2006.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___382_2006.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___382_2006.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___382_2006.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___382_2006.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___382_2006.FStar_Tactics_Types.local_state})))))


let dismiss_all : unit tac = (set_goals [])


let nwarn : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let check_valid_goal : FStar_Tactics_Types.goal  ->  unit = (fun g -> (

let uu____2033 = (FStar_Options.defensive ())
in (match (uu____2033) with
| true -> begin
(

let b = true
in (

let env = (FStar_Tactics_Types.goal_env g)
in (

let b1 = (b && (

let uu____2043 = (FStar_Tactics_Types.goal_witness g)
in (FStar_TypeChecker_Env.closed env uu____2043)))
in (

let b2 = (b1 && (

let uu____2047 = (FStar_Tactics_Types.goal_type g)
in (FStar_TypeChecker_Env.closed env uu____2047)))
in (

let rec aux = (fun b3 e -> (

let uu____2062 = (FStar_TypeChecker_Env.pop_bv e)
in (match (uu____2062) with
| FStar_Pervasives_Native.None -> begin
b3
end
| FStar_Pervasives_Native.Some (bv, e1) -> begin
(

let b4 = (b3 && (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort))
in (aux b4 e1))
end)))
in (

let uu____2082 = ((

let uu____2086 = (aux b2 env)
in (not (uu____2086))) && (

let uu____2089 = (FStar_ST.op_Bang nwarn)
in (uu____2089 < (Prims.parse_int "5"))))
in (match (uu____2082) with
| true -> begin
((

let uu____2115 = (

let uu____2116 = (FStar_Tactics_Types.goal_type g)
in uu____2116.FStar_Syntax_Syntax.pos)
in (

let uu____2119 = (

let uu____2125 = (

let uu____2127 = (goal_to_string_verbose g)
in (FStar_Util.format1 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n" uu____2127))
in ((FStar_Errors.Warning_IllFormedGoal), (uu____2125)))
in (FStar_Errors.log_issue uu____2115 uu____2119)));
(

let uu____2131 = (

let uu____2133 = (FStar_ST.op_Bang nwarn)
in (uu____2133 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals nwarn uu____2131));
)
end
| uu____2178 -> begin
()
end)))))))
end
| uu____2180 -> begin
()
end)))


let add_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___383_2202 = p
in {FStar_Tactics_Types.main_context = uu___383_2202.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___383_2202.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___383_2202.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append gs p.FStar_Tactics_Types.goals); FStar_Tactics_Types.smt_goals = uu___383_2202.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___383_2202.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___383_2202.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___383_2202.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___383_2202.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___383_2202.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___383_2202.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___383_2202.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___383_2202.FStar_Tactics_Types.local_state}));
))))


let add_smt_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___384_2223 = p
in {FStar_Tactics_Types.main_context = uu___384_2223.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___384_2223.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___384_2223.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___384_2223.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = (FStar_List.append gs p.FStar_Tactics_Types.smt_goals); FStar_Tactics_Types.depth = uu___384_2223.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___384_2223.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___384_2223.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___384_2223.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___384_2223.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___384_2223.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___384_2223.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___384_2223.FStar_Tactics_Types.local_state}));
))))


let push_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___385_2244 = p
in {FStar_Tactics_Types.main_context = uu___385_2244.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___385_2244.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___385_2244.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append p.FStar_Tactics_Types.goals gs); FStar_Tactics_Types.smt_goals = uu___385_2244.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___385_2244.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___385_2244.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___385_2244.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___385_2244.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___385_2244.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___385_2244.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___385_2244.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___385_2244.FStar_Tactics_Types.local_state}));
))))


let push_smt_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___386_2265 = p
in {FStar_Tactics_Types.main_context = uu___386_2265.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___386_2265.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___386_2265.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___386_2265.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = (FStar_List.append p.FStar_Tactics_Types.smt_goals gs); FStar_Tactics_Types.depth = uu___386_2265.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___386_2265.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___386_2265.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___386_2265.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___386_2265.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___386_2265.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___386_2265.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___386_2265.FStar_Tactics_Types.local_state}));
))))


let replace_cur : FStar_Tactics_Types.goal  ->  unit tac = (fun g -> (bind __dismiss (fun uu____2277 -> (add_goals ((g)::[])))))


let new_uvar : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac = (fun reason env typ -> (

let uu____2308 = (FStar_TypeChecker_Env.new_implicit_var_aux reason typ.FStar_Syntax_Syntax.pos env typ FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None)
in (match (uu____2308) with
| (u, ctx_uvar, g_u) -> begin
(

let uu____2346 = (add_implicits g_u.FStar_TypeChecker_Env.implicits)
in (bind uu____2346 (fun uu____2355 -> (

let uu____2356 = (

let uu____2361 = (

let uu____2362 = (FStar_List.hd ctx_uvar)
in (FStar_Pervasives_Native.fst uu____2362))
in ((u), (uu____2361)))
in (ret uu____2356)))))
end)))


let is_true : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____2383 = (FStar_Syntax_Util.un_squash t1)
in (match (uu____2383) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let t'1 = (FStar_Syntax_Util.unascribe t')
in (

let uu____2395 = (

let uu____2396 = (FStar_Syntax_Subst.compress t'1)
in uu____2396.FStar_Syntax_Syntax.n)
in (match (uu____2395) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)
end
| uu____2401 -> begin
false
end)))
end
| uu____2403 -> begin
false
end))))


let is_false : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____2416 = (FStar_Syntax_Util.un_squash t)
in (match (uu____2416) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____2427 = (

let uu____2428 = (FStar_Syntax_Subst.compress t')
in uu____2428.FStar_Syntax_Syntax.n)
in (match (uu____2427) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid)
end
| uu____2433 -> begin
false
end))
end
| uu____2435 -> begin
false
end)))


let cur_goal : unit  ->  FStar_Tactics_Types.goal tac = (fun uu____2448 -> (bind get (fun p -> (match (p.FStar_Tactics_Types.goals) with
| [] -> begin
(fail "No more goals (1)")
end
| (hd1)::tl1 -> begin
(

let uu____2460 = (FStar_Syntax_Unionfind.find hd1.FStar_Tactics_Types.goal_ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____2460) with
| FStar_Pervasives_Native.None -> begin
(ret hd1)
end
| FStar_Pervasives_Native.Some (t) -> begin
((

let uu____2467 = (goal_to_string_verbose hd1)
in (

let uu____2469 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n" uu____2467 uu____2469)));
(ret hd1);
)
end))
end))))


let tadmit_t : FStar_Syntax_Syntax.term  ->  unit tac = (fun t -> (

let uu____2482 = (bind get (fun ps -> (

let uu____2488 = (cur_goal ())
in (bind uu____2488 (fun g -> ((

let uu____2495 = (

let uu____2496 = (FStar_Tactics_Types.goal_type g)
in uu____2496.FStar_Syntax_Syntax.pos)
in (

let uu____2499 = (

let uu____2505 = (

let uu____2507 = (goal_to_string "" FStar_Pervasives_Native.None ps g)
in (FStar_Util.format1 "Tactics admitted goal <%s>\n\n" uu____2507))
in ((FStar_Errors.Warning_TacAdmit), (uu____2505)))
in (FStar_Errors.log_issue uu____2495 uu____2499)));
(solve' g t);
))))))
in (FStar_All.pipe_left (wrap_err "tadmit_t") uu____2482)))


let fresh : unit  ->  FStar_BigInt.t tac = (fun uu____2530 -> (bind get (fun ps -> (

let n1 = ps.FStar_Tactics_Types.freshness
in (

let ps1 = (

let uu___387_2541 = ps
in {FStar_Tactics_Types.main_context = uu___387_2541.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___387_2541.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___387_2541.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___387_2541.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___387_2541.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___387_2541.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___387_2541.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___387_2541.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___387_2541.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___387_2541.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1")); FStar_Tactics_Types.tac_verb_dbg = uu___387_2541.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___387_2541.FStar_Tactics_Types.local_state})
in (

let uu____2543 = (set ps1)
in (bind uu____2543 (fun uu____2548 -> (

let uu____2549 = (FStar_BigInt.of_int_fs n1)
in (ret uu____2549))))))))))


let mk_irrelevant_goal : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  FStar_Options.optionstate  ->  Prims.string  ->  FStar_Tactics_Types.goal tac = (fun reason env phi opts label1 -> (

let typ = (

let uu____2587 = (env.FStar_TypeChecker_Env.universe_of env phi)
in (FStar_Syntax_Util.mk_squash uu____2587 phi))
in (

let uu____2588 = (new_uvar reason env typ)
in (bind uu____2588 (fun uu____2603 -> (match (uu____2603) with
| (uu____2610, ctx_uvar) -> begin
(

let goal = (FStar_Tactics_Types.mk_goal env ctx_uvar opts false label1)
in (ret goal))
end))))))


let __tc : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ * FStar_TypeChecker_Env.guard_t) tac = (fun e t -> (bind get (fun ps -> (mlog (fun uu____2657 -> (

let uu____2658 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Tac> __tc(%s)\n" uu____2658))) (fun uu____2663 -> (

let e1 = (

let uu___388_2665 = e
in {FStar_TypeChecker_Env.solver = uu___388_2665.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___388_2665.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___388_2665.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___388_2665.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___388_2665.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___388_2665.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___388_2665.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___388_2665.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___388_2665.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___388_2665.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___388_2665.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___388_2665.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___388_2665.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___388_2665.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___388_2665.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___388_2665.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___388_2665.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___388_2665.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___388_2665.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___388_2665.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___388_2665.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___388_2665.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___388_2665.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___388_2665.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___388_2665.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = false; FStar_TypeChecker_Env.tc_term = uu___388_2665.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___388_2665.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___388_2665.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___388_2665.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___388_2665.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___388_2665.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___388_2665.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___388_2665.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___388_2665.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___388_2665.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___388_2665.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___388_2665.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___388_2665.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___388_2665.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___388_2665.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___388_2665.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___388_2665.FStar_TypeChecker_Env.nbe})
in (FStar_All.try_with (fun uu___390_2677 -> (match (()) with
| () -> begin
(

let uu____2686 = (FStar_TypeChecker_TcTerm.type_of_tot_term e1 t)
in (ret uu____2686))
end)) (fun uu___389_2704 -> (match (uu___389_2704) with
| FStar_Errors.Err (uu____2713, msg) -> begin
(

let uu____2717 = (tts e1 t)
in (

let uu____2719 = (

let uu____2721 = (FStar_TypeChecker_Env.all_binders e1)
in (FStar_All.pipe_right uu____2721 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____2717 uu____2719 msg)))
end
| FStar_Errors.Error (uu____2731, msg, uu____2733) -> begin
(

let uu____2736 = (tts e1 t)
in (

let uu____2738 = (

let uu____2740 = (FStar_TypeChecker_Env.all_binders e1)
in (FStar_All.pipe_right uu____2740 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____2736 uu____2738 msg)))
end)))))))))


let __tc_ghost : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ * FStar_TypeChecker_Env.guard_t) tac = (fun e t -> (bind get (fun ps -> (mlog (fun uu____2793 -> (

let uu____2794 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____2794))) (fun uu____2799 -> (

let e1 = (

let uu___391_2801 = e
in {FStar_TypeChecker_Env.solver = uu___391_2801.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___391_2801.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___391_2801.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___391_2801.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___391_2801.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___391_2801.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___391_2801.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___391_2801.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___391_2801.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___391_2801.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___391_2801.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___391_2801.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___391_2801.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___391_2801.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___391_2801.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___391_2801.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___391_2801.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___391_2801.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___391_2801.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___391_2801.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___391_2801.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___391_2801.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___391_2801.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___391_2801.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___391_2801.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = false; FStar_TypeChecker_Env.tc_term = uu___391_2801.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___391_2801.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___391_2801.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___391_2801.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___391_2801.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___391_2801.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___391_2801.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___391_2801.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___391_2801.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___391_2801.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___391_2801.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___391_2801.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___391_2801.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___391_2801.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___391_2801.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___391_2801.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___391_2801.FStar_TypeChecker_Env.nbe})
in (FStar_All.try_with (fun uu___393_2816 -> (match (()) with
| () -> begin
(

let uu____2825 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t)
in (match (uu____2825) with
| (t1, lc, g) -> begin
(ret ((t1), (lc.FStar_Syntax_Syntax.res_typ), (g)))
end))
end)) (fun uu___392_2854 -> (match (uu___392_2854) with
| FStar_Errors.Err (uu____2863, msg) -> begin
(

let uu____2867 = (tts e1 t)
in (

let uu____2869 = (

let uu____2871 = (FStar_TypeChecker_Env.all_binders e1)
in (FStar_All.pipe_right uu____2871 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____2867 uu____2869 msg)))
end
| FStar_Errors.Error (uu____2881, msg, uu____2883) -> begin
(

let uu____2886 = (tts e1 t)
in (

let uu____2888 = (

let uu____2890 = (FStar_TypeChecker_Env.all_binders e1)
in (FStar_All.pipe_right uu____2890 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____2886 uu____2888 msg)))
end)))))))))


let __tc_lax : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ * FStar_TypeChecker_Env.guard_t) tac = (fun e t -> (bind get (fun ps -> (mlog (fun uu____2943 -> (

let uu____2944 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Tac> __tc(%s)\n" uu____2944))) (fun uu____2950 -> (

let e1 = (

let uu___394_2952 = e
in {FStar_TypeChecker_Env.solver = uu___394_2952.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___394_2952.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___394_2952.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___394_2952.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___394_2952.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___394_2952.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___394_2952.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___394_2952.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___394_2952.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___394_2952.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___394_2952.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___394_2952.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___394_2952.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___394_2952.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___394_2952.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___394_2952.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___394_2952.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___394_2952.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___394_2952.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___394_2952.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___394_2952.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___394_2952.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___394_2952.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___394_2952.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___394_2952.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = false; FStar_TypeChecker_Env.tc_term = uu___394_2952.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___394_2952.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___394_2952.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___394_2952.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___394_2952.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___394_2952.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___394_2952.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___394_2952.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___394_2952.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___394_2952.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___394_2952.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___394_2952.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___394_2952.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___394_2952.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___394_2952.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___394_2952.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___394_2952.FStar_TypeChecker_Env.nbe})
in (

let e2 = (

let uu___395_2955 = e1
in {FStar_TypeChecker_Env.solver = uu___395_2955.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___395_2955.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___395_2955.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___395_2955.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___395_2955.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___395_2955.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___395_2955.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___395_2955.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___395_2955.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___395_2955.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___395_2955.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___395_2955.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___395_2955.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___395_2955.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___395_2955.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___395_2955.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___395_2955.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___395_2955.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___395_2955.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___395_2955.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___395_2955.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___395_2955.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___395_2955.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___395_2955.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___395_2955.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___395_2955.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___395_2955.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___395_2955.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___395_2955.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___395_2955.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___395_2955.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___395_2955.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___395_2955.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___395_2955.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___395_2955.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___395_2955.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___395_2955.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___395_2955.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___395_2955.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___395_2955.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___395_2955.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___395_2955.FStar_TypeChecker_Env.nbe})
in (FStar_All.try_with (fun uu___397_2970 -> (match (()) with
| () -> begin
(

let uu____2979 = (FStar_TypeChecker_TcTerm.tc_term e2 t)
in (match (uu____2979) with
| (t1, lc, g) -> begin
(ret ((t1), (lc.FStar_Syntax_Syntax.res_typ), (g)))
end))
end)) (fun uu___396_3008 -> (match (uu___396_3008) with
| FStar_Errors.Err (uu____3017, msg) -> begin
(

let uu____3021 = (tts e2 t)
in (

let uu____3023 = (

let uu____3025 = (FStar_TypeChecker_Env.all_binders e2)
in (FStar_All.pipe_right uu____3025 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____3021 uu____3023 msg)))
end
| FStar_Errors.Error (uu____3035, msg, uu____3037) -> begin
(

let uu____3040 = (tts e2 t)
in (

let uu____3042 = (

let uu____3044 = (FStar_TypeChecker_Env.all_binders e2)
in (FStar_All.pipe_right uu____3044 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____3040 uu____3042 msg)))
end))))))))))


let istrivial : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e t -> (

let steps = (FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Simplify)::(FStar_TypeChecker_Env.UnfoldTac)::(FStar_TypeChecker_Env.Unmeta)::[]
in (

let t1 = (normalize steps e t)
in (is_true t1))))


let get_guard_policy : unit  ->  FStar_Tactics_Types.guard_policy tac = (fun uu____3078 -> (bind get (fun ps -> (ret ps.FStar_Tactics_Types.guard_policy))))


let set_guard_policy : FStar_Tactics_Types.guard_policy  ->  unit tac = (fun pol -> (bind get (fun ps -> (set (

let uu___398_3097 = ps
in {FStar_Tactics_Types.main_context = uu___398_3097.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___398_3097.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___398_3097.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___398_3097.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___398_3097.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___398_3097.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___398_3097.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___398_3097.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___398_3097.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = pol; FStar_Tactics_Types.freshness = uu___398_3097.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___398_3097.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___398_3097.FStar_Tactics_Types.local_state})))))


let with_policy : 'a . FStar_Tactics_Types.guard_policy  ->  'a tac  ->  'a tac = (fun pol t -> (

let uu____3122 = (get_guard_policy ())
in (bind uu____3122 (fun old_pol -> (

let uu____3128 = (set_guard_policy pol)
in (bind uu____3128 (fun uu____3132 -> (bind t (fun r -> (

let uu____3136 = (set_guard_policy old_pol)
in (bind uu____3136 (fun uu____3140 -> (ret r)))))))))))))


let getopts : FStar_Options.optionstate tac = (

let uu____3144 = (

let uu____3149 = (cur_goal ())
in (trytac uu____3149))
in (bind uu____3144 (fun uu___361_3156 -> (match (uu___361_3156) with
| FStar_Pervasives_Native.Some (g) -> begin
(ret g.FStar_Tactics_Types.opts)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3162 = (FStar_Options.peek ())
in (ret uu____3162))
end))))


let proc_guard : Prims.string  ->  env  ->  FStar_TypeChecker_Env.guard_t  ->  unit tac = (fun reason e g -> (mlog (fun uu____3187 -> (

let uu____3188 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3188))) (fun uu____3193 -> (

let uu____3194 = (add_implicits g.FStar_TypeChecker_Env.implicits)
in (bind uu____3194 (fun uu____3198 -> (bind getopts (fun opts -> (

let uu____3202 = (

let uu____3203 = (FStar_TypeChecker_Rel.simplify_guard e g)
in uu____3203.FStar_TypeChecker_Env.guard_f)
in (match (uu____3202) with
| FStar_TypeChecker_Common.Trivial -> begin
(ret ())
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____3207 = (istrivial e f)
in (match (uu____3207) with
| true -> begin
(ret ())
end
| uu____3212 -> begin
(bind get (fun ps -> (match (ps.FStar_Tactics_Types.guard_policy) with
| FStar_Tactics_Types.Drop -> begin
((

let uu____3220 = (

let uu____3226 = (

let uu____3228 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.format1 "Tactics admitted guard <%s>\n\n" uu____3228))
in ((FStar_Errors.Warning_TacAdmit), (uu____3226)))
in (FStar_Errors.log_issue e.FStar_TypeChecker_Env.range uu____3220));
(ret ());
)
end
| FStar_Tactics_Types.Goal -> begin
(mlog (fun uu____3234 -> (

let uu____3235 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print2 "Making guard (%s:%s) into a goal\n" reason uu____3235))) (fun uu____3240 -> (

let uu____3241 = (mk_irrelevant_goal reason e f opts "")
in (bind uu____3241 (fun goal -> (

let goal1 = (

let uu___399_3249 = goal
in {FStar_Tactics_Types.goal_main_env = uu___399_3249.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = uu___399_3249.FStar_Tactics_Types.goal_ctx_uvar; FStar_Tactics_Types.opts = uu___399_3249.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = true; FStar_Tactics_Types.label = uu___399_3249.FStar_Tactics_Types.label})
in (push_goals ((goal1)::[]))))))))
end
| FStar_Tactics_Types.SMT -> begin
(mlog (fun uu____3253 -> (

let uu____3254 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print2 "Sending guard (%s:%s) to SMT goal\n" reason uu____3254))) (fun uu____3259 -> (

let uu____3260 = (mk_irrelevant_goal reason e f opts "")
in (bind uu____3260 (fun goal -> (

let goal1 = (

let uu___400_3268 = goal
in {FStar_Tactics_Types.goal_main_env = uu___400_3268.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = uu___400_3268.FStar_Tactics_Types.goal_ctx_uvar; FStar_Tactics_Types.opts = uu___400_3268.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = true; FStar_Tactics_Types.label = uu___400_3268.FStar_Tactics_Types.label})
in (push_smt_goals ((goal1)::[]))))))))
end
| FStar_Tactics_Types.Force -> begin
(mlog (fun uu____3272 -> (

let uu____3273 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print2 "Forcing guard (%s:%s)\n" reason uu____3273))) (fun uu____3277 -> (FStar_All.try_with (fun uu___402_3282 -> (match (()) with
| () -> begin
(

let uu____3285 = (

let uu____3287 = (

let uu____3289 = (FStar_TypeChecker_Rel.discharge_guard_no_smt e g)
in (FStar_All.pipe_left FStar_TypeChecker_Env.is_trivial uu____3289))
in (not (uu____3287)))
in (match (uu____3285) with
| true -> begin
(mlog (fun uu____3296 -> (

let uu____3297 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print1 "guard = %s\n" uu____3297))) (fun uu____3301 -> (fail1 "Forcing the guard failed (%s)" reason)))
end
| uu____3303 -> begin
(ret ())
end))
end)) (fun uu___401_3306 -> (mlog (fun uu____3311 -> (

let uu____3312 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print1 "guard = %s\n" uu____3312))) (fun uu____3316 -> (fail1 "Forcing the guard failed (%s)" reason)))))))
end)))
end))
end))))))))))


let tc : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.typ tac = (fun t -> (

let uu____3328 = (

let uu____3331 = (cur_goal ())
in (bind uu____3331 (fun goal -> (

let uu____3337 = (

let uu____3346 = (FStar_Tactics_Types.goal_env goal)
in (__tc_lax uu____3346 t))
in (bind uu____3337 (fun uu____3357 -> (match (uu____3357) with
| (uu____3366, typ, uu____3368) -> begin
(ret typ)
end)))))))
in (FStar_All.pipe_left (wrap_err "tc") uu____3328)))


let add_irrelevant_goal : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  FStar_Options.optionstate  ->  Prims.string  ->  unit tac = (fun reason env phi opts label1 -> (

let uu____3408 = (mk_irrelevant_goal reason env phi opts label1)
in (bind uu____3408 (fun goal -> (add_goals ((goal)::[]))))))


let trivial : unit  ->  unit tac = (fun uu____3420 -> (

let uu____3423 = (cur_goal ())
in (bind uu____3423 (fun goal -> (

let uu____3429 = (

let uu____3431 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____3432 = (FStar_Tactics_Types.goal_type goal)
in (istrivial uu____3431 uu____3432)))
in (match (uu____3429) with
| true -> begin
(solve' goal FStar_Syntax_Util.exp_unit)
end
| uu____3436 -> begin
(

let uu____3438 = (

let uu____3440 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____3441 = (FStar_Tactics_Types.goal_type goal)
in (tts uu____3440 uu____3441)))
in (fail1 "Not a trivial goal: %s" uu____3438))
end))))))


let divide : 'a 'b . FStar_BigInt.t  ->  'a tac  ->  'b tac  ->  ('a * 'b) tac = (fun n1 l r -> (bind get (fun p -> (

let uu____3492 = (FStar_All.try_with (fun uu___407_3515 -> (match (()) with
| () -> begin
(

let uu____3526 = (

let uu____3535 = (FStar_BigInt.to_int_fs n1)
in (FStar_List.splitAt uu____3535 p.FStar_Tactics_Types.goals))
in (ret uu____3526))
end)) (fun uu___406_3546 -> (fail "divide: not enough goals")))
in (bind uu____3492 (fun uu____3583 -> (match (uu____3583) with
| (lgs, rgs) -> begin
(

let lp = (

let uu___403_3609 = p
in {FStar_Tactics_Types.main_context = uu___403_3609.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___403_3609.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___403_3609.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = lgs; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = uu___403_3609.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___403_3609.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___403_3609.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___403_3609.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___403_3609.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___403_3609.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___403_3609.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___403_3609.FStar_Tactics_Types.local_state})
in (

let uu____3610 = (set lp)
in (bind uu____3610 (fun uu____3618 -> (bind l (fun a -> (bind get (fun lp' -> (

let rp = (

let uu___404_3634 = lp'
in {FStar_Tactics_Types.main_context = uu___404_3634.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___404_3634.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___404_3634.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = rgs; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = uu___404_3634.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___404_3634.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___404_3634.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___404_3634.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___404_3634.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___404_3634.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___404_3634.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___404_3634.FStar_Tactics_Types.local_state})
in (

let uu____3635 = (set rp)
in (bind uu____3635 (fun uu____3643 -> (bind r (fun b -> (bind get (fun rp' -> (

let p' = (

let uu___405_3659 = rp'
in {FStar_Tactics_Types.main_context = uu___405_3659.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___405_3659.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___405_3659.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append lp'.FStar_Tactics_Types.goals rp'.FStar_Tactics_Types.goals); FStar_Tactics_Types.smt_goals = (FStar_List.append lp'.FStar_Tactics_Types.smt_goals (FStar_List.append rp'.FStar_Tactics_Types.smt_goals p.FStar_Tactics_Types.smt_goals)); FStar_Tactics_Types.depth = uu___405_3659.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___405_3659.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___405_3659.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___405_3659.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___405_3659.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___405_3659.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___405_3659.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___405_3659.FStar_Tactics_Types.local_state})
in (

let uu____3660 = (set p')
in (bind uu____3660 (fun uu____3668 -> (bind remove_solved_goals (fun uu____3674 -> (ret ((a), (b)))))))))))))))))))))))))
end)))))))


let focus : 'a . 'a tac  ->  'a tac = (fun f -> (

let uu____3696 = (divide FStar_BigInt.one f idtac)
in (bind uu____3696 (fun uu____3709 -> (match (uu____3709) with
| (a, ()) -> begin
(ret a)
end)))))


let rec map : 'a . 'a tac  ->  'a Prims.list tac = (fun tau -> (bind get (fun p -> (match (p.FStar_Tactics_Types.goals) with
| [] -> begin
(ret [])
end
| (uu____3747)::uu____3748 -> begin
(

let uu____3751 = (

let uu____3760 = (map tau)
in (divide FStar_BigInt.one tau uu____3760))
in (bind uu____3751 (fun uu____3778 -> (match (uu____3778) with
| (h, t) -> begin
(ret ((h)::t))
end))))
end))))


let seq : unit tac  ->  unit tac  ->  unit tac = (fun t1 t2 -> (

let uu____3820 = (bind t1 (fun uu____3825 -> (

let uu____3826 = (map t2)
in (bind uu____3826 (fun uu____3834 -> (ret ()))))))
in (focus uu____3820)))


let intro : unit  ->  FStar_Syntax_Syntax.binder tac = (fun uu____3844 -> (

let uu____3847 = (

let uu____3850 = (cur_goal ())
in (bind uu____3850 (fun goal -> (

let uu____3859 = (

let uu____3866 = (FStar_Tactics_Types.goal_type goal)
in (FStar_Syntax_Util.arrow_one uu____3866))
in (match (uu____3859) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____3875 = (

let uu____3877 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____3877)))
in (match (uu____3875) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____3883 -> begin
(

let env' = (

let uu____3886 = (FStar_Tactics_Types.goal_env goal)
in (FStar_TypeChecker_Env.push_binders uu____3886 ((b)::[])))
in (

let typ' = (comp_to_typ c)
in (

let uu____3900 = (new_uvar "intro" env' typ')
in (bind uu____3900 (fun uu____3917 -> (match (uu____3917) with
| (body, ctx_uvar) -> begin
(

let sol = (FStar_Syntax_Util.abs ((b)::[]) body (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c))))
in (

let uu____3941 = (set_solution goal sol)
in (bind uu____3941 (fun uu____3947 -> (

let g = (FStar_Tactics_Types.mk_goal env' ctx_uvar goal.FStar_Tactics_Types.opts goal.FStar_Tactics_Types.is_guard goal.FStar_Tactics_Types.label)
in (

let uu____3949 = (

let uu____3952 = (bnorm_goal g)
in (replace_cur uu____3952))
in (bind uu____3949 (fun uu____3954 -> (ret b)))))))))
end))))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3959 = (

let uu____3961 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____3962 = (FStar_Tactics_Types.goal_type goal)
in (tts uu____3961 uu____3962)))
in (fail1 "goal is not an arrow (%s)" uu____3959))
end)))))
in (FStar_All.pipe_left (wrap_err "intro") uu____3847)))


let intro_rec : unit  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac = (fun uu____3980 -> (

let uu____3987 = (cur_goal ())
in (bind uu____3987 (fun goal -> ((FStar_Util.print_string "WARNING (intro_rec): calling this is known to cause normalizer loops\n");
(FStar_Util.print_string "WARNING (intro_rec): proceed at your own risk...\n");
(

let uu____4006 = (

let uu____4013 = (FStar_Tactics_Types.goal_type goal)
in (FStar_Syntax_Util.arrow_one uu____4013))
in (match (uu____4006) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____4026 = (

let uu____4028 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____4028)))
in (match (uu____4026) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____4042 -> begin
(

let bv = (

let uu____4045 = (FStar_Tactics_Types.goal_type goal)
in (FStar_Syntax_Syntax.gen_bv "__recf" FStar_Pervasives_Native.None uu____4045))
in (

let bs = (

let uu____4056 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____4056)::(b)::[])
in (

let env' = (

let uu____4082 = (FStar_Tactics_Types.goal_env goal)
in (FStar_TypeChecker_Env.push_binders uu____4082 bs))
in (

let uu____4083 = (

let uu____4090 = (comp_to_typ c)
in (new_uvar "intro_rec" env' uu____4090))
in (bind uu____4083 (fun uu____4110 -> (match (uu____4110) with
| (u, ctx_uvar_u) -> begin
(

let lb = (

let uu____4124 = (FStar_Tactics_Types.goal_type goal)
in (

let uu____4127 = (FStar_Syntax_Util.abs ((b)::[]) u FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] uu____4124 FStar_Parser_Const.effect_Tot_lid uu____4127 [] FStar_Range.dummyRange)))
in (

let body = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____4145 = (FStar_Syntax_Subst.close_let_rec ((lb)::[]) body)
in (match (uu____4145) with
| (lbs, body1) -> begin
(

let tm = (

let uu____4167 = (

let uu____4168 = (FStar_Tactics_Types.goal_witness goal)
in uu____4168.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body1)))) FStar_Pervasives_Native.None uu____4167))
in (

let uu____4184 = (set_solution goal tm)
in (bind uu____4184 (fun uu____4193 -> (

let uu____4194 = (

let uu____4197 = (bnorm_goal (

let uu___408_4200 = goal
in {FStar_Tactics_Types.goal_main_env = uu___408_4200.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = ctx_uvar_u; FStar_Tactics_Types.opts = uu___408_4200.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___408_4200.FStar_Tactics_Types.is_guard; FStar_Tactics_Types.label = uu___408_4200.FStar_Tactics_Types.label}))
in (replace_cur uu____4197))
in (bind uu____4194 (fun uu____4207 -> (

let uu____4208 = (

let uu____4213 = (FStar_Syntax_Syntax.mk_binder bv)
in ((uu____4213), (b)))
in (ret uu____4208)))))))))
end))))
end)))))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4222 = (

let uu____4224 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____4225 = (FStar_Tactics_Types.goal_type goal)
in (tts uu____4224 uu____4225)))
in (fail1 "intro_rec: goal is not an arrow (%s)" uu____4222))
end));
)))))


let norm : FStar_Syntax_Embeddings.norm_step Prims.list  ->  unit tac = (fun s -> (

let uu____4245 = (cur_goal ())
in (bind uu____4245 (fun goal -> (mlog (fun uu____4252 -> (

let uu____4253 = (

let uu____4255 = (FStar_Tactics_Types.goal_witness goal)
in (FStar_Syntax_Print.term_to_string uu____4255))
in (FStar_Util.print1 "norm: witness = %s\n" uu____4253))) (fun uu____4261 -> (

let steps = (

let uu____4265 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.UnfoldTac)::[]) uu____4265))
in (

let t = (

let uu____4269 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____4270 = (FStar_Tactics_Types.goal_type goal)
in (normalize steps uu____4269 uu____4270)))
in (

let uu____4271 = (FStar_Tactics_Types.goal_with_type goal t)
in (replace_cur uu____4271))))))))))


let norm_term_env : env  ->  FStar_Syntax_Embeddings.norm_step Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun e s t -> (

let uu____4296 = (bind get (fun ps -> (

let opts = (match (ps.FStar_Tactics_Types.goals) with
| (g)::uu____4304 -> begin
g.FStar_Tactics_Types.opts
end
| uu____4307 -> begin
(FStar_Options.peek ())
end)
in (mlog (fun uu____4312 -> (

let uu____4313 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "norm_term_env: t = %s\n" uu____4313))) (fun uu____4318 -> (

let uu____4319 = (__tc_lax e t)
in (bind uu____4319 (fun uu____4340 -> (match (uu____4340) with
| (t1, uu____4350, uu____4351) -> begin
(

let steps = (

let uu____4355 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.UnfoldTac)::[]) uu____4355))
in (

let t2 = (normalize steps ps.FStar_Tactics_Types.main_context t1)
in (mlog (fun uu____4361 -> (

let uu____4362 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print1 "norm_term_env: t\' = %s\n" uu____4362))) (fun uu____4366 -> (ret t2)))))
end)))))))))
in (FStar_All.pipe_left (wrap_err "norm_term") uu____4296)))


let refine_intro : unit  ->  unit tac = (fun uu____4379 -> (

let uu____4382 = (

let uu____4385 = (cur_goal ())
in (bind uu____4385 (fun g -> (

let uu____4392 = (

let uu____4403 = (FStar_Tactics_Types.goal_env g)
in (

let uu____4404 = (FStar_Tactics_Types.goal_type g)
in (FStar_TypeChecker_Rel.base_and_refinement uu____4403 uu____4404)))
in (match (uu____4392) with
| (uu____4407, FStar_Pervasives_Native.None) -> begin
(fail "not a refinement")
end
| (t, FStar_Pervasives_Native.Some (bv, phi)) -> begin
(

let g1 = (FStar_Tactics_Types.goal_with_type g t)
in (

let uu____4433 = (

let uu____4438 = (

let uu____4443 = (

let uu____4444 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____4444)::[])
in (FStar_Syntax_Subst.open_term uu____4443 phi))
in (match (uu____4438) with
| (bvs, phi1) -> begin
(

let uu____4469 = (

let uu____4470 = (FStar_List.hd bvs)
in (FStar_Pervasives_Native.fst uu____4470))
in ((uu____4469), (phi1)))
end))
in (match (uu____4433) with
| (bv1, phi1) -> begin
(

let uu____4489 = (

let uu____4492 = (FStar_Tactics_Types.goal_env g)
in (

let uu____4493 = (

let uu____4494 = (

let uu____4497 = (

let uu____4498 = (

let uu____4505 = (FStar_Tactics_Types.goal_witness g)
in ((bv1), (uu____4505)))
in FStar_Syntax_Syntax.NT (uu____4498))
in (uu____4497)::[])
in (FStar_Syntax_Subst.subst uu____4494 phi1))
in (mk_irrelevant_goal "refine_intro refinement" uu____4492 uu____4493 g.FStar_Tactics_Types.opts g.FStar_Tactics_Types.label)))
in (bind uu____4489 (fun g2 -> (bind __dismiss (fun uu____4514 -> (add_goals ((g1)::(g2)::[])))))))
end)))
end)))))
in (FStar_All.pipe_left (wrap_err "refine_intro") uu____4382)))


let __exact_now : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun set_expected_typ1 t -> (

let uu____4537 = (cur_goal ())
in (bind uu____4537 (fun goal -> (

let env = (match (set_expected_typ1) with
| true -> begin
(

let uu____4546 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____4547 = (FStar_Tactics_Types.goal_type goal)
in (FStar_TypeChecker_Env.set_expected_typ uu____4546 uu____4547)))
end
| uu____4548 -> begin
(FStar_Tactics_Types.goal_env goal)
end)
in (

let uu____4550 = (__tc env t)
in (bind uu____4550 (fun uu____4569 -> (match (uu____4569) with
| (t1, typ, guard) -> begin
(mlog (fun uu____4584 -> (

let uu____4585 = (FStar_Syntax_Print.term_to_string typ)
in (

let uu____4587 = (

let uu____4589 = (FStar_Tactics_Types.goal_env goal)
in (FStar_TypeChecker_Rel.guard_to_string uu____4589 guard))
in (FStar_Util.print2 "__exact_now: got type %s\n__exact_now: and guard %s\n" uu____4585 uu____4587)))) (fun uu____4593 -> (

let uu____4594 = (

let uu____4597 = (FStar_Tactics_Types.goal_env goal)
in (proc_guard "__exact typing" uu____4597 guard))
in (bind uu____4594 (fun uu____4600 -> (mlog (fun uu____4604 -> (

let uu____4605 = (FStar_Syntax_Print.term_to_string typ)
in (

let uu____4607 = (

let uu____4609 = (FStar_Tactics_Types.goal_type goal)
in (FStar_Syntax_Print.term_to_string uu____4609))
in (FStar_Util.print2 "__exact_now: unifying %s and %s\n" uu____4605 uu____4607)))) (fun uu____4613 -> (

let uu____4614 = (

let uu____4618 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____4619 = (FStar_Tactics_Types.goal_type goal)
in (do_unify uu____4618 typ uu____4619)))
in (bind uu____4614 (fun b -> (match (b) with
| true -> begin
(solve goal t1)
end
| uu____4627 -> begin
(

let uu____4629 = (

let uu____4631 = (FStar_Tactics_Types.goal_env goal)
in (tts uu____4631 t1))
in (

let uu____4632 = (

let uu____4634 = (FStar_Tactics_Types.goal_env goal)
in (tts uu____4634 typ))
in (

let uu____4635 = (

let uu____4637 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____4638 = (FStar_Tactics_Types.goal_type goal)
in (tts uu____4637 uu____4638)))
in (

let uu____4639 = (

let uu____4641 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____4642 = (FStar_Tactics_Types.goal_witness goal)
in (tts uu____4641 uu____4642)))
in (fail4 "%s : %s does not exactly solve the goal %s (witness = %s)" uu____4629 uu____4632 uu____4635 uu____4639)))))
end)))))))))))
end)))))))))


let t_exact : Prims.bool  ->  Prims.bool  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun try_refine set_expected_typ1 tm -> (

let uu____4668 = (mlog (fun uu____4673 -> (

let uu____4674 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "t_exact: tm = %s\n" uu____4674))) (fun uu____4679 -> (

let uu____4680 = (

let uu____4687 = (__exact_now set_expected_typ1 tm)
in (catch uu____4687))
in (bind uu____4680 (fun uu___363_4696 -> (match (uu___363_4696) with
| FStar_Util.Inr (r) -> begin
(ret ())
end
| FStar_Util.Inl (e) when (not (try_refine)) -> begin
(traise e)
end
| FStar_Util.Inl (e) -> begin
(mlog (fun uu____4707 -> (FStar_Util.print_string "__exact_now failed, trying refine...\n")) (fun uu____4711 -> (

let uu____4712 = (

let uu____4719 = (

let uu____4722 = (norm ((FStar_Syntax_Embeddings.Delta)::[]))
in (bind uu____4722 (fun uu____4727 -> (

let uu____4728 = (refine_intro ())
in (bind uu____4728 (fun uu____4732 -> (__exact_now set_expected_typ1 tm)))))))
in (catch uu____4719))
in (bind uu____4712 (fun uu___362_4739 -> (match (uu___362_4739) with
| FStar_Util.Inr (r) -> begin
(mlog (fun uu____4748 -> (FStar_Util.print_string "__exact_now: failed after refining too\n")) (fun uu____4751 -> (ret ())))
end
| FStar_Util.Inl (uu____4752) -> begin
(mlog (fun uu____4754 -> (FStar_Util.print_string "__exact_now: was not a refinement\n")) (fun uu____4757 -> (traise e)))
end))))))
end))))))
in (FStar_All.pipe_left (wrap_err "exact") uu____4668)))


let rec mapM : 'a 'b . ('a  ->  'b tac)  ->  'a Prims.list  ->  'b Prims.list tac = (fun f l -> (match (l) with
| [] -> begin
(ret [])
end
| (x)::xs -> begin
(

let uu____4809 = (f x)
in (bind uu____4809 (fun y -> (

let uu____4817 = (mapM f xs)
in (bind uu____4817 (fun ys -> (ret ((y)::ys))))))))
end))


let rec __try_match_by_application : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Syntax_Syntax.ctx_uvar) Prims.list  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Syntax_Syntax.ctx_uvar) Prims.list tac = (fun acc e ty1 ty2 -> (

let uu____4889 = (do_unify e ty1 ty2)
in (bind uu____4889 (fun uu___364_4903 -> if uu___364_4903 then begin
(ret acc)
end else begin
(

let uu____4923 = (FStar_Syntax_Util.arrow_one ty1)
in (match (uu____4923) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4944 = (FStar_Syntax_Print.term_to_string ty1)
in (

let uu____4946 = (FStar_Syntax_Print.term_to_string ty2)
in (fail2 "Could not instantiate, %s to %s" uu____4944 uu____4946)))
end
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____4963 = (

let uu____4965 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____4965)))
in (match (uu____4963) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____4987 -> begin
(

let uu____4989 = (new_uvar "apply arg" e (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (bind uu____4989 (fun uu____5016 -> (match (uu____5016) with
| (uvt, uv) -> begin
(

let typ = (comp_to_typ c)
in (

let typ' = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((((FStar_Pervasives_Native.fst b)), (uvt))))::[]) typ)
in (__try_match_by_application ((((uvt), ((FStar_Pervasives_Native.snd b)), (uv)))::acc) e typ' ty2)))
end))))
end))
end))
end))))


let try_match_by_application : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Syntax_Syntax.ctx_uvar) Prims.list tac = (fun e ty1 ty2 -> (__try_match_by_application [] e ty1 ty2))


let t_apply : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun uopt tm -> (

let uu____5106 = (mlog (fun uu____5111 -> (

let uu____5112 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "t_apply: tm = %s\n" uu____5112))) (fun uu____5117 -> (

let uu____5118 = (cur_goal ())
in (bind uu____5118 (fun goal -> (

let e = (FStar_Tactics_Types.goal_env goal)
in (

let uu____5126 = (__tc e tm)
in (bind uu____5126 (fun uu____5147 -> (match (uu____5147) with
| (tm1, typ, guard) -> begin
(

let typ1 = (bnorm e typ)
in (

let uu____5160 = (

let uu____5171 = (FStar_Tactics_Types.goal_type goal)
in (try_match_by_application e typ1 uu____5171))
in (bind uu____5160 (fun uvs -> (

let fix_qual = (fun q -> (match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____5209)) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false))
end
| uu____5213 -> begin
q
end))
in (

let w = (FStar_List.fold_right (fun uu____5236 w -> (match (uu____5236) with
| (uvt, q, uu____5254) -> begin
(FStar_Syntax_Util.mk_app w ((((uvt), ((fix_qual q))))::[]))
end)) uvs tm1)
in (

let uvset = (

let uu____5286 = (FStar_Syntax_Free.new_uv_set ())
in (FStar_List.fold_right (fun uu____5303 s -> (match (uu____5303) with
| (uu____5315, uu____5316, uv) -> begin
(

let uu____5318 = (FStar_Syntax_Free.uvars uv.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.set_union s uu____5318))
end)) uvs uu____5286))
in (

let free_in_some_goal = (fun uv -> (FStar_Util.set_mem uv uvset))
in (

let uu____5328 = (solve' goal w)
in (bind uu____5328 (fun uu____5333 -> (

let uu____5334 = (mapM (fun uu____5351 -> (match (uu____5351) with
| (uvt, q, uv) -> begin
(

let uu____5363 = (FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____5363) with
| FStar_Pervasives_Native.Some (uu____5368) -> begin
(ret ())
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5369 = (uopt && (free_in_some_goal uv))
in (match (uu____5369) with
| true -> begin
(ret ())
end
| uu____5374 -> begin
(

let uu____5376 = (

let uu____5379 = (bnorm_goal (

let uu___409_5382 = goal
in {FStar_Tactics_Types.goal_main_env = uu___409_5382.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = uv; FStar_Tactics_Types.opts = uu___409_5382.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = false; FStar_Tactics_Types.label = uu___409_5382.FStar_Tactics_Types.label}))
in (uu____5379)::[])
in (add_goals uu____5376))
end))
end))
end)) uvs)
in (bind uu____5334 (fun uu____5387 -> (proc_guard "apply guard" e guard)))))))))))))))
end))))))))))
in (FStar_All.pipe_left (wrap_err "apply") uu____5106)))


let lemma_or_sq : FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun c -> (

let ct = (FStar_Syntax_Util.comp_to_comp_typ_nouniv c)
in (

let uu____5415 = (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____5415) with
| true -> begin
(

let uu____5424 = (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre)::(post)::uu____5439 -> begin
(((FStar_Pervasives_Native.fst pre)), ((FStar_Pervasives_Native.fst post)))
end
| uu____5492 -> begin
(failwith "apply_lemma: impossible: not a lemma")
end)
in (match (uu____5424) with
| (pre, post) -> begin
(

let post1 = (

let uu____5525 = (

let uu____5536 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit)
in (uu____5536)::[])
in (FStar_Syntax_Util.mk_app post uu____5525))
in FStar_Pervasives_Native.Some (((pre), (post1))))
end))
end
| uu____5565 -> begin
(

let uu____5567 = (FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name)
in (match (uu____5567) with
| true -> begin
(

let uu____5576 = (FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.map_opt uu____5576 (fun post -> ((FStar_Syntax_Util.t_true), (post)))))
end
| uu____5595 -> begin
FStar_Pervasives_Native.None
end))
end))))


let rec fold_left : 'a 'b . ('a  ->  'b  ->  'b tac)  ->  'b  ->  'a Prims.list  ->  'b tac = (fun f e xs -> (match (xs) with
| [] -> begin
(ret e)
end
| (x)::xs1 -> begin
(

let uu____5655 = (f x e)
in (bind uu____5655 (fun e' -> (fold_left f e' xs1))))
end))


let apply_lemma : FStar_Syntax_Syntax.term  ->  unit tac = (fun tm -> (

let uu____5670 = (

let uu____5673 = (bind get (fun ps -> (mlog (fun uu____5680 -> (

let uu____5681 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "apply_lemma: tm = %s\n" uu____5681))) (fun uu____5687 -> (

let is_unit_t = (fun t -> (

let uu____5695 = (

let uu____5696 = (FStar_Syntax_Subst.compress t)
in uu____5696.FStar_Syntax_Syntax.n)
in (match (uu____5695) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
true
end
| uu____5702 -> begin
false
end)))
in (

let uu____5704 = (cur_goal ())
in (bind uu____5704 (fun goal -> (

let uu____5710 = (

let uu____5719 = (FStar_Tactics_Types.goal_env goal)
in (__tc uu____5719 tm))
in (bind uu____5710 (fun uu____5734 -> (match (uu____5734) with
| (tm1, t, guard) -> begin
(

let uu____5746 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____5746) with
| (bs, comp) -> begin
(

let uu____5779 = (lemma_or_sq comp)
in (match (uu____5779) with
| FStar_Pervasives_Native.None -> begin
(fail "not a lemma or squashed function")
end
| FStar_Pervasives_Native.Some (pre, post) -> begin
(

let uu____5799 = (fold_left (fun uu____5861 uu____5862 -> (match (((uu____5861), (uu____5862))) with
| ((b, aq), (uvs, imps, subst1)) -> begin
(

let b_t = (FStar_Syntax_Subst.subst subst1 b.FStar_Syntax_Syntax.sort)
in (

let uu____6013 = (is_unit_t b_t)
in (match (uu____6013) with
| true -> begin
(FStar_All.pipe_left ret (((((FStar_Syntax_Util.exp_unit), (aq)))::uvs), (imps), ((FStar_Syntax_Syntax.NT (((b), (FStar_Syntax_Util.exp_unit))))::subst1)))
end
| uu____6134 -> begin
(

let uu____6136 = (

let uu____6143 = (FStar_Tactics_Types.goal_env goal)
in (new_uvar "apply_lemma" uu____6143 b_t))
in (bind uu____6136 (fun uu____6174 -> (match (uu____6174) with
| (t1, u) -> begin
(FStar_All.pipe_left ret (((((t1), (aq)))::uvs), ((((t1), (u)))::imps), ((FStar_Syntax_Syntax.NT (((b), (t1))))::subst1)))
end))))
end)))
end)) (([]), ([]), ([])) bs)
in (bind uu____5799 (fun uu____6360 -> (match (uu____6360) with
| (uvs, implicits, subst1) -> begin
(

let implicits1 = (FStar_List.rev implicits)
in (

let uvs1 = (FStar_List.rev uvs)
in (

let pre1 = (FStar_Syntax_Subst.subst subst1 pre)
in (

let post1 = (FStar_Syntax_Subst.subst subst1 post)
in (

let uu____6448 = (

let uu____6452 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____6453 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero post1)
in (

let uu____6454 = (FStar_Tactics_Types.goal_type goal)
in (do_unify uu____6452 uu____6453 uu____6454))))
in (bind uu____6448 (fun b -> (match ((not (b))) with
| true -> begin
(

let uu____6465 = (

let uu____6467 = (FStar_Tactics_Types.goal_env goal)
in (tts uu____6467 tm1))
in (

let uu____6468 = (

let uu____6470 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____6471 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero post1)
in (tts uu____6470 uu____6471)))
in (

let uu____6472 = (

let uu____6474 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____6475 = (FStar_Tactics_Types.goal_type goal)
in (tts uu____6474 uu____6475)))
in (fail3 "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)" uu____6465 uu____6468 uu____6472))))
end
| uu____6477 -> begin
(

let uu____6479 = (solve' goal FStar_Syntax_Util.exp_unit)
in (bind uu____6479 (fun uu____6487 -> (

let is_free_uvar = (fun uv t1 -> (

let free_uvars = (

let uu____6513 = (

let uu____6516 = (FStar_Syntax_Free.uvars t1)
in (FStar_Util.set_elements uu____6516))
in (FStar_List.map (fun x -> x.FStar_Syntax_Syntax.ctx_uvar_head) uu____6513))
in (FStar_List.existsML (fun u -> (FStar_Syntax_Unionfind.equiv u uv)) free_uvars)))
in (

let appears = (fun uv goals -> (FStar_List.existsML (fun g' -> (

let uu____6552 = (FStar_Tactics_Types.goal_type g')
in (is_free_uvar uv uu____6552))) goals))
in (

let checkone = (fun t1 goals -> (

let uu____6569 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____6569) with
| (hd1, uu____6588) -> begin
(match (hd1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____6615) -> begin
(appears uv.FStar_Syntax_Syntax.ctx_uvar_head goals)
end
| uu____6632 -> begin
false
end)
end)))
in (

let uu____6634 = (FStar_All.pipe_right implicits1 (mapM (fun imp -> (

let t1 = (FStar_Util.now ())
in (

let uu____6677 = imp
in (match (uu____6677) with
| (term, ctx_uvar) -> begin
(

let uu____6688 = (FStar_Syntax_Util.head_and_args term)
in (match (uu____6688) with
| (hd1, uu____6710) -> begin
(

let uu____6735 = (

let uu____6736 = (FStar_Syntax_Subst.compress hd1)
in uu____6736.FStar_Syntax_Syntax.n)
in (match (uu____6735) with
| FStar_Syntax_Syntax.Tm_uvar (ctx_uvar1, uu____6744) -> begin
(

let goal1 = (bnorm_goal (

let uu___410_6764 = goal
in {FStar_Tactics_Types.goal_main_env = uu___410_6764.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = ctx_uvar1; FStar_Tactics_Types.opts = uu___410_6764.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___410_6764.FStar_Tactics_Types.is_guard; FStar_Tactics_Types.label = uu___410_6764.FStar_Tactics_Types.label}))
in (ret ((goal1)::[])))
end
| uu____6767 -> begin
(mlog (fun uu____6773 -> (

let uu____6774 = (FStar_Syntax_Print.uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____6776 = (FStar_Syntax_Print.term_to_string term)
in (FStar_Util.print2 "apply_lemma: arg %s unified to (%s)\n" uu____6774 uu____6776)))) (fun uu____6783 -> (

let env = (

let uu___411_6785 = (FStar_Tactics_Types.goal_env goal)
in {FStar_TypeChecker_Env.solver = uu___411_6785.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___411_6785.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___411_6785.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_TypeChecker_Env.gamma_sig = uu___411_6785.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___411_6785.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___411_6785.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___411_6785.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___411_6785.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___411_6785.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___411_6785.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___411_6785.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___411_6785.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___411_6785.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___411_6785.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___411_6785.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___411_6785.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___411_6785.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___411_6785.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___411_6785.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___411_6785.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___411_6785.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___411_6785.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___411_6785.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___411_6785.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___411_6785.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___411_6785.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___411_6785.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___411_6785.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___411_6785.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___411_6785.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___411_6785.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___411_6785.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___411_6785.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___411_6785.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___411_6785.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___411_6785.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___411_6785.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___411_6785.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___411_6785.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___411_6785.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___411_6785.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___411_6785.FStar_TypeChecker_Env.nbe})
in (

let g_typ = (FStar_TypeChecker_TcTerm.check_type_of_well_typed_term' true env term ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in (

let uu____6788 = (

let uu____6791 = (match (ps.FStar_Tactics_Types.tac_verb_dbg) with
| true -> begin
(

let uu____6795 = (FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar)
in (

let uu____6797 = (FStar_Syntax_Print.term_to_string term)
in (FStar_Util.format2 "apply_lemma solved arg %s to %s\n" uu____6795 uu____6797)))
end
| uu____6800 -> begin
"apply_lemma solved arg"
end)
in (

let uu____6803 = (FStar_Tactics_Types.goal_env goal)
in (proc_guard uu____6791 uu____6803 g_typ)))
in (bind uu____6788 (fun uu____6807 -> (ret []))))))))
end))
end))
end))))))
in (bind uu____6634 (fun sub_goals -> (

let sub_goals1 = (FStar_List.flatten sub_goals)
in (

let rec filter' = (fun f xs -> (match (xs) with
| [] -> begin
[]
end
| (x)::xs1 -> begin
(

let uu____6871 = (f x xs1)
in (match (uu____6871) with
| true -> begin
(

let uu____6876 = (filter' f xs1)
in (x)::uu____6876)
end
| uu____6879 -> begin
(filter' f xs1)
end))
end))
in (

let sub_goals2 = (filter' (fun g goals -> (

let uu____6891 = (

let uu____6893 = (FStar_Tactics_Types.goal_witness g)
in (checkone uu____6893 goals))
in (not (uu____6891)))) sub_goals1)
in (

let uu____6894 = (

let uu____6897 = (FStar_Tactics_Types.goal_env goal)
in (proc_guard "apply_lemma guard" uu____6897 guard))
in (bind uu____6894 (fun uu____6901 -> (

let uu____6902 = (

let uu____6905 = (

let uu____6907 = (

let uu____6909 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____6910 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero pre1)
in (istrivial uu____6909 uu____6910)))
in (not (uu____6907)))
in (match (uu____6905) with
| true -> begin
(

let uu____6914 = (FStar_Tactics_Types.goal_env goal)
in (add_irrelevant_goal "apply_lemma precondition" uu____6914 pre1 goal.FStar_Tactics_Types.opts goal.FStar_Tactics_Types.label))
end
| uu____6916 -> begin
(ret ())
end))
in (bind uu____6902 (fun uu____6919 -> (add_goals sub_goals2)))))))))))))))))))
end))))))))
end))))
end))
end))
end))))))))))))
in (focus uu____5673))
in (FStar_All.pipe_left (wrap_err "apply_lemma") uu____5670)))


let destruct_eq' : FStar_Reflection_Data.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun typ -> (

let uu____6943 = (FStar_Syntax_Util.destruct_typ_as_formula typ)
in (match (uu____6943) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (l, (uu____6953)::((e1, uu____6955))::((e2, uu____6957))::[])) when ((FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)) -> begin
FStar_Pervasives_Native.Some (((e1), (e2)))
end
| uu____7018 -> begin
FStar_Pervasives_Native.None
end)))


let destruct_eq : FStar_Reflection_Data.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun typ -> (

let uu____7043 = (destruct_eq' typ)
in (match (uu____7043) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____7073 = (FStar_Syntax_Util.un_squash typ)
in (match (uu____7073) with
| FStar_Pervasives_Native.Some (typ1) -> begin
(destruct_eq' typ1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end)))


let split_env : FStar_Syntax_Syntax.bv  ->  env  ->  (env * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.option = (fun bvar e -> (

let rec aux = (fun e1 -> (

let uu____7142 = (FStar_TypeChecker_Env.pop_bv e1)
in (match (uu____7142) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (bv', e') -> begin
(match ((FStar_Syntax_Syntax.bv_eq bvar bv')) with
| true -> begin
FStar_Pervasives_Native.Some (((e'), (bv'), ([])))
end
| uu____7198 -> begin
(

let uu____7200 = (aux e')
in (FStar_Util.map_opt uu____7200 (fun uu____7231 -> (match (uu____7231) with
| (e'', bv, bvs) -> begin
((e''), (bv), ((bv')::bvs))
end))))
end)
end)))
in (

let uu____7257 = (aux e)
in (FStar_Util.map_opt uu____7257 (fun uu____7288 -> (match (uu____7288) with
| (e', bv, bvs) -> begin
((e'), (bv), ((FStar_List.rev bvs)))
end))))))


let push_bvs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_TypeChecker_Env.env = (fun e bvs -> (FStar_List.fold_left (fun e1 b -> (FStar_TypeChecker_Env.push_bv e1 b)) e bvs))


let subst_goal : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Tactics_Types.goal  ->  FStar_Tactics_Types.goal FStar_Pervasives_Native.option = (fun b1 b2 s g -> (

let uu____7362 = (

let uu____7373 = (FStar_Tactics_Types.goal_env g)
in (split_env b1 uu____7373))
in (FStar_Util.map_opt uu____7362 (fun uu____7391 -> (match (uu____7391) with
| (e0, b11, bvs) -> begin
(

let s1 = (fun bv -> (

let uu___412_7413 = bv
in (

let uu____7414 = (FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___412_7413.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___412_7413.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7414})))
in (

let bvs1 = (FStar_List.map s1 bvs)
in (

let new_env = (push_bvs e0 ((b2)::bvs1))
in (

let new_goal = (

let uu___413_7422 = g.FStar_Tactics_Types.goal_ctx_uvar
in (

let uu____7423 = (FStar_TypeChecker_Env.all_binders new_env)
in (

let uu____7432 = (

let uu____7435 = (FStar_Tactics_Types.goal_type g)
in (FStar_Syntax_Subst.subst s uu____7435))
in {FStar_Syntax_Syntax.ctx_uvar_head = uu___413_7422.FStar_Syntax_Syntax.ctx_uvar_head; FStar_Syntax_Syntax.ctx_uvar_gamma = new_env.FStar_TypeChecker_Env.gamma; FStar_Syntax_Syntax.ctx_uvar_binders = uu____7423; FStar_Syntax_Syntax.ctx_uvar_typ = uu____7432; FStar_Syntax_Syntax.ctx_uvar_reason = uu___413_7422.FStar_Syntax_Syntax.ctx_uvar_reason; FStar_Syntax_Syntax.ctx_uvar_should_check = uu___413_7422.FStar_Syntax_Syntax.ctx_uvar_should_check; FStar_Syntax_Syntax.ctx_uvar_range = uu___413_7422.FStar_Syntax_Syntax.ctx_uvar_range; FStar_Syntax_Syntax.ctx_uvar_meta = uu___413_7422.FStar_Syntax_Syntax.ctx_uvar_meta})))
in (

let uu___414_7436 = g
in {FStar_Tactics_Types.goal_main_env = uu___414_7436.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = new_goal; FStar_Tactics_Types.opts = uu___414_7436.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___414_7436.FStar_Tactics_Types.is_guard; FStar_Tactics_Types.label = uu___414_7436.FStar_Tactics_Types.label})))))
end)))))


let rewrite : FStar_Syntax_Syntax.binder  ->  unit tac = (fun h -> (

let uu____7447 = (

let uu____7450 = (cur_goal ())
in (bind uu____7450 (fun goal -> (

let uu____7458 = h
in (match (uu____7458) with
| (bv, uu____7462) -> begin
(mlog (fun uu____7470 -> (

let uu____7471 = (FStar_Syntax_Print.bv_to_string bv)
in (

let uu____7473 = (FStar_Syntax_Print.term_to_string bv.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "+++Rewrite %s : %s\n" uu____7471 uu____7473)))) (fun uu____7478 -> (

let uu____7479 = (

let uu____7490 = (FStar_Tactics_Types.goal_env goal)
in (split_env bv uu____7490))
in (match (uu____7479) with
| FStar_Pervasives_Native.None -> begin
(fail "binder not found in environment")
end
| FStar_Pervasives_Native.Some (e0, bv1, bvs) -> begin
(

let uu____7517 = (destruct_eq bv1.FStar_Syntax_Syntax.sort)
in (match (uu____7517) with
| FStar_Pervasives_Native.Some (x, e) -> begin
(

let uu____7532 = (

let uu____7533 = (FStar_Syntax_Subst.compress x)
in uu____7533.FStar_Syntax_Syntax.n)
in (match (uu____7532) with
| FStar_Syntax_Syntax.Tm_name (x1) -> begin
(

let s = (FStar_Syntax_Syntax.NT (((x1), (e))))::[]
in (

let s1 = (fun bv2 -> (

let uu___415_7550 = bv2
in (

let uu____7551 = (FStar_Syntax_Subst.subst s bv2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___415_7550.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___415_7550.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7551})))
in (

let bvs1 = (FStar_List.map s1 bvs)
in (

let new_env = (push_bvs e0 ((bv1)::bvs1))
in (

let new_goal = (

let uu___416_7559 = goal.FStar_Tactics_Types.goal_ctx_uvar
in (

let uu____7560 = (FStar_TypeChecker_Env.all_binders new_env)
in (

let uu____7569 = (

let uu____7572 = (FStar_Tactics_Types.goal_type goal)
in (FStar_Syntax_Subst.subst s uu____7572))
in {FStar_Syntax_Syntax.ctx_uvar_head = uu___416_7559.FStar_Syntax_Syntax.ctx_uvar_head; FStar_Syntax_Syntax.ctx_uvar_gamma = new_env.FStar_TypeChecker_Env.gamma; FStar_Syntax_Syntax.ctx_uvar_binders = uu____7560; FStar_Syntax_Syntax.ctx_uvar_typ = uu____7569; FStar_Syntax_Syntax.ctx_uvar_reason = uu___416_7559.FStar_Syntax_Syntax.ctx_uvar_reason; FStar_Syntax_Syntax.ctx_uvar_should_check = uu___416_7559.FStar_Syntax_Syntax.ctx_uvar_should_check; FStar_Syntax_Syntax.ctx_uvar_range = uu___416_7559.FStar_Syntax_Syntax.ctx_uvar_range; FStar_Syntax_Syntax.ctx_uvar_meta = uu___416_7559.FStar_Syntax_Syntax.ctx_uvar_meta})))
in (replace_cur (

let uu___417_7575 = goal
in {FStar_Tactics_Types.goal_main_env = uu___417_7575.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = new_goal; FStar_Tactics_Types.opts = uu___417_7575.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___417_7575.FStar_Tactics_Types.is_guard; FStar_Tactics_Types.label = uu___417_7575.FStar_Tactics_Types.label})))))))
end
| uu____7576 -> begin
(fail "Not an equality hypothesis with a variable on the LHS")
end))
end
| uu____7578 -> begin
(fail "Not an equality hypothesis")
end))
end))))
end)))))
in (FStar_All.pipe_left (wrap_err "rewrite") uu____7447)))


let rename_to : FStar_Syntax_Syntax.binder  ->  Prims.string  ->  unit tac = (fun b s -> (

let uu____7608 = (

let uu____7611 = (cur_goal ())
in (bind uu____7611 (fun goal -> (

let uu____7622 = b
in (match (uu____7622) with
| (bv, uu____7626) -> begin
(

let bv' = (

let uu____7632 = (

let uu___418_7633 = bv
in (

let uu____7634 = (FStar_Ident.mk_ident ((s), (bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
in {FStar_Syntax_Syntax.ppname = uu____7634; FStar_Syntax_Syntax.index = uu___418_7633.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___418_7633.FStar_Syntax_Syntax.sort}))
in (FStar_Syntax_Syntax.freshen_bv uu____7632))
in (

let s1 = (

let uu____7639 = (

let uu____7640 = (

let uu____7647 = (FStar_Syntax_Syntax.bv_to_name bv')
in ((bv), (uu____7647)))
in FStar_Syntax_Syntax.NT (uu____7640))
in (uu____7639)::[])
in (

let uu____7652 = (subst_goal bv bv' s1 goal)
in (match (uu____7652) with
| FStar_Pervasives_Native.None -> begin
(fail "binder not found in environment")
end
| FStar_Pervasives_Native.Some (goal1) -> begin
(replace_cur goal1)
end))))
end)))))
in (FStar_All.pipe_left (wrap_err "rename_to") uu____7608)))


let binder_retype : FStar_Syntax_Syntax.binder  ->  unit tac = (fun b -> (

let uu____7674 = (

let uu____7677 = (cur_goal ())
in (bind uu____7677 (fun goal -> (

let uu____7686 = b
in (match (uu____7686) with
| (bv, uu____7690) -> begin
(

let uu____7695 = (

let uu____7706 = (FStar_Tactics_Types.goal_env goal)
in (split_env bv uu____7706))
in (match (uu____7695) with
| FStar_Pervasives_Native.None -> begin
(fail "binder is not present in environment")
end
| FStar_Pervasives_Native.Some (e0, bv1, bvs) -> begin
(

let uu____7733 = (FStar_Syntax_Util.type_u ())
in (match (uu____7733) with
| (ty, u) -> begin
(

let uu____7742 = (new_uvar "binder_retype" e0 ty)
in (bind uu____7742 (fun uu____7761 -> (match (uu____7761) with
| (t', u_t') -> begin
(

let bv'' = (

let uu___419_7771 = bv1
in {FStar_Syntax_Syntax.ppname = uu___419_7771.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___419_7771.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t'})
in (

let s = (

let uu____7775 = (

let uu____7776 = (

let uu____7783 = (FStar_Syntax_Syntax.bv_to_name bv'')
in ((bv1), (uu____7783)))
in FStar_Syntax_Syntax.NT (uu____7776))
in (uu____7775)::[])
in (

let bvs1 = (FStar_List.map (fun b1 -> (

let uu___420_7795 = b1
in (

let uu____7796 = (FStar_Syntax_Subst.subst s b1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___420_7795.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___420_7795.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7796}))) bvs)
in (

let env' = (push_bvs e0 ((bv'')::bvs1))
in (bind __dismiss (fun uu____7803 -> (

let new_goal = (

let uu____7805 = (FStar_Tactics_Types.goal_with_env goal env')
in (

let uu____7806 = (

let uu____7807 = (FStar_Tactics_Types.goal_type goal)
in (FStar_Syntax_Subst.subst s uu____7807))
in (FStar_Tactics_Types.goal_with_type uu____7805 uu____7806)))
in (

let uu____7808 = (add_goals ((new_goal)::[]))
in (bind uu____7808 (fun uu____7813 -> (

let uu____7814 = (FStar_Syntax_Util.mk_eq2 (FStar_Syntax_Syntax.U_succ (u)) ty bv1.FStar_Syntax_Syntax.sort t')
in (add_irrelevant_goal "binder_retype equation" e0 uu____7814 goal.FStar_Tactics_Types.opts goal.FStar_Tactics_Types.label))))))))))))
end))))
end))
end))
end)))))
in (FStar_All.pipe_left (wrap_err "binder_retype") uu____7674)))


let norm_binder_type : FStar_Syntax_Embeddings.norm_step Prims.list  ->  FStar_Syntax_Syntax.binder  ->  unit tac = (fun s b -> (

let uu____7840 = (

let uu____7843 = (cur_goal ())
in (bind uu____7843 (fun goal -> (

let uu____7852 = b
in (match (uu____7852) with
| (bv, uu____7856) -> begin
(

let uu____7861 = (

let uu____7872 = (FStar_Tactics_Types.goal_env goal)
in (split_env bv uu____7872))
in (match (uu____7861) with
| FStar_Pervasives_Native.None -> begin
(fail "binder is not present in environment")
end
| FStar_Pervasives_Native.Some (e0, bv1, bvs) -> begin
(

let steps = (

let uu____7902 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.UnfoldTac)::[]) uu____7902))
in (

let sort' = (normalize steps e0 bv1.FStar_Syntax_Syntax.sort)
in (

let bv' = (

let uu___421_7907 = bv1
in {FStar_Syntax_Syntax.ppname = uu___421_7907.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___421_7907.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort'})
in (

let env' = (push_bvs e0 ((bv')::bvs))
in (

let uu____7909 = (FStar_Tactics_Types.goal_with_env goal env')
in (replace_cur uu____7909))))))
end))
end)))))
in (FStar_All.pipe_left (wrap_err "norm_binder_type") uu____7840)))


let revert : unit  ->  unit tac = (fun uu____7922 -> (

let uu____7925 = (cur_goal ())
in (bind uu____7925 (fun goal -> (

let uu____7931 = (

let uu____7938 = (FStar_Tactics_Types.goal_env goal)
in (FStar_TypeChecker_Env.pop_bv uu____7938))
in (match (uu____7931) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot revert; empty context")
end
| FStar_Pervasives_Native.Some (x, env') -> begin
(

let typ' = (

let uu____7955 = (

let uu____7958 = (FStar_Tactics_Types.goal_type goal)
in (FStar_Syntax_Syntax.mk_Total uu____7958))
in (FStar_Syntax_Util.arrow ((((x), (FStar_Pervasives_Native.None)))::[]) uu____7955))
in (

let uu____7973 = (new_uvar "revert" env' typ')
in (bind uu____7973 (fun uu____7989 -> (match (uu____7989) with
| (r, u_r) -> begin
(

let uu____7998 = (

let uu____8001 = (

let uu____8002 = (

let uu____8003 = (FStar_Tactics_Types.goal_type goal)
in uu____8003.FStar_Syntax_Syntax.pos)
in (

let uu____8006 = (

let uu____8011 = (

let uu____8012 = (

let uu____8021 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____8021))
in (uu____8012)::[])
in (FStar_Syntax_Syntax.mk_Tm_app r uu____8011))
in (uu____8006 FStar_Pervasives_Native.None uu____8002)))
in (set_solution goal uu____8001))
in (bind uu____7998 (fun uu____8042 -> (

let g = (FStar_Tactics_Types.mk_goal env' u_r goal.FStar_Tactics_Types.opts goal.FStar_Tactics_Types.is_guard goal.FStar_Tactics_Types.label)
in (replace_cur g)))))
end)))))
end))))))


let free_in : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun bv t -> (

let uu____8056 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_mem bv uu____8056)))


let rec clear : FStar_Syntax_Syntax.binder  ->  unit tac = (fun b -> (

let bv = (FStar_Pervasives_Native.fst b)
in (

let uu____8072 = (cur_goal ())
in (bind uu____8072 (fun goal -> (mlog (fun uu____8080 -> (

let uu____8081 = (FStar_Syntax_Print.binder_to_string b)
in (

let uu____8083 = (

let uu____8085 = (

let uu____8087 = (

let uu____8096 = (FStar_Tactics_Types.goal_env goal)
in (FStar_TypeChecker_Env.all_binders uu____8096))
in (FStar_All.pipe_right uu____8087 FStar_List.length))
in (FStar_All.pipe_right uu____8085 FStar_Util.string_of_int))
in (FStar_Util.print2 "Clear of (%s), env has %s binders\n" uu____8081 uu____8083)))) (fun uu____8117 -> (

let uu____8118 = (

let uu____8129 = (FStar_Tactics_Types.goal_env goal)
in (split_env bv uu____8129))
in (match (uu____8118) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot clear; binder not in environment")
end
| FStar_Pervasives_Native.Some (e', bv1, bvs) -> begin
(

let rec check1 = (fun bvs1 -> (match (bvs1) with
| [] -> begin
(ret ())
end
| (bv')::bvs2 -> begin
(

let uu____8174 = (free_in bv1 bv'.FStar_Syntax_Syntax.sort)
in (match (uu____8174) with
| true -> begin
(

let uu____8179 = (

let uu____8181 = (FStar_Syntax_Print.bv_to_string bv')
in (FStar_Util.format1 "Cannot clear; binder present in the type of %s" uu____8181))
in (fail uu____8179))
end
| uu____8184 -> begin
(check1 bvs2)
end))
end))
in (

let uu____8186 = (

let uu____8188 = (FStar_Tactics_Types.goal_type goal)
in (free_in bv1 uu____8188))
in (match (uu____8186) with
| true -> begin
(fail "Cannot clear; binder present in goal")
end
| uu____8193 -> begin
(

let uu____8195 = (check1 bvs)
in (bind uu____8195 (fun uu____8201 -> (

let env' = (push_bvs e' bvs)
in (

let uu____8203 = (

let uu____8210 = (FStar_Tactics_Types.goal_type goal)
in (new_uvar "clear.witness" env' uu____8210))
in (bind uu____8203 (fun uu____8220 -> (match (uu____8220) with
| (ut, uvar_ut) -> begin
(

let uu____8229 = (set_solution goal ut)
in (bind uu____8229 (fun uu____8234 -> (

let uu____8235 = (FStar_Tactics_Types.mk_goal env' uvar_ut goal.FStar_Tactics_Types.opts goal.FStar_Tactics_Types.is_guard goal.FStar_Tactics_Types.label)
in (replace_cur uu____8235)))))
end))))))))
end)))
end)))))))))


let clear_top : unit  ->  unit tac = (fun uu____8243 -> (

let uu____8246 = (cur_goal ())
in (bind uu____8246 (fun goal -> (

let uu____8252 = (

let uu____8259 = (FStar_Tactics_Types.goal_env goal)
in (FStar_TypeChecker_Env.pop_bv uu____8259))
in (match (uu____8252) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot clear; empty context")
end
| FStar_Pervasives_Native.Some (x, uu____8268) -> begin
(

let uu____8273 = (FStar_Syntax_Syntax.mk_binder x)
in (clear uu____8273))
end))))))


let prune : Prims.string  ->  unit tac = (fun s -> (

let uu____8286 = (cur_goal ())
in (bind uu____8286 (fun g -> (

let ctx = (FStar_Tactics_Types.goal_env g)
in (

let ctx' = (

let uu____8296 = (FStar_Ident.path_of_text s)
in (FStar_TypeChecker_Env.rem_proof_ns ctx uu____8296))
in (

let g' = (FStar_Tactics_Types.goal_with_env g ctx')
in (bind __dismiss (fun uu____8299 -> (add_goals ((g')::[])))))))))))


let addns : Prims.string  ->  unit tac = (fun s -> (

let uu____8312 = (cur_goal ())
in (bind uu____8312 (fun g -> (

let ctx = (FStar_Tactics_Types.goal_env g)
in (

let ctx' = (

let uu____8322 = (FStar_Ident.path_of_text s)
in (FStar_TypeChecker_Env.add_proof_ns ctx uu____8322))
in (

let g' = (FStar_Tactics_Types.goal_with_env g ctx')
in (bind __dismiss (fun uu____8325 -> (add_goals ((g')::[])))))))))))


let rec tac_fold_env : FStar_Tactics_Types.direction  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac)  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun d f env t -> (

let tn = (

let uu____8366 = (FStar_Syntax_Subst.compress t)
in uu____8366.FStar_Syntax_Syntax.n)
in (

let uu____8369 = (match ((Prims.op_Equality d FStar_Tactics_Types.TopDown)) with
| true -> begin
(f env (

let uu___425_8376 = t
in {FStar_Syntax_Syntax.n = tn; FStar_Syntax_Syntax.pos = uu___425_8376.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___425_8376.FStar_Syntax_Syntax.vars}))
end
| uu____8377 -> begin
(ret t)
end)
in (bind uu____8369 (fun t1 -> (

let ff = (tac_fold_env d f env)
in (

let tn1 = (

let uu____8393 = (

let uu____8394 = (FStar_Syntax_Subst.compress t1)
in uu____8394.FStar_Syntax_Syntax.n)
in (match (uu____8393) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____8425 = (ff hd1)
in (bind uu____8425 (fun hd2 -> (

let fa = (fun uu____8451 -> (match (uu____8451) with
| (a, q) -> begin
(

let uu____8472 = (ff a)
in (bind uu____8472 (fun a1 -> (ret ((a1), (q))))))
end))
in (

let uu____8491 = (mapM fa args)
in (bind uu____8491 (fun args1 -> (ret (FStar_Syntax_Syntax.Tm_app (((hd2), (args1))))))))))))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, k) -> begin
(

let uu____8573 = (FStar_Syntax_Subst.open_term bs t2)
in (match (uu____8573) with
| (bs1, t') -> begin
(

let uu____8582 = (

let uu____8585 = (FStar_TypeChecker_Env.push_binders env bs1)
in (tac_fold_env d f uu____8585 t'))
in (bind uu____8582 (fun t'' -> (

let uu____8589 = (

let uu____8590 = (

let uu____8609 = (FStar_Syntax_Subst.close_binders bs1)
in (

let uu____8618 = (FStar_Syntax_Subst.close bs1 t'')
in ((uu____8609), (uu____8618), (k))))
in FStar_Syntax_Syntax.Tm_abs (uu____8590))
in (ret uu____8589)))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(ret tn)
end
| FStar_Syntax_Syntax.Tm_match (hd1, brs) -> begin
(

let uu____8693 = (ff hd1)
in (bind uu____8693 (fun hd2 -> (

let ffb = (fun br -> (

let uu____8708 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____8708) with
| (pat, w, e) -> begin
(

let bvs = (FStar_Syntax_Syntax.pat_bvs pat)
in (

let ff1 = (

let uu____8740 = (FStar_TypeChecker_Env.push_bvs env bvs)
in (tac_fold_env d f uu____8740))
in (

let uu____8741 = (ff1 e)
in (bind uu____8741 (fun e1 -> (

let br1 = (FStar_Syntax_Subst.close_branch ((pat), (w), (e1)))
in (ret br1)))))))
end)))
in (

let uu____8756 = (mapM ffb brs)
in (bind uu____8756 (fun brs1 -> (ret (FStar_Syntax_Syntax.Tm_match (((hd2), (brs1))))))))))))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (bv); FStar_Syntax_Syntax.lbunivs = uu____8800; FStar_Syntax_Syntax.lbtyp = uu____8801; FStar_Syntax_Syntax.lbeff = uu____8802; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu____8804; FStar_Syntax_Syntax.lbpos = uu____8805})::[]), e) -> begin
(

let lb = (

let uu____8833 = (

let uu____8834 = (FStar_Syntax_Subst.compress t1)
in uu____8834.FStar_Syntax_Syntax.n)
in (match (uu____8833) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), uu____8838) -> begin
lb
end
| uu____8854 -> begin
(failwith "impossible")
end))
in (

let fflb = (fun lb1 -> (

let uu____8864 = (ff lb1.FStar_Syntax_Syntax.lbdef)
in (bind uu____8864 (fun def1 -> (ret (

let uu___422_8870 = lb1
in {FStar_Syntax_Syntax.lbname = uu___422_8870.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___422_8870.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___422_8870.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___422_8870.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def1; FStar_Syntax_Syntax.lbattrs = uu___422_8870.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___422_8870.FStar_Syntax_Syntax.lbpos}))))))
in (

let uu____8871 = (fflb lb)
in (bind uu____8871 (fun lb1 -> (

let uu____8881 = (

let uu____8886 = (

let uu____8887 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____8887)::[])
in (FStar_Syntax_Subst.open_term uu____8886 e))
in (match (uu____8881) with
| (bs, e1) -> begin
(

let ff1 = (

let uu____8917 = (FStar_TypeChecker_Env.push_binders env bs)
in (tac_fold_env d f uu____8917))
in (

let uu____8918 = (ff1 e1)
in (bind uu____8918 (fun e2 -> (

let e3 = (FStar_Syntax_Subst.close bs e2)
in (ret (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e3))))))))))
end)))))))
end
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e) -> begin
(

let fflb = (fun lb -> (

let uu____8965 = (ff lb.FStar_Syntax_Syntax.lbdef)
in (bind uu____8965 (fun def -> (ret (

let uu___423_8971 = lb
in {FStar_Syntax_Syntax.lbname = uu___423_8971.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___423_8971.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___423_8971.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___423_8971.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu___423_8971.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___423_8971.FStar_Syntax_Syntax.lbpos}))))))
in (

let uu____8972 = (FStar_Syntax_Subst.open_let_rec lbs e)
in (match (uu____8972) with
| (lbs1, e1) -> begin
(

let uu____8987 = (mapM fflb lbs1)
in (bind uu____8987 (fun lbs2 -> (

let uu____8999 = (ff e1)
in (bind uu____8999 (fun e2 -> (

let uu____9007 = (FStar_Syntax_Subst.close_let_rec lbs2 e2)
in (match (uu____9007) with
| (lbs3, e3) -> begin
(ret (FStar_Syntax_Syntax.Tm_let (((((true), (lbs3))), (e3)))))
end))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, asc, eff) -> begin
(

let uu____9078 = (ff t2)
in (bind uu____9078 (fun t3 -> (ret (FStar_Syntax_Syntax.Tm_ascribed (((t3), (asc), (eff))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t2, m) -> begin
(

let uu____9109 = (ff t2)
in (bind uu____9109 (fun t3 -> (ret (FStar_Syntax_Syntax.Tm_meta (((t3), (m))))))))
end
| uu____9116 -> begin
(ret tn)
end))
in (bind tn1 (fun tn2 -> (

let t' = (

let uu___424_9123 = t1
in {FStar_Syntax_Syntax.n = tn2; FStar_Syntax_Syntax.pos = uu___424_9123.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___424_9123.FStar_Syntax_Syntax.vars})
in (match ((Prims.op_Equality d FStar_Tactics_Types.BottomUp)) with
| true -> begin
(f env t')
end
| uu____9127 -> begin
(ret t')
end)))))))))))


let pointwise_rec : FStar_Tactics_Types.proofstate  ->  unit tac  ->  FStar_Options.optionstate  ->  Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun ps tau opts label1 env t -> (

let uu____9170 = (FStar_TypeChecker_TcTerm.tc_term (

let uu___426_9179 = env
in {FStar_TypeChecker_Env.solver = uu___426_9179.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___426_9179.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___426_9179.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___426_9179.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___426_9179.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___426_9179.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___426_9179.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___426_9179.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___426_9179.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___426_9179.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___426_9179.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___426_9179.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___426_9179.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___426_9179.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___426_9179.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___426_9179.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___426_9179.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___426_9179.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___426_9179.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___426_9179.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___426_9179.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___426_9179.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___426_9179.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___426_9179.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___426_9179.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___426_9179.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___426_9179.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___426_9179.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___426_9179.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___426_9179.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___426_9179.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___426_9179.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___426_9179.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___426_9179.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___426_9179.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___426_9179.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___426_9179.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___426_9179.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___426_9179.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___426_9179.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___426_9179.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___426_9179.FStar_TypeChecker_Env.nbe}) t)
in (match (uu____9170) with
| (t1, lcomp, g) -> begin
(

let uu____9186 = ((

let uu____9190 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp)
in (not (uu____9190))) || (

let uu____9193 = (FStar_TypeChecker_Env.is_trivial g)
in (not (uu____9193))))
in (match (uu____9186) with
| true -> begin
(ret t1)
end
| uu____9198 -> begin
(

let rewrite_eq = (

let typ = lcomp.FStar_Syntax_Syntax.res_typ
in (

let uu____9204 = (new_uvar "pointwise_rec" env typ)
in (bind uu____9204 (fun uu____9221 -> (match (uu____9221) with
| (ut, uvar_ut) -> begin
((log ps (fun uu____9234 -> (

let uu____9235 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____9237 = (FStar_Syntax_Print.term_to_string ut)
in (FStar_Util.print2 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n" uu____9235 uu____9237)))));
(

let uu____9240 = (

let uu____9243 = (

let uu____9244 = (FStar_TypeChecker_TcTerm.universe_of env typ)
in (FStar_Syntax_Util.mk_eq2 uu____9244 typ t1 ut))
in (add_irrelevant_goal "pointwise_rec equation" env uu____9243 opts label1))
in (bind uu____9240 (fun uu____9248 -> (

let uu____9249 = (bind tau (fun uu____9255 -> (

let ut1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env ut)
in ((log ps (fun uu____9261 -> (

let uu____9262 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____9264 = (FStar_Syntax_Print.term_to_string ut1)
in (FStar_Util.print2 "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n" uu____9262 uu____9264)))));
(ret ut1);
))))
in (focus uu____9249)))));
)
end)))))
in (

let uu____9267 = (catch rewrite_eq)
in (bind uu____9267 (fun x -> (match (x) with
| FStar_Util.Inl (FStar_Tactics_Types.TacticFailure ("SKIP")) -> begin
(ret t1)
end
| FStar_Util.Inl (e) -> begin
(traise e)
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
| uu____9392 -> begin
c
end))
in (

let maybe_continue = (fun ctrl1 t1 k -> (match ((Prims.op_Equality ctrl1 globalStop)) with
| true -> begin
(ret ((t1), (globalStop)))
end
| uu____9464 -> begin
(match ((Prims.op_Equality ctrl1 proceedToNextSubtree)) with
| true -> begin
(ret ((t1), (keepGoing)))
end
| uu____9483 -> begin
(k t1)
end)
end))
in (

let uu____9485 = (FStar_Syntax_Subst.compress t)
in (maybe_continue ctrl uu____9485 (fun t1 -> (

let uu____9493 = (f env (

let uu___429_9502 = t1
in {FStar_Syntax_Syntax.n = t1.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = uu___429_9502.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___429_9502.FStar_Syntax_Syntax.vars}))
in (bind uu____9493 (fun uu____9518 -> (match (uu____9518) with
| (t2, ctrl1) -> begin
(maybe_continue ctrl1 t2 (fun t3 -> (

let uu____9541 = (

let uu____9542 = (FStar_Syntax_Subst.compress t3)
in uu____9542.FStar_Syntax_Syntax.n)
in (match (uu____9541) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____9579 = (ctrl_tac_fold f env ctrl1 hd1)
in (bind uu____9579 (fun uu____9604 -> (match (uu____9604) with
| (hd2, ctrl2) -> begin
(

let ctrl3 = (keep_going ctrl2)
in (

let uu____9620 = (ctrl_tac_fold_args f env ctrl3 args)
in (bind uu____9620 (fun uu____9647 -> (match (uu____9647) with
| (args1, ctrl4) -> begin
(ret (((

let uu___427_9677 = t3
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app (((hd2), (args1))); FStar_Syntax_Syntax.pos = uu___427_9677.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___427_9677.FStar_Syntax_Syntax.vars})), (ctrl4)))
end)))))
end))))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t4, k) -> begin
(

let uu____9719 = (FStar_Syntax_Subst.open_term bs t4)
in (match (uu____9719) with
| (bs1, t') -> begin
(

let uu____9734 = (

let uu____9741 = (FStar_TypeChecker_Env.push_binders env bs1)
in (ctrl_tac_fold f uu____9741 ctrl1 t'))
in (bind uu____9734 (fun uu____9759 -> (match (uu____9759) with
| (t'', ctrl2) -> begin
(

let uu____9774 = (

let uu____9781 = (

let uu___428_9784 = t4
in (

let uu____9787 = (

let uu____9788 = (

let uu____9807 = (FStar_Syntax_Subst.close_binders bs1)
in (

let uu____9816 = (FStar_Syntax_Subst.close bs1 t'')
in ((uu____9807), (uu____9816), (k))))
in FStar_Syntax_Syntax.Tm_abs (uu____9788))
in {FStar_Syntax_Syntax.n = uu____9787; FStar_Syntax_Syntax.pos = uu___428_9784.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___428_9784.FStar_Syntax_Syntax.vars}))
in ((uu____9781), (ctrl2)))
in (ret uu____9774))
end))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(ret ((t3), (ctrl1)))
end
| uu____9869 -> begin
(ret ((t3), (ctrl1)))
end))))
end))))))))))
and ctrl_tac_fold_args : (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term ctrl_tac)  ->  env  ->  ctrl  ->  FStar_Syntax_Syntax.arg Prims.list  ->  FStar_Syntax_Syntax.arg Prims.list ctrl_tac = (fun f env ctrl ts -> (match (ts) with
| [] -> begin
(ret (([]), (ctrl)))
end
| ((t, q))::ts1 -> begin
(

let uu____9916 = (ctrl_tac_fold f env ctrl t)
in (bind uu____9916 (fun uu____9940 -> (match (uu____9940) with
| (t1, ctrl1) -> begin
(

let uu____9955 = (ctrl_tac_fold_args f env ctrl1 ts1)
in (bind uu____9955 (fun uu____9982 -> (match (uu____9982) with
| (ts2, ctrl2) -> begin
(ret (((((t1), (q)))::ts2), (ctrl2)))
end))))
end))))
end))


let rewrite_rec : FStar_Tactics_Types.proofstate  ->  (FStar_Syntax_Syntax.term  ->  rewrite_result ctrl_tac)  ->  unit tac  ->  FStar_Options.optionstate  ->  Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term ctrl_tac = (fun ps ctrl rewriter opts label1 env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let uu____10076 = (

let uu____10084 = (add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true opts label1)
in (bind uu____10084 (fun uu____10095 -> (

let uu____10096 = (ctrl t1)
in (bind uu____10096 (fun res -> (

let uu____10123 = (trivial ())
in (bind uu____10123 (fun uu____10132 -> (ret res))))))))))
in (bind uu____10076 (fun uu____10150 -> (match (uu____10150) with
| (should_rewrite, ctrl1) -> begin
(match ((not (should_rewrite))) with
| true -> begin
(ret ((t1), (ctrl1)))
end
| uu____10177 -> begin
(

let uu____10179 = (FStar_TypeChecker_TcTerm.tc_term (

let uu___430_10188 = env
in {FStar_TypeChecker_Env.solver = uu___430_10188.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___430_10188.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___430_10188.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___430_10188.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___430_10188.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___430_10188.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___430_10188.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___430_10188.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___430_10188.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___430_10188.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___430_10188.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___430_10188.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___430_10188.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___430_10188.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___430_10188.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___430_10188.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___430_10188.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___430_10188.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___430_10188.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___430_10188.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___430_10188.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___430_10188.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___430_10188.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___430_10188.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___430_10188.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___430_10188.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___430_10188.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___430_10188.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___430_10188.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___430_10188.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___430_10188.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___430_10188.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___430_10188.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___430_10188.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___430_10188.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___430_10188.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___430_10188.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___430_10188.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___430_10188.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___430_10188.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___430_10188.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___430_10188.FStar_TypeChecker_Env.nbe}) t1)
in (match (uu____10179) with
| (t2, lcomp, g) -> begin
(

let uu____10199 = ((

let uu____10203 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp)
in (not (uu____10203))) || (

let uu____10206 = (FStar_TypeChecker_Env.is_trivial g)
in (not (uu____10206))))
in (match (uu____10199) with
| true -> begin
(ret ((t2), (globalStop)))
end
| uu____10219 -> begin
(

let typ = lcomp.FStar_Syntax_Syntax.res_typ
in (

let uu____10222 = (new_uvar "pointwise_rec" env typ)
in (bind uu____10222 (fun uu____10243 -> (match (uu____10243) with
| (ut, uvar_ut) -> begin
((log ps (fun uu____10260 -> (

let uu____10261 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____10263 = (FStar_Syntax_Print.term_to_string ut)
in (FStar_Util.print2 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n" uu____10261 uu____10263)))));
(

let uu____10266 = (

let uu____10269 = (

let uu____10270 = (FStar_TypeChecker_TcTerm.universe_of env typ)
in (FStar_Syntax_Util.mk_eq2 uu____10270 typ t2 ut))
in (add_irrelevant_goal "rewrite_rec equation" env uu____10269 opts label1))
in (bind uu____10266 (fun uu____10278 -> (

let uu____10279 = (bind rewriter (fun uu____10293 -> (

let ut1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env ut)
in ((log ps (fun uu____10299 -> (

let uu____10300 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____10302 = (FStar_Syntax_Print.term_to_string ut1)
in (FStar_Util.print2 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n" uu____10300 uu____10302)))));
(ret ((ut1), (ctrl1)));
))))
in (focus uu____10279)))));
)
end)))))
end))
end))
end)
end))))))


let topdown_rewrite : (FStar_Syntax_Syntax.term  ->  (Prims.bool * FStar_BigInt.t) tac)  ->  unit tac  ->  unit tac = (fun ctrl rewriter -> (

let uu____10348 = (bind get (fun ps -> (

let uu____10358 = (match (ps.FStar_Tactics_Types.goals) with
| (g)::gs -> begin
((g), (gs))
end
| [] -> begin
(failwith "no goals")
end)
in (match (uu____10358) with
| (g, gs) -> begin
(

let gt1 = (FStar_Tactics_Types.goal_type g)
in ((log ps (fun uu____10396 -> (

let uu____10397 = (FStar_Syntax_Print.term_to_string gt1)
in (FStar_Util.print1 "Topdown_rewrite starting with %s\n" uu____10397))));
(bind dismiss_all (fun uu____10402 -> (

let uu____10403 = (

let uu____10410 = (FStar_Tactics_Types.goal_env g)
in (ctrl_tac_fold (rewrite_rec ps ctrl rewriter g.FStar_Tactics_Types.opts g.FStar_Tactics_Types.label) uu____10410 keepGoing gt1))
in (bind uu____10403 (fun uu____10422 -> (match (uu____10422) with
| (gt', uu____10430) -> begin
((log ps (fun uu____10434 -> (

let uu____10435 = (FStar_Syntax_Print.term_to_string gt')
in (FStar_Util.print1 "Topdown_rewrite seems to have succeded with %s\n" uu____10435))));
(

let uu____10438 = (push_goals gs)
in (bind uu____10438 (fun uu____10443 -> (

let uu____10444 = (

let uu____10447 = (FStar_Tactics_Types.goal_with_type g gt')
in (uu____10447)::[])
in (add_goals uu____10444)))));
)
end))))));
))
end))))
in (FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____10348)))


let pointwise : FStar_Tactics_Types.direction  ->  unit tac  ->  unit tac = (fun d tau -> (

let uu____10472 = (bind get (fun ps -> (

let uu____10482 = (match (ps.FStar_Tactics_Types.goals) with
| (g)::gs -> begin
((g), (gs))
end
| [] -> begin
(failwith "no goals")
end)
in (match (uu____10482) with
| (g, gs) -> begin
(

let gt1 = (FStar_Tactics_Types.goal_type g)
in ((log ps (fun uu____10520 -> (

let uu____10521 = (FStar_Syntax_Print.term_to_string gt1)
in (FStar_Util.print1 "Pointwise starting with %s\n" uu____10521))));
(bind dismiss_all (fun uu____10526 -> (

let uu____10527 = (

let uu____10530 = (FStar_Tactics_Types.goal_env g)
in (tac_fold_env d (pointwise_rec ps tau g.FStar_Tactics_Types.opts g.FStar_Tactics_Types.label) uu____10530 gt1))
in (bind uu____10527 (fun gt' -> ((log ps (fun uu____10538 -> (

let uu____10539 = (FStar_Syntax_Print.term_to_string gt')
in (FStar_Util.print1 "Pointwise seems to have succeded with %s\n" uu____10539))));
(

let uu____10542 = (push_goals gs)
in (bind uu____10542 (fun uu____10547 -> (

let uu____10548 = (

let uu____10551 = (FStar_Tactics_Types.goal_with_type g gt')
in (uu____10551)::[])
in (add_goals uu____10548)))));
))))));
))
end))))
in (FStar_All.pipe_left (wrap_err "pointwise") uu____10472)))


let trefl : unit  ->  unit tac = (fun uu____10564 -> (

let uu____10567 = (

let uu____10570 = (cur_goal ())
in (bind uu____10570 (fun g -> (

let uu____10588 = (

let uu____10593 = (FStar_Tactics_Types.goal_type g)
in (FStar_Syntax_Util.un_squash uu____10593))
in (match (uu____10588) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____10601 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____10601) with
| (hd1, args) -> begin
(

let uu____10640 = (

let uu____10653 = (

let uu____10654 = (FStar_Syntax_Util.un_uinst hd1)
in uu____10654.FStar_Syntax_Syntax.n)
in ((uu____10653), (args)))
in (match (uu____10640) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____10668)::((l, uu____10670))::((r, uu____10672))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid) -> begin
(

let uu____10719 = (

let uu____10723 = (FStar_Tactics_Types.goal_env g)
in (do_unify uu____10723 l r))
in (bind uu____10719 (fun b -> (match (b) with
| true -> begin
(solve' g FStar_Syntax_Util.exp_unit)
end
| uu____10731 -> begin
(

let l1 = (

let uu____10734 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.UnfoldTac)::[]) uu____10734 l))
in (

let r1 = (

let uu____10736 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.UnfoldTac)::[]) uu____10736 r))
in (

let uu____10737 = (

let uu____10741 = (FStar_Tactics_Types.goal_env g)
in (do_unify uu____10741 l1 r1))
in (bind uu____10737 (fun b1 -> (match (b1) with
| true -> begin
(solve' g FStar_Syntax_Util.exp_unit)
end
| uu____10749 -> begin
(

let uu____10751 = (

let uu____10753 = (FStar_Tactics_Types.goal_env g)
in (tts uu____10753 l1))
in (

let uu____10754 = (

let uu____10756 = (FStar_Tactics_Types.goal_env g)
in (tts uu____10756 r1))
in (fail2 "not a trivial equality ((%s) vs (%s))" uu____10751 uu____10754)))
end))))))
end))))
end
| (hd2, uu____10759) -> begin
(

let uu____10776 = (

let uu____10778 = (FStar_Tactics_Types.goal_env g)
in (tts uu____10778 t))
in (fail1 "trefl: not an equality (%s)" uu____10776))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
(fail "not an irrelevant goal")
end)))))
in (FStar_All.pipe_left (wrap_err "trefl") uu____10567)))


let dup : unit  ->  unit tac = (fun uu____10795 -> (

let uu____10798 = (cur_goal ())
in (bind uu____10798 (fun g -> (

let uu____10804 = (

let uu____10811 = (FStar_Tactics_Types.goal_env g)
in (

let uu____10812 = (FStar_Tactics_Types.goal_type g)
in (new_uvar "dup" uu____10811 uu____10812)))
in (bind uu____10804 (fun uu____10822 -> (match (uu____10822) with
| (u, u_uvar) -> begin
(

let g' = (

let uu___431_10832 = g
in {FStar_Tactics_Types.goal_main_env = uu___431_10832.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = u_uvar; FStar_Tactics_Types.opts = uu___431_10832.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___431_10832.FStar_Tactics_Types.is_guard; FStar_Tactics_Types.label = uu___431_10832.FStar_Tactics_Types.label})
in (bind __dismiss (fun uu____10835 -> (

let uu____10836 = (

let uu____10839 = (FStar_Tactics_Types.goal_env g)
in (

let uu____10840 = (

let uu____10841 = (

let uu____10842 = (FStar_Tactics_Types.goal_env g)
in (

let uu____10843 = (FStar_Tactics_Types.goal_type g)
in (FStar_TypeChecker_TcTerm.universe_of uu____10842 uu____10843)))
in (

let uu____10844 = (FStar_Tactics_Types.goal_type g)
in (

let uu____10845 = (FStar_Tactics_Types.goal_witness g)
in (FStar_Syntax_Util.mk_eq2 uu____10841 uu____10844 u uu____10845))))
in (add_irrelevant_goal "dup equation" uu____10839 uu____10840 g.FStar_Tactics_Types.opts g.FStar_Tactics_Types.label)))
in (bind uu____10836 (fun uu____10849 -> (

let uu____10850 = (add_goals ((g')::[]))
in (bind uu____10850 (fun uu____10854 -> (ret ()))))))))))
end))))))))


let rec longest_prefix : 'a . ('a  ->  'a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list  ->  ('a Prims.list * 'a Prims.list * 'a Prims.list) = (fun f l1 l2 -> (

let rec aux = (fun acc l11 l21 -> (match (((l11), (l21))) with
| ((x)::xs, (y)::ys) -> begin
(

let uu____10980 = (f x y)
in (match (uu____10980) with
| true -> begin
(aux ((x)::acc) xs ys)
end
| uu____10995 -> begin
((acc), (xs), (ys))
end))
end
| uu____11003 -> begin
((acc), (l11), (l21))
end))
in (

let uu____11018 = (aux [] l1 l2)
in (match (uu____11018) with
| (pr, t1, t2) -> begin
(((FStar_List.rev pr)), (t1), (t2))
end))))


let join_goals : FStar_Tactics_Types.goal  ->  FStar_Tactics_Types.goal  ->  FStar_Tactics_Types.goal tac = (fun g1 g2 -> (

let close_forall_no_univs1 = (fun bs f -> (FStar_List.fold_right (fun b f1 -> (FStar_Syntax_Util.mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1)) bs f))
in (

let uu____11124 = (get_phi g1)
in (match (uu____11124) with
| FStar_Pervasives_Native.None -> begin
(fail "goal 1 is not irrelevant")
end
| FStar_Pervasives_Native.Some (phi1) -> begin
(

let uu____11131 = (get_phi g2)
in (match (uu____11131) with
| FStar_Pervasives_Native.None -> begin
(fail "goal 2 is not irrelevant")
end
| FStar_Pervasives_Native.Some (phi2) -> begin
(

let gamma1 = g1.FStar_Tactics_Types.goal_ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma
in (

let gamma2 = g2.FStar_Tactics_Types.goal_ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma
in (

let uu____11144 = (longest_prefix FStar_Syntax_Syntax.eq_binding (FStar_List.rev gamma1) (FStar_List.rev gamma2))
in (match (uu____11144) with
| (gamma, r1, r2) -> begin
(

let t1 = (

let uu____11175 = (FStar_TypeChecker_Env.binders_of_bindings (FStar_List.rev r1))
in (close_forall_no_univs1 uu____11175 phi1))
in (

let t2 = (

let uu____11185 = (FStar_TypeChecker_Env.binders_of_bindings (FStar_List.rev r2))
in (close_forall_no_univs1 uu____11185 phi2))
in (

let uu____11194 = (set_solution g1 FStar_Syntax_Util.exp_unit)
in (bind uu____11194 (fun uu____11199 -> (

let uu____11200 = (set_solution g2 FStar_Syntax_Util.exp_unit)
in (bind uu____11200 (fun uu____11207 -> (

let ng = (FStar_Syntax_Util.mk_conj t1 t2)
in (

let nenv = (

let uu___432_11212 = (FStar_Tactics_Types.goal_env g1)
in (

let uu____11213 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {FStar_TypeChecker_Env.solver = uu___432_11212.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___432_11212.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___432_11212.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = (FStar_List.rev gamma); FStar_TypeChecker_Env.gamma_sig = uu___432_11212.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu____11213; FStar_TypeChecker_Env.modules = uu___432_11212.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___432_11212.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___432_11212.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___432_11212.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___432_11212.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___432_11212.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___432_11212.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___432_11212.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___432_11212.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___432_11212.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___432_11212.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___432_11212.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___432_11212.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___432_11212.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___432_11212.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___432_11212.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___432_11212.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___432_11212.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___432_11212.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___432_11212.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___432_11212.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___432_11212.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___432_11212.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___432_11212.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___432_11212.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___432_11212.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___432_11212.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___432_11212.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___432_11212.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___432_11212.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___432_11212.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___432_11212.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___432_11212.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___432_11212.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___432_11212.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___432_11212.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___432_11212.FStar_TypeChecker_Env.nbe}))
in (

let uu____11217 = (mk_irrelevant_goal "joined" nenv ng g1.FStar_Tactics_Types.opts g1.FStar_Tactics_Types.label)
in (bind uu____11217 (fun goal -> (mlog (fun uu____11227 -> (

let uu____11228 = (goal_to_string_verbose g1)
in (

let uu____11230 = (goal_to_string_verbose g2)
in (

let uu____11232 = (goal_to_string_verbose goal)
in (FStar_Util.print3 "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n" uu____11228 uu____11230 uu____11232))))) (fun uu____11236 -> (ret goal))))))))))))))))
end))))
end))
end))))


let join : unit  ->  unit tac = (fun uu____11244 -> (bind get (fun ps -> (match (ps.FStar_Tactics_Types.goals) with
| (g1)::(g2)::gs -> begin
(

let uu____11260 = (set (

let uu___433_11265 = ps
in {FStar_Tactics_Types.main_context = uu___433_11265.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___433_11265.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___433_11265.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = gs; FStar_Tactics_Types.smt_goals = uu___433_11265.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___433_11265.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___433_11265.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___433_11265.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___433_11265.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___433_11265.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___433_11265.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___433_11265.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___433_11265.FStar_Tactics_Types.local_state}))
in (bind uu____11260 (fun uu____11268 -> (

let uu____11269 = (join_goals g1 g2)
in (bind uu____11269 (fun g12 -> (add_goals ((g12)::[]))))))))
end
| uu____11274 -> begin
(fail "join: less than 2 goals")
end))))


let cases : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac = (fun t -> (

let uu____11296 = (

let uu____11303 = (cur_goal ())
in (bind uu____11303 (fun g -> (

let uu____11313 = (

let uu____11322 = (FStar_Tactics_Types.goal_env g)
in (__tc uu____11322 t))
in (bind uu____11313 (fun uu____11350 -> (match (uu____11350) with
| (t1, typ, guard) -> begin
(

let uu____11366 = (FStar_Syntax_Util.head_and_args typ)
in (match (uu____11366) with
| (hd1, args) -> begin
(

let uu____11415 = (

let uu____11430 = (

let uu____11431 = (FStar_Syntax_Util.un_uinst hd1)
in uu____11431.FStar_Syntax_Syntax.n)
in ((uu____11430), (args)))
in (match (uu____11415) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____11452))::((q, uu____11454))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid) -> begin
(

let v_p = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p)
in (

let v_q = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None q)
in (

let g1 = (

let uu____11508 = (

let uu____11509 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Env.push_bv uu____11509 v_p))
in (FStar_Tactics_Types.goal_with_env g uu____11508))
in (

let g2 = (

let uu____11511 = (

let uu____11512 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Env.push_bv uu____11512 v_q))
in (FStar_Tactics_Types.goal_with_env g uu____11511))
in (bind __dismiss (fun uu____11519 -> (

let uu____11520 = (add_goals ((g1)::(g2)::[]))
in (bind uu____11520 (fun uu____11529 -> (

let uu____11530 = (

let uu____11535 = (FStar_Syntax_Syntax.bv_to_name v_p)
in (

let uu____11536 = (FStar_Syntax_Syntax.bv_to_name v_q)
in ((uu____11535), (uu____11536))))
in (ret uu____11530)))))))))))
end
| uu____11541 -> begin
(

let uu____11556 = (

let uu____11558 = (FStar_Tactics_Types.goal_env g)
in (tts uu____11558 typ))
in (fail1 "Not a disjunction: %s" uu____11556))
end))
end))
end)))))))
in (FStar_All.pipe_left (wrap_err "cases") uu____11296)))


let set_options : Prims.string  ->  unit tac = (fun s -> (

let uu____11593 = (

let uu____11596 = (cur_goal ())
in (bind uu____11596 (fun g -> ((FStar_Options.push ());
(

let uu____11609 = (FStar_Util.smap_copy g.FStar_Tactics_Types.opts)
in (FStar_Options.set uu____11609));
(

let res = (FStar_Options.set_options FStar_Options.Set s)
in (

let opts' = (FStar_Options.peek ())
in ((FStar_Options.pop ());
(match (res) with
| FStar_Getopt.Success -> begin
(

let g' = (

let uu___434_11616 = g
in {FStar_Tactics_Types.goal_main_env = uu___434_11616.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = uu___434_11616.FStar_Tactics_Types.goal_ctx_uvar; FStar_Tactics_Types.opts = opts'; FStar_Tactics_Types.is_guard = uu___434_11616.FStar_Tactics_Types.is_guard; FStar_Tactics_Types.label = uu___434_11616.FStar_Tactics_Types.label})
in (replace_cur g'))
end
| FStar_Getopt.Error (err) -> begin
(fail2 "Setting options `%s` failed: %s" s err)
end
| FStar_Getopt.Help -> begin
(fail1 "Setting options `%s` failed (got `Help`?)" s)
end);
)));
))))
in (FStar_All.pipe_left (wrap_err "set_options") uu____11593)))


let top_env : unit  ->  env tac = (fun uu____11633 -> (bind get (fun ps -> (FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context))))


let lax_on : unit  ->  Prims.bool tac = (fun uu____11648 -> (

let uu____11652 = (cur_goal ())
in (bind uu____11652 (fun g -> (

let uu____11659 = ((FStar_Options.lax ()) || (

let uu____11662 = (FStar_Tactics_Types.goal_env g)
in uu____11662.FStar_TypeChecker_Env.lax))
in (ret uu____11659))))))


let unquote : FStar_Reflection_Data.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun ty tm -> (

let uu____11679 = (mlog (fun uu____11684 -> (

let uu____11685 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "unquote: tm = %s\n" uu____11685))) (fun uu____11690 -> (

let uu____11691 = (cur_goal ())
in (bind uu____11691 (fun goal -> (

let env = (

let uu____11699 = (FStar_Tactics_Types.goal_env goal)
in (FStar_TypeChecker_Env.set_expected_typ uu____11699 ty))
in (

let uu____11700 = (__tc_ghost env tm)
in (bind uu____11700 (fun uu____11719 -> (match (uu____11719) with
| (tm1, typ, guard) -> begin
(mlog (fun uu____11733 -> (

let uu____11734 = (FStar_Syntax_Print.term_to_string tm1)
in (FStar_Util.print1 "unquote: tm\' = %s\n" uu____11734))) (fun uu____11738 -> (mlog (fun uu____11741 -> (

let uu____11742 = (FStar_Syntax_Print.term_to_string typ)
in (FStar_Util.print1 "unquote: typ = %s\n" uu____11742))) (fun uu____11747 -> (

let uu____11748 = (proc_guard "unquote" env guard)
in (bind uu____11748 (fun uu____11753 -> (ret tm1))))))))
end))))))))))
in (FStar_All.pipe_left (wrap_err "unquote") uu____11679)))


let uvar_env : env  ->  FStar_Reflection_Data.typ FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term tac = (fun env ty -> (

let uu____11778 = (match (ty) with
| FStar_Pervasives_Native.Some (ty1) -> begin
(ret ty1)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____11784 = (

let uu____11791 = (

let uu____11792 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11792))
in (new_uvar "uvar_env.2" env uu____11791))
in (bind uu____11784 (fun uu____11809 -> (match (uu____11809) with
| (typ, uvar_typ) -> begin
(ret typ)
end))))
end)
in (bind uu____11778 (fun typ -> (

let uu____11821 = (new_uvar "uvar_env" env typ)
in (bind uu____11821 (fun uu____11836 -> (match (uu____11836) with
| (t, uvar_t) -> begin
(ret t)
end))))))))


let unshelve : FStar_Syntax_Syntax.term  ->  unit tac = (fun t -> (

let uu____11855 = (bind get (fun ps -> (

let env = ps.FStar_Tactics_Types.main_context
in (

let opts = (match (ps.FStar_Tactics_Types.goals) with
| (g)::uu____11874 -> begin
g.FStar_Tactics_Types.opts
end
| uu____11877 -> begin
(FStar_Options.peek ())
end)
in (

let uu____11880 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____11880) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (ctx_uvar, uu____11900); FStar_Syntax_Syntax.pos = uu____11901; FStar_Syntax_Syntax.vars = uu____11902}, uu____11903) -> begin
(

let env1 = (

let uu___435_11945 = env
in {FStar_TypeChecker_Env.solver = uu___435_11945.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___435_11945.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___435_11945.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_TypeChecker_Env.gamma_sig = uu___435_11945.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___435_11945.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___435_11945.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___435_11945.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___435_11945.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___435_11945.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___435_11945.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___435_11945.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___435_11945.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___435_11945.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___435_11945.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___435_11945.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___435_11945.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___435_11945.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___435_11945.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___435_11945.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___435_11945.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___435_11945.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___435_11945.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___435_11945.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___435_11945.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___435_11945.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___435_11945.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___435_11945.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___435_11945.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___435_11945.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___435_11945.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___435_11945.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___435_11945.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___435_11945.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___435_11945.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___435_11945.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___435_11945.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___435_11945.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___435_11945.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___435_11945.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___435_11945.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___435_11945.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___435_11945.FStar_TypeChecker_Env.nbe})
in (

let g = (FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false "")
in (

let uu____11949 = (

let uu____11952 = (bnorm_goal g)
in (uu____11952)::[])
in (add_goals uu____11949))))
end
| uu____11953 -> begin
(fail "not a uvar")
end))))))
in (FStar_All.pipe_left (wrap_err "unshelve") uu____11855)))


let tac_and : Prims.bool tac  ->  Prims.bool tac  ->  Prims.bool tac = (fun t1 t2 -> (

let comp = (bind t1 (fun b -> (

let uu____12015 = (match (b) with
| true -> begin
t2
end
| uu____12023 -> begin
(ret false)
end)
in (bind uu____12015 (fun b' -> (match (b') with
| true -> begin
(ret b')
end
| uu____12037 -> begin
(fail "")
end))))))
in (

let uu____12041 = (trytac comp)
in (bind uu____12041 (fun uu___365_12053 -> (match (uu___365_12053) with
| FStar_Pervasives_Native.Some (true) -> begin
(ret true)
end
| FStar_Pervasives_Native.Some (false) -> begin
(failwith "impossible")
end
| FStar_Pervasives_Native.None -> begin
(ret false)
end))))))


let unify_env : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun e t1 t2 -> (

let uu____12095 = (bind get (fun ps -> (

let uu____12103 = (__tc e t1)
in (bind uu____12103 (fun uu____12124 -> (match (uu____12124) with
| (t11, ty1, g1) -> begin
(

let uu____12137 = (__tc e t2)
in (bind uu____12137 (fun uu____12158 -> (match (uu____12158) with
| (t21, ty2, g2) -> begin
(

let uu____12171 = (proc_guard "unify_env g1" e g1)
in (bind uu____12171 (fun uu____12178 -> (

let uu____12179 = (proc_guard "unify_env g2" e g2)
in (bind uu____12179 (fun uu____12187 -> (

let uu____12188 = (do_unify e ty1 ty2)
in (

let uu____12192 = (do_unify e t11 t21)
in (tac_and uu____12188 uu____12192)))))))))
end))))
end))))))
in (FStar_All.pipe_left (wrap_err "unify_env") uu____12095)))


let launch_process : Prims.string  ->  Prims.string Prims.list  ->  Prims.string  ->  Prims.string tac = (fun prog args input -> (bind idtac (fun uu____12240 -> (

let uu____12241 = (FStar_Options.unsafe_tactic_exec ())
in (match (uu____12241) with
| true -> begin
(

let s = (FStar_Util.run_process "tactic_launch" prog args (FStar_Pervasives_Native.Some (input)))
in (ret s))
end
| uu____12252 -> begin
(fail "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
end)))))


let fresh_bv_named : Prims.string  ->  FStar_Reflection_Data.typ  ->  FStar_Syntax_Syntax.bv tac = (fun nm t -> (bind idtac (fun uu____12275 -> (

let uu____12276 = (FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t)
in (ret uu____12276)))))


let change : FStar_Reflection_Data.typ  ->  unit tac = (fun ty -> (

let uu____12287 = (mlog (fun uu____12292 -> (

let uu____12293 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.print1 "change: ty = %s\n" uu____12293))) (fun uu____12298 -> (

let uu____12299 = (cur_goal ())
in (bind uu____12299 (fun g -> (

let uu____12305 = (

let uu____12314 = (FStar_Tactics_Types.goal_env g)
in (__tc uu____12314 ty))
in (bind uu____12305 (fun uu____12326 -> (match (uu____12326) with
| (ty1, uu____12336, guard) -> begin
(

let uu____12338 = (

let uu____12341 = (FStar_Tactics_Types.goal_env g)
in (proc_guard "change" uu____12341 guard))
in (bind uu____12338 (fun uu____12345 -> (

let uu____12346 = (

let uu____12350 = (FStar_Tactics_Types.goal_env g)
in (

let uu____12351 = (FStar_Tactics_Types.goal_type g)
in (do_unify uu____12350 uu____12351 ty1)))
in (bind uu____12346 (fun bb -> (match (bb) with
| true -> begin
(

let uu____12360 = (FStar_Tactics_Types.goal_with_type g ty1)
in (replace_cur uu____12360))
end
| uu____12361 -> begin
(

let steps = (FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::[]
in (

let ng = (

let uu____12367 = (FStar_Tactics_Types.goal_env g)
in (

let uu____12368 = (FStar_Tactics_Types.goal_type g)
in (normalize steps uu____12367 uu____12368)))
in (

let nty = (

let uu____12370 = (FStar_Tactics_Types.goal_env g)
in (normalize steps uu____12370 ty1))
in (

let uu____12371 = (

let uu____12375 = (FStar_Tactics_Types.goal_env g)
in (do_unify uu____12375 ng nty))
in (bind uu____12371 (fun b -> (match (b) with
| true -> begin
(

let uu____12384 = (FStar_Tactics_Types.goal_with_type g ty1)
in (replace_cur uu____12384))
end
| uu____12385 -> begin
(fail "not convertible")
end)))))))
end)))))))
end)))))))))
in (FStar_All.pipe_left (wrap_err "change") uu____12287)))


let failwhen : 'a . Prims.bool  ->  Prims.string  ->  (unit  ->  'a tac)  ->  'a tac = (fun b msg k -> (match (b) with
| true -> begin
(fail msg)
end
| uu____12434 -> begin
(k ())
end))


let t_destruct : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac = (fun s_tm -> (

let uu____12458 = (

let uu____12467 = (cur_goal ())
in (bind uu____12467 (fun g -> (

let uu____12479 = (

let uu____12488 = (FStar_Tactics_Types.goal_env g)
in (__tc uu____12488 s_tm))
in (bind uu____12479 (fun uu____12506 -> (match (uu____12506) with
| (s_tm1, s_ty, guard) -> begin
(

let uu____12524 = (

let uu____12527 = (FStar_Tactics_Types.goal_env g)
in (proc_guard "destruct" uu____12527 guard))
in (bind uu____12524 (fun uu____12540 -> (

let uu____12541 = (FStar_Syntax_Util.head_and_args' s_ty)
in (match (uu____12541) with
| (h, args) -> begin
(

let uu____12586 = (

let uu____12593 = (

let uu____12594 = (FStar_Syntax_Subst.compress h)
in uu____12594.FStar_Syntax_Syntax.n)
in (match (uu____12593) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(ret ((fv), ([])))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____12609; FStar_Syntax_Syntax.vars = uu____12610}, us) -> begin
(ret ((fv), (us)))
end
| uu____12620 -> begin
(fail "type is not an fv")
end))
in (bind uu____12586 (fun uu____12641 -> (match (uu____12641) with
| (fv, a_us) -> begin
(

let t_lid = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let uu____12657 = (

let uu____12660 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Env.lookup_sigelt uu____12660 t_lid))
in (match (uu____12657) with
| FStar_Pervasives_Native.None -> begin
(fail "type not found in environment")
end
| FStar_Pervasives_Native.Some (se) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_lid, t_us, t_ps, t_ty, mut, c_lids) -> begin
(failwhen (Prims.op_disEquality (FStar_List.length a_us) (FStar_List.length t_us)) "t_us don\'t match?" (fun uu____12711 -> (

let uu____12712 = (FStar_Syntax_Subst.open_term t_ps t_ty)
in (match (uu____12712) with
| (t_ps1, t_ty1) -> begin
(

let uu____12727 = (mapM (fun c_lid -> (

let uu____12755 = (

let uu____12758 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Env.lookup_sigelt uu____12758 c_lid))
in (match (uu____12755) with
| FStar_Pervasives_Native.None -> begin
(fail "ctor not found?")
end
| FStar_Pervasives_Native.Some (se1) -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (_c_lid, c_us, c_ty, _t_lid, nparam, mut1) -> begin
(

let fv1 = (FStar_Syntax_Syntax.lid_as_fv c_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (failwhen (Prims.op_disEquality (FStar_List.length a_us) (FStar_List.length c_us)) "t_us don\'t match?" (fun uu____12832 -> (

let s = (FStar_TypeChecker_Env.mk_univ_subst c_us a_us)
in (

let c_ty1 = (FStar_Syntax_Subst.subst s c_ty)
in (

let uu____12837 = (FStar_TypeChecker_Env.inst_tscheme ((c_us), (c_ty1)))
in (match (uu____12837) with
| (c_us1, c_ty2) -> begin
(

let uu____12860 = (FStar_Syntax_Util.arrow_formals_comp c_ty2)
in (match (uu____12860) with
| (bs, comp) -> begin
(

let uu____12903 = (FStar_List.splitAt nparam bs)
in (match (uu____12903) with
| (d_ps, bs1) -> begin
(

let uu____12976 = (

let uu____12978 = (FStar_Syntax_Util.is_total_comp comp)
in (not (uu____12978)))
in (failwhen uu____12976 "not total?" (fun uu____12997 -> (

let mk_pat = (fun p -> {FStar_Syntax_Syntax.v = p; FStar_Syntax_Syntax.p = s_tm1.FStar_Syntax_Syntax.pos})
in (

let is_imp = (fun uu___366_13014 -> (match (uu___366_13014) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____13018)) -> begin
true
end
| uu____13021 -> begin
false
end))
in (

let uu____13025 = (FStar_List.splitAt nparam args)
in (match (uu____13025) with
| (a_ps, a_is) -> begin
(failwhen (Prims.op_disEquality (FStar_List.length a_ps) (FStar_List.length d_ps)) "params not match?" (fun uu____13159 -> (

let d_ps_a_ps = (FStar_List.zip d_ps a_ps)
in (

let subst1 = (FStar_List.map (fun uu____13221 -> (match (uu____13221) with
| ((bv, uu____13241), (t, uu____13243)) -> begin
FStar_Syntax_Syntax.NT (((bv), (t)))
end)) d_ps_a_ps)
in (

let bs2 = (FStar_Syntax_Subst.subst_binders subst1 bs1)
in (

let subpats_1 = (FStar_List.map (fun uu____13313 -> (match (uu____13313) with
| ((bv, uu____13340), (t, uu____13342)) -> begin
(((mk_pat (FStar_Syntax_Syntax.Pat_dot_term (((bv), (t)))))), (true))
end)) d_ps_a_ps)
in (

let subpats_2 = (FStar_List.map (fun uu____13401 -> (match (uu____13401) with
| (bv, aq) -> begin
(((mk_pat (FStar_Syntax_Syntax.Pat_var (bv)))), ((is_imp aq)))
end)) bs2)
in (

let subpats = (FStar_List.append subpats_1 subpats_2)
in (

let pat = (mk_pat (FStar_Syntax_Syntax.Pat_cons (((fv1), (subpats)))))
in (

let env = (FStar_Tactics_Types.goal_env g)
in (

let cod = (FStar_Tactics_Types.goal_type g)
in (

let equ = (env.FStar_TypeChecker_Env.universe_of env s_ty)
in (

let uu____13456 = (FStar_TypeChecker_TcTerm.tc_pat (

let uu___436_13473 = env
in {FStar_TypeChecker_Env.solver = uu___436_13473.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___436_13473.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___436_13473.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___436_13473.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___436_13473.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___436_13473.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___436_13473.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___436_13473.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___436_13473.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___436_13473.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___436_13473.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___436_13473.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___436_13473.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___436_13473.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___436_13473.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___436_13473.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___436_13473.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___436_13473.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___436_13473.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___436_13473.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___436_13473.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___436_13473.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___436_13473.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___436_13473.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___436_13473.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___436_13473.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___436_13473.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___436_13473.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___436_13473.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___436_13473.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___436_13473.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___436_13473.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___436_13473.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___436_13473.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___436_13473.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___436_13473.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___436_13473.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___436_13473.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___436_13473.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___436_13473.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___436_13473.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___436_13473.FStar_TypeChecker_Env.nbe}) s_ty pat)
in (match (uu____13456) with
| (uu____13487, uu____13488, uu____13489, pat_t, uu____13491, _guard_pat) -> begin
(

let eq_b = (

let uu____13498 = (

let uu____13499 = (FStar_Syntax_Util.mk_eq2 equ s_ty s_tm1 pat_t)
in (FStar_Syntax_Util.mk_squash equ uu____13499))
in (FStar_Syntax_Syntax.gen_bv "breq" FStar_Pervasives_Native.None uu____13498))
in (

let cod1 = (

let uu____13504 = (

let uu____13513 = (FStar_Syntax_Syntax.mk_binder eq_b)
in (uu____13513)::[])
in (

let uu____13532 = (FStar_Syntax_Syntax.mk_Total cod)
in (FStar_Syntax_Util.arrow uu____13504 uu____13532)))
in (

let nty = (

let uu____13538 = (FStar_Syntax_Syntax.mk_Total cod1)
in (FStar_Syntax_Util.arrow bs2 uu____13538))
in (

let uu____13541 = (new_uvar "destruct branch" env nty)
in (bind uu____13541 (fun uu____13571 -> (match (uu____13571) with
| (uvt, uv) -> begin
(

let g' = (FStar_Tactics_Types.mk_goal env uv g.FStar_Tactics_Types.opts false g.FStar_Tactics_Types.label)
in (

let brt = (FStar_Syntax_Util.mk_app_binders uvt bs2)
in (

let brt1 = (

let uu____13598 = (

let uu____13609 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit)
in (uu____13609)::[])
in (FStar_Syntax_Util.mk_app brt uu____13598))
in (

let br = (FStar_Syntax_Subst.close_branch ((pat), (FStar_Pervasives_Native.None), (brt1)))
in (

let uu____13645 = (

let uu____13656 = (

let uu____13661 = (FStar_BigInt.of_int_fs (FStar_List.length bs2))
in ((fv1), (uu____13661)))
in ((g'), (br), (uu____13656)))
in (ret uu____13645))))))
end)))))))
end))))))))))))))
end)))))))
end))
end))
end)))))))
end
| uu____13682 -> begin
(fail "impossible: not a ctor")
end)
end))) c_lids)
in (bind uu____12727 (fun goal_brs -> (

let uu____13732 = (FStar_List.unzip3 goal_brs)
in (match (uu____13732) with
| (goals, brs, infos) -> begin
(

let w = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((s_tm1), (brs)))) FStar_Pervasives_Native.None s_tm1.FStar_Syntax_Syntax.pos)
in (

let uu____13805 = (solve' g w)
in (bind uu____13805 (fun uu____13816 -> (

let uu____13817 = (add_goals goals)
in (bind uu____13817 (fun uu____13827 -> (ret infos))))))))
end)))))
end))))
end
| uu____13834 -> begin
(fail "not an inductive type")
end)
end)))
end))))
end)))))
end)))))))
in (FStar_All.pipe_left (wrap_err "destruct") uu____12458)))


let rec last : 'a . 'a Prims.list  ->  'a = (fun l -> (match (l) with
| [] -> begin
(failwith "last: empty list")
end
| (x)::[] -> begin
x
end
| (uu____13883)::xs -> begin
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

let uu____13913 = (init xs)
in (x)::uu____13913)
end))


let rec inspect : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.term_view tac = (fun t -> (

let uu____13926 = (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let t2 = (FStar_Syntax_Util.un_uinst t1)
in (

let t3 = (FStar_Syntax_Util.unlazy_emb t2)
in (match (t3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t4, uu____13935) -> begin
(inspect t4)
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
(failwith "empty arguments on Tm_app")
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____14001 = (last args)
in (match (uu____14001) with
| (a, q) -> begin
(

let q' = (FStar_Reflection_Basic.inspect_aqual q)
in (

let uu____14031 = (

let uu____14032 = (

let uu____14037 = (

let uu____14038 = (

let uu____14043 = (init args)
in (FStar_Syntax_Syntax.mk_Tm_app hd1 uu____14043))
in (uu____14038 FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos))
in ((uu____14037), (((a), (q')))))
in FStar_Reflection_Data.Tv_App (uu____14032))
in (FStar_All.pipe_left ret uu____14031)))
end))
end
| FStar_Syntax_Syntax.Tm_abs ([], uu____14056, uu____14057) -> begin
(failwith "empty arguments on Tm_abs")
end
| FStar_Syntax_Syntax.Tm_abs (bs, t4, k) -> begin
(

let uu____14110 = (FStar_Syntax_Subst.open_term bs t4)
in (match (uu____14110) with
| (bs1, t5) -> begin
(match (bs1) with
| [] -> begin
(failwith "impossible")
end
| (b)::bs2 -> begin
(

let uu____14152 = (

let uu____14153 = (

let uu____14158 = (FStar_Syntax_Util.abs bs2 t5 k)
in ((b), (uu____14158)))
in FStar_Reflection_Data.Tv_Abs (uu____14153))
in (FStar_All.pipe_left ret uu____14152))
end)
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____14161) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type (())))
end
| FStar_Syntax_Syntax.Tm_arrow ([], k) -> begin
(failwith "empty binders on arrow")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____14186) -> begin
(

let uu____14201 = (FStar_Syntax_Util.arrow_one t3)
in (match (uu____14201) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (((b), (c)))))
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t4) -> begin
(

let b = (FStar_Syntax_Syntax.mk_binder bv)
in (

let uu____14232 = (FStar_Syntax_Subst.open_term ((b)::[]) t4)
in (match (uu____14232) with
| (b', t5) -> begin
(

let b1 = (match (b') with
| (b'1)::[] -> begin
b'1
end
| uu____14285 -> begin
(failwith "impossible")
end)
in (FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Refine ((((FStar_Pervasives_Native.fst b1)), (t5))))))
end)))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____14298 = (

let uu____14299 = (FStar_Reflection_Basic.inspect_const c)
in FStar_Reflection_Data.Tv_Const (uu____14299))
in (FStar_All.pipe_left ret uu____14298))
end
| FStar_Syntax_Syntax.Tm_uvar (ctx_u, s) -> begin
(

let uu____14320 = (

let uu____14321 = (

let uu____14326 = (

let uu____14327 = (FStar_Syntax_Unionfind.uvar_id ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_BigInt.of_int_fs uu____14327))
in ((uu____14326), (((ctx_u), (s)))))
in FStar_Reflection_Data.Tv_Uvar (uu____14321))
in (FStar_All.pipe_left ret uu____14320))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), t21) -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| uu____14363 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____14367) -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv) -> begin
(

let b = (FStar_Syntax_Syntax.mk_binder bv)
in (

let uu____14372 = (FStar_Syntax_Subst.open_term ((b)::[]) t21)
in (match (uu____14372) with
| (bs, t22) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____14425 -> begin
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
| uu____14463 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____14467) -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv) -> begin
(

let uu____14471 = (FStar_Syntax_Subst.open_let_rec ((lb)::[]) t21)
in (match (uu____14471) with
| (lbs, t22) -> begin
(match (lbs) with
| (lb1)::[] -> begin
(match (lb1.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____14491) -> begin
(ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv1) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Let (((true), (bv1), (lb1.FStar_Syntax_Syntax.lbdef), (t22)))))
end)
end
| uu____14497 -> begin
(failwith "impossible: open_term returned different amount of binders")
end)
end))
end)
end)
end
| FStar_Syntax_Syntax.Tm_match (t4, brs) -> begin
(

let rec inspect_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____14552 = (FStar_Reflection_Basic.inspect_const c)
in FStar_Reflection_Data.Pat_Constant (uu____14552))
end
| FStar_Syntax_Syntax.Pat_cons (fv, ps) -> begin
(

let uu____14573 = (

let uu____14580 = (FStar_List.map (fun uu____14593 -> (match (uu____14593) with
| (p1, uu____14602) -> begin
(inspect_pat p1)
end)) ps)
in ((fv), (uu____14580)))
in FStar_Reflection_Data.Pat_Cons (uu____14573))
end
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
FStar_Reflection_Data.Pat_Var (bv)
end
| FStar_Syntax_Syntax.Pat_wild (bv) -> begin
FStar_Reflection_Data.Pat_Wild (bv)
end
| FStar_Syntax_Syntax.Pat_dot_term (bv, t5) -> begin
FStar_Reflection_Data.Pat_Dot_Term (((bv), (t5)))
end))
in (

let brs1 = (FStar_List.map FStar_Syntax_Subst.open_branch brs)
in (

let brs2 = (FStar_List.map (fun uu___367_14698 -> (match (uu___367_14698) with
| (pat, uu____14720, t5) -> begin
(

let uu____14738 = (inspect_pat pat)
in ((uu____14738), (t5)))
end)) brs1)
in (FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (((t4), (brs2))))))))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| uu____14747 -> begin
((

let uu____14749 = (

let uu____14755 = (

let uu____14757 = (FStar_Syntax_Print.tag_of_term t3)
in (

let uu____14759 = (FStar_Syntax_Print.term_to_string t3)
in (FStar_Util.format2 "inspect: outside of expected syntax (%s, %s)\n" uu____14757 uu____14759)))
in ((FStar_Errors.Warning_CantInspect), (uu____14755)))
in (FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____14749));
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown);
)
end))))
in (wrap_err "inspect" uu____13926)))


let pack : FStar_Reflection_Data.term_view  ->  FStar_Syntax_Syntax.term tac = (fun tv -> (match (tv) with
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____14777 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_left ret uu____14777))
end
| FStar_Reflection_Data.Tv_BVar (bv) -> begin
(

let uu____14781 = (FStar_Syntax_Syntax.bv_to_tm bv)
in (FStar_All.pipe_left ret uu____14781))
end
| FStar_Reflection_Data.Tv_FVar (fv) -> begin
(

let uu____14785 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (FStar_All.pipe_left ret uu____14785))
end
| FStar_Reflection_Data.Tv_App (l, (r, q)) -> begin
(

let q' = (FStar_Reflection_Basic.pack_aqual q)
in (

let uu____14792 = (FStar_Syntax_Util.mk_app l ((((r), (q')))::[]))
in (FStar_All.pipe_left ret uu____14792)))
end
| FStar_Reflection_Data.Tv_Abs (b, t) -> begin
(

let uu____14817 = (FStar_Syntax_Util.abs ((b)::[]) t FStar_Pervasives_Native.None)
in (FStar_All.pipe_left ret uu____14817))
end
| FStar_Reflection_Data.Tv_Arrow (b, c) -> begin
(

let uu____14834 = (FStar_Syntax_Util.arrow ((b)::[]) c)
in (FStar_All.pipe_left ret uu____14834))
end
| FStar_Reflection_Data.Tv_Type (()) -> begin
(FStar_All.pipe_left ret FStar_Syntax_Util.ktype)
end
| FStar_Reflection_Data.Tv_Refine (bv, t) -> begin
(

let uu____14853 = (FStar_Syntax_Util.refine bv t)
in (FStar_All.pipe_left ret uu____14853))
end
| FStar_Reflection_Data.Tv_Const (c) -> begin
(

let uu____14857 = (

let uu____14858 = (

let uu____14865 = (

let uu____14866 = (FStar_Reflection_Basic.pack_const c)
in FStar_Syntax_Syntax.Tm_constant (uu____14866))
in (FStar_Syntax_Syntax.mk uu____14865))
in (uu____14858 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_All.pipe_left ret uu____14857))
end
| FStar_Reflection_Data.Tv_Uvar (_u, ctx_u_s) -> begin
(

let uu____14874 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (ctx_u_s)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____14874))
end
| FStar_Reflection_Data.Tv_Let (false, bv, t1, t2) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 [] FStar_Range.dummyRange)
in (

let uu____14885 = (

let uu____14886 = (

let uu____14893 = (

let uu____14894 = (

let uu____14908 = (

let uu____14911 = (

let uu____14912 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____14912)::[])
in (FStar_Syntax_Subst.close uu____14911 t2))
in ((((false), ((lb)::[]))), (uu____14908)))
in FStar_Syntax_Syntax.Tm_let (uu____14894))
in (FStar_Syntax_Syntax.mk uu____14893))
in (uu____14886 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_All.pipe_left ret uu____14885)))
end
| FStar_Reflection_Data.Tv_Let (true, bv, t1, t2) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 [] FStar_Range.dummyRange)
in (

let uu____14957 = (FStar_Syntax_Subst.close_let_rec ((lb)::[]) t2)
in (match (uu____14957) with
| (lbs, body) -> begin
(

let uu____14972 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____14972))
end)))
end
| FStar_Reflection_Data.Tv_Match (t, brs) -> begin
(

let wrap = (fun v1 -> {FStar_Syntax_Syntax.v = v1; FStar_Syntax_Syntax.p = FStar_Range.dummyRange})
in (

let rec pack_pat = (fun p -> (match (p) with
| FStar_Reflection_Data.Pat_Constant (c) -> begin
(

let uu____15009 = (

let uu____15010 = (FStar_Reflection_Basic.pack_const c)
in FStar_Syntax_Syntax.Pat_constant (uu____15010))
in (FStar_All.pipe_left wrap uu____15009))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____15017 = (

let uu____15018 = (

let uu____15032 = (FStar_List.map (fun p1 -> (

let uu____15050 = (pack_pat p1)
in ((uu____15050), (false)))) ps)
in ((fv), (uu____15032)))
in FStar_Syntax_Syntax.Pat_cons (uu____15018))
in (FStar_All.pipe_left wrap uu____15017))
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

let brs1 = (FStar_List.map (fun uu___368_15099 -> (match (uu___368_15099) with
| (pat, t1) -> begin
(

let uu____15116 = (pack_pat pat)
in ((uu____15116), (FStar_Pervasives_Native.None), (t1)))
end)) brs)
in (

let brs2 = (FStar_List.map FStar_Syntax_Subst.close_branch brs1)
in (

let uu____15164 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((t), (brs2)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____15164))))))
end
| FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) -> begin
(

let uu____15192 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (((FStar_Util.Inl (t)), (tacopt))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____15192))
end
| FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) -> begin
(

let uu____15238 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (((FStar_Util.Inr (c)), (tacopt))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____15238))
end
| FStar_Reflection_Data.Tv_Unknown -> begin
(

let uu____15277 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____15277))
end))


let lget : FStar_Reflection_Data.typ  ->  Prims.string  ->  FStar_Syntax_Syntax.term tac = (fun ty k -> (

let uu____15297 = (bind get (fun ps -> (

let uu____15303 = (FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k)
in (match (uu____15303) with
| FStar_Pervasives_Native.None -> begin
(fail "not found")
end
| FStar_Pervasives_Native.Some (t) -> begin
(unquote ty t)
end))))
in (FStar_All.pipe_left (wrap_err "lget") uu____15297)))


let lset : FStar_Reflection_Data.typ  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun _ty k t -> (

let uu____15337 = (bind get (fun ps -> (

let ps1 = (

let uu___437_15344 = ps
in (

let uu____15345 = (FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k t)
in {FStar_Tactics_Types.main_context = uu___437_15344.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___437_15344.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___437_15344.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___437_15344.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___437_15344.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___437_15344.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___437_15344.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___437_15344.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___437_15344.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___437_15344.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___437_15344.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___437_15344.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu____15345}))
in (set ps1))))
in (FStar_All.pipe_left (wrap_err "lset") uu____15337)))


let goal_of_goal_ty : env  ->  FStar_Reflection_Data.typ  ->  (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t) = (fun env typ -> (

let uu____15372 = (FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty" typ.FStar_Syntax_Syntax.pos env typ)
in (match (uu____15372) with
| (u, ctx_uvars, g_u) -> begin
(

let uu____15405 = (FStar_List.hd ctx_uvars)
in (match (uu____15405) with
| (ctx_uvar, uu____15419) -> begin
(

let g = (

let uu____15421 = (FStar_Options.peek ())
in (FStar_Tactics_Types.mk_goal env ctx_uvar uu____15421 false ""))
in ((g), (g_u)))
end))
end)))


let proofstate_of_goal_ty : FStar_Range.range  ->  env  ->  FStar_Reflection_Data.typ  ->  (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term) = (fun rng env typ -> (

let uu____15444 = (goal_of_goal_ty env typ)
in (match (uu____15444) with
| (g, g_u) -> begin
(

let ps = (

let uu____15456 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("TacVerbose")))
in (

let uu____15459 = (FStar_Util.psmap_empty ())
in {FStar_Tactics_Types.main_context = env; FStar_Tactics_Types.main_goal = g; FStar_Tactics_Types.all_implicits = g_u.FStar_TypeChecker_Env.implicits; FStar_Tactics_Types.goals = (g)::[]; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = (Prims.parse_int "0"); FStar_Tactics_Types.__dump = (fun ps msg -> (dump_proofstate ps msg)); FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc; FStar_Tactics_Types.entry_range = rng; FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT; FStar_Tactics_Types.freshness = (Prims.parse_int "0"); FStar_Tactics_Types.tac_verb_dbg = uu____15456; FStar_Tactics_Types.local_state = uu____15459}))
in (

let uu____15469 = (FStar_Tactics_Types.goal_witness g)
in ((ps), (uu____15469))))
end)))




