
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

let uu____39 = (

let uu____40 = (FStar_Tactics_Types.goal_env g)
in (

let uu____41 = (FStar_Tactics_Types.goal_type g)
in (bnorm uu____40 uu____41)))
in (FStar_Tactics_Types.goal_with_type g uu____39)))

type 'a tac =
{tac_f : FStar_Tactics_Types.proofstate  ->  'a FStar_Tactics_Result.__result}


let __proj__Mktac__item__tac_f : 'a . 'a tac  ->  FStar_Tactics_Types.proofstate  ->  'a FStar_Tactics_Result.__result = (fun projectee -> (match (projectee) with
| {tac_f = tac_f} -> begin
tac_f
end))


let mk_tac : 'a . (FStar_Tactics_Types.proofstate  ->  'a FStar_Tactics_Result.__result)  ->  'a tac = (fun f -> {tac_f = f})


let run : 'a . 'a tac  ->  FStar_Tactics_Types.proofstate  ->  'a FStar_Tactics_Result.__result = (fun t p -> (t.tac_f p))


let run_safe : 'a . 'a tac  ->  FStar_Tactics_Types.proofstate  ->  'a FStar_Tactics_Result.__result = (fun t p -> (

let uu____151 = (FStar_Options.tactics_failhard ())
in (match (uu____151) with
| true -> begin
(run t p)
end
| uu____154 -> begin
(FStar_All.try_with (fun uu___367_158 -> (match (()) with
| () -> begin
(run t p)
end)) (fun uu___366_164 -> (match (uu___366_164) with
| FStar_Errors.Err (uu____167, msg) -> begin
FStar_Tactics_Result.Failed (((FStar_Tactics_Types.TacticFailure (msg)), (p)))
end
| FStar_Errors.Error (uu____169, msg, uu____171) -> begin
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
| uu____188 -> begin
()
end))


let ret : 'a . 'a  ->  'a tac = (fun x -> (mk_tac (fun p -> FStar_Tactics_Result.Success (((x), (p))))))


let bind : 'a 'b . 'a tac  ->  ('a  ->  'b tac)  ->  'b tac = (fun t1 t2 -> (mk_tac (fun p -> (

let uu____244 = (run t1 p)
in (match (uu____244) with
| FStar_Tactics_Result.Success (a, q) -> begin
(

let uu____251 = (t2 a)
in (run uu____251 q))
end
| FStar_Tactics_Result.Failed (msg, q) -> begin
FStar_Tactics_Result.Failed (((msg), (q)))
end)))))


let get : FStar_Tactics_Types.proofstate tac = (mk_tac (fun p -> FStar_Tactics_Result.Success (((p), (p)))))


let idtac : unit tac = (ret ())


let get_uvar_solved : FStar_Syntax_Syntax.ctx_uvar  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun uv -> (

let uu____271 = (FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____271) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))


let check_goal_solved : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun goal -> (get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar))


let goal_to_string_verbose : FStar_Tactics_Types.goal  ->  Prims.string = (fun g -> (

let uu____289 = (FStar_Syntax_Print.ctx_uvar_to_string g.FStar_Tactics_Types.goal_ctx_uvar)
in (

let uu____290 = (

let uu____291 = (check_goal_solved g)
in (match (uu____291) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____295 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____295))
end))
in (FStar_Util.format2 "%s%s\n" uu____289 uu____290))))


let goal_to_string : Prims.string  ->  (Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  FStar_Tactics_Types.proofstate  ->  FStar_Tactics_Types.goal  ->  Prims.string = (fun kind maybe_num ps g -> (

let w = (

let uu____329 = (FStar_Options.print_implicits ())
in (match (uu____329) with
| true -> begin
(

let uu____330 = (FStar_Tactics_Types.goal_env g)
in (

let uu____331 = (FStar_Tactics_Types.goal_witness g)
in (tts uu____330 uu____331)))
end
| uu____332 -> begin
(

let uu____333 = (get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar)
in (match (uu____333) with
| FStar_Pervasives_Native.None -> begin
"_"
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____337 = (FStar_Tactics_Types.goal_env g)
in (

let uu____338 = (FStar_Tactics_Types.goal_witness g)
in (tts uu____337 uu____338)))
end))
end))
in (

let num = (match (maybe_num) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (i, n1) -> begin
(

let uu____350 = (FStar_Util.string_of_int i)
in (

let uu____351 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 " %s/%s" uu____350 uu____351)))
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
| uu____355 -> begin
(

let uu____356 = (FStar_Syntax_Print.binders_to_string ", " g.FStar_Tactics_Types.goal_ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders)
in (

let uu____357 = (

let uu____358 = (FStar_Tactics_Types.goal_env g)
in (tts uu____358 g.FStar_Tactics_Types.goal_ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ))
in (FStar_Util.format3 "%s |- %s : %s\n" uu____356 w uu____357)))
end)
in (FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal))))))


let tacprint : Prims.string  ->  unit = (fun s -> (FStar_Util.print1 "TAC>> %s\n" s))


let tacprint1 : Prims.string  ->  Prims.string  ->  unit = (fun s x -> (

let uu____374 = (FStar_Util.format1 s x)
in (FStar_Util.print1 "TAC>> %s\n" uu____374)))


let tacprint2 : Prims.string  ->  Prims.string  ->  Prims.string  ->  unit = (fun s x y -> (

let uu____390 = (FStar_Util.format2 s x y)
in (FStar_Util.print1 "TAC>> %s\n" uu____390)))


let tacprint3 : Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  unit = (fun s x y z -> (

let uu____411 = (FStar_Util.format3 s x y z)
in (FStar_Util.print1 "TAC>> %s\n" uu____411)))


let comp_to_typ : FStar_Syntax_Syntax.comp  ->  FStar_Reflection_Data.typ = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____418) -> begin
t
end
| FStar_Syntax_Syntax.GTotal (t, uu____428) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let get_phi : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun g -> (

let uu____447 = (

let uu____448 = (FStar_Tactics_Types.goal_env g)
in (

let uu____449 = (FStar_Tactics_Types.goal_type g)
in (FStar_TypeChecker_Normalize.unfold_whnf uu____448 uu____449)))
in (FStar_Syntax_Util.un_squash uu____447)))


let is_irrelevant : FStar_Tactics_Types.goal  ->  Prims.bool = (fun g -> (

let uu____455 = (get_phi g)
in (FStar_Option.isSome uu____455)))


let print : Prims.string  ->  unit tac = (fun msg -> ((tacprint msg);
(ret ());
))


let debugging : unit  ->  Prims.bool tac = (fun uu____474 -> (bind get (fun ps -> (

let uu____480 = (FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context (FStar_Options.Other ("Tac")))
in (ret uu____480)))))


let ps_to_string : (Prims.string * FStar_Tactics_Types.proofstate)  ->  Prims.string = (fun uu____489 -> (match (uu____489) with
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

let uu____515 = (

let uu____518 = (

let uu____521 = (

let uu____522 = (FStar_Util.string_of_int ps.FStar_Tactics_Types.depth)
in (FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____522 msg))
in (

let uu____523 = (

let uu____526 = (match ((Prims.op_disEquality ps.FStar_Tactics_Types.entry_range FStar_Range.dummyRange)) with
| true -> begin
(

let uu____527 = (FStar_Range.string_of_def_range ps.FStar_Tactics_Types.entry_range)
in (FStar_Util.format1 "Location: %s\n" uu____527))
end
| uu____528 -> begin
""
end)
in (

let uu____529 = (

let uu____532 = (

let uu____533 = (FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context (FStar_Options.Other ("Imp")))
in (match (uu____533) with
| true -> begin
(

let uu____534 = (FStar_Common.string_of_list p_imp ps.FStar_Tactics_Types.all_implicits)
in (FStar_Util.format1 "Imps: %s\n" uu____534))
end
| uu____535 -> begin
""
end))
in (uu____532)::[])
in (uu____526)::uu____529))
in (uu____521)::uu____523))
in (

let uu____536 = (

let uu____539 = (FStar_List.mapi (fun i g -> (goal_to_string "Goal" (FStar_Pervasives_Native.Some (((((Prims.parse_int "1") + i)), (n1)))) ps g)) ps.FStar_Tactics_Types.goals)
in (

let uu____550 = (FStar_List.mapi (fun i g -> (goal_to_string "SMT Goal" (FStar_Pervasives_Native.Some ((((((Prims.parse_int "1") + n_active) + i)), (n1)))) ps g)) ps.FStar_Tactics_Types.smt_goals)
in (FStar_List.append uu____539 uu____550)))
in (FStar_List.append uu____518 uu____536)))
in (FStar_String.concat "" uu____515))))))
end))


let goal_to_json : FStar_Tactics_Types.goal  ->  FStar_Util.json = (fun g -> (

let g_binders = (

let uu____571 = (

let uu____572 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Env.all_binders uu____572))
in (

let uu____573 = (

let uu____578 = (

let uu____579 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Env.dsenv uu____579))
in (FStar_Syntax_Print.binders_to_json uu____578))
in (FStar_All.pipe_right uu____571 uu____573)))
in (

let uu____580 = (

let uu____587 = (

let uu____594 = (

let uu____599 = (

let uu____600 = (

let uu____607 = (

let uu____612 = (

let uu____613 = (

let uu____614 = (FStar_Tactics_Types.goal_env g)
in (

let uu____615 = (FStar_Tactics_Types.goal_witness g)
in (tts uu____614 uu____615)))
in FStar_Util.JsonStr (uu____613))
in (("witness"), (uu____612)))
in (

let uu____616 = (

let uu____623 = (

let uu____628 = (

let uu____629 = (

let uu____630 = (FStar_Tactics_Types.goal_env g)
in (

let uu____631 = (FStar_Tactics_Types.goal_type g)
in (tts uu____630 uu____631)))
in FStar_Util.JsonStr (uu____629))
in (("type"), (uu____628)))
in (uu____623)::((("label"), (FStar_Util.JsonStr (g.FStar_Tactics_Types.label))))::[])
in (uu____607)::uu____616))
in FStar_Util.JsonAssoc (uu____600))
in (("goal"), (uu____599)))
in (uu____594)::[])
in ((("hyps"), (g_binders)))::uu____587)
in FStar_Util.JsonAssoc (uu____580))))


let ps_to_json : (Prims.string * FStar_Tactics_Types.proofstate)  ->  FStar_Util.json = (fun uu____668 -> (match (uu____668) with
| (msg, ps) -> begin
(

let uu____675 = (

let uu____682 = (

let uu____689 = (

let uu____696 = (

let uu____703 = (

let uu____708 = (

let uu____709 = (FStar_List.map goal_to_json ps.FStar_Tactics_Types.goals)
in FStar_Util.JsonList (uu____709))
in (("goals"), (uu____708)))
in (

let uu____712 = (

let uu____719 = (

let uu____724 = (

let uu____725 = (FStar_List.map goal_to_json ps.FStar_Tactics_Types.smt_goals)
in FStar_Util.JsonList (uu____725))
in (("smt-goals"), (uu____724)))
in (uu____719)::[])
in (uu____703)::uu____712))
in ((("depth"), (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth))))::uu____696)
in ((("label"), (FStar_Util.JsonStr (msg))))::uu____689)
in (

let uu____748 = (match ((Prims.op_disEquality ps.FStar_Tactics_Types.entry_range FStar_Range.dummyRange)) with
| true -> begin
(

let uu____761 = (

let uu____766 = (FStar_Range.json_of_def_range ps.FStar_Tactics_Types.entry_range)
in (("location"), (uu____766)))
in (uu____761)::[])
end
| uu____775 -> begin
[]
end)
in (FStar_List.append uu____682 uu____748)))
in FStar_Util.JsonAssoc (uu____675))
end))


let dump_proofstate : FStar_Tactics_Types.proofstate  ->  Prims.string  ->  unit = (fun ps msg -> (FStar_Options.with_saved_options (fun uu____796 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(FStar_Util.print_generic "proof-state" ps_to_string ps_to_json ((msg), (ps)));
))))


let print_proof_state : Prims.string  ->  unit tac = (fun msg -> (mk_tac (fun ps -> (

let psc = ps.FStar_Tactics_Types.psc
in (

let subst1 = (FStar_TypeChecker_Cfg.psc_subst psc)
in ((

let uu____819 = (FStar_Tactics_Types.subst_proof_state subst1 ps)
in (dump_proofstate uu____819 msg));
FStar_Tactics_Result.Success (((()), (ps)));
))))))


let mlog : 'a . (unit  ->  unit)  ->  (unit  ->  'a tac)  ->  'a tac = (fun f cont -> (bind get (fun ps -> ((log ps f);
(cont ());
))))


let traise : 'a . Prims.exn  ->  'a tac = (fun e -> (mk_tac (fun ps -> FStar_Tactics_Result.Failed (((e), (ps))))))


let fail : 'a . Prims.string  ->  'a tac = (fun msg -> (mk_tac (fun ps -> ((

let uu____887 = (FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context (FStar_Options.Other ("TacFail")))
in (match (uu____887) with
| true -> begin
(dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg))
end
| uu____888 -> begin
()
end));
FStar_Tactics_Result.Failed (((FStar_Tactics_Types.TacticFailure (msg)), (ps)));
))))


let fail1 : 'Auu____895 . Prims.string  ->  Prims.string  ->  'Auu____895 tac = (fun msg x -> (

let uu____908 = (FStar_Util.format1 msg x)
in (fail uu____908)))


let fail2 : 'Auu____917 . Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____917 tac = (fun msg x y -> (

let uu____935 = (FStar_Util.format2 msg x y)
in (fail uu____935)))


let fail3 : 'Auu____946 . Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____946 tac = (fun msg x y z -> (

let uu____969 = (FStar_Util.format3 msg x y z)
in (fail uu____969)))


let fail4 : 'Auu____982 . Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  Prims.string  ->  'Auu____982 tac = (fun msg x y z w -> (

let uu____1010 = (FStar_Util.format4 msg x y z w)
in (fail uu____1010)))


let catch : 'a . 'a tac  ->  (Prims.exn, 'a) FStar_Util.either tac = (fun t -> (mk_tac (fun ps -> (

let tx = (FStar_Syntax_Unionfind.new_transaction ())
in (

let uu____1043 = (run t ps)
in (match (uu____1043) with
| FStar_Tactics_Result.Success (a, q) -> begin
((FStar_Syntax_Unionfind.commit tx);
FStar_Tactics_Result.Success (((FStar_Util.Inr (a)), (q)));
)
end
| FStar_Tactics_Result.Failed (m, q) -> begin
((FStar_Syntax_Unionfind.rollback tx);
(

let ps1 = (

let uu___368_1067 = ps
in {FStar_Tactics_Types.main_context = uu___368_1067.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___368_1067.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___368_1067.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___368_1067.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___368_1067.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___368_1067.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___368_1067.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___368_1067.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___368_1067.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___368_1067.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = q.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___368_1067.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___368_1067.FStar_Tactics_Types.local_state})
in FStar_Tactics_Result.Success (((FStar_Util.Inl (m)), (ps1))));
)
end))))))


let recover : 'a . 'a tac  ->  (Prims.exn, 'a) FStar_Util.either tac = (fun t -> (mk_tac (fun ps -> (

let uu____1105 = (run t ps)
in (match (uu____1105) with
| FStar_Tactics_Result.Success (a, q) -> begin
FStar_Tactics_Result.Success (((FStar_Util.Inr (a)), (q)))
end
| FStar_Tactics_Result.Failed (m, q) -> begin
FStar_Tactics_Result.Success (((FStar_Util.Inl (m)), (q)))
end)))))


let trytac : 'a . 'a tac  ->  'a FStar_Pervasives_Native.option tac = (fun t -> (

let uu____1152 = (catch t)
in (bind uu____1152 (fun r -> (match (r) with
| FStar_Util.Inr (v1) -> begin
(ret (FStar_Pervasives_Native.Some (v1)))
end
| FStar_Util.Inl (uu____1179) -> begin
(ret FStar_Pervasives_Native.None)
end)))))


let trytac_exn : 'a . 'a tac  ->  'a FStar_Pervasives_Native.option tac = (fun t -> (mk_tac (fun ps -> (FStar_All.try_with (fun uu___370_1210 -> (match (()) with
| () -> begin
(

let uu____1215 = (trytac t)
in (run uu____1215 ps))
end)) (fun uu___369_1226 -> (match (uu___369_1226) with
| FStar_Errors.Err (uu____1231, msg) -> begin
((log ps (fun uu____1235 -> (FStar_Util.print1 "trytac_exn error: (%s)" msg)));
FStar_Tactics_Result.Success (((FStar_Pervasives_Native.None), (ps)));
)
end
| FStar_Errors.Error (uu____1240, msg, uu____1242) -> begin
((log ps (fun uu____1245 -> (FStar_Util.print1 "trytac_exn error: (%s)" msg)));
FStar_Tactics_Result.Success (((FStar_Pervasives_Native.None), (ps)));
)
end))))))


let wrap_err : 'a . Prims.string  ->  'a tac  ->  'a tac = (fun pref t -> (mk_tac (fun ps -> (

let uu____1278 = (run t ps)
in (match (uu____1278) with
| FStar_Tactics_Result.Success (a, q) -> begin
FStar_Tactics_Result.Success (((a), (q)))
end
| FStar_Tactics_Result.Failed (FStar_Tactics_Types.TacticFailure (msg), q) -> begin
FStar_Tactics_Result.Failed (((FStar_Tactics_Types.TacticFailure ((Prims.strcat pref (Prims.strcat ": " msg)))), (q)))
end
| FStar_Tactics_Result.Failed (e, q) -> begin
FStar_Tactics_Result.Failed (((e), (q)))
end)))))


let set : FStar_Tactics_Types.proofstate  ->  unit tac = (fun p -> (mk_tac (fun uu____1299 -> FStar_Tactics_Result.Success (((()), (p))))))


let add_implicits : implicits  ->  unit tac = (fun i -> (bind get (fun p -> (set (

let uu___371_1313 = p
in {FStar_Tactics_Types.main_context = uu___371_1313.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___371_1313.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = (FStar_List.append i p.FStar_Tactics_Types.all_implicits); FStar_Tactics_Types.goals = uu___371_1313.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___371_1313.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___371_1313.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___371_1313.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___371_1313.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___371_1313.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___371_1313.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___371_1313.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___371_1313.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___371_1313.FStar_Tactics_Types.local_state})))))


let __do_unify : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun env t1 t2 -> ((

let uu____1334 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1334) with
| true -> begin
(

let uu____1335 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1336 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1335 uu____1336)))
end
| uu____1337 -> begin
()
end));
(FStar_All.try_with (fun uu___373_1343 -> (match (()) with
| () -> begin
(

let res = (FStar_TypeChecker_Rel.teq_nosmt env t1 t2)
in ((

let uu____1350 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1350) with
| true -> begin
(

let uu____1351 = (FStar_Common.string_of_option (FStar_TypeChecker_Rel.guard_to_string env) res)
in (

let uu____1352 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____1353 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1351 uu____1352 uu____1353))))
end
| uu____1354 -> begin
()
end));
(match (res) with
| FStar_Pervasives_Native.None -> begin
(ret false)
end
| FStar_Pervasives_Native.Some (g) -> begin
(

let uu____1358 = (add_implicits g.FStar_TypeChecker_Env.implicits)
in (bind uu____1358 (fun uu____1362 -> (ret true))))
end);
))
end)) (fun uu___372_1366 -> (match (uu___372_1366) with
| FStar_Errors.Err (uu____1369, msg) -> begin
(mlog (fun uu____1372 -> (FStar_Util.print1 ">> do_unify error, (%s)\n" msg)) (fun uu____1374 -> (ret false)))
end
| FStar_Errors.Error (uu____1375, msg, r) -> begin
(mlog (fun uu____1380 -> (

let uu____1381 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg uu____1381))) (fun uu____1383 -> (ret false)))
end)));
))


let compress_implicits : unit tac = (bind get (fun ps -> (

let imps = ps.FStar_Tactics_Types.all_implicits
in (

let g = (

let uu___374_1394 = FStar_TypeChecker_Env.trivial_guard
in {FStar_TypeChecker_Env.guard_f = uu___374_1394.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___374_1394.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = uu___374_1394.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = imps})
in (

let g1 = (FStar_TypeChecker_Rel.resolve_implicits_tac ps.FStar_Tactics_Types.main_context g)
in (

let ps' = (

let uu___375_1397 = ps
in {FStar_Tactics_Types.main_context = uu___375_1397.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___375_1397.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = g1.FStar_TypeChecker_Env.implicits; FStar_Tactics_Types.goals = uu___375_1397.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___375_1397.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___375_1397.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___375_1397.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___375_1397.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___375_1397.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___375_1397.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___375_1397.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___375_1397.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___375_1397.FStar_Tactics_Types.local_state})
in (set ps')))))))


let do_unify : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun env t1 t2 -> (bind idtac (fun uu____1420 -> ((

let uu____1422 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1422) with
| true -> begin
((FStar_Options.push ());
(

let uu____1424 = (FStar_Options.set_options FStar_Options.Set "--debug_level Rel --debug_level RelCheck")
in ());
)
end
| uu____1425 -> begin
()
end));
(

let uu____1426 = (__do_unify env t1 t2)
in (bind uu____1426 (fun r -> ((

let uu____1433 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("1346")))
in (match (uu____1433) with
| true -> begin
(FStar_Options.pop ())
end
| uu____1434 -> begin
()
end));
(bind compress_implicits (fun uu____1436 -> (ret r)));
))));
))))


let remove_solved_goals : unit tac = (bind get (fun ps -> (

let ps' = (

let uu___376_1443 = ps
in (

let uu____1444 = (FStar_List.filter (fun g -> (

let uu____1450 = (check_goal_solved g)
in (FStar_Option.isNone uu____1450))) ps.FStar_Tactics_Types.goals)
in {FStar_Tactics_Types.main_context = uu___376_1443.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___376_1443.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___376_1443.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu____1444; FStar_Tactics_Types.smt_goals = uu___376_1443.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___376_1443.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___376_1443.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___376_1443.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___376_1443.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___376_1443.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___376_1443.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___376_1443.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___376_1443.FStar_Tactics_Types.local_state}))
in (set ps'))))


let set_solution : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun goal solution -> (

let uu____1467 = (FStar_Syntax_Unionfind.find goal.FStar_Tactics_Types.goal_ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____1467) with
| FStar_Pervasives_Native.Some (uu____1472) -> begin
(

let uu____1473 = (

let uu____1474 = (goal_to_string_verbose goal)
in (FStar_Util.format1 "Goal %s is already solved" uu____1474))
in (fail uu____1473))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Syntax_Unionfind.change goal.FStar_Tactics_Types.goal_ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head solution);
(ret ());
)
end)))


let trysolve : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term  ->  Prims.bool tac = (fun goal solution -> (

let uu____1490 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____1491 = (FStar_Tactics_Types.goal_witness goal)
in (do_unify uu____1490 solution uu____1491))))


let __dismiss : unit tac = (bind get (fun p -> (

let uu____1497 = (

let uu___377_1498 = p
in (

let uu____1499 = (FStar_List.tl p.FStar_Tactics_Types.goals)
in {FStar_Tactics_Types.main_context = uu___377_1498.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___377_1498.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___377_1498.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu____1499; FStar_Tactics_Types.smt_goals = uu___377_1498.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___377_1498.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___377_1498.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___377_1498.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___377_1498.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___377_1498.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___377_1498.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___377_1498.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___377_1498.FStar_Tactics_Types.local_state}))
in (set uu____1497))))


let solve : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun goal solution -> (

let e = (FStar_Tactics_Types.goal_env goal)
in (mlog (fun uu____1520 -> (

let uu____1521 = (

let uu____1522 = (FStar_Tactics_Types.goal_witness goal)
in (FStar_Syntax_Print.term_to_string uu____1522))
in (

let uu____1523 = (FStar_Syntax_Print.term_to_string solution)
in (FStar_Util.print2 "solve %s := %s\n" uu____1521 uu____1523)))) (fun uu____1526 -> (

let uu____1527 = (trysolve goal solution)
in (bind uu____1527 (fun b -> (match (b) with
| true -> begin
(bind __dismiss (fun uu____1535 -> remove_solved_goals))
end
| uu____1536 -> begin
(

let uu____1537 = (

let uu____1538 = (

let uu____1539 = (FStar_Tactics_Types.goal_env goal)
in (tts uu____1539 solution))
in (

let uu____1540 = (

let uu____1541 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____1542 = (FStar_Tactics_Types.goal_witness goal)
in (tts uu____1541 uu____1542)))
in (

let uu____1543 = (

let uu____1544 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____1545 = (FStar_Tactics_Types.goal_type goal)
in (tts uu____1544 uu____1545)))
in (FStar_Util.format3 "%s does not solve %s : %s" uu____1538 uu____1540 uu____1543))))
in (fail uu____1537))
end))))))))


let solve' : FStar_Tactics_Types.goal  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun goal solution -> (

let uu____1560 = (set_solution goal solution)
in (bind uu____1560 (fun uu____1564 -> (bind __dismiss (fun uu____1566 -> remove_solved_goals))))))


let set_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun ps -> (set (

let uu___378_1584 = ps
in {FStar_Tactics_Types.main_context = uu___378_1584.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___378_1584.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___378_1584.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = gs; FStar_Tactics_Types.smt_goals = uu___378_1584.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___378_1584.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___378_1584.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___378_1584.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___378_1584.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___378_1584.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___378_1584.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___378_1584.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___378_1584.FStar_Tactics_Types.local_state})))))


let set_smt_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun ps -> (set (

let uu___379_1602 = ps
in {FStar_Tactics_Types.main_context = uu___379_1602.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___379_1602.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___379_1602.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___379_1602.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = gs; FStar_Tactics_Types.depth = uu___379_1602.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___379_1602.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___379_1602.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___379_1602.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___379_1602.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___379_1602.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___379_1602.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___379_1602.FStar_Tactics_Types.local_state})))))


let dismiss_all : unit tac = (set_goals [])


let nwarn : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let check_valid_goal : FStar_Tactics_Types.goal  ->  unit = (fun g -> (

let uu____1623 = (FStar_Options.defensive ())
in (match (uu____1623) with
| true -> begin
(

let b = true
in (

let env = (FStar_Tactics_Types.goal_env g)
in (

let b1 = (b && (

let uu____1628 = (FStar_Tactics_Types.goal_witness g)
in (FStar_TypeChecker_Env.closed env uu____1628)))
in (

let b2 = (b1 && (

let uu____1631 = (FStar_Tactics_Types.goal_type g)
in (FStar_TypeChecker_Env.closed env uu____1631)))
in (

let rec aux = (fun b3 e -> (

let uu____1643 = (FStar_TypeChecker_Env.pop_bv e)
in (match (uu____1643) with
| FStar_Pervasives_Native.None -> begin
b3
end
| FStar_Pervasives_Native.Some (bv, e1) -> begin
(

let b4 = (b3 && (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort))
in (aux b4 e1))
end)))
in (

let uu____1661 = ((

let uu____1664 = (aux b2 env)
in (not (uu____1664))) && (

let uu____1666 = (FStar_ST.op_Bang nwarn)
in (uu____1666 < (Prims.parse_int "5"))))
in (match (uu____1661) with
| true -> begin
((

let uu____1687 = (

let uu____1688 = (FStar_Tactics_Types.goal_type g)
in uu____1688.FStar_Syntax_Syntax.pos)
in (

let uu____1691 = (

let uu____1696 = (

let uu____1697 = (goal_to_string_verbose g)
in (FStar_Util.format1 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n" uu____1697))
in ((FStar_Errors.Warning_IllFormedGoal), (uu____1696)))
in (FStar_Errors.log_issue uu____1687 uu____1691)));
(

let uu____1698 = (

let uu____1699 = (FStar_ST.op_Bang nwarn)
in (uu____1699 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals nwarn uu____1698));
)
end
| uu____1738 -> begin
()
end)))))))
end
| uu____1739 -> begin
()
end)))


let add_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___380_1759 = p
in {FStar_Tactics_Types.main_context = uu___380_1759.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___380_1759.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___380_1759.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append gs p.FStar_Tactics_Types.goals); FStar_Tactics_Types.smt_goals = uu___380_1759.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___380_1759.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___380_1759.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___380_1759.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___380_1759.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___380_1759.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___380_1759.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___380_1759.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___380_1759.FStar_Tactics_Types.local_state}));
))))


let add_smt_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___381_1779 = p
in {FStar_Tactics_Types.main_context = uu___381_1779.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___381_1779.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___381_1779.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___381_1779.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = (FStar_List.append gs p.FStar_Tactics_Types.smt_goals); FStar_Tactics_Types.depth = uu___381_1779.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___381_1779.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___381_1779.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___381_1779.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___381_1779.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___381_1779.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___381_1779.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___381_1779.FStar_Tactics_Types.local_state}));
))))


let push_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___382_1799 = p
in {FStar_Tactics_Types.main_context = uu___382_1799.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___382_1799.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___382_1799.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append p.FStar_Tactics_Types.goals gs); FStar_Tactics_Types.smt_goals = uu___382_1799.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___382_1799.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___382_1799.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___382_1799.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___382_1799.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___382_1799.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___382_1799.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___382_1799.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___382_1799.FStar_Tactics_Types.local_state}));
))))


let push_smt_goals : FStar_Tactics_Types.goal Prims.list  ->  unit tac = (fun gs -> (bind get (fun p -> ((FStar_List.iter check_valid_goal gs);
(set (

let uu___383_1819 = p
in {FStar_Tactics_Types.main_context = uu___383_1819.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___383_1819.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___383_1819.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___383_1819.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = (FStar_List.append p.FStar_Tactics_Types.smt_goals gs); FStar_Tactics_Types.depth = uu___383_1819.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___383_1819.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___383_1819.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___383_1819.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___383_1819.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___383_1819.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___383_1819.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___383_1819.FStar_Tactics_Types.local_state}));
))))


let replace_cur : FStar_Tactics_Types.goal  ->  unit tac = (fun g -> (bind __dismiss (fun uu____1830 -> (add_goals ((g)::[])))))


let new_uvar : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac = (fun reason env typ -> (

let uu____1858 = (FStar_TypeChecker_Env.new_implicit_var_aux reason typ.FStar_Syntax_Syntax.pos env typ FStar_Syntax_Syntax.Allow_untyped)
in (match (uu____1858) with
| (u, ctx_uvar, g_u) -> begin
(

let uu____1892 = (add_implicits g_u.FStar_TypeChecker_Env.implicits)
in (bind uu____1892 (fun uu____1901 -> (

let uu____1902 = (

let uu____1907 = (

let uu____1908 = (FStar_List.hd ctx_uvar)
in (FStar_Pervasives_Native.fst uu____1908))
in ((u), (uu____1907)))
in (ret uu____1902)))))
end)))


let is_true : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1926 = (FStar_Syntax_Util.un_squash t)
in (match (uu____1926) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____1936 = (

let uu____1937 = (FStar_Syntax_Subst.compress t')
in uu____1937.FStar_Syntax_Syntax.n)
in (match (uu____1936) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid)
end
| uu____1941 -> begin
false
end))
end
| uu____1942 -> begin
false
end)))


let is_false : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____1952 = (FStar_Syntax_Util.un_squash t)
in (match (uu____1952) with
| FStar_Pervasives_Native.Some (t') -> begin
(

let uu____1962 = (

let uu____1963 = (FStar_Syntax_Subst.compress t')
in uu____1963.FStar_Syntax_Syntax.n)
in (match (uu____1962) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid)
end
| uu____1967 -> begin
false
end))
end
| uu____1968 -> begin
false
end)))


let cur_goal : unit  ->  FStar_Tactics_Types.goal tac = (fun uu____1979 -> (bind get (fun p -> (match (p.FStar_Tactics_Types.goals) with
| [] -> begin
(fail "No more goals (1)")
end
| (hd1)::tl1 -> begin
(

let uu____1990 = (FStar_Syntax_Unionfind.find hd1.FStar_Tactics_Types.goal_ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____1990) with
| FStar_Pervasives_Native.None -> begin
(ret hd1)
end
| FStar_Pervasives_Native.Some (t) -> begin
((

let uu____1997 = (goal_to_string_verbose hd1)
in (

let uu____1998 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n" uu____1997 uu____1998)));
(ret hd1);
)
end))
end))))


let tadmit_t : FStar_Syntax_Syntax.term  ->  unit tac = (fun t -> (

let uu____2008 = (bind get (fun ps -> (

let uu____2014 = (cur_goal ())
in (bind uu____2014 (fun g -> ((

let uu____2021 = (

let uu____2022 = (FStar_Tactics_Types.goal_type g)
in uu____2022.FStar_Syntax_Syntax.pos)
in (

let uu____2025 = (

let uu____2030 = (

let uu____2031 = (goal_to_string "" FStar_Pervasives_Native.None ps g)
in (FStar_Util.format1 "Tactics admitted goal <%s>\n\n" uu____2031))
in ((FStar_Errors.Warning_TacAdmit), (uu____2030)))
in (FStar_Errors.log_issue uu____2021 uu____2025)));
(solve' g t);
))))))
in (FStar_All.pipe_left (wrap_err "tadmit_t") uu____2008)))


let fresh : unit  ->  FStar_BigInt.t tac = (fun uu____2046 -> (bind get (fun ps -> (

let n1 = ps.FStar_Tactics_Types.freshness
in (

let ps1 = (

let uu___384_2056 = ps
in {FStar_Tactics_Types.main_context = uu___384_2056.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___384_2056.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___384_2056.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___384_2056.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___384_2056.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___384_2056.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___384_2056.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___384_2056.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___384_2056.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___384_2056.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1")); FStar_Tactics_Types.tac_verb_dbg = uu___384_2056.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___384_2056.FStar_Tactics_Types.local_state})
in (

let uu____2057 = (set ps1)
in (bind uu____2057 (fun uu____2062 -> (

let uu____2063 = (FStar_BigInt.of_int_fs n1)
in (ret uu____2063))))))))))


let mk_irrelevant_goal : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  FStar_Options.optionstate  ->  Prims.string  ->  FStar_Tactics_Types.goal tac = (fun reason env phi opts label1 -> (

let typ = (

let uu____2096 = (env.FStar_TypeChecker_Env.universe_of env phi)
in (FStar_Syntax_Util.mk_squash uu____2096 phi))
in (

let uu____2097 = (new_uvar reason env typ)
in (bind uu____2097 (fun uu____2112 -> (match (uu____2112) with
| (uu____2119, ctx_uvar) -> begin
(

let goal = (FStar_Tactics_Types.mk_goal env ctx_uvar opts false label1)
in (ret goal))
end))))))


let __tc : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ * FStar_TypeChecker_Env.guard_t) tac = (fun e t -> (bind get (fun ps -> (mlog (fun uu____2164 -> (

let uu____2165 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Tac> __tc(%s)\n" uu____2165))) (fun uu____2168 -> (

let e1 = (

let uu___385_2170 = e
in {FStar_TypeChecker_Env.solver = uu___385_2170.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___385_2170.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___385_2170.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___385_2170.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___385_2170.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___385_2170.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___385_2170.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___385_2170.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___385_2170.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___385_2170.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___385_2170.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___385_2170.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___385_2170.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___385_2170.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___385_2170.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___385_2170.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___385_2170.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___385_2170.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___385_2170.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___385_2170.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___385_2170.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___385_2170.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___385_2170.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___385_2170.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___385_2170.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = false; FStar_TypeChecker_Env.tc_term = uu___385_2170.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___385_2170.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___385_2170.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___385_2170.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___385_2170.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___385_2170.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___385_2170.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___385_2170.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___385_2170.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___385_2170.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___385_2170.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___385_2170.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___385_2170.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___385_2170.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___385_2170.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___385_2170.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___385_2170.FStar_TypeChecker_Env.nbe})
in (FStar_All.try_with (fun uu___387_2181 -> (match (()) with
| () -> begin
(

let uu____2190 = (FStar_TypeChecker_TcTerm.type_of_tot_term e1 t)
in (ret uu____2190))
end)) (fun uu___386_2208 -> (match (uu___386_2208) with
| FStar_Errors.Err (uu____2217, msg) -> begin
(

let uu____2219 = (tts e1 t)
in (

let uu____2220 = (

let uu____2221 = (FStar_TypeChecker_Env.all_binders e1)
in (FStar_All.pipe_right uu____2221 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____2219 uu____2220 msg)))
end
| FStar_Errors.Error (uu____2228, msg, uu____2230) -> begin
(

let uu____2231 = (tts e1 t)
in (

let uu____2232 = (

let uu____2233 = (FStar_TypeChecker_Env.all_binders e1)
in (FStar_All.pipe_right uu____2233 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____2231 uu____2232 msg)))
end)))))))))


let __tc_ghost : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ * FStar_TypeChecker_Env.guard_t) tac = (fun e t -> (bind get (fun ps -> (mlog (fun uu____2282 -> (

let uu____2283 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____2283))) (fun uu____2286 -> (

let e1 = (

let uu___388_2288 = e
in {FStar_TypeChecker_Env.solver = uu___388_2288.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___388_2288.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___388_2288.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___388_2288.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___388_2288.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___388_2288.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___388_2288.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___388_2288.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___388_2288.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___388_2288.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___388_2288.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___388_2288.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___388_2288.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___388_2288.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___388_2288.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___388_2288.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___388_2288.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___388_2288.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___388_2288.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___388_2288.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___388_2288.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___388_2288.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___388_2288.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___388_2288.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___388_2288.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = false; FStar_TypeChecker_Env.tc_term = uu___388_2288.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___388_2288.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___388_2288.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___388_2288.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___388_2288.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___388_2288.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___388_2288.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___388_2288.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___388_2288.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___388_2288.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___388_2288.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___388_2288.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___388_2288.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___388_2288.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___388_2288.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___388_2288.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___388_2288.FStar_TypeChecker_Env.nbe})
in (FStar_All.try_with (fun uu___390_2302 -> (match (()) with
| () -> begin
(

let uu____2311 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t)
in (match (uu____2311) with
| (t1, lc, g) -> begin
(ret ((t1), (lc.FStar_Syntax_Syntax.res_typ), (g)))
end))
end)) (fun uu___389_2340 -> (match (uu___389_2340) with
| FStar_Errors.Err (uu____2349, msg) -> begin
(

let uu____2351 = (tts e1 t)
in (

let uu____2352 = (

let uu____2353 = (FStar_TypeChecker_Env.all_binders e1)
in (FStar_All.pipe_right uu____2353 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____2351 uu____2352 msg)))
end
| FStar_Errors.Error (uu____2360, msg, uu____2362) -> begin
(

let uu____2363 = (tts e1 t)
in (

let uu____2364 = (

let uu____2365 = (FStar_TypeChecker_Env.all_binders e1)
in (FStar_All.pipe_right uu____2365 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____2363 uu____2364 msg)))
end)))))))))


let __tc_lax : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ * FStar_TypeChecker_Env.guard_t) tac = (fun e t -> (bind get (fun ps -> (mlog (fun uu____2414 -> (

let uu____2415 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Tac> __tc(%s)\n" uu____2415))) (fun uu____2419 -> (

let e1 = (

let uu___391_2421 = e
in {FStar_TypeChecker_Env.solver = uu___391_2421.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___391_2421.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___391_2421.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___391_2421.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___391_2421.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___391_2421.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___391_2421.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___391_2421.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___391_2421.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___391_2421.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___391_2421.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___391_2421.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___391_2421.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___391_2421.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___391_2421.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___391_2421.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___391_2421.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___391_2421.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___391_2421.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___391_2421.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___391_2421.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___391_2421.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___391_2421.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___391_2421.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___391_2421.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = false; FStar_TypeChecker_Env.tc_term = uu___391_2421.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___391_2421.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___391_2421.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___391_2421.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___391_2421.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___391_2421.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___391_2421.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___391_2421.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___391_2421.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___391_2421.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___391_2421.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___391_2421.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___391_2421.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___391_2421.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___391_2421.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___391_2421.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___391_2421.FStar_TypeChecker_Env.nbe})
in (

let e2 = (

let uu___392_2423 = e1
in {FStar_TypeChecker_Env.solver = uu___392_2423.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___392_2423.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___392_2423.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___392_2423.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___392_2423.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___392_2423.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___392_2423.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___392_2423.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___392_2423.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___392_2423.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___392_2423.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___392_2423.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___392_2423.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___392_2423.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___392_2423.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___392_2423.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___392_2423.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___392_2423.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___392_2423.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___392_2423.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___392_2423.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___392_2423.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___392_2423.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___392_2423.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___392_2423.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___392_2423.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___392_2423.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___392_2423.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___392_2423.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___392_2423.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___392_2423.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___392_2423.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___392_2423.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___392_2423.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___392_2423.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___392_2423.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___392_2423.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___392_2423.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___392_2423.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___392_2423.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___392_2423.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___392_2423.FStar_TypeChecker_Env.nbe})
in (FStar_All.try_with (fun uu___394_2437 -> (match (()) with
| () -> begin
(

let uu____2446 = (FStar_TypeChecker_TcTerm.tc_term e2 t)
in (match (uu____2446) with
| (t1, lc, g) -> begin
(ret ((t1), (lc.FStar_Syntax_Syntax.res_typ), (g)))
end))
end)) (fun uu___393_2475 -> (match (uu___393_2475) with
| FStar_Errors.Err (uu____2484, msg) -> begin
(

let uu____2486 = (tts e2 t)
in (

let uu____2487 = (

let uu____2488 = (FStar_TypeChecker_Env.all_binders e2)
in (FStar_All.pipe_right uu____2488 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____2486 uu____2487 msg)))
end
| FStar_Errors.Error (uu____2495, msg, uu____2497) -> begin
(

let uu____2498 = (tts e2 t)
in (

let uu____2499 = (

let uu____2500 = (FStar_TypeChecker_Env.all_binders e2)
in (FStar_All.pipe_right uu____2500 (FStar_Syntax_Print.binders_to_string ", ")))
in (fail3 "Cannot type %s in context (%s). Error = (%s)" uu____2498 uu____2499 msg)))
end))))))))))


let istrivial : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e t -> (

let steps = (FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.Simplify)::(FStar_TypeChecker_Env.UnfoldTac)::(FStar_TypeChecker_Env.Unmeta)::[]
in (

let t1 = (normalize steps e t)
in (is_true t1))))


let get_guard_policy : unit  ->  FStar_Tactics_Types.guard_policy tac = (fun uu____2527 -> (bind get (fun ps -> (ret ps.FStar_Tactics_Types.guard_policy))))


let set_guard_policy : FStar_Tactics_Types.guard_policy  ->  unit tac = (fun pol -> (bind get (fun ps -> (set (

let uu___395_2545 = ps
in {FStar_Tactics_Types.main_context = uu___395_2545.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___395_2545.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___395_2545.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___395_2545.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___395_2545.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___395_2545.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___395_2545.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___395_2545.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___395_2545.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = pol; FStar_Tactics_Types.freshness = uu___395_2545.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___395_2545.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___395_2545.FStar_Tactics_Types.local_state})))))


let with_policy : 'a . FStar_Tactics_Types.guard_policy  ->  'a tac  ->  'a tac = (fun pol t -> (

let uu____2569 = (get_guard_policy ())
in (bind uu____2569 (fun old_pol -> (

let uu____2575 = (set_guard_policy pol)
in (bind uu____2575 (fun uu____2579 -> (bind t (fun r -> (

let uu____2583 = (set_guard_policy old_pol)
in (bind uu____2583 (fun uu____2587 -> (ret r)))))))))))))


let getopts : FStar_Options.optionstate tac = (

let uu____2590 = (

let uu____2595 = (cur_goal ())
in (trytac uu____2595))
in (bind uu____2590 (fun uu___358_2602 -> (match (uu___358_2602) with
| FStar_Pervasives_Native.Some (g) -> begin
(ret g.FStar_Tactics_Types.opts)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2608 = (FStar_Options.peek ())
in (ret uu____2608))
end))))


let proc_guard : Prims.string  ->  env  ->  FStar_TypeChecker_Env.guard_t  ->  unit tac = (fun reason e g -> (mlog (fun uu____2630 -> (

let uu____2631 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____2631))) (fun uu____2634 -> (

let uu____2635 = (add_implicits g.FStar_TypeChecker_Env.implicits)
in (bind uu____2635 (fun uu____2639 -> (bind getopts (fun opts -> (

let uu____2643 = (

let uu____2644 = (FStar_TypeChecker_Rel.simplify_guard e g)
in uu____2644.FStar_TypeChecker_Env.guard_f)
in (match (uu____2643) with
| FStar_TypeChecker_Common.Trivial -> begin
(ret ())
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____2648 = (istrivial e f)
in (match (uu____2648) with
| true -> begin
(ret ())
end
| uu____2651 -> begin
(bind get (fun ps -> (match (ps.FStar_Tactics_Types.guard_policy) with
| FStar_Tactics_Types.Drop -> begin
((

let uu____2658 = (

let uu____2663 = (

let uu____2664 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.format1 "Tactics admitted guard <%s>\n\n" uu____2664))
in ((FStar_Errors.Warning_TacAdmit), (uu____2663)))
in (FStar_Errors.log_issue e.FStar_TypeChecker_Env.range uu____2658));
(ret ());
)
end
| FStar_Tactics_Types.Goal -> begin
(mlog (fun uu____2667 -> (

let uu____2668 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print2 "Making guard (%s:%s) into a goal\n" reason uu____2668))) (fun uu____2671 -> (

let uu____2672 = (mk_irrelevant_goal reason e f opts "")
in (bind uu____2672 (fun goal -> (

let goal1 = (

let uu___396_2679 = goal
in {FStar_Tactics_Types.goal_main_env = uu___396_2679.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = uu___396_2679.FStar_Tactics_Types.goal_ctx_uvar; FStar_Tactics_Types.opts = uu___396_2679.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = true; FStar_Tactics_Types.label = uu___396_2679.FStar_Tactics_Types.label})
in (push_goals ((goal1)::[]))))))))
end
| FStar_Tactics_Types.SMT -> begin
(mlog (fun uu____2682 -> (

let uu____2683 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print2 "Sending guard (%s:%s) to SMT goal\n" reason uu____2683))) (fun uu____2686 -> (

let uu____2687 = (mk_irrelevant_goal reason e f opts "")
in (bind uu____2687 (fun goal -> (

let goal1 = (

let uu___397_2694 = goal
in {FStar_Tactics_Types.goal_main_env = uu___397_2694.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = uu___397_2694.FStar_Tactics_Types.goal_ctx_uvar; FStar_Tactics_Types.opts = uu___397_2694.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = true; FStar_Tactics_Types.label = uu___397_2694.FStar_Tactics_Types.label})
in (push_smt_goals ((goal1)::[]))))))))
end
| FStar_Tactics_Types.Force -> begin
(mlog (fun uu____2697 -> (

let uu____2698 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print2 "Forcing guard (%s:%s)\n" reason uu____2698))) (fun uu____2700 -> (FStar_All.try_with (fun uu___399_2705 -> (match (()) with
| () -> begin
(

let uu____2708 = (

let uu____2709 = (

let uu____2710 = (FStar_TypeChecker_Rel.discharge_guard_no_smt e g)
in (FStar_All.pipe_left FStar_TypeChecker_Env.is_trivial uu____2710))
in (not (uu____2709)))
in (match (uu____2708) with
| true -> begin
(mlog (fun uu____2715 -> (

let uu____2716 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print1 "guard = %s\n" uu____2716))) (fun uu____2718 -> (fail1 "Forcing the guard failed (%s)" reason)))
end
| uu____2719 -> begin
(ret ())
end))
end)) (fun uu___398_2721 -> (mlog (fun uu____2726 -> (

let uu____2727 = (FStar_TypeChecker_Rel.guard_to_string e g)
in (FStar_Util.print1 "guard = %s\n" uu____2727))) (fun uu____2729 -> (fail1 "Forcing the guard failed (%s)" reason)))))))
end)))
end))
end))))))))))


let tc : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.typ tac = (fun t -> (

let uu____2739 = (

let uu____2742 = (cur_goal ())
in (bind uu____2742 (fun goal -> (

let uu____2748 = (

let uu____2757 = (FStar_Tactics_Types.goal_env goal)
in (__tc_lax uu____2757 t))
in (bind uu____2748 (fun uu____2768 -> (match (uu____2768) with
| (uu____2777, typ, uu____2779) -> begin
(ret typ)
end)))))))
in (FStar_All.pipe_left (wrap_err "tc") uu____2739)))


let add_irrelevant_goal : Prims.string  ->  env  ->  FStar_Reflection_Data.typ  ->  FStar_Options.optionstate  ->  Prims.string  ->  unit tac = (fun reason env phi opts label1 -> (

let uu____2813 = (mk_irrelevant_goal reason env phi opts label1)
in (bind uu____2813 (fun goal -> (add_goals ((goal)::[]))))))


let trivial : unit  ->  unit tac = (fun uu____2824 -> (

let uu____2827 = (cur_goal ())
in (bind uu____2827 (fun goal -> (

let uu____2833 = (

let uu____2834 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____2835 = (FStar_Tactics_Types.goal_type goal)
in (istrivial uu____2834 uu____2835)))
in (match (uu____2833) with
| true -> begin
(solve' goal FStar_Syntax_Util.exp_unit)
end
| uu____2838 -> begin
(

let uu____2839 = (

let uu____2840 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____2841 = (FStar_Tactics_Types.goal_type goal)
in (tts uu____2840 uu____2841)))
in (fail1 "Not a trivial goal: %s" uu____2839))
end))))))


let divide : 'a 'b . FStar_BigInt.t  ->  'a tac  ->  'b tac  ->  ('a * 'b) tac = (fun n1 l r -> (bind get (fun p -> (

let uu____2890 = (FStar_All.try_with (fun uu___404_2913 -> (match (()) with
| () -> begin
(

let uu____2924 = (

let uu____2933 = (FStar_BigInt.to_int_fs n1)
in (FStar_List.splitAt uu____2933 p.FStar_Tactics_Types.goals))
in (ret uu____2924))
end)) (fun uu___403_2943 -> (fail "divide: not enough goals")))
in (bind uu____2890 (fun uu____2979 -> (match (uu____2979) with
| (lgs, rgs) -> begin
(

let lp = (

let uu___400_3005 = p
in {FStar_Tactics_Types.main_context = uu___400_3005.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___400_3005.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___400_3005.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = lgs; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = uu___400_3005.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___400_3005.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___400_3005.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___400_3005.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___400_3005.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___400_3005.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___400_3005.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___400_3005.FStar_Tactics_Types.local_state})
in (

let uu____3006 = (set lp)
in (bind uu____3006 (fun uu____3014 -> (bind l (fun a -> (bind get (fun lp' -> (

let rp = (

let uu___401_3030 = lp'
in {FStar_Tactics_Types.main_context = uu___401_3030.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___401_3030.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___401_3030.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = rgs; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = uu___401_3030.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___401_3030.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___401_3030.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___401_3030.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___401_3030.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___401_3030.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___401_3030.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___401_3030.FStar_Tactics_Types.local_state})
in (

let uu____3031 = (set rp)
in (bind uu____3031 (fun uu____3039 -> (bind r (fun b -> (bind get (fun rp' -> (

let p' = (

let uu___402_3055 = rp'
in {FStar_Tactics_Types.main_context = uu___402_3055.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___402_3055.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___402_3055.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = (FStar_List.append lp'.FStar_Tactics_Types.goals rp'.FStar_Tactics_Types.goals); FStar_Tactics_Types.smt_goals = (FStar_List.append lp'.FStar_Tactics_Types.smt_goals (FStar_List.append rp'.FStar_Tactics_Types.smt_goals p.FStar_Tactics_Types.smt_goals)); FStar_Tactics_Types.depth = uu___402_3055.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___402_3055.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___402_3055.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___402_3055.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___402_3055.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___402_3055.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___402_3055.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___402_3055.FStar_Tactics_Types.local_state})
in (

let uu____3056 = (set p')
in (bind uu____3056 (fun uu____3064 -> (bind remove_solved_goals (fun uu____3070 -> (ret ((a), (b)))))))))))))))))))))))))
end)))))))


let focus : 'a . 'a tac  ->  'a tac = (fun f -> (

let uu____3091 = (divide FStar_BigInt.one f idtac)
in (bind uu____3091 (fun uu____3104 -> (match (uu____3104) with
| (a, ()) -> begin
(ret a)
end)))))


let rec map : 'a . 'a tac  ->  'a Prims.list tac = (fun tau -> (bind get (fun p -> (match (p.FStar_Tactics_Types.goals) with
| [] -> begin
(ret [])
end
| (uu____3141)::uu____3142 -> begin
(

let uu____3145 = (

let uu____3154 = (map tau)
in (divide FStar_BigInt.one tau uu____3154))
in (bind uu____3145 (fun uu____3172 -> (match (uu____3172) with
| (h, t) -> begin
(ret ((h)::t))
end))))
end))))


let seq : unit tac  ->  unit tac  ->  unit tac = (fun t1 t2 -> (

let uu____3213 = (bind t1 (fun uu____3218 -> (

let uu____3219 = (map t2)
in (bind uu____3219 (fun uu____3227 -> (ret ()))))))
in (focus uu____3213)))


let intro : unit  ->  FStar_Syntax_Syntax.binder tac = (fun uu____3236 -> (

let uu____3239 = (

let uu____3242 = (cur_goal ())
in (bind uu____3242 (fun goal -> (

let uu____3251 = (

let uu____3258 = (FStar_Tactics_Types.goal_type goal)
in (FStar_Syntax_Util.arrow_one uu____3258))
in (match (uu____3251) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____3267 = (

let uu____3268 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____3268)))
in (match (uu____3267) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____3271 -> begin
(

let env' = (

let uu____3273 = (FStar_Tactics_Types.goal_env goal)
in (FStar_TypeChecker_Env.push_binders uu____3273 ((b)::[])))
in (

let typ' = (comp_to_typ c)
in (

let uu____3287 = (new_uvar "intro" env' typ')
in (bind uu____3287 (fun uu____3303 -> (match (uu____3303) with
| (body, ctx_uvar) -> begin
(

let sol = (FStar_Syntax_Util.abs ((b)::[]) body (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c))))
in (

let uu____3327 = (set_solution goal sol)
in (bind uu____3327 (fun uu____3333 -> (

let g = (FStar_Tactics_Types.mk_goal env' ctx_uvar goal.FStar_Tactics_Types.opts goal.FStar_Tactics_Types.is_guard goal.FStar_Tactics_Types.label)
in (

let uu____3335 = (

let uu____3338 = (bnorm_goal g)
in (replace_cur uu____3338))
in (bind uu____3335 (fun uu____3340 -> (ret b)))))))))
end))))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3345 = (

let uu____3346 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____3347 = (FStar_Tactics_Types.goal_type goal)
in (tts uu____3346 uu____3347)))
in (fail1 "goal is not an arrow (%s)" uu____3345))
end)))))
in (FStar_All.pipe_left (wrap_err "intro") uu____3239)))


let intro_rec : unit  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac = (fun uu____3362 -> (

let uu____3369 = (cur_goal ())
in (bind uu____3369 (fun goal -> ((FStar_Util.print_string "WARNING (intro_rec): calling this is known to cause normalizer loops\n");
(FStar_Util.print_string "WARNING (intro_rec): proceed at your own risk...\n");
(

let uu____3386 = (

let uu____3393 = (FStar_Tactics_Types.goal_type goal)
in (FStar_Syntax_Util.arrow_one uu____3393))
in (match (uu____3386) with
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____3406 = (

let uu____3407 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____3407)))
in (match (uu____3406) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____3418 -> begin
(

let bv = (

let uu____3420 = (FStar_Tactics_Types.goal_type goal)
in (FStar_Syntax_Syntax.gen_bv "__recf" FStar_Pervasives_Native.None uu____3420))
in (

let bs = (

let uu____3430 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____3430)::(b)::[])
in (

let env' = (

let uu____3456 = (FStar_Tactics_Types.goal_env goal)
in (FStar_TypeChecker_Env.push_binders uu____3456 bs))
in (

let uu____3457 = (

let uu____3464 = (comp_to_typ c)
in (new_uvar "intro_rec" env' uu____3464))
in (bind uu____3457 (fun uu____3483 -> (match (uu____3483) with
| (u, ctx_uvar_u) -> begin
(

let lb = (

let uu____3497 = (FStar_Tactics_Types.goal_type goal)
in (

let uu____3500 = (FStar_Syntax_Util.abs ((b)::[]) u FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] uu____3497 FStar_Parser_Const.effect_Tot_lid uu____3500 [] FStar_Range.dummyRange)))
in (

let body = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____3518 = (FStar_Syntax_Subst.close_let_rec ((lb)::[]) body)
in (match (uu____3518) with
| (lbs, body1) -> begin
(

let tm = (

let uu____3540 = (

let uu____3541 = (FStar_Tactics_Types.goal_witness goal)
in uu____3541.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body1)))) FStar_Pervasives_Native.None uu____3540))
in (

let uu____3554 = (set_solution goal tm)
in (bind uu____3554 (fun uu____3563 -> (

let uu____3564 = (

let uu____3567 = (bnorm_goal (

let uu___405_3570 = goal
in {FStar_Tactics_Types.goal_main_env = uu___405_3570.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = ctx_uvar_u; FStar_Tactics_Types.opts = uu___405_3570.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___405_3570.FStar_Tactics_Types.is_guard; FStar_Tactics_Types.label = uu___405_3570.FStar_Tactics_Types.label}))
in (replace_cur uu____3567))
in (bind uu____3564 (fun uu____3577 -> (

let uu____3578 = (

let uu____3583 = (FStar_Syntax_Syntax.mk_binder bv)
in ((uu____3583), (b)))
in (ret uu____3578)))))))))
end))))
end)))))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3592 = (

let uu____3593 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____3594 = (FStar_Tactics_Types.goal_type goal)
in (tts uu____3593 uu____3594)))
in (fail1 "intro_rec: goal is not an arrow (%s)" uu____3592))
end));
)))))


let norm : FStar_Syntax_Embeddings.norm_step Prims.list  ->  unit tac = (fun s -> (

let uu____3612 = (cur_goal ())
in (bind uu____3612 (fun goal -> (mlog (fun uu____3619 -> (

let uu____3620 = (

let uu____3621 = (FStar_Tactics_Types.goal_witness goal)
in (FStar_Syntax_Print.term_to_string uu____3621))
in (FStar_Util.print1 "norm: witness = %s\n" uu____3620))) (fun uu____3626 -> (

let steps = (

let uu____3630 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.UnfoldTac)::[]) uu____3630))
in (

let t = (

let uu____3634 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____3635 = (FStar_Tactics_Types.goal_type goal)
in (normalize steps uu____3634 uu____3635)))
in (

let uu____3636 = (FStar_Tactics_Types.goal_with_type goal t)
in (replace_cur uu____3636))))))))))


let norm_term_env : env  ->  FStar_Syntax_Embeddings.norm_step Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun e s t -> (

let uu____3660 = (bind get (fun ps -> (

let opts = (match (ps.FStar_Tactics_Types.goals) with
| (g)::uu____3668 -> begin
g.FStar_Tactics_Types.opts
end
| uu____3671 -> begin
(FStar_Options.peek ())
end)
in (mlog (fun uu____3676 -> (

let uu____3677 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "norm_term_env: t = %s\n" uu____3677))) (fun uu____3680 -> (

let uu____3681 = (__tc_lax e t)
in (bind uu____3681 (fun uu____3702 -> (match (uu____3702) with
| (t1, uu____3712, uu____3713) -> begin
(

let steps = (

let uu____3717 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.UnfoldTac)::[]) uu____3717))
in (

let t2 = (normalize steps ps.FStar_Tactics_Types.main_context t1)
in (mlog (fun uu____3723 -> (

let uu____3724 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print1 "norm_term_env: t\' = %s\n" uu____3724))) (fun uu____3726 -> (ret t2)))))
end)))))))))
in (FStar_All.pipe_left (wrap_err "norm_term") uu____3660)))


let refine_intro : unit  ->  unit tac = (fun uu____3737 -> (

let uu____3740 = (

let uu____3743 = (cur_goal ())
in (bind uu____3743 (fun g -> (

let uu____3750 = (

let uu____3761 = (FStar_Tactics_Types.goal_env g)
in (

let uu____3762 = (FStar_Tactics_Types.goal_type g)
in (FStar_TypeChecker_Rel.base_and_refinement uu____3761 uu____3762)))
in (match (uu____3750) with
| (uu____3765, FStar_Pervasives_Native.None) -> begin
(fail "not a refinement")
end
| (t, FStar_Pervasives_Native.Some (bv, phi)) -> begin
(

let g1 = (FStar_Tactics_Types.goal_with_type g t)
in (

let uu____3790 = (

let uu____3795 = (

let uu____3800 = (

let uu____3801 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____3801)::[])
in (FStar_Syntax_Subst.open_term uu____3800 phi))
in (match (uu____3795) with
| (bvs, phi1) -> begin
(

let uu____3826 = (

let uu____3827 = (FStar_List.hd bvs)
in (FStar_Pervasives_Native.fst uu____3827))
in ((uu____3826), (phi1)))
end))
in (match (uu____3790) with
| (bv1, phi1) -> begin
(

let uu____3846 = (

let uu____3849 = (FStar_Tactics_Types.goal_env g)
in (

let uu____3850 = (

let uu____3851 = (

let uu____3854 = (

let uu____3855 = (

let uu____3862 = (FStar_Tactics_Types.goal_witness g)
in ((bv1), (uu____3862)))
in FStar_Syntax_Syntax.NT (uu____3855))
in (uu____3854)::[])
in (FStar_Syntax_Subst.subst uu____3851 phi1))
in (mk_irrelevant_goal "refine_intro refinement" uu____3849 uu____3850 g.FStar_Tactics_Types.opts g.FStar_Tactics_Types.label)))
in (bind uu____3846 (fun g2 -> (bind __dismiss (fun uu____3870 -> (add_goals ((g1)::(g2)::[])))))))
end)))
end)))))
in (FStar_All.pipe_left (wrap_err "refine_intro") uu____3740)))


let __exact_now : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun set_expected_typ1 t -> (

let uu____3889 = (cur_goal ())
in (bind uu____3889 (fun goal -> (

let env = (match (set_expected_typ1) with
| true -> begin
(

let uu____3897 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____3898 = (FStar_Tactics_Types.goal_type goal)
in (FStar_TypeChecker_Env.set_expected_typ uu____3897 uu____3898)))
end
| uu____3899 -> begin
(FStar_Tactics_Types.goal_env goal)
end)
in (

let uu____3900 = (__tc env t)
in (bind uu____3900 (fun uu____3919 -> (match (uu____3919) with
| (t1, typ, guard) -> begin
(mlog (fun uu____3934 -> (

let uu____3935 = (FStar_Syntax_Print.term_to_string typ)
in (

let uu____3936 = (

let uu____3937 = (FStar_Tactics_Types.goal_env goal)
in (FStar_TypeChecker_Rel.guard_to_string uu____3937 guard))
in (FStar_Util.print2 "__exact_now: got type %s\n__exact_now: and guard %s\n" uu____3935 uu____3936)))) (fun uu____3940 -> (

let uu____3941 = (

let uu____3944 = (FStar_Tactics_Types.goal_env goal)
in (proc_guard "__exact typing" uu____3944 guard))
in (bind uu____3941 (fun uu____3946 -> (mlog (fun uu____3950 -> (

let uu____3951 = (FStar_Syntax_Print.term_to_string typ)
in (

let uu____3952 = (

let uu____3953 = (FStar_Tactics_Types.goal_type goal)
in (FStar_Syntax_Print.term_to_string uu____3953))
in (FStar_Util.print2 "__exact_now: unifying %s and %s\n" uu____3951 uu____3952)))) (fun uu____3956 -> (

let uu____3957 = (

let uu____3960 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____3961 = (FStar_Tactics_Types.goal_type goal)
in (do_unify uu____3960 typ uu____3961)))
in (bind uu____3957 (fun b -> (match (b) with
| true -> begin
(solve goal t1)
end
| uu____3966 -> begin
(

let uu____3967 = (

let uu____3968 = (FStar_Tactics_Types.goal_env goal)
in (tts uu____3968 t1))
in (

let uu____3969 = (

let uu____3970 = (FStar_Tactics_Types.goal_env goal)
in (tts uu____3970 typ))
in (

let uu____3971 = (

let uu____3972 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____3973 = (FStar_Tactics_Types.goal_type goal)
in (tts uu____3972 uu____3973)))
in (

let uu____3974 = (

let uu____3975 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____3976 = (FStar_Tactics_Types.goal_witness goal)
in (tts uu____3975 uu____3976)))
in (fail4 "%s : %s does not exactly solve the goal %s (witness = %s)" uu____3967 uu____3969 uu____3971 uu____3974)))))
end)))))))))))
end)))))))))


let t_exact : Prims.bool  ->  Prims.bool  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun try_refine set_expected_typ1 tm -> (

let uu____3996 = (mlog (fun uu____4001 -> (

let uu____4002 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "t_exact: tm = %s\n" uu____4002))) (fun uu____4005 -> (

let uu____4006 = (

let uu____4013 = (__exact_now set_expected_typ1 tm)
in (catch uu____4013))
in (bind uu____4006 (fun uu___360_4022 -> (match (uu___360_4022) with
| FStar_Util.Inr (r) -> begin
(ret ())
end
| FStar_Util.Inl (e) when (not (try_refine)) -> begin
(traise e)
end
| FStar_Util.Inl (e) -> begin
(mlog (fun uu____4033 -> (FStar_Util.print_string "__exact_now failed, trying refine...\n")) (fun uu____4036 -> (

let uu____4037 = (

let uu____4044 = (

let uu____4047 = (norm ((FStar_Syntax_Embeddings.Delta)::[]))
in (bind uu____4047 (fun uu____4052 -> (

let uu____4053 = (refine_intro ())
in (bind uu____4053 (fun uu____4057 -> (__exact_now set_expected_typ1 tm)))))))
in (catch uu____4044))
in (bind uu____4037 (fun uu___359_4064 -> (match (uu___359_4064) with
| FStar_Util.Inr (r) -> begin
(mlog (fun uu____4073 -> (FStar_Util.print_string "__exact_now: failed after refining too\n")) (fun uu____4075 -> (ret ())))
end
| FStar_Util.Inl (uu____4076) -> begin
(mlog (fun uu____4078 -> (FStar_Util.print_string "__exact_now: was not a refinement\n")) (fun uu____4080 -> (traise e)))
end))))))
end))))))
in (FStar_All.pipe_left (wrap_err "exact") uu____3996)))


let rec mapM : 'a 'b . ('a  ->  'b tac)  ->  'a Prims.list  ->  'b Prims.list tac = (fun f l -> (match (l) with
| [] -> begin
(ret [])
end
| (x)::xs -> begin
(

let uu____4130 = (f x)
in (bind uu____4130 (fun y -> (

let uu____4138 = (mapM f xs)
in (bind uu____4138 (fun ys -> (ret ((y)::ys))))))))
end))


let rec __try_match_by_application : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Syntax_Syntax.ctx_uvar) Prims.list  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Syntax_Syntax.ctx_uvar) Prims.list tac = (fun acc e ty1 ty2 -> (

let uu____4209 = (do_unify e ty1 ty2)
in (bind uu____4209 (fun uu___361_4221 -> if uu___361_4221 then begin
(ret acc)
end else begin
(

let uu____4240 = (FStar_Syntax_Util.arrow_one ty1)
in (match (uu____4240) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4261 = (FStar_Syntax_Print.term_to_string ty1)
in (

let uu____4262 = (FStar_Syntax_Print.term_to_string ty2)
in (fail2 "Could not instantiate, %s to %s" uu____4261 uu____4262)))
end
| FStar_Pervasives_Native.Some (b, c) -> begin
(

let uu____4277 = (

let uu____4278 = (FStar_Syntax_Util.is_total_comp c)
in (not (uu____4278)))
in (match (uu____4277) with
| true -> begin
(fail "Codomain is effectful")
end
| uu____4297 -> begin
(

let uu____4298 = (new_uvar "apply arg" e (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort)
in (bind uu____4298 (fun uu____4324 -> (match (uu____4324) with
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

let uu____4410 = (mlog (fun uu____4415 -> (

let uu____4416 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "t_apply: tm = %s\n" uu____4416))) (fun uu____4419 -> (

let uu____4420 = (cur_goal ())
in (bind uu____4420 (fun goal -> (

let e = (FStar_Tactics_Types.goal_env goal)
in (

let uu____4428 = (__tc e tm)
in (bind uu____4428 (fun uu____4449 -> (match (uu____4449) with
| (tm1, typ, guard) -> begin
(

let typ1 = (bnorm e typ)
in (

let uu____4462 = (

let uu____4473 = (FStar_Tactics_Types.goal_type goal)
in (try_match_by_application e typ1 uu____4473))
in (bind uu____4462 (fun uvs -> (

let w = (FStar_List.fold_right (fun uu____4516 w -> (match (uu____4516) with
| (uvt, q, uu____4534) -> begin
(FStar_Syntax_Util.mk_app w ((((uvt), (q)))::[]))
end)) uvs tm1)
in (

let uvset = (

let uu____4566 = (FStar_Syntax_Free.new_uv_set ())
in (FStar_List.fold_right (fun uu____4583 s -> (match (uu____4583) with
| (uu____4595, uu____4596, uv) -> begin
(

let uu____4598 = (FStar_Syntax_Free.uvars uv.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.set_union s uu____4598))
end)) uvs uu____4566))
in (

let free_in_some_goal = (fun uv -> (FStar_Util.set_mem uv uvset))
in (

let uu____4607 = (solve' goal w)
in (bind uu____4607 (fun uu____4612 -> (

let uu____4613 = (mapM (fun uu____4630 -> (match (uu____4630) with
| (uvt, q, uv) -> begin
(

let uu____4642 = (FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head)
in (match (uu____4642) with
| FStar_Pervasives_Native.Some (uu____4647) -> begin
(ret ())
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4648 = (uopt && (free_in_some_goal uv))
in (match (uu____4648) with
| true -> begin
(ret ())
end
| uu____4651 -> begin
(

let uu____4652 = (

let uu____4655 = (bnorm_goal (

let uu___406_4658 = goal
in {FStar_Tactics_Types.goal_main_env = uu___406_4658.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = uv; FStar_Tactics_Types.opts = uu___406_4658.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = false; FStar_Tactics_Types.label = uu___406_4658.FStar_Tactics_Types.label}))
in (uu____4655)::[])
in (add_goals uu____4652))
end))
end))
end)) uvs)
in (bind uu____4613 (fun uu____4662 -> (proc_guard "apply guard" e guard))))))))))))))
end))))))))))
in (FStar_All.pipe_left (wrap_err "apply") uu____4410)))


let lemma_or_sq : FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun c -> (

let ct = (FStar_Syntax_Util.comp_to_comp_typ_nouniv c)
in (

let uu____4687 = (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____4687) with
| true -> begin
(

let uu____4694 = (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre)::(post)::uu____4709 -> begin
(((FStar_Pervasives_Native.fst pre)), ((FStar_Pervasives_Native.fst post)))
end
| uu____4762 -> begin
(failwith "apply_lemma: impossible: not a lemma")
end)
in (match (uu____4694) with
| (pre, post) -> begin
(

let post1 = (

let uu____4794 = (

let uu____4805 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit)
in (uu____4805)::[])
in (FStar_Syntax_Util.mk_app post uu____4794))
in FStar_Pervasives_Native.Some (((pre), (post1))))
end))
end
| uu____4834 -> begin
(

let uu____4835 = (FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name)
in (match (uu____4835) with
| true -> begin
(

let uu____4842 = (FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.map_opt uu____4842 (fun post -> ((FStar_Syntax_Util.t_true), (post)))))
end
| uu____4861 -> begin
FStar_Pervasives_Native.None
end))
end))))


let apply_lemma : FStar_Syntax_Syntax.term  ->  unit tac = (fun tm -> (

let uu____4875 = (

let uu____4878 = (bind get (fun ps -> (mlog (fun uu____4885 -> (

let uu____4886 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4886))) (fun uu____4890 -> (

let is_unit_t = (fun t -> (

let uu____4897 = (

let uu____4898 = (FStar_Syntax_Subst.compress t)
in uu____4898.FStar_Syntax_Syntax.n)
in (match (uu____4897) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
true
end
| uu____4902 -> begin
false
end)))
in (

let uu____4903 = (cur_goal ())
in (bind uu____4903 (fun goal -> (

let uu____4909 = (

let uu____4918 = (FStar_Tactics_Types.goal_env goal)
in (__tc uu____4918 tm))
in (bind uu____4909 (fun uu____4933 -> (match (uu____4933) with
| (tm1, t, guard) -> begin
(

let uu____4945 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (uu____4945) with
| (bs, comp) -> begin
(

let uu____4978 = (lemma_or_sq comp)
in (match (uu____4978) with
| FStar_Pervasives_Native.None -> begin
(fail "not a lemma or squashed function")
end
| FStar_Pervasives_Native.Some (pre, post) -> begin
(

let uu____4997 = (FStar_List.fold_left (fun uu____5045 uu____5046 -> (match (((uu____5045), (uu____5046))) with
| ((uvs, guard1, subst1), (b, aq)) -> begin
(

let b_t = (FStar_Syntax_Subst.subst subst1 b.FStar_Syntax_Syntax.sort)
in (

let uu____5159 = (is_unit_t b_t)
in (match (uu____5159) with
| true -> begin
(((((FStar_Syntax_Util.exp_unit), (aq)))::uvs), (guard1), ((FStar_Syntax_Syntax.NT (((b), (FStar_Syntax_Util.exp_unit))))::subst1))
end
| uu____5196 -> begin
(

let uu____5197 = (

let uu____5210 = (

let uu____5211 = (FStar_Tactics_Types.goal_type goal)
in uu____5211.FStar_Syntax_Syntax.pos)
in (

let uu____5214 = (FStar_Tactics_Types.goal_env goal)
in (FStar_TypeChecker_Util.new_implicit_var "apply_lemma" uu____5210 uu____5214 b_t)))
in (match (uu____5197) with
| (u, uu____5232, g_u) -> begin
(

let uu____5246 = (FStar_TypeChecker_Env.conj_guard guard1 g_u)
in (((((u), (aq)))::uvs), (uu____5246), ((FStar_Syntax_Syntax.NT (((b), (u))))::subst1)))
end))
end)))
end)) (([]), (guard), ([])) bs)
in (match (uu____4997) with
| (uvs, implicits, subst1) -> begin
(

let uvs1 = (FStar_List.rev uvs)
in (

let pre1 = (FStar_Syntax_Subst.subst subst1 pre)
in (

let post1 = (FStar_Syntax_Subst.subst subst1 post)
in (

let uu____5325 = (

let uu____5328 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____5329 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero post1)
in (

let uu____5330 = (FStar_Tactics_Types.goal_type goal)
in (do_unify uu____5328 uu____5329 uu____5330))))
in (bind uu____5325 (fun b -> (match ((not (b))) with
| true -> begin
(

let uu____5338 = (

let uu____5339 = (FStar_Tactics_Types.goal_env goal)
in (tts uu____5339 tm1))
in (

let uu____5340 = (

let uu____5341 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____5342 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero post1)
in (tts uu____5341 uu____5342)))
in (

let uu____5343 = (

let uu____5344 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____5345 = (FStar_Tactics_Types.goal_type goal)
in (tts uu____5344 uu____5345)))
in (fail3 "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)" uu____5338 uu____5340 uu____5343))))
end
| uu____5346 -> begin
(

let uu____5347 = (add_implicits implicits.FStar_TypeChecker_Env.implicits)
in (bind uu____5347 (fun uu____5352 -> (

let uu____5353 = (solve' goal FStar_Syntax_Util.exp_unit)
in (bind uu____5353 (fun uu____5361 -> (

let is_free_uvar = (fun uv t1 -> (

let free_uvars = (

let uu____5386 = (

let uu____5389 = (FStar_Syntax_Free.uvars t1)
in (FStar_Util.set_elements uu____5389))
in (FStar_List.map (fun x -> x.FStar_Syntax_Syntax.ctx_uvar_head) uu____5386))
in (FStar_List.existsML (fun u -> (FStar_Syntax_Unionfind.equiv u uv)) free_uvars)))
in (

let appears = (fun uv goals -> (FStar_List.existsML (fun g' -> (

let uu____5424 = (FStar_Tactics_Types.goal_type g')
in (is_free_uvar uv uu____5424))) goals))
in (

let checkone = (fun t1 goals -> (

let uu____5440 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____5440) with
| (hd1, uu____5458) -> begin
(match (hd1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, uu____5484) -> begin
(appears uv.FStar_Syntax_Syntax.ctx_uvar_head goals)
end
| uu____5501 -> begin
false
end)
end)))
in (

let uu____5502 = (FStar_All.pipe_right implicits.FStar_TypeChecker_Env.implicits (mapM (fun imp -> (

let term = imp.FStar_TypeChecker_Env.imp_tm
in (

let ctx_uvar = imp.FStar_TypeChecker_Env.imp_uvar
in (

let uu____5532 = (FStar_Syntax_Util.head_and_args term)
in (match (uu____5532) with
| (hd1, uu____5554) -> begin
(

let uu____5579 = (

let uu____5580 = (FStar_Syntax_Subst.compress hd1)
in uu____5580.FStar_Syntax_Syntax.n)
in (match (uu____5579) with
| FStar_Syntax_Syntax.Tm_uvar (ctx_uvar1, uu____5588) -> begin
(

let goal1 = (bnorm_goal (

let uu___407_5608 = goal
in {FStar_Tactics_Types.goal_main_env = uu___407_5608.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = ctx_uvar1; FStar_Tactics_Types.opts = uu___407_5608.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___407_5608.FStar_Tactics_Types.is_guard; FStar_Tactics_Types.label = uu___407_5608.FStar_Tactics_Types.label}))
in (ret ((goal1)::[])))
end
| uu____5611 -> begin
(mlog (fun uu____5617 -> (

let uu____5618 = (FStar_Syntax_Print.uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____5619 = (FStar_Syntax_Print.term_to_string term)
in (FStar_Util.print2 "apply_lemma: arg %s unified to (%s)\n" uu____5618 uu____5619)))) (fun uu____5624 -> (

let env = (

let uu___408_5626 = (FStar_Tactics_Types.goal_env goal)
in {FStar_TypeChecker_Env.solver = uu___408_5626.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___408_5626.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___408_5626.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_TypeChecker_Env.gamma_sig = uu___408_5626.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___408_5626.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___408_5626.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___408_5626.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___408_5626.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___408_5626.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___408_5626.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___408_5626.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___408_5626.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___408_5626.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___408_5626.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___408_5626.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___408_5626.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___408_5626.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___408_5626.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___408_5626.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___408_5626.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___408_5626.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___408_5626.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___408_5626.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___408_5626.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___408_5626.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___408_5626.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___408_5626.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___408_5626.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___408_5626.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___408_5626.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___408_5626.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___408_5626.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___408_5626.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___408_5626.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___408_5626.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___408_5626.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___408_5626.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___408_5626.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___408_5626.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___408_5626.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___408_5626.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___408_5626.FStar_TypeChecker_Env.nbe})
in (

let g_typ = (FStar_TypeChecker_TcTerm.check_type_of_well_typed_term' true env term ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in (

let uu____5628 = (

let uu____5631 = (match (ps.FStar_Tactics_Types.tac_verb_dbg) with
| true -> begin
(

let uu____5632 = (FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar)
in (

let uu____5633 = (FStar_Syntax_Print.term_to_string term)
in (FStar_Util.format2 "apply_lemma solved arg %s to %s\n" uu____5632 uu____5633)))
end
| uu____5634 -> begin
"apply_lemma solved arg"
end)
in (

let uu____5635 = (FStar_Tactics_Types.goal_env goal)
in (proc_guard uu____5631 uu____5635 g_typ)))
in (bind uu____5628 (fun uu____5639 -> (ret []))))))))
end))
end)))))))
in (bind uu____5502 (fun sub_goals -> (

let sub_goals1 = (FStar_List.flatten sub_goals)
in (

let rec filter' = (fun f xs -> (match (xs) with
| [] -> begin
[]
end
| (x)::xs1 -> begin
(

let uu____5701 = (f x xs1)
in (match (uu____5701) with
| true -> begin
(

let uu____5704 = (filter' f xs1)
in (x)::uu____5704)
end
| uu____5707 -> begin
(filter' f xs1)
end))
end))
in (

let sub_goals2 = (filter' (fun g goals -> (

let uu____5718 = (

let uu____5719 = (FStar_Tactics_Types.goal_witness g)
in (checkone uu____5719 goals))
in (not (uu____5718)))) sub_goals1)
in (

let uu____5720 = (

let uu____5723 = (FStar_Tactics_Types.goal_env goal)
in (proc_guard "apply_lemma guard" uu____5723 guard))
in (bind uu____5720 (fun uu____5726 -> (

let uu____5727 = (

let uu____5730 = (

let uu____5731 = (

let uu____5732 = (FStar_Tactics_Types.goal_env goal)
in (

let uu____5733 = (FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero pre1)
in (istrivial uu____5732 uu____5733)))
in (not (uu____5731)))
in (match (uu____5730) with
| true -> begin
(

let uu____5736 = (FStar_Tactics_Types.goal_env goal)
in (add_irrelevant_goal "apply_lemma precondition" uu____5736 pre1 goal.FStar_Tactics_Types.opts goal.FStar_Tactics_Types.label))
end
| uu____5737 -> begin
(ret ())
end))
in (bind uu____5727 (fun uu____5739 -> (add_goals sub_goals2))))))))))))))))))))))
end)))))))
end))
end))
end))
end))))))))))))
in (focus uu____4878))
in (FStar_All.pipe_left (wrap_err "apply_lemma") uu____4875)))


let destruct_eq' : FStar_Reflection_Data.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun typ -> (

let uu____5761 = (FStar_Syntax_Util.destruct_typ_as_formula typ)
in (match (uu____5761) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (l, (uu____5771)::((e1, uu____5773))::((e2, uu____5775))::[])) when ((FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)) -> begin
FStar_Pervasives_Native.Some (((e1), (e2)))
end
| uu____5836 -> begin
FStar_Pervasives_Native.None
end)))


let destruct_eq : FStar_Reflection_Data.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun typ -> (

let uu____5860 = (destruct_eq' typ)
in (match (uu____5860) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5890 = (FStar_Syntax_Util.un_squash typ)
in (match (uu____5890) with
| FStar_Pervasives_Native.Some (typ1) -> begin
(destruct_eq' typ1)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end)))


let split_env : FStar_Syntax_Syntax.bv  ->  env  ->  (env * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.option = (fun bvar e -> (

let rec aux = (fun e1 -> (

let uu____5958 = (FStar_TypeChecker_Env.pop_bv e1)
in (match (uu____5958) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (bv', e') -> begin
(match ((FStar_Syntax_Syntax.bv_eq bvar bv')) with
| true -> begin
FStar_Pervasives_Native.Some (((e'), (bv'), ([])))
end
| uu____6013 -> begin
(

let uu____6014 = (aux e')
in (FStar_Util.map_opt uu____6014 (fun uu____6045 -> (match (uu____6045) with
| (e'', bv, bvs) -> begin
((e''), (bv), ((bv')::bvs))
end))))
end)
end)))
in (

let uu____6071 = (aux e)
in (FStar_Util.map_opt uu____6071 (fun uu____6102 -> (match (uu____6102) with
| (e', bv, bvs) -> begin
((e'), (bv), ((FStar_List.rev bvs)))
end))))))


let push_bvs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_TypeChecker_Env.env = (fun e bvs -> (FStar_List.fold_left (fun e1 b -> (FStar_TypeChecker_Env.push_bv e1 b)) e bvs))


let subst_goal : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Tactics_Types.goal  ->  FStar_Tactics_Types.goal FStar_Pervasives_Native.option = (fun b1 b2 s g -> (

let uu____6174 = (

let uu____6185 = (FStar_Tactics_Types.goal_env g)
in (split_env b1 uu____6185))
in (FStar_Util.map_opt uu____6174 (fun uu____6203 -> (match (uu____6203) with
| (e0, b11, bvs) -> begin
(

let s1 = (fun bv -> (

let uu___409_6225 = bv
in (

let uu____6226 = (FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___409_6225.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___409_6225.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6226})))
in (

let bvs1 = (FStar_List.map s1 bvs)
in (

let new_env = (push_bvs e0 ((b2)::bvs1))
in (

let new_goal = (

let uu___410_6234 = g.FStar_Tactics_Types.goal_ctx_uvar
in (

let uu____6235 = (FStar_TypeChecker_Env.all_binders new_env)
in (

let uu____6244 = (

let uu____6247 = (FStar_Tactics_Types.goal_type g)
in (FStar_Syntax_Subst.subst s uu____6247))
in {FStar_Syntax_Syntax.ctx_uvar_head = uu___410_6234.FStar_Syntax_Syntax.ctx_uvar_head; FStar_Syntax_Syntax.ctx_uvar_gamma = new_env.FStar_TypeChecker_Env.gamma; FStar_Syntax_Syntax.ctx_uvar_binders = uu____6235; FStar_Syntax_Syntax.ctx_uvar_typ = uu____6244; FStar_Syntax_Syntax.ctx_uvar_reason = uu___410_6234.FStar_Syntax_Syntax.ctx_uvar_reason; FStar_Syntax_Syntax.ctx_uvar_should_check = uu___410_6234.FStar_Syntax_Syntax.ctx_uvar_should_check; FStar_Syntax_Syntax.ctx_uvar_range = uu___410_6234.FStar_Syntax_Syntax.ctx_uvar_range})))
in (

let uu___411_6248 = g
in {FStar_Tactics_Types.goal_main_env = uu___411_6248.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = new_goal; FStar_Tactics_Types.opts = uu___411_6248.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___411_6248.FStar_Tactics_Types.is_guard; FStar_Tactics_Types.label = uu___411_6248.FStar_Tactics_Types.label})))))
end)))))


let rewrite : FStar_Syntax_Syntax.binder  ->  unit tac = (fun h -> (

let uu____6258 = (

let uu____6261 = (cur_goal ())
in (bind uu____6261 (fun goal -> (

let uu____6269 = h
in (match (uu____6269) with
| (bv, uu____6273) -> begin
(mlog (fun uu____6281 -> (

let uu____6282 = (FStar_Syntax_Print.bv_to_string bv)
in (

let uu____6283 = (FStar_Syntax_Print.term_to_string bv.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6282 uu____6283)))) (fun uu____6286 -> (

let uu____6287 = (

let uu____6298 = (FStar_Tactics_Types.goal_env goal)
in (split_env bv uu____6298))
in (match (uu____6287) with
| FStar_Pervasives_Native.None -> begin
(fail "binder not found in environment")
end
| FStar_Pervasives_Native.Some (e0, bv1, bvs) -> begin
(

let uu____6324 = (destruct_eq bv1.FStar_Syntax_Syntax.sort)
in (match (uu____6324) with
| FStar_Pervasives_Native.Some (x, e) -> begin
(

let uu____6339 = (

let uu____6340 = (FStar_Syntax_Subst.compress x)
in uu____6340.FStar_Syntax_Syntax.n)
in (match (uu____6339) with
| FStar_Syntax_Syntax.Tm_name (x1) -> begin
(

let s = (FStar_Syntax_Syntax.NT (((x1), (e))))::[]
in (

let s1 = (fun bv2 -> (

let uu___412_6357 = bv2
in (

let uu____6358 = (FStar_Syntax_Subst.subst s bv2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___412_6357.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___412_6357.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6358})))
in (

let bvs1 = (FStar_List.map s1 bvs)
in (

let new_env = (push_bvs e0 ((bv1)::bvs1))
in (

let new_goal = (

let uu___413_6366 = goal.FStar_Tactics_Types.goal_ctx_uvar
in (

let uu____6367 = (FStar_TypeChecker_Env.all_binders new_env)
in (

let uu____6376 = (

let uu____6379 = (FStar_Tactics_Types.goal_type goal)
in (FStar_Syntax_Subst.subst s uu____6379))
in {FStar_Syntax_Syntax.ctx_uvar_head = uu___413_6366.FStar_Syntax_Syntax.ctx_uvar_head; FStar_Syntax_Syntax.ctx_uvar_gamma = new_env.FStar_TypeChecker_Env.gamma; FStar_Syntax_Syntax.ctx_uvar_binders = uu____6367; FStar_Syntax_Syntax.ctx_uvar_typ = uu____6376; FStar_Syntax_Syntax.ctx_uvar_reason = uu___413_6366.FStar_Syntax_Syntax.ctx_uvar_reason; FStar_Syntax_Syntax.ctx_uvar_should_check = uu___413_6366.FStar_Syntax_Syntax.ctx_uvar_should_check; FStar_Syntax_Syntax.ctx_uvar_range = uu___413_6366.FStar_Syntax_Syntax.ctx_uvar_range})))
in (replace_cur (

let uu___414_6382 = goal
in {FStar_Tactics_Types.goal_main_env = uu___414_6382.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = new_goal; FStar_Tactics_Types.opts = uu___414_6382.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___414_6382.FStar_Tactics_Types.is_guard; FStar_Tactics_Types.label = uu___414_6382.FStar_Tactics_Types.label})))))))
end
| uu____6383 -> begin
(fail "Not an equality hypothesis with a variable on the LHS")
end))
end
| uu____6384 -> begin
(fail "Not an equality hypothesis")
end))
end))))
end)))))
in (FStar_All.pipe_left (wrap_err "rewrite") uu____6258)))


let rename_to : FStar_Syntax_Syntax.binder  ->  Prims.string  ->  unit tac = (fun b s -> (

let uu____6409 = (

let uu____6412 = (cur_goal ())
in (bind uu____6412 (fun goal -> (

let uu____6423 = b
in (match (uu____6423) with
| (bv, uu____6427) -> begin
(

let bv' = (

let uu____6433 = (

let uu___415_6434 = bv
in (

let uu____6435 = (FStar_Ident.mk_ident ((s), (bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
in {FStar_Syntax_Syntax.ppname = uu____6435; FStar_Syntax_Syntax.index = uu___415_6434.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___415_6434.FStar_Syntax_Syntax.sort}))
in (FStar_Syntax_Syntax.freshen_bv uu____6433))
in (

let s1 = (

let uu____6439 = (

let uu____6440 = (

let uu____6447 = (FStar_Syntax_Syntax.bv_to_name bv')
in ((bv), (uu____6447)))
in FStar_Syntax_Syntax.NT (uu____6440))
in (uu____6439)::[])
in (

let uu____6452 = (subst_goal bv bv' s1 goal)
in (match (uu____6452) with
| FStar_Pervasives_Native.None -> begin
(fail "binder not found in environment")
end
| FStar_Pervasives_Native.Some (goal1) -> begin
(replace_cur goal1)
end))))
end)))))
in (FStar_All.pipe_left (wrap_err "rename_to") uu____6409)))


let binder_retype : FStar_Syntax_Syntax.binder  ->  unit tac = (fun b -> (

let uu____6471 = (

let uu____6474 = (cur_goal ())
in (bind uu____6474 (fun goal -> (

let uu____6483 = b
in (match (uu____6483) with
| (bv, uu____6487) -> begin
(

let uu____6492 = (

let uu____6503 = (FStar_Tactics_Types.goal_env goal)
in (split_env bv uu____6503))
in (match (uu____6492) with
| FStar_Pervasives_Native.None -> begin
(fail "binder is not present in environment")
end
| FStar_Pervasives_Native.Some (e0, bv1, bvs) -> begin
(

let uu____6529 = (FStar_Syntax_Util.type_u ())
in (match (uu____6529) with
| (ty, u) -> begin
(

let uu____6538 = (new_uvar "binder_retype" e0 ty)
in (bind uu____6538 (fun uu____6556 -> (match (uu____6556) with
| (t', u_t') -> begin
(

let bv'' = (

let uu___416_6566 = bv1
in {FStar_Syntax_Syntax.ppname = uu___416_6566.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___416_6566.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t'})
in (

let s = (

let uu____6570 = (

let uu____6571 = (

let uu____6578 = (FStar_Syntax_Syntax.bv_to_name bv'')
in ((bv1), (uu____6578)))
in FStar_Syntax_Syntax.NT (uu____6571))
in (uu____6570)::[])
in (

let bvs1 = (FStar_List.map (fun b1 -> (

let uu___417_6590 = b1
in (

let uu____6591 = (FStar_Syntax_Subst.subst s b1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___417_6590.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___417_6590.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6591}))) bvs)
in (

let env' = (push_bvs e0 ((bv'')::bvs1))
in (bind __dismiss (fun uu____6598 -> (

let new_goal = (

let uu____6600 = (FStar_Tactics_Types.goal_with_env goal env')
in (

let uu____6601 = (

let uu____6602 = (FStar_Tactics_Types.goal_type goal)
in (FStar_Syntax_Subst.subst s uu____6602))
in (FStar_Tactics_Types.goal_with_type uu____6600 uu____6601)))
in (

let uu____6603 = (add_goals ((new_goal)::[]))
in (bind uu____6603 (fun uu____6608 -> (

let uu____6609 = (FStar_Syntax_Util.mk_eq2 (FStar_Syntax_Syntax.U_succ (u)) ty bv1.FStar_Syntax_Syntax.sort t')
in (add_irrelevant_goal "binder_retype equation" e0 uu____6609 goal.FStar_Tactics_Types.opts goal.FStar_Tactics_Types.label))))))))))))
end))))
end))
end))
end)))))
in (FStar_All.pipe_left (wrap_err "binder_retype") uu____6471)))


let norm_binder_type : FStar_Syntax_Embeddings.norm_step Prims.list  ->  FStar_Syntax_Syntax.binder  ->  unit tac = (fun s b -> (

let uu____6632 = (

let uu____6635 = (cur_goal ())
in (bind uu____6635 (fun goal -> (

let uu____6644 = b
in (match (uu____6644) with
| (bv, uu____6648) -> begin
(

let uu____6653 = (

let uu____6664 = (FStar_Tactics_Types.goal_env goal)
in (split_env bv uu____6664))
in (match (uu____6653) with
| FStar_Pervasives_Native.None -> begin
(fail "binder is not present in environment")
end
| FStar_Pervasives_Native.Some (e0, bv1, bvs) -> begin
(

let steps = (

let uu____6693 = (FStar_TypeChecker_Normalize.tr_norm_steps s)
in (FStar_List.append ((FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.UnfoldTac)::[]) uu____6693))
in (

let sort' = (normalize steps e0 bv1.FStar_Syntax_Syntax.sort)
in (

let bv' = (

let uu___418_6698 = bv1
in {FStar_Syntax_Syntax.ppname = uu___418_6698.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___418_6698.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort'})
in (

let env' = (push_bvs e0 ((bv')::bvs))
in (

let uu____6700 = (FStar_Tactics_Types.goal_with_env goal env')
in (replace_cur uu____6700))))))
end))
end)))))
in (FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6632)))


let revert : unit  ->  unit tac = (fun uu____6711 -> (

let uu____6714 = (cur_goal ())
in (bind uu____6714 (fun goal -> (

let uu____6720 = (

let uu____6727 = (FStar_Tactics_Types.goal_env goal)
in (FStar_TypeChecker_Env.pop_bv uu____6727))
in (match (uu____6720) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot revert; empty context")
end
| FStar_Pervasives_Native.Some (x, env') -> begin
(

let typ' = (

let uu____6743 = (

let uu____6746 = (FStar_Tactics_Types.goal_type goal)
in (FStar_Syntax_Syntax.mk_Total uu____6746))
in (FStar_Syntax_Util.arrow ((((x), (FStar_Pervasives_Native.None)))::[]) uu____6743))
in (

let uu____6761 = (new_uvar "revert" env' typ')
in (bind uu____6761 (fun uu____6776 -> (match (uu____6776) with
| (r, u_r) -> begin
(

let uu____6785 = (

let uu____6788 = (

let uu____6789 = (

let uu____6790 = (FStar_Tactics_Types.goal_type goal)
in uu____6790.FStar_Syntax_Syntax.pos)
in (

let uu____6793 = (

let uu____6798 = (

let uu____6799 = (

let uu____6808 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____6808))
in (uu____6799)::[])
in (FStar_Syntax_Syntax.mk_Tm_app r uu____6798))
in (uu____6793 FStar_Pervasives_Native.None uu____6789)))
in (set_solution goal uu____6788))
in (bind uu____6785 (fun uu____6829 -> (

let g = (FStar_Tactics_Types.mk_goal env' u_r goal.FStar_Tactics_Types.opts goal.FStar_Tactics_Types.is_guard goal.FStar_Tactics_Types.label)
in (replace_cur g)))))
end)))))
end))))))


let free_in : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun bv t -> (

let uu____6841 = (FStar_Syntax_Free.names t)
in (FStar_Util.set_mem bv uu____6841)))


let rec clear : FStar_Syntax_Syntax.binder  ->  unit tac = (fun b -> (

let bv = (FStar_Pervasives_Native.fst b)
in (

let uu____6856 = (cur_goal ())
in (bind uu____6856 (fun goal -> (mlog (fun uu____6864 -> (

let uu____6865 = (FStar_Syntax_Print.binder_to_string b)
in (

let uu____6866 = (

let uu____6867 = (

let uu____6868 = (

let uu____6877 = (FStar_Tactics_Types.goal_env goal)
in (FStar_TypeChecker_Env.all_binders uu____6877))
in (FStar_All.pipe_right uu____6868 FStar_List.length))
in (FStar_All.pipe_right uu____6867 FStar_Util.string_of_int))
in (FStar_Util.print2 "Clear of (%s), env has %s binders\n" uu____6865 uu____6866)))) (fun uu____6894 -> (

let uu____6895 = (

let uu____6906 = (FStar_Tactics_Types.goal_env goal)
in (split_env bv uu____6906))
in (match (uu____6895) with
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

let uu____6950 = (free_in bv1 bv'.FStar_Syntax_Syntax.sort)
in (match (uu____6950) with
| true -> begin
(

let uu____6953 = (

let uu____6954 = (FStar_Syntax_Print.bv_to_string bv')
in (FStar_Util.format1 "Cannot clear; binder present in the type of %s" uu____6954))
in (fail uu____6953))
end
| uu____6955 -> begin
(check1 bvs2)
end))
end))
in (

let uu____6956 = (

let uu____6957 = (FStar_Tactics_Types.goal_type goal)
in (free_in bv1 uu____6957))
in (match (uu____6956) with
| true -> begin
(fail "Cannot clear; binder present in goal")
end
| uu____6960 -> begin
(

let uu____6961 = (check1 bvs)
in (bind uu____6961 (fun uu____6967 -> (

let env' = (push_bvs e' bvs)
in (

let uu____6969 = (

let uu____6976 = (FStar_Tactics_Types.goal_type goal)
in (new_uvar "clear.witness" env' uu____6976))
in (bind uu____6969 (fun uu____6985 -> (match (uu____6985) with
| (ut, uvar_ut) -> begin
(

let uu____6994 = (set_solution goal ut)
in (bind uu____6994 (fun uu____6999 -> (

let uu____7000 = (FStar_Tactics_Types.mk_goal env' uvar_ut goal.FStar_Tactics_Types.opts goal.FStar_Tactics_Types.is_guard goal.FStar_Tactics_Types.label)
in (replace_cur uu____7000)))))
end))))))))
end)))
end)))))))))


let clear_top : unit  ->  unit tac = (fun uu____7007 -> (

let uu____7010 = (cur_goal ())
in (bind uu____7010 (fun goal -> (

let uu____7016 = (

let uu____7023 = (FStar_Tactics_Types.goal_env goal)
in (FStar_TypeChecker_Env.pop_bv uu____7023))
in (match (uu____7016) with
| FStar_Pervasives_Native.None -> begin
(fail "Cannot clear; empty context")
end
| FStar_Pervasives_Native.Some (x, uu____7031) -> begin
(

let uu____7036 = (FStar_Syntax_Syntax.mk_binder x)
in (clear uu____7036))
end))))))


let prune : Prims.string  ->  unit tac = (fun s -> (

let uu____7046 = (cur_goal ())
in (bind uu____7046 (fun g -> (

let ctx = (FStar_Tactics_Types.goal_env g)
in (

let ctx' = (

let uu____7056 = (FStar_Ident.path_of_text s)
in (FStar_TypeChecker_Env.rem_proof_ns ctx uu____7056))
in (

let g' = (FStar_Tactics_Types.goal_with_env g ctx')
in (bind __dismiss (fun uu____7059 -> (add_goals ((g')::[])))))))))))


let addns : Prims.string  ->  unit tac = (fun s -> (

let uu____7069 = (cur_goal ())
in (bind uu____7069 (fun g -> (

let ctx = (FStar_Tactics_Types.goal_env g)
in (

let ctx' = (

let uu____7079 = (FStar_Ident.path_of_text s)
in (FStar_TypeChecker_Env.add_proof_ns ctx uu____7079))
in (

let g' = (FStar_Tactics_Types.goal_with_env g ctx')
in (bind __dismiss (fun uu____7082 -> (add_goals ((g')::[])))))))))))


let rec tac_fold_env : FStar_Tactics_Types.direction  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac)  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun d f env t -> (

let tn = (

let uu____7122 = (FStar_Syntax_Subst.compress t)
in uu____7122.FStar_Syntax_Syntax.n)
in (

let uu____7125 = (match ((Prims.op_Equality d FStar_Tactics_Types.TopDown)) with
| true -> begin
(f env (

let uu___422_7131 = t
in {FStar_Syntax_Syntax.n = tn; FStar_Syntax_Syntax.pos = uu___422_7131.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___422_7131.FStar_Syntax_Syntax.vars}))
end
| uu____7132 -> begin
(ret t)
end)
in (bind uu____7125 (fun t1 -> (

let ff = (tac_fold_env d f env)
in (

let tn1 = (

let uu____7147 = (

let uu____7148 = (FStar_Syntax_Subst.compress t1)
in uu____7148.FStar_Syntax_Syntax.n)
in (match (uu____7147) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____7179 = (ff hd1)
in (bind uu____7179 (fun hd2 -> (

let fa = (fun uu____7205 -> (match (uu____7205) with
| (a, q) -> begin
(

let uu____7226 = (ff a)
in (bind uu____7226 (fun a1 -> (ret ((a1), (q))))))
end))
in (

let uu____7245 = (mapM fa args)
in (bind uu____7245 (fun args1 -> (ret (FStar_Syntax_Syntax.Tm_app (((hd2), (args1))))))))))))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, k) -> begin
(

let uu____7327 = (FStar_Syntax_Subst.open_term bs t2)
in (match (uu____7327) with
| (bs1, t') -> begin
(

let uu____7336 = (

let uu____7339 = (FStar_TypeChecker_Env.push_binders env bs1)
in (tac_fold_env d f uu____7339 t'))
in (bind uu____7336 (fun t'' -> (

let uu____7343 = (

let uu____7344 = (

let uu____7363 = (FStar_Syntax_Subst.close_binders bs1)
in (

let uu____7372 = (FStar_Syntax_Subst.close bs1 t'')
in ((uu____7363), (uu____7372), (k))))
in FStar_Syntax_Syntax.Tm_abs (uu____7344))
in (ret uu____7343)))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(ret tn)
end
| FStar_Syntax_Syntax.Tm_match (hd1, brs) -> begin
(

let uu____7447 = (ff hd1)
in (bind uu____7447 (fun hd2 -> (

let ffb = (fun br -> (

let uu____7462 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____7462) with
| (pat, w, e) -> begin
(

let bvs = (FStar_Syntax_Syntax.pat_bvs pat)
in (

let ff1 = (

let uu____7494 = (FStar_TypeChecker_Env.push_bvs env bvs)
in (tac_fold_env d f uu____7494))
in (

let uu____7495 = (ff1 e)
in (bind uu____7495 (fun e1 -> (

let br1 = (FStar_Syntax_Subst.close_branch ((pat), (w), (e1)))
in (ret br1)))))))
end)))
in (

let uu____7510 = (mapM ffb brs)
in (bind uu____7510 (fun brs1 -> (ret (FStar_Syntax_Syntax.Tm_match (((hd2), (brs1))))))))))))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (bv); FStar_Syntax_Syntax.lbunivs = uu____7554; FStar_Syntax_Syntax.lbtyp = uu____7555; FStar_Syntax_Syntax.lbeff = uu____7556; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu____7558; FStar_Syntax_Syntax.lbpos = uu____7559})::[]), e) -> begin
(

let lb = (

let uu____7584 = (

let uu____7585 = (FStar_Syntax_Subst.compress t1)
in uu____7585.FStar_Syntax_Syntax.n)
in (match (uu____7584) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), uu____7589) -> begin
lb
end
| uu____7602 -> begin
(failwith "impossible")
end))
in (

let fflb = (fun lb1 -> (

let uu____7611 = (ff lb1.FStar_Syntax_Syntax.lbdef)
in (bind uu____7611 (fun def1 -> (ret (

let uu___419_7617 = lb1
in {FStar_Syntax_Syntax.lbname = uu___419_7617.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___419_7617.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___419_7617.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___419_7617.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def1; FStar_Syntax_Syntax.lbattrs = uu___419_7617.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___419_7617.FStar_Syntax_Syntax.lbpos}))))))
in (

let uu____7618 = (fflb lb)
in (bind uu____7618 (fun lb1 -> (

let uu____7628 = (

let uu____7633 = (

let uu____7634 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____7634)::[])
in (FStar_Syntax_Subst.open_term uu____7633 e))
in (match (uu____7628) with
| (bs, e1) -> begin
(

let ff1 = (

let uu____7664 = (FStar_TypeChecker_Env.push_binders env bs)
in (tac_fold_env d f uu____7664))
in (

let uu____7665 = (ff1 e1)
in (bind uu____7665 (fun e2 -> (

let e3 = (FStar_Syntax_Subst.close bs e2)
in (ret (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (e3))))))))))
end)))))))
end
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e) -> begin
(

let fflb = (fun lb -> (

let uu____7706 = (ff lb.FStar_Syntax_Syntax.lbdef)
in (bind uu____7706 (fun def -> (ret (

let uu___420_7712 = lb
in {FStar_Syntax_Syntax.lbname = uu___420_7712.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___420_7712.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___420_7712.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___420_7712.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu___420_7712.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___420_7712.FStar_Syntax_Syntax.lbpos}))))))
in (

let uu____7713 = (FStar_Syntax_Subst.open_let_rec lbs e)
in (match (uu____7713) with
| (lbs1, e1) -> begin
(

let uu____7728 = (mapM fflb lbs1)
in (bind uu____7728 (fun lbs2 -> (

let uu____7740 = (ff e1)
in (bind uu____7740 (fun e2 -> (

let uu____7748 = (FStar_Syntax_Subst.close_let_rec lbs2 e2)
in (match (uu____7748) with
| (lbs3, e3) -> begin
(ret (FStar_Syntax_Syntax.Tm_let (((((true), (lbs3))), (e3)))))
end))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, asc, eff) -> begin
(

let uu____7816 = (ff t2)
in (bind uu____7816 (fun t3 -> (ret (FStar_Syntax_Syntax.Tm_ascribed (((t3), (asc), (eff))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t2, m) -> begin
(

let uu____7847 = (ff t2)
in (bind uu____7847 (fun t3 -> (ret (FStar_Syntax_Syntax.Tm_meta (((t3), (m))))))))
end
| uu____7854 -> begin
(ret tn)
end))
in (bind tn1 (fun tn2 -> (

let t' = (

let uu___421_7861 = t1
in {FStar_Syntax_Syntax.n = tn2; FStar_Syntax_Syntax.pos = uu___421_7861.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___421_7861.FStar_Syntax_Syntax.vars})
in (match ((Prims.op_Equality d FStar_Tactics_Types.BottomUp)) with
| true -> begin
(f env t')
end
| uu____7864 -> begin
(ret t')
end)))))))))))


let pointwise_rec : FStar_Tactics_Types.proofstate  ->  unit tac  ->  FStar_Options.optionstate  ->  Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun ps tau opts label1 env t -> (

let uu____7903 = (FStar_TypeChecker_TcTerm.tc_term (

let uu___423_7912 = env
in {FStar_TypeChecker_Env.solver = uu___423_7912.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___423_7912.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___423_7912.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___423_7912.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___423_7912.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___423_7912.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___423_7912.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___423_7912.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___423_7912.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___423_7912.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___423_7912.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___423_7912.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___423_7912.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___423_7912.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___423_7912.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___423_7912.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___423_7912.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___423_7912.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___423_7912.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___423_7912.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___423_7912.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___423_7912.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___423_7912.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___423_7912.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___423_7912.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___423_7912.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___423_7912.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___423_7912.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___423_7912.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___423_7912.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___423_7912.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___423_7912.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___423_7912.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___423_7912.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___423_7912.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___423_7912.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___423_7912.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___423_7912.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___423_7912.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___423_7912.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___423_7912.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___423_7912.FStar_TypeChecker_Env.nbe}) t)
in (match (uu____7903) with
| (t1, lcomp, g) -> begin
(

let uu____7918 = ((

let uu____7921 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp)
in (not (uu____7921))) || (

let uu____7923 = (FStar_TypeChecker_Env.is_trivial g)
in (not (uu____7923))))
in (match (uu____7918) with
| true -> begin
(ret t1)
end
| uu____7926 -> begin
(

let rewrite_eq = (

let typ = lcomp.FStar_Syntax_Syntax.res_typ
in (

let uu____7931 = (new_uvar "pointwise_rec" env typ)
in (bind uu____7931 (fun uu____7947 -> (match (uu____7947) with
| (ut, uvar_ut) -> begin
((log ps (fun uu____7960 -> (

let uu____7961 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____7962 = (FStar_Syntax_Print.term_to_string ut)
in (FStar_Util.print2 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n" uu____7961 uu____7962)))));
(

let uu____7963 = (

let uu____7966 = (

let uu____7967 = (FStar_TypeChecker_TcTerm.universe_of env typ)
in (FStar_Syntax_Util.mk_eq2 uu____7967 typ t1 ut))
in (add_irrelevant_goal "pointwise_rec equation" env uu____7966 opts label1))
in (bind uu____7963 (fun uu____7970 -> (

let uu____7971 = (bind tau (fun uu____7977 -> (

let ut1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env ut)
in ((log ps (fun uu____7983 -> (

let uu____7984 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____7985 = (FStar_Syntax_Print.term_to_string ut1)
in (FStar_Util.print2 "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n" uu____7984 uu____7985)))));
(ret ut1);
))))
in (focus uu____7971)))));
)
end)))))
in (

let uu____7986 = (catch rewrite_eq)
in (bind uu____7986 (fun x -> (match (x) with
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
| uu____8096 -> begin
c
end))
in (

let maybe_continue = (fun ctrl1 t1 k -> (match ((Prims.op_Equality ctrl1 globalStop)) with
| true -> begin
(ret ((t1), (globalStop)))
end
| uu____8166 -> begin
(match ((Prims.op_Equality ctrl1 proceedToNextSubtree)) with
| true -> begin
(ret ((t1), (keepGoing)))
end
| uu____8183 -> begin
(k t1)
end)
end))
in (

let uu____8184 = (FStar_Syntax_Subst.compress t)
in (maybe_continue ctrl uu____8184 (fun t1 -> (

let uu____8192 = (f env (

let uu___426_8201 = t1
in {FStar_Syntax_Syntax.n = t1.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = uu___426_8201.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___426_8201.FStar_Syntax_Syntax.vars}))
in (bind uu____8192 (fun uu____8217 -> (match (uu____8217) with
| (t2, ctrl1) -> begin
(maybe_continue ctrl1 t2 (fun t3 -> (

let uu____8240 = (

let uu____8241 = (FStar_Syntax_Subst.compress t3)
in uu____8241.FStar_Syntax_Syntax.n)
in (match (uu____8240) with
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____8278 = (ctrl_tac_fold f env ctrl1 hd1)
in (bind uu____8278 (fun uu____8303 -> (match (uu____8303) with
| (hd2, ctrl2) -> begin
(

let ctrl3 = (keep_going ctrl2)
in (

let uu____8319 = (ctrl_tac_fold_args f env ctrl3 args)
in (bind uu____8319 (fun uu____8346 -> (match (uu____8346) with
| (args1, ctrl4) -> begin
(ret (((

let uu___424_8376 = t3
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app (((hd2), (args1))); FStar_Syntax_Syntax.pos = uu___424_8376.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___424_8376.FStar_Syntax_Syntax.vars})), (ctrl4)))
end)))))
end))))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t4, k) -> begin
(

let uu____8418 = (FStar_Syntax_Subst.open_term bs t4)
in (match (uu____8418) with
| (bs1, t') -> begin
(

let uu____8433 = (

let uu____8440 = (FStar_TypeChecker_Env.push_binders env bs1)
in (ctrl_tac_fold f uu____8440 ctrl1 t'))
in (bind uu____8433 (fun uu____8458 -> (match (uu____8458) with
| (t'', ctrl2) -> begin
(

let uu____8473 = (

let uu____8480 = (

let uu___425_8483 = t4
in (

let uu____8486 = (

let uu____8487 = (

let uu____8506 = (FStar_Syntax_Subst.close_binders bs1)
in (

let uu____8515 = (FStar_Syntax_Subst.close bs1 t'')
in ((uu____8506), (uu____8515), (k))))
in FStar_Syntax_Syntax.Tm_abs (uu____8487))
in {FStar_Syntax_Syntax.n = uu____8486; FStar_Syntax_Syntax.pos = uu___425_8483.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___425_8483.FStar_Syntax_Syntax.vars}))
in ((uu____8480), (ctrl2)))
in (ret uu____8473))
end))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(ret ((t3), (ctrl1)))
end
| uu____8568 -> begin
(ret ((t3), (ctrl1)))
end))))
end))))))))))
and ctrl_tac_fold_args : (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term ctrl_tac)  ->  env  ->  ctrl  ->  FStar_Syntax_Syntax.arg Prims.list  ->  FStar_Syntax_Syntax.arg Prims.list ctrl_tac = (fun f env ctrl ts -> (match (ts) with
| [] -> begin
(ret (([]), (ctrl)))
end
| ((t, q))::ts1 -> begin
(

let uu____8615 = (ctrl_tac_fold f env ctrl t)
in (bind uu____8615 (fun uu____8639 -> (match (uu____8639) with
| (t1, ctrl1) -> begin
(

let uu____8654 = (ctrl_tac_fold_args f env ctrl1 ts1)
in (bind uu____8654 (fun uu____8681 -> (match (uu____8681) with
| (ts2, ctrl2) -> begin
(ret (((((t1), (q)))::ts2), (ctrl2)))
end))))
end))))
end))


let rewrite_rec : FStar_Tactics_Types.proofstate  ->  (FStar_Syntax_Syntax.term  ->  rewrite_result ctrl_tac)  ->  unit tac  ->  FStar_Options.optionstate  ->  Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term ctrl_tac = (fun ps ctrl rewriter opts label1 env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let uu____8770 = (

let uu____8777 = (add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true opts label1)
in (bind uu____8777 (fun uu____8786 -> (

let uu____8787 = (ctrl t1)
in (bind uu____8787 (fun res -> (

let uu____8810 = (trivial ())
in (bind uu____8810 (fun uu____8818 -> (ret res))))))))))
in (bind uu____8770 (fun uu____8834 -> (match (uu____8834) with
| (should_rewrite, ctrl1) -> begin
(match ((not (should_rewrite))) with
| true -> begin
(ret ((t1), (ctrl1)))
end
| uu____8857 -> begin
(

let uu____8858 = (FStar_TypeChecker_TcTerm.tc_term (

let uu___427_8867 = env
in {FStar_TypeChecker_Env.solver = uu___427_8867.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___427_8867.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___427_8867.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___427_8867.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___427_8867.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___427_8867.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___427_8867.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___427_8867.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___427_8867.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___427_8867.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___427_8867.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___427_8867.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___427_8867.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___427_8867.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___427_8867.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___427_8867.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___427_8867.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___427_8867.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___427_8867.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___427_8867.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___427_8867.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___427_8867.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___427_8867.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___427_8867.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___427_8867.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___427_8867.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___427_8867.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___427_8867.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___427_8867.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___427_8867.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___427_8867.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___427_8867.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___427_8867.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___427_8867.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___427_8867.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___427_8867.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___427_8867.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___427_8867.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___427_8867.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___427_8867.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___427_8867.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___427_8867.FStar_TypeChecker_Env.nbe}) t1)
in (match (uu____8858) with
| (t2, lcomp, g) -> begin
(

let uu____8877 = ((

let uu____8880 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp)
in (not (uu____8880))) || (

let uu____8882 = (FStar_TypeChecker_Env.is_trivial g)
in (not (uu____8882))))
in (match (uu____8877) with
| true -> begin
(ret ((t2), (globalStop)))
end
| uu____8893 -> begin
(

let typ = lcomp.FStar_Syntax_Syntax.res_typ
in (

let uu____8895 = (new_uvar "pointwise_rec" env typ)
in (bind uu____8895 (fun uu____8915 -> (match (uu____8915) with
| (ut, uvar_ut) -> begin
((log ps (fun uu____8932 -> (

let uu____8933 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____8934 = (FStar_Syntax_Print.term_to_string ut)
in (FStar_Util.print2 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n" uu____8933 uu____8934)))));
(

let uu____8935 = (

let uu____8938 = (

let uu____8939 = (FStar_TypeChecker_TcTerm.universe_of env typ)
in (FStar_Syntax_Util.mk_eq2 uu____8939 typ t2 ut))
in (add_irrelevant_goal "rewrite_rec equation" env uu____8938 opts label1))
in (bind uu____8935 (fun uu____8946 -> (

let uu____8947 = (bind rewriter (fun uu____8961 -> (

let ut1 = (FStar_TypeChecker_Normalize.reduce_uvar_solutions env ut)
in ((log ps (fun uu____8967 -> (

let uu____8968 = (FStar_Syntax_Print.term_to_string t2)
in (

let uu____8969 = (FStar_Syntax_Print.term_to_string ut1)
in (FStar_Util.print2 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n" uu____8968 uu____8969)))));
(ret ((ut1), (ctrl1)));
))))
in (focus uu____8947)))));
)
end)))))
end))
end))
end)
end))))))


let topdown_rewrite : (FStar_Syntax_Syntax.term  ->  (Prims.bool * FStar_BigInt.t) tac)  ->  unit tac  ->  unit tac = (fun ctrl rewriter -> (

let uu____9010 = (bind get (fun ps -> (

let uu____9020 = (match (ps.FStar_Tactics_Types.goals) with
| (g)::gs -> begin
((g), (gs))
end
| [] -> begin
(failwith "no goals")
end)
in (match (uu____9020) with
| (g, gs) -> begin
(

let gt1 = (FStar_Tactics_Types.goal_type g)
in ((log ps (fun uu____9057 -> (

let uu____9058 = (FStar_Syntax_Print.term_to_string gt1)
in (FStar_Util.print1 "Topdown_rewrite starting with %s\n" uu____9058))));
(bind dismiss_all (fun uu____9061 -> (

let uu____9062 = (

let uu____9069 = (FStar_Tactics_Types.goal_env g)
in (ctrl_tac_fold (rewrite_rec ps ctrl rewriter g.FStar_Tactics_Types.opts g.FStar_Tactics_Types.label) uu____9069 keepGoing gt1))
in (bind uu____9062 (fun uu____9081 -> (match (uu____9081) with
| (gt', uu____9089) -> begin
((log ps (fun uu____9093 -> (

let uu____9094 = (FStar_Syntax_Print.term_to_string gt')
in (FStar_Util.print1 "Topdown_rewrite seems to have succeded with %s\n" uu____9094))));
(

let uu____9095 = (push_goals gs)
in (bind uu____9095 (fun uu____9100 -> (

let uu____9101 = (

let uu____9104 = (FStar_Tactics_Types.goal_with_type g gt')
in (uu____9104)::[])
in (add_goals uu____9101)))));
)
end))))));
))
end))))
in (FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____9010)))


let pointwise : FStar_Tactics_Types.direction  ->  unit tac  ->  unit tac = (fun d tau -> (

let uu____9127 = (bind get (fun ps -> (

let uu____9137 = (match (ps.FStar_Tactics_Types.goals) with
| (g)::gs -> begin
((g), (gs))
end
| [] -> begin
(failwith "no goals")
end)
in (match (uu____9137) with
| (g, gs) -> begin
(

let gt1 = (FStar_Tactics_Types.goal_type g)
in ((log ps (fun uu____9174 -> (

let uu____9175 = (FStar_Syntax_Print.term_to_string gt1)
in (FStar_Util.print1 "Pointwise starting with %s\n" uu____9175))));
(bind dismiss_all (fun uu____9178 -> (

let uu____9179 = (

let uu____9182 = (FStar_Tactics_Types.goal_env g)
in (tac_fold_env d (pointwise_rec ps tau g.FStar_Tactics_Types.opts g.FStar_Tactics_Types.label) uu____9182 gt1))
in (bind uu____9179 (fun gt' -> ((log ps (fun uu____9190 -> (

let uu____9191 = (FStar_Syntax_Print.term_to_string gt')
in (FStar_Util.print1 "Pointwise seems to have succeded with %s\n" uu____9191))));
(

let uu____9192 = (push_goals gs)
in (bind uu____9192 (fun uu____9197 -> (

let uu____9198 = (

let uu____9201 = (FStar_Tactics_Types.goal_with_type g gt')
in (uu____9201)::[])
in (add_goals uu____9198)))));
))))));
))
end))))
in (FStar_All.pipe_left (wrap_err "pointwise") uu____9127)))


let trefl : unit  ->  unit tac = (fun uu____9212 -> (

let uu____9215 = (

let uu____9218 = (cur_goal ())
in (bind uu____9218 (fun g -> (

let uu____9236 = (

let uu____9241 = (FStar_Tactics_Types.goal_type g)
in (FStar_Syntax_Util.un_squash uu____9241))
in (match (uu____9236) with
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____9249 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____9249) with
| (hd1, args) -> begin
(

let uu____9288 = (

let uu____9301 = (

let uu____9302 = (FStar_Syntax_Util.un_uinst hd1)
in uu____9302.FStar_Syntax_Syntax.n)
in ((uu____9301), (args)))
in (match (uu____9288) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____9316)::((l, uu____9318))::((r, uu____9320))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid) -> begin
(

let uu____9367 = (

let uu____9370 = (FStar_Tactics_Types.goal_env g)
in (do_unify uu____9370 l r))
in (bind uu____9367 (fun b -> (match (b) with
| true -> begin
(solve' g FStar_Syntax_Util.exp_unit)
end
| uu____9375 -> begin
(

let l1 = (

let uu____9377 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.UnfoldTac)::[]) uu____9377 l))
in (

let r1 = (

let uu____9379 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.UnfoldTac)::[]) uu____9379 r))
in (

let uu____9380 = (

let uu____9383 = (FStar_Tactics_Types.goal_env g)
in (do_unify uu____9383 l1 r1))
in (bind uu____9380 (fun b1 -> (match (b1) with
| true -> begin
(solve' g FStar_Syntax_Util.exp_unit)
end
| uu____9388 -> begin
(

let uu____9389 = (

let uu____9390 = (FStar_Tactics_Types.goal_env g)
in (tts uu____9390 l1))
in (

let uu____9391 = (

let uu____9392 = (FStar_Tactics_Types.goal_env g)
in (tts uu____9392 r1))
in (fail2 "not a trivial equality ((%s) vs (%s))" uu____9389 uu____9391)))
end))))))
end))))
end
| (hd2, uu____9394) -> begin
(

let uu____9411 = (

let uu____9412 = (FStar_Tactics_Types.goal_env g)
in (tts uu____9412 t))
in (fail1 "trefl: not an equality (%s)" uu____9411))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
(fail "not an irrelevant goal")
end)))))
in (FStar_All.pipe_left (wrap_err "trefl") uu____9215)))


let dup : unit  ->  unit tac = (fun uu____9425 -> (

let uu____9428 = (cur_goal ())
in (bind uu____9428 (fun g -> (

let uu____9434 = (

let uu____9441 = (FStar_Tactics_Types.goal_env g)
in (

let uu____9442 = (FStar_Tactics_Types.goal_type g)
in (new_uvar "dup" uu____9441 uu____9442)))
in (bind uu____9434 (fun uu____9451 -> (match (uu____9451) with
| (u, u_uvar) -> begin
(

let g' = (

let uu___428_9461 = g
in {FStar_Tactics_Types.goal_main_env = uu___428_9461.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = u_uvar; FStar_Tactics_Types.opts = uu___428_9461.FStar_Tactics_Types.opts; FStar_Tactics_Types.is_guard = uu___428_9461.FStar_Tactics_Types.is_guard; FStar_Tactics_Types.label = uu___428_9461.FStar_Tactics_Types.label})
in (bind __dismiss (fun uu____9464 -> (

let uu____9465 = (

let uu____9468 = (FStar_Tactics_Types.goal_env g)
in (

let uu____9469 = (

let uu____9470 = (

let uu____9471 = (FStar_Tactics_Types.goal_env g)
in (

let uu____9472 = (FStar_Tactics_Types.goal_type g)
in (FStar_TypeChecker_TcTerm.universe_of uu____9471 uu____9472)))
in (

let uu____9473 = (FStar_Tactics_Types.goal_type g)
in (

let uu____9474 = (FStar_Tactics_Types.goal_witness g)
in (FStar_Syntax_Util.mk_eq2 uu____9470 uu____9473 u uu____9474))))
in (add_irrelevant_goal "dup equation" uu____9468 uu____9469 g.FStar_Tactics_Types.opts g.FStar_Tactics_Types.label)))
in (bind uu____9465 (fun uu____9477 -> (

let uu____9478 = (add_goals ((g')::[]))
in (bind uu____9478 (fun uu____9482 -> (ret ()))))))))))
end))))))))


let rec longest_prefix : 'a . ('a  ->  'a  ->  Prims.bool)  ->  'a Prims.list  ->  'a Prims.list  ->  ('a Prims.list * 'a Prims.list * 'a Prims.list) = (fun f l1 l2 -> (

let rec aux = (fun acc l11 l21 -> (match (((l11), (l21))) with
| ((x)::xs, (y)::ys) -> begin
(

let uu____9605 = (f x y)
in (match (uu____9605) with
| true -> begin
(aux ((x)::acc) xs ys)
end
| uu____9618 -> begin
((acc), (xs), (ys))
end))
end
| uu____9625 -> begin
((acc), (l11), (l21))
end))
in (

let uu____9640 = (aux [] l1 l2)
in (match (uu____9640) with
| (pr, t1, t2) -> begin
(((FStar_List.rev pr)), (t1), (t2))
end))))


let join_goals : FStar_Tactics_Types.goal  ->  FStar_Tactics_Types.goal  ->  FStar_Tactics_Types.goal tac = (fun g1 g2 -> (

let close_forall_no_univs1 = (fun bs f -> (FStar_List.fold_right (fun b f1 -> (FStar_Syntax_Util.mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1)) bs f))
in (

let uu____9745 = (get_phi g1)
in (match (uu____9745) with
| FStar_Pervasives_Native.None -> begin
(fail "goal 1 is not irrelevant")
end
| FStar_Pervasives_Native.Some (phi1) -> begin
(

let uu____9751 = (get_phi g2)
in (match (uu____9751) with
| FStar_Pervasives_Native.None -> begin
(fail "goal 2 is not irrelevant")
end
| FStar_Pervasives_Native.Some (phi2) -> begin
(

let gamma1 = g1.FStar_Tactics_Types.goal_ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma
in (

let gamma2 = g2.FStar_Tactics_Types.goal_ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma
in (

let uu____9763 = (longest_prefix FStar_Syntax_Syntax.eq_binding (FStar_List.rev gamma1) (FStar_List.rev gamma2))
in (match (uu____9763) with
| (gamma, r1, r2) -> begin
(

let t1 = (

let uu____9794 = (FStar_TypeChecker_Env.binders_of_bindings (FStar_List.rev r1))
in (close_forall_no_univs1 uu____9794 phi1))
in (

let t2 = (

let uu____9804 = (FStar_TypeChecker_Env.binders_of_bindings (FStar_List.rev r2))
in (close_forall_no_univs1 uu____9804 phi2))
in (

let uu____9813 = (set_solution g1 FStar_Syntax_Util.exp_unit)
in (bind uu____9813 (fun uu____9818 -> (

let uu____9819 = (set_solution g2 FStar_Syntax_Util.exp_unit)
in (bind uu____9819 (fun uu____9826 -> (

let ng = (FStar_Syntax_Util.mk_conj t1 t2)
in (

let nenv = (

let uu___429_9831 = (FStar_Tactics_Types.goal_env g1)
in (

let uu____9832 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {FStar_TypeChecker_Env.solver = uu___429_9831.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___429_9831.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___429_9831.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = (FStar_List.rev gamma); FStar_TypeChecker_Env.gamma_sig = uu___429_9831.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu____9832; FStar_TypeChecker_Env.modules = uu___429_9831.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___429_9831.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___429_9831.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___429_9831.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___429_9831.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___429_9831.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___429_9831.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___429_9831.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___429_9831.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___429_9831.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___429_9831.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___429_9831.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___429_9831.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___429_9831.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___429_9831.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___429_9831.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___429_9831.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___429_9831.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___429_9831.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___429_9831.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___429_9831.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___429_9831.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___429_9831.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___429_9831.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___429_9831.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___429_9831.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___429_9831.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___429_9831.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___429_9831.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___429_9831.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___429_9831.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___429_9831.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___429_9831.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___429_9831.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___429_9831.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___429_9831.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___429_9831.FStar_TypeChecker_Env.nbe}))
in (

let uu____9835 = (mk_irrelevant_goal "joined" nenv ng g1.FStar_Tactics_Types.opts g1.FStar_Tactics_Types.label)
in (bind uu____9835 (fun goal -> (mlog (fun uu____9844 -> (

let uu____9845 = (goal_to_string_verbose g1)
in (

let uu____9846 = (goal_to_string_verbose g2)
in (

let uu____9847 = (goal_to_string_verbose goal)
in (FStar_Util.print3 "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n" uu____9845 uu____9846 uu____9847))))) (fun uu____9849 -> (ret goal))))))))))))))))
end))))
end))
end))))


let join : unit  ->  unit tac = (fun uu____9856 -> (bind get (fun ps -> (match (ps.FStar_Tactics_Types.goals) with
| (g1)::(g2)::gs -> begin
(

let uu____9872 = (set (

let uu___430_9877 = ps
in {FStar_Tactics_Types.main_context = uu___430_9877.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___430_9877.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___430_9877.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = gs; FStar_Tactics_Types.smt_goals = uu___430_9877.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___430_9877.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___430_9877.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___430_9877.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___430_9877.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___430_9877.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___430_9877.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___430_9877.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu___430_9877.FStar_Tactics_Types.local_state}))
in (bind uu____9872 (fun uu____9880 -> (

let uu____9881 = (join_goals g1 g2)
in (bind uu____9881 (fun g12 -> (add_goals ((g12)::[]))))))))
end
| uu____9886 -> begin
(fail "join: less than 2 goals")
end))))


let cases : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac = (fun t -> (

let uu____9906 = (

let uu____9913 = (cur_goal ())
in (bind uu____9913 (fun g -> (

let uu____9923 = (

let uu____9932 = (FStar_Tactics_Types.goal_env g)
in (__tc uu____9932 t))
in (bind uu____9923 (fun uu____9960 -> (match (uu____9960) with
| (t1, typ, guard) -> begin
(

let uu____9976 = (FStar_Syntax_Util.head_and_args typ)
in (match (uu____9976) with
| (hd1, args) -> begin
(

let uu____10025 = (

let uu____10040 = (

let uu____10041 = (FStar_Syntax_Util.un_uinst hd1)
in uu____10041.FStar_Syntax_Syntax.n)
in ((uu____10040), (args)))
in (match (uu____10025) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((p, uu____10062))::((q, uu____10064))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid) -> begin
(

let v_p = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p)
in (

let v_q = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None q)
in (

let g1 = (

let uu____10118 = (

let uu____10119 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Env.push_bv uu____10119 v_p))
in (FStar_Tactics_Types.goal_with_env g uu____10118))
in (

let g2 = (

let uu____10121 = (

let uu____10122 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Env.push_bv uu____10122 v_q))
in (FStar_Tactics_Types.goal_with_env g uu____10121))
in (bind __dismiss (fun uu____10129 -> (

let uu____10130 = (add_goals ((g1)::(g2)::[]))
in (bind uu____10130 (fun uu____10139 -> (

let uu____10140 = (

let uu____10145 = (FStar_Syntax_Syntax.bv_to_name v_p)
in (

let uu____10146 = (FStar_Syntax_Syntax.bv_to_name v_q)
in ((uu____10145), (uu____10146))))
in (ret uu____10140)))))))))))
end
| uu____10151 -> begin
(

let uu____10166 = (

let uu____10167 = (FStar_Tactics_Types.goal_env g)
in (tts uu____10167 typ))
in (fail1 "Not a disjunction: %s" uu____10166))
end))
end))
end)))))))
in (FStar_All.pipe_left (wrap_err "cases") uu____9906)))


let set_options : Prims.string  ->  unit tac = (fun s -> (

let uu____10197 = (

let uu____10200 = (cur_goal ())
in (bind uu____10200 (fun g -> ((FStar_Options.push ());
(

let uu____10213 = (FStar_Util.smap_copy g.FStar_Tactics_Types.opts)
in (FStar_Options.set uu____10213));
(

let res = (FStar_Options.set_options FStar_Options.Set s)
in (

let opts' = (FStar_Options.peek ())
in ((FStar_Options.pop ());
(match (res) with
| FStar_Getopt.Success -> begin
(

let g' = (

let uu___431_10220 = g
in {FStar_Tactics_Types.goal_main_env = uu___431_10220.FStar_Tactics_Types.goal_main_env; FStar_Tactics_Types.goal_ctx_uvar = uu___431_10220.FStar_Tactics_Types.goal_ctx_uvar; FStar_Tactics_Types.opts = opts'; FStar_Tactics_Types.is_guard = uu___431_10220.FStar_Tactics_Types.is_guard; FStar_Tactics_Types.label = uu___431_10220.FStar_Tactics_Types.label})
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
in (FStar_All.pipe_left (wrap_err "set_options") uu____10197)))


let top_env : unit  ->  env tac = (fun uu____10232 -> (bind get (fun ps -> (FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context))))


let lax_on : unit  ->  Prims.bool tac = (fun uu____10245 -> (

let uu____10248 = (cur_goal ())
in (bind uu____10248 (fun g -> (

let uu____10254 = ((FStar_Options.lax ()) || (

let uu____10256 = (FStar_Tactics_Types.goal_env g)
in uu____10256.FStar_TypeChecker_Env.lax))
in (ret uu____10254))))))


let unquote : FStar_Reflection_Data.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term tac = (fun ty tm -> (

let uu____10271 = (mlog (fun uu____10276 -> (

let uu____10277 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "unquote: tm = %s\n" uu____10277))) (fun uu____10280 -> (

let uu____10281 = (cur_goal ())
in (bind uu____10281 (fun goal -> (

let env = (

let uu____10289 = (FStar_Tactics_Types.goal_env goal)
in (FStar_TypeChecker_Env.set_expected_typ uu____10289 ty))
in (

let uu____10290 = (__tc_ghost env tm)
in (bind uu____10290 (fun uu____10309 -> (match (uu____10309) with
| (tm1, typ, guard) -> begin
(mlog (fun uu____10323 -> (

let uu____10324 = (FStar_Syntax_Print.term_to_string tm1)
in (FStar_Util.print1 "unquote: tm\' = %s\n" uu____10324))) (fun uu____10326 -> (mlog (fun uu____10329 -> (

let uu____10330 = (FStar_Syntax_Print.term_to_string typ)
in (FStar_Util.print1 "unquote: typ = %s\n" uu____10330))) (fun uu____10333 -> (

let uu____10334 = (proc_guard "unquote" env guard)
in (bind uu____10334 (fun uu____10338 -> (ret tm1))))))))
end))))))))))
in (FStar_All.pipe_left (wrap_err "unquote") uu____10271)))


let uvar_env : env  ->  FStar_Reflection_Data.typ FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term tac = (fun env ty -> (

let uu____10361 = (match (ty) with
| FStar_Pervasives_Native.Some (ty1) -> begin
(ret ty1)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____10367 = (

let uu____10374 = (

let uu____10375 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10375))
in (new_uvar "uvar_env.2" env uu____10374))
in (bind uu____10367 (fun uu____10391 -> (match (uu____10391) with
| (typ, uvar_typ) -> begin
(ret typ)
end))))
end)
in (bind uu____10361 (fun typ -> (

let uu____10403 = (new_uvar "uvar_env" env typ)
in (bind uu____10403 (fun uu____10417 -> (match (uu____10417) with
| (t, uvar_t) -> begin
(ret t)
end))))))))


let unshelve : FStar_Syntax_Syntax.term  ->  unit tac = (fun t -> (

let uu____10435 = (bind get (fun ps -> (

let env = ps.FStar_Tactics_Types.main_context
in (

let opts = (match (ps.FStar_Tactics_Types.goals) with
| (g)::uu____10454 -> begin
g.FStar_Tactics_Types.opts
end
| uu____10457 -> begin
(FStar_Options.peek ())
end)
in (

let uu____10460 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____10460) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (ctx_uvar, uu____10480); FStar_Syntax_Syntax.pos = uu____10481; FStar_Syntax_Syntax.vars = uu____10482}, uu____10483) -> begin
(

let env1 = (

let uu___432_10525 = env
in {FStar_TypeChecker_Env.solver = uu___432_10525.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___432_10525.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___432_10525.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma; FStar_TypeChecker_Env.gamma_sig = uu___432_10525.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___432_10525.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___432_10525.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___432_10525.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___432_10525.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___432_10525.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___432_10525.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___432_10525.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___432_10525.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___432_10525.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___432_10525.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___432_10525.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___432_10525.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___432_10525.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___432_10525.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___432_10525.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___432_10525.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___432_10525.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___432_10525.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___432_10525.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___432_10525.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___432_10525.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___432_10525.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___432_10525.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___432_10525.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___432_10525.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___432_10525.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___432_10525.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___432_10525.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___432_10525.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___432_10525.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___432_10525.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___432_10525.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___432_10525.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___432_10525.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___432_10525.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___432_10525.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___432_10525.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___432_10525.FStar_TypeChecker_Env.nbe})
in (

let g = (FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false "")
in (

let uu____10527 = (

let uu____10530 = (bnorm_goal g)
in (uu____10530)::[])
in (add_goals uu____10527))))
end
| uu____10531 -> begin
(fail "not a uvar")
end))))))
in (FStar_All.pipe_left (wrap_err "unshelve") uu____10435)))


let tac_and : Prims.bool tac  ->  Prims.bool tac  ->  Prims.bool tac = (fun t1 t2 -> (

let comp = (bind t1 (fun b -> (

let uu____10580 = (match (b) with
| true -> begin
t2
end
| uu____10585 -> begin
(ret false)
end)
in (bind uu____10580 (fun b' -> (match (b') with
| true -> begin
(ret b')
end
| uu____10590 -> begin
(fail "")
end))))))
in (

let uu____10591 = (trytac comp)
in (bind uu____10591 (fun uu___362_10599 -> (match (uu___362_10599) with
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

let uu____10625 = (bind get (fun ps -> (

let uu____10631 = (__tc e t1)
in (bind uu____10631 (fun uu____10651 -> (match (uu____10651) with
| (t11, ty1, g1) -> begin
(

let uu____10663 = (__tc e t2)
in (bind uu____10663 (fun uu____10683 -> (match (uu____10683) with
| (t21, ty2, g2) -> begin
(

let uu____10695 = (proc_guard "unify_env g1" e g1)
in (bind uu____10695 (fun uu____10700 -> (

let uu____10701 = (proc_guard "unify_env g2" e g2)
in (bind uu____10701 (fun uu____10707 -> (

let uu____10708 = (do_unify e ty1 ty2)
in (

let uu____10711 = (do_unify e t11 t21)
in (tac_and uu____10708 uu____10711)))))))))
end))))
end))))))
in (FStar_All.pipe_left (wrap_err "unify_env") uu____10625)))


let launch_process : Prims.string  ->  Prims.string Prims.list  ->  Prims.string  ->  Prims.string tac = (fun prog args input -> (bind idtac (fun uu____10744 -> (

let uu____10745 = (FStar_Options.unsafe_tactic_exec ())
in (match (uu____10745) with
| true -> begin
(

let s = (FStar_Util.run_process "tactic_launch" prog args (FStar_Pervasives_Native.Some (input)))
in (ret s))
end
| uu____10749 -> begin
(fail "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
end)))))


let fresh_bv_named : Prims.string  ->  FStar_Reflection_Data.typ  ->  FStar_Syntax_Syntax.bv tac = (fun nm t -> (bind idtac (fun uu____10766 -> (

let uu____10767 = (FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t)
in (ret uu____10767)))))


let change : FStar_Reflection_Data.typ  ->  unit tac = (fun ty -> (

let uu____10777 = (mlog (fun uu____10782 -> (

let uu____10783 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.print1 "change: ty = %s\n" uu____10783))) (fun uu____10786 -> (

let uu____10787 = (cur_goal ())
in (bind uu____10787 (fun g -> (

let uu____10793 = (

let uu____10802 = (FStar_Tactics_Types.goal_env g)
in (__tc uu____10802 ty))
in (bind uu____10793 (fun uu____10814 -> (match (uu____10814) with
| (ty1, uu____10824, guard) -> begin
(

let uu____10826 = (

let uu____10829 = (FStar_Tactics_Types.goal_env g)
in (proc_guard "change" uu____10829 guard))
in (bind uu____10826 (fun uu____10832 -> (

let uu____10833 = (

let uu____10836 = (FStar_Tactics_Types.goal_env g)
in (

let uu____10837 = (FStar_Tactics_Types.goal_type g)
in (do_unify uu____10836 uu____10837 ty1)))
in (bind uu____10833 (fun bb -> (match (bb) with
| true -> begin
(

let uu____10843 = (FStar_Tactics_Types.goal_with_type g ty1)
in (replace_cur uu____10843))
end
| uu____10844 -> begin
(

let steps = (FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Primops)::[]
in (

let ng = (

let uu____10849 = (FStar_Tactics_Types.goal_env g)
in (

let uu____10850 = (FStar_Tactics_Types.goal_type g)
in (normalize steps uu____10849 uu____10850)))
in (

let nty = (

let uu____10852 = (FStar_Tactics_Types.goal_env g)
in (normalize steps uu____10852 ty1))
in (

let uu____10853 = (

let uu____10856 = (FStar_Tactics_Types.goal_env g)
in (do_unify uu____10856 ng nty))
in (bind uu____10853 (fun b -> (match (b) with
| true -> begin
(

let uu____10862 = (FStar_Tactics_Types.goal_with_type g ty1)
in (replace_cur uu____10862))
end
| uu____10863 -> begin
(fail "not convertible")
end)))))))
end)))))))
end)))))))))
in (FStar_All.pipe_left (wrap_err "change") uu____10777)))


let failwhen : 'a . Prims.bool  ->  Prims.string  ->  (unit  ->  'a tac)  ->  'a tac = (fun b msg k -> (match (b) with
| true -> begin
(fail msg)
end
| uu____10903 -> begin
(k ())
end))


let t_destruct : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac = (fun s_tm -> (

let uu____10925 = (

let uu____10934 = (cur_goal ())
in (bind uu____10934 (fun g -> (

let uu____10946 = (

let uu____10955 = (FStar_Tactics_Types.goal_env g)
in (__tc uu____10955 s_tm))
in (bind uu____10946 (fun uu____10973 -> (match (uu____10973) with
| (s_tm1, s_ty, guard) -> begin
(

let uu____10991 = (

let uu____10994 = (FStar_Tactics_Types.goal_env g)
in (proc_guard "destruct" uu____10994 guard))
in (bind uu____10991 (fun uu____11006 -> (

let uu____11007 = (FStar_Syntax_Util.head_and_args' s_ty)
in (match (uu____11007) with
| (h, args) -> begin
(

let uu____11052 = (

let uu____11059 = (

let uu____11060 = (FStar_Syntax_Subst.compress h)
in uu____11060.FStar_Syntax_Syntax.n)
in (match (uu____11059) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(ret ((fv), ([])))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____11075; FStar_Syntax_Syntax.vars = uu____11076}, us) -> begin
(ret ((fv), (us)))
end
| uu____11086 -> begin
(fail "type is not an fv")
end))
in (bind uu____11052 (fun uu____11106 -> (match (uu____11106) with
| (fv, a_us) -> begin
(

let t_lid = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let uu____11122 = (

let uu____11125 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Env.lookup_sigelt uu____11125 t_lid))
in (match (uu____11122) with
| FStar_Pervasives_Native.None -> begin
(fail "type not found in environment")
end
| FStar_Pervasives_Native.Some (se) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_lid, t_us, t_ps, t_ty, mut, c_lids) -> begin
(failwhen (Prims.op_disEquality (FStar_List.length a_us) (FStar_List.length t_us)) "t_us don\'t match?" (fun uu____11174 -> (

let uu____11175 = (FStar_Syntax_Subst.open_term t_ps t_ty)
in (match (uu____11175) with
| (t_ps1, t_ty1) -> begin
(

let uu____11190 = (mapM (fun c_lid -> (

let uu____11218 = (

let uu____11221 = (FStar_Tactics_Types.goal_env g)
in (FStar_TypeChecker_Env.lookup_sigelt uu____11221 c_lid))
in (match (uu____11218) with
| FStar_Pervasives_Native.None -> begin
(fail "ctor not found?")
end
| FStar_Pervasives_Native.Some (se1) -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (_c_lid, c_us, c_ty, _t_lid, nparam, mut1) -> begin
(

let fv1 = (FStar_Syntax_Syntax.lid_as_fv c_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in (failwhen (Prims.op_disEquality (FStar_List.length a_us) (FStar_List.length c_us)) "t_us don\'t match?" (fun uu____11291 -> (

let s = (FStar_TypeChecker_Env.mk_univ_subst c_us a_us)
in (

let c_ty1 = (FStar_Syntax_Subst.subst s c_ty)
in (

let uu____11296 = (FStar_TypeChecker_Env.inst_tscheme ((c_us), (c_ty1)))
in (match (uu____11296) with
| (c_us1, c_ty2) -> begin
(

let uu____11319 = (FStar_Syntax_Util.arrow_formals_comp c_ty2)
in (match (uu____11319) with
| (bs, comp) -> begin
(

let uu____11362 = (FStar_List.splitAt nparam bs)
in (match (uu____11362) with
| (d_ps, bs1) -> begin
(

let uu____11435 = (

let uu____11436 = (FStar_Syntax_Util.is_total_comp comp)
in (not (uu____11436)))
in (failwhen uu____11435 "not total?" (fun uu____11453 -> (

let mk_pat = (fun p -> {FStar_Syntax_Syntax.v = p; FStar_Syntax_Syntax.p = s_tm1.FStar_Syntax_Syntax.pos})
in (

let is_imp = (fun uu___363_11469 -> (match (uu___363_11469) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11472)) -> begin
true
end
| uu____11473 -> begin
false
end))
in (

let uu____11476 = (FStar_List.splitAt nparam args)
in (match (uu____11476) with
| (a_ps, a_is) -> begin
(failwhen (Prims.op_disEquality (FStar_List.length a_ps) (FStar_List.length d_ps)) "params not match?" (fun uu____11609 -> (

let d_ps_a_ps = (FStar_List.zip d_ps a_ps)
in (

let subst1 = (FStar_List.map (fun uu____11671 -> (match (uu____11671) with
| ((bv, uu____11691), (t, uu____11693)) -> begin
FStar_Syntax_Syntax.NT (((bv), (t)))
end)) d_ps_a_ps)
in (

let bs2 = (FStar_Syntax_Subst.subst_binders subst1 bs1)
in (

let subpats_1 = (FStar_List.map (fun uu____11761 -> (match (uu____11761) with
| ((bv, uu____11787), (t, uu____11789)) -> begin
(((mk_pat (FStar_Syntax_Syntax.Pat_dot_term (((bv), (t)))))), (true))
end)) d_ps_a_ps)
in (

let subpats_2 = (FStar_List.map (fun uu____11844 -> (match (uu____11844) with
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

let uu____11894 = (FStar_TypeChecker_TcTerm.tc_pat (

let uu___433_11911 = env
in {FStar_TypeChecker_Env.solver = uu___433_11911.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___433_11911.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___433_11911.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___433_11911.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___433_11911.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___433_11911.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___433_11911.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___433_11911.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___433_11911.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___433_11911.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___433_11911.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___433_11911.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___433_11911.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___433_11911.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___433_11911.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___433_11911.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___433_11911.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___433_11911.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___433_11911.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___433_11911.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___433_11911.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___433_11911.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___433_11911.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___433_11911.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___433_11911.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___433_11911.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___433_11911.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___433_11911.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___433_11911.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___433_11911.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___433_11911.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___433_11911.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___433_11911.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___433_11911.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___433_11911.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___433_11911.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___433_11911.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___433_11911.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___433_11911.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___433_11911.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___433_11911.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___433_11911.FStar_TypeChecker_Env.nbe}) s_ty pat)
in (match (uu____11894) with
| (uu____11924, uu____11925, uu____11926, pat_t, uu____11928, _guard_pat) -> begin
(

let eq_b = (

let uu____11935 = (

let uu____11936 = (FStar_Syntax_Util.mk_eq2 equ s_ty s_tm1 pat_t)
in (FStar_Syntax_Util.mk_squash equ uu____11936))
in (FStar_Syntax_Syntax.gen_bv "breq" FStar_Pervasives_Native.None uu____11935))
in (

let cod1 = (

let uu____11940 = (

let uu____11949 = (FStar_Syntax_Syntax.mk_binder eq_b)
in (uu____11949)::[])
in (

let uu____11968 = (FStar_Syntax_Syntax.mk_Total cod)
in (FStar_Syntax_Util.arrow uu____11940 uu____11968)))
in (

let nty = (

let uu____11974 = (FStar_Syntax_Syntax.mk_Total cod1)
in (FStar_Syntax_Util.arrow bs2 uu____11974))
in (

let uu____11977 = (new_uvar "destruct branch" env nty)
in (bind uu____11977 (fun uu____12006 -> (match (uu____12006) with
| (uvt, uv) -> begin
(

let g' = (FStar_Tactics_Types.mk_goal env uv g.FStar_Tactics_Types.opts false g.FStar_Tactics_Types.label)
in (

let brt = (FStar_Syntax_Util.mk_app_binders uvt bs2)
in (

let brt1 = (

let uu____12032 = (

let uu____12043 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit)
in (uu____12043)::[])
in (FStar_Syntax_Util.mk_app brt uu____12032))
in (

let br = (FStar_Syntax_Subst.close_branch ((pat), (FStar_Pervasives_Native.None), (brt1)))
in (

let uu____12079 = (

let uu____12090 = (

let uu____12095 = (FStar_BigInt.of_int_fs (FStar_List.length bs2))
in ((fv1), (uu____12095)))
in ((g'), (br), (uu____12090)))
in (ret uu____12079))))))
end)))))))
end))))))))))))))
end)))))))
end))
end))
end)))))))
end
| uu____12116 -> begin
(fail "impossible: not a ctor")
end)
end))) c_lids)
in (bind uu____11190 (fun goal_brs -> (

let uu____12165 = (FStar_List.unzip3 goal_brs)
in (match (uu____12165) with
| (goals, brs, infos) -> begin
(

let w = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((s_tm1), (brs)))) FStar_Pervasives_Native.None s_tm1.FStar_Syntax_Syntax.pos)
in (

let uu____12238 = (solve' g w)
in (bind uu____12238 (fun uu____12249 -> (

let uu____12250 = (add_goals goals)
in (bind uu____12250 (fun uu____12260 -> (ret infos))))))))
end)))))
end))))
end
| uu____12267 -> begin
(fail "not an inductive type")
end)
end)))
end))))
end)))))
end)))))))
in (FStar_All.pipe_left (wrap_err "destruct") uu____10925)))


let rec last : 'a . 'a Prims.list  ->  'a = (fun l -> (match (l) with
| [] -> begin
(failwith "last: empty list")
end
| (x)::[] -> begin
x
end
| (uu____12312)::xs -> begin
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

let uu____12340 = (init xs)
in (x)::uu____12340)
end))


let rec inspect : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.term_view tac = (fun t -> (

let uu____12352 = (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let t2 = (FStar_Syntax_Util.un_uinst t1)
in (

let t3 = (FStar_Syntax_Util.unlazy_emb t2)
in (match (t3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t4, uu____12361) -> begin
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

let uu____12426 = (last args)
in (match (uu____12426) with
| (a, q) -> begin
(

let q' = (FStar_Reflection_Basic.inspect_aqual q)
in (

let uu____12456 = (

let uu____12457 = (

let uu____12462 = (

let uu____12463 = (

let uu____12468 = (init args)
in (FStar_Syntax_Syntax.mk_Tm_app hd1 uu____12468))
in (uu____12463 FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos))
in ((uu____12462), (((a), (q')))))
in FStar_Reflection_Data.Tv_App (uu____12457))
in (FStar_All.pipe_left ret uu____12456)))
end))
end
| FStar_Syntax_Syntax.Tm_abs ([], uu____12481, uu____12482) -> begin
(failwith "empty arguments on Tm_abs")
end
| FStar_Syntax_Syntax.Tm_abs (bs, t4, k) -> begin
(

let uu____12534 = (FStar_Syntax_Subst.open_term bs t4)
in (match (uu____12534) with
| (bs1, t5) -> begin
(match (bs1) with
| [] -> begin
(failwith "impossible")
end
| (b)::bs2 -> begin
(

let uu____12575 = (

let uu____12576 = (

let uu____12581 = (FStar_Syntax_Util.abs bs2 t5 k)
in ((b), (uu____12581)))
in FStar_Reflection_Data.Tv_Abs (uu____12576))
in (FStar_All.pipe_left ret uu____12575))
end)
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____12584) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type (())))
end
| FStar_Syntax_Syntax.Tm_arrow ([], k) -> begin
(failwith "empty binders on arrow")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____12608) -> begin
(

let uu____12623 = (FStar_Syntax_Util.arrow_one t3)
in (match (uu____12623) with
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

let uu____12653 = (FStar_Syntax_Subst.open_term ((b)::[]) t4)
in (match (uu____12653) with
| (b', t5) -> begin
(

let b1 = (match (b') with
| (b'1)::[] -> begin
b'1
end
| uu____12706 -> begin
(failwith "impossible")
end)
in (FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Refine ((((FStar_Pervasives_Native.fst b1)), (t5))))))
end)))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____12718 = (

let uu____12719 = (FStar_Reflection_Basic.inspect_const c)
in FStar_Reflection_Data.Tv_Const (uu____12719))
in (FStar_All.pipe_left ret uu____12718))
end
| FStar_Syntax_Syntax.Tm_uvar (ctx_u, s) -> begin
(

let uu____12740 = (

let uu____12741 = (

let uu____12746 = (

let uu____12747 = (FStar_Syntax_Unionfind.uvar_id ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_BigInt.of_int_fs uu____12747))
in ((uu____12746), (((ctx_u), (s)))))
in FStar_Reflection_Data.Tv_Uvar (uu____12741))
in (FStar_All.pipe_left ret uu____12740))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), t21) -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| uu____12778 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____12781) -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv) -> begin
(

let b = (FStar_Syntax_Syntax.mk_binder bv)
in (

let uu____12786 = (FStar_Syntax_Subst.open_term ((b)::[]) t21)
in (match (uu____12786) with
| (bs, t22) -> begin
(

let b1 = (match (bs) with
| (b1)::[] -> begin
b1
end
| uu____12839 -> begin
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
| uu____12870 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____12873) -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv) -> begin
(

let uu____12877 = (FStar_Syntax_Subst.open_let_rec ((lb)::[]) t21)
in (match (uu____12877) with
| (lbs, t22) -> begin
(match (lbs) with
| (lb1)::[] -> begin
(match (lb1.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____12897) -> begin
(ret FStar_Reflection_Data.Tv_Unknown)
end
| FStar_Util.Inl (bv1) -> begin
(FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Let (((true), (bv1), (lb1.FStar_Syntax_Syntax.lbdef), (t22)))))
end)
end
| uu____12901 -> begin
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

let uu____12955 = (FStar_Reflection_Basic.inspect_const c)
in FStar_Reflection_Data.Pat_Constant (uu____12955))
end
| FStar_Syntax_Syntax.Pat_cons (fv, ps) -> begin
(

let uu____12974 = (

let uu____12981 = (FStar_List.map (fun uu____12993 -> (match (uu____12993) with
| (p1, uu____13001) -> begin
(inspect_pat p1)
end)) ps)
in ((fv), (uu____12981)))
in FStar_Reflection_Data.Pat_Cons (uu____12974))
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

let brs2 = (FStar_List.map (fun uu___364_13095 -> (match (uu___364_13095) with
| (pat, uu____13117, t5) -> begin
(

let uu____13135 = (inspect_pat pat)
in ((uu____13135), (t5)))
end)) brs1)
in (FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (((t4), (brs2))))))))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
end
| uu____13144 -> begin
((

let uu____13146 = (

let uu____13151 = (

let uu____13152 = (FStar_Syntax_Print.tag_of_term t3)
in (

let uu____13153 = (FStar_Syntax_Print.term_to_string t3)
in (FStar_Util.format2 "inspect: outside of expected syntax (%s, %s)\n" uu____13152 uu____13153)))
in ((FStar_Errors.Warning_CantInspect), (uu____13151)))
in (FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____13146));
(FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown);
)
end))))
in (wrap_err "inspect" uu____12352)))


let pack : FStar_Reflection_Data.term_view  ->  FStar_Syntax_Syntax.term tac = (fun tv -> (match (tv) with
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____13166 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_left ret uu____13166))
end
| FStar_Reflection_Data.Tv_BVar (bv) -> begin
(

let uu____13170 = (FStar_Syntax_Syntax.bv_to_tm bv)
in (FStar_All.pipe_left ret uu____13170))
end
| FStar_Reflection_Data.Tv_FVar (fv) -> begin
(

let uu____13174 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (FStar_All.pipe_left ret uu____13174))
end
| FStar_Reflection_Data.Tv_App (l, (r, q)) -> begin
(

let q' = (FStar_Reflection_Basic.pack_aqual q)
in (

let uu____13181 = (FStar_Syntax_Util.mk_app l ((((r), (q')))::[]))
in (FStar_All.pipe_left ret uu____13181)))
end
| FStar_Reflection_Data.Tv_Abs (b, t) -> begin
(

let uu____13206 = (FStar_Syntax_Util.abs ((b)::[]) t FStar_Pervasives_Native.None)
in (FStar_All.pipe_left ret uu____13206))
end
| FStar_Reflection_Data.Tv_Arrow (b, c) -> begin
(

let uu____13223 = (FStar_Syntax_Util.arrow ((b)::[]) c)
in (FStar_All.pipe_left ret uu____13223))
end
| FStar_Reflection_Data.Tv_Type (()) -> begin
(FStar_All.pipe_left ret FStar_Syntax_Util.ktype)
end
| FStar_Reflection_Data.Tv_Refine (bv, t) -> begin
(

let uu____13242 = (FStar_Syntax_Util.refine bv t)
in (FStar_All.pipe_left ret uu____13242))
end
| FStar_Reflection_Data.Tv_Const (c) -> begin
(

let uu____13246 = (

let uu____13247 = (

let uu____13254 = (

let uu____13255 = (FStar_Reflection_Basic.pack_const c)
in FStar_Syntax_Syntax.Tm_constant (uu____13255))
in (FStar_Syntax_Syntax.mk uu____13254))
in (uu____13247 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_All.pipe_left ret uu____13246))
end
| FStar_Reflection_Data.Tv_Uvar (_u, ctx_u_s) -> begin
(

let uu____13263 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (ctx_u_s)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____13263))
end
| FStar_Reflection_Data.Tv_Let (false, bv, t1, t2) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 [] FStar_Range.dummyRange)
in (

let uu____13272 = (

let uu____13273 = (

let uu____13280 = (

let uu____13281 = (

let uu____13294 = (

let uu____13297 = (

let uu____13298 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____13298)::[])
in (FStar_Syntax_Subst.close uu____13297 t2))
in ((((false), ((lb)::[]))), (uu____13294)))
in FStar_Syntax_Syntax.Tm_let (uu____13281))
in (FStar_Syntax_Syntax.mk uu____13280))
in (uu____13273 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (FStar_All.pipe_left ret uu____13272)))
end
| FStar_Reflection_Data.Tv_Let (true, bv, t1, t2) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 [] FStar_Range.dummyRange)
in (

let uu____13338 = (FStar_Syntax_Subst.close_let_rec ((lb)::[]) t2)
in (match (uu____13338) with
| (lbs, body) -> begin
(

let uu____13353 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____13353))
end)))
end
| FStar_Reflection_Data.Tv_Match (t, brs) -> begin
(

let wrap = (fun v1 -> {FStar_Syntax_Syntax.v = v1; FStar_Syntax_Syntax.p = FStar_Range.dummyRange})
in (

let rec pack_pat = (fun p -> (match (p) with
| FStar_Reflection_Data.Pat_Constant (c) -> begin
(

let uu____13387 = (

let uu____13388 = (FStar_Reflection_Basic.pack_const c)
in FStar_Syntax_Syntax.Pat_constant (uu____13388))
in (FStar_All.pipe_left wrap uu____13387))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____13395 = (

let uu____13396 = (

let uu____13409 = (FStar_List.map (fun p1 -> (

let uu____13425 = (pack_pat p1)
in ((uu____13425), (false)))) ps)
in ((fv), (uu____13409)))
in FStar_Syntax_Syntax.Pat_cons (uu____13396))
in (FStar_All.pipe_left wrap uu____13395))
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

let brs1 = (FStar_List.map (fun uu___365_13471 -> (match (uu___365_13471) with
| (pat, t1) -> begin
(

let uu____13488 = (pack_pat pat)
in ((uu____13488), (FStar_Pervasives_Native.None), (t1)))
end)) brs)
in (

let brs2 = (FStar_List.map FStar_Syntax_Subst.close_branch brs1)
in (

let uu____13536 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((t), (brs2)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____13536))))))
end
| FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) -> begin
(

let uu____13564 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (((FStar_Util.Inl (t)), (tacopt))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____13564))
end
| FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) -> begin
(

let uu____13610 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (((FStar_Util.Inr (c)), (tacopt))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____13610))
end
| FStar_Reflection_Data.Tv_Unknown -> begin
(

let uu____13649 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_All.pipe_left ret uu____13649))
end))


let lget : FStar_Reflection_Data.typ  ->  Prims.string  ->  FStar_Syntax_Syntax.term tac = (fun ty k -> (

let uu____13666 = (bind get (fun ps -> (

let uu____13672 = (FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k)
in (match (uu____13672) with
| FStar_Pervasives_Native.None -> begin
(fail "not found")
end
| FStar_Pervasives_Native.Some (t) -> begin
(unquote ty t)
end))))
in (FStar_All.pipe_left (wrap_err "lget") uu____13666)))


let lset : FStar_Reflection_Data.typ  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  unit tac = (fun _ty k t -> (

let uu____13701 = (bind get (fun ps -> (

let ps1 = (

let uu___434_13708 = ps
in (

let uu____13709 = (FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k t)
in {FStar_Tactics_Types.main_context = uu___434_13708.FStar_Tactics_Types.main_context; FStar_Tactics_Types.main_goal = uu___434_13708.FStar_Tactics_Types.main_goal; FStar_Tactics_Types.all_implicits = uu___434_13708.FStar_Tactics_Types.all_implicits; FStar_Tactics_Types.goals = uu___434_13708.FStar_Tactics_Types.goals; FStar_Tactics_Types.smt_goals = uu___434_13708.FStar_Tactics_Types.smt_goals; FStar_Tactics_Types.depth = uu___434_13708.FStar_Tactics_Types.depth; FStar_Tactics_Types.__dump = uu___434_13708.FStar_Tactics_Types.__dump; FStar_Tactics_Types.psc = uu___434_13708.FStar_Tactics_Types.psc; FStar_Tactics_Types.entry_range = uu___434_13708.FStar_Tactics_Types.entry_range; FStar_Tactics_Types.guard_policy = uu___434_13708.FStar_Tactics_Types.guard_policy; FStar_Tactics_Types.freshness = uu___434_13708.FStar_Tactics_Types.freshness; FStar_Tactics_Types.tac_verb_dbg = uu___434_13708.FStar_Tactics_Types.tac_verb_dbg; FStar_Tactics_Types.local_state = uu____13709}))
in (set ps1))))
in (FStar_All.pipe_left (wrap_err "lset") uu____13701)))


let goal_of_goal_ty : env  ->  FStar_Reflection_Data.typ  ->  (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t) = (fun env typ -> (

let uu____13734 = (FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty" typ.FStar_Syntax_Syntax.pos env typ)
in (match (uu____13734) with
| (u, ctx_uvars, g_u) -> begin
(

let uu____13766 = (FStar_List.hd ctx_uvars)
in (match (uu____13766) with
| (ctx_uvar, uu____13780) -> begin
(

let g = (

let uu____13782 = (FStar_Options.peek ())
in (FStar_Tactics_Types.mk_goal env ctx_uvar uu____13782 false ""))
in ((g), (g_u)))
end))
end)))


let proofstate_of_goal_ty : FStar_Range.range  ->  env  ->  FStar_Reflection_Data.typ  ->  (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term) = (fun rng env typ -> (

let uu____13802 = (goal_of_goal_ty env typ)
in (match (uu____13802) with
| (g, g_u) -> begin
(

let ps = (

let uu____13814 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("TacVerbose")))
in (

let uu____13815 = (FStar_Util.psmap_empty ())
in {FStar_Tactics_Types.main_context = env; FStar_Tactics_Types.main_goal = g; FStar_Tactics_Types.all_implicits = g_u.FStar_TypeChecker_Env.implicits; FStar_Tactics_Types.goals = (g)::[]; FStar_Tactics_Types.smt_goals = []; FStar_Tactics_Types.depth = (Prims.parse_int "0"); FStar_Tactics_Types.__dump = (fun ps msg -> (dump_proofstate ps msg)); FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc; FStar_Tactics_Types.entry_range = rng; FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT; FStar_Tactics_Types.freshness = (Prims.parse_int "0"); FStar_Tactics_Types.tac_verb_dbg = uu____13814; FStar_Tactics_Types.local_state = uu____13815}))
in (

let uu____13822 = (FStar_Tactics_Types.goal_witness g)
in ((ps), (uu____13822))))
end)))




