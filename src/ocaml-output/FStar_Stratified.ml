
open Prims

let module_or_interface_name : FStar_Absyn_Syntax.modul  ->  (Prims.bool * FStar_Absyn_Syntax.lident) = (fun m -> ((m.FStar_Absyn_Syntax.is_interface), (m.FStar_Absyn_Syntax.name)))


let parse : FStar_Parser_DesugarEnv.env  ->  Prims.string  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env fn -> (

let _94_7 = (FStar_Parser_Driver.parse_file fn)
in (match (_94_7) with
| (ast, _94_6) -> begin
(FStar_Parser_Desugar.desugar_file env ast)
end)))


let tc_prims : Prims.unit  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun _94_8 -> (match (()) with
| () -> begin
(

let solver = if (FStar_Options.lax ()) then begin
FStar_ToSMT_Encode.dummy
end else begin
FStar_ToSMT_Encode.solver
end
in (

let env = (FStar_Tc_Env.initial_env solver FStar_Absyn_Const.prims_lid)
in (

let _94_11 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.init env)
in (

let p = (FStar_Options.prims ())
in (

let _94_16 = (let _192_9 = (FStar_Parser_DesugarEnv.empty_env ())
in (parse _192_9 p))
in (match (_94_16) with
| (dsenv, prims_mod) -> begin
(

let _94_19 = (let _192_10 = (FStar_List.hd prims_mod)
in (FStar_Tc_Tc.check_module env _192_10))
in (match (_94_19) with
| (prims_mod, env) -> begin
((prims_mod), (dsenv), (env))
end))
end))))))
end))


let tc_one_file : FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun dsenv env fn -> (

let _94_25 = (parse dsenv fn)
in (match (_94_25) with
| (dsenv, fmods) -> begin
(

let _94_35 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _94_28 m -> (match (_94_28) with
| (env, all_mods) -> begin
(

let _94_32 = (FStar_Tc_Tc.check_module env m)
in (match (_94_32) with
| (ms, env) -> begin
((env), ((FStar_List.append ms all_mods)))
end))
end)) ((env), ([]))))
in (match (_94_35) with
| (env, all_mods) -> begin
(((FStar_List.rev all_mods)), (dsenv), (env))
end))
end)))


let batch_mode_tc_no_prims : FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string Prims.list  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun dsenv env filenames -> (

let _94_53 = (FStar_All.pipe_right filenames (FStar_List.fold_left (fun _94_42 f -> (match (_94_42) with
| (all_mods, dsenv, env) -> begin
(

let _94_44 = (FStar_Absyn_Util.reset_gensym ())
in (

let _94_49 = (tc_one_file dsenv env f)
in (match (_94_49) with
| (ms, dsenv, env) -> begin
(((FStar_List.append all_mods ms)), (dsenv), (env))
end)))
end)) (([]), (dsenv), (env))))
in (match (_94_53) with
| (all_mods, dsenv, env) -> begin
(

let _94_54 = if ((FStar_Options.interactive ()) && ((FStar_Tc_Errors.get_err_count ()) = (Prims.parse_int "0"))) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
end else begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.finish ())
end
in ((all_mods), (dsenv), (env)))
end)))


let batch_mode_tc : FStar_Parser_Dep.verify_mode  ->  Prims.string Prims.list  ->  ((FStar_Absyn_Syntax.modul * Prims.int) Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun verify_mode filenames -> (

let _94_61 = (tc_prims ())
in (match (_94_61) with
| (prims_mod, dsenv, env) -> begin
(

let filenames = (FStar_Dependences.find_deps_if_needed verify_mode filenames)
in (

let _94_66 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_94_66) with
| (all_mods, dsenv, env) -> begin
(

let all_mods = (FStar_All.pipe_right (FStar_List.append prims_mod all_mods) (FStar_List.map (fun x -> ((x), ((~- ((Prims.parse_int "1"))))))))
in ((all_mods), (dsenv), (env)))
end)))
end)))


let tc_one_fragment : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Absyn_Syntax.modul Prims.option * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) Prims.option = (fun curmod dsenv env frag -> try
(match (()) with
| () -> begin
(match ((FStar_Parser_Driver.parse_fragment frag)) with
| FStar_Parser_Driver.Empty -> begin
Some (((curmod), (dsenv), (env)))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let _94_94 = (FStar_Parser_Desugar.desugar_partial_modul curmod dsenv ast_modul)
in (match (_94_94) with
| (dsenv, modul) -> begin
(

let env = (match (curmod) with
| None -> begin
env
end
| Some (_94_97) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (

let _94_102 = (FStar_Tc_Tc.tc_partial_modul env modul)
in (match (_94_102) with
| (modul, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let _94_107 = (FStar_Parser_Desugar.desugar_decls dsenv ast_decls)
in (match (_94_107) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(

let _94_109 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit (Prims.parse_int "1")))
end
| Some (modul) -> begin
(

let _94_115 = (FStar_Tc_Tc.tc_more_partial_modul env modul decls)
in (match (_94_115) with
| (modul, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end))
end)
end))
end)
end)
with
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(

let _94_80 = (FStar_Tc_Errors.add_errors env ((((msg), (r)))::[]))
in None)
end
| FStar_Absyn_Syntax.Err (msg) -> begin
(

let _94_84 = (FStar_Tc_Errors.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]))
in None)
end
| e -> begin
(Prims.raise e)
end)


let interactive_tc : ((FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env), FStar_Absyn_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (

let pop = (fun _94_119 msg -> (match (_94_119) with
| (dsenv, env) -> begin
(

let _94_121 = (let _192_46 = (FStar_Parser_DesugarEnv.pop dsenv)
in (FStar_All.pipe_right _192_46 Prims.ignore))
in (

let _94_123 = (let _192_47 = (FStar_Tc_Env.pop env msg)
in (FStar_All.pipe_right _192_47 Prims.ignore))
in (

let _94_125 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (FStar_Options.pop ()))))
end))
in (

let push = (fun _94_130 lax restore_cmd_line_options msg -> (match (_94_130) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_DesugarEnv.push dsenv)
in (

let env = (FStar_Tc_Env.push env msg)
in (

let _94_136 = (FStar_Options.push ())
in ((dsenv), (env)))))
end))
in (

let mark = (fun _94_141 -> (match (_94_141) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_DesugarEnv.mark dsenv)
in (

let env = (FStar_Tc_Env.mark env)
in (

let _94_144 = (FStar_Options.push ())
in ((dsenv), (env)))))
end))
in (

let reset_mark = (fun _94_149 -> (match (_94_149) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_DesugarEnv.reset_mark dsenv)
in (

let env = (FStar_Tc_Env.reset_mark env)
in (

let _94_152 = (FStar_Options.pop ())
in ((dsenv), (env)))))
end))
in (

let commit_mark = (fun _94_157 -> (match (_94_157) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_DesugarEnv.commit_mark dsenv)
in (

let env = (FStar_Tc_Env.commit_mark env)
in ((dsenv), (env))))
end))
in (

let check_frag = (fun _94_163 curmod frag -> (match (_94_163) with
| (dsenv, env) -> begin
(match ((tc_one_fragment curmod dsenv env frag)) with
| Some (m, dsenv, env) -> begin
(let _192_69 = (let _192_68 = (FStar_Tc_Errors.get_err_count ())
in ((m), (((dsenv), (env))), (_192_68)))
in Some (_192_69))
end
| _94_172 -> begin
None
end)
end))
in (

let report_fail = (fun _94_174 -> (match (()) with
| () -> begin
(

let _94_175 = (let _192_72 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _192_72 Prims.ignore))
in (FStar_ST.op_Colon_Equals FStar_Tc_Errors.num_errs (Prims.parse_int "0")))
end))
in (

let tc_prims_interactive = (fun _94_178 -> (match (()) with
| () -> begin
(

let _94_183 = (tc_prims ())
in (match (_94_183) with
| (_94_180, dsenv, env) -> begin
((dsenv), (env))
end))
end))
in (

let tc_one_file_interactive = (fun remaining uenv -> (match (remaining) with
| (file)::remaining -> begin
(

let _94_194 = (tc_one_file (Prims.fst uenv) (Prims.snd uenv) file)
in (match (_94_194) with
| (_94_191, dsenv, env) -> begin
((((None), (file))), (((dsenv), (env))), (None), (remaining))
end))
end
| [] -> begin
(failwith "Impossible")
end))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail; FStar_Interactive.tc_prims = tc_prims_interactive; FStar_Interactive.tc_one_file = tc_one_file_interactive; FStar_Interactive.cleanup = (fun _94_196 -> ())})))))))))




