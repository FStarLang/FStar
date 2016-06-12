
open Prims

let module_or_interface_name : FStar_Absyn_Syntax.modul  ->  (Prims.bool * FStar_Absyn_Syntax.lident) = (fun m -> (m.FStar_Absyn_Syntax.is_interface, m.FStar_Absyn_Syntax.name))


let parse : FStar_Parser_DesugarEnv.env  ->  Prims.string  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env fn -> (

let ast = (FStar_Parser_Driver.parse_file fn)
in (FStar_Parser_Desugar.desugar_file env ast)))


let tc_prims : Prims.unit  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun _87_5 -> (match (()) with
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

let _87_8 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.init env)
in (

let p = (FStar_Options.prims ())
in (

let _87_13 = (let _177_9 = (FStar_Parser_DesugarEnv.empty_env ())
in (parse _177_9 p))
in (match (_87_13) with
| (dsenv, prims_mod) -> begin
(

let _87_16 = (let _177_10 = (FStar_List.hd prims_mod)
in (FStar_Tc_Tc.check_module env _177_10))
in (match (_87_16) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))


let tc_one_file : FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun dsenv env fn -> (

let _87_22 = (parse dsenv fn)
in (match (_87_22) with
| (dsenv, fmods) -> begin
(

let _87_32 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _87_25 m -> (match (_87_25) with
| (env, all_mods) -> begin
(

let _87_29 = (FStar_Tc_Tc.check_module env m)
in (match (_87_29) with
| (ms, env) -> begin
(env, (FStar_List.append ms all_mods))
end))
end)) (env, [])))
in (match (_87_32) with
| (env, all_mods) -> begin
((FStar_List.rev all_mods), dsenv, env)
end))
end)))


let batch_mode_tc_no_prims : FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string Prims.list  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun dsenv env filenames -> (

let _87_50 = (FStar_All.pipe_right filenames (FStar_List.fold_left (fun _87_39 f -> (match (_87_39) with
| (all_mods, dsenv, env) -> begin
(

let _87_41 = (FStar_Absyn_Util.reset_gensym ())
in (

let _87_46 = (tc_one_file dsenv env f)
in (match (_87_46) with
| (ms, dsenv, env) -> begin
((FStar_List.append all_mods ms), dsenv, env)
end)))
end)) ([], dsenv, env)))
in (match (_87_50) with
| (all_mods, dsenv, env) -> begin
(

let _87_51 = if ((FStar_Options.interactive ()) && ((FStar_Tc_Errors.get_err_count ()) = 0)) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
end else begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.finish ())
end
in (all_mods, dsenv, env))
end)))


let batch_mode_tc : Prims.string Prims.list  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun filenames -> (

let _87_57 = (tc_prims ())
in (match (_87_57) with
| (prims_mod, dsenv, env) -> begin
(

let filenames = (FStar_Dependences.find_deps_if_needed filenames)
in (

let _87_62 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_87_62) with
| (all_mods, dsenv, env) -> begin
((FStar_List.append prims_mod all_mods), dsenv, env)
end)))
end)))


let tc_one_fragment : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string  ->  (FStar_Absyn_Syntax.modul Prims.option * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) Prims.option = (fun curmod dsenv env frag -> try
(match (()) with
| () -> begin
(match ((FStar_Parser_Driver.parse_fragment frag)) with
| FStar_Parser_Driver.Empty -> begin
Some ((curmod, dsenv, env))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let _87_88 = (FStar_Parser_Desugar.desugar_partial_modul curmod dsenv ast_modul)
in (match (_87_88) with
| (dsenv, modul) -> begin
(

let env = (match (curmod) with
| None -> begin
env
end
| Some (_87_91) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (

let _87_96 = (FStar_Tc_Tc.tc_partial_modul env modul)
in (match (_87_96) with
| (modul, env) -> begin
Some ((Some (modul), dsenv, env))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let _87_101 = (FStar_Parser_Desugar.desugar_decls dsenv ast_decls)
in (match (_87_101) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(

let _87_103 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit 1))
end
| Some (modul) -> begin
(

let _87_109 = (FStar_Tc_Tc.tc_more_partial_modul env modul decls)
in (match (_87_109) with
| (modul, env) -> begin
Some ((Some (modul), dsenv, env))
end))
end)
end))
end)
end)
with
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(

let _87_74 = (FStar_Tc_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Absyn_Syntax.Err (msg) -> begin
(

let _87_78 = (FStar_Tc_Errors.add_errors env (((msg, FStar_Range.dummyRange))::[]))
in None)
end
| e -> begin
(Prims.raise e)
end)


let interactive_tc : ((FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env), FStar_Absyn_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (

let pop = (fun _87_113 msg -> (match (_87_113) with
| (dsenv, env) -> begin
(

let _87_115 = (let _177_43 = (FStar_Parser_DesugarEnv.pop dsenv)
in (FStar_All.pipe_right _177_43 Prims.ignore))
in (

let _87_117 = (let _177_44 = (FStar_Tc_Env.pop env msg)
in (FStar_All.pipe_right _177_44 Prims.ignore))
in (

let _87_119 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (FStar_Options.pop ()))))
end))
in (

let push = (fun _87_124 msg -> (match (_87_124) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_DesugarEnv.push dsenv)
in (

let env = (FStar_Tc_Env.push env msg)
in (

let _87_128 = (FStar_Options.push ())
in (dsenv, env))))
end))
in (

let mark = (fun _87_133 -> (match (_87_133) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_DesugarEnv.mark dsenv)
in (

let env = (FStar_Tc_Env.mark env)
in (

let _87_136 = (FStar_Options.push ())
in (dsenv, env))))
end))
in (

let reset_mark = (fun _87_141 -> (match (_87_141) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_DesugarEnv.reset_mark dsenv)
in (

let env = (FStar_Tc_Env.reset_mark env)
in (

let _87_144 = (FStar_Options.pop ())
in (dsenv, env))))
end))
in (

let commit_mark = (fun _87_149 -> (match (_87_149) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_DesugarEnv.commit_mark dsenv)
in (

let env = (FStar_Tc_Env.commit_mark env)
in (dsenv, env)))
end))
in (

let check_frag = (fun _87_155 curmod text -> (match (_87_155) with
| (dsenv, env) -> begin
(match ((tc_one_fragment curmod dsenv env text)) with
| Some (m, dsenv, env) -> begin
(let _177_62 = (let _177_61 = (FStar_Tc_Errors.get_err_count ())
in (m, (dsenv, env), _177_61))
in Some (_177_62))
end
| _87_164 -> begin
None
end)
end))
in (

let report_fail = (fun _87_166 -> (match (()) with
| () -> begin
(

let _87_167 = (let _177_65 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _177_65 Prims.ignore))
in (FStar_ST.op_Colon_Equals FStar_Tc_Errors.num_errs 0))
end))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail})))))))




