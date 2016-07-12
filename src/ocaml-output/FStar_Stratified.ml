
open Prims

let module_or_interface_name : FStar_Absyn_Syntax.modul  ->  (Prims.bool * FStar_Absyn_Syntax.lident) = (fun m -> (m.FStar_Absyn_Syntax.is_interface, m.FStar_Absyn_Syntax.name))


let parse : FStar_Parser_DesugarEnv.env  ->  Prims.string  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env fn -> (

let ast = (FStar_Parser_Driver.parse_file fn)
in (FStar_Parser_Desugar.desugar_file env ast)))


let tc_prims : Prims.unit  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun _88_5 -> (match (()) with
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

let _88_8 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.init env)
in (

let p = (FStar_Options.prims ())
in (

let _88_13 = (let _179_9 = (FStar_Parser_DesugarEnv.empty_env ())
in (parse _179_9 p))
in (match (_88_13) with
| (dsenv, prims_mod) -> begin
(

let _88_16 = (let _179_10 = (FStar_List.hd prims_mod)
in (FStar_Tc_Tc.check_module env _179_10))
in (match (_88_16) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))


let tc_one_file : FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun dsenv env fn -> (

let _88_22 = (parse dsenv fn)
in (match (_88_22) with
| (dsenv, fmods) -> begin
(

let _88_32 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _88_25 m -> (match (_88_25) with
| (env, all_mods) -> begin
(

let _88_29 = (FStar_Tc_Tc.check_module env m)
in (match (_88_29) with
| (ms, env) -> begin
(env, (FStar_List.append ms all_mods))
end))
end)) (env, [])))
in (match (_88_32) with
| (env, all_mods) -> begin
((FStar_List.rev all_mods), dsenv, env)
end))
end)))


let batch_mode_tc_no_prims : FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string Prims.list  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun dsenv env filenames -> (

let _88_50 = (FStar_All.pipe_right filenames (FStar_List.fold_left (fun _88_39 f -> (match (_88_39) with
| (all_mods, dsenv, env) -> begin
(

let _88_41 = (FStar_Absyn_Util.reset_gensym ())
in (

let _88_46 = (tc_one_file dsenv env f)
in (match (_88_46) with
| (ms, dsenv, env) -> begin
((FStar_List.append all_mods ms), dsenv, env)
end)))
end)) ([], dsenv, env)))
in (match (_88_50) with
| (all_mods, dsenv, env) -> begin
(

let _88_51 = if ((FStar_Options.interactive ()) && ((FStar_Tc_Errors.get_err_count ()) = 0)) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
end else begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.finish ())
end
in (all_mods, dsenv, env))
end)))


let batch_mode_tc : FStar_Parser_Dep.verify_mode  ->  Prims.string Prims.list  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun verify_mode filenames -> (

let _88_58 = (tc_prims ())
in (match (_88_58) with
| (prims_mod, dsenv, env) -> begin
(

let filenames = (FStar_Dependences.find_deps_if_needed verify_mode filenames)
in (

let _88_63 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_88_63) with
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

let _88_89 = (FStar_Parser_Desugar.desugar_partial_modul curmod dsenv ast_modul)
in (match (_88_89) with
| (dsenv, modul) -> begin
(

let env = (match (curmod) with
| None -> begin
env
end
| Some (_88_92) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (

let _88_97 = (FStar_Tc_Tc.tc_partial_modul env modul)
in (match (_88_97) with
| (modul, env) -> begin
Some ((Some (modul), dsenv, env))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let _88_102 = (FStar_Parser_Desugar.desugar_decls dsenv ast_decls)
in (match (_88_102) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(

let _88_104 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit 1))
end
| Some (modul) -> begin
(

let _88_110 = (FStar_Tc_Tc.tc_more_partial_modul env modul decls)
in (match (_88_110) with
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

let _88_75 = (FStar_Tc_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Absyn_Syntax.Err (msg) -> begin
(

let _88_79 = (FStar_Tc_Errors.add_errors env (((msg, FStar_Range.dummyRange))::[]))
in None)
end
| e -> begin
(Prims.raise e)
end)


let interactive_tc : ((FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env), FStar_Absyn_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (

let pop = (fun _88_114 msg -> (match (_88_114) with
| (dsenv, env) -> begin
(

let _88_116 = (let _179_45 = (FStar_Parser_DesugarEnv.pop dsenv)
in (FStar_All.pipe_right _179_45 Prims.ignore))
in (

let _88_118 = (let _179_46 = (FStar_Tc_Env.pop env msg)
in (FStar_All.pipe_right _179_46 Prims.ignore))
in (

let _88_120 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (FStar_Options.pop ()))))
end))
in (

let push = (fun _88_125 msg -> (match (_88_125) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_DesugarEnv.push dsenv)
in (

let env = (FStar_Tc_Env.push env msg)
in (

let _88_129 = (FStar_Options.push ())
in (dsenv, env))))
end))
in (

let mark = (fun _88_134 -> (match (_88_134) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_DesugarEnv.mark dsenv)
in (

let env = (FStar_Tc_Env.mark env)
in (

let _88_137 = (FStar_Options.push ())
in (dsenv, env))))
end))
in (

let reset_mark = (fun _88_142 -> (match (_88_142) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_DesugarEnv.reset_mark dsenv)
in (

let env = (FStar_Tc_Env.reset_mark env)
in (

let _88_145 = (FStar_Options.pop ())
in (dsenv, env))))
end))
in (

let commit_mark = (fun _88_150 -> (match (_88_150) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_DesugarEnv.commit_mark dsenv)
in (

let env = (FStar_Tc_Env.commit_mark env)
in (dsenv, env)))
end))
in (

let check_frag = (fun _88_156 curmod text -> (match (_88_156) with
| (dsenv, env) -> begin
(match ((tc_one_fragment curmod dsenv env text)) with
| Some (m, dsenv, env) -> begin
(let _179_64 = (let _179_63 = (FStar_Tc_Errors.get_err_count ())
in (m, (dsenv, env), _179_63))
in Some (_179_64))
end
| _88_165 -> begin
None
end)
end))
in (

let report_fail = (fun _88_167 -> (match (()) with
| () -> begin
(

let _88_168 = (let _179_67 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _179_67 Prims.ignore))
in (FStar_ST.op_Colon_Equals FStar_Tc_Errors.num_errs 0))
end))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail})))))))




