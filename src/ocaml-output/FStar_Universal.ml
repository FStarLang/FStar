
open Prims

let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


let parse : FStar_Parser_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env pre_fn fn -> (

let _95_8 = (FStar_Parser_Driver.parse_file fn)
in (match (_95_8) with
| (ast, _95_7) -> begin
(

let ast = (match (pre_fn) with
| None -> begin
ast
end
| Some (pre_fn) -> begin
(

let _95_15 = (FStar_Parser_Driver.parse_file pre_fn)
in (match (_95_15) with
| (pre_ast, _95_14) -> begin
(match (((pre_ast), (ast))) with
| ((FStar_Parser_AST.Interface (lid1, decls1, _95_19))::[], (FStar_Parser_AST.Module (lid2, decls2))::[]) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(let _193_11 = (let _193_10 = (let _193_9 = (FStar_Parser_Interleave.interleave decls1 decls2)
in ((lid1), (_193_9)))
in FStar_Parser_AST.Module (_193_10))
in (_193_11)::[])
end
| _95_30 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("mismatch between pre-module and module\n")))
end)
end))
end)
in (FStar_Parser_ToSyntax.desugar_file env ast))
end)))


let tc_prims : Prims.unit  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _95_32 -> (match (()) with
| () -> begin
(

let solver = if (FStar_Options.lax ()) then begin
FStar_SMTEncoding_Solver.dummy
end else begin
FStar_SMTEncoding_Solver.solver
end
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of solver FStar_Syntax_Const.prims_lid)
in (

let _95_35 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env)
in (

let prims_filename = (FStar_Options.prims ())
in (

let _95_40 = (let _193_14 = (FStar_Parser_Env.empty_env ())
in (parse _193_14 None prims_filename))
in (match (_95_40) with
| (dsenv, prims_mod) -> begin
(

let _95_46 = (FStar_Util.record_time (fun _95_41 -> (match (()) with
| () -> begin
(let _193_16 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _193_16))
end)))
in (match (_95_46) with
| ((prims_mod, env), elapsed_time) -> begin
((((prims_mod), (elapsed_time))), (dsenv), (env))
end))
end))))))
end))


let tc_one_fragment : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul Prims.option * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) Prims.option = (fun curmod dsenv env frag -> try
(match (()) with
| () -> begin
(match ((FStar_Parser_Driver.parse_fragment frag)) with
| FStar_Parser_Driver.Empty -> begin
Some (((curmod), (dsenv), (env)))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let _95_72 = (FStar_Parser_ToSyntax.desugar_partial_modul curmod dsenv ast_modul)
in (match (_95_72) with
| (dsenv, modul) -> begin
(

let env = (match (curmod) with
| None -> begin
env
end
| Some (_95_75) -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (

let _95_82 = (FStar_TypeChecker_Tc.tc_partial_modul env modul)
in (match (_95_82) with
| (modul, _95_80, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let _95_87 = (FStar_Parser_ToSyntax.desugar_decls dsenv ast_decls)
in (match (_95_87) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(

let _95_89 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit (Prims.parse_int "1")))
end
| Some (modul) -> begin
(

let _95_97 = (FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
in (match (_95_97) with
| (modul, _95_95, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end))
end)
end))
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _95_58 = (FStar_TypeChecker_Errors.add_errors env ((((msg), (r)))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _95_62 = (FStar_TypeChecker_Errors.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]))
in None)
end
| e when (not ((FStar_Options.trace_error ()))) -> begin
(Prims.raise e)
end)


let pop_context : (FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  Prims.unit = (fun _95_100 msg -> (match (_95_100) with
| (dsenv, env) -> begin
(

let _95_102 = (let _193_31 = (FStar_Parser_Env.pop dsenv)
in (FStar_All.pipe_right _193_31 Prims.ignore))
in (

let _95_104 = (let _193_32 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right _193_32 Prims.ignore))
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())))
end))


let push_context : (FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _95_108 msg -> (match (_95_108) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.push dsenv)
in (

let env = (FStar_TypeChecker_Env.push env msg)
in ((dsenv), (env))))
end))


let interactive_tc : ((FStar_Parser_Env.env * FStar_TypeChecker_Env.env), FStar_Syntax_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (

let pop = (fun _95_115 msg -> (match (_95_115) with
| (dsenv, env) -> begin
(

let _95_117 = (pop_context ((dsenv), (env)) msg)
in (FStar_Options.pop ()))
end))
in (

let push = (fun _95_122 msg -> (match (_95_122) with
| (dsenv, env) -> begin
(

let res = (push_context ((dsenv), (env)) msg)
in (

let _95_125 = (FStar_Options.push ())
in res))
end))
in (

let mark = (fun _95_130 -> (match (_95_130) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.mark dsenv)
in (

let env = (FStar_TypeChecker_Env.mark env)
in (

let _95_133 = (FStar_Options.push ())
in ((dsenv), (env)))))
end))
in (

let reset_mark = (fun _95_138 -> (match (_95_138) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.reset_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.reset_mark env)
in (

let _95_141 = (FStar_Options.pop ())
in ((dsenv), (env)))))
end))
in (

let commit_mark = (fun _95_146 -> (match (_95_146) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.commit_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.commit_mark env)
in ((dsenv), (env))))
end))
in (

let check_frag = (fun _95_152 curmod text -> (match (_95_152) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(match ((tc_one_fragment curmod dsenv env text)) with
| Some (m, dsenv, env) -> begin
(let _193_59 = (let _193_58 = (FStar_TypeChecker_Errors.get_err_count ())
in ((m), (((dsenv), (env))), (_193_58)))
in Some (_193_59))
end
| _95_176 -> begin
None
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _95_162 = (FStar_TypeChecker_Errors.add_errors env ((((msg), (r)))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _95_166 = (let _193_63 = (let _193_62 = (let _193_61 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_193_61)))
in (_193_62)::[])
in (FStar_TypeChecker_Errors.add_errors env _193_63))
in None)
end
end))
in (

let report_fail = (fun _95_178 -> (match (()) with
| () -> begin
(

let _95_179 = (let _193_66 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _193_66 Prims.ignore))
in (FStar_ST.op_Colon_Equals FStar_TypeChecker_Errors.num_errs (Prims.parse_int "0")))
end))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail})))))))


let tc_one_file : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let _95_187 = (parse dsenv pre_fn fn)
in (match (_95_187) with
| (dsenv, fmods) -> begin
(

let check_mods = (fun _95_189 -> (match (()) with
| () -> begin
(

let _95_202 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _95_192 m -> (match (_95_192) with
| (env, all_mods) -> begin
(

let _95_199 = (FStar_Util.record_time (fun _95_194 -> (match (()) with
| () -> begin
(FStar_TypeChecker_Tc.check_module env m)
end)))
in (match (_95_199) with
| ((m, env), elapsed_ms) -> begin
((env), ((((m), (elapsed_ms)))::all_mods))
end))
end)) ((env), ([]))))
in (match (_95_202) with
| (env, all_mods) -> begin
(((FStar_List.rev all_mods)), (dsenv), (env))
end))
end))
in (match (fmods) with
| (m)::[] when ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) -> begin
(FStar_SMTEncoding_Solver.with_hints_db fn check_mods)
end
| _95_206 -> begin
(check_mods ())
end))
end)))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && ((FStar_Util.get_file_extension intf) = "fsti")) && ((FStar_Util.get_file_extension impl) = "fst")))))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun acc remaining -> (

let move = (fun intf impl remaining -> (

let _95_217 = (FStar_Syntax_Syntax.reset_gensym ())
in (

let _95_222 = acc
in (match (_95_222) with
| (all_mods, dsenv, env) -> begin
(

let _95_247 = (match (intf) with
| None -> begin
(tc_one_file dsenv env None impl)
end
| Some (_95_225) when ((FStar_Options.codegen ()) <> None) -> begin
(

let _95_227 = if (not ((FStar_Options.lax ()))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")))
end else begin
()
end
in (tc_one_file dsenv env intf impl))
end
| Some (iname) -> begin
(

let _95_231 = if (FStar_Options.debug_any ()) then begin
(FStar_Util.print1 "Interleaving iface+module: %s\n" iname)
end else begin
()
end
in (

let caption = (Prims.strcat "interface: " iname)
in (

let _95_236 = (push_context ((dsenv), (env)) caption)
in (match (_95_236) with
| (dsenv', env') -> begin
(

let _95_241 = (tc_one_file dsenv' env' intf impl)
in (match (_95_241) with
| (_95_238, dsenv', env') -> begin
(

let _95_242 = (pop_context ((dsenv'), (env')) caption)
in (tc_one_file dsenv env None iname))
end))
end))))
end)
in (match (_95_247) with
| (ms, dsenv, env) -> begin
(

let acc = (((FStar_List.append all_mods ms)), (dsenv), (env))
in (tc_fold_interleave acc remaining))
end))
end))))
in (match (remaining) with
| (intf)::(impl)::remaining when (needs_interleaving intf impl) -> begin
(move (Some (intf)) impl remaining)
end
| (intf_or_impl)::remaining -> begin
(move None intf_or_impl remaining)
end
| [] -> begin
acc
end)))


let batch_mode_tc_no_prims : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let _95_264 = (tc_fold_interleave (([]), (dsenv), (env)) filenames)
in (match (_95_264) with
| (all_mods, dsenv, env) -> begin
(

let _95_265 = if ((FStar_Options.interactive ()) && ((FStar_TypeChecker_Errors.get_err_count ()) = (Prims.parse_int "0"))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end else begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end
in ((all_mods), (dsenv), (env)))
end)))


let batch_mode_tc : FStar_Parser_Dep.verify_mode  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun verify_mode filenames -> (

let _95_272 = (tc_prims ())
in (match (_95_272) with
| (prims_mod, dsenv, env) -> begin
(

let filenames = (FStar_Dependences.find_deps_if_needed verify_mode filenames)
in (

let _95_278 = if ((not ((FStar_Options.explicit_deps ()))) && (FStar_Options.debug_any ())) then begin
(

let _95_274 = (FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.")
in (

let _95_276 = (FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames))
in (let _193_105 = (let _193_104 = (FStar_Options.verify_module ())
in (FStar_String.concat " " _193_104))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" _193_105))))
end else begin
()
end
in (

let _95_283 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_95_283) with
| (all_mods, dsenv, env) -> begin
(((prims_mod)::all_mods), (dsenv), (env))
end))))
end)))




