
open Prims

let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> (m.FStar_Syntax_Syntax.is_interface, m.FStar_Syntax_Syntax.name))


let parse : FStar_Parser_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env pre_fn fn -> (

let ast = (FStar_Parser_Driver.parse_file fn)
in (

let _87_27 = (match (pre_fn) with
| None -> begin
(ast, false)
end
| Some (pre_fn) -> begin
(

let pre_ast = (FStar_Parser_Driver.parse_file pre_fn)
in (match ((pre_ast, ast)) with
| (FStar_Parser_AST.Interface (lid1, decls1, _87_13)::[], FStar_Parser_AST.Module (lid2, decls2)::[]) when (FStar_Ident.lid_equals lid1 lid2) -> begin
((FStar_Parser_AST.Module ((lid1, (FStar_List.append decls1 decls2))))::[], true)
end
| _87_24 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("mismatch between pre-module and module\n")))
end))
end)
in (match (_87_27) with
| (ast, needs_interleaving) -> begin
(FStar_Parser_ToSyntax.desugar_file env ast needs_interleaving)
end))))


let tc_prims : Prims.unit  ->  (FStar_Syntax_Syntax.modul * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _87_28 -> (match (()) with
| () -> begin
(

let solver = if (FStar_ST.read FStar_Options.verify) then begin
FStar_SMTEncoding_Encode.solver
end else begin
FStar_SMTEncoding_Encode.dummy
end
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_Tc.type_of solver FStar_Syntax_Const.prims_lid)
in (

let _87_31 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env)
in (

let p = (FStar_Options.prims ())
in (

let _87_36 = (let _176_11 = (FStar_Parser_Env.empty_env ())
in (parse _176_11 None p))
in (match (_87_36) with
| (dsenv, prims_mod) -> begin
(

let _87_39 = (let _176_12 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _176_12))
in (match (_87_39) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))


let tc_one_file : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let _87_46 = (parse dsenv pre_fn fn)
in (match (_87_46) with
| (dsenv, fmods) -> begin
(

let _87_56 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _87_49 m -> (match (_87_49) with
| (env, all_mods) -> begin
(

let _87_53 = (FStar_TypeChecker_Tc.check_module env m)
in (match (_87_53) with
| (m, env) -> begin
(env, (m)::all_mods)
end))
end)) (env, [])))
in (match (_87_56) with
| (env, all_mods) -> begin
((FStar_List.rev all_mods), dsenv, env)
end))
end)))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && ((FStar_Util.get_file_extension intf) = "fsti")) && ((FStar_Util.get_file_extension impl) = "fst")))))


let rec tc_fold_interleave : (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun acc remaining -> (

let move = (fun intf impl remaining -> (

let _87_70 = acc
in (match (_87_70) with
| (all_mods, dsenv, env) -> begin
(

let _87_71 = (FStar_Syntax_Syntax.reset_gensym ())
in (

let _87_76 = (tc_one_file dsenv env intf impl)
in (match (_87_76) with
| (ms, dsenv, env) -> begin
(

let acc = ((FStar_List.append all_mods ms), dsenv, env)
in (tc_fold_interleave acc remaining))
end)))
end)))
in (match (remaining) with
| intf::impl::remaining when (needs_interleaving intf impl) -> begin
(move (Some (intf)) impl remaining)
end
| intf_or_impl::remaining -> begin
(move None intf_or_impl remaining)
end
| [] -> begin
acc
end)))


let batch_mode_tc_no_prims : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let _87_93 = (tc_fold_interleave ([], dsenv, env) filenames)
in (match (_87_93) with
| (all_mods, dsenv, env) -> begin
(

let _87_94 = if ((FStar_ST.read FStar_Options.interactive) && ((FStar_TypeChecker_Errors.get_err_count ()) = 0)) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end else begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end
in (all_mods, dsenv, env))
end)))


let batch_mode_tc : Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let _87_100 = (tc_prims ())
in (match (_87_100) with
| (prims_mod, dsenv, env) -> begin
(

let _87_103 = (FStar_Dependences.find_deps_if_needed filenames)
in (match (_87_103) with
| (filenames, admit_fsi) -> begin
(

let _87_107 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_87_107) with
| (all_mods, dsenv, env) -> begin
((prims_mod)::all_mods, dsenv, env)
end))
end))
end)))


let tc_one_fragment : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul Prims.option * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) Prims.option = (fun curmod dsenv env frag -> try
(match (()) with
| () -> begin
(match ((FStar_Parser_Driver.parse_fragment frag)) with
| FStar_Parser_Driver.Empty -> begin
Some ((curmod, dsenv, env))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let _87_133 = (FStar_Parser_ToSyntax.desugar_partial_modul curmod dsenv ast_modul)
in (match (_87_133) with
| (dsenv, modul) -> begin
(

let env = (match (curmod) with
| None -> begin
env
end
| Some (_87_136) -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (

let _87_143 = (FStar_TypeChecker_Tc.tc_partial_modul env modul)
in (match (_87_143) with
| (modul, _87_141, env) -> begin
Some ((Some (modul), dsenv, env))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let _87_148 = (FStar_Parser_ToSyntax.desugar_decls dsenv ast_decls)
in (match (_87_148) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(

let _87_150 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit 1))
end
| Some (modul) -> begin
(

let _87_158 = (FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
in (match (_87_158) with
| (modul, _87_156, env) -> begin
Some ((Some (modul), dsenv, env))
end))
end)
end))
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(

let _87_119 = (FStar_TypeChecker_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(

let _87_123 = (FStar_TypeChecker_Errors.add_errors env (((msg, FStar_Range.dummyRange))::[]))
in None)
end
| e when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(Prims.raise e)
end)


let interactive_tc : ((FStar_Parser_Env.env * FStar_TypeChecker_Env.env), FStar_Syntax_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (

let pop = (fun _87_162 msg -> (match (_87_162) with
| (dsenv, env) -> begin
(

let _87_164 = (let _176_59 = (FStar_Parser_Env.pop dsenv)
in (FStar_All.pipe_right _176_59 Prims.ignore))
in (

let _87_166 = (let _176_60 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right _176_60 Prims.ignore))
in (

let _87_168 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _176_61 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _176_61 Prims.ignore)))))
end))
in (

let push = (fun _87_173 msg -> (match (_87_173) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.push dsenv)
in (

let env = (FStar_TypeChecker_Env.push env msg)
in (dsenv, env)))
end))
in (

let mark = (fun _87_180 -> (match (_87_180) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.mark dsenv)
in (

let env = (FStar_TypeChecker_Env.mark env)
in (dsenv, env)))
end))
in (

let reset_mark = (fun _87_186 -> (match (_87_186) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.reset_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.reset_mark env)
in (dsenv, env)))
end))
in (

let commit_mark = (fun _87_192 -> (match (_87_192) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.commit_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.commit_mark env)
in (dsenv, env)))
end))
in (

let check_frag = (fun _87_198 curmod text -> (match (_87_198) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(match ((tc_one_fragment curmod dsenv env text)) with
| Some (m, dsenv, env) -> begin
(let _176_80 = (let _176_79 = (FStar_TypeChecker_Errors.get_err_count ())
in (m, (dsenv, env), _176_79))
in Some (_176_80))
end
| _87_222 -> begin
None
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(

let _87_208 = (FStar_TypeChecker_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(

let _87_212 = (let _176_84 = (let _176_83 = (let _176_82 = (FStar_TypeChecker_Env.get_range env)
in (msg, _176_82))
in (_176_83)::[])
in (FStar_TypeChecker_Errors.add_errors env _176_84))
in None)
end
end))
in (

let report_fail = (fun _87_224 -> (match (()) with
| () -> begin
(

let _87_225 = (let _176_87 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _176_87 Prims.ignore))
in (FStar_ST.op_Colon_Equals FStar_TypeChecker_Errors.num_errs 0))
end))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail})))))))




