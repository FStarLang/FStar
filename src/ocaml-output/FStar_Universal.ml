
open Prims
# 37 "FStar.Universal.fst"
let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> (m.FStar_Syntax_Syntax.is_interface, m.FStar_Syntax_Syntax.name))

# 39 "FStar.Universal.fst"
let parse : FStar_Parser_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env pre_fn fn -> (
# 46 "FStar.Universal.fst"
let ast = (FStar_Parser_Driver.parse_file fn)
in (
# 47 "FStar.Universal.fst"
let _77_27 = (match (pre_fn) with
| None -> begin
(ast, false)
end
| Some (pre_fn) -> begin
(
# 51 "FStar.Universal.fst"
let pre_ast = (FStar_Parser_Driver.parse_file pre_fn)
in (match ((pre_ast, ast)) with
| (FStar_Parser_AST.Interface (lid1, decls1, _77_13)::[], FStar_Parser_AST.Module (lid2, decls2)::[]) when (FStar_Ident.lid_equals lid1 lid2) -> begin
((FStar_Parser_AST.Module ((lid1, (FStar_List.append decls1 decls2))))::[], true)
end
| _77_24 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("mismatch between pre-module and module\n")))
end))
end)
in (match (_77_27) with
| (ast, needs_interleaving) -> begin
(FStar_Parser_ToSyntax.desugar_file env ast needs_interleaving)
end))))

# 59 "FStar.Universal.fst"
let tc_prims : Prims.unit  ->  (FStar_Syntax_Syntax.modul * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _77_28 -> (match (()) with
| () -> begin
(
# 68 "FStar.Universal.fst"
let solver = if (FStar_ST.read FStar_Options.verify) then begin
FStar_SMTEncoding_Encode.solver
end else begin
FStar_SMTEncoding_Encode.dummy
end
in (
# 69 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_Tc.type_of solver FStar_Syntax_Const.prims_lid)
in (
# 70 "FStar.Universal.fst"
let _77_31 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env)
in (
# 71 "FStar.Universal.fst"
let p = (FStar_Options.prims ())
in (
# 72 "FStar.Universal.fst"
let _77_36 = (let _156_11 = (FStar_Parser_Env.empty_env ())
in (parse _156_11 None p))
in (match (_77_36) with
| (dsenv, prims_mod) -> begin
(
# 73 "FStar.Universal.fst"
let _77_39 = (let _156_12 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _156_12))
in (match (_77_39) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))

# 74 "FStar.Universal.fst"
let tc_one_file : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (
# 82 "FStar.Universal.fst"
let _77_46 = (parse dsenv pre_fn fn)
in (match (_77_46) with
| (dsenv, fmods) -> begin
(
# 83 "FStar.Universal.fst"
let _77_56 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _77_49 m -> (match (_77_49) with
| (env, all_mods) -> begin
(
# 85 "FStar.Universal.fst"
let _77_53 = (FStar_TypeChecker_Tc.check_module env m)
in (match (_77_53) with
| (m, env) -> begin
(env, (m)::all_mods)
end))
end)) (env, [])))
in (match (_77_56) with
| (env, all_mods) -> begin
((FStar_List.rev all_mods), dsenv, env)
end))
end)))

# 87 "FStar.Universal.fst"
let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (
# 93 "FStar.Universal.fst"
let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (
# 94 "FStar.Universal.fst"
let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && ((FStar_Util.get_file_extension intf) = "fsti")) && ((FStar_Util.get_file_extension impl) = "fst")))))

# 96 "FStar.Universal.fst"
let rec tc_fold_interleave : (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun acc remaining -> (
# 99 "FStar.Universal.fst"
let move = (fun intf impl remaining -> (
# 100 "FStar.Universal.fst"
let _77_70 = acc
in (match (_77_70) with
| (all_mods, dsenv, env) -> begin
(
# 101 "FStar.Universal.fst"
let _77_71 = (FStar_Syntax_Syntax.reset_gensym ())
in (
# 102 "FStar.Universal.fst"
let _77_76 = (tc_one_file dsenv env intf impl)
in (match (_77_76) with
| (ms, dsenv, env) -> begin
(
# 103 "FStar.Universal.fst"
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

# 113 "FStar.Universal.fst"
let batch_mode_tc_no_prims : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (
# 119 "FStar.Universal.fst"
let _77_93 = (tc_fold_interleave ([], dsenv, env) filenames)
in (match (_77_93) with
| (all_mods, dsenv, env) -> begin
(
# 120 "FStar.Universal.fst"
let _77_94 = if ((FStar_ST.read FStar_Options.interactive) && ((FStar_TypeChecker_Errors.get_err_count ()) = 0)) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end else begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end
in (all_mods, dsenv, env))
end)))

# 123 "FStar.Universal.fst"
let batch_mode_tc : Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (
# 126 "FStar.Universal.fst"
let _77_100 = (tc_prims ())
in (match (_77_100) with
| (prims_mod, dsenv, env) -> begin
(
# 127 "FStar.Universal.fst"
let _77_103 = (FStar_Dependences.find_deps_if_needed filenames)
in (match (_77_103) with
| (filenames, admit_fsi) -> begin
(
# 128 "FStar.Universal.fst"
let _77_107 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_77_107) with
| (all_mods, dsenv, env) -> begin
((prims_mod)::all_mods, dsenv, env)
end))
end))
end)))

# 129 "FStar.Universal.fst"
let tc_one_fragment : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul Prims.option * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) Prims.option = (fun curmod dsenv env frag -> try
(match (()) with
| () -> begin
(match ((FStar_Parser_Driver.parse_fragment frag)) with
| FStar_Parser_Driver.Empty -> begin
Some ((curmod, dsenv, env))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(
# 141 "FStar.Universal.fst"
let _77_133 = (FStar_Parser_ToSyntax.desugar_partial_modul curmod dsenv ast_modul)
in (match (_77_133) with
| (dsenv, modul) -> begin
(
# 142 "FStar.Universal.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (_77_136) -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (
# 145 "FStar.Universal.fst"
let _77_143 = (FStar_TypeChecker_Tc.tc_partial_modul env modul)
in (match (_77_143) with
| (modul, _77_141, env) -> begin
Some ((Some (modul), dsenv, env))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(
# 149 "FStar.Universal.fst"
let _77_148 = (FStar_Parser_ToSyntax.desugar_decls dsenv ast_decls)
in (match (_77_148) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(
# 151 "FStar.Universal.fst"
let _77_150 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit 1))
end
| Some (modul) -> begin
(
# 153 "FStar.Universal.fst"
let _77_158 = (FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
in (match (_77_158) with
| (modul, _77_156, env) -> begin
Some ((Some (modul), dsenv, env))
end))
end)
end))
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) -> begin
(
# 158 "FStar.Universal.fst"
let _77_119 = (FStar_TypeChecker_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) -> begin
(
# 161 "FStar.Universal.fst"
let _77_123 = (FStar_TypeChecker_Errors.add_errors env (((msg, FStar_Range.dummyRange))::[]))
in None)
end
| e -> begin
(Prims.raise e)
end)

# 163 "FStar.Universal.fst"
let interactive_tc : ((FStar_Parser_Env.env * FStar_TypeChecker_Env.env), FStar_Syntax_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (
# 169 "FStar.Universal.fst"
let pop = (fun _77_162 msg -> (match (_77_162) with
| (dsenv, env) -> begin
(
# 170 "FStar.Universal.fst"
let _77_164 = (let _156_59 = (FStar_Parser_Env.pop dsenv)
in (FStar_All.pipe_right _156_59 Prims.ignore))
in (
# 171 "FStar.Universal.fst"
let _77_166 = (let _156_60 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right _156_60 Prims.ignore))
in (
# 172 "FStar.Universal.fst"
let _77_168 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _156_61 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _156_61 Prims.ignore)))))
end))
in (
# 175 "FStar.Universal.fst"
let push = (fun _77_173 msg -> (match (_77_173) with
| (dsenv, env) -> begin
(
# 176 "FStar.Universal.fst"
let dsenv = (FStar_Parser_Env.push dsenv)
in (
# 177 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.push env msg)
in (dsenv, env)))
end))
in (
# 180 "FStar.Universal.fst"
let mark = (fun _77_180 -> (match (_77_180) with
| (dsenv, env) -> begin
(
# 181 "FStar.Universal.fst"
let dsenv = (FStar_Parser_Env.mark dsenv)
in (
# 182 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.mark env)
in (dsenv, env)))
end))
in (
# 185 "FStar.Universal.fst"
let reset_mark = (fun _77_186 -> (match (_77_186) with
| (dsenv, env) -> begin
(
# 186 "FStar.Universal.fst"
let dsenv = (FStar_Parser_Env.reset_mark dsenv)
in (
# 187 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.reset_mark env)
in (dsenv, env)))
end))
in (
# 190 "FStar.Universal.fst"
let commit_mark = (fun _77_192 -> (match (_77_192) with
| (dsenv, env) -> begin
(
# 191 "FStar.Universal.fst"
let dsenv = (FStar_Parser_Env.commit_mark dsenv)
in (
# 192 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.commit_mark env)
in (dsenv, env)))
end))
in (
# 195 "FStar.Universal.fst"
let check_frag = (fun _77_198 curmod text -> (match (_77_198) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(match ((tc_one_fragment curmod dsenv env text)) with
| Some (m, dsenv, env) -> begin
(let _156_80 = (let _156_79 = (FStar_TypeChecker_Errors.get_err_count ())
in (m, (dsenv, env), _156_79))
in Some (_156_80))
end
| _77_222 -> begin
None
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) -> begin
(
# 203 "FStar.Universal.fst"
let _77_208 = (FStar_TypeChecker_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) -> begin
(
# 207 "FStar.Universal.fst"
let _77_212 = (let _156_84 = (let _156_83 = (let _156_82 = (FStar_TypeChecker_Env.get_range env)
in (msg, _156_82))
in (_156_83)::[])
in (FStar_TypeChecker_Errors.add_errors env _156_84))
in None)
end
end))
in (
# 210 "FStar.Universal.fst"
let report_fail = (fun _77_224 -> (match (()) with
| () -> begin
(
# 211 "FStar.Universal.fst"
let _77_225 = (let _156_87 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _156_87 Prims.ignore))
in (FStar_ST.op_Colon_Equals FStar_TypeChecker_Errors.num_errs 0))
end))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail})))))))




