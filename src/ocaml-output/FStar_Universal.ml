
open Prims
# 37 "FStar.Universal.fst"
let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> (m.FStar_Syntax_Syntax.is_interface, m.FStar_Syntax_Syntax.name))

# 39 "FStar.Universal.fst"
let parse : FStar_Parser_Env.env  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env fn -> (
# 46 "FStar.Universal.fst"
let ast = (FStar_Parser_Driver.parse_file fn)
in (FStar_Parser_ToSyntax.desugar_file env ast)))

# 47 "FStar.Universal.fst"
let tc_prims : Prims.unit  ->  (FStar_Syntax_Syntax.modul * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _79_5 -> (match (()) with
| () -> begin
(
# 56 "FStar.Universal.fst"
let solver = if (FStar_ST.read FStar_Options.verify) then begin
FStar_SMTEncoding_Encode.solver
end else begin
FStar_SMTEncoding_Encode.dummy
end
in (
# 57 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_Tc.type_of solver FStar_Syntax_Const.prims_lid)
in (
# 58 "FStar.Universal.fst"
let _79_8 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env)
in (
# 59 "FStar.Universal.fst"
let p = (FStar_Options.prims ())
in (
# 60 "FStar.Universal.fst"
let _79_13 = (let _160_9 = (FStar_Parser_Env.empty_env ())
in (parse _160_9 p))
in (match (_79_13) with
| (dsenv, prims_mod) -> begin
(
# 61 "FStar.Universal.fst"
let _79_16 = (let _160_10 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _160_10))
in (match (_79_16) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))

# 62 "FStar.Universal.fst"
let tc_one_file : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env fn -> (
# 70 "FStar.Universal.fst"
let _79_22 = (parse dsenv fn)
in (match (_79_22) with
| (dsenv, fmods) -> begin
(
# 71 "FStar.Universal.fst"
let _79_32 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _79_25 m -> (match (_79_25) with
| (env, all_mods) -> begin
(
# 73 "FStar.Universal.fst"
let _79_29 = (FStar_TypeChecker_Tc.check_module env m)
in (match (_79_29) with
| (m, env) -> begin
(env, (m)::all_mods)
end))
end)) (env, [])))
in (match (_79_32) with
| (env, all_mods) -> begin
((FStar_List.rev all_mods), dsenv, env)
end))
end)))

# 75 "FStar.Universal.fst"
let batch_mode_tc_no_prims : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (
# 81 "FStar.Universal.fst"
let _79_50 = (FStar_All.pipe_right filenames (FStar_List.fold_left (fun _79_39 f -> (match (_79_39) with
| (all_mods, dsenv, env) -> begin
(
# 83 "FStar.Universal.fst"
let _79_41 = (FStar_Syntax_Syntax.reset_gensym ())
in (
# 84 "FStar.Universal.fst"
let _79_46 = (tc_one_file dsenv env f)
in (match (_79_46) with
| (ms, dsenv, env) -> begin
((FStar_List.append all_mods ms), dsenv, env)
end)))
end)) ([], dsenv, env)))
in (match (_79_50) with
| (all_mods, dsenv, env) -> begin
(
# 87 "FStar.Universal.fst"
let _79_51 = if ((FStar_ST.read FStar_Options.interactive) && ((FStar_TypeChecker_Errors.get_err_count ()) = 0)) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end else begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end
in (all_mods, dsenv, env))
end)))

# 90 "FStar.Universal.fst"
let batch_mode_tc : Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (
# 93 "FStar.Universal.fst"
let _79_57 = (tc_prims ())
in (match (_79_57) with
| (prims_mod, dsenv, env) -> begin
(
# 94 "FStar.Universal.fst"
let _79_60 = (FStar_Dependences.find_deps_if_needed filenames)
in (match (_79_60) with
| (filenames, admit_fsi) -> begin
(
# 95 "FStar.Universal.fst"
let _79_64 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_79_64) with
| (all_mods, dsenv, env) -> begin
((prims_mod)::all_mods, dsenv, env)
end))
end))
end)))

# 96 "FStar.Universal.fst"
let tc_one_fragment : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul Prims.option * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) Prims.option = (fun curmod dsenv env frag -> (FStar_All.try_with (fun _79_70 -> (match (()) with
| () -> begin
(match ((FStar_Parser_Driver.parse_fragment frag)) with
| FStar_Parser_Driver.Empty -> begin
Some ((curmod, dsenv, env))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(
# 108 "FStar.Universal.fst"
let _79_90 = (FStar_Parser_ToSyntax.desugar_partial_modul curmod dsenv ast_modul)
in (match (_79_90) with
| (dsenv, modul) -> begin
(
# 109 "FStar.Universal.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (_79_93) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (
# 112 "FStar.Universal.fst"
let _79_100 = (FStar_TypeChecker_Tc.tc_partial_modul env modul)
in (match (_79_100) with
| (modul, _79_98, env) -> begin
Some ((Some (modul), dsenv, env))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(
# 116 "FStar.Universal.fst"
let _79_105 = (FStar_Parser_ToSyntax.desugar_decls dsenv ast_decls)
in (match (_79_105) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(
# 118 "FStar.Universal.fst"
let _79_107 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit 1))
end
| Some (modul) -> begin
(
# 120 "FStar.Universal.fst"
let _79_115 = (FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
in (match (_79_115) with
| (modul, _79_113, env) -> begin
Some ((Some (modul), dsenv, env))
end))
end)
end))
end)
end)) (fun _79_69 -> (match (_79_69) with
| FStar_Syntax_Syntax.Error (msg, r) -> begin
(
# 125 "FStar.Universal.fst"
let _79_76 = (FStar_TypeChecker_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) -> begin
(
# 128 "FStar.Universal.fst"
let _79_80 = (FStar_TypeChecker_Errors.add_errors env (((msg, FStar_Range.dummyRange))::[]))
in None)
end
| e -> begin
(Prims.raise e)
end))))

# 130 "FStar.Universal.fst"
let interactive_tc : ((FStar_Parser_Env.env * FStar_TypeChecker_Env.env), FStar_Syntax_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (
# 136 "FStar.Universal.fst"
let pop = (fun _79_119 msg -> (match (_79_119) with
| (dsenv, env) -> begin
(
# 137 "FStar.Universal.fst"
let _79_121 = (let _160_43 = (FStar_Parser_Env.pop dsenv)
in (FStar_All.pipe_right _160_43 Prims.ignore))
in (
# 138 "FStar.Universal.fst"
let _79_123 = (let _160_44 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right _160_44 Prims.ignore))
in (
# 139 "FStar.Universal.fst"
let _79_125 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _160_45 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _160_45 Prims.ignore)))))
end))
in (
# 142 "FStar.Universal.fst"
let push = (fun _79_130 msg -> (match (_79_130) with
| (dsenv, env) -> begin
(
# 143 "FStar.Universal.fst"
let dsenv = (FStar_Parser_Env.push dsenv)
in (
# 144 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.push env msg)
in (dsenv, env)))
end))
in (
# 147 "FStar.Universal.fst"
let mark = (fun _79_137 -> (match (_79_137) with
| (dsenv, env) -> begin
(
# 148 "FStar.Universal.fst"
let dsenv = (FStar_Parser_Env.mark dsenv)
in (
# 149 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.mark env)
in (dsenv, env)))
end))
in (
# 152 "FStar.Universal.fst"
let reset_mark = (fun _79_143 -> (match (_79_143) with
| (dsenv, env) -> begin
(
# 153 "FStar.Universal.fst"
let dsenv = (FStar_Parser_Env.reset_mark dsenv)
in (
# 154 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.reset_mark env)
in (dsenv, env)))
end))
in (
# 157 "FStar.Universal.fst"
let commit_mark = (fun _79_149 -> (match (_79_149) with
| (dsenv, env) -> begin
(
# 158 "FStar.Universal.fst"
let dsenv = (FStar_Parser_Env.commit_mark dsenv)
in (
# 159 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.commit_mark env)
in (dsenv, env)))
end))
in (
# 162 "FStar.Universal.fst"
let check_frag = (fun _79_155 curmod text -> (match (_79_155) with
| (dsenv, env) -> begin
(match ((tc_one_fragment curmod dsenv env text)) with
| Some (m, dsenv, env) -> begin
(let _160_63 = (let _160_62 = (FStar_TypeChecker_Errors.get_err_count ())
in (m, (dsenv, env), _160_62))
in Some (_160_63))
end
| _79_164 -> begin
None
end)
end))
in (
# 168 "FStar.Universal.fst"
let report_fail = (fun _79_166 -> (match (()) with
| () -> begin
(
# 169 "FStar.Universal.fst"
let _79_167 = (let _160_66 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _160_66 Prims.ignore))
in (FStar_ST.op_Colon_Equals FStar_TypeChecker_Errors.num_errs 0))
end))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail})))))))




