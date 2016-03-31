
open Prims
# 26 "FStar.FStar.fst"
let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun _88_1 -> (match (()) with
| () -> begin
(
# 27 "FStar.FStar.fst"
let file_list = (FStar_Util.mk_ref [])
in (
# 28 "FStar.FStar.fst"
let res = (let _177_6 = (FStar_Options.specs ())
in (FStar_Getopt.parse_cmdline _177_6 (fun i -> (let _177_5 = (let _177_4 = (FStar_ST.read file_list)
in (FStar_List.append _177_4 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list _177_5)))))
in (
# 29 "FStar.FStar.fst"
let _88_8 = (match (res) with
| FStar_Getopt.GoOn -> begin
(let _177_7 = (FStar_Options.set_fstar_home ())
in (Prims.ignore _177_7))
end
| _88_7 -> begin
()
end)
in (let _177_8 = (FStar_ST.read file_list)
in (res, _177_8)))))
end))

# 35 "FStar.FStar.fst"
let cleanup : Prims.unit  ->  Prims.unit = (fun _88_10 -> (match (()) with
| () -> begin
(FStar_Util.kill_all ())
end))

# 38 "FStar.FStar.fst"
let report_errors : Prims.unit  ->  Prims.unit = (fun _88_11 -> (match (()) with
| () -> begin
(
# 39 "FStar.FStar.fst"
let errs = if (FStar_ST.read FStar_Options.universes) then begin
(FStar_TypeChecker_Errors.get_err_count ())
end else begin
(FStar_Tc_Errors.get_err_count ())
end
in if (errs > 0) then begin
(
# 44 "FStar.FStar.fst"
let _88_13 = (let _177_13 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" _177_13))
in (FStar_All.exit 1))
end else begin
()
end)
end))

# 49 "FStar.FStar.fst"
let finished_message : (Prims.bool * FStar_Ident.lident) Prims.list  ->  Prims.unit = (fun fmods -> if (not ((FStar_ST.read FStar_Options.silent))) then begin
(
# 51 "FStar.FStar.fst"
let msg = if (FStar_ST.read FStar_Options.verify) then begin
"Verifying"
end else begin
if (FStar_ST.read FStar_Options.pretype) then begin
"Lax type-checked"
end else begin
"Parsed and desugared"
end
end
in (
# 55 "FStar.FStar.fst"
let _88_21 = (FStar_All.pipe_right fmods (FStar_List.iter (fun _88_19 -> (match (_88_19) with
| (iface, name) -> begin
(
# 56 "FStar.FStar.fst"
let tag = if iface then begin
"i\'face"
end else begin
"module"
end
in if (FStar_Options.should_print_message name.FStar_Ident.str) then begin
(let _177_17 = (FStar_Util.format3 "%s %s: %s\n" msg tag (FStar_Ident.text_of_lid name))
in (FStar_Util.print_string _177_17))
end else begin
()
end)
end))))
in (let _177_19 = (let _177_18 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" _177_18))
in (FStar_Util.print_string _177_19))))
end else begin
()
end)

# 63 "FStar.FStar.fst"
let codegen : ((FStar_Absyn_Syntax.modul Prims.list * FStar_Tc_Env.env), (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env)) FStar_Util.either  ->  Prims.unit = (fun uf_mods_env -> if (((FStar_ST.read FStar_Options.codegen) = Some ("OCaml")) || ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp"))) then begin
(
# 67 "FStar.FStar.fst"
let mllibs = (match (uf_mods_env) with
| FStar_Util.Inl (fmods, env) -> begin
(let _177_23 = (let _177_22 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _177_22 fmods))
in (FStar_All.pipe_left Prims.snd _177_23))
end
| FStar_Util.Inr (umods, env) -> begin
(let _177_25 = (let _177_24 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract _177_24 umods))
in (FStar_All.pipe_left Prims.snd _177_25))
end)
in (
# 70 "FStar.FStar.fst"
let mllibs = (FStar_List.flatten mllibs)
in (
# 71 "FStar.FStar.fst"
let ext = if ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp")) then begin
".fs"
end else begin
".ml"
end
in (
# 72 "FStar.FStar.fst"
let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun _88_38 -> (match (_88_38) with
| (n, d) -> begin
(let _177_28 = (FStar_Options.prependOutputDir (Prims.strcat n ext))
in (let _177_27 = (FStar_Format.pretty 120 d)
in (FStar_Util.write_file _177_28 _177_27)))
end)) newDocs)))))
end else begin
()
end)

# 79 "FStar.FStar.fst"
let go = (fun _88_39 -> (
# 80 "FStar.FStar.fst"
let _88_43 = (process_args ())
in (match (_88_43) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(let _177_30 = (FStar_Options.specs ())
in (FStar_Options.display_usage _177_30))
end
| FStar_Getopt.Die (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.GoOn -> begin
if ((FStar_ST.read FStar_Options.dep) <> None) then begin
(let _177_31 = (FStar_Parser_Dep.collect filenames)
in (FStar_Parser_Dep.print _177_31))
end else begin
if (FStar_ST.read FStar_Options.interactive) then begin
(
# 90 "FStar.FStar.fst"
let filenames = if (FStar_ST.read FStar_Options.explicit_deps) then begin
(
# 92 "FStar.FStar.fst"
let _88_48 = if ((FStar_List.length filenames) = 0) then begin
(FStar_Util.print_error "--explicit_deps was provided without a file list!\n")
end else begin
()
end
in filenames)
end else begin
(
# 97 "FStar.FStar.fst"
let _88_50 = if ((FStar_List.length filenames) > 0) then begin
(FStar_Util.print_warning "ignoring the file list (no --explicit_deps)\n")
end else begin
()
end
in (FStar_Interactive.detect_dependencies_with_first_interactive_chunk ()))
end
in if (FStar_ST.read FStar_Options.universes) then begin
(
# 103 "FStar.FStar.fst"
let _88_56 = (FStar_Universal.batch_mode_tc filenames)
in (match (_88_56) with
| (fmods, dsenv, env) -> begin
(FStar_Interactive.interactive_mode (dsenv, env) None FStar_Universal.interactive_tc)
end))
end else begin
(
# 105 "FStar.FStar.fst"
let _88_60 = (FStar_Stratified.batch_mode_tc filenames)
in (match (_88_60) with
| (fmods, dsenv, env) -> begin
(FStar_Interactive.interactive_mode (dsenv, env) None FStar_Stratified.interactive_tc)
end))
end)
end else begin
if ((FStar_List.length filenames) >= 1) then begin
if (FStar_ST.read FStar_Options.universes) then begin
(
# 110 "FStar.FStar.fst"
let _88_64 = (FStar_Universal.batch_mode_tc filenames)
in (match (_88_64) with
| (fmods, dsenv, env) -> begin
(
# 111 "FStar.FStar.fst"
let _88_65 = (report_errors ())
in (
# 112 "FStar.FStar.fst"
let _88_67 = (codegen (FStar_Util.Inr ((fmods, env))))
in (let _177_32 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Universal.module_or_interface_name))
in (finished_message _177_32))))
end))
end else begin
(
# 114 "FStar.FStar.fst"
let _88_72 = (FStar_Stratified.batch_mode_tc filenames)
in (match (_88_72) with
| (fmods, dsenv, env) -> begin
(
# 115 "FStar.FStar.fst"
let _88_73 = (report_errors ())
in (
# 116 "FStar.FStar.fst"
let _88_75 = (codegen (FStar_Util.Inl ((fmods, env))))
in (let _177_33 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Stratified.module_or_interface_name))
in (finished_message _177_33))))
end))
end
end else begin
(FStar_Util.print_error "no file provided\n")
end
end
end
end)
end)))

# 124 "FStar.FStar.fst"
let main = (fun _88_77 -> (match (()) with
| () -> begin
try
(match (()) with
| () -> begin
(
# 126 "FStar.FStar.fst"
let _88_96 = (go ())
in (
# 127 "FStar.FStar.fst"
let _88_98 = (cleanup ())
in (FStar_All.exit 0)))
end)
with
| e -> begin
(
# 130 "FStar.FStar.fst"
let _88_86 = (
# 131 "FStar.FStar.fst"
let _88_82 = if (FStar_Absyn_Util.handleable e) then begin
(FStar_Absyn_Util.handle_err false () e)
end else begin
()
end
in (
# 132 "FStar.FStar.fst"
let _88_84 = if (FStar_Syntax_Util.handleable e) then begin
(FStar_Syntax_Util.handle_err false e)
end else begin
()
end
in if (FStar_ST.read FStar_Options.trace_error) then begin
(let _177_38 = (FStar_Util.message_of_exn e)
in (let _177_37 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" _177_38 _177_37)))
end else begin
if (not (((FStar_Absyn_Util.handleable e) || (FStar_Syntax_Util.handleable e)))) then begin
(let _177_39 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _177_39))
end else begin
()
end
end))
in (
# 138 "FStar.FStar.fst"
let _88_88 = (cleanup ())
in (
# 139 "FStar.FStar.fst"
let _88_90 = (let _177_40 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _177_40 Prims.ignore))
in (
# 140 "FStar.FStar.fst"
let _88_92 = (report_errors ())
in (FStar_All.exit 1)))))
end
end))




