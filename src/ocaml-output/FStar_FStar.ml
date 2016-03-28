
open Prims
# 22 "FStar.FStar.fst"
let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun _84_1 -> (match (()) with
| () -> begin
(
# 27 "FStar.FStar.fst"
let file_list = (FStar_Util.mk_ref [])
in (
# 28 "FStar.FStar.fst"
let res = (let _169_6 = (FStar_Options.specs ())
in (FStar_Getopt.parse_cmdline _169_6 (fun i -> (let _169_5 = (let _169_4 = (FStar_ST.read file_list)
in (FStar_List.append _169_4 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list _169_5)))))
in (
# 29 "FStar.FStar.fst"
let _84_8 = (match (res) with
| FStar_Getopt.GoOn -> begin
(let _169_7 = (FStar_Options.set_fstar_home ())
in (Prims.ignore _169_7))
end
| _84_7 -> begin
()
end)
in (let _169_8 = (FStar_ST.read file_list)
in (res, _169_8)))))
end))

# 32 "FStar.FStar.fst"
let cleanup : Prims.unit  ->  Prims.unit = (fun _84_10 -> (match (()) with
| () -> begin
(FStar_Util.kill_all ())
end))

# 35 "FStar.FStar.fst"
let report_errors : Prims.unit  ->  Prims.unit = (fun _84_11 -> (match (()) with
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
let _84_13 = (let _169_13 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" _169_13))
in (FStar_All.exit 1))
end else begin
()
end)
end))

# 46 "FStar.FStar.fst"
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
let _84_21 = (FStar_All.pipe_right fmods (FStar_List.iter (fun _84_19 -> (match (_84_19) with
| (iface, name) -> begin
(
# 56 "FStar.FStar.fst"
let tag = if iface then begin
"i\'face"
end else begin
"module"
end
in if (FStar_Options.should_print_message name.FStar_Ident.str) then begin
(let _169_17 = (FStar_Util.format3 "%s %s: %s\n" msg tag (FStar_Ident.text_of_lid name))
in (FStar_Util.print_string _169_17))
end else begin
()
end)
end))))
in (let _169_19 = (let _169_18 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" _169_18))
in (FStar_Util.print_string _169_19))))
end else begin
()
end)

# 60 "FStar.FStar.fst"
let codegen : ((FStar_Absyn_Syntax.modul Prims.list * FStar_Tc_Env.env), (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env)) FStar_Util.either  ->  Prims.unit = (fun uf_mods_env -> if (((FStar_ST.read FStar_Options.codegen) = Some ("OCaml")) || ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp"))) then begin
(
# 67 "FStar.FStar.fst"
let mllibs = (match (uf_mods_env) with
| FStar_Util.Inl (fmods, env) -> begin
(let _169_23 = (let _169_22 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _169_22 fmods))
in (FStar_All.pipe_left Prims.snd _169_23))
end
| FStar_Util.Inr (umods, env) -> begin
(let _169_25 = (let _169_24 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract _169_24 umods))
in (FStar_All.pipe_left Prims.snd _169_25))
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
in (FStar_List.iter (fun _84_38 -> (match (_84_38) with
| (n, d) -> begin
(let _169_28 = (FStar_Options.prependOutputDir (Prims.strcat n ext))
in (let _169_27 = (FStar_Format.pretty 120 d)
in (FStar_Util.write_file _169_28 _169_27)))
end)) newDocs)))))
end else begin
()
end)

# 74 "FStar.FStar.fst"
let go = (fun _84_39 -> (
# 80 "FStar.FStar.fst"
let _84_43 = (process_args ())
in (match (_84_43) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(let _169_30 = (FStar_Options.specs ())
in (FStar_Options.display_usage _169_30))
end
| FStar_Getopt.Die (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.GoOn -> begin
if ((FStar_ST.read FStar_Options.dep) <> None) then begin
(let _169_31 = (FStar_Parser_Dep.collect filenames)
in (FStar_Parser_Dep.print _169_31))
end else begin
if (FStar_ST.read FStar_Options.interactive) then begin
(
# 90 "FStar.FStar.fst"
let filenames = if (FStar_ST.read FStar_Options.explicit_deps) then begin
(
# 92 "FStar.FStar.fst"
let _84_48 = if ((FStar_List.length filenames) = 0) then begin
(FStar_Util.print_error "--explicit_deps was provided without a file list!\n")
end else begin
()
end
in filenames)
end else begin
(
# 97 "FStar.FStar.fst"
let _84_50 = if ((FStar_List.length filenames) > 0) then begin
(FStar_Util.print_warning "ignoring the file list (no --explicit_deps)\n")
end else begin
()
end
in (FStar_Interactive.detect_dependencies_with_first_interactive_chunk ()))
end
in if (FStar_ST.read FStar_Options.universes) then begin
(
# 103 "FStar.FStar.fst"
let _84_56 = (FStar_Universal.batch_mode_tc filenames)
in (match (_84_56) with
| (fmods, dsenv, env) -> begin
(FStar_Interactive.interactive_mode (dsenv, env) None FStar_Universal.interactive_tc)
end))
end else begin
(
# 105 "FStar.FStar.fst"
let _84_60 = (FStar_Stratified.batch_mode_tc filenames)
in (match (_84_60) with
| (fmods, dsenv, env) -> begin
(FStar_Interactive.interactive_mode (dsenv, env) None FStar_Stratified.interactive_tc)
end))
end)
end else begin
if ((FStar_List.length filenames) >= 1) then begin
if (FStar_ST.read FStar_Options.universes) then begin
(
# 110 "FStar.FStar.fst"
let _84_64 = (FStar_Universal.batch_mode_tc filenames)
in (match (_84_64) with
| (fmods, dsenv, env) -> begin
(
# 111 "FStar.FStar.fst"
let _84_65 = (report_errors ())
in (
# 112 "FStar.FStar.fst"
let _84_67 = (codegen (FStar_Util.Inr ((fmods, env))))
in (let _169_32 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Universal.module_or_interface_name))
in (finished_message _169_32))))
end))
end else begin
(
# 114 "FStar.FStar.fst"
let _84_72 = (FStar_Stratified.batch_mode_tc filenames)
in (match (_84_72) with
| (fmods, dsenv, env) -> begin
(
# 115 "FStar.FStar.fst"
let _84_73 = (report_errors ())
in (
# 116 "FStar.FStar.fst"
let _84_75 = (codegen (FStar_Util.Inl ((fmods, env))))
in (let _169_33 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Stratified.module_or_interface_name))
in (finished_message _169_33))))
end))
end
end else begin
(FStar_Util.print_error "no file provided\n")
end
end
end
end)
end)))

# 122 "FStar.FStar.fst"
let main = (fun _84_77 -> (match (()) with
| () -> begin
try
(match (()) with
| () -> begin
(
# 126 "FStar.FStar.fst"
let _84_96 = (go ())
in (
# 127 "FStar.FStar.fst"
let _84_98 = (cleanup ())
in (FStar_All.exit 0)))
end)
with
| e -> begin
(
# 130 "FStar.FStar.fst"
let _84_86 = (
# 131 "FStar.FStar.fst"
let _84_82 = if (FStar_Absyn_Util.handleable e) then begin
(FStar_Absyn_Util.handle_err false () e)
end else begin
()
end
in (
# 132 "FStar.FStar.fst"
let _84_84 = if (FStar_Syntax_Util.handleable e) then begin
(FStar_Syntax_Util.handle_err false e)
end else begin
()
end
in if (FStar_ST.read FStar_Options.trace_error) then begin
(let _169_38 = (FStar_Util.message_of_exn e)
in (let _169_37 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" _169_38 _169_37)))
end else begin
if (not (((FStar_Absyn_Util.handleable e) || (FStar_Syntax_Util.handleable e)))) then begin
(let _169_39 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _169_39))
end else begin
()
end
end))
in (
# 138 "FStar.FStar.fst"
let _84_88 = (cleanup ())
in (
# 139 "FStar.FStar.fst"
let _84_90 = (let _169_40 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _169_40 Prims.ignore))
in (
# 140 "FStar.FStar.fst"
let _84_92 = (report_errors ())
in (FStar_All.exit 1)))))
end
end))




