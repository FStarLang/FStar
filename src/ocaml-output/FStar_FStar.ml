
open Prims
# 26 "FStar.FStar.fst"
let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun _83_1 -> (match (()) with
| () -> begin
(
# 27 "FStar.FStar.fst"
let file_list = (FStar_Util.mk_ref [])
in (
# 28 "FStar.FStar.fst"
let res = (let _167_6 = (FStar_Options.specs ())
in (FStar_Getopt.parse_cmdline _167_6 (fun i -> (let _167_5 = (let _167_4 = (FStar_ST.read file_list)
in (FStar_List.append _167_4 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list _167_5)))))
in (
# 29 "FStar.FStar.fst"
let _83_8 = (match (res) with
| FStar_Getopt.GoOn -> begin
(let _167_7 = (FStar_Options.set_fstar_home ())
in (Prims.ignore _167_7))
end
| _83_7 -> begin
()
end)
in (let _167_8 = (FStar_ST.read file_list)
in (res, _167_8)))))
end))

# 35 "FStar.FStar.fst"
let cleanup : Prims.unit  ->  Prims.unit = (fun _83_10 -> (match (()) with
| () -> begin
(FStar_Util.kill_all ())
end))

# 38 "FStar.FStar.fst"
let report_errors : Prims.int Prims.option  ->  Prims.unit = (fun nopt -> (
# 39 "FStar.FStar.fst"
let errs = (match (nopt) with
| None -> begin
if (FStar_ST.read FStar_Options.universes) then begin
(FStar_TypeChecker_Errors.get_err_count ())
end else begin
(FStar_Tc_Errors.get_err_count ())
end
end
| Some (n) -> begin
n
end)
in if (errs > 0) then begin
(
# 47 "FStar.FStar.fst"
let _83_16 = (let _167_13 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" _167_13))
in (FStar_All.exit 1))
end else begin
()
end))

# 52 "FStar.FStar.fst"
let finished_message : (Prims.bool * FStar_Ident.lident) Prims.list  ->  Prims.unit = (fun fmods -> if (not ((FStar_ST.read FStar_Options.silent))) then begin
(
# 54 "FStar.FStar.fst"
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
# 58 "FStar.FStar.fst"
let _83_24 = (FStar_All.pipe_right fmods (FStar_List.iter (fun _83_22 -> (match (_83_22) with
| (iface, name) -> begin
(
# 59 "FStar.FStar.fst"
let tag = if iface then begin
"i\'face"
end else begin
"module"
end
in if (FStar_Options.should_print_message name.FStar_Ident.str) then begin
(let _167_17 = (FStar_Util.format3 "%s %s: %s\n" msg tag (FStar_Ident.text_of_lid name))
in (FStar_Util.print_string _167_17))
end else begin
()
end)
end))))
in (let _167_19 = (let _167_18 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" _167_18))
in (FStar_Util.print_string _167_19))))
end else begin
()
end)

# 66 "FStar.FStar.fst"
let codegen : ((FStar_Absyn_Syntax.modul Prims.list * FStar_Tc_Env.env), (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env)) FStar_Util.either  ->  Prims.unit = (fun uf_mods_env -> if (((FStar_ST.read FStar_Options.codegen) = Some ("OCaml")) || ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp"))) then begin
(
# 70 "FStar.FStar.fst"
let mllibs = (match (uf_mods_env) with
| FStar_Util.Inl (fmods, env) -> begin
(let _167_23 = (let _167_22 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _167_22 fmods))
in (FStar_All.pipe_left Prims.snd _167_23))
end
| FStar_Util.Inr (umods, env) -> begin
(let _167_25 = (let _167_24 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract _167_24 umods))
in (FStar_All.pipe_left Prims.snd _167_25))
end)
in (
# 73 "FStar.FStar.fst"
let mllibs = (FStar_List.flatten mllibs)
in (
# 74 "FStar.FStar.fst"
let ext = if ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp")) then begin
".fs"
end else begin
".ml"
end
in (
# 75 "FStar.FStar.fst"
let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun _83_41 -> (match (_83_41) with
| (n, d) -> begin
(let _167_28 = (FStar_Options.prependOutputDir (Prims.strcat n ext))
in (let _167_27 = (FStar_Format.pretty 120 d)
in (FStar_Util.write_file _167_28 _167_27)))
end)) newDocs)))))
end else begin
()
end)

# 82 "FStar.FStar.fst"
let go = (fun _83_42 -> (
# 83 "FStar.FStar.fst"
let _83_46 = (process_args ())
in (match (_83_46) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(let _167_30 = (FStar_Options.specs ())
in (FStar_Options.display_usage _167_30))
end
| FStar_Getopt.Die (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.GoOn -> begin
if ((FStar_ST.read FStar_Options.dep) <> None) then begin
(let _167_31 = (FStar_Parser_Dep.collect filenames)
in (FStar_Parser_Dep.print _167_31))
end else begin
if (FStar_ST.read FStar_Options.interactive) then begin
(
# 93 "FStar.FStar.fst"
let filenames = if (FStar_ST.read FStar_Options.explicit_deps) then begin
(
# 95 "FStar.FStar.fst"
let _83_51 = if ((FStar_List.length filenames) = 0) then begin
(FStar_Util.print_error "--explicit_deps was provided without a file list!\n")
end else begin
()
end
in filenames)
end else begin
(
# 100 "FStar.FStar.fst"
let _83_53 = if ((FStar_List.length filenames) > 0) then begin
(FStar_Util.print_warning "ignoring the file list (no --explicit_deps)\n")
end else begin
()
end
in (FStar_Interactive.detect_dependencies_with_first_interactive_chunk ()))
end
in if (FStar_ST.read FStar_Options.universes) then begin
(
# 106 "FStar.FStar.fst"
let _83_59 = (FStar_Universal.batch_mode_tc filenames)
in (match (_83_59) with
| (fmods, dsenv, env) -> begin
(FStar_Interactive.interactive_mode (dsenv, env) None FStar_Universal.interactive_tc)
end))
end else begin
(
# 108 "FStar.FStar.fst"
let _83_63 = (FStar_Stratified.batch_mode_tc filenames)
in (match (_83_63) with
| (fmods, dsenv, env) -> begin
(FStar_Interactive.interactive_mode (dsenv, env) None FStar_Stratified.interactive_tc)
end))
end)
end else begin
if ((FStar_List.length filenames) >= 1) then begin
if (FStar_ST.read FStar_Options.universes) then begin
(
# 113 "FStar.FStar.fst"
let _83_67 = (FStar_Universal.batch_mode_tc filenames)
in (match (_83_67) with
| (fmods, dsenv, env) -> begin
(
# 114 "FStar.FStar.fst"
let _83_68 = (report_errors None)
in (
# 115 "FStar.FStar.fst"
let _83_70 = (codegen (FStar_Util.Inr ((fmods, env))))
in (let _167_32 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Universal.module_or_interface_name))
in (finished_message _167_32))))
end))
end else begin
(
# 117 "FStar.FStar.fst"
let _83_75 = (FStar_Stratified.batch_mode_tc filenames)
in (match (_83_75) with
| (fmods, dsenv, env) -> begin
(
# 118 "FStar.FStar.fst"
let _83_76 = (report_errors None)
in (
# 119 "FStar.FStar.fst"
let _83_78 = (codegen (FStar_Util.Inl ((fmods, env))))
in (let _167_33 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Stratified.module_or_interface_name))
in (finished_message _167_33))))
end))
end
end else begin
(FStar_Util.print_error "no file provided\n")
end
end
end
end)
end)))

# 127 "FStar.FStar.fst"
let main = (fun _83_80 -> (match (()) with
| () -> begin
(FStar_All.try_with (fun _83_82 -> (match (()) with
| () -> begin
(
# 129 "FStar.FStar.fst"
let _83_95 = (go ())
in (
# 130 "FStar.FStar.fst"
let _83_97 = (cleanup ())
in (FStar_All.exit 0)))
end)) (fun _83_81 -> (match (_83_81) with
| e -> begin
(
# 133 "FStar.FStar.fst"
let _83_91 = (
# 134 "FStar.FStar.fst"
let _83_85 = if (FStar_Absyn_Util.handleable e) then begin
(FStar_Absyn_Util.handle_err false () e)
end else begin
()
end
in (
# 135 "FStar.FStar.fst"
let _83_87 = if (FStar_Syntax_Util.handleable e) then begin
(FStar_Syntax_Util.handle_err false () e)
end else begin
()
end
in (
# 136 "FStar.FStar.fst"
let _83_89 = if (FStar_ST.read FStar_Options.trace_error) then begin
(let _167_38 = (FStar_Util.message_of_exn e)
in (let _167_37 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" _167_38 _167_37)))
end else begin
if (not (((FStar_Absyn_Util.handleable e) || (FStar_Syntax_Util.handleable e)))) then begin
(let _167_39 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _167_39))
end else begin
()
end
end
in (cleanup ()))))
in (FStar_All.exit 1))
end)))
end))




