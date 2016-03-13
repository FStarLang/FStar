
open Prims
# 26 "FStar.FStar.fst"
let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun _81_1 -> (match (()) with
| () -> begin
(
# 27 "FStar.FStar.fst"
let file_list = (FStar_Util.mk_ref [])
in (
# 28 "FStar.FStar.fst"
let res = (let _163_6 = (FStar_Options.specs ())
in (FStar_Getopt.parse_cmdline _163_6 (fun i -> (let _163_5 = (let _163_4 = (FStar_ST.read file_list)
in (FStar_List.append _163_4 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list _163_5)))))
in (
# 29 "FStar.FStar.fst"
let _81_8 = (match (res) with
| FStar_Getopt.GoOn -> begin
(let _163_7 = (FStar_Options.set_fstar_home ())
in (Prims.ignore _163_7))
end
| _81_7 -> begin
()
end)
in (let _163_8 = (FStar_ST.read file_list)
in (res, _163_8)))))
end))

# 35 "FStar.FStar.fst"
let cleanup : Prims.unit  ->  Prims.unit = (fun _81_10 -> (match (()) with
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
let _81_16 = (let _163_13 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" _163_13))
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
let _81_24 = (FStar_All.pipe_right fmods (FStar_List.iter (fun _81_22 -> (match (_81_22) with
| (iface, name) -> begin
(
# 59 "FStar.FStar.fst"
let tag = if iface then begin
"i\'face"
end else begin
"module"
end
in if (FStar_Options.should_print_message name.FStar_Ident.str) then begin
(let _163_17 = (FStar_Util.format3 "%s %s: %s\n" msg tag (FStar_Ident.text_of_lid name))
in (FStar_Util.print_string _163_17))
end else begin
()
end)
end))))
in (let _163_19 = (let _163_18 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" _163_18))
in (FStar_Util.print_string _163_19))))
end else begin
()
end)

# 66 "FStar.FStar.fst"
let codegen : FStar_Absyn_Syntax.modul Prims.list  ->  FStar_Tc_Env.env  ->  Prims.unit = (fun fmods env -> if (((FStar_ST.read FStar_Options.codegen) = Some ("OCaml")) || ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp"))) then begin
(
# 70 "FStar.FStar.fst"
let _81_30 = (let _163_24 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _163_24 fmods))
in (match (_81_30) with
| (c, mllibs) -> begin
(
# 71 "FStar.FStar.fst"
let mllibs = (FStar_List.flatten mllibs)
in (
# 72 "FStar.FStar.fst"
let ext = if ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp")) then begin
".fs"
end else begin
".ml"
end
in (
# 73 "FStar.FStar.fst"
let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun _81_36 -> (match (_81_36) with
| (n, d) -> begin
(let _163_27 = (FStar_Options.prependOutputDir (Prims.strcat n ext))
in (let _163_26 = (FStar_Format.pretty 120 d)
in (FStar_Util.write_file _163_27 _163_26)))
end)) newDocs))))
end))
end else begin
if ((FStar_ST.read FStar_Options.codegen) = Some ("Wysteria")) then begin
(FStar_Extraction_Wysteria_Extract.extract fmods env)
end else begin
()
end
end)

# 86 "FStar.FStar.fst"
let go = (fun _81_37 -> (
# 87 "FStar.FStar.fst"
let _81_41 = (process_args ())
in (match (_81_41) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(let _163_29 = (FStar_Options.specs ())
in (FStar_Options.display_usage _163_29))
end
| FStar_Getopt.Die (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.GoOn -> begin
if ((FStar_ST.read FStar_Options.dep) <> None) then begin
(let _163_30 = (FStar_Parser_Dep.collect filenames)
in (FStar_Parser_Dep.print _163_30))
end else begin
if (FStar_ST.read FStar_Options.interactive) then begin
(
# 97 "FStar.FStar.fst"
let filenames = if (FStar_ST.read FStar_Options.explicit_deps) then begin
(
# 99 "FStar.FStar.fst"
let _81_46 = if ((FStar_List.length filenames) = 0) then begin
(FStar_Util.print_error "--explicit_deps was provided without a file list!\n")
end else begin
()
end
in filenames)
end else begin
(
# 104 "FStar.FStar.fst"
let _81_48 = if ((FStar_List.length filenames) > 0) then begin
(FStar_Util.print_warning "ignoring the file list (no --explicit_deps)\n")
end else begin
()
end
in (FStar_Interactive.detect_dependencies_with_first_interactive_chunk ()))
end
in if (FStar_ST.read FStar_Options.universes) then begin
(
# 110 "FStar.FStar.fst"
let _81_54 = (FStar_Universal.batch_mode_tc filenames)
in (match (_81_54) with
| (fmods, dsenv, env) -> begin
(FStar_Interactive.interactive_mode (dsenv, env) None FStar_Universal.interactive_tc)
end))
end else begin
(
# 112 "FStar.FStar.fst"
let _81_58 = (FStar_Stratified.batch_mode_tc filenames)
in (match (_81_58) with
| (fmods, dsenv, env) -> begin
(FStar_Interactive.interactive_mode (dsenv, env) None FStar_Stratified.interactive_tc)
end))
end)
end else begin
if ((FStar_List.length filenames) >= 1) then begin
if (FStar_ST.read FStar_Options.universes) then begin
(
# 117 "FStar.FStar.fst"
let _81_62 = (FStar_Universal.batch_mode_tc filenames)
in (match (_81_62) with
| (fmods, dsenv, env) -> begin
(
# 118 "FStar.FStar.fst"
let _81_63 = (report_errors None)
in (let _163_31 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Universal.module_or_interface_name))
in (finished_message _163_31)))
end))
end else begin
(
# 120 "FStar.FStar.fst"
let _81_68 = (FStar_Stratified.batch_mode_tc filenames)
in (match (_81_68) with
| (fmods, dsenv, env) -> begin
(
# 121 "FStar.FStar.fst"
let _81_69 = (report_errors None)
in (
# 122 "FStar.FStar.fst"
let _81_71 = (codegen fmods env)
in (let _163_32 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Stratified.module_or_interface_name))
in (finished_message _163_32))))
end))
end
end else begin
(FStar_Util.print_error "no file provided\n")
end
end
end
end)
end)))

# 130 "FStar.FStar.fst"
let main = (fun _81_73 -> (match (()) with
| () -> begin
(FStar_All.try_with (fun _81_75 -> (match (()) with
| () -> begin
(
# 132 "FStar.FStar.fst"
let _81_88 = (go ())
in (
# 133 "FStar.FStar.fst"
let _81_90 = (cleanup ())
in (FStar_All.exit 0)))
end)) (fun _81_74 -> (match (_81_74) with
| e -> begin
(
# 136 "FStar.FStar.fst"
let _81_78 = if (FStar_Absyn_Util.handleable e) then begin
(FStar_Absyn_Util.handle_err false () e)
end else begin
()
end
in (
# 137 "FStar.FStar.fst"
let _81_80 = if (FStar_Syntax_Util.handleable e) then begin
(FStar_Syntax_Util.handle_err false () e)
end else begin
()
end
in (
# 138 "FStar.FStar.fst"
let _81_82 = if (FStar_ST.read FStar_Options.trace_error) then begin
(let _163_37 = (FStar_Util.message_of_exn e)
in (let _163_36 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" _163_37 _163_36)))
end else begin
if (not (((FStar_Absyn_Util.handleable e) || (FStar_Syntax_Util.handleable e)))) then begin
(let _163_38 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _163_38))
end else begin
()
end
end
in (
# 142 "FStar.FStar.fst"
let _81_84 = (cleanup ())
in (FStar_All.exit 1)))))
end)))
end))




