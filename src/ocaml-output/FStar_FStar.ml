
open Prims

let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun _88_1 -> (match (()) with
| () -> begin
(FStar_Options.parse_cmd_line ())
end))


let cleanup : Prims.unit  ->  Prims.unit = (fun _88_2 -> (match (()) with
| () -> begin
(FStar_Util.kill_all ())
end))


let report_errors : Prims.unit  ->  Prims.unit = (fun _88_3 -> (match (()) with
| () -> begin
(

let errs = if (FStar_Options.universes ()) then begin
(FStar_TypeChecker_Errors.get_err_count ())
end else begin
(FStar_Tc_Errors.get_err_count ())
end
in if (errs > 0) then begin
(

let _88_5 = (let _177_7 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" _177_7))
in (FStar_All.exit 1))
end else begin
()
end)
end))


let finished_message : (Prims.bool * FStar_Ident.lident) Prims.list  ->  Prims.unit = (fun fmods -> if (not ((FStar_Options.silent ()))) then begin
(

let _88_12 = (FStar_All.pipe_right fmods (FStar_List.iter (fun _88_10 -> (match (_88_10) with
| (iface, name) -> begin
(

let tag = if iface then begin
"i\'face"
end else begin
"module"
end
in if (FStar_Options.should_print_message name.FStar_Ident.str) then begin
(let _177_11 = (FStar_Util.format2 "Verifying %s: %s\n" tag (FStar_Ident.text_of_lid name))
in (FStar_Util.print_string _177_11))
end else begin
()
end)
end))))
in (let _177_13 = (let _177_12 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" _177_12))
in (FStar_Util.print_string _177_13)))
end else begin
()
end)


let codegen : ((FStar_Absyn_Syntax.modul Prims.list * FStar_Tc_Env.env), (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env)) FStar_Util.either  ->  Prims.unit = (fun uf_mods_env -> if (((FStar_Options.codegen ()) = Some ("OCaml")) || ((FStar_Options.codegen ()) = Some ("FSharp"))) then begin
(

let mllibs = (match (uf_mods_env) with
| FStar_Util.Inl (fmods, env) -> begin
(let _177_17 = (let _177_16 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _177_16 fmods))
in (FStar_All.pipe_left Prims.snd _177_17))
end
| FStar_Util.Inr (umods, env) -> begin
(let _177_19 = (let _177_18 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract _177_18 umods))
in (FStar_All.pipe_left Prims.snd _177_19))
end)
in (

let mllibs = (FStar_List.flatten mllibs)
in (

let ext = if ((FStar_Options.codegen ()) = Some ("FSharp")) then begin
".fs"
end else begin
".ml"
end
in (

let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun _88_29 -> (match (_88_29) with
| (n, d) -> begin
(let _177_22 = (FStar_Options.prepend_output_dir (Prims.strcat n ext))
in (let _177_21 = (FStar_Format.pretty 120 d)
in (FStar_Util.write_file _177_22 _177_21)))
end)) newDocs)))))
end else begin
()
end)


let go = (fun _88_30 -> (

let _88_34 = (process_args ())
in (match (_88_34) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(

let _88_36 = (FStar_Options.display_usage ())
in (FStar_All.exit 0))
end
| FStar_Getopt.Die (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.GoOn -> begin
if ((FStar_Options.dep ()) <> None) then begin
(let _177_24 = (FStar_Parser_Dep.collect filenames)
in (FStar_Parser_Dep.print _177_24))
end else begin
if (FStar_Options.interactive ()) then begin
(

let filenames = if (FStar_Options.explicit_deps ()) then begin
(

let _88_41 = if ((FStar_List.length filenames) = 0) then begin
(FStar_Util.print_error "--explicit_deps was provided without a file list!\n")
end else begin
()
end
in filenames)
end else begin
(

let _88_43 = if ((FStar_List.length filenames) > 0) then begin
(FStar_Util.print_warning "ignoring the file list (no --explicit_deps)\n")
end else begin
()
end
in (FStar_Interactive.detect_dependencies_with_first_interactive_chunk ()))
end
in if (FStar_Options.universes ()) then begin
(

let _88_49 = (FStar_Universal.batch_mode_tc filenames)
in (match (_88_49) with
| (fmods, dsenv, env) -> begin
(FStar_Interactive.interactive_mode (dsenv, env) None FStar_Universal.interactive_tc)
end))
end else begin
(

let _88_53 = (FStar_Stratified.batch_mode_tc filenames)
in (match (_88_53) with
| (fmods, dsenv, env) -> begin
(FStar_Interactive.interactive_mode (dsenv, env) None FStar_Stratified.interactive_tc)
end))
end)
end else begin
if ((FStar_List.length filenames) >= 1) then begin
(

let _88_61 = if (not ((FStar_Options.explicit_deps ()))) then begin
(

let files = (FStar_List.map (fun f -> (match ((let _177_26 = (FStar_Util.basename f)
in (FStar_Parser_Dep.check_and_strip_suffix _177_26))) with
| None -> begin
(

let _88_56 = (FStar_Util.print1 "Unrecognized file type: %s\n" f)
in (FStar_All.exit 1))
end
| Some (f) -> begin
(FStar_String.lowercase f)
end)) filenames)
in (FStar_List.iter FStar_Options.add_verify_module files))
end else begin
()
end
in if (FStar_Options.universes ()) then begin
(

let _88_66 = (FStar_Universal.batch_mode_tc filenames)
in (match (_88_66) with
| (fmods, dsenv, env) -> begin
(

let _88_67 = (report_errors ())
in (

let _88_69 = (codegen (FStar_Util.Inr ((fmods, env))))
in (let _177_27 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Universal.module_or_interface_name))
in (finished_message _177_27))))
end))
end else begin
(

let _88_74 = (FStar_Stratified.batch_mode_tc filenames)
in (match (_88_74) with
| (fmods, dsenv, env) -> begin
(

let _88_75 = (report_errors ())
in (

let _88_77 = (codegen (FStar_Util.Inl ((fmods, env))))
in (let _177_28 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Stratified.module_or_interface_name))
in (finished_message _177_28))))
end))
end)
end else begin
(FStar_Util.print_error "no file provided\n")
end
end
end
end)
end)))


let main = (fun _88_79 -> (match (()) with
| () -> begin
try
(match (()) with
| () -> begin
(

let _88_98 = (go ())
in (

let _88_100 = (cleanup ())
in (FStar_All.exit 0)))
end)
with
| e -> begin
(

let _88_88 = (

let _88_84 = if (FStar_Absyn_Util.handleable e) then begin
(FStar_Absyn_Util.handle_err false () e)
end else begin
()
end
in (

let _88_86 = if (FStar_Syntax_Util.handleable e) then begin
(FStar_Syntax_Util.handle_err false e)
end else begin
()
end
in if (FStar_Options.trace_error ()) then begin
(let _177_33 = (FStar_Util.message_of_exn e)
in (let _177_32 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" _177_33 _177_32)))
end else begin
if (not (((FStar_Absyn_Util.handleable e) || (FStar_Syntax_Util.handleable e)))) then begin
(let _177_34 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _177_34))
end else begin
()
end
end))
in (

let _88_90 = (cleanup ())
in (

let _88_92 = (let _177_35 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _177_35 Prims.ignore))
in (

let _88_94 = (report_errors ())
in (FStar_All.exit 1)))))
end
end))




