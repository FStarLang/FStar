
open Prims

let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun _99_1 -> (match (()) with
| () -> begin
(FStar_Options.parse_cmd_line ())
end))


let cleanup : Prims.unit  ->  Prims.unit = (fun _99_2 -> (match (()) with
| () -> begin
(FStar_Util.kill_all ())
end))


let finished_message : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  Prims.int  ->  Prims.unit = (fun fmods errs -> (

let print_to = if (errs > (Prims.parse_int "0")) then begin
FStar_Util.print_error
end else begin
FStar_Util.print_string
end
in if (not ((FStar_Options.silent ()))) then begin
(

let _99_12 = (FStar_All.pipe_right fmods (FStar_List.iter (fun _99_10 -> (match (_99_10) with
| ((iface, name), time) -> begin
(

let tag = if iface then begin
"i\'face"
end else begin
"module"
end
in if (FStar_Options.should_print_message name.FStar_Ident.str) then begin
if (time >= (Prims.parse_int "0")) then begin
(let _199_13 = (let _199_12 = (FStar_Util.string_of_int time)
in (FStar_Util.format3 "Verified %s: %s (%s milliseconds)\n" tag (FStar_Ident.text_of_lid name) _199_12))
in (print_to _199_13))
end else begin
(let _199_14 = (FStar_Util.format2 "Verified %s: %s\n" tag (FStar_Ident.text_of_lid name))
in (print_to _199_14))
end
end else begin
()
end)
end))))
in if (errs > (Prims.parse_int "0")) then begin
if (errs = (Prims.parse_int "1")) then begin
(FStar_Util.print_error "1 error was reported (see above)\n")
end else begin
(let _199_15 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" _199_15))
end
end else begin
(let _199_17 = (let _199_16 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" _199_16))
in (FStar_Util.print_string _199_17))
end)
end else begin
()
end))


let report_errors : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  Prims.unit = (fun fmods -> (

let errs = if (FStar_Options.universes ()) then begin
(FStar_TypeChecker_Errors.get_err_count ())
end else begin
(FStar_Tc_Errors.get_err_count ())
end
in if (errs > (Prims.parse_int "0")) then begin
(

let _99_16 = (finished_message fmods errs)
in (FStar_All.exit (Prims.parse_int "1")))
end else begin
()
end))


let codegen : ((FStar_Absyn_Syntax.modul Prims.list * FStar_Tc_Env.env), (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env)) FStar_Util.either  ->  Prims.unit = (fun uf_mods_env -> (

let opt = (FStar_Options.codegen ())
in if (opt <> None) then begin
(

let mllibs = (match (uf_mods_env) with
| FStar_Util.Inl (fmods, env) -> begin
(let _199_23 = (let _199_22 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _199_22 fmods))
in (FStar_All.pipe_left Prims.snd _199_23))
end
| FStar_Util.Inr (umods, env) -> begin
(let _199_25 = (let _199_24 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract _199_24 umods))
in (FStar_All.pipe_left Prims.snd _199_25))
end)
in (

let mllibs = (FStar_List.flatten mllibs)
in (

let ext = (match (opt) with
| Some ("FSharp") -> begin
".fs"
end
| Some ("OCaml") -> begin
".ml"
end
| Some ("Kremlin") -> begin
".krml"
end
| Some ("JavaScript") -> begin
".flow"
end
| _99_39 -> begin
(failwith "Unrecognized option")
end)
in (match (opt) with
| (Some ("FSharp")) | (Some ("OCaml")) -> begin
(

let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun _99_48 -> (match (_99_48) with
| (n, d) -> begin
(let _199_27 = (FStar_Options.prepend_output_dir (Prims.strcat n ext))
in (FStar_Util.write_file _199_27 (FStar_Format.pretty (Prims.parse_int "120") d)))
end)) newDocs))
end
| Some ("JavaScript") -> begin
(

let newDocs = (FStar_List.collect FStar_Extraction_JavaScript_Translate.translate mllibs)
in (FStar_List.iter (fun _99_54 -> (match (_99_54) with
| (n, d) -> begin
(

let res = (FStar_Extraction_JavaScript_PrintAst.pretty_print d)
in (let _199_29 = (FStar_Options.prepend_output_dir (Prims.strcat n ext))
in (FStar_Util.write_file _199_29 (FStar_Format.pretty (Prims.parse_int "120") res))))
end)) newDocs))
end
| Some ("Kremlin") -> begin
(

let programs = (let _199_30 = (FStar_List.map FStar_Extraction_Kremlin.translate mllibs)
in (FStar_List.flatten _199_30))
in (

let bin = ((FStar_Extraction_Kremlin.current_version), (programs))
in (let _199_31 = (FStar_Options.prepend_output_dir "out.krml")
in (FStar_Util.save_value_to_file _199_31 bin))))
end
| _99_61 -> begin
(failwith "Unrecognized option")
end))))
end else begin
()
end))


let go = (fun _99_62 -> (

let _99_66 = (process_args ())
in (match (_99_66) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(

let _99_68 = (FStar_Options.display_usage ())
in (FStar_All.exit (Prims.parse_int "0")))
end
| FStar_Getopt.Error (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.Success -> begin
if ((FStar_Options.dep ()) <> None) then begin
(let _199_33 = (FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames)
in (FStar_Parser_Dep.print _199_33))
end else begin
if (FStar_Options.interactive ()) then begin
(

let _99_84 = if (FStar_Options.explicit_deps ()) then begin
(

let _99_73 = if ((FStar_List.length filenames) = (Prims.parse_int "0")) then begin
(FStar_Util.print_error "--explicit_deps was provided without a file list!\n")
end else begin
()
end
in ((None), (None), (filenames)))
end else begin
(

let _99_75 = if ((FStar_List.length filenames) > (Prims.parse_int "0")) then begin
(FStar_Util.print_warning "ignoring the file list (no --explicit_deps)\n")
end else begin
()
end
in (

let _99_80 = (FStar_Interactive.detect_dependencies_with_first_interactive_chunk ())
in (match (_99_80) with
| (fn, mn, deps) -> begin
((Some (fn)), (Some (mn)), (deps))
end)))
end
in (match (_99_84) with
| (main_buffer_filename_opt, main_buffer_mod_name_opt, filenames) -> begin
if (FStar_Options.universes ()) then begin
(FStar_Interactive.interactive_mode main_buffer_filename_opt main_buffer_mod_name_opt FStar_Parser_Dep.VerifyUserList filenames None FStar_Universal.interactive_tc)
end else begin
(FStar_Interactive.interactive_mode None None FStar_Parser_Dep.VerifyUserList filenames None FStar_Stratified.interactive_tc)
end
end))
end else begin
if (FStar_Options.doc ()) then begin
(FStar_Fsdoc_Generator.generate filenames)
end else begin
if ((FStar_List.length filenames) >= (Prims.parse_int "1")) then begin
(

let verify_mode = if (FStar_Options.verify_all ()) then begin
(

let _99_87 = if ((FStar_Options.verify_module ()) <> []) then begin
(

let _99_85 = (FStar_Util.print_error "--verify_module is incompatible with --verify_all")
in (FStar_All.exit (Prims.parse_int "1")))
end else begin
()
end
in FStar_Parser_Dep.VerifyAll)
end else begin
if ((FStar_Options.verify_module ()) <> []) then begin
FStar_Parser_Dep.VerifyUserList
end else begin
FStar_Parser_Dep.VerifyFigureItOut
end
end
in if (FStar_Options.universes ()) then begin
(

let filenames = (FStar_Dependences.find_deps_if_needed verify_mode filenames)
in (

let _99_94 = (FStar_Universal.batch_mode_tc filenames)
in (match (_99_94) with
| (fmods, dsenv, env) -> begin
(

let module_names_and_times = (FStar_All.pipe_right fmods (FStar_List.map (fun _99_97 -> (match (_99_97) with
| (x, t) -> begin
(((FStar_Universal.module_or_interface_name x)), (t))
end))))
in (

let _99_99 = (report_errors module_names_and_times)
in (

let _99_101 = (let _199_37 = (let _199_36 = (let _199_35 = (FStar_All.pipe_right fmods (FStar_List.map Prims.fst))
in ((_199_35), (env)))
in FStar_Util.Inr (_199_36))
in (codegen _199_37))
in (finished_message module_names_and_times (Prims.parse_int "0")))))
end)))
end else begin
(

let _99_106 = (FStar_Stratified.batch_mode_tc verify_mode filenames)
in (match (_99_106) with
| (fmods, dsenv, env) -> begin
(

let module_names_and_times = (FStar_All.pipe_right fmods (FStar_List.map (fun _99_109 -> (match (_99_109) with
| (x, t) -> begin
(((FStar_Stratified.module_or_interface_name x)), (t))
end))))
in (

let _99_111 = (report_errors module_names_and_times)
in (

let _99_113 = (let _199_41 = (let _199_40 = (let _199_39 = (FStar_All.pipe_right fmods (FStar_List.map Prims.fst))
in ((_199_39), (env)))
in FStar_Util.Inl (_199_40))
in (codegen _199_41))
in (finished_message module_names_and_times (Prims.parse_int "0")))))
end))
end)
end else begin
(FStar_Util.print_error "no file provided\n")
end
end
end
end
end)
end)))


let main = (fun _99_115 -> (match (()) with
| () -> begin
try
(match (()) with
| () -> begin
(

let _99_134 = (go ())
in (

let _99_136 = (cleanup ())
in (FStar_All.exit (Prims.parse_int "0"))))
end)
with
| e -> begin
(

let _99_124 = (

let _99_120 = if (FStar_Absyn_Util.handleable e) then begin
(FStar_Absyn_Util.handle_err false () e)
end else begin
()
end
in (

let _99_122 = if (FStar_TypeChecker_Errors.handleable e) then begin
(FStar_TypeChecker_Errors.handle_err false e)
end else begin
()
end
in if (FStar_Options.trace_error ()) then begin
(let _199_46 = (FStar_Util.message_of_exn e)
in (let _199_45 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" _199_46 _199_45)))
end else begin
if (not (((FStar_Absyn_Util.handleable e) || (FStar_TypeChecker_Errors.handleable e)))) then begin
(let _199_47 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _199_47))
end else begin
()
end
end))
in (

let _99_126 = (cleanup ())
in (

let _99_128 = (let _199_48 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _199_48 Prims.ignore))
in (

let _99_130 = (report_errors [])
in (FStar_All.exit (Prims.parse_int "1"))))))
end
end))




