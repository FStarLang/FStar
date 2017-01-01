
open Prims

let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun _97_1 -> (match (()) with
| () -> begin
(FStar_Options.parse_cmd_line ())
end))


let cleanup : Prims.unit  ->  Prims.unit = (fun _97_2 -> (match (()) with
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

let _97_12 = (FStar_All.pipe_right fmods (FStar_List.iter (fun _97_10 -> (match (_97_10) with
| ((iface, name), time) -> begin
(

let tag = if iface then begin
"i\'face"
end else begin
"module"
end
in if (FStar_Options.should_print_message name.FStar_Ident.str) then begin
if (time >= (Prims.parse_int "0")) then begin
(let _195_13 = (let _195_12 = (FStar_Util.string_of_int time)
in (FStar_Util.format3 "Verified %s: %s (%s milliseconds)\n" tag (FStar_Ident.text_of_lid name) _195_12))
in (print_to _195_13))
end else begin
(let _195_14 = (FStar_Util.format2 "Verified %s: %s\n" tag (FStar_Ident.text_of_lid name))
in (print_to _195_14))
end
end else begin
()
end)
end))))
in if (errs > (Prims.parse_int "0")) then begin
if (errs = (Prims.parse_int "1")) then begin
(FStar_Util.print_error "1 error was reported (see above)\n")
end else begin
(let _195_15 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" _195_15))
end
end else begin
(let _195_17 = (let _195_16 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" _195_16))
in (FStar_Util.print_string _195_17))
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

let _97_16 = (finished_message fmods errs)
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
(let _195_23 = (let _195_22 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _195_22 fmods))
in (FStar_All.pipe_left Prims.snd _195_23))
end
| FStar_Util.Inr (umods, env) -> begin
(let _195_25 = (let _195_24 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract _195_24 umods))
in (FStar_All.pipe_left Prims.snd _195_25))
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
| _97_37 -> begin
(FStar_All.failwith "Unrecognized option")
end)
in (match (opt) with
| (Some ("FSharp")) | (Some ("OCaml")) -> begin
(

let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun _97_46 -> (match (_97_46) with
| (n, d) -> begin
(let _195_27 = (FStar_Options.prepend_output_dir (Prims.strcat n ext))
in (FStar_Util.write_file _195_27 (FStar_Format.pretty (Prims.parse_int "120") d)))
end)) newDocs))
end
| Some ("Kremlin") -> begin
(

let programs = (let _195_28 = (FStar_List.map FStar_Extraction_Kremlin.translate mllibs)
in (FStar_List.flatten _195_28))
in (

let bin = ((FStar_Extraction_Kremlin.current_version), (programs))
in (let _195_29 = (FStar_Options.prepend_output_dir "out.krml")
in (FStar_Util.save_value_to_file _195_29 bin))))
end
| _97_52 -> begin
(FStar_All.failwith "Unrecognized option")
end))))
end else begin
()
end))


let go = (fun _97_53 -> (

let _97_57 = (process_args ())
in (match (_97_57) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(

let _97_59 = (FStar_Options.display_usage ())
in (FStar_All.exit (Prims.parse_int "0")))
end
| FStar_Getopt.Error (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.Success -> begin
if ((FStar_Options.dep ()) <> None) then begin
(let _195_31 = (FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames)
in (FStar_Parser_Dep.print _195_31))
end else begin
if (FStar_Options.interactive ()) then begin
(

let _97_75 = if (FStar_Options.explicit_deps ()) then begin
(

let _97_64 = if ((FStar_List.length filenames) = (Prims.parse_int "0")) then begin
(FStar_Util.print_error "--explicit_deps was provided without a file list!\n")
end else begin
()
end
in ((None), (None), (filenames)))
end else begin
(

let _97_66 = if ((FStar_List.length filenames) > (Prims.parse_int "0")) then begin
(FStar_Util.print_warning "ignoring the file list (no --explicit_deps)\n")
end else begin
()
end
in (

let _97_71 = (FStar_Interactive.detect_dependencies_with_first_interactive_chunk ())
in (match (_97_71) with
| (fn, mn, deps) -> begin
((Some (fn)), (Some (mn)), (deps))
end)))
end
in (match (_97_75) with
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
if (FStar_Options.indent ()) then begin
(FStar_Indent.generate filenames)
end else begin
if ((FStar_List.length filenames) >= (Prims.parse_int "1")) then begin
(

let verify_mode = if (FStar_Options.verify_all ()) then begin
(

let _97_78 = if ((FStar_Options.verify_module ()) <> []) then begin
(

let _97_76 = (FStar_Util.print_error "--verify_module is incompatible with --verify_all")
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

let _97_85 = (FStar_Universal.batch_mode_tc filenames)
in (match (_97_85) with
| (fmods, dsenv, env) -> begin
(

let module_names_and_times = (FStar_All.pipe_right fmods (FStar_List.map (fun _97_88 -> (match (_97_88) with
| (x, t) -> begin
(((FStar_Universal.module_or_interface_name x)), (t))
end))))
in (

let _97_90 = (report_errors module_names_and_times)
in (

let _97_92 = (let _195_35 = (let _195_34 = (let _195_33 = (FStar_All.pipe_right fmods (FStar_List.map Prims.fst))
in ((_195_33), (env)))
in FStar_Util.Inr (_195_34))
in (codegen _195_35))
in (finished_message module_names_and_times (Prims.parse_int "0")))))
end)))
end else begin
(

let _97_97 = (FStar_Stratified.batch_mode_tc verify_mode filenames)
in (match (_97_97) with
| (fmods, dsenv, env) -> begin
(

let module_names_and_times = (FStar_All.pipe_right fmods (FStar_List.map (fun _97_100 -> (match (_97_100) with
| (x, t) -> begin
(((FStar_Stratified.module_or_interface_name x)), (t))
end))))
in (

let _97_102 = (report_errors module_names_and_times)
in (

let _97_104 = (let _195_39 = (let _195_38 = (let _195_37 = (FStar_All.pipe_right fmods (FStar_List.map Prims.fst))
in ((_195_37), (env)))
in FStar_Util.Inl (_195_38))
in (codegen _195_39))
in (finished_message module_names_and_times (Prims.parse_int "0")))))
end))
end)
end else begin
(FStar_Util.print_error "no file provided\n")
end
end
end
end
end
end)
end)))


let main = (fun _97_106 -> (match (()) with
| () -> begin
try
(match (()) with
| () -> begin
(

let _97_125 = (go ())
in (

let _97_127 = (cleanup ())
in (FStar_All.exit (Prims.parse_int "0"))))
end)
with
| e -> begin
(

let _97_115 = (

let _97_111 = if (FStar_Absyn_Util.handleable e) then begin
(FStar_Absyn_Util.handle_err false () e)
end else begin
()
end
in (

let _97_113 = if (FStar_TypeChecker_Errors.handleable e) then begin
(FStar_TypeChecker_Errors.handle_err false e)
end else begin
()
end
in if (FStar_Options.trace_error ()) then begin
(let _195_44 = (FStar_Util.message_of_exn e)
in (let _195_43 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" _195_44 _195_43)))
end else begin
if (not (((FStar_Absyn_Util.handleable e) || (FStar_TypeChecker_Errors.handleable e)))) then begin
(let _195_45 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _195_45))
end else begin
()
end
end))
in (

let _97_117 = (cleanup ())
in (

let _97_119 = (let _195_46 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _195_46 Prims.ignore))
in (

let _97_121 = (report_errors [])
in (FStar_All.exit (Prims.parse_int "1"))))))
end
end))




