
open Prims

let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun _98_1 -> (match (()) with
| () -> begin
(FStar_Options.parse_cmd_line ())
end))


let cleanup : Prims.unit  ->  Prims.unit = (fun _98_2 -> (match (()) with
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

let _98_12 = (FStar_All.pipe_right fmods (FStar_List.iter (fun _98_10 -> (match (_98_10) with
| ((iface, name), time) -> begin
(

let tag = if iface then begin
"i\'face (or impl+i\'face)"
end else begin
"module"
end
in if (FStar_Options.should_print_message name.FStar_Ident.str) then begin
if (time >= (Prims.parse_int "0")) then begin
(let _197_13 = (let _197_12 = (FStar_Util.string_of_int time)
in (FStar_Util.format3 "Verified %s: %s (%s milliseconds)\n" tag (FStar_Ident.text_of_lid name) _197_12))
in (print_to _197_13))
end else begin
(let _197_14 = (FStar_Util.format2 "Verified %s: %s\n" tag (FStar_Ident.text_of_lid name))
in (print_to _197_14))
end
end else begin
()
end)
end))))
in if (errs > (Prims.parse_int "0")) then begin
if (errs = (Prims.parse_int "1")) then begin
(FStar_Util.print_error "1 error was reported (see above)\n")
end else begin
(let _197_15 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" _197_15))
end
end else begin
(let _197_17 = (let _197_16 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" _197_16))
in (FStar_Util.print_string _197_17))
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

let _98_16 = (finished_message fmods errs)
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
(let _197_23 = (let _197_22 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _197_22 fmods))
in (FStar_All.pipe_left Prims.snd _197_23))
end
| FStar_Util.Inr (umods, env) -> begin
(let _197_25 = (let _197_24 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract _197_24 umods))
in (FStar_All.pipe_left Prims.snd _197_25))
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
| _98_37 -> begin
(failwith "Unrecognized option")
end)
in (match (opt) with
| (Some ("FSharp")) | (Some ("OCaml")) -> begin
(

let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun _98_46 -> (match (_98_46) with
| (n, d) -> begin
(let _197_27 = (FStar_Options.prepend_output_dir (Prims.strcat n ext))
in (FStar_Util.write_file _197_27 (FStar_Format.pretty (Prims.parse_int "120") d)))
end)) newDocs))
end
| Some ("Kremlin") -> begin
(

let programs = (let _197_28 = (FStar_List.map FStar_Extraction_Kremlin.translate mllibs)
in (FStar_List.flatten _197_28))
in (

let bin = ((FStar_Extraction_Kremlin.current_version), (programs))
in (let _197_29 = (FStar_Options.prepend_output_dir "out.krml")
in (FStar_Util.save_value_to_file _197_29 bin))))
end
| _98_52 -> begin
(failwith "Unrecognized option")
end))))
end else begin
()
end))


let go = (fun _98_53 -> (

let _98_57 = (process_args ())
in (match (_98_57) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(

let _98_59 = (FStar_Options.display_usage ())
in (FStar_All.exit (Prims.parse_int "0")))
end
| FStar_Getopt.Error (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.Success -> begin
if ((FStar_Options.dep ()) <> None) then begin
(let _197_31 = (FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames)
in (FStar_Parser_Dep.print _197_31))
end else begin
if (FStar_Options.interactive ()) then begin
(

let _98_66 = if (FStar_Options.explicit_deps ()) then begin
(

let _98_64 = (FStar_Util.print_error "--explicit_deps incompatible with --in|n")
in (FStar_All.exit (Prims.parse_int "1")))
end else begin
()
end
in (

let _98_70 = if ((FStar_List.length filenames) <> (Prims.parse_int "1")) then begin
(

let _98_68 = (FStar_Util.print_error "fstar-mode.el should pass the current filename to F*\n")
in (FStar_All.exit (Prims.parse_int "1")))
end else begin
()
end
in (

let filename = (FStar_List.hd filenames)
in (

let try_convert_file_name_to_windows = (fun s -> try
(match (()) with
| () -> begin
(

let _98_87 = (FStar_Util.run_proc "which" "cygpath" "")
in (match (_98_87) with
| (_98_83, t_out, _98_86) -> begin
if (not (((FStar_Util.trim_string t_out) = "/usr/bin/cygpath"))) then begin
s
end else begin
(

let _98_93 = (FStar_Util.run_proc "cygpath" (Prims.strcat "-m " s) "")
in (match (_98_93) with
| (_98_89, t_out, _98_92) -> begin
(FStar_Util.trim_string t_out)
end))
end
end))
end)
with
| _98_79 -> begin
s
end)
in (

let filename = (try_convert_file_name_to_windows filename)
in (

let _98_95 = if ((FStar_Options.verify_module ()) <> []) then begin
(FStar_Util.print_warning "Interactive mode; ignoring --verify_module")
end else begin
()
end
in if (FStar_Options.universes ()) then begin
(FStar_Interactive.interactive_mode filename None FStar_Universal.interactive_tc)
end else begin
(FStar_Interactive.interactive_mode filename None FStar_Stratified.interactive_tc)
end))))))
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

let _98_99 = if ((FStar_Options.verify_module ()) <> []) then begin
(

let _98_97 = (FStar_Util.print_error "--verify_module is incompatible with --verify_all")
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

let filenames = (FStar_Dependencies.find_deps_if_needed verify_mode filenames)
in (

let _98_106 = (FStar_Universal.batch_mode_tc filenames)
in (match (_98_106) with
| (fmods, dsenv, env) -> begin
(

let module_names_and_times = (FStar_All.pipe_right fmods (FStar_List.map (fun _98_109 -> (match (_98_109) with
| (x, t) -> begin
(((FStar_Universal.module_or_interface_name x)), (t))
end))))
in (

let _98_111 = (report_errors module_names_and_times)
in (

let _98_113 = (let _197_39 = (let _197_38 = (let _197_37 = (FStar_All.pipe_right fmods (FStar_List.map Prims.fst))
in ((_197_37), (env)))
in FStar_Util.Inr (_197_38))
in (codegen _197_39))
in (finished_message module_names_and_times (Prims.parse_int "0")))))
end)))
end else begin
(

let _98_118 = (FStar_Stratified.batch_mode_tc verify_mode filenames)
in (match (_98_118) with
| (fmods, dsenv, env) -> begin
(

let module_names_and_times = (FStar_All.pipe_right fmods (FStar_List.map (fun _98_121 -> (match (_98_121) with
| (x, t) -> begin
(((FStar_Stratified.module_or_interface_name x)), (t))
end))))
in (

let _98_123 = (report_errors module_names_and_times)
in (

let _98_125 = (let _197_43 = (let _197_42 = (let _197_41 = (FStar_All.pipe_right fmods (FStar_List.map Prims.fst))
in ((_197_41), (env)))
in FStar_Util.Inl (_197_42))
in (codegen _197_43))
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


let main = (fun _98_127 -> (match (()) with
| () -> begin
try
(match (()) with
| () -> begin
(

let _98_146 = (go ())
in (

let _98_148 = (cleanup ())
in (FStar_All.exit (Prims.parse_int "0"))))
end)
with
| e -> begin
(

let _98_136 = (

let _98_132 = if (FStar_Absyn_Util.handleable e) then begin
(FStar_Absyn_Util.handle_err false () e)
end else begin
()
end
in (

let _98_134 = if (FStar_TypeChecker_Errors.handleable e) then begin
(FStar_TypeChecker_Errors.handle_err false e)
end else begin
()
end
in if (FStar_Options.trace_error ()) then begin
(let _197_48 = (FStar_Util.message_of_exn e)
in (let _197_47 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" _197_48 _197_47)))
end else begin
if (not (((FStar_Absyn_Util.handleable e) || (FStar_TypeChecker_Errors.handleable e)))) then begin
(let _197_49 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _197_49))
end else begin
()
end
end))
in (

let _98_138 = (cleanup ())
in (

let _98_140 = (let _197_50 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _197_50 Prims.ignore))
in (

let _98_142 = (report_errors [])
in (FStar_All.exit (Prims.parse_int "1"))))))
end
end))




