
open Prims

let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun _92_1 -> (match (()) with
| () -> begin
(FStar_Options.parse_cmd_line ())
end))


let cleanup : Prims.unit  ->  Prims.unit = (fun _92_2 -> (match (()) with
| () -> begin
(FStar_Util.kill_all ())
end))


let report_errors : Prims.unit  ->  Prims.unit = (fun _92_3 -> (match (()) with
| () -> begin
(

let errs = if (FStar_Options.universes ()) then begin
(FStar_TypeChecker_Errors.get_err_count ())
end else begin
(FStar_Tc_Errors.get_err_count ())
end
in if (errs > (Prims.parse_int "0")) then begin
(

let _92_5 = (let _185_7 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" _185_7))
in (FStar_All.exit (Prims.parse_int "1")))
end else begin
()
end)
end))


let finished_message : (Prims.bool * FStar_Ident.lident) Prims.list  ->  Prims.unit = (fun fmods -> if (not ((FStar_Options.silent ()))) then begin
(

let _92_12 = (FStar_All.pipe_right fmods (FStar_List.iter (fun _92_10 -> (match (_92_10) with
| (iface, name) -> begin
(

let tag = if iface then begin
"i\'face"
end else begin
"module"
end
in if (FStar_Options.should_print_message name.FStar_Ident.str) then begin
(let _185_11 = (FStar_Util.format2 "Verifying %s: %s\n" tag (FStar_Ident.text_of_lid name))
in (FStar_Util.print_string _185_11))
end else begin
()
end)
end))))
in (let _185_13 = (let _185_12 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" _185_12))
in (FStar_Util.print_string _185_13)))
end else begin
()
end)


let codegen : ((FStar_Absyn_Syntax.modul Prims.list * FStar_Tc_Env.env), (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env)) FStar_Util.either  ->  Prims.unit = (fun uf_mods_env -> (

let opt = (FStar_Options.codegen ())
in if (opt <> None) then begin
(

let mllibs = (match (uf_mods_env) with
| FStar_Util.Inl (fmods, env) -> begin
(let _185_17 = (let _185_16 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _185_16 fmods))
in (FStar_All.pipe_left Prims.snd _185_17))
end
| FStar_Util.Inr (umods, env) -> begin
(let _185_19 = (let _185_18 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract _185_18 umods))
in (FStar_All.pipe_left Prims.snd _185_19))
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
| _92_33 -> begin
(FStar_All.failwith "Unrecognized option")
end)
in (match (opt) with
| (Some ("FSharp")) | (Some ("OCaml")) -> begin
(

let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun _92_42 -> (match (_92_42) with
| (n, d) -> begin
(let _185_22 = (FStar_Options.prepend_output_dir (Prims.strcat n ext))
in (let _185_21 = (FStar_Format.pretty (Prims.parse_int "120") d)
in (FStar_Util.write_file _185_22 _185_21)))
end)) newDocs))
end
| Some ("Kremlin") -> begin
(

let programs = (let _185_23 = (FStar_List.map FStar_Extraction_Kremlin.translate mllibs)
in (FStar_List.flatten _185_23))
in (

let bin = ((FStar_Extraction_Kremlin.current_version), (programs))
in (FStar_Util.save_value_to_file "out.krml" bin)))
end
| _92_48 -> begin
(FStar_All.failwith "Unrecognized option")
end))))
end else begin
()
end))


let go = (fun _92_49 -> (

let _92_53 = (process_args ())
in (match (_92_53) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(

let _92_55 = (FStar_Options.display_usage ())
in (FStar_All.exit (Prims.parse_int "0")))
end
| FStar_Getopt.Error (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.Success -> begin
if ((FStar_Options.dep ()) <> None) then begin
(let _185_25 = (FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames)
in (FStar_Parser_Dep.print _185_25))
end else begin
if (FStar_Options.interactive ()) then begin
(

let _92_69 = if (FStar_Options.explicit_deps ()) then begin
(

let _92_60 = if ((FStar_List.length filenames) = (Prims.parse_int "0")) then begin
(FStar_Util.print_error "--explicit_deps was provided without a file list!\n")
end else begin
()
end
in ((None), (filenames)))
end else begin
(

let _92_62 = if ((FStar_List.length filenames) > (Prims.parse_int "0")) then begin
(FStar_Util.print_warning "ignoring the file list (no --explicit_deps)\n")
end else begin
()
end
in (

let _92_66 = (FStar_Interactive.detect_dependencies_with_first_interactive_chunk ())
in (match (_92_66) with
| (fn, deps) -> begin
((Some (fn)), (deps))
end)))
end
in (match (_92_69) with
| (main_buffer_filename_opt, filenames) -> begin
if (FStar_Options.universes ()) then begin
(

let _92_73 = (FStar_Universal.batch_mode_tc FStar_Parser_Dep.VerifyUserList filenames)
in (match (_92_73) with
| (fmods, dsenv, env) -> begin
(FStar_Interactive.interactive_mode main_buffer_filename_opt ((dsenv), (env)) None FStar_Universal.interactive_tc)
end))
end else begin
(

let _92_77 = (FStar_Stratified.batch_mode_tc FStar_Parser_Dep.VerifyUserList filenames)
in (match (_92_77) with
| (fmods, dsenv, env) -> begin
(FStar_Interactive.interactive_mode None ((dsenv), (env)) None FStar_Stratified.interactive_tc)
end))
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

let _92_80 = if ((FStar_Options.verify_module ()) <> []) then begin
(

let _92_78 = (FStar_Util.print_error "--verify_module is incompatible with --verify_all")
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

let _92_86 = (FStar_Universal.batch_mode_tc verify_mode filenames)
in (match (_92_86) with
| (fmods, dsenv, env) -> begin
(

let _92_87 = (report_errors ())
in (

let _92_89 = (codegen (FStar_Util.Inr (((fmods), (env)))))
in (let _185_26 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Universal.module_or_interface_name))
in (finished_message _185_26))))
end))
end else begin
(

let _92_94 = (FStar_Stratified.batch_mode_tc verify_mode filenames)
in (match (_92_94) with
| (fmods, dsenv, env) -> begin
(

let _92_95 = (report_errors ())
in (

let _92_97 = (codegen (FStar_Util.Inl (((fmods), (env)))))
in (let _185_27 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Stratified.module_or_interface_name))
in (finished_message _185_27))))
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


let main = (fun _92_99 -> (match (()) with
| () -> begin
try
(match (()) with
| () -> begin
(

let _92_118 = (go ())
in (

let _92_120 = (cleanup ())
in (FStar_All.exit (Prims.parse_int "0"))))
end)
with
| e -> begin
(

let _92_108 = (

let _92_104 = if (FStar_Absyn_Util.handleable e) then begin
(FStar_Absyn_Util.handle_err false () e)
end else begin
()
end
in (

let _92_106 = if (FStar_Syntax_Util.handleable e) then begin
(FStar_Syntax_Util.handle_err false e)
end else begin
()
end
in if (FStar_Options.trace_error ()) then begin
(let _185_32 = (FStar_Util.message_of_exn e)
in (let _185_31 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" _185_32 _185_31)))
end else begin
if (not (((FStar_Absyn_Util.handleable e) || (FStar_Syntax_Util.handleable e)))) then begin
(let _185_33 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _185_33))
end else begin
()
end
end))
in (

let _92_110 = (cleanup ())
in (

let _92_112 = (let _185_34 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _185_34 Prims.ignore))
in (

let _92_114 = (report_errors ())
in (FStar_All.exit (Prims.parse_int "1"))))))
end
end))




