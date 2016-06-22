
open Prims

let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun _90_1 -> (match (()) with
| () -> begin
(FStar_Options.parse_cmd_line ())
end))


let cleanup : Prims.unit  ->  Prims.unit = (fun _90_2 -> (match (()) with
| () -> begin
(FStar_Util.kill_all ())
end))


let report_errors : Prims.unit  ->  Prims.unit = (fun _90_3 -> (match (()) with
| () -> begin
(

let errs = if (FStar_Options.universes ()) then begin
(FStar_TypeChecker_Errors.get_err_count ())
end else begin
(FStar_Tc_Errors.get_err_count ())
end
in if (errs > 0) then begin
(

let _90_5 = (let _181_7 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" _181_7))
in (FStar_All.exit 1))
end else begin
()
end)
end))


let finished_message : (Prims.bool * FStar_Ident.lident) Prims.list  ->  Prims.unit = (fun fmods -> if (not ((FStar_Options.silent ()))) then begin
(

let _90_12 = (FStar_All.pipe_right fmods (FStar_List.iter (fun _90_10 -> (match (_90_10) with
| (iface, name) -> begin
(

let tag = if iface then begin
"i\'face"
end else begin
"module"
end
in if (FStar_Options.should_print_message name.FStar_Ident.str) then begin
(let _181_11 = (FStar_Util.format2 "Verifying %s: %s\n" tag (FStar_Ident.text_of_lid name))
in (FStar_Util.print_string _181_11))
end else begin
()
end)
end))))
in (let _181_13 = (let _181_12 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" _181_12))
in (FStar_Util.print_string _181_13)))
end else begin
()
end)


let codegen : ((FStar_Absyn_Syntax.modul Prims.list * FStar_Tc_Env.env), (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env)) FStar_Util.either  ->  Prims.unit = (fun uf_mods_env -> (

let opt = (FStar_Options.codegen ())
in if (opt <> None) then begin
(

let mllibs = (match (uf_mods_env) with
| FStar_Util.Inl (fmods, env) -> begin
(let _181_17 = (let _181_16 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _181_16 fmods))
in (FStar_All.pipe_left Prims.snd _181_17))
end
| FStar_Util.Inr (umods, env) -> begin
(let _181_19 = (let _181_18 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract _181_18 umods))
in (FStar_All.pipe_left Prims.snd _181_19))
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
| _90_33 -> begin
(FStar_All.failwith "Unrecognized option")
end)
in (match (opt) with
| (Some ("FSharp")) | (Some ("OCaml")) -> begin
(

let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun _90_42 -> (match (_90_42) with
| (n, d) -> begin
(let _181_22 = (FStar_Options.prepend_output_dir (Prims.strcat n ext))
in (let _181_21 = (FStar_Format.pretty 120 d)
in (FStar_Util.write_file _181_22 _181_21)))
end)) newDocs))
end
| Some ("Kremlin") -> begin
(

let programs = (let _181_23 = (FStar_List.map FStar_Extraction_Kremlin.translate mllibs)
in (FStar_List.flatten _181_23))
in (

let bin = (FStar_Extraction_Kremlin.current_version, programs)
in (FStar_Util.save_value_to_file "out.krml" bin)))
end
| _90_48 -> begin
(FStar_All.failwith "Unrecognized option")
end))))
end else begin
()
end))


let go = (fun _90_49 -> (

let _90_53 = (process_args ())
in (match (_90_53) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(

let _90_55 = (FStar_Options.display_usage ())
in (FStar_All.exit 0))
end
| FStar_Getopt.Die (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.GoOn -> begin
if ((FStar_Options.dep ()) <> None) then begin
(let _181_25 = (FStar_Parser_Dep.collect filenames)
in (FStar_Parser_Dep.print _181_25))
end else begin
if (FStar_Options.interactive ()) then begin
(

let filenames = if (FStar_Options.explicit_deps ()) then begin
(

let _90_60 = if ((FStar_List.length filenames) = 0) then begin
(FStar_Util.print_error "--explicit_deps was provided without a file list!\n")
end else begin
()
end
in filenames)
end else begin
(

let _90_62 = if ((FStar_List.length filenames) > 0) then begin
(FStar_Util.print_warning "ignoring the file list (no --explicit_deps)\n")
end else begin
()
end
in (FStar_Interactive.detect_dependencies_with_first_interactive_chunk ()))
end
in if (FStar_Options.universes ()) then begin
(

let _90_68 = (FStar_Universal.batch_mode_tc filenames)
in (match (_90_68) with
| (fmods, dsenv, env) -> begin
(FStar_Interactive.interactive_mode (dsenv, env) None FStar_Universal.interactive_tc)
end))
end else begin
(

let _90_72 = (FStar_Stratified.batch_mode_tc filenames)
in (match (_90_72) with
| (fmods, dsenv, env) -> begin
(FStar_Interactive.interactive_mode (dsenv, env) None FStar_Stratified.interactive_tc)
end))
end)
end else begin
if ((FStar_List.length filenames) >= 1) then begin
(

let _90_80 = if ((not ((FStar_Options.explicit_deps ()))) && (not (((FStar_Options.verify_module ()) <> [])))) then begin
(

let files = (FStar_List.map (fun f -> (match ((let _181_27 = (FStar_Util.basename f)
in (FStar_Parser_Dep.check_and_strip_suffix _181_27))) with
| None -> begin
(

let _90_75 = (FStar_Util.print1 "Unrecognized file type: %s\n" f)
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

let _90_85 = (FStar_Universal.batch_mode_tc filenames)
in (match (_90_85) with
| (fmods, dsenv, env) -> begin
(

let _90_86 = (report_errors ())
in (

let _90_88 = (codegen (FStar_Util.Inr ((fmods, env))))
in (let _181_28 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Universal.module_or_interface_name))
in (finished_message _181_28))))
end))
end else begin
(

let _90_93 = (FStar_Stratified.batch_mode_tc filenames)
in (match (_90_93) with
| (fmods, dsenv, env) -> begin
(

let _90_94 = (report_errors ())
in (

let _90_96 = (codegen (FStar_Util.Inl ((fmods, env))))
in (let _181_29 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Stratified.module_or_interface_name))
in (finished_message _181_29))))
end))
end)
end else begin
(FStar_Util.print_error "no file provided\n")
end
end
end
end)
end)))


let main = (fun _90_98 -> (match (()) with
| () -> begin
try
(match (()) with
| () -> begin
(

let _90_117 = (go ())
in (

let _90_119 = (cleanup ())
in (FStar_All.exit 0)))
end)
with
| e -> begin
(

let _90_107 = (

let _90_103 = if (FStar_Absyn_Util.handleable e) then begin
(FStar_Absyn_Util.handle_err false () e)
end else begin
()
end
in (

let _90_105 = if (FStar_Syntax_Util.handleable e) then begin
(FStar_Syntax_Util.handle_err false e)
end else begin
()
end
in if (FStar_Options.trace_error ()) then begin
(let _181_34 = (FStar_Util.message_of_exn e)
in (let _181_33 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" _181_34 _181_33)))
end else begin
if (not (((FStar_Absyn_Util.handleable e) || (FStar_Syntax_Util.handleable e)))) then begin
(let _181_35 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _181_35))
end else begin
()
end
end))
in (

let _90_109 = (cleanup ())
in (

let _90_111 = (let _181_36 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _181_36 Prims.ignore))
in (

let _90_113 = (report_errors ())
in (FStar_All.exit 1)))))
end
end))




