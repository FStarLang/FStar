
open Prims
open FStar_Pervasives

let uu___213 : Prims.unit = (FStar_Version.dummy ())


let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____7 -> (FStar_Options.parse_cmd_line ()))


let cleanup : Prims.unit  ->  Prims.unit = (fun uu____14 -> (FStar_Util.kill_all ()))


let finished_message : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  Prims.int  ->  Prims.unit = (fun fmods errs -> (

let print_to = (match ((errs > (Prims.parse_int "0"))) with
| true -> begin
FStar_Util.print_error
end
| uu____38 -> begin
FStar_Util.print_string
end)
in (

let uu____39 = (

let uu____40 = (FStar_Options.silent ())
in (not (uu____40)))
in (match (uu____39) with
| true -> begin
((FStar_All.pipe_right fmods (FStar_List.iter (fun uu____58 -> (match (uu____58) with
| ((iface1, name), time) -> begin
(

let tag = (match (iface1) with
| true -> begin
"i\'face (or impl+i\'face)"
end
| uu____69 -> begin
"module"
end)
in (

let uu____70 = (FStar_Options.should_print_message name.FStar_Ident.str)
in (match (uu____70) with
| true -> begin
(match ((time >= (Prims.parse_int "0"))) with
| true -> begin
(

let uu____71 = (

let uu____72 = (FStar_Util.string_of_int time)
in (FStar_Util.format3 "Verified %s: %s (%s milliseconds)\n" tag (FStar_Ident.text_of_lid name) uu____72))
in (print_to uu____71))
end
| uu____73 -> begin
(

let uu____74 = (FStar_Util.format2 "Verified %s: %s\n" tag (FStar_Ident.text_of_lid name))
in (print_to uu____74))
end)
end
| uu____75 -> begin
()
end)))
end))));
(match ((errs > (Prims.parse_int "0"))) with
| true -> begin
(match ((errs = (Prims.parse_int "1"))) with
| true -> begin
(FStar_Util.print_error "1 error was reported (see above)\n")
end
| uu____76 -> begin
(

let uu____77 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" uu____77))
end)
end
| uu____78 -> begin
(

let uu____79 = (

let uu____80 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" uu____80))
in (FStar_Util.print_string uu____79))
end);
)
end
| uu____81 -> begin
()
end))))


let report_errors : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  Prims.unit = (fun fmods -> ((

let uu____97 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____97 FStar_Pervasives.ignore));
(

let nerrs = (FStar_Errors.get_err_count ())
in (match ((nerrs > (Prims.parse_int "0"))) with
| true -> begin
((finished_message fmods nerrs);
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____103 -> begin
()
end));
))


let codegen : (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env)  ->  Prims.unit = (fun uu____110 -> (match (uu____110) with
| (umods, env) -> begin
(

let opt = (FStar_Options.codegen ())
in (match ((opt <> FStar_Pervasives_Native.None)) with
| true -> begin
(

let mllibs = (

let uu____124 = (

let uu____129 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____129 umods))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____124))
in (

let mllibs1 = (FStar_List.flatten mllibs)
in (

let ext = (match (opt) with
| FStar_Pervasives_Native.Some ("FSharp") -> begin
".fs"
end
| FStar_Pervasives_Native.Some ("OCaml") -> begin
".ml"
end
| FStar_Pervasives_Native.Some ("Kremlin") -> begin
".krml"
end
| uu____142 -> begin
(failwith "Unrecognized option")
end)
in (match (opt) with
| FStar_Pervasives_Native.Some ("FSharp") -> begin
(

let outdir = (FStar_Options.output_dir ())
in (FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext) mllibs1))
end
| FStar_Pervasives_Native.Some ("OCaml") -> begin
(

let outdir = (FStar_Options.output_dir ())
in (FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext) mllibs1))
end
| FStar_Pervasives_Native.Some ("Kremlin") -> begin
(

let programs = (

let uu____150 = (FStar_List.map FStar_Extraction_Kremlin.translate mllibs1)
in (FStar_List.flatten uu____150))
in (

let bin = ((FStar_Extraction_Kremlin.current_version), (programs))
in (

let uu____156 = (FStar_Options.prepend_output_dir "out.krml")
in (FStar_Util.save_value_to_file uu____156 bin))))
end
| uu____157 -> begin
(failwith "Unrecognized option")
end))))
end
| uu____159 -> begin
()
end))
end))


let go = (fun uu____168 -> (

let uu____169 = (process_args ())
in (match (uu____169) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
((FStar_Options.display_usage ());
(FStar_All.exit (Prims.parse_int "0"));
)
end
| FStar_Getopt.Error (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.Success -> begin
(

let uu____179 = (

let uu____180 = (FStar_Options.dep ())
in (uu____180 <> FStar_Pervasives_Native.None))
in (match (uu____179) with
| true -> begin
(

let uu____183 = (FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames)
in (FStar_Parser_Dep.print uu____183))
end
| uu____197 -> begin
(

let uu____198 = (FStar_Options.interactive ())
in (match (uu____198) with
| true -> begin
((

let uu____200 = (FStar_Options.explicit_deps ())
in (match (uu____200) with
| true -> begin
((FStar_Util.print_error "--explicit_deps incompatible with --in\n");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____202 -> begin
()
end));
(match (((FStar_List.length filenames) <> (Prims.parse_int "1"))) with
| true -> begin
((FStar_Util.print_error "fstar-mode.el should pass the current filename to F*\n");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____209 -> begin
()
end);
(

let filename = (FStar_List.hd filenames)
in ((

let uu____212 = (

let uu____213 = (FStar_Options.verify_module ())
in (uu____213 <> []))
in (match (uu____212) with
| true -> begin
(FStar_Util.print_warning "Interactive mode; ignoring --verify_module")
end
| uu____216 -> begin
()
end));
(

let uu____217 = (FStar_Options.legacy_interactive ())
in (match (uu____217) with
| true -> begin
(FStar_Legacy_Interactive.interactive_mode filename)
end
| uu____218 -> begin
(FStar_Interactive.interactive_mode filename)
end));
));
)
end
| uu____219 -> begin
(

let uu____220 = (FStar_Options.doc ())
in (match (uu____220) with
| true -> begin
(FStar_Fsdoc_Generator.generate filenames)
end
| uu____221 -> begin
(

let uu____222 = (FStar_Options.indent ())
in (match (uu____222) with
| true -> begin
(match (FStar_Platform.is_fstar_compiler_using_ocaml) with
| true -> begin
(FStar_Indent.generate filenames)
end
| uu____223 -> begin
(failwith "You seem to be using the F#-generated version ofthe compiler ; reindenting is not known to work yet with this version")
end)
end
| uu____224 -> begin
(match (((FStar_List.length filenames) >= (Prims.parse_int "1"))) with
| true -> begin
(

let verify_mode = (

let uu____232 = (FStar_Options.verify_all ())
in (match (uu____232) with
| true -> begin
((

let uu____234 = (

let uu____235 = (FStar_Options.verify_module ())
in (uu____235 <> []))
in (match (uu____234) with
| true -> begin
((FStar_Util.print_error "--verify_module is incompatible with --verify_all");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____239 -> begin
()
end));
FStar_Parser_Dep.VerifyAll;
)
end
| uu____240 -> begin
(

let uu____241 = (

let uu____242 = (FStar_Options.verify_module ())
in (uu____242 <> []))
in (match (uu____241) with
| true -> begin
FStar_Parser_Dep.VerifyUserList
end
| uu____245 -> begin
FStar_Parser_Dep.VerifyFigureItOut
end))
end))
in (

let filenames1 = (FStar_Dependencies.find_deps_if_needed verify_mode filenames)
in ((

let uu____249 = (FStar_Options.load ())
in (FStar_Tactics_Load.load_tactics uu____249));
(

let uu____251 = (FStar_Universal.batch_mode_tc filenames1)
in (match (uu____251) with
| (fmods, dsenv, env) -> begin
(

let module_names_and_times = (FStar_All.pipe_right fmods (FStar_List.map (fun uu____290 -> (match (uu____290) with
| (x, t) -> begin
(((FStar_Universal.module_or_interface_name x)), (t))
end))))
in ((report_errors module_names_and_times);
(

let uu____303 = (

let uu____307 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Pervasives_Native.fst))
in ((uu____307), (env)))
in (codegen uu____303));
(finished_message module_names_and_times (Prims.parse_int "0"));
))
end));
)))
end
| uu____316 -> begin
(FStar_Util.print_error "no file provided\n")
end)
end))
end))
end))
end))
end)
end)))


let main = (fun uu____325 -> try
(match (()) with
| () -> begin
((go ());
(cleanup ());
(FStar_All.exit (Prims.parse_int "0"));
)
end)
with
| e -> begin
(

let trace = (FStar_Util.trace_of_exn e)
in ((match ((FStar_Errors.handleable e)) with
| true -> begin
(FStar_Errors.err_exn e)
end
| uu____343 -> begin
()
end);
(

let uu____344 = (FStar_Options.trace_error ())
in (match (uu____344) with
| true -> begin
(

let uu____345 = (FStar_Util.message_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____345 trace))
end
| uu____346 -> begin
(match ((not ((FStar_Errors.handleable e)))) with
| true -> begin
(

let uu____347 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" uu____347))
end
| uu____348 -> begin
()
end)
end));
(cleanup ());
(report_errors []);
(FStar_All.exit (Prims.parse_int "1"));
))
end)




