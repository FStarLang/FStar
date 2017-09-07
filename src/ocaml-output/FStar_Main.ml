
open Prims
open FStar_Pervasives

let uu___224 : Prims.unit = (FStar_Version.dummy ())


let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____10 -> (FStar_Options.parse_cmd_line ()))


let cleanup : Prims.unit  ->  Prims.unit = (fun uu____20 -> (FStar_Util.kill_all ()))


let finished_message : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  Prims.int  ->  Prims.unit = (fun fmods errs -> (

let print_to = (match ((errs > (Prims.parse_int "0"))) with
| true -> begin
FStar_Util.print_error
end
| uu____54 -> begin
FStar_Util.print_string
end)
in (

let uu____55 = (

let uu____56 = (FStar_Options.silent ())
in (not (uu____56)))
in (match (uu____55) with
| true -> begin
((FStar_All.pipe_right fmods (FStar_List.iter (fun uu____83 -> (match (uu____83) with
| ((iface1, name), time) -> begin
(

let tag = (match (iface1) with
| true -> begin
"i\'face (or impl+i\'face)"
end
| uu____100 -> begin
"module"
end)
in (

let uu____101 = (FStar_Options.should_print_message name.FStar_Ident.str)
in (match (uu____101) with
| true -> begin
(match ((time >= (Prims.parse_int "0"))) with
| true -> begin
(

let uu____102 = (

let uu____103 = (FStar_Util.string_of_int time)
in (FStar_Util.format3 "Verified %s: %s (%s milliseconds)\n" tag (FStar_Ident.text_of_lid name) uu____103))
in (print_to uu____102))
end
| uu____104 -> begin
(

let uu____105 = (FStar_Util.format2 "Verified %s: %s\n" tag (FStar_Ident.text_of_lid name))
in (print_to uu____105))
end)
end
| uu____106 -> begin
()
end)))
end))));
(match ((errs > (Prims.parse_int "0"))) with
| true -> begin
(match ((errs = (Prims.parse_int "1"))) with
| true -> begin
(FStar_Util.print_error "1 error was reported (see above)\n")
end
| uu____107 -> begin
(

let uu____108 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" uu____108))
end)
end
| uu____109 -> begin
(

let uu____110 = (

let uu____111 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" uu____111))
in (FStar_Util.print_string uu____110))
end);
)
end
| uu____112 -> begin
()
end))))


let report_errors : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  Prims.unit = (fun fmods -> ((

let uu____138 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____138 FStar_Pervasives.ignore));
(

let nerrs = (FStar_Errors.get_err_count ())
in (match ((nerrs > (Prims.parse_int "0"))) with
| true -> begin
((finished_message fmods nerrs);
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____147 -> begin
()
end));
))


let codegen : (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env)  ->  Prims.unit = (fun uu____157 -> (match (uu____157) with
| (umods, env) -> begin
(

let opt = (FStar_Options.codegen ())
in (match ((opt <> FStar_Pervasives_Native.None)) with
| true -> begin
(

let mllibs = (

let uu____180 = (

let uu____189 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____189 umods))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____180))
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
| uu____212 -> begin
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

let uu____224 = (FStar_List.map FStar_Extraction_Kremlin.translate mllibs1)
in (FStar_List.flatten uu____224))
in (

let bin = ((FStar_Extraction_Kremlin.current_version), (programs))
in (

let uu____234 = (FStar_Options.prepend_output_dir "out.krml")
in (FStar_Util.save_value_to_file uu____234 bin))))
end
| uu____235 -> begin
(failwith "Unrecognized option")
end))))
end
| uu____238 -> begin
()
end))
end))


let go : 'Auu____243 . 'Auu____243  ->  Prims.unit = (fun uu____247 -> (

let uu____248 = (process_args ())
in (match (uu____248) with
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

let uu____263 = (

let uu____264 = (FStar_Options.dep ())
in (uu____264 <> FStar_Pervasives_Native.None))
in (match (uu____263) with
| true -> begin
(

let uu____269 = (FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames)
in (FStar_Parser_Dep.print uu____269))
end
| uu____296 -> begin
(

let uu____297 = (FStar_Options.interactive ())
in (match (uu____297) with
| true -> begin
((

let uu____299 = (FStar_Options.explicit_deps ())
in (match (uu____299) with
| true -> begin
((FStar_Util.print_error "--explicit_deps incompatible with --in\n");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____301 -> begin
()
end));
(match (((FStar_List.length filenames) <> (Prims.parse_int "1"))) with
| true -> begin
((FStar_Util.print_error "fstar-mode.el should pass the current filename to F*\n");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____304 -> begin
()
end);
(

let filename = (FStar_List.hd filenames)
in ((

let uu____307 = (

let uu____308 = (FStar_Options.verify_module ())
in (uu____308 <> []))
in (match (uu____307) with
| true -> begin
(FStar_Util.print_warning "Interactive mode; ignoring --verify_module")
end
| uu____313 -> begin
()
end));
(

let uu____314 = (FStar_Options.legacy_interactive ())
in (match (uu____314) with
| true -> begin
(FStar_Legacy_Interactive.interactive_mode filename)
end
| uu____315 -> begin
(FStar_Interactive.interactive_mode filename)
end));
));
)
end
| uu____316 -> begin
(

let uu____317 = (FStar_Options.doc ())
in (match (uu____317) with
| true -> begin
(FStar_Fsdoc_Generator.generate filenames)
end
| uu____318 -> begin
(

let uu____319 = (FStar_Options.indent ())
in (match (uu____319) with
| true -> begin
(match (FStar_Platform.is_fstar_compiler_using_ocaml) with
| true -> begin
(FStar_Indent.generate filenames)
end
| uu____320 -> begin
(failwith "You seem to be using the F#-generated version ofthe compiler ; reindenting is not known to work yet with this version")
end)
end
| uu____321 -> begin
(match (((FStar_List.length filenames) >= (Prims.parse_int "1"))) with
| true -> begin
(

let verify_mode = (

let uu____323 = (FStar_Options.verify_all ())
in (match (uu____323) with
| true -> begin
((

let uu____325 = (

let uu____326 = (FStar_Options.verify_module ())
in (uu____326 <> []))
in (match (uu____325) with
| true -> begin
((FStar_Util.print_error "--verify_module is incompatible with --verify_all");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____332 -> begin
()
end));
FStar_Parser_Dep.VerifyAll;
)
end
| uu____333 -> begin
(

let uu____334 = (

let uu____335 = (FStar_Options.verify_module ())
in (uu____335 <> []))
in (match (uu____334) with
| true -> begin
FStar_Parser_Dep.VerifyUserList
end
| uu____340 -> begin
FStar_Parser_Dep.VerifyFigureItOut
end))
end))
in (

let filenames1 = (FStar_Dependencies.find_deps_if_needed verify_mode filenames)
in ((

let uu____345 = (FStar_Options.load ())
in (FStar_Tactics_Load.load_tactics uu____345));
(

let uu____348 = (FStar_Universal.batch_mode_tc filenames1)
in (match (uu____348) with
| (fmods, dsenv, env) -> begin
(

let module_names_and_times = (FStar_All.pipe_right fmods (FStar_List.map (fun uu____418 -> (match (uu____418) with
| (x, t) -> begin
(((FStar_Universal.module_or_interface_name x)), (t))
end))))
in ((report_errors module_names_and_times);
(

let uu____439 = (

let uu____446 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Pervasives_Native.fst))
in ((uu____446), (env)))
in (codegen uu____439));
(finished_message module_names_and_times (Prims.parse_int "0"));
))
end));
)))
end
| uu____463 -> begin
(FStar_Util.print_error "no file provided\n")
end)
end))
end))
end))
end))
end)
end)))


let main : 'Auu____468 . Prims.unit  ->  'Auu____468 = (fun uu____472 -> try
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
| uu____490 -> begin
()
end);
(

let uu____491 = (FStar_Options.trace_error ())
in (match (uu____491) with
| true -> begin
(

let uu____492 = (FStar_Util.message_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____492 trace))
end
| uu____493 -> begin
(match ((not ((FStar_Errors.handleable e)))) with
| true -> begin
(

let uu____494 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" uu____494))
end
| uu____495 -> begin
()
end)
end));
(cleanup ());
(report_errors []);
(FStar_All.exit (Prims.parse_int "1"));
))
end)




