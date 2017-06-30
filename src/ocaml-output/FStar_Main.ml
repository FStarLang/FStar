
open Prims
open FStar_Pervasives

let uu___228 : Prims.unit = (FStar_Version.dummy ())


let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____6 -> (FStar_Options.parse_cmd_line ()))


let cleanup : Prims.unit  ->  Prims.unit = (fun uu____12 -> (FStar_Util.kill_all ()))


let finished_message : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  Prims.int  ->  Prims.unit = (fun fmods errs -> (

let print_to = (match ((errs > (Prims.parse_int "0"))) with
| true -> begin
FStar_Util.print_error
end
| uu____34 -> begin
FStar_Util.print_string
end)
in (

let uu____35 = (

let uu____36 = (FStar_Options.silent ())
in (not (uu____36)))
in (match (uu____35) with
| true -> begin
((FStar_All.pipe_right fmods (FStar_List.iter (fun uu____47 -> (match (uu____47) with
| ((iface1, name), time) -> begin
(

let tag = (match (iface1) with
| true -> begin
"i\'face (or impl+i\'face)"
end
| uu____58 -> begin
"module"
end)
in (

let uu____59 = (FStar_Options.should_print_message name.FStar_Ident.str)
in (match (uu____59) with
| true -> begin
(match ((time >= (Prims.parse_int "0"))) with
| true -> begin
(

let uu____60 = (

let uu____61 = (FStar_Util.string_of_int time)
in (FStar_Util.format3 "Verified %s: %s (%s milliseconds)\n" tag (FStar_Ident.text_of_lid name) uu____61))
in (print_to uu____60))
end
| uu____62 -> begin
(

let uu____63 = (FStar_Util.format2 "Verified %s: %s\n" tag (FStar_Ident.text_of_lid name))
in (print_to uu____63))
end)
end
| uu____64 -> begin
()
end)))
end))));
(match ((errs > (Prims.parse_int "0"))) with
| true -> begin
(match ((errs = (Prims.parse_int "1"))) with
| true -> begin
(FStar_Util.print_error "1 error was reported (see above)\n")
end
| uu____65 -> begin
(

let uu____66 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" uu____66))
end)
end
| uu____67 -> begin
(

let uu____68 = (

let uu____69 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" uu____69))
in (FStar_Util.print_string uu____68))
end);
)
end
| uu____70 -> begin
()
end))))


let report_errors : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  Prims.unit = (fun fmods -> ((

let uu____85 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____85 FStar_Pervasives.ignore));
(

let nerrs = (FStar_Errors.get_err_count ())
in (match ((nerrs > (Prims.parse_int "0"))) with
| true -> begin
((finished_message fmods nerrs);
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____91 -> begin
()
end));
))


let codegen : (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env)  ->  Prims.unit = (fun uu____97 -> (match (uu____97) with
| (umods, env) -> begin
(

let opt = (FStar_Options.codegen ())
in (match ((opt <> FStar_Pervasives_Native.None)) with
| true -> begin
(

let mllibs = (

let uu____111 = (

let uu____116 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____116 umods))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____111))
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
| uu____129 -> begin
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

let uu____137 = (FStar_List.map FStar_Extraction_Kremlin.translate mllibs1)
in (FStar_List.flatten uu____137))
in (

let bin = ((FStar_Extraction_Kremlin.current_version), (programs))
in (

let uu____143 = (FStar_Options.prepend_output_dir "out.krml")
in (FStar_Util.save_value_to_file uu____143 bin))))
end
| uu____144 -> begin
(failwith "Unrecognized option")
end))))
end
| uu____146 -> begin
()
end))
end))


let go = (fun uu____153 -> (

let uu____154 = (process_args ())
in (match (uu____154) with
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

let uu____164 = (

let uu____165 = (FStar_Options.dep ())
in (uu____165 <> FStar_Pervasives_Native.None))
in (match (uu____164) with
| true -> begin
(

let uu____168 = (FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames)
in (FStar_Parser_Dep.print uu____168))
end
| uu____182 -> begin
(

let uu____183 = (FStar_Options.interactive ())
in (match (uu____183) with
| true -> begin
((

let uu____185 = (FStar_Options.explicit_deps ())
in (match (uu____185) with
| true -> begin
((FStar_Util.print_error "--explicit_deps incompatible with --in\n");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____187 -> begin
()
end));
(match (((FStar_List.length filenames) <> (Prims.parse_int "1"))) with
| true -> begin
((FStar_Util.print_error "fstar-mode.el should pass the current filename to F*\n");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____192 -> begin
()
end);
(

let filename = (FStar_List.hd filenames)
in ((

let uu____195 = (

let uu____196 = (FStar_Options.verify_module ())
in (uu____196 <> []))
in (match (uu____195) with
| true -> begin
(FStar_Util.print_warning "Interactive mode; ignoring --verify_module")
end
| uu____199 -> begin
()
end));
(

let uu____200 = (FStar_Options.legacy_interactive ())
in (match (uu____200) with
| true -> begin
(FStar_Legacy_Interactive.interactive_mode filename)
end
| uu____201 -> begin
(FStar_Interactive.interactive_mode filename)
end));
));
)
end
| uu____202 -> begin
(

let uu____203 = (FStar_Options.doc ())
in (match (uu____203) with
| true -> begin
(FStar_Fsdoc_Generator.generate filenames)
end
| uu____204 -> begin
(

let uu____205 = (FStar_Options.indent ())
in (match (uu____205) with
| true -> begin
(match (FStar_Platform.is_fstar_compiler_using_ocaml) with
| true -> begin
(FStar_Indent.generate filenames)
end
| uu____206 -> begin
(failwith "You seem to be using the F#-generated version ofthe compiler ; reindenting is not known to work yet with this version")
end)
end
| uu____207 -> begin
(match (((FStar_List.length filenames) >= (Prims.parse_int "1"))) with
| true -> begin
(

let verify_mode = (

let uu____212 = (FStar_Options.verify_all ())
in (match (uu____212) with
| true -> begin
((

let uu____214 = (

let uu____215 = (FStar_Options.verify_module ())
in (uu____215 <> []))
in (match (uu____214) with
| true -> begin
((FStar_Util.print_error "--verify_module is incompatible with --verify_all");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____219 -> begin
()
end));
FStar_Parser_Dep.VerifyAll;
)
end
| uu____220 -> begin
(

let uu____221 = (

let uu____222 = (FStar_Options.verify_module ())
in (uu____222 <> []))
in (match (uu____221) with
| true -> begin
FStar_Parser_Dep.VerifyUserList
end
| uu____225 -> begin
FStar_Parser_Dep.VerifyFigureItOut
end))
end))
in (

let filenames1 = (FStar_Dependencies.find_deps_if_needed verify_mode filenames)
in (

let uu____228 = (FStar_Universal.batch_mode_tc filenames1)
in (match (uu____228) with
| (fmods, dsenv, env) -> begin
(

let module_names_and_times = (FStar_All.pipe_right fmods (FStar_List.map (fun uu____264 -> (match (uu____264) with
| (x, t) -> begin
(((FStar_Universal.module_or_interface_name x)), (t))
end))))
in ((report_errors module_names_and_times);
(

let uu____277 = (

let uu____281 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Pervasives_Native.fst))
in ((uu____281), (env)))
in (codegen uu____277));
(finished_message module_names_and_times (Prims.parse_int "0"));
))
end))))
end
| uu____290 -> begin
(FStar_Util.print_error "no file provided\n")
end)
end))
end))
end))
end))
end)
end)))


let main = (fun uu____297 -> try
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
| uu____306 -> begin
()
end);
(

let uu____307 = (FStar_Options.trace_error ())
in (match (uu____307) with
| true -> begin
(

let uu____308 = (FStar_Util.message_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____308 trace))
end
| uu____309 -> begin
(match ((not ((FStar_Errors.handleable e)))) with
| true -> begin
(

let uu____310 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" uu____310))
end
| uu____311 -> begin
()
end)
end));
(cleanup ());
(report_errors []);
(FStar_All.exit (Prims.parse_int "1"));
))
end)




