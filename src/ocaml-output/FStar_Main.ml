
open Prims

let uu___220 : Prims.unit = (FStar_Version.dummy ())


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
| ((iface, name), time) -> begin
(

let tag = (match (iface) with
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


let report_errors : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  Prims.unit = (fun fmods -> (

let errs = (FStar_Errors.get_err_count ())
in (match ((errs > (Prims.parse_int "0"))) with
| true -> begin
((finished_message fmods errs);
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____86 -> begin
()
end)))


let codegen : (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env)  ->  Prims.unit = (fun uu____92 -> (match (uu____92) with
| (umods, env) -> begin
(

let opt = (FStar_Options.codegen ())
in (match ((opt <> None)) with
| true -> begin
(

let mllibs = (

let uu____106 = (

let uu____111 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____111 umods))
in (FStar_All.pipe_left Prims.snd uu____106))
in (

let mllibs1 = (FStar_List.flatten mllibs)
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
| uu____124 -> begin
(failwith "Unrecognized option")
end)
in (match (opt) with
| (Some ("FSharp")) | (Some ("OCaml")) -> begin
(

let outdir = (FStar_Options.output_dir ())
in (FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext) mllibs1))
end
| Some ("Kremlin") -> begin
(

let programs = (

let uu____130 = (FStar_List.map FStar_Extraction_Kremlin.translate mllibs1)
in (FStar_List.flatten uu____130))
in (

let bin = ((FStar_Extraction_Kremlin.current_version), (programs))
in (

let uu____136 = (FStar_Options.prepend_output_dir "out.krml")
in (FStar_Util.save_value_to_file uu____136 bin))))
end
| uu____137 -> begin
(failwith "Unrecognized option")
end))))
end
| uu____139 -> begin
()
end))
end))


let go = (fun uu____146 -> (

let uu____147 = (process_args ())
in (match (uu____147) with
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

let uu____157 = (

let uu____158 = (FStar_Options.dep ())
in (uu____158 <> None))
in (match (uu____157) with
| true -> begin
(

let uu____161 = (FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames)
in (FStar_Parser_Dep.print uu____161))
end
| uu____175 -> begin
(

let uu____176 = (FStar_Options.interactive ())
in (match (uu____176) with
| true -> begin
((

let uu____178 = (FStar_Options.explicit_deps ())
in (match (uu____178) with
| true -> begin
((FStar_Util.print_error "--explicit_deps incompatible with --in|n");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____180 -> begin
()
end));
(match (((FStar_List.length filenames) <> (Prims.parse_int "1"))) with
| true -> begin
((FStar_Util.print_error "fstar-mode.el should pass the current filename to F*\n");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____185 -> begin
()
end);
(

let filename = (FStar_List.hd filenames)
in ((

let uu____188 = (

let uu____189 = (FStar_Options.verify_module ())
in (uu____189 <> []))
in (match (uu____188) with
| true -> begin
(FStar_Util.print_warning "Interactive mode; ignoring --verify_module")
end
| uu____192 -> begin
()
end));
(FStar_Interactive.interactive_mode filename);
));
)
end
| uu____193 -> begin
(

let uu____194 = (FStar_Options.doc ())
in (match (uu____194) with
| true -> begin
(FStar_Fsdoc_Generator.generate filenames)
end
| uu____195 -> begin
(

let uu____196 = (FStar_Options.indent ())
in (match (uu____196) with
| true -> begin
(match (FStar_Platform.is_fstar_compiler_using_ocaml) with
| true -> begin
(FStar_Indent.generate filenames)
end
| uu____197 -> begin
(failwith "You seem to be using the F#-generated version ofthe compiler ; reindenting is not known to work yet with this version")
end)
end
| uu____198 -> begin
(match (((FStar_List.length filenames) >= (Prims.parse_int "1"))) with
| true -> begin
(

let verify_mode = (

let uu____203 = (FStar_Options.verify_all ())
in (match (uu____203) with
| true -> begin
((

let uu____205 = (

let uu____206 = (FStar_Options.verify_module ())
in (uu____206 <> []))
in (match (uu____205) with
| true -> begin
((FStar_Util.print_error "--verify_module is incompatible with --verify_all");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____210 -> begin
()
end));
FStar_Parser_Dep.VerifyAll;
)
end
| uu____211 -> begin
(

let uu____212 = (

let uu____213 = (FStar_Options.verify_module ())
in (uu____213 <> []))
in (match (uu____212) with
| true -> begin
FStar_Parser_Dep.VerifyUserList
end
| uu____216 -> begin
FStar_Parser_Dep.VerifyFigureItOut
end))
end))
in (

let filenames1 = (FStar_Dependencies.find_deps_if_needed verify_mode filenames)
in (

let uu____219 = (FStar_Universal.batch_mode_tc filenames1)
in (match (uu____219) with
| (fmods, dsenv, env) -> begin
(

let module_names_and_times = (FStar_All.pipe_right fmods (FStar_List.map (fun uu____255 -> (match (uu____255) with
| (x, t) -> begin
(((FStar_Universal.module_or_interface_name x)), (t))
end))))
in ((report_errors module_names_and_times);
(

let uu____268 = (

let uu____272 = (FStar_All.pipe_right fmods (FStar_List.map Prims.fst))
in ((uu____272), (env)))
in (codegen uu____268));
(finished_message module_names_and_times (Prims.parse_int "0"));
))
end))))
end
| uu____281 -> begin
(FStar_Util.print_error "no file provided\n")
end)
end))
end))
end))
end))
end)
end)))


let main = (fun uu____288 -> try
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
(FStar_Errors.handle_err false e)
end
| uu____297 -> begin
()
end);
(

let uu____298 = (FStar_Options.trace_error ())
in (match (uu____298) with
| true -> begin
(

let uu____299 = (FStar_Util.message_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____299 trace))
end
| uu____300 -> begin
(match ((not ((FStar_Errors.handleable e)))) with
| true -> begin
(

let uu____301 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" uu____301))
end
| uu____302 -> begin
()
end)
end));
(cleanup ());
(

let uu____305 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____305 Prims.ignore));
(report_errors []);
(FStar_All.exit (Prims.parse_int "1"));
))
end)




