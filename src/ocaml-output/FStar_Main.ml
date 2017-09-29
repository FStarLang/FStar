
open Prims
open FStar_Pervasives

let uu___270 : Prims.unit = (FStar_Version.dummy ())


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
(match ((Prims.op_Equality errs (Prims.parse_int "1"))) with
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

let uu____110 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.print1 "%s\n" uu____110))
end);
)
end
| uu____111 -> begin
()
end))))


let report_errors : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  Prims.unit = (fun fmods -> ((

let uu____137 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____137 FStar_Pervasives.ignore));
(

let nerrs = (FStar_Errors.get_err_count ())
in (match ((nerrs > (Prims.parse_int "0"))) with
| true -> begin
((finished_message fmods nerrs);
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____146 -> begin
()
end));
))


let codegen : (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env)  ->  Prims.unit = (fun uu____156 -> (match (uu____156) with
| (umods, env) -> begin
(

let opt = (FStar_Options.codegen ())
in (match ((Prims.op_disEquality opt FStar_Pervasives_Native.None)) with
| true -> begin
(

let mllibs = (

let uu____179 = (

let uu____188 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____188 umods))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____179))
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
| uu____211 -> begin
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

let uu____223 = (FStar_List.map FStar_Extraction_Kremlin.translate mllibs1)
in (FStar_List.flatten uu____223))
in (

let bin = ((FStar_Extraction_Kremlin.current_version), (programs))
in (

let uu____233 = (FStar_Options.prepend_output_dir "out.krml")
in (FStar_Util.save_value_to_file uu____233 bin))))
end
| uu____234 -> begin
(failwith "Unrecognized option")
end))))
end
| uu____237 -> begin
()
end))
end))


let gen_native_tactics : (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  Prims.unit = (fun uu____250 out_dir -> (match (uu____250) with
| (umods, env) -> begin
((FStar_Options.set_option "codegen" (FStar_Options.String ("OCaml")));
(

let mllibs = (

let uu____270 = (

let uu____279 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____279 umods))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____270))
in (

let mllibs1 = (FStar_List.flatten mllibs)
in ((FStar_List.iter (FStar_Extraction_ML_PrintML.print (FStar_Pervasives_Native.Some (out_dir)) ".ml") mllibs1);
(

let user_tactics_modules1 = FStar_Universal.user_tactics_modules
in (

let uu____307 = (FStar_ST.op_Bang user_tactics_modules1)
in (FStar_Tactics_Load.compile_modules out_dir uu____307)));
)));
)
end))


let init_native_tactics : Prims.unit  ->  Prims.unit = (fun uu____377 -> ((

let uu____379 = (FStar_Options.load ())
in (FStar_Tactics_Load.load_tactics uu____379));
(

let uu____382 = (FStar_Options.use_native_tactics ())
in (match (uu____382) with
| FStar_Pervasives_Native.Some (dir) -> begin
((FStar_Util.print1 "Using native tactics from %s\n" dir);
(FStar_Tactics_Load.load_tactics_dir dir);
)
end
| FStar_Pervasives_Native.None -> begin
()
end));
))


let go : 'Auu____391 . 'Auu____391  ->  Prims.unit = (fun uu____395 -> (

let uu____396 = (process_args ())
in (match (uu____396) with
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
((init_native_tactics ());
(

let uu____412 = (

let uu____413 = (FStar_Options.dep ())
in (Prims.op_disEquality uu____413 FStar_Pervasives_Native.None))
in (match (uu____412) with
| true -> begin
(

let uu____418 = (FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames)
in (FStar_Parser_Dep.print uu____418))
end
| uu____445 -> begin
(

let uu____446 = (FStar_Options.interactive ())
in (match (uu____446) with
| true -> begin
((

let uu____448 = (FStar_Options.explicit_deps ())
in (match (uu____448) with
| true -> begin
((FStar_Util.print_error "--explicit_deps incompatible with --in\n");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____450 -> begin
()
end));
(match ((Prims.op_disEquality (FStar_List.length filenames) (Prims.parse_int "1"))) with
| true -> begin
((FStar_Util.print_error "fstar-mode.el should pass the current filename to F*\n");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____453 -> begin
()
end);
(

let filename = (FStar_List.hd filenames)
in ((

let uu____456 = (

let uu____457 = (FStar_Options.verify_module ())
in (Prims.op_disEquality uu____457 []))
in (match (uu____456) with
| true -> begin
(FStar_Util.print_warning "Interactive mode; ignoring --verify_module")
end
| uu____462 -> begin
()
end));
(

let uu____463 = (FStar_Options.legacy_interactive ())
in (match (uu____463) with
| true -> begin
(FStar_Interactive_Legacy.interactive_mode filename)
end
| uu____464 -> begin
(FStar_Interactive_Ide.interactive_mode filename)
end));
));
)
end
| uu____465 -> begin
(

let uu____466 = (FStar_Options.doc ())
in (match (uu____466) with
| true -> begin
(FStar_Fsdoc_Generator.generate filenames)
end
| uu____467 -> begin
(

let uu____468 = (FStar_Options.indent ())
in (match (uu____468) with
| true -> begin
(match (FStar_Platform.is_fstar_compiler_using_ocaml) with
| true -> begin
(FStar_Indent.generate filenames)
end
| uu____469 -> begin
(failwith "You seem to be using the F#-generated version ofthe compiler ; reindenting is not known to work yet with this version")
end)
end
| uu____470 -> begin
(match (((FStar_List.length filenames) >= (Prims.parse_int "1"))) with
| true -> begin
(

let verify_mode = (

let uu____472 = (FStar_Options.verify_all ())
in (match (uu____472) with
| true -> begin
((

let uu____474 = (

let uu____475 = (FStar_Options.verify_module ())
in (Prims.op_disEquality uu____475 []))
in (match (uu____474) with
| true -> begin
((FStar_Util.print_error "--verify_module is incompatible with --verify_all");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____481 -> begin
()
end));
FStar_Parser_Dep.VerifyAll;
)
end
| uu____482 -> begin
(

let uu____483 = (

let uu____484 = (FStar_Options.verify_module ())
in (Prims.op_disEquality uu____484 []))
in (match (uu____483) with
| true -> begin
FStar_Parser_Dep.VerifyUserList
end
| uu____489 -> begin
FStar_Parser_Dep.VerifyFigureItOut
end))
end))
in (

let filenames1 = (FStar_Dependencies.find_deps_if_needed verify_mode filenames)
in ((

let uu____494 = (FStar_Options.gen_native_tactics ())
in (match (uu____494) with
| FStar_Pervasives_Native.Some (dir) -> begin
((FStar_Util.print1 "Generating native tactics in %s\n" dir);
(FStar_Options.set_option "lax" (FStar_Options.Bool (true)));
)
end
| FStar_Pervasives_Native.None -> begin
()
end));
(

let uu____499 = (FStar_Universal.batch_mode_tc filenames1)
in (match (uu____499) with
| (fmods, dsenv, env) -> begin
(

let module_names_and_times = (FStar_All.pipe_right fmods (FStar_List.map (fun uu____569 -> (match (uu____569) with
| (x, t) -> begin
(((FStar_Universal.module_or_interface_name x)), (t))
end))))
in ((report_errors module_names_and_times);
(

let uu____590 = (

let uu____597 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Pervasives_Native.fst))
in ((uu____597), (env)))
in (codegen uu____590));
(

let uu____615 = (FStar_Options.gen_native_tactics ())
in (match (uu____615) with
| FStar_Pervasives_Native.Some (dir) -> begin
(

let uu____619 = (

let uu____626 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Pervasives_Native.fst))
in ((uu____626), (env)))
in (gen_native_tactics uu____619 dir))
end
| FStar_Pervasives_Native.None -> begin
()
end));
(finished_message module_names_and_times (Prims.parse_int "0"));
))
end));
)))
end
| uu____643 -> begin
(FStar_Util.print_error "no file provided\n")
end)
end))
end))
end))
end));
)
end)
end)))


let main : 'Auu____648 . Prims.unit  ->  'Auu____648 = (fun uu____652 -> (FStar_All.try_with (fun uu___272_656 -> (match (()) with
| () -> begin
((go ());
(cleanup ());
(FStar_All.exit (Prims.parse_int "0"));
)
end)) (fun uu___271_665 -> (match (uu___271_665) with
| e -> begin
(

let trace = (FStar_Util.trace_of_exn e)
in ((match ((FStar_Errors.handleable e)) with
| true -> begin
(FStar_Errors.err_exn e)
end
| uu____670 -> begin
()
end);
(

let uu____671 = (FStar_Options.trace_error ())
in (match (uu____671) with
| true -> begin
(

let uu____672 = (FStar_Util.message_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____672 trace))
end
| uu____673 -> begin
(match ((not ((FStar_Errors.handleable e)))) with
| true -> begin
(

let uu____674 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" uu____674))
end
| uu____675 -> begin
()
end)
end));
(cleanup ());
(report_errors []);
(FStar_All.exit (Prims.parse_int "1"));
))
end))))




