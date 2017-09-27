
open Prims
open FStar_Pervasives

let uu___234 : Prims.unit = (FStar_Version.dummy ())


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
in (match ((Prims.op_disEquality opt FStar_Pervasives_Native.None)) with
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


let gen_native_tactics : (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  Prims.unit = (fun uu____251 out_dir -> (match (uu____251) with
| (umods, env) -> begin
((FStar_Options.set_option "codegen" (FStar_Options.String ("OCaml")));
(

let mllibs = (

let uu____271 = (

let uu____280 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____280 umods))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____271))
in (

let mllibs1 = (FStar_List.flatten mllibs)
in ((FStar_List.iter (FStar_Extraction_ML_PrintML.print (FStar_Pervasives_Native.Some (out_dir)) ".ml") mllibs1);
(

let user_tactics_modules1 = FStar_Universal.user_tactics_modules
in (

let uu____308 = (FStar_ST.op_Bang user_tactics_modules1)
in (FStar_Tactics_Load.compile_modules out_dir uu____308)));
)));
)
end))


let go : 'Auu____347 . 'Auu____347  ->  Prims.unit = (fun uu____351 -> (

let uu____352 = (process_args ())
in (match (uu____352) with
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

let uu____367 = (

let uu____368 = (FStar_Options.dep ())
in (Prims.op_disEquality uu____368 FStar_Pervasives_Native.None))
in (match (uu____367) with
| true -> begin
(

let uu____373 = (FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames)
in (FStar_Parser_Dep.print uu____373))
end
| uu____400 -> begin
(

let uu____401 = (FStar_Options.interactive ())
in (match (uu____401) with
| true -> begin
((

let uu____403 = (FStar_Options.explicit_deps ())
in (match (uu____403) with
| true -> begin
((FStar_Util.print_error "--explicit_deps incompatible with --in\n");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____405 -> begin
()
end));
(match ((Prims.op_disEquality (FStar_List.length filenames) (Prims.parse_int "1"))) with
| true -> begin
((FStar_Util.print_error "fstar-mode.el should pass the current filename to F*\n");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____408 -> begin
()
end);
(

let filename = (FStar_List.hd filenames)
in ((

let uu____411 = (

let uu____412 = (FStar_Options.verify_module ())
in (Prims.op_disEquality uu____412 []))
in (match (uu____411) with
| true -> begin
(FStar_Util.print_warning "Interactive mode; ignoring --verify_module")
end
| uu____417 -> begin
()
end));
(

let uu____418 = (FStar_Options.legacy_interactive ())
in (match (uu____418) with
| true -> begin
(FStar_Legacy_Interactive.interactive_mode filename)
end
| uu____419 -> begin
(FStar_Interactive.interactive_mode filename)
end));
));
)
end
| uu____420 -> begin
(

let uu____421 = (FStar_Options.doc ())
in (match (uu____421) with
| true -> begin
(FStar_Fsdoc_Generator.generate filenames)
end
| uu____422 -> begin
(

let uu____423 = (FStar_Options.indent ())
in (match (uu____423) with
| true -> begin
(match (FStar_Platform.is_fstar_compiler_using_ocaml) with
| true -> begin
(FStar_Indent.generate filenames)
end
| uu____424 -> begin
(failwith "You seem to be using the F#-generated version ofthe compiler ; reindenting is not known to work yet with this version")
end)
end
| uu____425 -> begin
(match (((FStar_List.length filenames) >= (Prims.parse_int "1"))) with
| true -> begin
(

let verify_mode = (

let uu____427 = (FStar_Options.verify_all ())
in (match (uu____427) with
| true -> begin
((

let uu____429 = (

let uu____430 = (FStar_Options.verify_module ())
in (Prims.op_disEquality uu____430 []))
in (match (uu____429) with
| true -> begin
((FStar_Util.print_error "--verify_module is incompatible with --verify_all");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____436 -> begin
()
end));
FStar_Parser_Dep.VerifyAll;
)
end
| uu____437 -> begin
(

let uu____438 = (

let uu____439 = (FStar_Options.verify_module ())
in (Prims.op_disEquality uu____439 []))
in (match (uu____438) with
| true -> begin
FStar_Parser_Dep.VerifyUserList
end
| uu____444 -> begin
FStar_Parser_Dep.VerifyFigureItOut
end))
end))
in (

let filenames1 = (FStar_Dependencies.find_deps_if_needed verify_mode filenames)
in ((

let uu____449 = (FStar_Options.gen_native_tactics ())
in (match (uu____449) with
| FStar_Pervasives_Native.Some (dir) -> begin
((FStar_Util.print1 "Generating native tactics in %s\n" dir);
(FStar_Options.set_option "lax" (FStar_Options.Bool (true)));
)
end
| FStar_Pervasives_Native.None -> begin
()
end));
(

let uu____455 = (FStar_Options.use_native_tactics ())
in (match (uu____455) with
| FStar_Pervasives_Native.Some (dir) -> begin
((FStar_Util.print1 "Using native tactics from %s\n" dir);
(FStar_Tactics_Load.load_tactics_dir dir);
)
end
| FStar_Pervasives_Native.None -> begin
()
end));
(

let uu____461 = (FStar_Options.load ())
in (FStar_Tactics_Load.load_tactics uu____461));
(

let uu____464 = (FStar_Universal.batch_mode_tc filenames1)
in (match (uu____464) with
| (fmods, dsenv, env) -> begin
(

let module_names_and_times = (FStar_All.pipe_right fmods (FStar_List.map (fun uu____534 -> (match (uu____534) with
| (x, t) -> begin
(((FStar_Universal.module_or_interface_name x)), (t))
end))))
in ((report_errors module_names_and_times);
(

let uu____555 = (

let uu____562 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Pervasives_Native.fst))
in ((uu____562), (env)))
in (codegen uu____555));
(

let uu____580 = (FStar_Options.gen_native_tactics ())
in (match (uu____580) with
| FStar_Pervasives_Native.Some (dir) -> begin
(

let uu____584 = (

let uu____591 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Pervasives_Native.fst))
in ((uu____591), (env)))
in (gen_native_tactics uu____584 dir))
end
| FStar_Pervasives_Native.None -> begin
()
end));
(finished_message module_names_and_times (Prims.parse_int "0"));
))
end));
)))
end
| uu____608 -> begin
(FStar_Util.print_error "no file provided\n")
end)
end))
end))
end))
end))
end)
end)))


let main : 'Auu____613 . Prims.unit  ->  'Auu____613 = (fun uu____617 -> (FStar_All.try_with (fun uu___236_621 -> (match (()) with
| () -> begin
((go ());
(cleanup ());
(FStar_All.exit (Prims.parse_int "0"));
)
end)) (fun uu___235_630 -> (match (uu___235_630) with
| e -> begin
(

let trace = (FStar_Util.trace_of_exn e)
in ((match ((FStar_Errors.handleable e)) with
| true -> begin
(FStar_Errors.err_exn e)
end
| uu____635 -> begin
()
end);
(

let uu____636 = (FStar_Options.trace_error ())
in (match (uu____636) with
| true -> begin
(

let uu____637 = (FStar_Util.message_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____637 trace))
end
| uu____638 -> begin
(match ((not ((FStar_Errors.handleable e)))) with
| true -> begin
(

let uu____639 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" uu____639))
end
| uu____640 -> begin
()
end)
end));
(cleanup ());
(report_errors []);
(FStar_All.exit (Prims.parse_int "1"));
))
end))))




