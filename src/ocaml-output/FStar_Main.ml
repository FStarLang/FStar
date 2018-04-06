
open Prims
open FStar_Pervasives

let uu___78 : Prims.unit = (FStar_Version.dummy ())


let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____9 -> (FStar_Options.parse_cmd_line ()))


let cleanup : Prims.unit  ->  Prims.unit = (fun uu____18 -> (FStar_Util.kill_all ()))


let finished_message : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  Prims.int  ->  Prims.unit = (fun fmods errs -> (

let print_to = (match ((errs > (Prims.parse_int "0"))) with
| true -> begin
FStar_Util.print_error
end
| uu____50 -> begin
FStar_Util.print_string
end)
in (

let uu____51 = (

let uu____52 = (FStar_Options.silent ())
in (not (uu____52)))
in (match (uu____51) with
| true -> begin
((FStar_All.pipe_right fmods (FStar_List.iter (fun uu____79 -> (match (uu____79) with
| ((iface1, name), time) -> begin
(

let tag = (match (iface1) with
| true -> begin
"i\'face (or impl+i\'face)"
end
| uu____96 -> begin
"module"
end)
in (

let uu____97 = (FStar_Options.should_print_message name.FStar_Ident.str)
in (match (uu____97) with
| true -> begin
(match ((time >= (Prims.parse_int "0"))) with
| true -> begin
(

let uu____98 = (

let uu____99 = (FStar_Util.string_of_int time)
in (FStar_Util.format3 "Verified %s: %s (%s milliseconds)\n" tag (FStar_Ident.text_of_lid name) uu____99))
in (print_to uu____98))
end
| uu____100 -> begin
(

let uu____101 = (FStar_Util.format2 "Verified %s: %s\n" tag (FStar_Ident.text_of_lid name))
in (print_to uu____101))
end)
end
| uu____102 -> begin
()
end)))
end))));
(match ((errs > (Prims.parse_int "0"))) with
| true -> begin
(match ((Prims.op_Equality errs (Prims.parse_int "1"))) with
| true -> begin
(FStar_Util.print_error "1 error was reported (see above)\n")
end
| uu____103 -> begin
(

let uu____104 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" uu____104))
end)
end
| uu____105 -> begin
(

let uu____106 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.print1 "%s\n" uu____106))
end);
)
end
| uu____107 -> begin
()
end))))


let report_errors : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  Prims.unit = (fun fmods -> ((

let uu____132 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____132 FStar_Pervasives.ignore));
(

let nerrs = (FStar_Errors.get_err_count ())
in (match ((nerrs > (Prims.parse_int "0"))) with
| true -> begin
((finished_message fmods nerrs);
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____141 -> begin
()
end));
))


let codegen : (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env)  ->  Prims.unit = (fun uu____150 -> (match (uu____150) with
| (umods, env) -> begin
(

let opt = (FStar_Options.codegen ())
in (match ((Prims.op_disEquality opt FStar_Pervasives_Native.None)) with
| true -> begin
(

let mllibs = (

let uu____173 = (

let uu____182 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____182 umods))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____173))
in (

let mllibs1 = (FStar_List.flatten mllibs)
in (

let ext = (match (opt) with
| FStar_Pervasives_Native.Some (FStar_Options.FSharp) -> begin
".fs"
end
| FStar_Pervasives_Native.Some (FStar_Options.OCaml) -> begin
".ml"
end
| FStar_Pervasives_Native.Some (FStar_Options.Plugin) -> begin
".ml"
end
| FStar_Pervasives_Native.Some (FStar_Options.Kremlin) -> begin
".krml"
end
| uu____205 -> begin
(failwith "Unrecognized option")
end)
in (match (opt) with
| FStar_Pervasives_Native.Some (FStar_Options.FSharp) -> begin
(

let outdir = (FStar_Options.output_dir ())
in (FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext) mllibs1))
end
| FStar_Pervasives_Native.Some (FStar_Options.OCaml) -> begin
(

let outdir = (FStar_Options.output_dir ())
in (FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext) mllibs1))
end
| FStar_Pervasives_Native.Some (FStar_Options.Plugin) -> begin
(

let outdir = (FStar_Options.output_dir ())
in (FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext) mllibs1))
end
| FStar_Pervasives_Native.Some (FStar_Options.Kremlin) -> begin
(

let programs = (

let uu____220 = (FStar_List.map FStar_Extraction_Kremlin.translate mllibs1)
in (FStar_List.flatten uu____220))
in (

let bin = ((FStar_Extraction_Kremlin.current_version), (programs))
in (match (programs) with
| ((name, uu____231))::[] -> begin
(

let uu____240 = (FStar_Options.prepend_output_dir (Prims.strcat name ext))
in (FStar_Util.save_value_to_file uu____240 bin))
end
| uu____241 -> begin
(

let uu____244 = (FStar_Options.prepend_output_dir "out.krml")
in (FStar_Util.save_value_to_file uu____244 bin))
end)))
end
| uu____245 -> begin
(failwith "Unrecognized option")
end))))
end
| uu____248 -> begin
()
end))
end))


let load_native_tactics : Prims.unit  ->  Prims.unit = (fun uu____251 -> (

let modules_to_load = (

let uu____255 = (FStar_Options.load ())
in (FStar_All.pipe_right uu____255 (FStar_List.map FStar_Ident.lid_of_str)))
in (

let ml_module_name = (fun m -> (

let uu____266 = (FStar_Extraction_ML_Util.mlpath_of_lid m)
in (FStar_All.pipe_right uu____266 FStar_Extraction_ML_Util.flatten_mlpath)))
in (

let ml_file = (fun m -> (

let uu____283 = (ml_module_name m)
in (Prims.strcat uu____283 ".ml")))
in (

let cmxs_file = (fun m -> (

let cmxs = (

let uu____289 = (ml_module_name m)
in (Prims.strcat uu____289 ".cmxs"))
in (

let uu____290 = (FStar_Options.find_file cmxs)
in (match (uu____290) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let uu____294 = (

let uu____297 = (ml_file m)
in (FStar_Options.find_file uu____297))
in (match (uu____294) with
| FStar_Pervasives_Native.None -> begin
(

let uu____298 = (

let uu____303 = (

let uu____304 = (ml_file m)
in (FStar_Util.format1 "Failed to compile native tactic; extracted module %s not found" uu____304))
in ((FStar_Errors.Fatal_FailToCompileNativeTactic), (uu____303)))
in (FStar_Errors.raise_err uu____298))
end
| FStar_Pervasives_Native.Some (ml) -> begin
(

let dir = (FStar_Util.dirname ml)
in ((

let uu____308 = (

let uu____311 = (ml_module_name m)
in (uu____311)::[])
in (FStar_Tactics_Load.compile_modules dir uu____308));
(

let uu____312 = (FStar_Options.find_file cmxs)
in (match (uu____312) with
| FStar_Pervasives_Native.None -> begin
(

let uu____315 = (

let uu____320 = (FStar_Util.format1 "Failed to compile native tactic; compiled object %s not found" cmxs)
in ((FStar_Errors.Fatal_FailToCompileNativeTactic), (uu____320)))
in (FStar_Errors.raise_err uu____315))
end
| FStar_Pervasives_Native.Some (f) -> begin
f
end));
))
end))
end))))
in (

let cmxs_files = (FStar_All.pipe_right modules_to_load (FStar_List.map cmxs_file))
in ((FStar_List.iter (fun x -> (FStar_Util.print1 "cmxs file: %s\n" x)) cmxs_files);
(FStar_Tactics_Load.load_tactics cmxs_files);
)))))))


let init_warn_error : Prims.unit  ->  Prims.unit = (fun uu____334 -> (

let s = (FStar_Options.warn_error ())
in (match ((Prims.op_disEquality s "")) with
| true -> begin
(FStar_Parser_ParseIt.parse_warn_error s)
end
| uu____337 -> begin
()
end)))


let go : 'Auu____340 . 'Auu____340  ->  Prims.unit = (fun uu____344 -> (

let uu____345 = (process_args ())
in (match (uu____345) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
((FStar_Options.display_usage ());
(FStar_All.exit (Prims.parse_int "0"));
)
end
| FStar_Getopt.Error (msg) -> begin
((FStar_Util.print_string msg);
(FStar_All.exit (Prims.parse_int "1"));
)
end
| FStar_Getopt.Success -> begin
((load_native_tactics ());
(init_warn_error ());
(

let uu____363 = (

let uu____364 = (FStar_Options.dep ())
in (Prims.op_disEquality uu____364 FStar_Pervasives_Native.None))
in (match (uu____363) with
| true -> begin
(

let uu____369 = (FStar_Parser_Dep.collect filenames)
in (match (uu____369) with
| (uu____376, deps) -> begin
(FStar_Parser_Dep.print deps)
end))
end
| uu____382 -> begin
(

let uu____383 = ((FStar_Options.use_extracted_interfaces ()) && ((FStar_List.length filenames) > (Prims.parse_int "1")))
in (match (uu____383) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Error_TooManyFiles), ("Only one command line file is allowed if --use_extracted_interfaces is set")) FStar_Range.dummyRange)
end
| uu____384 -> begin
(

let uu____385 = (FStar_Options.interactive ())
in (match (uu____385) with
| true -> begin
(match (filenames) with
| [] -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_MissingFileName), ("--ide: Name of current file missing in command line invocation\n")));
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (uu____387)::(uu____388)::uu____389 -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_TooManyFiles), ("--ide: Too many files in command line invocation\n")));
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (filename)::[] -> begin
(

let uu____394 = (FStar_Options.legacy_interactive ())
in (match (uu____394) with
| true -> begin
(FStar_Interactive_Legacy.interactive_mode filename)
end
| uu____395 -> begin
(FStar_Interactive_Ide.interactive_mode filename)
end))
end)
end
| uu____396 -> begin
(

let uu____397 = (FStar_Options.doc ())
in (match (uu____397) with
| true -> begin
(FStar_Fsdoc_Generator.generate filenames)
end
| uu____398 -> begin
(

let uu____399 = (FStar_Options.indent ())
in (match (uu____399) with
| true -> begin
(match (FStar_Platform.is_fstar_compiler_using_ocaml) with
| true -> begin
(FStar_Indent.generate filenames)
end
| uu____400 -> begin
(failwith "You seem to be using the F#-generated version ofthe compiler ; reindenting is not known to work yet with this version")
end)
end
| uu____401 -> begin
(match (((FStar_List.length filenames) >= (Prims.parse_int "1"))) with
| true -> begin
(

let uu____402 = (FStar_Dependencies.find_deps_if_needed filenames)
in (match (uu____402) with
| (filenames1, dep_graph1) -> begin
(

let uu____415 = (FStar_Universal.batch_mode_tc filenames1 dep_graph1)
in (match (uu____415) with
| (fmods, env) -> begin
(

let module_names_and_times = (FStar_All.pipe_right fmods (FStar_List.map (fun uu____482 -> (match (uu____482) with
| (x, t) -> begin
(((FStar_Universal.module_or_interface_name x)), (t))
end))))
in ((report_errors module_names_and_times);
(

let uu____503 = (

let uu____510 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Pervasives_Native.fst))
in ((uu____510), (env)))
in (codegen uu____503));
(report_errors module_names_and_times);
(finished_message module_names_and_times (Prims.parse_int "0"));
))
end))
end))
end
| uu____528 -> begin
(FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_MissingFileName), ("no file provided\n")))
end)
end))
end))
end))
end))
end));
)
end)
end)))


let lazy_chooser : FStar_Syntax_Syntax.lazy_kind  ->  FStar_Syntax_Syntax.lazyinfo  ->  FStar_Syntax_Syntax.term = (fun k i -> (match (k) with
| FStar_Syntax_Syntax.BadLazy -> begin
(failwith "lazy chooser: got a BadLazy")
end
| FStar_Syntax_Syntax.Lazy_bv -> begin
(FStar_Reflection_Embeddings.unfold_lazy_bv i)
end
| FStar_Syntax_Syntax.Lazy_binder -> begin
(FStar_Reflection_Embeddings.unfold_lazy_binder i)
end
| FStar_Syntax_Syntax.Lazy_fvar -> begin
(FStar_Reflection_Embeddings.unfold_lazy_fvar i)
end
| FStar_Syntax_Syntax.Lazy_comp -> begin
(FStar_Reflection_Embeddings.unfold_lazy_comp i)
end
| FStar_Syntax_Syntax.Lazy_env -> begin
(FStar_Reflection_Embeddings.unfold_lazy_env i)
end
| FStar_Syntax_Syntax.Lazy_sigelt -> begin
(FStar_Reflection_Embeddings.unfold_lazy_sigelt i)
end
| FStar_Syntax_Syntax.Lazy_proofstate -> begin
(FStar_Tactics_Embedding.unfold_lazy_proofstate i)
end))


let main : 'Auu____537 . Prims.unit  ->  'Auu____537 = (fun uu____541 -> (FStar_All.try_with (fun uu___80_551 -> (match (()) with
| () -> begin
((FStar_ST.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser (FStar_Pervasives_Native.Some (lazy_chooser)));
(FStar_ST.op_Colon_Equals FStar_Syntax_Util.tts_f (FStar_Pervasives_Native.Some (FStar_Syntax_Print.term_to_string)));
(FStar_ST.op_Colon_Equals FStar_TypeChecker_Normalize.unembed_binder_knot (FStar_Pervasives_Native.Some (FStar_Reflection_Embeddings.unembed_binder)));
(

let uu____666 = (FStar_Util.record_time go)
in (match (uu____666) with
| (uu____671, time) -> begin
((

let uu____674 = (FStar_Options.query_stats ())
in (match (uu____674) with
| true -> begin
(

let uu____675 = (FStar_Util.string_of_int time)
in (

let uu____676 = (

let uu____677 = (FStar_Getopt.cmdline ())
in (FStar_String.concat " " uu____677))
in (FStar_Util.print2 "TOTAL TIME %s ms: %s\n" uu____675 uu____676)))
end
| uu____680 -> begin
()
end));
(cleanup ());
(FStar_All.exit (Prims.parse_int "0"));
)
end));
)
end)) (fun uu___79_688 -> (match (uu___79_688) with
| e -> begin
(

let trace = (FStar_Util.trace_of_exn e)
in ((match ((FStar_Errors.handleable e)) with
| true -> begin
(FStar_Errors.err_exn e)
end
| uu____693 -> begin
()
end);
(

let uu____694 = (FStar_Options.trace_error ())
in (match (uu____694) with
| true -> begin
(

let uu____695 = (FStar_Util.message_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____695 trace))
end
| uu____696 -> begin
(match ((not ((FStar_Errors.handleable e)))) with
| true -> begin
(

let uu____697 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" uu____697))
end
| uu____698 -> begin
()
end)
end));
(cleanup ());
(report_errors []);
(FStar_All.exit (Prims.parse_int "1"));
))
end))))




