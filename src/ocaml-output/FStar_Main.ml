
open Prims
open FStar_Pervasives

let uu___483 : unit = (FStar_Version.dummy ())


let process_args : unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____13 -> (FStar_Options.parse_cmd_line ()))


let cleanup : unit  ->  unit = (fun uu____26 -> (FStar_Util.kill_all ()))


let finished_message : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  Prims.int  ->  unit = (fun fmods errs -> (

let print_to = (match ((errs > (Prims.parse_int "0"))) with
| true -> begin
FStar_Util.print_error
end
| uu____76 -> begin
FStar_Util.print_string
end)
in (

let uu____78 = (

let uu____80 = (FStar_Options.silent ())
in (not (uu____80)))
in (match (uu____78) with
| true -> begin
((FStar_All.pipe_right fmods (FStar_List.iter (fun uu____113 -> (match (uu____113) with
| ((iface1, name), time) -> begin
(

let tag = (match (iface1) with
| true -> begin
"i\'face (or impl+i\'face)"
end
| uu____141 -> begin
"module"
end)
in (

let uu____144 = (FStar_Options.should_print_message name.FStar_Ident.str)
in (match (uu____144) with
| true -> begin
(match ((time >= (Prims.parse_int "0"))) with
| true -> begin
(

let uu____149 = (

let uu____151 = (FStar_Ident.text_of_lid name)
in (

let uu____153 = (FStar_Util.string_of_int time)
in (FStar_Util.format3 "Verified %s: %s (%s milliseconds)\n" tag uu____151 uu____153)))
in (print_to uu____149))
end
| uu____156 -> begin
(

let uu____158 = (

let uu____160 = (FStar_Ident.text_of_lid name)
in (FStar_Util.format2 "Verified %s: %s\n" tag uu____160))
in (print_to uu____158))
end)
end
| uu____163 -> begin
()
end)))
end))));
(match ((errs > (Prims.parse_int "0"))) with
| true -> begin
(match ((Prims.op_Equality errs (Prims.parse_int "1"))) with
| true -> begin
(FStar_Util.print_error "1 error was reported (see above)\n")
end
| uu____171 -> begin
(

let uu____173 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" uu____173))
end)
end
| uu____176 -> begin
(

let uu____178 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.print1 "%s\n" uu____178))
end);
)
end
| uu____182 -> begin
()
end))))


let report_errors : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  unit = (fun fmods -> ((

let uu____215 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____215 (fun a1 -> ())));
(

let nerrs = (FStar_Errors.get_err_count ())
in (match ((nerrs > (Prims.parse_int "0"))) with
| true -> begin
((finished_message fmods nerrs);
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____226 -> begin
()
end));
))


let load_native_tactics : unit  ->  unit = (fun uu____233 -> (

let modules_to_load = (

let uu____237 = (FStar_Options.load ())
in (FStar_All.pipe_right uu____237 (FStar_List.map FStar_Ident.lid_of_str)))
in (

let ml_module_name = (fun m -> (

let uu____254 = (FStar_Extraction_ML_Util.mlpath_of_lid m)
in (FStar_All.pipe_right uu____254 FStar_Extraction_ML_Util.flatten_mlpath)))
in (

let ml_file = (fun m -> (

let uu____279 = (ml_module_name m)
in (Prims.strcat uu____279 ".ml")))
in (

let cmxs_file = (fun m -> (

let cmxs = (

let uu____291 = (ml_module_name m)
in (Prims.strcat uu____291 ".cmxs"))
in (

let uu____294 = (FStar_Options.find_file cmxs)
in (match (uu____294) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let uu____303 = (

let uu____307 = (ml_file m)
in (FStar_Options.find_file uu____307))
in (match (uu____303) with
| FStar_Pervasives_Native.None -> begin
(

let uu____311 = (

let uu____317 = (

let uu____319 = (ml_file m)
in (FStar_Util.format1 "Failed to compile native tactic; extracted module %s not found" uu____319))
in ((FStar_Errors.Fatal_FailToCompileNativeTactic), (uu____317)))
in (FStar_Errors.raise_err uu____311))
end
| FStar_Pervasives_Native.Some (ml) -> begin
(

let dir = (FStar_Util.dirname ml)
in ((

let uu____330 = (

let uu____334 = (ml_module_name m)
in (uu____334)::[])
in (FStar_Tactics_Load.compile_modules dir uu____330));
(

let uu____338 = (FStar_Options.find_file cmxs)
in (match (uu____338) with
| FStar_Pervasives_Native.None -> begin
(

let uu____344 = (

let uu____350 = (FStar_Util.format1 "Failed to compile native tactic; compiled object %s not found" cmxs)
in ((FStar_Errors.Fatal_FailToCompileNativeTactic), (uu____350)))
in (FStar_Errors.raise_err uu____344))
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


let init_warn_error : unit  ->  unit = (fun uu____379 -> (

let s = (FStar_Options.warn_error ())
in (match ((Prims.op_disEquality s "")) with
| true -> begin
(FStar_Parser_ParseIt.parse_warn_error s)
end
| uu____386 -> begin
()
end)))


let fstar_files : Prims.string Prims.list FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let go : 'Auu____420 . 'Auu____420  ->  unit = (fun uu____425 -> (

let uu____426 = (process_args ())
in (match (uu____426) with
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
((FStar_ST.op_Colon_Equals fstar_files (FStar_Pervasives_Native.Some (filenames)));
(load_native_tactics ());
(init_warn_error ());
(

let uu____483 = (

let uu____485 = (FStar_Options.dep ())
in (Prims.op_disEquality uu____485 FStar_Pervasives_Native.None))
in (match (uu____483) with
| true -> begin
(

let uu____494 = (FStar_Parser_Dep.collect filenames)
in (match (uu____494) with
| (uu____502, deps) -> begin
(FStar_Parser_Dep.print deps)
end))
end
| uu____510 -> begin
(

let uu____512 = (((FStar_Options.use_extracted_interfaces ()) && (

let uu____515 = (FStar_Options.expose_interfaces ())
in (not (uu____515)))) && ((FStar_List.length filenames) > (Prims.parse_int "1")))
in (match (uu____512) with
| true -> begin
(

let uu____520 = (

let uu____526 = (

let uu____528 = (FStar_Util.string_of_int (FStar_List.length filenames))
in (Prims.strcat "Only one command line file is allowed if --use_extracted_interfaces is set, found " uu____528))
in ((FStar_Errors.Error_TooManyFiles), (uu____526)))
in (FStar_Errors.raise_error uu____520 FStar_Range.dummyRange))
end
| uu____533 -> begin
(

let uu____535 = (FStar_Options.interactive ())
in (match (uu____535) with
| true -> begin
(match (filenames) with
| [] -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_MissingFileName), ("--ide: Name of current file missing in command line invocation\n")));
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (uu____543)::(uu____544)::uu____545 -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_TooManyFiles), ("--ide: Too many files in command line invocation\n")));
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (filename)::[] -> begin
(

let uu____561 = (FStar_Options.legacy_interactive ())
in (match (uu____561) with
| true -> begin
(FStar_Interactive_Legacy.interactive_mode filename)
end
| uu____564 -> begin
(FStar_Interactive_Ide.interactive_mode filename)
end))
end)
end
| uu____566 -> begin
(

let uu____568 = (FStar_Options.doc ())
in (match (uu____568) with
| true -> begin
(FStar_Fsdoc_Generator.generate filenames)
end
| uu____571 -> begin
(

let uu____573 = ((FStar_Options.print ()) || (FStar_Options.print_in_place ()))
in (match (uu____573) with
| true -> begin
(match (FStar_Platform.is_fstar_compiler_using_ocaml) with
| true -> begin
(FStar_Prettyprint.generate FStar_Prettyprint.ToTempFile filenames)
end
| uu____577 -> begin
(failwith "You seem to be using the F#-generated version ofthe compiler ; reindenting is not known to work yet with this version")
end)
end
| uu____580 -> begin
(match (((FStar_List.length filenames) >= (Prims.parse_int "1"))) with
| true -> begin
(

let uu____585 = (FStar_Dependencies.find_deps_if_needed filenames)
in (match (uu____585) with
| (filenames1, dep_graph1) -> begin
(

let uu____601 = (FStar_Universal.batch_mode_tc filenames1 dep_graph1)
in (match (uu____601) with
| (tcrs, env, delta_env) -> begin
(

let module_names_and_times = (FStar_All.pipe_right tcrs (FStar_List.map (fun tcr -> (((FStar_Universal.module_or_interface_name tcr.FStar_Universal.checked_module)), (tcr.FStar_Universal.tc_time)))))
in ((report_errors module_names_and_times);
(finished_message module_names_and_times (Prims.parse_int "0"));
))
end))
end))
end
| uu____679 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Error_MissingFileName), ("No file provided")) FStar_Range.dummyRange)
end)
end))
end))
end))
end))
end));
)
end)
end)))


let lazy_chooser : FStar_Syntax_Syntax.lazy_kind  ->  FStar_Syntax_Syntax.lazyinfo  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun k i -> (match (k) with
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
end
| FStar_Syntax_Syntax.Lazy_goal -> begin
(FStar_Tactics_Embedding.unfold_lazy_goal i)
end
| FStar_Syntax_Syntax.Lazy_uvar -> begin
(FStar_Syntax_Util.exp_string "((uvar))")
end
| FStar_Syntax_Syntax.Lazy_embedding (uu____702, t) -> begin
(FStar_Common.force_thunk t)
end))


let setup_hooks : unit  ->  unit = (fun uu____759 -> ((FStar_ST.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser (FStar_Pervasives_Native.Some (lazy_chooser)));
(FStar_ST.op_Colon_Equals FStar_Syntax_Util.tts_f (FStar_Pervasives_Native.Some (FStar_Syntax_Print.term_to_string)));
(FStar_ST.op_Colon_Equals FStar_TypeChecker_Normalize.unembed_binder_knot (FStar_Pervasives_Native.Some (FStar_Reflection_Embeddings.e_binder)));
))


let handle_error : Prims.exn  ->  unit = (fun e -> ((match ((FStar_Errors.handleable e)) with
| true -> begin
(FStar_Errors.err_exn e)
end
| uu____875 -> begin
()
end);
(

let uu____878 = (FStar_Options.trace_error ())
in (match (uu____878) with
| true -> begin
(

let uu____881 = (FStar_Util.message_of_exn e)
in (

let uu____883 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____881 uu____883)))
end
| uu____886 -> begin
(match ((not ((FStar_Errors.handleable e)))) with
| true -> begin
(

let uu____889 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" uu____889))
end
| uu____892 -> begin
()
end)
end));
(cleanup ());
(report_errors []);
))


let main : unit  ->  unit = (fun uu____910 -> (FStar_All.try_with (fun uu___485_920 -> (match (()) with
| () -> begin
((setup_hooks ());
(

let uu____922 = (FStar_Util.record_time go)
in (match (uu____922) with
| (uu____928, time) -> begin
(

let uu____932 = ((FStar_Options.print ()) || (FStar_Options.print_in_place ()))
in (match (uu____932) with
| true -> begin
(

let uu____935 = (FStar_ST.op_Bang fstar_files)
in (match (uu____935) with
| FStar_Pervasives_Native.Some (filenames) -> begin
(

let printing_mode = (

let uu____978 = (FStar_Options.print ())
in (match (uu____978) with
| true -> begin
FStar_Prettyprint.FromTempToStdout
end
| uu____981 -> begin
FStar_Prettyprint.FromTempToFile
end))
in (FStar_Prettyprint.generate printing_mode filenames))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Util.print_error "Internal error: List of source files not properly set");
(

let uu____989 = (FStar_Options.query_stats ())
in (match (uu____989) with
| true -> begin
(

let uu____992 = (FStar_Util.string_of_int time)
in (

let uu____994 = (

let uu____996 = (FStar_Getopt.cmdline ())
in (FStar_String.concat " " uu____996))
in (FStar_Util.print2 "TOTAL TIME %s ms: %s\n" uu____992 uu____994)))
end
| uu____1002 -> begin
()
end));
(cleanup ());
(FStar_All.exit (Prims.parse_int "0"));
)
end))
end
| uu____1006 -> begin
()
end))
end));
)
end)) (fun uu___484_1010 -> ((handle_error uu___484_1010);
(FStar_All.exit (Prims.parse_int "1"));
))))




