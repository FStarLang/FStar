
open Prims
open FStar_Pervasives

let uu___0 : unit = (FStar_Version.dummy ())


let process_args : unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____12 -> (FStar_Options.parse_cmd_line ()))


let cleanup : unit  ->  unit = (fun uu____25 -> (FStar_Util.kill_all ()))


let finished_message : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  Prims.int  ->  unit = (fun fmods errs -> (

let print_to = (match ((errs > (Prims.parse_int "0"))) with
| true -> begin
FStar_Util.print_error
end
| uu____75 -> begin
FStar_Util.print_string
end)
in (

let uu____77 = (

let uu____79 = (FStar_Options.silent ())
in (not (uu____79)))
in (match (uu____77) with
| true -> begin
((FStar_All.pipe_right fmods (FStar_List.iter (fun uu____112 -> (match (uu____112) with
| ((iface1, name), time) -> begin
(

let tag = (match (iface1) with
| true -> begin
"i\'face (or impl+i\'face)"
end
| uu____140 -> begin
"module"
end)
in (

let uu____143 = (FStar_Options.should_print_message name.FStar_Ident.str)
in (match (uu____143) with
| true -> begin
(match ((time >= (Prims.parse_int "0"))) with
| true -> begin
(

let uu____148 = (

let uu____150 = (FStar_Ident.text_of_lid name)
in (

let uu____152 = (FStar_Util.string_of_int time)
in (FStar_Util.format3 "Verified %s: %s (%s milliseconds)\n" tag uu____150 uu____152)))
in (print_to uu____148))
end
| uu____155 -> begin
(

let uu____157 = (

let uu____159 = (FStar_Ident.text_of_lid name)
in (FStar_Util.format2 "Verified %s: %s\n" tag uu____159))
in (print_to uu____157))
end)
end
| uu____162 -> begin
()
end)))
end))));
(match ((errs > (Prims.parse_int "0"))) with
| true -> begin
(match ((Prims.op_Equality errs (Prims.parse_int "1"))) with
| true -> begin
(FStar_Util.print_error "1 error was reported (see above)\n")
end
| uu____170 -> begin
(

let uu____172 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" uu____172))
end)
end
| uu____175 -> begin
(

let uu____177 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.print1 "%s\n" uu____177))
end);
)
end
| uu____181 -> begin
()
end))))


let report_errors : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  unit = (fun fmods -> ((

let uu____214 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____214 (fun a1 -> ())));
(

let nerrs = (FStar_Errors.get_err_count ())
in (match ((nerrs > (Prims.parse_int "0"))) with
| true -> begin
((finished_message fmods nerrs);
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____225 -> begin
()
end));
))


let load_native_tactics : unit  ->  unit = (fun uu____232 -> (

let modules_to_load = (

let uu____236 = (FStar_Options.load ())
in (FStar_All.pipe_right uu____236 (FStar_List.map FStar_Ident.lid_of_str)))
in (

let ml_module_name = (fun m -> (

let uu____253 = (FStar_Extraction_ML_Util.mlpath_of_lid m)
in (FStar_All.pipe_right uu____253 FStar_Extraction_ML_Util.flatten_mlpath)))
in (

let ml_file = (fun m -> (

let uu____278 = (ml_module_name m)
in (Prims.op_Hat uu____278 ".ml")))
in (

let cmxs_file = (fun m -> (

let cmxs = (

let uu____290 = (ml_module_name m)
in (Prims.op_Hat uu____290 ".cmxs"))
in (

let uu____293 = (FStar_Options.find_file cmxs)
in (match (uu____293) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let uu____302 = (

let uu____306 = (ml_file m)
in (FStar_Options.find_file uu____306))
in (match (uu____302) with
| FStar_Pervasives_Native.None -> begin
(

let uu____310 = (

let uu____316 = (

let uu____318 = (ml_file m)
in (FStar_Util.format1 "Failed to compile native tactic; extracted module %s not found" uu____318))
in ((FStar_Errors.Fatal_FailToCompileNativeTactic), (uu____316)))
in (FStar_Errors.raise_err uu____310))
end
| FStar_Pervasives_Native.Some (ml) -> begin
(

let dir = (FStar_Util.dirname ml)
in ((

let uu____329 = (

let uu____333 = (ml_module_name m)
in (uu____333)::[])
in (FStar_Tactics_Load.compile_modules dir uu____329));
(

let uu____337 = (FStar_Options.find_file cmxs)
in (match (uu____337) with
| FStar_Pervasives_Native.None -> begin
(

let uu____343 = (

let uu____349 = (FStar_Util.format1 "Failed to compile native tactic; compiled object %s not found" cmxs)
in ((FStar_Errors.Fatal_FailToCompileNativeTactic), (uu____349)))
in (FStar_Errors.raise_err uu____343))
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


let fstar_files : Prims.string Prims.list FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let go : 'Auu____394 . 'Auu____394  ->  unit = (fun uu____399 -> (

let uu____400 = (process_args ())
in (match (uu____400) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
((FStar_Options.display_usage ());
(FStar_All.exit (Prims.parse_int "0"));
)
end
| FStar_Getopt.Error (msg) -> begin
((FStar_Util.print_error msg);
(FStar_All.exit (Prims.parse_int "1"));
)
end
| FStar_Getopt.Success -> begin
((FStar_ST.op_Colon_Equals fstar_files (FStar_Pervasives_Native.Some (filenames)));
(load_native_tactics ());
(

let uu____456 = (

let uu____458 = (FStar_Options.dep ())
in (Prims.op_disEquality uu____458 FStar_Pervasives_Native.None))
in (match (uu____456) with
| true -> begin
(

let uu____467 = (FStar_Parser_Dep.collect filenames FStar_CheckedFiles.load_parsing_data_from_cache)
in (match (uu____467) with
| (uu____475, deps) -> begin
(FStar_Parser_Dep.print deps)
end))
end
| uu____483 -> begin
(

let uu____485 = (((FStar_Options.use_extracted_interfaces ()) && (

let uu____488 = (FStar_Options.expose_interfaces ())
in (not (uu____488)))) && ((FStar_List.length filenames) > (Prims.parse_int "1")))
in (match (uu____485) with
| true -> begin
(

let uu____493 = (

let uu____499 = (

let uu____501 = (FStar_Util.string_of_int (FStar_List.length filenames))
in (Prims.op_Hat "Only one command line file is allowed if --use_extracted_interfaces is set, found " uu____501))
in ((FStar_Errors.Error_TooManyFiles), (uu____499)))
in (FStar_Errors.raise_error uu____493 FStar_Range.dummyRange))
end
| uu____506 -> begin
(

let uu____508 = (FStar_Options.interactive ())
in (match (uu____508) with
| true -> begin
(match (filenames) with
| [] -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_MissingFileName), ("--ide: Name of current file missing in command line invocation\n")));
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (uu____516)::(uu____517)::uu____518 -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_TooManyFiles), ("--ide: Too many files in command line invocation\n")));
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (filename)::[] -> begin
(

let uu____534 = (FStar_Options.legacy_interactive ())
in (match (uu____534) with
| true -> begin
(FStar_Interactive_Legacy.interactive_mode filename)
end
| uu____537 -> begin
(FStar_Interactive_Ide.interactive_mode filename)
end))
end)
end
| uu____539 -> begin
(

let uu____541 = (FStar_Options.doc ())
in (match (uu____541) with
| true -> begin
(FStar_Fsdoc_Generator.generate filenames)
end
| uu____544 -> begin
(

let uu____546 = ((FStar_Options.print ()) || (FStar_Options.print_in_place ()))
in (match (uu____546) with
| true -> begin
(match (FStar_Platform.is_fstar_compiler_using_ocaml) with
| true -> begin
(FStar_Prettyprint.generate FStar_Prettyprint.ToTempFile filenames)
end
| uu____550 -> begin
(failwith "You seem to be using the F#-generated version ofthe compiler ; reindenting is not known to work yet with this version")
end)
end
| uu____553 -> begin
(match (((FStar_List.length filenames) >= (Prims.parse_int "1"))) with
| true -> begin
(

let uu____558 = (FStar_Dependencies.find_deps_if_needed filenames FStar_CheckedFiles.load_parsing_data_from_cache)
in (match (uu____558) with
| (filenames1, dep_graph1) -> begin
(

let uu____574 = (FStar_Universal.batch_mode_tc filenames1 dep_graph1)
in (match (uu____574) with
| (tcrs, env, cleanup1) -> begin
((

let uu____600 = (cleanup1 env)
in ());
(

let module_names_and_times = (FStar_All.pipe_right tcrs (FStar_List.map (fun tcr -> (((FStar_Universal.module_or_interface_name tcr.FStar_CheckedFiles.checked_module)), (tcr.FStar_CheckedFiles.tc_time)))))
in ((report_errors module_names_and_times);
(finished_message module_names_and_times (Prims.parse_int "0"));
));
)
end))
end))
end
| uu____648 -> begin
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
| FStar_Syntax_Syntax.Lazy_embedding (uu____671, t) -> begin
(FStar_Common.force_thunk t)
end))


let setup_hooks : unit  ->  unit = (fun uu____688 -> ((FStar_Options.initialize_parse_warn_error FStar_Parser_ParseIt.parse_warn_error);
(FStar_ST.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser (FStar_Pervasives_Native.Some (lazy_chooser)));
(FStar_ST.op_Colon_Equals FStar_Syntax_Util.tts_f (FStar_Pervasives_Native.Some (FStar_Syntax_Print.term_to_string)));
(FStar_ST.op_Colon_Equals FStar_TypeChecker_Normalize.unembed_binder_knot (FStar_Pervasives_Native.Some (FStar_Reflection_Embeddings.e_binder)));
))


let handle_error : Prims.exn  ->  unit = (fun e -> ((match ((FStar_Errors.handleable e)) with
| true -> begin
(FStar_Errors.err_exn e)
end
| uu____805 -> begin
()
end);
(

let uu____808 = (FStar_Options.trace_error ())
in (match (uu____808) with
| true -> begin
(

let uu____811 = (FStar_Util.message_of_exn e)
in (

let uu____813 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____811 uu____813)))
end
| uu____816 -> begin
(match ((not ((FStar_Errors.handleable e)))) with
| true -> begin
(

let uu____819 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" uu____819))
end
| uu____822 -> begin
()
end)
end));
(cleanup ());
(report_errors []);
))


let main : unit  ->  unit = (fun uu____840 -> (FStar_All.try_with (fun uu___121_850 -> (match (()) with
| () -> begin
((setup_hooks ());
(

let uu____852 = (FStar_Util.record_time go)
in (match (uu____852) with
| (uu____858, time) -> begin
(

let uu____862 = ((FStar_Options.print ()) || (FStar_Options.print_in_place ()))
in (match (uu____862) with
| true -> begin
(

let uu____865 = (FStar_ST.op_Bang fstar_files)
in (match (uu____865) with
| FStar_Pervasives_Native.Some (filenames) -> begin
(

let printing_mode = (

let uu____908 = (FStar_Options.print ())
in (match (uu____908) with
| true -> begin
FStar_Prettyprint.FromTempToStdout
end
| uu____911 -> begin
FStar_Prettyprint.FromTempToFile
end))
in (FStar_Prettyprint.generate printing_mode filenames))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Util.print_error "Internal error: List of source files not properly set");
(

let uu____919 = (FStar_Options.query_stats ())
in (match (uu____919) with
| true -> begin
(

let uu____922 = (FStar_Util.string_of_int time)
in (

let uu____924 = (

let uu____926 = (FStar_Getopt.cmdline ())
in (FStar_String.concat " " uu____926))
in (FStar_Util.print2 "TOTAL TIME %s ms: %s\n" uu____922 uu____924)))
end
| uu____932 -> begin
()
end));
(cleanup ());
(FStar_All.exit (Prims.parse_int "0"));
)
end))
end
| uu____936 -> begin
()
end))
end));
)
end)) (fun uu___120_940 -> ((handle_error uu___120_940);
(FStar_All.exit (Prims.parse_int "1"));
))))




