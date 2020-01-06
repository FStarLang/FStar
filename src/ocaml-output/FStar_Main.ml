
open Prims
open FStar_Pervasives

let uu___0 : unit = (FStar_Version.dummy ())


let process_args : unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____12 -> (FStar_Options.parse_cmd_line ()))


let cleanup : unit  ->  unit = (fun uu____25 -> (FStar_Util.kill_all ()))


let finished_message : (Prims.bool * FStar_Ident.lident) Prims.list  ->  Prims.int  ->  unit = (fun fmods errs -> (

let print_to = (match ((errs > (Prims.parse_int "0"))) with
| true -> begin
FStar_Util.print_error
end
| uu____65 -> begin
FStar_Util.print_string
end)
in (

let uu____67 = (

let uu____69 = (FStar_Options.silent ())
in (not (uu____69)))
in (match (uu____67) with
| true -> begin
((FStar_All.pipe_right fmods (FStar_List.iter (fun uu____91 -> (match (uu____91) with
| (iface1, name) -> begin
(

let tag = (match (iface1) with
| true -> begin
"i\'face (or impl+i\'face)"
end
| uu____106 -> begin
"module"
end)
in (

let uu____109 = (FStar_Options.should_print_message name.FStar_Ident.str)
in (match (uu____109) with
| true -> begin
(

let uu____112 = (

let uu____114 = (FStar_Ident.text_of_lid name)
in (FStar_Util.format2 "Verified %s: %s\n" tag uu____114))
in (print_to uu____112))
end
| uu____117 -> begin
()
end)))
end))));
(match ((errs > (Prims.parse_int "0"))) with
| true -> begin
(match ((Prims.op_Equality errs (Prims.parse_int "1"))) with
| true -> begin
(FStar_Util.print_error "1 error was reported (see above)\n")
end
| uu____125 -> begin
(

let uu____127 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" uu____127))
end)
end
| uu____130 -> begin
(

let uu____132 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.print1 "%s\n" uu____132))
end);
)
end
| uu____136 -> begin
()
end))))


let report_errors : (Prims.bool * FStar_Ident.lident) Prims.list  ->  unit = (fun fmods -> ((

let uu____159 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____159 (fun a1 -> ())));
(

let nerrs = (FStar_Errors.get_err_count ())
in (match ((nerrs > (Prims.parse_int "0"))) with
| true -> begin
((finished_message fmods nerrs);
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____170 -> begin
()
end));
))


let load_native_tactics : unit  ->  unit = (fun uu____177 -> (

let modules_to_load = (

let uu____181 = (FStar_Options.load ())
in (FStar_All.pipe_right uu____181 (FStar_List.map FStar_Ident.lid_of_str)))
in (

let ml_module_name = (fun m -> (

let uu____198 = (FStar_Extraction_ML_Util.mlpath_of_lid m)
in (FStar_All.pipe_right uu____198 FStar_Extraction_ML_Util.flatten_mlpath)))
in (

let ml_file = (fun m -> (

let uu____223 = (ml_module_name m)
in (Prims.op_Hat uu____223 ".ml")))
in (

let cmxs_file = (fun m -> (

let cmxs = (

let uu____235 = (ml_module_name m)
in (Prims.op_Hat uu____235 ".cmxs"))
in (

let uu____238 = (FStar_Options.find_file cmxs)
in (match (uu____238) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let uu____247 = (

let uu____251 = (ml_file m)
in (FStar_Options.find_file uu____251))
in (match (uu____247) with
| FStar_Pervasives_Native.None -> begin
(

let uu____255 = (

let uu____261 = (

let uu____263 = (ml_file m)
in (FStar_Util.format1 "Failed to compile native tactic; extracted module %s not found" uu____263))
in ((FStar_Errors.Fatal_FailToCompileNativeTactic), (uu____261)))
in (FStar_Errors.raise_err uu____255))
end
| FStar_Pervasives_Native.Some (ml) -> begin
(

let dir = (FStar_Util.dirname ml)
in ((

let uu____274 = (

let uu____278 = (ml_module_name m)
in (uu____278)::[])
in (FStar_Tactics_Load.compile_modules dir uu____274));
(

let uu____282 = (FStar_Options.find_file cmxs)
in (match (uu____282) with
| FStar_Pervasives_Native.None -> begin
(

let uu____288 = (

let uu____294 = (FStar_Util.format1 "Failed to compile native tactic; compiled object %s not found" cmxs)
in ((FStar_Errors.Fatal_FailToCompileNativeTactic), (uu____294)))
in (FStar_Errors.raise_err uu____288))
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
(

let uu____320 = (FStar_Options.use_native_tactics ())
in (FStar_Util.iter_opt uu____320 FStar_Tactics_Load.load_tactics_dir));
)))))))


let fstar_files : Prims.string Prims.list FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let go : 'Auu____346 . 'Auu____346  ->  unit = (fun uu____351 -> (

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
((FStar_Util.print_error msg);
(FStar_All.exit (Prims.parse_int "1"));
)
end
| FStar_Getopt.Success -> begin
((FStar_ST.op_Colon_Equals fstar_files (FStar_Pervasives_Native.Some (filenames)));
(load_native_tactics ());
(

let uu____408 = (

let uu____410 = (FStar_Options.dep ())
in (Prims.op_disEquality uu____410 FStar_Pervasives_Native.None))
in (match (uu____408) with
| true -> begin
(

let uu____419 = (FStar_Parser_Dep.collect filenames FStar_CheckedFiles.load_parsing_data_from_cache)
in (match (uu____419) with
| (uu____427, deps) -> begin
(FStar_Parser_Dep.print deps)
end))
end
| uu____435 -> begin
(

let uu____437 = (((FStar_Options.use_extracted_interfaces ()) && (

let uu____440 = (FStar_Options.expose_interfaces ())
in (not (uu____440)))) && ((FStar_List.length filenames) > (Prims.parse_int "1")))
in (match (uu____437) with
| true -> begin
(

let uu____445 = (

let uu____451 = (

let uu____453 = (FStar_Util.string_of_int (FStar_List.length filenames))
in (Prims.op_Hat "Only one command line file is allowed if --use_extracted_interfaces is set, found " uu____453))
in ((FStar_Errors.Error_TooManyFiles), (uu____451)))
in (FStar_Errors.raise_error uu____445 FStar_Range.dummyRange))
end
| uu____458 -> begin
(

let uu____460 = (FStar_Options.lsp_server ())
in (match (uu____460) with
| true -> begin
(FStar_Interactive_Lsp.start_server ())
end
| uu____463 -> begin
(

let uu____465 = (FStar_Options.interactive ())
in (match (uu____465) with
| true -> begin
(match (filenames) with
| [] -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_MissingFileName), ("--ide: Name of current file missing in command line invocation\n")));
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (uu____473)::(uu____474)::uu____475 -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_TooManyFiles), ("--ide: Too many files in command line invocation\n")));
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (filename)::[] -> begin
(

let uu____491 = (FStar_Options.legacy_interactive ())
in (match (uu____491) with
| true -> begin
(FStar_Interactive_Legacy.interactive_mode filename)
end
| uu____494 -> begin
(FStar_Interactive_Ide.interactive_mode filename)
end))
end)
end
| uu____496 -> begin
(

let uu____498 = (FStar_Options.doc ())
in (match (uu____498) with
| true -> begin
(FStar_Fsdoc_Generator.generate filenames)
end
| uu____501 -> begin
(

let uu____503 = ((FStar_Options.print ()) || (FStar_Options.print_in_place ()))
in (match (uu____503) with
| true -> begin
(match (FStar_Platform.is_fstar_compiler_using_ocaml) with
| true -> begin
(FStar_Prettyprint.generate FStar_Prettyprint.ToTempFile filenames)
end
| uu____507 -> begin
(failwith "You seem to be using the F#-generated version ofthe compiler ; reindenting is not known to work yet with this version")
end)
end
| uu____510 -> begin
(match (((FStar_List.length filenames) >= (Prims.parse_int "1"))) with
| true -> begin
(

let uu____515 = (FStar_Dependencies.find_deps_if_needed filenames FStar_CheckedFiles.load_parsing_data_from_cache)
in (match (uu____515) with
| (filenames1, dep_graph1) -> begin
(

let uu____531 = (FStar_Universal.batch_mode_tc filenames1 dep_graph1)
in (match (uu____531) with
| (tcrs, env, cleanup1) -> begin
((

let uu____557 = (cleanup1 env)
in ());
(

let module_names = (FStar_All.pipe_right tcrs (FStar_List.map (fun tcr -> (FStar_Universal.module_or_interface_name tcr.FStar_CheckedFiles.checked_module))))
in ((report_errors module_names);
(finished_message module_names (Prims.parse_int "0"));
));
)
end))
end))
end
| uu____584 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Error_MissingFileName), ("No file provided")) FStar_Range.dummyRange)
end)
end))
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
| FStar_Syntax_Syntax.Lazy_optionstate -> begin
(FStar_Reflection_Embeddings.unfold_lazy_optionstate i)
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
| FStar_Syntax_Syntax.Lazy_embedding (uu____607, t) -> begin
(FStar_Thunk.force t)
end))


let setup_hooks : unit  ->  unit = (fun uu____624 -> ((FStar_Options.initialize_parse_warn_error FStar_Parser_ParseIt.parse_warn_error);
(FStar_ST.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser (FStar_Pervasives_Native.Some (lazy_chooser)));
(FStar_ST.op_Colon_Equals FStar_Syntax_Util.tts_f (FStar_Pervasives_Native.Some (FStar_Syntax_Print.term_to_string)));
(FStar_ST.op_Colon_Equals FStar_TypeChecker_Normalize.unembed_binder_knot (FStar_Pervasives_Native.Some (FStar_Reflection_Embeddings.e_binder)));
(FStar_ST.op_Colon_Equals FStar_TypeChecker_Tc.unembed_optionstate_knot (FStar_Pervasives_Native.Some (FStar_Reflection_Embeddings.e_optionstate)));
))


let handle_error : Prims.exn  ->  unit = (fun e -> ((match ((FStar_Errors.handleable e)) with
| true -> begin
(FStar_Errors.err_exn e)
end
| uu____772 -> begin
()
end);
(

let uu____775 = (FStar_Options.trace_error ())
in (match (uu____775) with
| true -> begin
(

let uu____778 = (FStar_Util.message_of_exn e)
in (

let uu____780 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____778 uu____780)))
end
| uu____783 -> begin
(match ((not ((FStar_Errors.handleable e)))) with
| true -> begin
(

let uu____786 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" uu____786))
end
| uu____789 -> begin
()
end)
end));
(cleanup ());
(report_errors []);
))


let main : unit  ->  unit = (fun uu____802 -> (FStar_All.try_with (fun uu___124_812 -> (match (()) with
| () -> begin
((setup_hooks ());
(

let uu____814 = (FStar_Util.record_time go)
in (match (uu____814) with
| (uu____820, time) -> begin
(

let uu____824 = ((FStar_Options.print ()) || (FStar_Options.print_in_place ()))
in (match (uu____824) with
| true -> begin
(

let uu____827 = (FStar_ST.op_Bang fstar_files)
in (match (uu____827) with
| FStar_Pervasives_Native.Some (filenames) -> begin
(

let printing_mode = (

let uu____870 = (FStar_Options.print ())
in (match (uu____870) with
| true -> begin
FStar_Prettyprint.FromTempToStdout
end
| uu____873 -> begin
FStar_Prettyprint.FromTempToFile
end))
in (FStar_Prettyprint.generate printing_mode filenames))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Util.print_error "Internal error: List of source files not properly set");
(

let uu____881 = (FStar_Options.query_stats ())
in (match (uu____881) with
| true -> begin
(

let uu____884 = (FStar_Util.string_of_int time)
in (

let uu____886 = (

let uu____888 = (FStar_Getopt.cmdline ())
in (FStar_String.concat " " uu____888))
in (FStar_Util.print2 "TOTAL TIME %s ms: %s\n" uu____884 uu____886)))
end
| uu____894 -> begin
()
end));
(cleanup ());
(FStar_All.exit (Prims.parse_int "0"));
)
end))
end
| uu____898 -> begin
()
end))
end));
)
end)) (fun uu___123_902 -> ((handle_error uu___123_902);
(FStar_All.exit (Prims.parse_int "1"));
))))




