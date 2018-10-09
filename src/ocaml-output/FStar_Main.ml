
open Prims
open FStar_Pervasives

let uu___478 : unit = (FStar_Version.dummy ())


let process_args : unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____11 -> (FStar_Options.parse_cmd_line ()))


let cleanup : unit  ->  unit = (fun uu____22 -> (FStar_Util.kill_all ()))


let finished_message : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  Prims.int  ->  unit = (fun fmods errs -> (

let print_to = (match ((errs > (Prims.parse_int "0"))) with
| true -> begin
FStar_Util.print_error
end
| uu____61 -> begin
FStar_Util.print_string
end)
in (

let uu____62 = (

let uu____63 = (FStar_Options.silent ())
in (not (uu____63)))
in (match (uu____62) with
| true -> begin
((FStar_All.pipe_right fmods (FStar_List.iter (fun uu____90 -> (match (uu____90) with
| ((iface1, name), time) -> begin
(

let tag = (match (iface1) with
| true -> begin
"i\'face (or impl+i\'face)"
end
| uu____107 -> begin
"module"
end)
in (

let uu____108 = (FStar_Options.should_print_message name.FStar_Ident.str)
in (match (uu____108) with
| true -> begin
(match ((time >= (Prims.parse_int "0"))) with
| true -> begin
(

let uu____109 = (

let uu____110 = (FStar_Ident.text_of_lid name)
in (

let uu____111 = (FStar_Util.string_of_int time)
in (FStar_Util.format3 "Verified %s: %s (%s milliseconds)\n" tag uu____110 uu____111)))
in (print_to uu____109))
end
| uu____112 -> begin
(

let uu____113 = (

let uu____114 = (FStar_Ident.text_of_lid name)
in (FStar_Util.format2 "Verified %s: %s\n" tag uu____114))
in (print_to uu____113))
end)
end
| uu____115 -> begin
()
end)))
end))));
(match ((errs > (Prims.parse_int "0"))) with
| true -> begin
(match ((Prims.op_Equality errs (Prims.parse_int "1"))) with
| true -> begin
(FStar_Util.print_error "1 error was reported (see above)\n")
end
| uu____116 -> begin
(

let uu____117 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" uu____117))
end)
end
| uu____118 -> begin
(

let uu____119 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.print1 "%s\n" uu____119))
end);
)
end
| uu____120 -> begin
()
end))))


let report_errors : ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list  ->  unit = (fun fmods -> ((

let uu____147 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____147 (fun a1 -> ())));
(

let nerrs = (FStar_Errors.get_err_count ())
in (match ((nerrs > (Prims.parse_int "0"))) with
| true -> begin
((finished_message fmods nerrs);
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____154 -> begin
()
end));
))


let codegen : (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env * FStar_Universal.delta_env)  ->  unit = (fun uu____167 -> (match (uu____167) with
| (umods, env, delta1) -> begin
(

let opt = (FStar_Options.codegen ())
in (match ((Prims.op_disEquality opt FStar_Pervasives_Native.None)) with
| true -> begin
(

let env1 = (FStar_Universal.apply_delta_env env delta1)
in (

let mllibs = (

let uu____196 = (

let uu____205 = (FStar_Extraction_ML_UEnv.mkContext env1)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____205 umods))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____196))
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
| uu____228 -> begin
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

let uu____247 = (FStar_List.map FStar_Extraction_Kremlin.translate mllibs1)
in (FStar_List.flatten uu____247))
in (

let bin = ((FStar_Extraction_Kremlin.current_version), (programs))
in (match (programs) with
| ((name, uu____270))::[] -> begin
(

let uu____279 = (FStar_Options.prepend_output_dir (Prims.strcat name ext))
in (FStar_Util.save_value_to_file uu____279 bin))
end
| uu____280 -> begin
(

let uu____287 = (FStar_Options.prepend_output_dir "out.krml")
in (FStar_Util.save_value_to_file uu____287 bin))
end)))
end
| uu____288 -> begin
(failwith "Unrecognized option")
end)))))
end
| uu____291 -> begin
()
end))
end))


let load_native_tactics : unit  ->  unit = (fun uu____296 -> (

let modules_to_load = (

let uu____300 = (FStar_Options.load ())
in (FStar_All.pipe_right uu____300 (FStar_List.map FStar_Ident.lid_of_str)))
in (

let ml_module_name = (fun m -> (

let uu____313 = (FStar_Extraction_ML_Util.mlpath_of_lid m)
in (FStar_All.pipe_right uu____313 FStar_Extraction_ML_Util.flatten_mlpath)))
in (

let ml_file = (fun m -> (

let uu____332 = (ml_module_name m)
in (Prims.strcat uu____332 ".ml")))
in (

let cmxs_file = (fun m -> (

let cmxs = (

let uu____340 = (ml_module_name m)
in (Prims.strcat uu____340 ".cmxs"))
in (

let uu____341 = (FStar_Options.find_file cmxs)
in (match (uu____341) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let uu____345 = (

let uu____348 = (ml_file m)
in (FStar_Options.find_file uu____348))
in (match (uu____345) with
| FStar_Pervasives_Native.None -> begin
(

let uu____349 = (

let uu____354 = (

let uu____355 = (ml_file m)
in (FStar_Util.format1 "Failed to compile native tactic; extracted module %s not found" uu____355))
in ((FStar_Errors.Fatal_FailToCompileNativeTactic), (uu____354)))
in (FStar_Errors.raise_err uu____349))
end
| FStar_Pervasives_Native.Some (ml) -> begin
(

let dir = (FStar_Util.dirname ml)
in ((

let uu____359 = (

let uu____362 = (ml_module_name m)
in (uu____362)::[])
in (FStar_Tactics_Load.compile_modules dir uu____359));
(

let uu____363 = (FStar_Options.find_file cmxs)
in (match (uu____363) with
| FStar_Pervasives_Native.None -> begin
(

let uu____366 = (

let uu____371 = (FStar_Util.format1 "Failed to compile native tactic; compiled object %s not found" cmxs)
in ((FStar_Errors.Fatal_FailToCompileNativeTactic), (uu____371)))
in (FStar_Errors.raise_err uu____366))
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


let init_warn_error : unit  ->  unit = (fun uu____387 -> (

let s = (FStar_Options.warn_error ())
in (match ((Prims.op_disEquality s "")) with
| true -> begin
(FStar_Parser_ParseIt.parse_warn_error s)
end
| uu____390 -> begin
()
end)))


let go : 'Auu____395 . 'Auu____395  ->  unit = (fun uu____400 -> (

let uu____401 = (process_args ())
in (match (uu____401) with
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

let uu____419 = (

let uu____420 = (FStar_Options.dep ())
in (Prims.op_disEquality uu____420 FStar_Pervasives_Native.None))
in (match (uu____419) with
| true -> begin
(

let uu____425 = (FStar_Parser_Dep.collect filenames)
in (match (uu____425) with
| (uu____432, deps) -> begin
(FStar_Parser_Dep.print deps)
end))
end
| uu____438 -> begin
(

let uu____439 = (((FStar_Options.use_extracted_interfaces ()) && (

let uu____441 = (FStar_Options.expose_interfaces ())
in (not (uu____441)))) && ((FStar_List.length filenames) > (Prims.parse_int "1")))
in (match (uu____439) with
| true -> begin
(

let uu____442 = (

let uu____447 = (

let uu____448 = (FStar_Util.string_of_int (FStar_List.length filenames))
in (Prims.strcat "Only one command line file is allowed if --use_extracted_interfaces is set, found %s" uu____448))
in ((FStar_Errors.Error_TooManyFiles), (uu____447)))
in (FStar_Errors.raise_error uu____442 FStar_Range.dummyRange))
end
| uu____449 -> begin
(

let uu____450 = (FStar_Options.interactive ())
in (match (uu____450) with
| true -> begin
(match (filenames) with
| [] -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_MissingFileName), ("--ide: Name of current file missing in command line invocation\n")));
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (uu____452)::(uu____453)::uu____454 -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_TooManyFiles), ("--ide: Too many files in command line invocation\n")));
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (filename)::[] -> begin
(

let uu____459 = (FStar_Options.legacy_interactive ())
in (match (uu____459) with
| true -> begin
(FStar_Interactive_Legacy.interactive_mode filename)
end
| uu____460 -> begin
(FStar_Interactive_Ide.interactive_mode filename)
end))
end)
end
| uu____461 -> begin
(

let uu____462 = (FStar_Options.doc ())
in (match (uu____462) with
| true -> begin
(FStar_Fsdoc_Generator.generate filenames)
end
| uu____463 -> begin
(

let uu____464 = (FStar_Options.indent ())
in (match (uu____464) with
| true -> begin
(match (FStar_Platform.is_fstar_compiler_using_ocaml) with
| true -> begin
(FStar_Indent.generate filenames)
end
| uu____465 -> begin
(failwith "You seem to be using the F#-generated version ofthe compiler ; reindenting is not known to work yet with this version")
end)
end
| uu____466 -> begin
(match (((FStar_List.length filenames) >= (Prims.parse_int "1"))) with
| true -> begin
(

let uu____467 = (FStar_Dependencies.find_deps_if_needed filenames)
in (match (uu____467) with
| (filenames1, dep_graph1) -> begin
(

let uu____480 = (FStar_Universal.batch_mode_tc filenames1 dep_graph1)
in (match (uu____480) with
| (fmods, env, delta_env) -> begin
(

let module_names_and_times = (FStar_All.pipe_right fmods (FStar_List.map (fun uu____565 -> (match (uu____565) with
| (x, t) -> begin
(((FStar_Universal.module_or_interface_name x)), (t))
end))))
in ((report_errors module_names_and_times);
(

let uu____586 = (

let uu____595 = (FStar_All.pipe_right fmods (FStar_List.map FStar_Pervasives_Native.fst))
in ((uu____595), (env), (delta_env)))
in (codegen uu____586));
(report_errors module_names_and_times);
(finished_message module_names_and_times (Prims.parse_int "0"));
))
end))
end))
end
| uu____613 -> begin
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
| FStar_Syntax_Syntax.Lazy_embedding (uu____630, t) -> begin
(FStar_Common.force_thunk t)
end))


let setup_hooks : unit  ->  unit = (fun uu____686 -> ((FStar_ST.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser (FStar_Pervasives_Native.Some (lazy_chooser)));
(FStar_ST.op_Colon_Equals FStar_Syntax_Util.tts_f (FStar_Pervasives_Native.Some (FStar_Syntax_Print.term_to_string)));
(FStar_ST.op_Colon_Equals FStar_TypeChecker_Normalize.unembed_binder_knot (FStar_Pervasives_Native.Some (FStar_Reflection_Embeddings.e_binder)));
))


let handle_error : Prims.exn  ->  unit = (fun e -> ((match ((FStar_Errors.handleable e)) with
| true -> begin
(FStar_Errors.err_exn e)
end
| uu____797 -> begin
()
end);
(

let uu____799 = (FStar_Options.trace_error ())
in (match (uu____799) with
| true -> begin
(

let uu____800 = (FStar_Util.message_of_exn e)
in (

let uu____801 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____800 uu____801)))
end
| uu____802 -> begin
(match ((not ((FStar_Errors.handleable e)))) with
| true -> begin
(

let uu____803 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" uu____803))
end
| uu____804 -> begin
()
end)
end));
(cleanup ());
(report_errors []);
))


let main : 'Auu____818 . unit  ->  'Auu____818 = (fun uu____823 -> (FStar_All.try_with (fun uu___480_831 -> (match (()) with
| () -> begin
((setup_hooks ());
(

let uu____833 = (FStar_Util.record_time go)
in (match (uu____833) with
| (uu____838, time) -> begin
((

let uu____841 = (FStar_Options.query_stats ())
in (match (uu____841) with
| true -> begin
(

let uu____842 = (FStar_Util.string_of_int time)
in (

let uu____843 = (

let uu____844 = (FStar_Getopt.cmdline ())
in (FStar_String.concat " " uu____844))
in (FStar_Util.print2 "TOTAL TIME %s ms: %s\n" uu____842 uu____843)))
end
| uu____847 -> begin
()
end));
(cleanup ());
(FStar_All.exit (Prims.parse_int "0"));
)
end));
)
end)) (fun uu___479_851 -> ((handle_error uu___479_851);
(FStar_All.exit (Prims.parse_int "1"));
))))




