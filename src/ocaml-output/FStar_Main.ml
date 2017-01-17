
open Prims

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

let uu____35 = (not ((FStar_Options.silent ())))
in (match (uu____35) with
| true -> begin
((FStar_All.pipe_right fmods (FStar_List.iter (fun uu____46 -> (match (uu____46) with
| ((iface, name), time) -> begin
(

let tag = (match (iface) with
| true -> begin
"i\'face (or impl+i\'face)"
end
| uu____57 -> begin
"module"
end)
in (

let uu____58 = (FStar_Options.should_print_message name.FStar_Ident.str)
in (match (uu____58) with
| true -> begin
(match ((time >= (Prims.parse_int "0"))) with
| true -> begin
(print_to (let _0_1409 = (FStar_Util.string_of_int time)
in (FStar_Util.format3 "Verified %s: %s (%s milliseconds)\n" tag (FStar_Ident.text_of_lid name) _0_1409)))
end
| uu____59 -> begin
(print_to (FStar_Util.format2 "Verified %s: %s\n" tag (FStar_Ident.text_of_lid name)))
end)
end
| uu____60 -> begin
()
end)))
end))));
(match ((errs > (Prims.parse_int "0"))) with
| true -> begin
(match ((errs = (Prims.parse_int "1"))) with
| true -> begin
(FStar_Util.print_error "1 error was reported (see above)\n")
end
| uu____61 -> begin
(let _0_1410 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" _0_1410))
end)
end
| uu____62 -> begin
(FStar_Util.print_string (let _0_1411 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" _0_1411)))
end);
)
end
| uu____63 -> begin
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
| uu____79 -> begin
()
end)))


let codegen : (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env)  ->  Prims.unit = (fun uu____85 -> (match (uu____85) with
| (umods, env) -> begin
(

let opt = (FStar_Options.codegen ())
in (match ((opt <> None)) with
| true -> begin
(

let mllibs = (let _0_1413 = (let _0_1412 = (FStar_Extraction_ML_UEnv.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_Modul.extract _0_1412 umods))
in (FStar_All.pipe_left Prims.snd _0_1413))
in (

let mllibs = (FStar_List.flatten mllibs)
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
| uu____111 -> begin
(failwith "Unrecognized option")
end)
in (match (opt) with
| (Some ("FSharp")) | (Some ("OCaml")) -> begin
(

let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun uu____121 -> (match (uu____121) with
| (n, d) -> begin
(let _0_1414 = (FStar_Options.prepend_output_dir (Prims.strcat n ext))
in (FStar_Util.write_file _0_1414 (FStar_Format.pretty (Prims.parse_int "120") d)))
end)) newDocs))
end
| Some ("Kremlin") -> begin
(

let programs = (FStar_List.flatten (FStar_List.map FStar_Extraction_Kremlin.translate mllibs))
in (

let bin = ((FStar_Extraction_Kremlin.current_version), (programs))
in (let _0_1415 = (FStar_Options.prepend_output_dir "out.krml")
in (FStar_Util.save_value_to_file _0_1415 bin))))
end
| uu____131 -> begin
(failwith "Unrecognized option")
end))))
end
| uu____133 -> begin
()
end))
end))


let go = (fun uu____140 -> (

let uu____141 = (process_args ())
in (match (uu____141) with
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

let uu____151 = (let _0_1416 = (FStar_Options.dep ())
in (_0_1416 <> None))
in (match (uu____151) with
| true -> begin
(FStar_Parser_Dep.print (FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames))
end
| uu____154 -> begin
(

let uu____155 = (FStar_Options.interactive ())
in (match (uu____155) with
| true -> begin
((

let uu____157 = (FStar_Options.explicit_deps ())
in (match (uu____157) with
| true -> begin
((FStar_Util.print_error "--explicit_deps incompatible with --in|n");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____159 -> begin
()
end));
(match (((FStar_List.length filenames) <> (Prims.parse_int "1"))) with
| true -> begin
((FStar_Util.print_error "fstar-mode.el should pass the current filename to F*\n");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____164 -> begin
()
end);
(

let filename = (FStar_List.hd filenames)
in ((

let uu____167 = (let _0_1417 = (FStar_Options.verify_module ())
in (_0_1417 <> []))
in (match (uu____167) with
| true -> begin
(FStar_Util.print_warning "Interactive mode; ignoring --verify_module")
end
| uu____169 -> begin
()
end));
(FStar_Interactive.interactive_mode filename None FStar_Universal.interactive_tc);
));
)
end
| uu____173 -> begin
(

let uu____174 = (FStar_Options.doc ())
in (match (uu____174) with
| true -> begin
(FStar_Fsdoc_Generator.generate filenames)
end
| uu____175 -> begin
(

let uu____176 = (FStar_Options.indent ())
in (match (uu____176) with
| true -> begin
(FStar_Indent.generate filenames)
end
| uu____177 -> begin
(match (((FStar_List.length filenames) >= (Prims.parse_int "1"))) with
| true -> begin
(

let verify_mode = (

let uu____182 = (FStar_Options.verify_all ())
in (match (uu____182) with
| true -> begin
((

let uu____184 = (let _0_1418 = (FStar_Options.verify_module ())
in (_0_1418 <> []))
in (match (uu____184) with
| true -> begin
((FStar_Util.print_error "--verify_module is incompatible with --verify_all");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____187 -> begin
()
end));
FStar_Parser_Dep.VerifyAll;
)
end
| uu____188 -> begin
(

let uu____189 = (let _0_1419 = (FStar_Options.verify_module ())
in (_0_1419 <> []))
in (match (uu____189) with
| true -> begin
FStar_Parser_Dep.VerifyUserList
end
| uu____191 -> begin
FStar_Parser_Dep.VerifyFigureItOut
end))
end))
in (

let filenames = (FStar_Dependencies.find_deps_if_needed verify_mode filenames)
in (

let uu____194 = (FStar_Universal.batch_mode_tc filenames)
in (match (uu____194) with
| (fmods, dsenv, env) -> begin
(

let module_names_and_times = (FStar_All.pipe_right fmods (FStar_List.map (fun uu____230 -> (match (uu____230) with
| (x, t) -> begin
(((FStar_Universal.module_or_interface_name x)), (t))
end))))
in ((report_errors module_names_and_times);
(codegen (let _0_1420 = (FStar_All.pipe_right fmods (FStar_List.map Prims.fst))
in ((_0_1420), (env))));
(finished_message module_names_and_times (Prims.parse_int "0"));
))
end))))
end
| uu____250 -> begin
(FStar_Util.print_error "no file provided\n")
end)
end))
end))
end))
end))
end)
end)))


let main = (fun uu____257 -> try
(match (()) with
| () -> begin
((go ());
(cleanup ());
(FStar_All.exit (Prims.parse_int "0"));
)
end)
with
| e -> begin
((match ((FStar_Errors.handleable e)) with
| true -> begin
(FStar_Errors.handle_err false e)
end
| uu____265 -> begin
()
end);
(

let uu____266 = (FStar_Options.trace_error ())
in (match (uu____266) with
| true -> begin
(let _0_1422 = (FStar_Util.message_of_exn e)
in (let _0_1421 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" _0_1422 _0_1421)))
end
| uu____267 -> begin
(match ((not ((FStar_Errors.handleable e)))) with
| true -> begin
(let _0_1423 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _0_1423))
end
| uu____268 -> begin
()
end)
end));
(cleanup ());
(let _0_1424 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right _0_1424 Prims.ignore));
(report_errors []);
(FStar_All.exit (Prims.parse_int "1"));
)
end)




