
open Prims
open FStar_Pervasives

let _z3version_checked : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let _z3version_expected : Prims.string = "Z3 version 4.8.5"


let _z3url : Prims.string = "https://github.com/FStarLang/binaries/tree/master/z3-tested"


let parse_z3_version_lines : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun out -> (match ((FStar_Util.splitlines out)) with
| (version)::uu____46 -> begin
(match ((FStar_Util.starts_with version _z3version_expected)) with
| true -> begin
((

let uu____57 = (FStar_Options.debug_any ())
in (match (uu____57) with
| true -> begin
(

let uu____60 = (FStar_Util.format1 "Successfully found expected Z3 version %s\n" version)
in (FStar_Util.print_string uu____60))
end
| uu____63 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| uu____66 -> begin
(

let msg = (FStar_Util.format2 "Expected Z3 version \"%s\", got \"%s\"" _z3version_expected out)
in FStar_Pervasives_Native.Some (msg))
end)
end
| uu____72 -> begin
FStar_Pervasives_Native.Some ("No Z3 version string found")
end))


let z3version_warning_message : unit  ->  (FStar_Errors.raw_error * Prims.string) FStar_Pervasives_Native.option = (fun uu____90 -> (

let run_proc_result = (FStar_All.try_with (fun uu___15_100 -> (match (()) with
| () -> begin
(

let uu____104 = (

let uu____106 = (FStar_Options.z3_exe ())
in (FStar_Util.run_process "z3_version" uu____106 (("-version")::[]) FStar_Pervasives_Native.None))
in FStar_Pervasives_Native.Some (uu____104))
end)) (fun uu___14_115 -> FStar_Pervasives_Native.None))
in (match (run_proc_result) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((FStar_Errors.Error_Z3InvocationError), ("Could not run Z3")))
end
| FStar_Pervasives_Native.Some (out) -> begin
(

let uu____138 = (parse_z3_version_lines out)
in (match (uu____138) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (msg) -> begin
FStar_Pervasives_Native.Some (((FStar_Errors.Warning_Z3InvocationWarning), (msg)))
end))
end)))


let check_z3version : unit  ->  unit = (fun uu____169 -> (

let uu____170 = (

let uu____172 = (FStar_ST.op_Bang _z3version_checked)
in (not (uu____172)))
in (match (uu____170) with
| true -> begin
((FStar_ST.op_Colon_Equals _z3version_checked true);
(

let uu____219 = (z3version_warning_message ())
in (match (uu____219) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (e, msg) -> begin
(

let msg1 = (FStar_Util.format4 "%s\n%s\n%s\n%s\n" msg "Please download the version of Z3 corresponding to your platform from:" _z3url "and add the bin/ subdirectory into your PATH")
in (FStar_Errors.log_issue FStar_Range.dummyRange ((e), (msg1))))
end));
)
end
| uu____247 -> begin
()
end)))


type label =
Prims.string


type unsat_core =
Prims.string Prims.list FStar_Pervasives_Native.option

type z3status =
| UNSAT of unsat_core
| SAT of (FStar_SMTEncoding_Term.error_labels * Prims.string FStar_Pervasives_Native.option)
| UNKNOWN of (FStar_SMTEncoding_Term.error_labels * Prims.string FStar_Pervasives_Native.option)
| TIMEOUT of (FStar_SMTEncoding_Term.error_labels * Prims.string FStar_Pervasives_Native.option)
| KILLED


let uu___is_UNSAT : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UNSAT (_0) -> begin
true
end
| uu____307 -> begin
false
end))


let __proj__UNSAT__item___0 : z3status  ->  unsat_core = (fun projectee -> (match (projectee) with
| UNSAT (_0) -> begin
_0
end))


let uu___is_SAT : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SAT (_0) -> begin
true
end
| uu____333 -> begin
false
end))


let __proj__SAT__item___0 : z3status  ->  (FStar_SMTEncoding_Term.error_labels * Prims.string FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| SAT (_0) -> begin
_0
end))


let uu___is_UNKNOWN : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UNKNOWN (_0) -> begin
true
end
| uu____380 -> begin
false
end))


let __proj__UNKNOWN__item___0 : z3status  ->  (FStar_SMTEncoding_Term.error_labels * Prims.string FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| UNKNOWN (_0) -> begin
_0
end))


let uu___is_TIMEOUT : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TIMEOUT (_0) -> begin
true
end
| uu____427 -> begin
false
end))


let __proj__TIMEOUT__item___0 : z3status  ->  (FStar_SMTEncoding_Term.error_labels * Prims.string FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| TIMEOUT (_0) -> begin
_0
end))


let uu___is_KILLED : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| KILLED -> begin
true
end
| uu____466 -> begin
false
end))


type z3statistics =
Prims.string FStar_Util.smap


let status_tag : z3status  ->  Prims.string = (fun uu___0_477 -> (match (uu___0_477) with
| SAT (uu____479) -> begin
"sat"
end
| UNSAT (uu____488) -> begin
"unsat"
end
| UNKNOWN (uu____490) -> begin
"unknown"
end
| TIMEOUT (uu____499) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let status_string_and_errors : z3status  ->  (Prims.string * FStar_SMTEncoding_Term.error_labels) = (fun s -> (match (s) with
| KILLED -> begin
(((status_tag s)), ([]))
end
| UNSAT (uu____526) -> begin
(((status_tag s)), ([]))
end
| SAT (errs, msg) -> begin
(

let uu____536 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.op_Hat " because " msg1)
end))
in ((uu____536), (errs)))
end
| UNKNOWN (errs, msg) -> begin
(

let uu____555 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.op_Hat " because " msg1)
end))
in ((uu____555), (errs)))
end
| TIMEOUT (errs, msg) -> begin
(

let uu____574 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.op_Hat " because " msg1)
end))
in ((uu____574), (errs)))
end))

type query_log =
{get_module_name : unit  ->  Prims.string; set_module_name : Prims.string  ->  unit; write_to_log : Prims.bool  ->  Prims.string  ->  Prims.string; close_log : unit  ->  unit}


let __proj__Mkquery_log__item__get_module_name : query_log  ->  unit  ->  Prims.string = (fun projectee -> (match (projectee) with
| {get_module_name = get_module_name; set_module_name = set_module_name; write_to_log = write_to_log; close_log = close_log} -> begin
get_module_name
end))


let __proj__Mkquery_log__item__set_module_name : query_log  ->  Prims.string  ->  unit = (fun projectee -> (match (projectee) with
| {get_module_name = get_module_name; set_module_name = set_module_name; write_to_log = write_to_log; close_log = close_log} -> begin
set_module_name
end))


let __proj__Mkquery_log__item__write_to_log : query_log  ->  Prims.bool  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {get_module_name = get_module_name; set_module_name = set_module_name; write_to_log = write_to_log; close_log = close_log} -> begin
write_to_log
end))


let __proj__Mkquery_log__item__close_log : query_log  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {get_module_name = get_module_name; set_module_name = set_module_name; write_to_log = write_to_log; close_log = close_log} -> begin
close_log
end))


let query_logging : query_log = (

let query_number = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let log_file_opt = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let used_file_names = (FStar_Util.mk_ref [])
in (

let current_module_name = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let current_file_name = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let set_module_name = (fun n1 -> (FStar_ST.op_Colon_Equals current_module_name (FStar_Pervasives_Native.Some (n1))))
in (

let get_module_name = (fun uu____914 -> (

let uu____915 = (FStar_ST.op_Bang current_module_name)
in (match (uu____915) with
| FStar_Pervasives_Native.None -> begin
(failwith "Module name not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in (

let next_file_name = (fun uu____957 -> (

let n1 = (get_module_name ())
in (

let file_name = (

let uu____962 = (

let uu____971 = (FStar_ST.op_Bang used_file_names)
in (FStar_List.tryFind (fun uu____1024 -> (match (uu____1024) with
| (m, uu____1033) -> begin
(Prims.op_Equality n1 m)
end)) uu____971))
in (match (uu____962) with
| FStar_Pervasives_Native.None -> begin
((

let uu____1047 = (

let uu____1056 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((Prims.parse_int "0"))))::uu____1056)
in (FStar_ST.op_Colon_Equals used_file_names uu____1047));
n1;
)
end
| FStar_Pervasives_Native.Some (uu____1144, k) -> begin
((

let uu____1157 = (

let uu____1166 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((k + (Prims.parse_int "1")))))::uu____1166)
in (FStar_ST.op_Colon_Equals used_file_names uu____1157));
(

let uu____1254 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n1 uu____1254));
)
end))
in (FStar_Util.format1 "queries-%s.smt2" file_name))))
in (

let new_log_file = (fun uu____1269 -> (

let file_name = (next_file_name ())
in ((FStar_ST.op_Colon_Equals current_file_name (FStar_Pervasives_Native.Some (file_name)));
(

let fh = (FStar_Util.open_file_for_writing file_name)
in ((FStar_ST.op_Colon_Equals log_file_opt (FStar_Pervasives_Native.Some (((fh), (file_name)))));
((fh), (file_name));
));
)))
in (

let get_log_file = (fun uu____1351 -> (

let uu____1352 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____1352) with
| FStar_Pervasives_Native.None -> begin
(new_log_file ())
end
| FStar_Pervasives_Native.Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____1423 = (get_log_file ())
in (match (uu____1423) with
| (f, nm) -> begin
((FStar_Util.append_to_file f str);
nm;
)
end)))
in (

let write_to_new_log = (fun str -> (

let file_name = (next_file_name ())
in ((FStar_Util.write_file file_name str);
file_name;
)))
in (

let write_to_log = (fun fresh str -> (match (fresh) with
| true -> begin
(write_to_new_log str)
end
| uu____1465 -> begin
(append_to_log str)
end))
in (

let close_log = (fun uu____1472 -> (

let uu____1473 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____1473) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (fh, uu____1520) -> begin
((FStar_Util.close_file fh);
(FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None);
)
end)))
in (

let log_file_name = (fun uu____1573 -> (

let uu____1574 = (FStar_ST.op_Bang current_file_name)
in (match (uu____1574) with
| FStar_Pervasives_Native.None -> begin
(failwith "no log file")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in {get_module_name = get_module_name; set_module_name = set_module_name; write_to_log = write_to_log; close_log = close_log})))))))))))))))


let z3_cmd_and_args : unit  ->  (Prims.string * Prims.string Prims.list) = (fun uu____1623 -> (

let cmd = (FStar_Options.z3_exe ())
in (

let cmd_args = (

let uu____1630 = (

let uu____1634 = (

let uu____1638 = (

let uu____1642 = (

let uu____1646 = (

let uu____1648 = (

let uu____1650 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int uu____1650))
in (FStar_Util.format1 "smt.random_seed=%s" uu____1648))
in (uu____1646)::[])
in ("-in")::uu____1642)
in ("-smt2")::uu____1638)
in (

let uu____1659 = (FStar_Options.z3_cliopt ())
in (FStar_List.append uu____1634 uu____1659)))
in (

let uu____1664 = (

let uu____1668 = (FStar_Options.report_qi ())
in (match (uu____1668) with
| true -> begin
("smt.qi.profile=true")::[]
end
| uu____1677 -> begin
[]
end))
in (FStar_List.append uu____1630 uu____1664)))
in ((cmd), (cmd_args)))))


let new_z3proc : Prims.string  ->  (Prims.string * Prims.string Prims.list)  ->  FStar_Util.proc = (fun id1 cmd_and_args -> (

let filter1 = (

let uu____1721 = (FStar_Options.report_qi ())
in (match (uu____1721) with
| true -> begin
(fun s -> (not ((FStar_Util.starts_with s "[quantifier_instances]"))))
end
| uu____1732 -> begin
(fun s -> true)
end))
in ((check_z3version ());
(FStar_Util.start_process id1 (FStar_Pervasives_Native.fst cmd_and_args) (FStar_Pervasives_Native.snd cmd_and_args) (fun s -> (Prims.op_Equality s "Done!")) filter1);
)))


let new_z3proc_with_id : (Prims.string * Prims.string Prims.list)  ->  FStar_Util.proc = (

let ctr = (FStar_Util.mk_ref (~- ((Prims.parse_int "1"))))
in (fun cmd_and_args -> (

let uu____1779 = (

let uu____1781 = ((FStar_Util.incr ctr);
(

let uu____1784 = (FStar_ST.op_Bang ctr)
in (FStar_All.pipe_right uu____1784 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____1781))
in (new_z3proc uu____1779 cmd_and_args))))

type bgproc =
{ask : Prims.string  ->  Prims.string; refresh : unit  ->  Prims.string FStar_Pervasives_Native.option; restart : unit  ->  unit; store : FStar_SMTEncoding_QIReport.query_info  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  unit; extract : unit  ->  (FStar_SMTEncoding_QIReport.query_info * FStar_SMTEncoding_Term.decl Prims.list) Prims.list}


let __proj__Mkbgproc__item__ask : bgproc  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; store = store; extract = extract} -> begin
ask
end))


let __proj__Mkbgproc__item__refresh : bgproc  ->  unit  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; store = store; extract = extract} -> begin
refresh
end))


let __proj__Mkbgproc__item__restart : bgproc  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; store = store; extract = extract} -> begin
restart
end))


let __proj__Mkbgproc__item__store : bgproc  ->  FStar_SMTEncoding_QIReport.query_info  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; store = store; extract = extract} -> begin
store
end))


let __proj__Mkbgproc__item__extract : bgproc  ->  unit  ->  (FStar_SMTEncoding_QIReport.query_info * FStar_SMTEncoding_Term.decl Prims.list) Prims.list = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; store = store; extract = extract} -> begin
extract
end))


let cmd_and_args_to_string : (Prims.string * Prims.string Prims.list)  ->  Prims.string = (fun cmd_and_args -> (FStar_String.concat "" (("cmd=")::((FStar_Pervasives_Native.fst cmd_and_args))::(" args=[")::((FStar_String.concat ", " (FStar_Pervasives_Native.snd cmd_and_args)))::("]")::[])))


let bg_z3_proc : bgproc FStar_ST.ref = (

let the_z3proc = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let the_queries = (FStar_Util.mk_ref [])
in (

let the_z3proc_params = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some (((""), (("")::[])))))
in (

let the_z3proc_ask_count = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let make_new_z3_proc = (fun cmd_and_args -> ((

let uu____2317 = (

let uu____2320 = (new_z3proc_with_id cmd_and_args)
in FStar_Pervasives_Native.Some (uu____2320))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2317));
(FStar_ST.op_Colon_Equals the_z3proc_params (FStar_Pervasives_Native.Some (cmd_and_args)));
(FStar_ST.op_Colon_Equals the_z3proc_ask_count (Prims.parse_int "0"));
(FStar_ST.op_Colon_Equals the_queries []);
))
in (

let z3proc = (fun uu____2461 -> ((

let uu____2463 = (

let uu____2465 = (FStar_ST.op_Bang the_z3proc)
in (Prims.op_Equality uu____2465 FStar_Pervasives_Native.None))
in (match (uu____2463) with
| true -> begin
(

let uu____2494 = (z3_cmd_and_args ())
in (make_new_z3_proc uu____2494))
end
| uu____2503 -> begin
()
end));
(

let uu____2505 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.must uu____2505));
))
in (

let ask = (fun input -> ((FStar_Util.incr the_z3proc_ask_count);
(

let kill_handler = (fun uu____2547 -> "\nkilled\n")
in (

let uu____2549 = (z3proc ())
in (FStar_Util.ask_process uu____2549 input kill_handler)));
))
in (

let refresh = (fun uu____2558 -> (

let next_params = (z3_cmd_and_args ())
in (

let old_params = (

let uu____2577 = (FStar_ST.op_Bang the_z3proc_params)
in (FStar_Util.must uu____2577))
in (

let extra = (

let uu____2639 = (((FStar_Options.log_queries ()) || (

let uu____2642 = (FStar_ST.op_Bang the_z3proc_ask_count)
in (uu____2642 > (Prims.parse_int "0")))) || (not ((Prims.op_Equality old_params next_params))))
in (match (uu____2639) with
| true -> begin
((

let uu____2679 = ((FStar_Options.query_stats ()) && (

let uu____2682 = (

let uu____2684 = (FStar_ST.op_Bang the_z3proc)
in (Prims.op_Equality uu____2684 FStar_Pervasives_Native.None))
in (not (uu____2682))))
in (match (uu____2679) with
| true -> begin
(

let uu____2713 = (

let uu____2715 = (FStar_ST.op_Bang the_z3proc_ask_count)
in (FStar_Util.string_of_int uu____2715))
in (FStar_Util.print3 "Refreshing the z3proc (ask_count=%s old=[%s] new=[%s]) \n" uu____2713 (cmd_and_args_to_string old_params) (cmd_and_args_to_string next_params)))
end
| uu____2739 -> begin
()
end));
(

let out = (

let uu____2743 = (z3proc ())
in (FStar_Util.kill_z3_process uu____2743))
in ((make_new_z3_proc next_params);
(FStar_ST.op_Colon_Equals the_queries []);
FStar_Pervasives_Native.Some (out);
));
)
end
| uu____2788 -> begin
FStar_Pervasives_Native.None
end))
in ((query_logging.close_log ());
extra;
)))))
in (

let restart = (fun uu____2797 -> ((query_logging.close_log ());
(

let next_params = (z3_cmd_and_args ())
in (make_new_z3_proc next_params));
))
in (

let x = []
in (

let store = (fun info decls -> (

let uu____2826 = (

let uu____2835 = (FStar_ST.op_Bang the_queries)
in (FStar_List.append uu____2835 ((((info), (decls)))::[])))
in (FStar_ST.op_Colon_Equals the_queries uu____2826)))
in (

let extract = (fun uu____2947 -> (FStar_ST.op_Bang the_queries))
in (FStar_Util.mk_ref {ask = (FStar_Util.with_monitor x ask); refresh = (FStar_Util.with_monitor x refresh); restart = (FStar_Util.with_monitor x restart); store = store; extract = extract})))))))))))))


type smt_output_section =
Prims.string Prims.list

type smt_output =
{smt_result : smt_output_section; smt_reason_unknown : smt_output_section FStar_Pervasives_Native.option; smt_unsat_core : smt_output_section FStar_Pervasives_Native.option; smt_statistics : smt_output_section FStar_Pervasives_Native.option; smt_labels : smt_output_section FStar_Pervasives_Native.option}


let __proj__Mksmt_output__item__smt_result : smt_output  ->  smt_output_section = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels} -> begin
smt_result
end))


let __proj__Mksmt_output__item__smt_reason_unknown : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels} -> begin
smt_reason_unknown
end))


let __proj__Mksmt_output__item__smt_unsat_core : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels} -> begin
smt_unsat_core
end))


let __proj__Mksmt_output__item__smt_statistics : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels} -> begin
smt_statistics
end))


let __proj__Mksmt_output__item__smt_labels : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = smt_result; smt_reason_unknown = smt_reason_unknown; smt_unsat_core = smt_unsat_core; smt_statistics = smt_statistics; smt_labels = smt_labels} -> begin
smt_labels
end))


let smt_output_sections : Prims.string FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  Prims.string Prims.list  ->  smt_output = (fun log_file r lines -> (

let rec until = (fun tag lines1 -> (match (lines1) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (l)::lines2 -> begin
(match ((Prims.op_Equality tag l)) with
| true -> begin
FStar_Pervasives_Native.Some ((([]), (lines2)))
end
| uu____3269 -> begin
(

let uu____3271 = (until tag lines2)
in (FStar_Util.map_opt uu____3271 (fun uu____3307 -> (match (uu____3307) with
| (until_tag, rest) -> begin
(((l)::until_tag), (rest))
end))))
end)
end))
in (

let start_tag = (fun tag -> (Prims.op_Hat "<" (Prims.op_Hat tag ">")))
in (

let end_tag = (fun tag -> (Prims.op_Hat "</" (Prims.op_Hat tag ">")))
in (

let find_section = (fun tag lines1 -> (

let uu____3414 = (until (start_tag tag) lines1)
in (match (uu____3414) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (lines1))
end
| FStar_Pervasives_Native.Some (prefix1, suffix) -> begin
(

let uu____3484 = (until (end_tag tag) suffix)
in (match (uu____3484) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.op_Hat "Parse error: " (Prims.op_Hat (end_tag tag) " not found")))
end
| FStar_Pervasives_Native.Some (section, suffix1) -> begin
((FStar_Pervasives_Native.Some (section)), ((FStar_List.append prefix1 suffix1)))
end))
end)))
in (

let uu____3569 = (find_section "result" lines)
in (match (uu____3569) with
| (result_opt, lines1) -> begin
(

let result = (FStar_Util.must result_opt)
in (

let uu____3608 = (find_section "reason-unknown" lines1)
in (match (uu____3608) with
| (reason_unknown, lines2) -> begin
(

let uu____3640 = (find_section "unsat-core" lines2)
in (match (uu____3640) with
| (unsat_core, lines3) -> begin
(

let uu____3672 = (find_section "statistics" lines3)
in (match (uu____3672) with
| (statistics, lines4) -> begin
(

let uu____3704 = (find_section "labels" lines4)
in (match (uu____3704) with
| (labels, lines5) -> begin
(

let remaining = (

let uu____3740 = (until "Done!" lines5)
in (match (uu____3740) with
| FStar_Pervasives_Native.None -> begin
lines5
end
| FStar_Pervasives_Native.Some (prefix1, suffix) -> begin
(FStar_List.append prefix1 suffix)
end))
in ((match (remaining) with
| [] -> begin
()
end
| uu____3794 -> begin
(

let msg = (FStar_Util.format2 "%sUnexpected additional output from Z3: %s\n" (match (log_file) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (f) -> begin
(Prims.op_Hat f ": ")
end) (FStar_String.concat "\n" remaining))
in (FStar_Errors.log_issue r ((FStar_Errors.Warning_UnexpectedZ3Output), (msg))))
end);
(

let uu____3810 = (FStar_Util.must result_opt)
in {smt_result = uu____3810; smt_reason_unknown = reason_unknown; smt_unsat_core = unsat_core; smt_statistics = statistics; smt_labels = labels});
))
end))
end))
end))
end)))
end)))))))


let doZ3Exe : Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_QIReport.query_info  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.bool  ->  Prims.string  ->  FStar_SMTEncoding_Term.error_labels  ->  (z3status * z3statistics) = (fun log_file info decls fresh input label_messages -> (

let r = info.FStar_SMTEncoding_QIReport.query_info_range
in (

let parse = (fun z3out -> (

let lines = (FStar_All.pipe_right (FStar_String.split ((10)::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (

let smt_output = (smt_output_sections log_file r lines)
in (

let unsat_core = (match (smt_output.smt_unsat_core) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s) -> begin
(

let s1 = (FStar_Util.trim_string (FStar_String.concat " " s))
in (

let s2 = (FStar_Util.substring s1 (Prims.parse_int "1") ((FStar_String.length s1) - (Prims.parse_int "2")))
in (match ((FStar_Util.starts_with s2 "error")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3913 -> begin
(

let uu____3915 = (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_Util.sort_with FStar_String.compare))
in FStar_Pervasives_Native.Some (uu____3915))
end)))
end)
in (

let labels = (match (smt_output.smt_labels) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (lines1) -> begin
(

let rec lblnegs = (fun lines2 -> (match (lines2) with
| (lname)::("false")::rest when (FStar_Util.starts_with lname "label_") -> begin
(

let uu____3960 = (lblnegs rest)
in (lname)::uu____3960)
end
| (lname)::(uu____3966)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest)
end
| uu____3976 -> begin
[]
end))
in (

let lblnegs1 = (lblnegs lines1)
in (FStar_All.pipe_right lblnegs1 (FStar_List.collect (fun l -> (

let uu____4000 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____4040 -> (match (uu____4040) with
| (m, uu____4050, uu____4051) -> begin
(

let uu____4054 = (FStar_SMTEncoding_Term.fv_name m)
in (Prims.op_Equality uu____4054 l))
end))))
in (match (uu____4000) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (lbl, msg, r1) -> begin
(((lbl), (msg), (r1)))::[]
end)))))))
end)
in (

let statistics = (

let statistics = (FStar_Util.smap_create (Prims.parse_int "0"))
in (match (smt_output.smt_statistics) with
| FStar_Pervasives_Native.None -> begin
statistics
end
| FStar_Pervasives_Native.Some (lines1) -> begin
(

let parse_line = (fun line -> (

let pline = (FStar_Util.split (FStar_Util.trim_string line) ":")
in (match (pline) with
| ("(")::(entry)::[] -> begin
(

let tokens = (FStar_Util.split entry " ")
in (

let key = (FStar_List.hd tokens)
in (

let ltok = (FStar_List.nth tokens ((FStar_List.length tokens) - (Prims.parse_int "1")))
in (

let value = (match ((FStar_Util.ends_with ltok ")")) with
| true -> begin
(FStar_Util.substring ltok (Prims.parse_int "0") ((FStar_String.length ltok) - (Prims.parse_int "1")))
end
| uu____4151 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| ("")::(entry)::[] -> begin
(

let tokens = (FStar_Util.split entry " ")
in (

let key = (FStar_List.hd tokens)
in (

let ltok = (FStar_List.nth tokens ((FStar_List.length tokens) - (Prims.parse_int "1")))
in (

let value = (match ((FStar_Util.ends_with ltok ")")) with
| true -> begin
(FStar_Util.substring ltok (Prims.parse_int "0") ((FStar_String.length ltok) - (Prims.parse_int "1")))
end
| uu____4180 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| uu____4183 -> begin
()
end)))
in ((FStar_List.iter parse_line lines1);
statistics;
))
end))
in (

let reason_unknown = (FStar_Util.map_opt smt_output.smt_reason_unknown (fun x -> (

let ru = (FStar_String.concat " " x)
in (match ((FStar_Util.starts_with ru "(:reason-unknown \"")) with
| true -> begin
(

let reason = (FStar_Util.substring_from ru (FStar_String.length "(:reason-unknown \""))
in (

let res = (FStar_String.substring reason (Prims.parse_int "0") ((FStar_String.length reason) - (Prims.parse_int "2")))
in res))
end
| uu____4212 -> begin
ru
end))))
in (

let status = ((

let uu____4216 = (FStar_Options.debug_any ())
in (match (uu____4216) with
| true -> begin
(

let uu____4219 = (FStar_Util.format1 "Z3 says: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (FStar_All.pipe_left FStar_Util.print_string uu____4219))
end
| uu____4224 -> begin
()
end));
(match (smt_output.smt_result) with
| ("unsat")::[] -> begin
UNSAT (unsat_core)
end
| ("sat")::[] -> begin
SAT (((labels), (reason_unknown)))
end
| ("unknown")::[] -> begin
UNKNOWN (((labels), (reason_unknown)))
end
| ("timeout")::[] -> begin
TIMEOUT (((labels), (reason_unknown)))
end
| ("killed")::[] -> begin
((

let uu____4251 = (

let uu____4256 = (FStar_ST.op_Bang bg_z3_proc)
in uu____4256.restart)
in (uu____4251 ()));
KILLED;
)
end
| uu____4276 -> begin
(

let uu____4277 = (FStar_Util.format1 "Unexpected output from Z3: got output result: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (failwith uu____4277))
end);
)
in ((status), (statistics))))))))))
in (

let stdout1 = (match (fresh) with
| true -> begin
(

let proc = (

let uu____4286 = (z3_cmd_and_args ())
in (new_z3proc_with_id uu____4286))
in (

let kill_handler = (fun uu____4301 -> "\nkilled\n")
in (

let out = (FStar_Util.ask_process proc input kill_handler)
in (

let qip_output = (FStar_Util.kill_z3_process proc)
in ((

let uu____4308 = (FStar_Options.report_qi ())
in (match (uu____4308) with
| true -> begin
(

let query_data = (((info), (decls)))::[]
in (FStar_SMTEncoding_QIReport.qiprofile_analysis query_data qip_output))
end
| uu____4334 -> begin
()
end));
out;
)))))
end
| uu____4336 -> begin
(

let uu____4338 = (

let uu____4345 = (FStar_ST.op_Bang bg_z3_proc)
in uu____4345.ask)
in (uu____4338 input))
end)
in (

let uu____4365 = (parse (FStar_Util.trim_string stdout1))
in (match (uu____4365) with
| (status, statistics) -> begin
((

let uu____4377 = (FStar_Options.report_qi ())
in (match (uu____4377) with
| true -> begin
(match (status) with
| UNSAT (uu____4380) -> begin
(match (fresh) with
| true -> begin
()
end
| uu____4382 -> begin
(

let uu____4384 = (

let uu____4395 = (FStar_ST.op_Bang bg_z3_proc)
in uu____4395.store)
in (uu____4384 info decls))
end)
end
| uu____4415 -> begin
()
end)
end
| uu____4416 -> begin
()
end));
((status), (statistics));
)
end))))))


let z3_options : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n(set-option :model true)\n(set-option :smt.case_split 3)\n(set-option :smt.relevancy 2)\n")


let set_z3_options : Prims.string  ->  unit = (fun opts -> (FStar_ST.op_Colon_Equals z3_options opts))

type z3result =
{z3result_status : z3status; z3result_time : Prims.int; z3result_statistics : z3statistics; z3result_query_hash : Prims.string FStar_Pervasives_Native.option; z3result_query_decls : FStar_SMTEncoding_Term.decl Prims.list; z3result_log_file : Prims.string FStar_Pervasives_Native.option}


let __proj__Mkz3result__item__z3result_status : z3result  ->  z3status = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_log_file = z3result_log_file} -> begin
z3result_status
end))


let __proj__Mkz3result__item__z3result_time : z3result  ->  Prims.int = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_log_file = z3result_log_file} -> begin
z3result_time
end))


let __proj__Mkz3result__item__z3result_statistics : z3result  ->  z3statistics = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_log_file = z3result_log_file} -> begin
z3result_statistics
end))


let __proj__Mkz3result__item__z3result_query_hash : z3result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_log_file = z3result_log_file} -> begin
z3result_query_hash
end))


let __proj__Mkz3result__item__z3result_query_decls : z3result  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_log_file = z3result_log_file} -> begin
z3result_query_decls
end))


let __proj__Mkz3result__item__z3result_log_file : z3result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_log_file = z3result_log_file} -> begin
z3result_log_file
end))


let init : unit  ->  unit = (fun uu____4641 -> ())


let finish : unit  ->  unit = (fun uu____4647 -> ())


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let fresh_scope : scope_t FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let mk_fresh_scope : unit  ->  scope_t = (fun uu____4664 -> (FStar_ST.op_Bang fresh_scope))


let flatten_fresh_scope : unit  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun uu____4691 -> (

let uu____4692 = (

let uu____4697 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____4697))
in (FStar_List.flatten uu____4692)))


let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : Prims.string  ->  unit = (fun msg -> (FStar_Util.atomically (fun uu____4741 -> ((

let uu____4743 = (

let uu____4744 = (FStar_ST.op_Bang fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::uu____4744)
in (FStar_ST.op_Colon_Equals fresh_scope uu____4743));
(

let uu____4789 = (

let uu____4792 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____4792 ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____4789));
))))


let pop : Prims.string  ->  unit = (fun msg -> (FStar_Util.atomically (fun uu____4852 -> ((

let uu____4854 = (

let uu____4855 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.tl uu____4855))
in (FStar_ST.op_Colon_Equals fresh_scope uu____4854));
(

let uu____4900 = (

let uu____4903 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____4903 ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____4900));
))))


let snapshot : Prims.string  ->  (Prims.int * unit) = (fun msg -> (FStar_Common.snapshot push fresh_scope msg))


let rollback : Prims.string  ->  Prims.int FStar_Pervasives_Native.option  ->  unit = (fun msg depth -> (FStar_Common.rollback (fun uu____4990 -> (pop msg)) fresh_scope depth))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___1_5005 -> (match (uu___1_5005) with
| FStar_SMTEncoding_Term.Push -> begin
(failwith "Unexpected push/pop")
end
| FStar_SMTEncoding_Term.Pop -> begin
(failwith "Unexpected push/pop")
end
| uu____5008 -> begin
()
end))));
(

let uu____5010 = (FStar_ST.op_Bang fresh_scope)
in (match (uu____5010) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd1 decls))::tl1))
end
| uu____5061 -> begin
(failwith "Impossible")
end));
(

let uu____5063 = (

let uu____5066 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____5066 decls))
in (FStar_ST.op_Colon_Equals bg_scope uu____5063));
))


let refresh : unit  ->  unit = (fun uu____5120 -> (

let qdata = (

let uu____5130 = (

let uu____5143 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5143.extract)
in (uu____5130 ()))
in ((

let uu____5164 = (

let uu____5168 = (

let uu____5176 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5176.refresh)
in (uu____5168 ()))
in (match (uu____5164) with
| FStar_Pervasives_Native.Some (qip_output) -> begin
(

let uu____5199 = (FStar_Options.report_qi ())
in (match (uu____5199) with
| true -> begin
(FStar_SMTEncoding_QIReport.qiprofile_analysis qdata qip_output)
end
| uu____5202 -> begin
()
end))
end
| FStar_Pervasives_Native.None -> begin
()
end));
(

let uu____5205 = (flatten_fresh_scope ())
in (FStar_ST.op_Colon_Equals bg_scope uu____5205));
)))


let context_profile : FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun theory -> (

let uu____5241 = (FStar_List.fold_left (fun uu____5274 d -> (match (uu____5274) with
| (out, _total) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Module (name, decls) -> begin
(

let decls1 = (FStar_List.filter (fun uu___2_5343 -> (match (uu___2_5343) with
| FStar_SMTEncoding_Term.Assume (uu____5345) -> begin
true
end
| uu____5347 -> begin
false
end)) decls)
in (

let n1 = (FStar_List.length decls1)
in (((((name), (n1)))::out), ((n1 + _total)))))
end
| uu____5364 -> begin
((out), (_total))
end)
end)) (([]), ((Prims.parse_int "0"))) theory)
in (match (uu____5241) with
| (modules, total_decls) -> begin
(

let modules1 = (FStar_List.sortWith (fun uu____5426 uu____5427 -> (match (((uu____5426), (uu____5427))) with
| ((uu____5453, n1), (uu____5455, m)) -> begin
(m - n1)
end)) modules)
in ((match ((Prims.op_disEquality modules1 [])) with
| true -> begin
(

let uu____5493 = (FStar_Util.string_of_int total_decls)
in (FStar_Util.print1 "Z3 Proof Stats: context_profile with %s assertions\n" uu____5493))
end
| uu____5496 -> begin
()
end);
(FStar_List.iter (fun uu____5508 -> (match (uu____5508) with
| (m, n1) -> begin
(match ((Prims.op_disEquality n1 (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5524 = (FStar_Util.string_of_int n1)
in (FStar_Util.print2 "Z3 Proof Stats: %s produced %s SMT decls\n" m uu____5524))
end
| uu____5527 -> begin
()
end)
end)) modules1);
))
end)))


let mk_input : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (Prims.string * Prims.string FStar_Pervasives_Native.option * Prims.string FStar_Pervasives_Native.option) = (fun fresh theory -> (

let options = (FStar_ST.op_Bang z3_options)
in ((

let uu____5583 = (FStar_Options.print_z3_statistics ())
in (match (uu____5583) with
| true -> begin
(context_profile theory)
end
| uu____5586 -> begin
()
end));
(

let uu____5588 = (

let uu____5597 = ((FStar_Options.record_hints ()) || ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())))
in (match (uu____5597) with
| true -> begin
(

let uu____5608 = (

let uu____5619 = (FStar_All.pipe_right theory (FStar_Util.prefix_until (fun uu___3_5647 -> (match (uu___3_5647) with
| FStar_SMTEncoding_Term.CheckSat -> begin
true
end
| uu____5650 -> begin
false
end))))
in (FStar_All.pipe_right uu____5619 FStar_Option.get))
in (match (uu____5608) with
| (prefix1, check_sat, suffix) -> begin
(

let pp = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options))
in (

let suffix1 = (check_sat)::suffix
in (

let ps_lines = (pp prefix1)
in (

let ss_lines = (pp suffix1)
in (

let ps = (FStar_String.concat "\n" ps_lines)
in (

let ss = (FStar_String.concat "\n" ss_lines)
in (

let hs = (

let uu____5733 = (FStar_Options.keep_query_captions ())
in (match (uu____5733) with
| true -> begin
(

let uu____5737 = (FStar_All.pipe_right prefix1 (FStar_List.map (FStar_SMTEncoding_Term.declToSmt_no_caps options)))
in (FStar_All.pipe_right uu____5737 (FStar_String.concat "\n")))
end
| uu____5752 -> begin
ps
end))
in (

let uu____5754 = (

let uu____5758 = (FStar_Util.digest_of_string hs)
in FStar_Pervasives_Native.Some (uu____5758))
in (((Prims.op_Hat ps (Prims.op_Hat "\n" ss))), (uu____5754))))))))))
end))
end
| uu____5766 -> begin
(

let uu____5768 = (

let uu____5770 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory)
in (FStar_All.pipe_right uu____5770 (FStar_String.concat "\n")))
in ((uu____5768), (FStar_Pervasives_Native.None)))
end))
in (match (uu____5588) with
| (r, hash) -> begin
(

let log_file_name = (

let uu____5812 = (FStar_Options.log_queries ())
in (match (uu____5812) with
| true -> begin
(

let uu____5818 = (query_logging.write_to_log fresh r)
in FStar_Pervasives_Native.Some (uu____5818))
end
| uu____5821 -> begin
FStar_Pervasives_Native.None
end))
in ((r), (hash), (log_file_name)))
end));
)))


let cache_hit : Prims.string FStar_Pervasives_Native.option  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string FStar_Pervasives_Native.option  ->  z3result FStar_Pervasives_Native.option = (fun log_file cache qhash -> (

let uu____5869 = ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()))
in (match (uu____5869) with
| true -> begin
(match (qhash) with
| FStar_Pervasives_Native.Some (x) when (Prims.op_Equality qhash cache) -> begin
(

let stats = (FStar_Util.smap_create (Prims.parse_int "0"))
in ((FStar_Util.smap_add stats "fstar_cache_hit" "1");
(

let result = {z3result_status = UNSAT (FStar_Pervasives_Native.None); z3result_time = (Prims.parse_int "0"); z3result_statistics = stats; z3result_query_hash = qhash; z3result_query_decls = []; z3result_log_file = log_file}
in FStar_Pervasives_Native.Some (result));
))
end
| uu____5894 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____5898 -> begin
FStar_Pervasives_Native.None
end)))


let z3_job : Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_QIReport.query_info  ->  Prims.bool  ->  FStar_SMTEncoding_Term.error_labels  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.string FStar_Pervasives_Native.option  ->  unit  ->  z3result = (fun log_file qi fresh label_messages input decls qhash uu____5950 -> (

let uu____5961 = (

let uu____5971 = (

let uu____5975 = (query_logging.get_module_name ())
in FStar_Pervasives_Native.Some (uu____5975))
in (FStar_Profiling.profile (fun uu____5988 -> (FStar_All.try_with (fun uu___531_5999 -> (match (()) with
| () -> begin
(FStar_Util.record_time (fun uu____6014 -> (doZ3Exe log_file qi decls fresh input label_messages)))
end)) (fun uu___530_6017 -> ((refresh ());
(FStar_Exn.raise uu___530_6017);
)))) uu____5971 "FStar.SMTEncoding.Z3"))
in (match (uu____5961) with
| ((status, statistics), elapsed_time) -> begin
{z3result_status = status; z3result_time = elapsed_time; z3result_statistics = statistics; z3result_query_hash = qhash; z3result_query_decls = decls; z3result_log_file = log_file}
end)))


let ask : FStar_SMTEncoding_QIReport.query_info  ->  (FStar_SMTEncoding_Term.decl Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  Prims.bool  ->  z3result = (fun qi filter_theory cache label_messages qry _scope fresh -> (

let theory = (match (fresh) with
| true -> begin
(flatten_fresh_scope ())
end
| uu____6128 -> begin
(

let theory = (FStar_ST.op_Bang bg_scope)
in ((FStar_ST.op_Colon_Equals bg_scope []);
theory;
))
end)
in (

let theory1 = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let uu____6183 = (filter_theory theory1)
in (match (uu____6183) with
| (theory2, _used_unsat_core) -> begin
(

let uu____6199 = (mk_input fresh theory2)
in (match (uu____6199) with
| (input, qhash, log_file_name) -> begin
(

let fscp = (

let uu____6233 = (FStar_Options.report_qi ())
in (match (uu____6233) with
| true -> begin
(

let fscp = (

let uu____6241 = (flatten_fresh_scope ())
in (FStar_List.append uu____6241 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
in (

let uu____6244 = (filter_theory fscp)
in (match (uu____6244) with
| (fscp1, uu____6255) -> begin
fscp1
end)))
end
| uu____6262 -> begin
[]
end))
in (

let just_ask = (fun uu____6269 -> (z3_job log_file_name qi fresh label_messages input fscp qhash ()))
in (match (fresh) with
| true -> begin
(

let uu____6271 = (cache_hit log_file_name cache qhash)
in (match (uu____6271) with
| FStar_Pervasives_Native.Some (z3r) -> begin
z3r
end
| FStar_Pervasives_Native.None -> begin
(just_ask ())
end))
end
| uu____6275 -> begin
(just_ask ())
end)))
end))
end)))))




