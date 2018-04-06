
open Prims
open FStar_Pervasives

let _z3hash_checked : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let _z3hash_expected : Prims.string = "1f29cebd4df6"


let _z3url : Prims.string = "https://github.com/FStarLang/binaries/tree/master/z3-tested"


let parse_z3_version_lines : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun out -> (match ((FStar_Util.splitlines out)) with
| (x)::uu____46 -> begin
(

let trimmed = (FStar_Util.trim_string x)
in (

let parts = (FStar_Util.split trimmed " ")
in (

let rec aux = (fun uu___39_60 -> (match (uu___39_60) with
| (hash)::[] -> begin
(

let n1 = (Prims.min (FStar_String.strlen _z3hash_expected) (FStar_String.strlen hash))
in (

let hash_prefix = (FStar_String.substring hash (Prims.parse_int "0") n1)
in (match ((Prims.op_Equality hash_prefix _z3hash_expected)) with
| true -> begin
((

let uu____71 = (FStar_Options.debug_any ())
in (match (uu____71) with
| true -> begin
(

let msg = (FStar_Util.format1 "Successfully found expected Z3 commit hash %s\n" hash)
in (FStar_Util.print_string msg))
end
| uu____73 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| uu____74 -> begin
(

let msg = (FStar_Util.format2 "Expected Z3 commit hash \"%s\", got \"%s\"" _z3hash_expected trimmed)
in FStar_Pervasives_Native.Some (msg))
end)))
end
| (uu____76)::q -> begin
(aux q)
end
| uu____80 -> begin
FStar_Pervasives_Native.Some ("No Z3 commit hash found")
end))
in (aux parts))))
end
| uu____83 -> begin
FStar_Pervasives_Native.Some ("No Z3 version string found")
end))


let z3hash_warning_message : Prims.unit  ->  (FStar_Errors.raw_error * Prims.string) FStar_Pervasives_Native.option = (fun uu____94 -> (

let run_proc_result = (FStar_All.try_with (fun uu___45_114 -> (match (()) with
| () -> begin
(

let uu____123 = (

let uu____130 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc uu____130 "-version" ""))
in FStar_Pervasives_Native.Some (uu____123))
end)) (fun uu___44_139 -> (match (uu___44_139) with
| uu____148 -> begin
FStar_Pervasives_Native.None
end)))
in (match (run_proc_result) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((FStar_Errors.Error_Z3InvocationError), ("Could not run Z3")))
end
| FStar_Pervasives_Native.Some (uu____171, out, uu____173) -> begin
(

let uu____180 = (parse_z3_version_lines out)
in (match (uu____180) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (msg) -> begin
FStar_Pervasives_Native.Some (((FStar_Errors.Warning_Z3InvocationWarning), (msg)))
end))
end)))


let check_z3hash : Prims.unit  ->  Prims.unit = (fun uu____200 -> (

let uu____201 = (

let uu____202 = (FStar_ST.op_Bang _z3hash_checked)
in (not (uu____202)))
in (match (uu____201) with
| true -> begin
((FStar_ST.op_Colon_Equals _z3hash_checked true);
(

let uu____254 = (z3hash_warning_message ())
in (match (uu____254) with
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
| uu____272 -> begin
()
end)))


let ini_params : Prims.unit  ->  Prims.string = (fun uu____275 -> ((check_z3hash ());
(

let uu____277 = (

let uu____280 = (

let uu____283 = (

let uu____286 = (

let uu____287 = (

let uu____288 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int uu____288))
in (FStar_Util.format1 "smt.random_seed=%s" uu____287))
in (uu____286)::[])
in ("-smt2 -in auto_config=false model=true smt.relevancy=2 smt.case_split=3")::uu____283)
in (

let uu____289 = (FStar_Options.z3_cliopt ())
in (FStar_List.append uu____280 uu____289)))
in (FStar_String.concat " " uu____277));
))


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
| uu____334 -> begin
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
| uu____352 -> begin
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
| uu____388 -> begin
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
| uu____424 -> begin
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
| uu____453 -> begin
false
end))


type z3statistics =
Prims.string FStar_Util.smap


let status_tag : z3status  ->  Prims.string = (fun uu___40_458 -> (match (uu___40_458) with
| SAT (uu____459) -> begin
"sat"
end
| UNSAT (uu____466) -> begin
"unsat"
end
| UNKNOWN (uu____467) -> begin
"unknown"
end
| TIMEOUT (uu____474) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let status_string_and_errors : z3status  ->  (Prims.string * FStar_SMTEncoding_Term.error_labels) = (fun s -> (match (s) with
| KILLED -> begin
(((status_tag s)), ([]))
end
| UNSAT (uu____494) -> begin
(((status_tag s)), ([]))
end
| SAT (errs, msg) -> begin
(

let uu____503 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____503), (errs)))
end
| UNKNOWN (errs, msg) -> begin
(

let uu____511 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____511), (errs)))
end
| TIMEOUT (errs, msg) -> begin
(

let uu____519 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____519), (errs)))
end))


let tid : Prims.unit  ->  Prims.string = (fun uu____523 -> (

let uu____524 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right uu____524 FStar_Util.string_of_int)))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id1 -> (

let cond = (fun pid s -> (

let x = (Prims.op_Equality (FStar_Util.trim_string s) "Done!")
in x))
in (

let uu____536 = (FStar_Options.z3_exe ())
in (

let uu____537 = (ini_params ())
in (FStar_Util.start_process false id1 uu____536 uu____537 cond)))))

type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit; restart : Prims.unit  ->  Prims.unit}


let __proj__Mkbgproc__item__grab : bgproc  ->  Prims.unit  ->  FStar_Util.proc = (fun projectee -> (match (projectee) with
| {grab = __fname__grab; release = __fname__release; refresh = __fname__refresh; restart = __fname__restart} -> begin
__fname__grab
end))


let __proj__Mkbgproc__item__release : bgproc  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {grab = __fname__grab; release = __fname__release; refresh = __fname__refresh; restart = __fname__restart} -> begin
__fname__release
end))


let __proj__Mkbgproc__item__refresh : bgproc  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {grab = __fname__grab; release = __fname__release; refresh = __fname__refresh; restart = __fname__restart} -> begin
__fname__refresh
end))


let __proj__Mkbgproc__item__restart : bgproc  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {grab = __fname__grab; release = __fname__release; refresh = __fname__refresh; restart = __fname__restart} -> begin
__fname__restart
end))

type query_log =
{get_module_name : Prims.unit  ->  Prims.string; set_module_name : Prims.string  ->  Prims.unit; write_to_log : Prims.string  ->  Prims.unit; close_log : Prims.unit  ->  Prims.unit; log_file_name : Prims.unit  ->  Prims.string}


let __proj__Mkquery_log__item__get_module_name : query_log  ->  Prims.unit  ->  Prims.string = (fun projectee -> (match (projectee) with
| {get_module_name = __fname__get_module_name; set_module_name = __fname__set_module_name; write_to_log = __fname__write_to_log; close_log = __fname__close_log; log_file_name = __fname__log_file_name} -> begin
__fname__get_module_name
end))


let __proj__Mkquery_log__item__set_module_name : query_log  ->  Prims.string  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {get_module_name = __fname__get_module_name; set_module_name = __fname__set_module_name; write_to_log = __fname__write_to_log; close_log = __fname__close_log; log_file_name = __fname__log_file_name} -> begin
__fname__set_module_name
end))


let __proj__Mkquery_log__item__write_to_log : query_log  ->  Prims.string  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {get_module_name = __fname__get_module_name; set_module_name = __fname__set_module_name; write_to_log = __fname__write_to_log; close_log = __fname__close_log; log_file_name = __fname__log_file_name} -> begin
__fname__write_to_log
end))


let __proj__Mkquery_log__item__close_log : query_log  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {get_module_name = __fname__get_module_name; set_module_name = __fname__set_module_name; write_to_log = __fname__write_to_log; close_log = __fname__close_log; log_file_name = __fname__log_file_name} -> begin
__fname__close_log
end))


let __proj__Mkquery_log__item__log_file_name : query_log  ->  Prims.unit  ->  Prims.string = (fun projectee -> (match (projectee) with
| {get_module_name = __fname__get_module_name; set_module_name = __fname__set_module_name; write_to_log = __fname__write_to_log; close_log = __fname__close_log; log_file_name = __fname__log_file_name} -> begin
__fname__log_file_name
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

let get_module_name = (fun uu____945 -> (

let uu____946 = (FStar_ST.op_Bang current_module_name)
in (match (uu____946) with
| FStar_Pervasives_Native.None -> begin
(failwith "Module name not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in (

let new_log_file = (fun uu____1052 -> (

let uu____1053 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1053) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let file_name = (

let uu____1157 = (

let uu____1164 = (FStar_ST.op_Bang used_file_names)
in (FStar_List.tryFind (fun uu____1285 -> (match (uu____1285) with
| (m, uu____1291) -> begin
(Prims.op_Equality n1 m)
end)) uu____1164))
in (match (uu____1157) with
| FStar_Pervasives_Native.None -> begin
((

let uu____1297 = (

let uu____1304 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((Prims.parse_int "0"))))::uu____1304)
in (FStar_ST.op_Colon_Equals used_file_names uu____1297));
n1;
)
end
| FStar_Pervasives_Native.Some (uu____1529, k) -> begin
((

let uu____1536 = (

let uu____1543 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((k + (Prims.parse_int "1")))))::uu____1543)
in (FStar_ST.op_Colon_Equals used_file_names uu____1536));
(

let uu____1768 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n1 uu____1768));
)
end))
in (

let file_name1 = (FStar_Util.format1 "queries-%s.smt2" file_name)
in ((FStar_ST.op_Colon_Equals current_file_name (FStar_Pervasives_Native.Some (file_name1)));
(

let fh = (FStar_Util.open_file_for_writing file_name1)
in ((FStar_ST.op_Colon_Equals log_file_opt (FStar_Pervasives_Native.Some (fh)));
fh;
));
)))
end)))
in (

let get_log_file = (fun uu____1974 -> (

let uu____1975 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____1975) with
| FStar_Pervasives_Native.None -> begin
(new_log_file ())
end
| FStar_Pervasives_Native.Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____2082 = (get_log_file ())
in (FStar_Util.append_to_file uu____2082 str)))
in (

let write_to_new_log = (fun str -> (

let dir_name = (

let uu____2088 = (FStar_ST.op_Bang current_file_name)
in (match (uu____2088) with
| FStar_Pervasives_Native.None -> begin
(

let dir_name = (

let uu____2191 = (FStar_ST.op_Bang current_module_name)
in (match (uu____2191) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(FStar_Util.format1 "queries-%s" n1)
end))
in ((FStar_Util.mkdir true dir_name);
(FStar_ST.op_Colon_Equals current_file_name (FStar_Pervasives_Native.Some (dir_name)));
dir_name;
))
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end))
in (

let qnum = (FStar_ST.op_Bang query_number)
in ((

let uu____2493 = (

let uu____2494 = (FStar_ST.op_Bang query_number)
in (uu____2494 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals query_number uu____2493));
(

let file_name = (

let uu____2686 = (FStar_Util.string_of_int qnum)
in (FStar_Util.format1 "query-%s.smt2" uu____2686))
in (

let file_name1 = (FStar_Util.concat_dir_filename dir_name file_name)
in (FStar_Util.write_file file_name1 str)));
))))
in (

let write_to_log = (fun str -> (

let uu____2692 = (

let uu____2693 = (FStar_Options.n_cores ())
in (uu____2693 > (Prims.parse_int "1")))
in (match (uu____2692) with
| true -> begin
(write_to_new_log str)
end
| uu____2694 -> begin
(append_to_log str)
end)))
in (

let close_log = (fun uu____2698 -> (

let uu____2699 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____2699) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (fh) -> begin
((FStar_Util.close_file fh);
(FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None);
)
end)))
in (

let log_file_name = (fun uu____2905 -> (

let uu____2906 = (FStar_ST.op_Bang current_file_name)
in (match (uu____2906) with
| FStar_Pervasives_Native.None -> begin
(failwith "no log file")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in {get_module_name = get_module_name; set_module_name = set_module_name; write_to_log = write_to_log; close_log = close_log; log_file_name = log_file_name}))))))))))))))


let bg_z3_proc : bgproc = (

let the_z3proc = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let new_proc = (

let ctr = (FStar_Util.mk_ref (~- ((Prims.parse_int "1"))))
in (fun uu____3022 -> (

let uu____3023 = (

let uu____3024 = ((FStar_Util.incr ctr);
(

let uu____3131 = (FStar_ST.op_Bang ctr)
in (FStar_All.pipe_right uu____3131 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____3024))
in (new_z3proc uu____3023))))
in (

let z3proc = (fun uu____3230 -> ((

let uu____3232 = (

let uu____3233 = (FStar_ST.op_Bang the_z3proc)
in (Prims.op_Equality uu____3233 FStar_Pervasives_Native.None))
in (match (uu____3232) with
| true -> begin
(

let uu____3337 = (

let uu____3340 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____3340))
in (FStar_ST.op_Colon_Equals the_z3proc uu____3337))
end
| uu____3440 -> begin
()
end));
(

let uu____3441 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.must uu____3441));
))
in (

let x = []
in (

let grab = (fun uu____3549 -> ((FStar_Util.monitor_enter x);
(z3proc ());
))
in (

let release = (fun uu____3556 -> (FStar_Util.monitor_exit x))
in (

let refresh = (fun uu____3562 -> (

let proc = (grab ())
in ((FStar_Util.kill_process proc);
(

let uu____3566 = (

let uu____3569 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____3569))
in (FStar_ST.op_Colon_Equals the_z3proc uu____3566));
(query_logging.close_log ());
(release ());
)))
in (

let restart = (fun uu____3673 -> ((FStar_Util.monitor_enter ());
(query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(

let uu____3777 = (

let uu____3780 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____3780))
in (FStar_ST.op_Colon_Equals the_z3proc uu____3777));
(FStar_Util.monitor_exit ());
))
in {grab = grab; release = release; refresh = refresh; restart = restart}))))))))


let at_log_file : Prims.unit  ->  Prims.string = (fun uu____3882 -> (

let uu____3883 = (FStar_Options.log_queries ())
in (match (uu____3883) with
| true -> begin
(

let uu____3884 = (query_logging.log_file_name ())
in (Prims.strcat "@" uu____3884))
end
| uu____3885 -> begin
""
end)))


type smt_output_section =
Prims.string Prims.list

type smt_output =
{smt_result : smt_output_section; smt_reason_unknown : smt_output_section FStar_Pervasives_Native.option; smt_unsat_core : smt_output_section FStar_Pervasives_Native.option; smt_statistics : smt_output_section FStar_Pervasives_Native.option; smt_labels : smt_output_section FStar_Pervasives_Native.option}


let __proj__Mksmt_output__item__smt_result : smt_output  ->  smt_output_section = (fun projectee -> (match (projectee) with
| {smt_result = __fname__smt_result; smt_reason_unknown = __fname__smt_reason_unknown; smt_unsat_core = __fname__smt_unsat_core; smt_statistics = __fname__smt_statistics; smt_labels = __fname__smt_labels} -> begin
__fname__smt_result
end))


let __proj__Mksmt_output__item__smt_reason_unknown : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = __fname__smt_result; smt_reason_unknown = __fname__smt_reason_unknown; smt_unsat_core = __fname__smt_unsat_core; smt_statistics = __fname__smt_statistics; smt_labels = __fname__smt_labels} -> begin
__fname__smt_reason_unknown
end))


let __proj__Mksmt_output__item__smt_unsat_core : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = __fname__smt_result; smt_reason_unknown = __fname__smt_reason_unknown; smt_unsat_core = __fname__smt_unsat_core; smt_statistics = __fname__smt_statistics; smt_labels = __fname__smt_labels} -> begin
__fname__smt_unsat_core
end))


let __proj__Mksmt_output__item__smt_statistics : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = __fname__smt_result; smt_reason_unknown = __fname__smt_reason_unknown; smt_unsat_core = __fname__smt_unsat_core; smt_statistics = __fname__smt_statistics; smt_labels = __fname__smt_labels} -> begin
__fname__smt_statistics
end))


let __proj__Mksmt_output__item__smt_labels : smt_output  ->  smt_output_section FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {smt_result = __fname__smt_result; smt_reason_unknown = __fname__smt_reason_unknown; smt_unsat_core = __fname__smt_unsat_core; smt_statistics = __fname__smt_statistics; smt_labels = __fname__smt_labels} -> begin
__fname__smt_labels
end))


let smt_output_sections : Prims.string Prims.list  ->  smt_output = (fun lines -> (

let rec until = (fun tag lines1 -> (match (lines1) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (l)::lines2 -> begin
(match ((Prims.op_Equality tag l)) with
| true -> begin
FStar_Pervasives_Native.Some ((([]), (lines2)))
end
| uu____4084 -> begin
(

let uu____4085 = (until tag lines2)
in (FStar_Util.map_opt uu____4085 (fun uu____4115 -> (match (uu____4115) with
| (until_tag, rest) -> begin
(((l)::until_tag), (rest))
end))))
end)
end))
in (

let start_tag = (fun tag -> (Prims.strcat "<" (Prims.strcat tag ">")))
in (

let end_tag = (fun tag -> (Prims.strcat "</" (Prims.strcat tag ">")))
in (

let find_section = (fun tag lines1 -> (

let uu____4185 = (until (start_tag tag) lines1)
in (match (uu____4185) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (lines1))
end
| FStar_Pervasives_Native.Some (prefix1, suffix) -> begin
(

let uu____4240 = (until (end_tag tag) suffix)
in (match (uu____4240) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Parse error: " (Prims.strcat (end_tag tag) " not found")))
end
| FStar_Pervasives_Native.Some (section, suffix1) -> begin
((FStar_Pervasives_Native.Some (section)), ((FStar_List.append prefix1 suffix1)))
end))
end)))
in (

let uu____4305 = (find_section "result" lines)
in (match (uu____4305) with
| (result_opt, lines1) -> begin
(

let result = (FStar_Util.must result_opt)
in (

let uu____4335 = (find_section "reason-unknown" lines1)
in (match (uu____4335) with
| (reason_unknown, lines2) -> begin
(

let uu____4360 = (find_section "unsat-core" lines2)
in (match (uu____4360) with
| (unsat_core, lines3) -> begin
(

let uu____4385 = (find_section "statistics" lines3)
in (match (uu____4385) with
| (statistics, lines4) -> begin
(

let uu____4410 = (find_section "labels" lines4)
in (match (uu____4410) with
| (labels, lines5) -> begin
(

let remaining = (

let uu____4438 = (until "Done!" lines5)
in (match (uu____4438) with
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
| uu____4478 -> begin
(

let uu____4481 = (

let uu____4486 = (

let uu____4487 = (query_logging.get_module_name ())
in (FStar_Util.format2 "%s: Unexpected output from Z3: %s\n" uu____4487 (FStar_String.concat "\n" remaining)))
in ((FStar_Errors.Warning_UnexpectedZ3Output), (uu____4486)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____4481))
end);
(

let uu____4488 = (FStar_Util.must result_opt)
in {smt_result = uu____4488; smt_reason_unknown = reason_unknown; smt_unsat_core = unsat_core; smt_statistics = statistics; smt_labels = labels});
))
end))
end))
end))
end)))
end)))))))


let doZ3Exe : Prims.bool  ->  Prims.string  ->  FStar_SMTEncoding_Term.error_labels  ->  (z3status * z3statistics) = (fun fresh input label_messages -> (

let parse = (fun z3out -> (

let lines = (FStar_All.pipe_right (FStar_String.split ((10)::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (

let smt_output = (smt_output_sections lines)
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
| uu____4547 -> begin
(

let uu____4548 = (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_Util.sort_with FStar_String.compare))
in FStar_Pervasives_Native.Some (uu____4548))
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

let uu____4609 = (lblnegs rest)
in (lname)::uu____4609)
end
| (lname)::(uu____4613)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest)
end
| uu____4617 -> begin
[]
end))
in (

let lblnegs1 = (lblnegs lines1)
in (FStar_All.pipe_right lblnegs1 (FStar_List.collect (fun l -> (

let uu____4650 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____4689 -> (match (uu____4689) with
| (m, uu____4701, uu____4702) -> begin
(Prims.op_Equality (FStar_Pervasives_Native.fst m) l)
end))))
in (match (uu____4650) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
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
| uu____4805 -> begin
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
| uu____4813 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| uu____4814 -> begin
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
| uu____4829 -> begin
ru
end))))
in (

let status = ((

let uu____4832 = (FStar_Options.debug_any ())
in (match (uu____4832) with
| true -> begin
(

let uu____4833 = (FStar_Util.format1 "Z3 says: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (FStar_All.pipe_left FStar_Util.print_string uu____4833))
end
| uu____4834 -> begin
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
((bg_z3_proc.restart ());
KILLED;
)
end
| uu____4878 -> begin
(

let uu____4879 = (FStar_Util.format1 "Unexpected output from Z3: got output result: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (failwith uu____4879))
end);
)
in ((status), (statistics))))))))))
in (

let cond = (fun pid s -> (

let x = (Prims.op_Equality (FStar_Util.trim_string s) "Done!")
in x))
in (

let stdout1 = (match (fresh) with
| true -> begin
(

let uu____4889 = (tid ())
in (

let uu____4890 = (FStar_Options.z3_exe ())
in (

let uu____4891 = (ini_params ())
in (FStar_Util.launch_process false uu____4889 uu____4890 uu____4891 input cond))))
end
| uu____4892 -> begin
(

let proc = (bg_z3_proc.grab ())
in (

let stdout1 = (FStar_Util.ask_process proc input)
in ((bg_z3_proc.release ());
stdout1;
)))
end)
in (parse (FStar_Util.trim_string stdout1))))))


let z3_options : Prims.unit  ->  Prims.string = (fun uu____4898 -> "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n")

type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}


let __proj__Mkjob__item__job : 'a . 'a job  ->  Prims.unit  ->  'a = (fun projectee -> (match (projectee) with
| {job = __fname__job; callback = __fname__callback} -> begin
__fname__job
end))


let __proj__Mkjob__item__callback : 'a . 'a job  ->  'a  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {job = __fname__job; callback = __fname__callback} -> begin
__fname__callback
end))

type z3result =
{z3result_status : z3status; z3result_time : Prims.int; z3result_statistics : z3statistics; z3result_query_hash : Prims.string FStar_Pervasives_Native.option}


let __proj__Mkz3result__item__z3result_status : z3result  ->  z3status = (fun projectee -> (match (projectee) with
| {z3result_status = __fname__z3result_status; z3result_time = __fname__z3result_time; z3result_statistics = __fname__z3result_statistics; z3result_query_hash = __fname__z3result_query_hash} -> begin
__fname__z3result_status
end))


let __proj__Mkz3result__item__z3result_time : z3result  ->  Prims.int = (fun projectee -> (match (projectee) with
| {z3result_status = __fname__z3result_status; z3result_time = __fname__z3result_time; z3result_statistics = __fname__z3result_statistics; z3result_query_hash = __fname__z3result_query_hash} -> begin
__fname__z3result_time
end))


let __proj__Mkz3result__item__z3result_statistics : z3result  ->  z3statistics = (fun projectee -> (match (projectee) with
| {z3result_status = __fname__z3result_status; z3result_time = __fname__z3result_time; z3result_statistics = __fname__z3result_statistics; z3result_query_hash = __fname__z3result_query_hash} -> begin
__fname__z3result_statistics
end))


let __proj__Mkz3result__item__z3result_query_hash : z3result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {z3result_status = __fname__z3result_status; z3result_time = __fname__z3result_time; z3result_statistics = __fname__z3result_statistics; z3result_query_hash = __fname__z3result_query_hash} -> begin
__fname__z3result_query_hash
end))


type z3job =
z3result job


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let with_monitor : 'Auu____5099 'Auu____5100 . 'Auu____5099  ->  (Prims.unit  ->  'Auu____5100)  ->  'Auu____5100 = (fun m f -> ((FStar_Util.monitor_enter m);
(

let res = (f ())
in ((FStar_Util.monitor_exit m);
res;
));
))


let z3_job : Prims.bool  ->  FStar_SMTEncoding_Term.error_labels  ->  Prims.string  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.unit  ->  z3result = (fun fresh label_messages input qhash uu____5133 -> (

let start = (FStar_Util.now ())
in (

let uu____5137 = (FStar_All.try_with (fun uu___47_5147 -> (match (()) with
| () -> begin
(doZ3Exe fresh input label_messages)
end)) (fun uu___46_5156 -> (match (uu___46_5156) with
| uu____5161 when (

let uu____5162 = (FStar_Options.trace_error ())
in (not (uu____5162))) -> begin
((bg_z3_proc.refresh ());
(

let uu____5164 = (FStar_Util.smap_create (Prims.parse_int "0"))
in ((UNKNOWN ((([]), (FStar_Pervasives_Native.Some ("Z3 raised an exception"))))), (uu____5164)));
)
end)))
in (match (uu____5137) with
| (status, statistics) -> begin
(

let uu____5175 = (

let uu____5180 = (FStar_Util.now ())
in (FStar_Util.time_diff start uu____5180))
in (match (uu____5175) with
| (uu____5181, elapsed_time) -> begin
{z3result_status = status; z3result_time = elapsed_time; z3result_statistics = statistics; z3result_query_hash = qhash}
end))
end))))


let running : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun uu____5226 -> (

let j = (

let uu____5228 = (FStar_ST.op_Bang job_queue)
in (match (uu____5228) with
| [] -> begin
(failwith "Impossible")
end
| (hd1)::tl1 -> begin
((FStar_ST.op_Colon_Equals job_queue tl1);
hd1;
)
end))
in ((FStar_Util.incr pending_jobs);
(FStar_Util.monitor_exit job_queue);
(run_job j);
(with_monitor job_queue (fun uu____5307 -> (FStar_Util.decr pending_jobs)));
(dequeue ());
)))
and dequeue : Prims.unit  ->  Prims.unit = (fun uu____5309 -> (

let uu____5310 = (FStar_ST.op_Bang running)
in if uu____5310 then begin
(

let rec aux = (fun uu____5339 -> ((FStar_Util.monitor_enter job_queue);
(

let uu____5345 = (FStar_ST.op_Bang job_queue)
in (match (uu____5345) with
| [] -> begin
((FStar_Util.monitor_exit job_queue);
(FStar_Util.sleep (Prims.parse_int "50"));
(aux ());
)
end
| uu____5383 -> begin
(dequeue' ())
end));
))
in (aux ()))
end else begin
()
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (

let uu____5387 = (j.job ())
in (FStar_All.pipe_left j.callback uu____5387)))


let init : Prims.unit  ->  Prims.unit = (fun uu____5390 -> ((FStar_ST.op_Colon_Equals running true);
(

let n_cores1 = (FStar_Options.n_cores ())
in (match ((n_cores1 > (Prims.parse_int "1"))) with
| true -> begin
(

let rec aux = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____5422 -> begin
((FStar_Util.spawn dequeue);
(aux (n1 - (Prims.parse_int "1")));
)
end))
in (aux n_cores1))
end
| uu____5424 -> begin
()
end));
))


let enqueue : z3job  ->  Prims.unit = (fun j -> ((FStar_Util.monitor_enter job_queue);
(

let uu____5434 = (

let uu____5437 = (FStar_ST.op_Bang job_queue)
in (FStar_List.append uu____5437 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue uu____5434));
(FStar_Util.monitor_pulse job_queue);
(FStar_Util.monitor_exit job_queue);
))


let finish : Prims.unit  ->  Prims.unit = (fun uu____5509 -> (

let rec aux = (fun uu____5513 -> (

let uu____5514 = (with_monitor job_queue (fun uu____5530 -> (

let uu____5531 = (FStar_ST.op_Bang pending_jobs)
in (

let uu____5557 = (

let uu____5558 = (FStar_ST.op_Bang job_queue)
in (FStar_List.length uu____5558))
in ((uu____5531), (uu____5557))))))
in (match (uu____5514) with
| (n1, m) -> begin
(match ((Prims.op_Equality (n1 + m) (Prims.parse_int "0"))) with
| true -> begin
(FStar_ST.op_Colon_Equals running false)
end
| uu____5625 -> begin
((FStar_Util.sleep (Prims.parse_int "500"));
(aux ());
)
end)
end)))
in (aux ())))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let mk_fresh_scope : Prims.unit  ->  scope_t = (fun uu____5682 -> (FStar_ST.op_Bang fresh_scope))


let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : Prims.string  ->  Prims.unit = (fun msg -> ((

let uu____5761 = (

let uu____5766 = (FStar_ST.op_Bang fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::uu____5766)
in (FStar_ST.op_Colon_Equals fresh_scope uu____5761));
(

let uu____5839 = (

let uu____5842 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____5842 ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____5839));
))


let pop : Prims.string  ->  Prims.unit = (fun msg -> ((

let uu____5907 = (

let uu____5912 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.tl uu____5912))
in (FStar_ST.op_Colon_Equals fresh_scope uu____5907));
(

let uu____5985 = (

let uu____5988 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____5988 ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____5985));
))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___41_6060 -> (match (uu___41_6060) with
| FStar_SMTEncoding_Term.Push -> begin
(failwith "Unexpected push/pop")
end
| FStar_SMTEncoding_Term.Pop -> begin
(failwith "Unexpected push/pop")
end
| uu____6061 -> begin
()
end))));
(

let uu____6063 = (FStar_ST.op_Bang fresh_scope)
in (match (uu____6063) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd1 decls))::tl1))
end
| uu____6146 -> begin
(failwith "Impossible")
end));
(

let uu____6151 = (

let uu____6154 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____6154 decls))
in (FStar_ST.op_Colon_Equals bg_scope uu____6151));
))


let refresh : Prims.unit  ->  Prims.unit = (fun uu____6217 -> ((

let uu____6219 = (

let uu____6220 = (FStar_Options.n_cores ())
in (uu____6220 < (Prims.parse_int "2")))
in (match (uu____6219) with
| true -> begin
(bg_z3_proc.refresh ())
end
| uu____6221 -> begin
()
end));
(

let uu____6222 = (

let uu____6225 = (

let uu____6230 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____6230))
in (FStar_List.flatten uu____6225))
in (FStar_ST.op_Colon_Equals bg_scope uu____6222));
))


let mk_input : FStar_SMTEncoding_Term.decl Prims.list  ->  (Prims.string * Prims.string FStar_Pervasives_Native.option) = (fun theory -> (

let options = (z3_options ())
in (

let uu____6313 = (

let uu____6320 = ((FStar_Options.record_hints ()) || ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())))
in (match (uu____6320) with
| true -> begin
(

let uu____6327 = (

let uu____6338 = (FStar_All.pipe_right theory (FStar_Util.prefix_until (fun uu___42_6366 -> (match (uu___42_6366) with
| FStar_SMTEncoding_Term.CheckSat -> begin
true
end
| uu____6367 -> begin
false
end))))
in (FStar_All.pipe_right uu____6338 FStar_Option.get))
in (match (uu____6327) with
| (prefix1, check_sat, suffix) -> begin
(

let pp = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options))
in (

let pp_no_cap = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt_no_caps options))
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

let uncaption = (fun uu___43_6445 -> (match (uu___43_6445) with
| FStar_SMTEncoding_Term.Caption (uu____6446) -> begin
FStar_SMTEncoding_Term.Caption ("")
end
| FStar_SMTEncoding_Term.Assume (a) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___48_6450 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___48_6450.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.None; FStar_SMTEncoding_Term.assumption_name = uu___48_6450.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = uu___48_6450.FStar_SMTEncoding_Term.assumption_fact_ids}))
end
| FStar_SMTEncoding_Term.DeclFun (n1, a, s, uu____6454) -> begin
FStar_SMTEncoding_Term.DeclFun (((n1), (a), (s), (FStar_Pervasives_Native.None)))
end
| FStar_SMTEncoding_Term.DefineFun (n1, a, s, b, uu____6467) -> begin
FStar_SMTEncoding_Term.DefineFun (((n1), (a), (s), (b), (FStar_Pervasives_Native.None)))
end
| d -> begin
d
end))
in (

let hs = (

let uu____6478 = (

let uu____6481 = (

let uu____6484 = (FStar_All.pipe_right prefix1 (FStar_List.map uncaption))
in (FStar_All.pipe_right uu____6484 pp_no_cap))
in (FStar_All.pipe_right uu____6481 (FStar_List.filter (fun s -> (Prims.op_disEquality s "")))))
in (FStar_All.pipe_right uu____6478 (FStar_String.concat "\n")))
in (

let uu____6503 = (

let uu____6506 = (FStar_Util.digest_of_string hs)
in FStar_Pervasives_Native.Some (uu____6506))
in (((Prims.strcat ps (Prims.strcat "\n" ss))), (uu____6503))))))))))))
end))
end
| uu____6509 -> begin
(

let uu____6510 = (

let uu____6511 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory)
in (FStar_All.pipe_right uu____6511 (FStar_String.concat "\n")))
in ((uu____6510), (FStar_Pervasives_Native.None)))
end))
in (match (uu____6313) with
| (r, hash) -> begin
((

let uu____6531 = (FStar_Options.log_queries ())
in (match (uu____6531) with
| true -> begin
(query_logging.write_to_log r)
end
| uu____6532 -> begin
()
end));
((r), (hash));
)
end))))


type cb =
z3result  ->  Prims.unit


let cache_hit : Prims.string FStar_Pervasives_Native.option  ->  Prims.string FStar_Pervasives_Native.option  ->  cb  ->  Prims.bool = (fun cache qhash cb -> (

let uu____6556 = ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()))
in (match (uu____6556) with
| true -> begin
(match (qhash) with
| FStar_Pervasives_Native.Some (x) when (Prims.op_Equality qhash cache) -> begin
(

let stats = (FStar_Util.smap_create (Prims.parse_int "0"))
in ((FStar_Util.smap_add stats "fstar_cache_hit" "1");
(

let result = {z3result_status = UNSAT (FStar_Pervasives_Native.None); z3result_time = (Prims.parse_int "0"); z3result_statistics = stats; z3result_query_hash = qhash}
in ((cb result);
true;
));
))
end
| uu____6567 -> begin
false
end)
end
| uu____6570 -> begin
false
end)))


let ask_1_core : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  cb  ->  Prims.unit = (fun filter_theory cache label_messages qry cb -> (

let theory = (

let uu____6608 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____6608 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
in (

let uu____6640 = (filter_theory theory)
in (match (uu____6640) with
| (theory1, used_unsat_core) -> begin
(

let uu____6647 = (mk_input theory1)
in (match (uu____6647) with
| (input, qhash) -> begin
((FStar_ST.op_Colon_Equals bg_scope []);
(

let uu____6690 = (

let uu____6691 = (cache_hit cache qhash cb)
in (not (uu____6691)))
in (match (uu____6690) with
| true -> begin
(run_job {job = (z3_job false label_messages input qhash); callback = cb})
end
| uu____6696 -> begin
()
end));
)
end))
end))))


let ask_n_cores : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  Prims.unit = (fun filter_theory cache label_messages qry scope cb -> (

let theory = (

let uu____6741 = (match (scope) with
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_List.rev s)
end
| FStar_Pervasives_Native.None -> begin
((FStar_ST.op_Colon_Equals bg_scope []);
(

let uu____6783 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____6783));
)
end)
in (FStar_List.flatten uu____6741))
in (

let theory1 = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let uu____6826 = (filter_theory theory1)
in (match (uu____6826) with
| (theory2, used_unsat_core) -> begin
(

let uu____6833 = (mk_input theory2)
in (match (uu____6833) with
| (input, qhash) -> begin
(

let uu____6846 = (

let uu____6847 = (cache_hit cache qhash cb)
in (not (uu____6847)))
in (match (uu____6846) with
| true -> begin
(enqueue {job = (z3_job true label_messages input qhash); callback = cb})
end
| uu____6852 -> begin
()
end))
end))
end)))))


let ask : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  Prims.unit = (fun filter1 cache label_messages qry scope cb -> (

let uu____6896 = (

let uu____6897 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____6897 (Prims.parse_int "1")))
in (match (uu____6896) with
| true -> begin
(ask_1_core filter1 cache label_messages qry cb)
end
| uu____6900 -> begin
(ask_n_cores filter1 cache label_messages qry scope cb)
end)))




