
open Prims
open FStar_Pervasives

let _z3hash_checked : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let _z3hash_expected : Prims.string = "1f29cebd4df6"


let _z3url : Prims.string = "https://github.com/FStarLang/binaries/tree/master/z3-tested"


let parse_z3_version_lines : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun out -> (match ((FStar_Util.splitlines out)) with
| (x)::uu____48 -> begin
(

let trimmed = (FStar_Util.trim_string x)
in (

let parts = (FStar_Util.split trimmed " ")
in (

let rec aux = (fun uu___41_64 -> (match (uu___41_64) with
| (hash)::[] -> begin
(

let n1 = (Prims.min (FStar_String.strlen _z3hash_expected) (FStar_String.strlen hash))
in (

let hash_prefix = (FStar_String.substring hash (Prims.parse_int "0") n1)
in (match ((Prims.op_Equality hash_prefix _z3hash_expected)) with
| true -> begin
((

let uu____75 = (FStar_Options.debug_any ())
in (match (uu____75) with
| true -> begin
(

let msg = (FStar_Util.format1 "Successfully found expected Z3 commit hash %s\n" hash)
in (FStar_Util.print_string msg))
end
| uu____77 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| uu____78 -> begin
(

let msg = (FStar_Util.format2 "Expected Z3 commit hash \"%s\", got \"%s\"" _z3hash_expected trimmed)
in FStar_Pervasives_Native.Some (msg))
end)))
end
| (uu____80)::q -> begin
(aux q)
end
| uu____84 -> begin
FStar_Pervasives_Native.Some ("No Z3 commit hash found")
end))
in (aux parts))))
end
| uu____87 -> begin
FStar_Pervasives_Native.Some ("No Z3 version string found")
end))


let z3hash_warning_message : unit  ->  (FStar_Errors.raw_error * Prims.string) FStar_Pervasives_Native.option = (fun uu____100 -> (

let run_proc_result = (FStar_All.try_with (fun uu___47_108 -> (match (()) with
| () -> begin
(

let uu____111 = (

let uu____112 = (FStar_Options.z3_exe ())
in (FStar_Util.run_process "z3_version" uu____112 (("-version")::[]) FStar_Pervasives_Native.None))
in FStar_Pervasives_Native.Some (uu____111))
end)) (fun uu___46_115 -> (match (uu___46_115) with
| uu____118 -> begin
FStar_Pervasives_Native.None
end)))
in (match (run_proc_result) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((FStar_Errors.Error_Z3InvocationError), ("Could not run Z3")))
end
| FStar_Pervasives_Native.Some (out) -> begin
(

let uu____130 = (parse_z3_version_lines out)
in (match (uu____130) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (msg) -> begin
FStar_Pervasives_Native.Some (((FStar_Errors.Warning_Z3InvocationWarning), (msg)))
end))
end)))


let check_z3hash : unit  ->  unit = (fun uu____152 -> (

let uu____153 = (

let uu____154 = (FStar_ST.op_Bang _z3hash_checked)
in (not (uu____154)))
in (match (uu____153) with
| true -> begin
((FStar_ST.op_Colon_Equals _z3hash_checked true);
(

let uu____214 = (z3hash_warning_message ())
in (match (uu____214) with
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
| uu____232 -> begin
()
end)))


let ini_params : unit  ->  Prims.string Prims.list = (fun uu____239 -> ((check_z3hash ());
(

let uu____241 = (

let uu____244 = (

let uu____247 = (

let uu____250 = (

let uu____253 = (

let uu____256 = (

let uu____259 = (

let uu____262 = (

let uu____263 = (

let uu____264 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int uu____264))
in (FStar_Util.format1 "smt.random_seed=%s" uu____263))
in (uu____262)::[])
in ("smt.case_split=3")::uu____259)
in ("smt.relevancy=2")::uu____256)
in ("model=true")::uu____253)
in ("auto_config=false")::uu____250)
in ("-in")::uu____247)
in ("-smt2")::uu____244)
in (

let uu____265 = (FStar_Options.z3_cliopt ())
in (FStar_List.append uu____241 uu____265)));
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
| uu____316 -> begin
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
| uu____336 -> begin
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
| uu____374 -> begin
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
| uu____412 -> begin
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
| uu____443 -> begin
false
end))


type z3statistics =
Prims.string FStar_Util.smap


let status_tag : z3status  ->  Prims.string = (fun uu___42_450 -> (match (uu___42_450) with
| SAT (uu____451) -> begin
"sat"
end
| UNSAT (uu____458) -> begin
"unsat"
end
| UNKNOWN (uu____459) -> begin
"unknown"
end
| TIMEOUT (uu____466) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let status_string_and_errors : z3status  ->  (Prims.string * FStar_SMTEncoding_Term.error_labels) = (fun s -> (match (s) with
| KILLED -> begin
(((status_tag s)), ([]))
end
| UNSAT (uu____488) -> begin
(((status_tag s)), ([]))
end
| SAT (errs, msg) -> begin
(

let uu____497 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____497), (errs)))
end
| UNKNOWN (errs, msg) -> begin
(

let uu____505 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____505), (errs)))
end
| TIMEOUT (errs, msg) -> begin
(

let uu____513 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____513), (errs)))
end))


let tid : unit  ->  Prims.string = (fun uu____519 -> (

let uu____520 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right uu____520 FStar_Util.string_of_int)))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id1 -> (

let uu____526 = (FStar_Options.z3_exe ())
in (

let uu____527 = (ini_params ())
in (FStar_Util.start_process id1 uu____526 uu____527 (fun s -> (Prims.op_Equality s "Done!"))))))

type bgproc =
{ask : Prims.string  ->  Prims.string; refresh : unit  ->  unit; restart : unit  ->  unit}


let __proj__Mkbgproc__item__ask : bgproc  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {ask = __fname__ask; refresh = __fname__refresh; restart = __fname__restart} -> begin
__fname__ask
end))


let __proj__Mkbgproc__item__refresh : bgproc  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {ask = __fname__ask; refresh = __fname__refresh; restart = __fname__restart} -> begin
__fname__refresh
end))


let __proj__Mkbgproc__item__restart : bgproc  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {ask = __fname__ask; refresh = __fname__refresh; restart = __fname__restart} -> begin
__fname__restart
end))

type query_log =
{get_module_name : unit  ->  Prims.string; set_module_name : Prims.string  ->  unit; write_to_log : Prims.string  ->  unit; close_log : unit  ->  unit; log_file_name : unit  ->  Prims.string}


let __proj__Mkquery_log__item__get_module_name : query_log  ->  unit  ->  Prims.string = (fun projectee -> (match (projectee) with
| {get_module_name = __fname__get_module_name; set_module_name = __fname__set_module_name; write_to_log = __fname__write_to_log; close_log = __fname__close_log; log_file_name = __fname__log_file_name} -> begin
__fname__get_module_name
end))


let __proj__Mkquery_log__item__set_module_name : query_log  ->  Prims.string  ->  unit = (fun projectee -> (match (projectee) with
| {get_module_name = __fname__get_module_name; set_module_name = __fname__set_module_name; write_to_log = __fname__write_to_log; close_log = __fname__close_log; log_file_name = __fname__log_file_name} -> begin
__fname__set_module_name
end))


let __proj__Mkquery_log__item__write_to_log : query_log  ->  Prims.string  ->  unit = (fun projectee -> (match (projectee) with
| {get_module_name = __fname__get_module_name; set_module_name = __fname__set_module_name; write_to_log = __fname__write_to_log; close_log = __fname__close_log; log_file_name = __fname__log_file_name} -> begin
__fname__write_to_log
end))


let __proj__Mkquery_log__item__close_log : query_log  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {get_module_name = __fname__get_module_name; set_module_name = __fname__set_module_name; write_to_log = __fname__write_to_log; close_log = __fname__close_log; log_file_name = __fname__log_file_name} -> begin
__fname__close_log
end))


let __proj__Mkquery_log__item__log_file_name : query_log  ->  unit  ->  Prims.string = (fun projectee -> (match (projectee) with
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

let get_module_name = (fun uu____1001 -> (

let uu____1002 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1002) with
| FStar_Pervasives_Native.None -> begin
(failwith "Module name not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in (

let new_log_file = (fun uu____1114 -> (

let uu____1115 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1115) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let file_name = (

let uu____1223 = (

let uu____1230 = (FStar_ST.op_Bang used_file_names)
in (FStar_List.tryFind (fun uu____1355 -> (match (uu____1355) with
| (m, uu____1361) -> begin
(Prims.op_Equality n1 m)
end)) uu____1230))
in (match (uu____1223) with
| FStar_Pervasives_Native.None -> begin
((

let uu____1367 = (

let uu____1374 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((Prims.parse_int "0"))))::uu____1374)
in (FStar_ST.op_Colon_Equals used_file_names uu____1367));
n1;
)
end
| FStar_Pervasives_Native.Some (uu____1607, k) -> begin
((

let uu____1614 = (

let uu____1621 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((k + (Prims.parse_int "1")))))::uu____1621)
in (FStar_ST.op_Colon_Equals used_file_names uu____1614));
(

let uu____1854 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n1 uu____1854));
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

let get_log_file = (fun uu____2070 -> (

let uu____2071 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____2071) with
| FStar_Pervasives_Native.None -> begin
(new_log_file ())
end
| FStar_Pervasives_Native.Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____2184 = (get_log_file ())
in (FStar_Util.append_to_file uu____2184 str)))
in (

let write_to_new_log = (fun str -> (

let dir_name = (

let uu____2192 = (FStar_ST.op_Bang current_file_name)
in (match (uu____2192) with
| FStar_Pervasives_Native.None -> begin
(

let dir_name = (

let uu____2299 = (FStar_ST.op_Bang current_module_name)
in (match (uu____2299) with
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

let uu____2613 = (

let uu____2614 = (FStar_ST.op_Bang query_number)
in (uu____2614 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals query_number uu____2613));
(

let file_name = (

let uu____2814 = (FStar_Util.string_of_int qnum)
in (FStar_Util.format1 "query-%s.smt2" uu____2814))
in (

let file_name1 = (FStar_Util.concat_dir_filename dir_name file_name)
in (FStar_Util.write_file file_name1 str)));
))))
in (

let write_to_log = (fun str -> (

let uu____2822 = (

let uu____2823 = (FStar_Options.n_cores ())
in (uu____2823 > (Prims.parse_int "1")))
in (match (uu____2822) with
| true -> begin
(write_to_new_log str)
end
| uu____2824 -> begin
(append_to_log str)
end)))
in (

let close_log = (fun uu____2830 -> (

let uu____2831 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____2831) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (fh) -> begin
((FStar_Util.close_file fh);
(FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None);
)
end)))
in (

let log_file_name = (fun uu____3047 -> (

let uu____3048 = (FStar_ST.op_Bang current_file_name)
in (match (uu____3048) with
| FStar_Pervasives_Native.None -> begin
(failwith "no log file")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in {get_module_name = get_module_name; set_module_name = set_module_name; write_to_log = write_to_log; close_log = close_log; log_file_name = log_file_name}))))))))))))))


let bg_z3_proc : bgproc FStar_ST.ref = (

let the_z3proc = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let new_proc = (

let ctr = (FStar_Util.mk_ref (~- ((Prims.parse_int "1"))))
in (fun uu____3207 -> (

let uu____3208 = (

let uu____3209 = ((FStar_Util.incr ctr);
(

let uu____3316 = (FStar_ST.op_Bang ctr)
in (FStar_All.pipe_right uu____3316 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____3209))
in (new_z3proc uu____3208))))
in (

let z3proc = (fun uu____3421 -> ((

let uu____3423 = (

let uu____3424 = (FStar_ST.op_Bang the_z3proc)
in (Prims.op_Equality uu____3424 FStar_Pervasives_Native.None))
in (match (uu____3423) with
| true -> begin
(

let uu____3532 = (

let uu____3535 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____3535))
in (FStar_ST.op_Colon_Equals the_z3proc uu____3532))
end
| uu____3639 -> begin
()
end));
(

let uu____3640 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.must uu____3640));
))
in (

let x = []
in (

let ask = (fun input -> (

let kill_handler = (fun uu____3760 -> "\nkilled\n")
in (

let uu____3761 = (z3proc ())
in (FStar_Util.ask_process uu____3761 input kill_handler))))
in (

let refresh = (fun uu____3767 -> ((

let uu____3769 = (z3proc ())
in (FStar_Util.kill_process uu____3769));
(

let uu____3771 = (

let uu____3774 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____3774))
in (FStar_ST.op_Colon_Equals the_z3proc uu____3771));
(query_logging.close_log ());
))
in (

let restart = (fun uu____3883 -> ((query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(

let uu____3989 = (

let uu____3992 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____3992))
in (FStar_ST.op_Colon_Equals the_z3proc uu____3989));
))
in (FStar_Util.mk_ref {ask = (FStar_Util.with_monitor x ask); refresh = (FStar_Util.with_monitor x refresh); restart = (FStar_Util.with_monitor x restart)}))))))))


let set_bg_z3_proc : bgproc  ->  unit = (fun bgp -> (FStar_ST.op_Colon_Equals bg_z3_proc bgp))


let at_log_file : unit  ->  Prims.string = (fun uu____4140 -> (

let uu____4141 = (FStar_Options.log_queries ())
in (match (uu____4141) with
| true -> begin
(

let uu____4142 = (query_logging.log_file_name ())
in (Prims.strcat "@" uu____4142))
end
| uu____4143 -> begin
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


let smt_output_sections : FStar_Range.range  ->  Prims.string Prims.list  ->  smt_output = (fun r lines -> (

let rec until = (fun tag lines1 -> (match (lines1) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (l)::lines2 -> begin
(match ((Prims.op_Equality tag l)) with
| true -> begin
FStar_Pervasives_Native.Some ((([]), (lines2)))
end
| uu____4368 -> begin
(

let uu____4369 = (until tag lines2)
in (FStar_Util.map_opt uu____4369 (fun uu____4399 -> (match (uu____4399) with
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

let uu____4477 = (until (start_tag tag) lines1)
in (match (uu____4477) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (lines1))
end
| FStar_Pervasives_Native.Some (prefix1, suffix) -> begin
(

let uu____4532 = (until (end_tag tag) suffix)
in (match (uu____4532) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Parse error: " (Prims.strcat (end_tag tag) " not found")))
end
| FStar_Pervasives_Native.Some (section, suffix1) -> begin
((FStar_Pervasives_Native.Some (section)), ((FStar_List.append prefix1 suffix1)))
end))
end)))
in (

let uu____4597 = (find_section "result" lines)
in (match (uu____4597) with
| (result_opt, lines1) -> begin
(

let result = (FStar_Util.must result_opt)
in (

let uu____4627 = (find_section "reason-unknown" lines1)
in (match (uu____4627) with
| (reason_unknown, lines2) -> begin
(

let uu____4652 = (find_section "unsat-core" lines2)
in (match (uu____4652) with
| (unsat_core, lines3) -> begin
(

let uu____4677 = (find_section "statistics" lines3)
in (match (uu____4677) with
| (statistics, lines4) -> begin
(

let uu____4702 = (find_section "labels" lines4)
in (match (uu____4702) with
| (labels, lines5) -> begin
(

let remaining = (

let uu____4730 = (until "Done!" lines5)
in (match (uu____4730) with
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
| uu____4770 -> begin
(

let uu____4773 = (

let uu____4778 = (FStar_Util.format1 "Unexpected output from Z3: %s\n" (FStar_String.concat "\n" remaining))
in ((FStar_Errors.Warning_UnexpectedZ3Output), (uu____4778)))
in (FStar_Errors.log_issue r uu____4773))
end);
(

let uu____4779 = (FStar_Util.must result_opt)
in {smt_result = uu____4779; smt_reason_unknown = reason_unknown; smt_unsat_core = unsat_core; smt_statistics = statistics; smt_labels = labels});
))
end))
end))
end))
end)))
end)))))))


let doZ3Exe : FStar_Range.range  ->  Prims.bool  ->  Prims.string  ->  FStar_SMTEncoding_Term.error_labels  ->  (z3status * z3statistics) = (fun r fresh input label_messages -> (

let parse = (fun z3out -> (

let lines = (FStar_All.pipe_right (FStar_String.split ((10)::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (

let smt_output = (smt_output_sections r lines)
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
| uu____4851 -> begin
(

let uu____4852 = (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_Util.sort_with FStar_String.compare))
in FStar_Pervasives_Native.Some (uu____4852))
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

let uu____4915 = (lblnegs rest)
in (lname)::uu____4915)
end
| (lname)::(uu____4919)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest)
end
| uu____4923 -> begin
[]
end))
in (

let lblnegs1 = (lblnegs lines1)
in (FStar_All.pipe_right lblnegs1 (FStar_List.collect (fun l -> (

let uu____4956 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____4995 -> (match (uu____4995) with
| (m, uu____5007, uu____5008) -> begin
(Prims.op_Equality (FStar_Pervasives_Native.fst m) l)
end))))
in (match (uu____4956) with
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
| uu____5113 -> begin
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
| uu____5121 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| uu____5122 -> begin
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
| uu____5137 -> begin
ru
end))))
in (

let status = ((

let uu____5140 = (FStar_Options.debug_any ())
in (match (uu____5140) with
| true -> begin
(

let uu____5141 = (FStar_Util.format1 "Z3 says: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (FStar_All.pipe_left FStar_Util.print_string uu____5141))
end
| uu____5142 -> begin
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

let uu____5186 = (

let uu____5191 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5191.restart)
in (uu____5186 ()));
KILLED;
)
end
| uu____5221 -> begin
(

let uu____5222 = (FStar_Util.format1 "Unexpected output from Z3: got output result: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (failwith uu____5222))
end);
)
in ((status), (statistics))))))))))
in (

let stdout1 = (match (fresh) with
| true -> begin
(

let uu____5224 = (tid ())
in (

let uu____5225 = (FStar_Options.z3_exe ())
in (

let uu____5226 = (ini_params ())
in (FStar_Util.run_process uu____5224 uu____5225 uu____5226 (FStar_Pervasives_Native.Some (input))))))
end
| uu____5229 -> begin
(

let uu____5230 = (

let uu____5235 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5235.ask)
in (uu____5230 input))
end)
in (parse (FStar_Util.trim_string stdout1)))))


let z3_options : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n")


let set_z3_options : Prims.string  ->  unit = (fun opts -> (FStar_ST.op_Colon_Equals z3_options opts))

type 'a job =
{job : unit  ->  'a; callback : 'a  ->  unit}


let __proj__Mkjob__item__job : 'a . 'a job  ->  unit  ->  'a = (fun projectee -> (match (projectee) with
| {job = __fname__job; callback = __fname__callback} -> begin
__fname__job
end))


let __proj__Mkjob__item__callback : 'a . 'a job  ->  'a  ->  unit = (fun projectee -> (match (projectee) with
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


let z3_job : FStar_Range.range  ->  Prims.bool  ->  FStar_SMTEncoding_Term.error_labels  ->  Prims.string  ->  Prims.string FStar_Pervasives_Native.option  ->  unit  ->  z3result = (fun r fresh label_messages input qhash uu____5593 -> (

let start = (FStar_Util.now ())
in (

let uu____5597 = (FStar_All.try_with (fun uu___49_5607 -> (match (()) with
| () -> begin
(doZ3Exe r fresh input label_messages)
end)) (fun uu___48_5615 -> (match (uu___48_5615) with
| e when (

let uu____5621 = (FStar_Options.trace_error ())
in (not (uu____5621))) -> begin
((

let uu____5623 = (

let uu____5628 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5628.refresh)
in (uu____5623 ()));
(FStar_Exn.raise e);
)
end)))
in (match (uu____5597) with
| (status, statistics) -> begin
(

let uu____5664 = (

let uu____5669 = (FStar_Util.now ())
in (FStar_Util.time_diff start uu____5669))
in (match (uu____5664) with
| (uu____5670, elapsed_time) -> begin
{z3result_status = status; z3result_time = elapsed_time; z3result_statistics = statistics; z3result_query_hash = qhash}
end))
end))))


let running : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let rec dequeue' : unit  ->  unit = (fun uu____5721 -> (

let j = (

let uu____5723 = (FStar_ST.op_Bang job_queue)
in (match (uu____5723) with
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
(FStar_Util.with_monitor job_queue (fun uu____5810 -> (FStar_Util.decr pending_jobs)) ());
(dequeue ());
)))
and dequeue : unit  ->  unit = (fun uu____5812 -> (

let uu____5813 = (FStar_ST.op_Bang running)
in if uu____5813 then begin
(

let rec aux = (fun uu____5848 -> ((FStar_Util.monitor_enter job_queue);
(

let uu____5854 = (FStar_ST.op_Bang job_queue)
in (match (uu____5854) with
| [] -> begin
((FStar_Util.monitor_exit job_queue);
(FStar_Util.sleep (Prims.parse_int "50"));
(aux ());
)
end
| uu____5896 -> begin
(dequeue' ())
end));
))
in (aux ()))
end else begin
()
end))
and run_job : z3job  ->  unit = (fun j -> (

let uu____5900 = (j.job ())
in (FStar_All.pipe_left j.callback uu____5900)))


let init : unit  ->  unit = (fun uu____5905 -> ((FStar_ST.op_Colon_Equals running true);
(

let n_cores1 = (FStar_Options.n_cores ())
in (match ((n_cores1 > (Prims.parse_int "1"))) with
| true -> begin
(

let rec aux = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____5943 -> begin
((FStar_Util.spawn dequeue);
(aux (n1 - (Prims.parse_int "1")));
)
end))
in (aux n_cores1))
end
| uu____5945 -> begin
()
end));
))


let enqueue : z3job  ->  unit = (fun j -> (FStar_Util.with_monitor job_queue (fun uu____5957 -> ((

let uu____5959 = (

let uu____5962 = (FStar_ST.op_Bang job_queue)
in (FStar_List.append uu____5962 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue uu____5959));
(FStar_Util.monitor_pulse job_queue);
)) ()))


let finish : unit  ->  unit = (fun uu____6039 -> (

let rec aux = (fun uu____6045 -> (

let uu____6046 = (FStar_Util.with_monitor job_queue (fun uu____6062 -> (

let uu____6063 = (FStar_ST.op_Bang pending_jobs)
in (

let uu____6093 = (

let uu____6094 = (FStar_ST.op_Bang job_queue)
in (FStar_List.length uu____6094))
in ((uu____6063), (uu____6093))))) ())
in (match (uu____6046) with
| (n1, m) -> begin
(match ((Prims.op_Equality (n1 + m) (Prims.parse_int "0"))) with
| true -> begin
(FStar_ST.op_Colon_Equals running false)
end
| uu____6169 -> begin
((FStar_Util.sleep (Prims.parse_int "500"));
(aux ());
)
end)
end)))
in (aux ())))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let mk_fresh_scope : unit  ->  scope_t = (fun uu____6228 -> (FStar_ST.op_Bang fresh_scope))


let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : Prims.string  ->  unit = (fun msg -> ((

let uu____6313 = (

let uu____6318 = (FStar_ST.op_Bang fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::uu____6318)
in (FStar_ST.op_Colon_Equals fresh_scope uu____6313));
(

let uu____6399 = (

let uu____6402 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____6402 ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____6399));
))


let pop : Prims.string  ->  unit = (fun msg -> ((

let uu____6477 = (

let uu____6482 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.tl uu____6482))
in (FStar_ST.op_Colon_Equals fresh_scope uu____6477));
(

let uu____6563 = (

let uu____6566 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____6566 ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____6563));
))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___43_6648 -> (match (uu___43_6648) with
| FStar_SMTEncoding_Term.Push -> begin
(failwith "Unexpected push/pop")
end
| FStar_SMTEncoding_Term.Pop -> begin
(failwith "Unexpected push/pop")
end
| uu____6649 -> begin
()
end))));
(

let uu____6651 = (FStar_ST.op_Bang fresh_scope)
in (match (uu____6651) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd1 decls))::tl1))
end
| uu____6742 -> begin
(failwith "Impossible")
end));
(

let uu____6747 = (

let uu____6750 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____6750 decls))
in (FStar_ST.op_Colon_Equals bg_scope uu____6747));
))


let refresh : unit  ->  unit = (fun uu____6823 -> ((

let uu____6825 = (

let uu____6826 = (FStar_Options.n_cores ())
in (uu____6826 < (Prims.parse_int "2")))
in (match (uu____6825) with
| true -> begin
(

let uu____6827 = (

let uu____6832 = (FStar_ST.op_Bang bg_z3_proc)
in uu____6832.refresh)
in (uu____6827 ()))
end
| uu____6862 -> begin
()
end));
(

let uu____6863 = (

let uu____6866 = (

let uu____6871 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____6871))
in (FStar_List.flatten uu____6866))
in (FStar_ST.op_Colon_Equals bg_scope uu____6863));
))


let mk_input : FStar_SMTEncoding_Term.decl Prims.list  ->  (Prims.string * Prims.string FStar_Pervasives_Native.option) = (fun theory -> (

let options = (FStar_ST.op_Bang z3_options)
in (

let uu____6993 = (

let uu____7000 = ((FStar_Options.record_hints ()) || ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())))
in (match (uu____7000) with
| true -> begin
(

let uu____7007 = (

let uu____7018 = (FStar_All.pipe_right theory (FStar_Util.prefix_until (fun uu___44_7046 -> (match (uu___44_7046) with
| FStar_SMTEncoding_Term.CheckSat -> begin
true
end
| uu____7047 -> begin
false
end))))
in (FStar_All.pipe_right uu____7018 FStar_Option.get))
in (match (uu____7007) with
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

let uncaption = (fun uu___45_7131 -> (match (uu___45_7131) with
| FStar_SMTEncoding_Term.Caption (uu____7132) -> begin
FStar_SMTEncoding_Term.Caption ("")
end
| FStar_SMTEncoding_Term.Assume (a) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___50_7136 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___50_7136.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.None; FStar_SMTEncoding_Term.assumption_name = uu___50_7136.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = uu___50_7136.FStar_SMTEncoding_Term.assumption_fact_ids}))
end
| FStar_SMTEncoding_Term.DeclFun (n1, a, s, uu____7140) -> begin
FStar_SMTEncoding_Term.DeclFun (((n1), (a), (s), (FStar_Pervasives_Native.None)))
end
| FStar_SMTEncoding_Term.DefineFun (n1, a, s, b, uu____7153) -> begin
FStar_SMTEncoding_Term.DefineFun (((n1), (a), (s), (b), (FStar_Pervasives_Native.None)))
end
| d -> begin
d
end))
in (

let hs = (

let uu____7164 = (

let uu____7167 = (

let uu____7170 = (FStar_All.pipe_right prefix1 (FStar_List.map uncaption))
in (FStar_All.pipe_right uu____7170 pp_no_cap))
in (FStar_All.pipe_right uu____7167 (FStar_List.filter (fun s -> (Prims.op_disEquality s "")))))
in (FStar_All.pipe_right uu____7164 (FStar_String.concat "\n")))
in (

let uu____7189 = (

let uu____7192 = (FStar_Util.digest_of_string hs)
in FStar_Pervasives_Native.Some (uu____7192))
in (((Prims.strcat ps (Prims.strcat "\n" ss))), (uu____7189))))))))))))
end))
end
| uu____7195 -> begin
(

let uu____7196 = (

let uu____7197 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory)
in (FStar_All.pipe_right uu____7197 (FStar_String.concat "\n")))
in ((uu____7196), (FStar_Pervasives_Native.None)))
end))
in (match (uu____6993) with
| (r, hash) -> begin
((

let uu____7217 = (FStar_Options.log_queries ())
in (match (uu____7217) with
| true -> begin
(query_logging.write_to_log r)
end
| uu____7218 -> begin
()
end));
((r), (hash));
)
end))))


type cb =
z3result  ->  unit


let cache_hit : Prims.string FStar_Pervasives_Native.option  ->  Prims.string FStar_Pervasives_Native.option  ->  cb  ->  Prims.bool = (fun cache qhash cb -> (

let uu____7251 = ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()))
in (match (uu____7251) with
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
| uu____7262 -> begin
false
end)
end
| uu____7265 -> begin
false
end)))


let ask_1_core : FStar_Range.range  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  cb  ->  unit = (fun r filter_theory cache label_messages qry cb -> (

let theory = (

let uu____7320 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____7320 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
in (

let uu____7356 = (filter_theory theory)
in (match (uu____7356) with
| (theory1, used_unsat_core) -> begin
(

let uu____7363 = (mk_input theory1)
in (match (uu____7363) with
| (input, qhash) -> begin
((FStar_ST.op_Colon_Equals bg_scope []);
(

let uu____7410 = (

let uu____7411 = (cache_hit cache qhash cb)
in (not (uu____7411)))
in (match (uu____7410) with
| true -> begin
(run_job {job = (z3_job r false label_messages input qhash); callback = cb})
end
| uu____7416 -> begin
()
end));
)
end))
end))))


let ask_n_cores : FStar_Range.range  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  unit = (fun r filter_theory cache label_messages qry scope cb -> (

let theory = (

let uu____7480 = (match (scope) with
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_List.rev s)
end
| FStar_Pervasives_Native.None -> begin
((FStar_ST.op_Colon_Equals bg_scope []);
(

let uu____7526 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____7526));
)
end)
in (FStar_List.flatten uu____7480))
in (

let theory1 = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let uu____7573 = (filter_theory theory1)
in (match (uu____7573) with
| (theory2, used_unsat_core) -> begin
(

let uu____7580 = (mk_input theory2)
in (match (uu____7580) with
| (input, qhash) -> begin
(

let uu____7593 = (

let uu____7594 = (cache_hit cache qhash cb)
in (not (uu____7594)))
in (match (uu____7593) with
| true -> begin
(enqueue {job = (z3_job r true label_messages input qhash); callback = cb})
end
| uu____7599 -> begin
()
end))
end))
end)))))


let ask : FStar_Range.range  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  unit = (fun r filter1 cache label_messages qry scope cb -> (

let uu____7662 = (

let uu____7663 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____7663 (Prims.parse_int "1")))
in (match (uu____7662) with
| true -> begin
(ask_1_core r filter1 cache label_messages qry cb)
end
| uu____7666 -> begin
(ask_n_cores r filter1 cache label_messages qry scope cb)
end)))




