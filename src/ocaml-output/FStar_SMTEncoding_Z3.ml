
open Prims
open FStar_Pervasives

let _z3hash_checked : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let _z3hash_expected : Prims.string = "1f29cebd4df6"


let _z3url : Prims.string = "https://github.com/FStarLang/binaries/tree/master/z3-tested"


let parse_z3_version_lines : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun out -> (match ((FStar_Util.splitlines out)) with
| (x)::uu____19 -> begin
(

let trimmed = (FStar_Util.trim_string x)
in (

let parts = (FStar_Util.split trimmed " ")
in (

let rec aux = (fun uu___124_33 -> (match (uu___124_33) with
| (hash)::[] -> begin
(

let n1 = (Prims.min (FStar_String.strlen _z3hash_expected) (FStar_String.strlen hash))
in (

let hash_prefix = (FStar_String.substring hash (Prims.parse_int "0") n1)
in (match ((Prims.op_Equality hash_prefix _z3hash_expected)) with
| true -> begin
((

let uu____44 = (FStar_Options.debug_any ())
in (match (uu____44) with
| true -> begin
(

let msg = (FStar_Util.format1 "Successfully found expected Z3 commit hash %s" hash)
in (FStar_Util.print_string msg))
end
| uu____46 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| uu____47 -> begin
(

let msg = (FStar_Util.format2 "Expected Z3 commit hash \"%s\", got \"%s\"" _z3hash_expected trimmed)
in FStar_Pervasives_Native.Some (msg))
end)))
end
| (uu____49)::q -> begin
(aux q)
end
| uu____53 -> begin
FStar_Pervasives_Native.Some ("No Z3 commit hash found")
end))
in (aux parts))))
end
| uu____56 -> begin
FStar_Pervasives_Native.Some ("No Z3 version string found")
end))


let z3hash_warning_message : Prims.unit  ->  (FStar_Errors.issue_level * Prims.string) FStar_Pervasives_Native.option = (fun uu____68 -> (

let run_proc_result = (FStar_All.try_with (fun uu___130_88 -> (match (()) with
| () -> begin
(

let uu____97 = (

let uu____104 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc uu____104 "-version" ""))
in FStar_Pervasives_Native.Some (uu____97))
end)) (fun uu___129_113 -> (match (uu___129_113) with
| uu____122 -> begin
FStar_Pervasives_Native.None
end)))
in (match (run_proc_result) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((FStar_Errors.EError), ("Could not run Z3")))
end
| FStar_Pervasives_Native.Some (uu____145, out, uu____147) -> begin
(

let uu____154 = (parse_z3_version_lines out)
in (match (uu____154) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (msg) -> begin
FStar_Pervasives_Native.Some (((FStar_Errors.EWarning), (msg)))
end))
end)))


let check_z3hash : Prims.unit  ->  Prims.unit = (fun uu____175 -> (

let uu____176 = (

let uu____177 = (FStar_ST.op_Bang _z3hash_checked)
in (not (uu____177)))
in (match (uu____176) with
| true -> begin
((FStar_ST.op_Colon_Equals _z3hash_checked true);
(

let uu____271 = (z3hash_warning_message ())
in (match (uu____271) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (level, msg) -> begin
(

let msg1 = (FStar_Util.format4 "%s\n%s\n%s\n%s\n" msg "Please download the version of Z3 corresponding to your platform from:" _z3url "and add the bin/ subdirectory into your PATH")
in (FStar_Errors.add_one (FStar_Errors.mk_issue level FStar_Pervasives_Native.None msg1)))
end));
)
end
| uu____289 -> begin
()
end)))


let ini_params : Prims.unit  ->  Prims.string = (fun uu____293 -> ((check_z3hash ());
(

let uu____295 = (

let uu____298 = (

let uu____301 = (

let uu____304 = (

let uu____305 = (

let uu____306 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int uu____306))
in (FStar_Util.format1 "smt.random_seed=%s" uu____305))
in (uu____304)::[])
in ("-smt2 -in auto_config=false model=true smt.relevancy=2")::uu____301)
in (

let uu____307 = (FStar_Options.z3_cliopt ())
in (FStar_List.append uu____298 uu____307)))
in (FStar_String.concat " " uu____295));
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
| uu____353 -> begin
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
| uu____373 -> begin
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
| uu____411 -> begin
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
| uu____449 -> begin
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
| uu____480 -> begin
false
end))


type z3statistics =
Prims.string FStar_Util.smap


let status_tag : z3status  ->  Prims.string = (fun uu___125_486 -> (match (uu___125_486) with
| SAT (uu____487) -> begin
"sat"
end
| UNSAT (uu____494) -> begin
"unsat"
end
| UNKNOWN (uu____495) -> begin
"unknown"
end
| TIMEOUT (uu____502) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let status_string_and_errors : z3status  ->  (Prims.string * FStar_SMTEncoding_Term.error_labels) = (fun s -> (match (s) with
| KILLED -> begin
(((status_tag s)), ([]))
end
| UNSAT (uu____523) -> begin
(((status_tag s)), ([]))
end
| SAT (errs, msg) -> begin
(

let uu____532 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____532), (errs)))
end
| UNKNOWN (errs, msg) -> begin
(

let uu____540 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____540), (errs)))
end
| TIMEOUT (errs, msg) -> begin
(

let uu____548 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____548), (errs)))
end))


let tid : Prims.unit  ->  Prims.string = (fun uu____553 -> (

let uu____554 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right uu____554 FStar_Util.string_of_int)))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = (Prims.op_Equality (FStar_Util.trim_string s) "Done!")
in x))
in (

let uu____567 = (FStar_Options.z3_exe ())
in (

let uu____568 = (ini_params ())
in (FStar_Util.start_process false id uu____567 uu____568 cond)))))

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

let get_module_name = (fun uu____959 -> (

let uu____960 = (FStar_ST.op_Bang current_module_name)
in (match (uu____960) with
| FStar_Pervasives_Native.None -> begin
(failwith "Module name not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in (

let new_log_file = (fun uu____1031 -> (

let uu____1032 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1032) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let file_name = (

let uu____1101 = (

let uu____1108 = (FStar_ST.op_Bang used_file_names)
in (FStar_List.tryFind (fun uu____1194 -> (match (uu____1194) with
| (m, uu____1200) -> begin
(Prims.op_Equality n1 m)
end)) uu____1108))
in (match (uu____1101) with
| FStar_Pervasives_Native.None -> begin
((

let uu____1206 = (

let uu____1213 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((Prims.parse_int "0"))))::uu____1213)
in (FStar_ST.op_Colon_Equals used_file_names uu____1206));
n1;
)
end
| FStar_Pervasives_Native.Some (uu____1368, k) -> begin
((

let uu____1375 = (

let uu____1382 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((k + (Prims.parse_int "1")))))::uu____1382)
in (FStar_ST.op_Colon_Equals used_file_names uu____1375));
(

let uu____1537 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n1 uu____1537));
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

let get_log_file = (fun uu____1673 -> (

let uu____1674 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____1674) with
| FStar_Pervasives_Native.None -> begin
(new_log_file ())
end
| FStar_Pervasives_Native.Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____1746 = (get_log_file ())
in (FStar_Util.append_to_file uu____1746 str)))
in (

let write_to_new_log = (fun str -> (

let dir_name = (

let uu____1752 = (FStar_ST.op_Bang current_file_name)
in (match (uu____1752) with
| FStar_Pervasives_Native.None -> begin
(

let dir_name = (

let uu____1820 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1820) with
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

let uu____2017 = (

let uu____2018 = (FStar_ST.op_Bang query_number)
in (uu____2018 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals query_number uu____2017));
(

let file_name = (

let uu____2140 = (FStar_Util.string_of_int qnum)
in (FStar_Util.format1 "query-%s.smt2" uu____2140))
in (

let file_name1 = (FStar_Util.concat_dir_filename dir_name file_name)
in (FStar_Util.write_file file_name1 str)));
))))
in (

let write_to_log = (fun str -> (

let uu____2146 = (

let uu____2147 = (FStar_Options.n_cores ())
in (uu____2147 > (Prims.parse_int "1")))
in (match (uu____2146) with
| true -> begin
(write_to_new_log str)
end
| uu____2148 -> begin
(append_to_log str)
end)))
in (

let close_log = (fun uu____2152 -> (

let uu____2153 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____2153) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (fh) -> begin
((FStar_Util.close_file fh);
(FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None);
)
end)))
in (

let log_file_name = (fun uu____2289 -> (

let uu____2290 = (FStar_ST.op_Bang current_file_name)
in (match (uu____2290) with
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
in (fun uu____2371 -> (

let uu____2372 = (

let uu____2373 = ((FStar_Util.incr ctr);
(

let uu____2396 = (FStar_ST.op_Bang ctr)
in (FStar_All.pipe_right uu____2396 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____2373))
in (new_z3proc uu____2372))))
in (

let z3proc = (fun uu____2460 -> ((

let uu____2462 = (

let uu____2463 = (FStar_ST.op_Bang the_z3proc)
in (Prims.op_Equality uu____2463 FStar_Pervasives_Native.None))
in (match (uu____2462) with
| true -> begin
(

let uu____2532 = (

let uu____2535 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____2535))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2532))
end
| uu____2600 -> begin
()
end));
(

let uu____2601 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.must uu____2601));
))
in (

let x = []
in (

let grab = (fun uu____2674 -> ((FStar_Util.monitor_enter x);
(z3proc ());
))
in (

let release = (fun uu____2681 -> (FStar_Util.monitor_exit x))
in (

let refresh = (fun uu____2687 -> (

let proc = (grab ())
in ((FStar_Util.kill_process proc);
(

let uu____2691 = (

let uu____2694 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____2694))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2691));
(query_logging.close_log ());
(release ());
)))
in (

let restart = (fun uu____2763 -> ((FStar_Util.monitor_enter ());
(query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(

let uu____2832 = (

let uu____2835 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____2835))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2832));
(FStar_Util.monitor_exit ());
))
in {grab = grab; release = release; refresh = refresh; restart = restart}))))))))


let at_log_file : Prims.unit  ->  Prims.string = (fun uu____2903 -> (

let uu____2904 = (FStar_Options.log_queries ())
in (match (uu____2904) with
| true -> begin
(

let uu____2905 = (query_logging.log_file_name ())
in (Prims.strcat "@" uu____2905))
end
| uu____2906 -> begin
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
| uu____3111 -> begin
(

let uu____3112 = (until tag lines2)
in (FStar_Util.map_opt uu____3112 (fun uu____3142 -> (match (uu____3142) with
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

let uu____3212 = (until (start_tag tag) lines1)
in (match (uu____3212) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (lines1))
end
| FStar_Pervasives_Native.Some (prefix1, suffix) -> begin
(

let uu____3267 = (until (end_tag tag) suffix)
in (match (uu____3267) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Parse error: " (Prims.strcat (end_tag tag) " not found")))
end
| FStar_Pervasives_Native.Some (section, suffix1) -> begin
((FStar_Pervasives_Native.Some (section)), ((FStar_List.append prefix1 suffix1)))
end))
end)))
in (

let uu____3332 = (find_section "result" lines)
in (match (uu____3332) with
| (result_opt, lines1) -> begin
(

let result = (FStar_Util.must result_opt)
in (

let uu____3362 = (find_section "reason-unknown" lines1)
in (match (uu____3362) with
| (reason_unknown, lines2) -> begin
(

let uu____3387 = (find_section "unsat-core" lines2)
in (match (uu____3387) with
| (unsat_core, lines3) -> begin
(

let uu____3412 = (find_section "statistics" lines3)
in (match (uu____3412) with
| (statistics, lines4) -> begin
(

let uu____3437 = (find_section "labels" lines4)
in (match (uu____3437) with
| (labels, lines5) -> begin
(

let remaining = (

let uu____3465 = (until "Done!" lines5)
in (match (uu____3465) with
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
| uu____3505 -> begin
(

let uu____3508 = (

let uu____3509 = (query_logging.get_module_name ())
in (FStar_Util.format2 "%s: Unexpected output from Z3: %s\n" uu____3509 (FStar_String.concat "\n" remaining)))
in (FStar_Errors.warn FStar_Range.dummyRange uu____3508))
end);
(

let uu____3510 = (FStar_Util.must result_opt)
in {smt_result = uu____3510; smt_reason_unknown = reason_unknown; smt_unsat_core = unsat_core; smt_statistics = statistics; smt_labels = labels});
))
end))
end))
end))
end)))
end)))))))


let doZ3Exe : Prims.bool  ->  Prims.string  ->  FStar_SMTEncoding_Term.error_labels  ->  (z3status * z3statistics) = (fun fresh1 input label_messages -> (

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
| uu____3569 -> begin
(

let uu____3570 = (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_Util.sort_with FStar_String.compare))
in FStar_Pervasives_Native.Some (uu____3570))
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

let uu____3631 = (lblnegs rest)
in (lname)::uu____3631)
end
| (lname)::(uu____3635)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest)
end
| uu____3639 -> begin
[]
end))
in (

let lblnegs1 = (lblnegs lines1)
in (FStar_All.pipe_right lblnegs1 (FStar_List.collect (fun l -> (

let uu____3672 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____3711 -> (match (uu____3711) with
| (m, uu____3723, uu____3724) -> begin
(Prims.op_Equality (FStar_Pervasives_Native.fst m) l)
end))))
in (match (uu____3672) with
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
| uu____3827 -> begin
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
| uu____3835 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| uu____3836 -> begin
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
| uu____3851 -> begin
ru
end))))
in (

let status = ((

let uu____3854 = (FStar_Options.debug_any ())
in (match (uu____3854) with
| true -> begin
(

let uu____3855 = (FStar_Util.format1 "Z3 says: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (FStar_All.pipe_left FStar_Util.print_string uu____3855))
end
| uu____3856 -> begin
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
| uu____3900 -> begin
(

let uu____3901 = (FStar_Util.format1 "Unexpected output from Z3: got output result: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (failwith uu____3901))
end);
)
in ((status), (statistics))))))))))
in (

let cond = (fun pid s -> (

let x = (Prims.op_Equality (FStar_Util.trim_string s) "Done!")
in x))
in (

let stdout1 = (match (fresh1) with
| true -> begin
(

let uu____3911 = (tid ())
in (

let uu____3912 = (FStar_Options.z3_exe ())
in (

let uu____3913 = (ini_params ())
in (FStar_Util.launch_process false uu____3911 uu____3912 uu____3913 input cond))))
end
| uu____3914 -> begin
(

let proc = (bg_z3_proc.grab ())
in (

let stdout1 = (FStar_Util.ask_process proc input)
in ((bg_z3_proc.release ());
stdout1;
)))
end)
in (parse (FStar_Util.trim_string stdout1))))))


let z3_options : Prims.unit  ->  Prims.string = (fun uu____3921 -> "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n")

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


let with_monitor : 'Auu____4080 'Auu____4081 . 'Auu____4081  ->  (Prims.unit  ->  'Auu____4080)  ->  'Auu____4080 = (fun m f -> ((FStar_Util.monitor_enter m);
(

let res = (f ())
in ((FStar_Util.monitor_exit m);
res;
));
))


let z3_job : Prims.bool  ->  FStar_SMTEncoding_Term.error_labels  ->  Prims.string  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.unit  ->  z3result = (fun fresh1 label_messages input qhash uu____4119 -> (

let start = (FStar_Util.now ())
in (

let uu____4123 = (FStar_All.try_with (fun uu___132_4133 -> (match (()) with
| () -> begin
(doZ3Exe fresh1 input label_messages)
end)) (fun uu___131_4142 -> (match (uu___131_4142) with
| uu____4147 when (

let uu____4148 = (FStar_Options.trace_error ())
in (not (uu____4148))) -> begin
((bg_z3_proc.refresh ());
(

let uu____4150 = (FStar_Util.smap_create (Prims.parse_int "0"))
in ((UNKNOWN ((([]), (FStar_Pervasives_Native.Some ("Z3 raised an exception"))))), (uu____4150)));
)
end)))
in (match (uu____4123) with
| (status, statistics) -> begin
(

let uu____4161 = (

let uu____4166 = (FStar_Util.now ())
in (FStar_Util.time_diff start uu____4166))
in (match (uu____4161) with
| (uu____4167, elapsed_time) -> begin
{z3result_status = status; z3result_time = elapsed_time; z3result_statistics = statistics; z3result_query_hash = qhash}
end))
end))))


let running : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun uu____4184 -> (

let j = (

let uu____4186 = (FStar_ST.op_Bang job_queue)
in (match (uu____4186) with
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
(with_monitor job_queue (fun uu____4307 -> (FStar_Util.decr pending_jobs)));
(dequeue ());
)))
and dequeue : Prims.unit  ->  Prims.unit = (fun uu____4309 -> (

let uu____4310 = (FStar_ST.op_Bang running)
in if uu____4310 then begin
(

let rec aux = (fun uu____4360 -> ((FStar_Util.monitor_enter job_queue);
(

let uu____4366 = (FStar_ST.op_Bang job_queue)
in (match (uu____4366) with
| [] -> begin
((FStar_Util.monitor_exit job_queue);
(FStar_Util.sleep (Prims.parse_int "50"));
(aux ());
)
end
| uu____4425 -> begin
(dequeue' ())
end));
))
in (aux ()))
end else begin
()
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (

let uu____4429 = (j.job ())
in (FStar_All.pipe_left j.callback uu____4429)))


let init : Prims.unit  ->  Prims.unit = (fun uu____4433 -> ((FStar_ST.op_Colon_Equals running true);
(

let n_cores1 = (FStar_Options.n_cores ())
in (match ((n_cores1 > (Prims.parse_int "1"))) with
| true -> begin
(

let rec aux = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____4486 -> begin
((FStar_Util.spawn dequeue);
(aux (n1 - (Prims.parse_int "1")));
)
end))
in (aux n_cores1))
end
| uu____4488 -> begin
()
end));
))


let enqueue : z3job  ->  Prims.unit = (fun j -> ((FStar_Util.monitor_enter job_queue);
(

let uu____4499 = (

let uu____4502 = (FStar_ST.op_Bang job_queue)
in (FStar_List.append uu____4502 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue uu____4499));
(FStar_Util.monitor_pulse job_queue);
(FStar_Util.monitor_exit job_queue);
))


let finish : Prims.unit  ->  Prims.unit = (fun uu____4617 -> (

let rec aux = (fun uu____4621 -> (

let uu____4622 = (with_monitor job_queue (fun uu____4638 -> (

let uu____4639 = (FStar_ST.op_Bang pending_jobs)
in (

let uu____4686 = (

let uu____4687 = (FStar_ST.op_Bang job_queue)
in (FStar_List.length uu____4687))
in ((uu____4639), (uu____4686))))))
in (match (uu____4622) with
| (n1, m) -> begin
(match ((Prims.op_Equality (n1 + m) (Prims.parse_int "0"))) with
| true -> begin
(FStar_ST.op_Colon_Equals running false)
end
| uu____4796 -> begin
((FStar_Util.sleep (Prims.parse_int "500"));
(aux ());
)
end)
end)))
in (aux ())))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let mk_fresh_scope : Prims.unit  ->  scope_t = (fun uu____4826 -> (FStar_ST.op_Bang fresh_scope))


let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : Prims.string  ->  Prims.unit = (fun msg -> ((

let uu____4899 = (

let uu____4904 = (FStar_ST.op_Bang fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::uu____4904)
in (FStar_ST.op_Colon_Equals fresh_scope uu____4899));
(

let uu____5019 = (

let uu____5022 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____5022 ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____5019));
))


let pop : Prims.string  ->  Prims.unit = (fun msg -> ((

let uu____5130 = (

let uu____5135 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.tl uu____5135))
in (FStar_ST.op_Colon_Equals fresh_scope uu____5130));
(

let uu____5250 = (

let uu____5253 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____5253 ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____5250));
))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___126_5368 -> (match (uu___126_5368) with
| FStar_SMTEncoding_Term.Push -> begin
(failwith "Unexpected push/pop")
end
| FStar_SMTEncoding_Term.Pop -> begin
(failwith "Unexpected push/pop")
end
| uu____5369 -> begin
()
end))));
(

let uu____5371 = (FStar_ST.op_Bang fresh_scope)
in (match (uu____5371) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd1 decls))::tl1))
end
| uu____5496 -> begin
(failwith "Impossible")
end));
(

let uu____5501 = (

let uu____5504 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____5504 decls))
in (FStar_ST.op_Colon_Equals bg_scope uu____5501));
))


let refresh : Prims.unit  ->  Prims.unit = (fun uu____5610 -> ((

let uu____5612 = (

let uu____5613 = (FStar_Options.n_cores ())
in (uu____5613 < (Prims.parse_int "2")))
in (match (uu____5612) with
| true -> begin
(bg_z3_proc.refresh ())
end
| uu____5614 -> begin
()
end));
(

let uu____5615 = (

let uu____5618 = (

let uu____5623 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____5623))
in (FStar_List.flatten uu____5618))
in (FStar_ST.op_Colon_Equals bg_scope uu____5615));
))


let mk_input : FStar_SMTEncoding_Term.decl Prims.list  ->  (Prims.string * Prims.string FStar_Pervasives_Native.option) = (fun theory -> (

let options = (z3_options ())
in (

let uu____5749 = (

let uu____5756 = ((FStar_Options.record_hints ()) || ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())))
in (match (uu____5756) with
| true -> begin
(

let uu____5763 = (

let uu____5774 = (FStar_All.pipe_right theory (FStar_Util.prefix_until (fun uu___127_5802 -> (match (uu___127_5802) with
| FStar_SMTEncoding_Term.CheckSat -> begin
true
end
| uu____5803 -> begin
false
end))))
in (FStar_All.pipe_right uu____5774 FStar_Option.get))
in (match (uu____5763) with
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

let uncaption = (fun uu___128_5881 -> (match (uu___128_5881) with
| FStar_SMTEncoding_Term.Caption (uu____5882) -> begin
FStar_SMTEncoding_Term.Caption ("")
end
| FStar_SMTEncoding_Term.Assume (a) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___133_5886 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___133_5886.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.None; FStar_SMTEncoding_Term.assumption_name = uu___133_5886.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = uu___133_5886.FStar_SMTEncoding_Term.assumption_fact_ids}))
end
| FStar_SMTEncoding_Term.DeclFun (n1, a, s, uu____5890) -> begin
FStar_SMTEncoding_Term.DeclFun (((n1), (a), (s), (FStar_Pervasives_Native.None)))
end
| FStar_SMTEncoding_Term.DefineFun (n1, a, s, b, uu____5903) -> begin
FStar_SMTEncoding_Term.DefineFun (((n1), (a), (s), (b), (FStar_Pervasives_Native.None)))
end
| d -> begin
d
end))
in (

let hs = (

let uu____5914 = (

let uu____5917 = (

let uu____5920 = (FStar_All.pipe_right prefix1 (FStar_List.map uncaption))
in (FStar_All.pipe_right uu____5920 pp_no_cap))
in (FStar_All.pipe_right uu____5917 (FStar_List.filter (fun s -> (Prims.op_disEquality s "")))))
in (FStar_All.pipe_right uu____5914 (FStar_String.concat "\n")))
in (

let uu____5939 = (

let uu____5942 = (FStar_Util.digest_of_string hs)
in FStar_Pervasives_Native.Some (uu____5942))
in (((Prims.strcat ps (Prims.strcat "\n" ss))), (uu____5939))))))))))))
end))
end
| uu____5945 -> begin
(

let uu____5946 = (

let uu____5947 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory)
in (FStar_All.pipe_right uu____5947 (FStar_String.concat "\n")))
in ((uu____5946), (FStar_Pervasives_Native.None)))
end))
in (match (uu____5749) with
| (r, hash) -> begin
((

let uu____5967 = (FStar_Options.log_queries ())
in (match (uu____5967) with
| true -> begin
(query_logging.write_to_log r)
end
| uu____5968 -> begin
()
end));
((r), (hash));
)
end))))


type cb =
z3result  ->  Prims.unit


let cache_hit : (Prims.string FStar_Pervasives_Native.option * unsat_core)  ->  Prims.string FStar_Pervasives_Native.option  ->  cb  ->  Prims.bool = (fun cache qhash cb -> (

let uu____6003 = ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()))
in (match (uu____6003) with
| true -> begin
(match (qhash) with
| FStar_Pervasives_Native.Some (x) when (Prims.op_Equality qhash (FStar_Pervasives_Native.fst cache)) -> begin
(

let stats = (FStar_Util.smap_create (Prims.parse_int "0"))
in ((FStar_Util.smap_add stats "fstar_cache_hit" "1");
(

let result = {z3result_status = UNSAT ((FStar_Pervasives_Native.snd cache)); z3result_time = (Prims.parse_int "0"); z3result_statistics = stats; z3result_query_hash = qhash}
in ((cb result);
true;
));
))
end
| uu____6016 -> begin
false
end)
end
| uu____6019 -> begin
false
end)))


let ask_1_core : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  (Prims.string FStar_Pervasives_Native.option * unsat_core)  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  cb  ->  Prims.unit = (fun filter_theory cache label_messages qry cb -> (

let theory = (

let uu____6070 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____6070 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
in (

let uu____6123 = (filter_theory theory)
in (match (uu____6123) with
| (theory1, used_unsat_core) -> begin
(

let uu____6130 = (mk_input theory1)
in (match (uu____6130) with
| (input, qhash) -> begin
((FStar_ST.op_Colon_Equals bg_scope []);
(

let uu____6194 = (

let uu____6195 = (cache_hit cache qhash cb)
in (not (uu____6195)))
in (match (uu____6194) with
| true -> begin
(run_job {job = (z3_job false label_messages input qhash); callback = cb})
end
| uu____6200 -> begin
()
end));
)
end))
end))))


let ask_n_cores : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  (Prims.string FStar_Pervasives_Native.option * unsat_core)  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  Prims.unit = (fun filter_theory cache label_messages qry scope cb -> (

let theory = (

let uu____6259 = (match (scope) with
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_List.rev s)
end
| FStar_Pervasives_Native.None -> begin
((FStar_ST.op_Colon_Equals bg_scope []);
(

let uu____6322 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____6322));
)
end)
in (FStar_List.flatten uu____6259))
in (

let theory1 = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let uu____6386 = (filter_theory theory1)
in (match (uu____6386) with
| (theory2, used_unsat_core) -> begin
(

let uu____6393 = (mk_input theory2)
in (match (uu____6393) with
| (input, qhash) -> begin
(

let uu____6406 = (

let uu____6407 = (cache_hit cache qhash cb)
in (not (uu____6407)))
in (match (uu____6406) with
| true -> begin
(enqueue {job = (z3_job true label_messages input qhash); callback = cb})
end
| uu____6412 -> begin
()
end))
end))
end)))))


let ask : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  (Prims.string FStar_Pervasives_Native.option * unsat_core)  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  Prims.unit = (fun filter1 cache label_messages qry scope cb -> (

let uu____6470 = (

let uu____6471 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____6471 (Prims.parse_int "1")))
in (match (uu____6470) with
| true -> begin
(ask_1_core filter1 cache label_messages qry cb)
end
| uu____6474 -> begin
(ask_n_cores filter1 cache label_messages qry scope cb)
end)))




