
open Prims
open FStar_Pervasives

let _z3hash_checked : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let _z3hash_expected : Prims.string = "1f29cebd4df6"


let _z3url : Prims.string = "https://github.com/FStarLang/binaries/tree/master/z3-tested"


let parse_z3_version_lines : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun out -> (match ((FStar_Util.splitlines out)) with
| (x)::uu____24 -> begin
(

let trimmed = (FStar_Util.trim_string x)
in (

let parts = (FStar_Util.split trimmed " ")
in (

let rec aux = (fun uu___38_40 -> (match (uu___38_40) with
| (hash)::[] -> begin
(

let n1 = (Prims.min (FStar_String.strlen _z3hash_expected) (FStar_String.strlen hash))
in (

let hash_prefix = (FStar_String.substring hash (Prims.parse_int "0") n1)
in (match ((Prims.op_Equality hash_prefix _z3hash_expected)) with
| true -> begin
((

let uu____51 = (FStar_Options.debug_any ())
in (match (uu____51) with
| true -> begin
(

let msg = (FStar_Util.format1 "Successfully found expected Z3 commit hash %s\n" hash)
in (FStar_Util.print_string msg))
end
| uu____53 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| uu____54 -> begin
(

let msg = (FStar_Util.format2 "Expected Z3 commit hash \"%s\", got \"%s\"" _z3hash_expected trimmed)
in FStar_Pervasives_Native.Some (msg))
end)))
end
| (uu____56)::q -> begin
(aux q)
end
| uu____60 -> begin
FStar_Pervasives_Native.Some ("No Z3 commit hash found")
end))
in (aux parts))))
end
| uu____63 -> begin
FStar_Pervasives_Native.Some ("No Z3 version string found")
end))


let z3hash_warning_message : unit  ->  (FStar_Errors.raw_error * Prims.string) FStar_Pervasives_Native.option = (fun uu____76 -> (

let run_proc_result = (FStar_All.try_with (fun uu___44_96 -> (match (()) with
| () -> begin
(

let uu____105 = (

let uu____112 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc uu____112 "-version" ""))
in FStar_Pervasives_Native.Some (uu____105))
end)) (fun uu___43_121 -> (match (uu___43_121) with
| uu____130 -> begin
FStar_Pervasives_Native.None
end)))
in (match (run_proc_result) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((FStar_Errors.Error_Z3InvocationError), ("Could not run Z3")))
end
| FStar_Pervasives_Native.Some (uu____153, out, uu____155) -> begin
(

let uu____162 = (parse_z3_version_lines out)
in (match (uu____162) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (msg) -> begin
FStar_Pervasives_Native.Some (((FStar_Errors.Warning_Z3InvocationWarning), (msg)))
end))
end)))


let check_z3hash : unit  ->  unit = (fun uu____184 -> (

let uu____185 = (

let uu____186 = (FStar_ST.op_Bang _z3hash_checked)
in (not (uu____186)))
in (match (uu____185) with
| true -> begin
((FStar_ST.op_Colon_Equals _z3hash_checked true);
(

let uu____234 = (z3hash_warning_message ())
in (match (uu____234) with
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
| uu____252 -> begin
()
end)))


let ini_params : unit  ->  Prims.string = (fun uu____257 -> ((check_z3hash ());
(

let uu____259 = (

let uu____262 = (

let uu____265 = (

let uu____268 = (

let uu____269 = (

let uu____270 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int uu____270))
in (FStar_Util.format1 "smt.random_seed=%s" uu____269))
in (uu____268)::[])
in ("-smt2 -in auto_config=false model=true smt.relevancy=2 smt.case_split=3")::uu____265)
in (

let uu____271 = (FStar_Options.z3_cliopt ())
in (FStar_List.append uu____262 uu____271)))
in (FStar_String.concat " " uu____259));
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
| uu____322 -> begin
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
| uu____342 -> begin
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
| uu____418 -> begin
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
| uu____449 -> begin
false
end))


type z3statistics =
Prims.string FStar_Util.smap


let status_tag : z3status  ->  Prims.string = (fun uu___39_456 -> (match (uu___39_456) with
| SAT (uu____457) -> begin
"sat"
end
| UNSAT (uu____464) -> begin
"unsat"
end
| UNKNOWN (uu____465) -> begin
"unknown"
end
| TIMEOUT (uu____472) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let status_string_and_errors : z3status  ->  (Prims.string * FStar_SMTEncoding_Term.error_labels) = (fun s -> (match (s) with
| KILLED -> begin
(((status_tag s)), ([]))
end
| UNSAT (uu____492) -> begin
(((status_tag s)), ([]))
end
| SAT (errs, msg) -> begin
(

let uu____499 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____499), (errs)))
end
| UNKNOWN (errs, msg) -> begin
(

let uu____507 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____507), (errs)))
end
| TIMEOUT (errs, msg) -> begin
(

let uu____515 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____515), (errs)))
end))


let tid : unit  ->  Prims.string = (fun uu____521 -> (

let uu____522 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right uu____522 FStar_Util.string_of_int)))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id1 -> (

let cond = (fun pid s -> (

let x = (Prims.op_Equality (FStar_Util.trim_string s) "Done!")
in x))
in (

let uu____540 = (FStar_Options.z3_exe ())
in (

let uu____541 = (ini_params ())
in (FStar_Util.start_process false id1 uu____540 uu____541 cond)))))

type bgproc =
{grab : unit  ->  FStar_Util.proc; release : unit  ->  unit; refresh : unit  ->  unit; restart : unit  ->  unit}


let __proj__Mkbgproc__item__grab : bgproc  ->  unit  ->  FStar_Util.proc = (fun projectee -> (match (projectee) with
| {grab = __fname__grab; release = __fname__release; refresh = __fname__refresh; restart = __fname__restart} -> begin
__fname__grab
end))


let __proj__Mkbgproc__item__release : bgproc  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {grab = __fname__grab; release = __fname__release; refresh = __fname__refresh; restart = __fname__restart} -> begin
__fname__release
end))


let __proj__Mkbgproc__item__refresh : bgproc  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {grab = __fname__grab; release = __fname__release; refresh = __fname__refresh; restart = __fname__restart} -> begin
__fname__refresh
end))


let __proj__Mkbgproc__item__restart : bgproc  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {grab = __fname__grab; release = __fname__release; refresh = __fname__refresh; restart = __fname__restart} -> begin
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

let get_module_name = (fun uu____1007 -> (

let uu____1008 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1008) with
| FStar_Pervasives_Native.None -> begin
(failwith "Module name not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in (

let new_log_file = (fun uu____1066 -> (

let uu____1067 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1067) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let file_name = (

let uu____1121 = (

let uu____1128 = (FStar_ST.op_Bang used_file_names)
in (FStar_List.tryFind (fun uu____1199 -> (match (uu____1199) with
| (m, uu____1205) -> begin
(Prims.op_Equality n1 m)
end)) uu____1128))
in (match (uu____1121) with
| FStar_Pervasives_Native.None -> begin
((

let uu____1211 = (

let uu____1218 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((Prims.parse_int "0"))))::uu____1218)
in (FStar_ST.op_Colon_Equals used_file_names uu____1211));
n1;
)
end
| FStar_Pervasives_Native.Some (uu____1343, k) -> begin
((

let uu____1350 = (

let uu____1357 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((k + (Prims.parse_int "1")))))::uu____1357)
in (FStar_ST.op_Colon_Equals used_file_names uu____1350));
(

let uu____1482 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n1 uu____1482));
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

let get_log_file = (fun uu____1590 -> (

let uu____1591 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____1591) with
| FStar_Pervasives_Native.None -> begin
(new_log_file ())
end
| FStar_Pervasives_Native.Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____1650 = (get_log_file ())
in (FStar_Util.append_to_file uu____1650 str)))
in (

let write_to_new_log = (fun str -> (

let dir_name = (

let uu____1658 = (FStar_ST.op_Bang current_file_name)
in (match (uu____1658) with
| FStar_Pervasives_Native.None -> begin
(

let dir_name = (

let uu____1711 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1711) with
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

let uu____1863 = (

let uu____1864 = (FStar_ST.op_Bang query_number)
in (uu____1864 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals query_number uu____1863));
(

let file_name = (

let uu____1956 = (FStar_Util.string_of_int qnum)
in (FStar_Util.format1 "query-%s.smt2" uu____1956))
in (

let file_name1 = (FStar_Util.concat_dir_filename dir_name file_name)
in (FStar_Util.write_file file_name1 str)));
))))
in (

let write_to_log = (fun str -> (

let uu____1964 = (

let uu____1965 = (FStar_Options.n_cores ())
in (uu____1965 > (Prims.parse_int "1")))
in (match (uu____1964) with
| true -> begin
(write_to_new_log str)
end
| uu____1966 -> begin
(append_to_log str)
end)))
in (

let close_log = (fun uu____1972 -> (

let uu____1973 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____1973) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (fh) -> begin
((FStar_Util.close_file fh);
(FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None);
)
end)))
in (

let log_file_name = (fun uu____2081 -> (

let uu____2082 = (FStar_ST.op_Bang current_file_name)
in (match (uu____2082) with
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
in (fun uu____2150 -> (

let uu____2151 = (

let uu____2152 = ((FStar_Util.incr ctr);
(

let uu____2187 = (FStar_ST.op_Bang ctr)
in (FStar_All.pipe_right uu____2187 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____2152))
in (new_z3proc uu____2151))))
in (

let z3proc = (fun uu____2238 -> ((

let uu____2240 = (

let uu____2241 = (FStar_ST.op_Bang the_z3proc)
in (Prims.op_Equality uu____2241 FStar_Pervasives_Native.None))
in (match (uu____2240) with
| true -> begin
(

let uu____2295 = (

let uu____2298 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____2298))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2295))
end
| uu____2348 -> begin
()
end));
(

let uu____2349 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.must uu____2349));
))
in (

let x = []
in (

let grab = (fun uu____2409 -> ((FStar_Util.monitor_enter x);
(z3proc ());
))
in (

let release = (fun uu____2418 -> (FStar_Util.monitor_exit x))
in (

let refresh = (fun uu____2426 -> (

let proc = (grab ())
in ((FStar_Util.kill_process proc);
(

let uu____2430 = (

let uu____2433 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____2433))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2430));
(query_logging.close_log ());
(release ());
)))
in (

let restart = (fun uu____2489 -> ((FStar_Util.monitor_enter ());
(query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(

let uu____2543 = (

let uu____2546 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____2546))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2543));
(FStar_Util.monitor_exit ());
))
in {grab = grab; release = release; refresh = refresh; restart = restart}))))))))


let at_log_file : unit  ->  Prims.string = (fun uu____2600 -> (

let uu____2601 = (FStar_Options.log_queries ())
in (match (uu____2601) with
| true -> begin
(

let uu____2602 = (query_logging.log_file_name ())
in (Prims.strcat "@" uu____2602))
end
| uu____2603 -> begin
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
| uu____2823 -> begin
(

let uu____2824 = (until tag lines2)
in (FStar_Util.map_opt uu____2824 (fun uu____2854 -> (match (uu____2854) with
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

let uu____2932 = (until (start_tag tag) lines1)
in (match (uu____2932) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (lines1))
end
| FStar_Pervasives_Native.Some (prefix1, suffix) -> begin
(

let uu____2987 = (until (end_tag tag) suffix)
in (match (uu____2987) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Parse error: " (Prims.strcat (end_tag tag) " not found")))
end
| FStar_Pervasives_Native.Some (section, suffix1) -> begin
((FStar_Pervasives_Native.Some (section)), ((FStar_List.append prefix1 suffix1)))
end))
end)))
in (

let uu____3052 = (find_section "result" lines)
in (match (uu____3052) with
| (result_opt, lines1) -> begin
(

let result = (FStar_Util.must result_opt)
in (

let uu____3082 = (find_section "reason-unknown" lines1)
in (match (uu____3082) with
| (reason_unknown, lines2) -> begin
(

let uu____3107 = (find_section "unsat-core" lines2)
in (match (uu____3107) with
| (unsat_core, lines3) -> begin
(

let uu____3132 = (find_section "statistics" lines3)
in (match (uu____3132) with
| (statistics, lines4) -> begin
(

let uu____3157 = (find_section "labels" lines4)
in (match (uu____3157) with
| (labels, lines5) -> begin
(

let remaining = (

let uu____3185 = (until "Done!" lines5)
in (match (uu____3185) with
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
| uu____3225 -> begin
(

let uu____3228 = (

let uu____3233 = (

let uu____3234 = (query_logging.get_module_name ())
in (FStar_Util.format2 "%s: Unexpected output from Z3: %s\n" uu____3234 (FStar_String.concat "\n" remaining)))
in ((FStar_Errors.Warning_UnexpectedZ3Output), (uu____3233)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____3228))
end);
(

let uu____3235 = (FStar_Util.must result_opt)
in {smt_result = uu____3235; smt_reason_unknown = reason_unknown; smt_unsat_core = unsat_core; smt_statistics = statistics; smt_labels = labels});
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
| uu____3302 -> begin
(

let uu____3303 = (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_Util.sort_with FStar_String.compare))
in FStar_Pervasives_Native.Some (uu____3303))
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

let uu____3366 = (lblnegs rest)
in (lname)::uu____3366)
end
| (lname)::(uu____3370)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest)
end
| uu____3374 -> begin
[]
end))
in (

let lblnegs1 = (lblnegs lines1)
in (FStar_All.pipe_right lblnegs1 (FStar_List.collect (fun l -> (

let uu____3407 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____3458 -> (match (uu____3458) with
| (m, uu____3470, uu____3471) -> begin
(Prims.op_Equality (FStar_Pervasives_Native.fst m) l)
end))))
in (match (uu____3407) with
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
| uu____3576 -> begin
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
| uu____3584 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| uu____3585 -> begin
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
| uu____3600 -> begin
ru
end))))
in (

let status = ((

let uu____3603 = (FStar_Options.debug_any ())
in (match (uu____3603) with
| true -> begin
(

let uu____3604 = (FStar_Util.format1 "Z3 says: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (FStar_All.pipe_left FStar_Util.print_string uu____3604))
end
| uu____3605 -> begin
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
| uu____3613 -> begin
(

let uu____3614 = (FStar_Util.format1 "Unexpected output from Z3: got output result: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (failwith uu____3614))
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

let uu____3628 = (tid ())
in (

let uu____3629 = (FStar_Options.z3_exe ())
in (

let uu____3630 = (ini_params ())
in (FStar_Util.launch_process false uu____3628 uu____3629 uu____3630 input cond))))
end
| uu____3631 -> begin
(

let proc = (bg_z3_proc.grab ())
in (

let stdout1 = (FStar_Util.ask_process proc input)
in ((bg_z3_proc.release ());
stdout1;
)))
end)
in (parse (FStar_Util.trim_string stdout1))))))


let z3_options : unit  ->  Prims.string = (fun uu____3639 -> "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n")

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


let with_monitor : 'Auu____3826 'Auu____3827 . 'Auu____3826  ->  (unit  ->  'Auu____3827)  ->  'Auu____3827 = (fun m f -> ((FStar_Util.monitor_enter m);
(

let res = (f ())
in ((FStar_Util.monitor_exit m);
res;
));
))


let z3_job : Prims.bool  ->  FStar_SMTEncoding_Term.error_labels  ->  Prims.string  ->  Prims.string FStar_Pervasives_Native.option  ->  unit  ->  z3result = (fun fresh label_messages input qhash uu____3872 -> (

let start = (FStar_Util.now ())
in (

let uu____3876 = (FStar_All.try_with (fun uu___46_3886 -> (match (()) with
| () -> begin
(doZ3Exe fresh input label_messages)
end)) (fun uu___45_3895 -> (match (uu___45_3895) with
| uu____3900 when (

let uu____3901 = (FStar_Options.trace_error ())
in (not (uu____3901))) -> begin
((bg_z3_proc.refresh ());
(

let uu____3903 = (FStar_Util.smap_create (Prims.parse_int "0"))
in ((UNKNOWN ((([]), (FStar_Pervasives_Native.Some ("Z3 raised an exception"))))), (uu____3903)));
)
end)))
in (match (uu____3876) with
| (status, statistics) -> begin
(

let uu____3908 = (

let uu____3913 = (FStar_Util.now ())
in (FStar_Util.time_diff start uu____3913))
in (match (uu____3908) with
| (uu____3914, elapsed_time) -> begin
{z3result_status = status; z3result_time = elapsed_time; z3result_statistics = statistics; z3result_query_hash = qhash}
end))
end))))


let running : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let rec dequeue' : unit  ->  unit = (fun uu____3941 -> (

let j = (

let uu____3943 = (FStar_ST.op_Bang job_queue)
in (match (uu____3943) with
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
(with_monitor job_queue (fun uu____4018 -> (FStar_Util.decr pending_jobs)));
(dequeue ());
)))
and dequeue : unit  ->  unit = (fun uu____4020 -> (

let uu____4021 = (FStar_ST.op_Bang running)
in if uu____4021 then begin
(

let rec aux = (fun uu____4050 -> ((FStar_Util.monitor_enter job_queue);
(

let uu____4056 = (FStar_ST.op_Bang job_queue)
in (match (uu____4056) with
| [] -> begin
((FStar_Util.monitor_exit job_queue);
(FStar_Util.sleep (Prims.parse_int "50"));
(aux ());
)
end
| uu____4092 -> begin
(dequeue' ())
end));
))
in (aux ()))
end else begin
()
end))
and run_job : z3job  ->  unit = (fun j -> (

let uu____4096 = (j.job ())
in (FStar_All.pipe_left j.callback uu____4096)))


let init : unit  ->  unit = (fun uu____4101 -> ((FStar_ST.op_Colon_Equals running true);
(

let n_cores1 = (FStar_Options.n_cores ())
in (match ((n_cores1 > (Prims.parse_int "1"))) with
| true -> begin
(

let rec aux = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____4133 -> begin
((FStar_Util.spawn dequeue);
(aux (n1 - (Prims.parse_int "1")));
)
end))
in (aux n_cores1))
end
| uu____4135 -> begin
()
end));
))


let enqueue : z3job  ->  unit = (fun j -> ((FStar_Util.monitor_enter job_queue);
(

let uu____4147 = (

let uu____4150 = (FStar_ST.op_Bang job_queue)
in (FStar_List.append uu____4150 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue uu____4147));
(FStar_Util.monitor_pulse job_queue);
(FStar_Util.monitor_exit job_queue);
))


let finish : unit  ->  unit = (fun uu____4220 -> (

let rec aux = (fun uu____4226 -> (

let uu____4227 = (with_monitor job_queue (fun uu____4243 -> (

let uu____4244 = (FStar_ST.op_Bang pending_jobs)
in (

let uu____4268 = (

let uu____4269 = (FStar_ST.op_Bang job_queue)
in (FStar_List.length uu____4269))
in ((uu____4244), (uu____4268))))))
in (match (uu____4227) with
| (n1, m) -> begin
(match ((Prims.op_Equality (n1 + m) (Prims.parse_int "0"))) with
| true -> begin
(FStar_ST.op_Colon_Equals running false)
end
| uu____4332 -> begin
((FStar_Util.sleep (Prims.parse_int "500"));
(aux ());
)
end)
end)))
in (aux ())))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let fresh_scope : scope_t FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let mk_fresh_scope : unit  ->  scope_t = (fun uu____4359 -> (FStar_ST.op_Bang fresh_scope))


let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : Prims.string  ->  unit = (fun msg -> ((

let uu____4406 = (

let uu____4407 = (FStar_ST.op_Bang fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::uu____4407)
in (FStar_ST.op_Colon_Equals fresh_scope uu____4406));
(

let uu____4460 = (

let uu____4463 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____4463 ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____4460));
))


let pop : Prims.string  ->  unit = (fun msg -> ((

let uu____4526 = (

let uu____4527 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.tl uu____4527))
in (FStar_ST.op_Colon_Equals fresh_scope uu____4526));
(

let uu____4580 = (

let uu____4583 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____4583 ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____4580));
))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___40_4653 -> (match (uu___40_4653) with
| FStar_SMTEncoding_Term.Push -> begin
(failwith "Unexpected push/pop")
end
| FStar_SMTEncoding_Term.Pop -> begin
(failwith "Unexpected push/pop")
end
| uu____4654 -> begin
()
end))));
(

let uu____4656 = (FStar_ST.op_Bang fresh_scope)
in (match (uu____4656) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd1 decls))::tl1))
end
| uu____4715 -> begin
(failwith "Impossible")
end));
(

let uu____4716 = (

let uu____4719 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____4719 decls))
in (FStar_ST.op_Colon_Equals bg_scope uu____4716));
))


let refresh : unit  ->  unit = (fun uu____4780 -> ((

let uu____4782 = (

let uu____4783 = (FStar_Options.n_cores ())
in (uu____4783 < (Prims.parse_int "2")))
in (match (uu____4782) with
| true -> begin
(bg_z3_proc.refresh ())
end
| uu____4784 -> begin
()
end));
(

let uu____4785 = (

let uu____4788 = (

let uu____4793 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____4793))
in (FStar_List.flatten uu____4788))
in (FStar_ST.op_Colon_Equals bg_scope uu____4785));
))


let mk_input : FStar_SMTEncoding_Term.decl Prims.list  ->  (Prims.string * Prims.string FStar_Pervasives_Native.option) = (fun theory -> (

let options = (z3_options ())
in (

let uu____4866 = (

let uu____4873 = ((FStar_Options.record_hints ()) || ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())))
in (match (uu____4873) with
| true -> begin
(

let uu____4880 = (

let uu____4891 = (FStar_All.pipe_right theory (FStar_Util.prefix_until (fun uu___41_4919 -> (match (uu___41_4919) with
| FStar_SMTEncoding_Term.CheckSat -> begin
true
end
| uu____4920 -> begin
false
end))))
in (FStar_All.pipe_right uu____4891 FStar_Option.get))
in (match (uu____4880) with
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

let uncaption = (fun uu___42_5004 -> (match (uu___42_5004) with
| FStar_SMTEncoding_Term.Caption (uu____5005) -> begin
FStar_SMTEncoding_Term.Caption ("")
end
| FStar_SMTEncoding_Term.Assume (a) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___47_5009 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___47_5009.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.None; FStar_SMTEncoding_Term.assumption_name = uu___47_5009.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = uu___47_5009.FStar_SMTEncoding_Term.assumption_fact_ids}))
end
| FStar_SMTEncoding_Term.DeclFun (n1, a, s, uu____5013) -> begin
FStar_SMTEncoding_Term.DeclFun (((n1), (a), (s), (FStar_Pervasives_Native.None)))
end
| FStar_SMTEncoding_Term.DefineFun (n1, a, s, b, uu____5024) -> begin
FStar_SMTEncoding_Term.DefineFun (((n1), (a), (s), (b), (FStar_Pervasives_Native.None)))
end
| d -> begin
d
end))
in (

let hs = (

let uu____5033 = (

let uu____5036 = (

let uu____5039 = (FStar_All.pipe_right prefix1 (FStar_List.map uncaption))
in (FStar_All.pipe_right uu____5039 pp_no_cap))
in (FStar_All.pipe_right uu____5036 (FStar_List.filter (fun s -> (Prims.op_disEquality s "")))))
in (FStar_All.pipe_right uu____5033 (FStar_String.concat "\n")))
in (

let uu____5058 = (

let uu____5061 = (FStar_Util.digest_of_string hs)
in FStar_Pervasives_Native.Some (uu____5061))
in (((Prims.strcat ps (Prims.strcat "\n" ss))), (uu____5058))))))))))))
end))
end
| uu____5064 -> begin
(

let uu____5065 = (

let uu____5066 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory)
in (FStar_All.pipe_right uu____5066 (FStar_String.concat "\n")))
in ((uu____5065), (FStar_Pervasives_Native.None)))
end))
in (match (uu____4866) with
| (r, hash) -> begin
((

let uu____5086 = (FStar_Options.log_queries ())
in (match (uu____5086) with
| true -> begin
(query_logging.write_to_log r)
end
| uu____5087 -> begin
()
end));
((r), (hash));
)
end))))


type cb =
z3result  ->  unit


let cache_hit : Prims.string FStar_Pervasives_Native.option  ->  Prims.string FStar_Pervasives_Native.option  ->  cb  ->  Prims.bool = (fun cache qhash cb -> (

let uu____5120 = ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()))
in (match (uu____5120) with
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
| uu____5131 -> begin
false
end)
end
| uu____5134 -> begin
false
end)))


let ask_1_core : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  cb  ->  unit = (fun filter_theory cache label_messages qry cb -> (

let theory = (

let uu____5184 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____5184 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
in (

let uu____5214 = (filter_theory theory)
in (match (uu____5214) with
| (theory1, used_unsat_core) -> begin
(

let uu____5221 = (mk_input theory1)
in (match (uu____5221) with
| (input, qhash) -> begin
((FStar_ST.op_Colon_Equals bg_scope []);
(

let uu____5262 = (

let uu____5263 = (cache_hit cache qhash cb)
in (not (uu____5263)))
in (match (uu____5262) with
| true -> begin
(run_job {job = (z3_job false label_messages input qhash); callback = cb})
end
| uu____5268 -> begin
()
end));
)
end))
end))))


let ask_n_cores : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  unit = (fun filter_theory cache label_messages qry scope cb -> (

let theory = (

let uu____5327 = (match (scope) with
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_List.rev s)
end
| FStar_Pervasives_Native.None -> begin
((FStar_ST.op_Colon_Equals bg_scope []);
(

let uu____5367 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____5367));
)
end)
in (FStar_List.flatten uu____5327))
in (

let theory1 = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let uu____5400 = (filter_theory theory1)
in (match (uu____5400) with
| (theory2, used_unsat_core) -> begin
(

let uu____5407 = (mk_input theory2)
in (match (uu____5407) with
| (input, qhash) -> begin
(

let uu____5420 = (

let uu____5421 = (cache_hit cache qhash cb)
in (not (uu____5421)))
in (match (uu____5420) with
| true -> begin
(enqueue {job = (z3_job true label_messages input qhash); callback = cb})
end
| uu____5426 -> begin
()
end))
end))
end)))))


let ask : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  unit = (fun filter1 cache label_messages qry scope cb -> (

let uu____5484 = (

let uu____5485 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____5485 (Prims.parse_int "1")))
in (match (uu____5484) with
| true -> begin
(ask_1_core filter1 cache label_messages qry cb)
end
| uu____5488 -> begin
(ask_n_cores filter1 cache label_messages qry scope cb)
end)))




