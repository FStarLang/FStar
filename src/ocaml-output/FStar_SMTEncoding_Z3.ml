
open Prims
open FStar_Pervasives
type z3version =
| Z3V_Unknown of Prims.string
| Z3V of (Prims.int * Prims.int * Prims.int)


let uu___is_Z3V_Unknown : z3version  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Z3V_Unknown (_0) -> begin
true
end
| uu____20 -> begin
false
end))


let __proj__Z3V_Unknown__item___0 : z3version  ->  Prims.string = (fun projectee -> (match (projectee) with
| Z3V_Unknown (_0) -> begin
_0
end))


let uu___is_Z3V : z3version  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Z3V (_0) -> begin
true
end
| uu____40 -> begin
false
end))


let __proj__Z3V__item___0 : z3version  ->  (Prims.int * Prims.int * Prims.int) = (fun projectee -> (match (projectee) with
| Z3V (_0) -> begin
_0
end))


let z3version_as_string : z3version  ->  Prims.string = (fun uu___115_70 -> (match (uu___115_70) with
| Z3V_Unknown (s) -> begin
(FStar_Util.format1 "unknown version: %s" s)
end
| Z3V (i, j, k) -> begin
(

let uu____75 = (FStar_Util.string_of_int i)
in (

let uu____76 = (FStar_Util.string_of_int j)
in (

let uu____77 = (FStar_Util.string_of_int k)
in (FStar_Util.format3 "%s.%s.%s" uu____75 uu____76 uu____77))))
end))


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int FStar_Pervasives_Native.option = (fun known uu____93 -> (match (uu____93) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown (uu____107) -> begin
FStar_Pervasives_Native.None
end
| Z3V (k1, k2, k3) -> begin
FStar_Pervasives_Native.Some ((match ((Prims.op_disEquality k1 w1)) with
| true -> begin
(w1 - k1)
end
| uu____111 -> begin
(match ((Prims.op_disEquality k2 w2)) with
| true -> begin
(w2 - k2)
end
| uu____112 -> begin
(w3 - k3)
end)
end))
end)
end))


let z3v_le : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.bool = (fun known wanted -> (match ((z3v_compare known wanted)) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (i) -> begin
(i >= (Prims.parse_int "0"))
end))


let _z3version : z3version FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let get_z3version : Prims.unit  ->  z3version = (fun uu____150 -> (

let prefix1 = "Z3 version "
in (

let uu____152 = (FStar_ST.op_Bang _z3version)
in (match (uu____152) with
| FStar_Pervasives_Native.Some (version) -> begin
version
end
| FStar_Pervasives_Native.None -> begin
(

let uu____206 = (

let uu____213 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc uu____213 "-version" ""))
in (match (uu____206) with
| (uu____214, out, uu____216) -> begin
(

let out1 = (match ((FStar_Util.splitlines out)) with
| (x)::uu____219 when (FStar_Util.starts_with x prefix1) -> begin
(

let x1 = (

let uu____223 = (FStar_Util.substring_from x (FStar_String.length prefix1))
in (FStar_Util.trim_string uu____223))
in (

let x2 = (FStar_All.try_with (fun uu___120_230 -> (match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x1 "."))
end)) (fun uu___119_235 -> (match (uu___119_235) with
| uu____238 -> begin
[]
end)))
in (match (x2) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V (((i1), (i2), (i3)))
end
| uu____242 -> begin
Z3V_Unknown (out)
end)))
end
| uu____245 -> begin
Z3V_Unknown (out)
end)
in ((FStar_ST.op_Colon_Equals _z3version (FStar_Pervasives_Native.Some (out1)));
out1;
))
end))
end))))


let ini_params : Prims.unit  ->  Prims.string = (fun uu____302 -> (

let z3_v = (get_z3version ())
in ((

let uu____305 = (

let uu____306 = (get_z3version ())
in (z3v_le uu____306 (((Prims.parse_int "4")), ((Prims.parse_int "4")), ((Prims.parse_int "0")))))
in (match (uu____305) with
| true -> begin
(

let uu____307 = (

let uu____308 = (

let uu____309 = (z3version_as_string z3_v)
in (FStar_Util.format1 "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n" uu____309))
in FStar_Util.HardError (uu____308))
in (FStar_Exn.raise uu____307))
end
| uu____310 -> begin
()
end));
(

let uu____311 = (

let uu____314 = (

let uu____317 = (

let uu____320 = (

let uu____321 = (

let uu____322 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int uu____322))
in (FStar_Util.format1 "smt.random_seed=%s" uu____321))
in (uu____320)::[])
in ("-smt2 -in auto_config=false model=true smt.relevancy=2")::uu____317)
in (

let uu____323 = (FStar_Options.z3_cliopt ())
in (FStar_List.append uu____314 uu____323)))
in (FStar_String.concat " " uu____311));
)))


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
| uu____369 -> begin
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
| uu____389 -> begin
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
| uu____427 -> begin
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
| uu____465 -> begin
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
| uu____496 -> begin
false
end))


type z3statistics =
Prims.string FStar_Util.smap


let status_tag : z3status  ->  Prims.string = (fun uu___116_502 -> (match (uu___116_502) with
| SAT (uu____503) -> begin
"sat"
end
| UNSAT (uu____510) -> begin
"unsat"
end
| UNKNOWN (uu____511) -> begin
"unknown"
end
| TIMEOUT (uu____518) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let status_string_and_errors : z3status  ->  (Prims.string * FStar_SMTEncoding_Term.error_labels) = (fun s -> (match (s) with
| KILLED -> begin
(((status_tag s)), ([]))
end
| UNSAT (uu____539) -> begin
(((status_tag s)), ([]))
end
| SAT (errs, msg) -> begin
(

let uu____548 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____548), (errs)))
end
| UNKNOWN (errs, msg) -> begin
(

let uu____556 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____556), (errs)))
end
| TIMEOUT (errs, msg) -> begin
(

let uu____564 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____564), (errs)))
end))


let tid : Prims.unit  ->  Prims.string = (fun uu____569 -> (

let uu____570 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right uu____570 FStar_Util.string_of_int)))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = (Prims.op_Equality (FStar_Util.trim_string s) "Done!")
in x))
in (

let uu____583 = (FStar_Options.z3_exe ())
in (

let uu____584 = (ini_params ())
in (FStar_Util.start_process false id uu____583 uu____584 cond)))))

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

let get_module_name = (fun uu____975 -> (

let uu____976 = (FStar_ST.op_Bang current_module_name)
in (match (uu____976) with
| FStar_Pervasives_Native.None -> begin
(failwith "Module name not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in (

let new_log_file = (fun uu____1047 -> (

let uu____1048 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1048) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let file_name = (

let uu____1117 = (

let uu____1124 = (FStar_ST.op_Bang used_file_names)
in (FStar_List.tryFind (fun uu____1210 -> (match (uu____1210) with
| (m, uu____1216) -> begin
(Prims.op_Equality n1 m)
end)) uu____1124))
in (match (uu____1117) with
| FStar_Pervasives_Native.None -> begin
((

let uu____1222 = (

let uu____1229 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((Prims.parse_int "0"))))::uu____1229)
in (FStar_ST.op_Colon_Equals used_file_names uu____1222));
n1;
)
end
| FStar_Pervasives_Native.Some (uu____1384, k) -> begin
((

let uu____1391 = (

let uu____1398 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((k + (Prims.parse_int "1")))))::uu____1398)
in (FStar_ST.op_Colon_Equals used_file_names uu____1391));
(

let uu____1553 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n1 uu____1553));
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

let get_log_file = (fun uu____1689 -> (

let uu____1690 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____1690) with
| FStar_Pervasives_Native.None -> begin
(new_log_file ())
end
| FStar_Pervasives_Native.Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____1762 = (get_log_file ())
in (FStar_Util.append_to_file uu____1762 str)))
in (

let write_to_new_log = (fun str -> (

let dir_name = (

let uu____1768 = (FStar_ST.op_Bang current_file_name)
in (match (uu____1768) with
| FStar_Pervasives_Native.None -> begin
(

let dir_name = (

let uu____1836 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1836) with
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

let uu____2033 = (

let uu____2034 = (FStar_ST.op_Bang query_number)
in (uu____2034 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals query_number uu____2033));
(

let file_name = (

let uu____2156 = (FStar_Util.string_of_int qnum)
in (FStar_Util.format1 "query-%s.smt2" uu____2156))
in (

let file_name1 = (FStar_Util.concat_dir_filename dir_name file_name)
in (FStar_Util.write_file file_name1 str)));
))))
in (

let write_to_log = (fun str -> (

let uu____2162 = (

let uu____2163 = (FStar_Options.n_cores ())
in (uu____2163 > (Prims.parse_int "1")))
in (match (uu____2162) with
| true -> begin
(write_to_new_log str)
end
| uu____2164 -> begin
(append_to_log str)
end)))
in (

let close_log = (fun uu____2168 -> (

let uu____2169 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____2169) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (fh) -> begin
((FStar_Util.close_file fh);
(FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None);
)
end)))
in (

let log_file_name = (fun uu____2305 -> (

let uu____2306 = (FStar_ST.op_Bang current_file_name)
in (match (uu____2306) with
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
in (fun uu____2387 -> (

let uu____2388 = (

let uu____2389 = ((FStar_Util.incr ctr);
(

let uu____2412 = (FStar_ST.op_Bang ctr)
in (FStar_All.pipe_right uu____2412 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____2389))
in (new_z3proc uu____2388))))
in (

let z3proc = (fun uu____2476 -> ((

let uu____2478 = (

let uu____2479 = (FStar_ST.op_Bang the_z3proc)
in (Prims.op_Equality uu____2479 FStar_Pervasives_Native.None))
in (match (uu____2478) with
| true -> begin
(

let uu____2548 = (

let uu____2551 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____2551))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2548))
end
| uu____2616 -> begin
()
end));
(

let uu____2617 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.must uu____2617));
))
in (

let x = []
in (

let grab = (fun uu____2690 -> ((FStar_Util.monitor_enter x);
(z3proc ());
))
in (

let release = (fun uu____2697 -> (FStar_Util.monitor_exit x))
in (

let refresh = (fun uu____2703 -> (

let proc = (grab ())
in ((FStar_Util.kill_process proc);
(

let uu____2707 = (

let uu____2710 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____2710))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2707));
(query_logging.close_log ());
(release ());
)))
in (

let restart = (fun uu____2779 -> ((FStar_Util.monitor_enter ());
(query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(

let uu____2848 = (

let uu____2851 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____2851))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2848));
(FStar_Util.monitor_exit ());
))
in {grab = grab; release = release; refresh = refresh; restart = restart}))))))))


let at_log_file : Prims.unit  ->  Prims.string = (fun uu____2919 -> (

let uu____2920 = (FStar_Options.log_queries ())
in (match (uu____2920) with
| true -> begin
(

let uu____2921 = (query_logging.log_file_name ())
in (Prims.strcat "@" uu____2921))
end
| uu____2922 -> begin
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
| uu____3127 -> begin
(

let uu____3128 = (until tag lines2)
in (FStar_Util.map_opt uu____3128 (fun uu____3158 -> (match (uu____3158) with
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

let uu____3228 = (until (start_tag tag) lines1)
in (match (uu____3228) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (lines1))
end
| FStar_Pervasives_Native.Some (prefix1, suffix) -> begin
(

let uu____3283 = (until (end_tag tag) suffix)
in (match (uu____3283) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Parse error: " (Prims.strcat (end_tag tag) " not found")))
end
| FStar_Pervasives_Native.Some (section, suffix1) -> begin
((FStar_Pervasives_Native.Some (section)), ((FStar_List.append prefix1 suffix1)))
end))
end)))
in (

let uu____3348 = (find_section "result" lines)
in (match (uu____3348) with
| (result_opt, lines1) -> begin
(

let result = (FStar_Util.must result_opt)
in (

let uu____3378 = (find_section "reason-unknown" lines1)
in (match (uu____3378) with
| (reason_unknown, lines2) -> begin
(

let uu____3403 = (find_section "unsat-core" lines2)
in (match (uu____3403) with
| (unsat_core, lines3) -> begin
(

let uu____3428 = (find_section "statistics" lines3)
in (match (uu____3428) with
| (statistics, lines4) -> begin
(

let uu____3453 = (find_section "labels" lines4)
in (match (uu____3453) with
| (labels, lines5) -> begin
(

let remaining = (

let uu____3481 = (until "Done!" lines5)
in (match (uu____3481) with
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
| uu____3521 -> begin
(

let uu____3524 = (

let uu____3525 = (query_logging.get_module_name ())
in (FStar_Util.format2 "%s: Unexpected output from Z3: %s\n" uu____3525 (FStar_String.concat "\n" remaining)))
in (FStar_Errors.warn FStar_Range.dummyRange uu____3524))
end);
(

let uu____3526 = (FStar_Util.must result_opt)
in {smt_result = uu____3526; smt_reason_unknown = reason_unknown; smt_unsat_core = unsat_core; smt_statistics = statistics; smt_labels = labels});
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
| uu____3585 -> begin
(

let uu____3586 = (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_Util.sort_with FStar_String.compare))
in FStar_Pervasives_Native.Some (uu____3586))
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

let uu____3647 = (lblnegs rest)
in (lname)::uu____3647)
end
| (lname)::(uu____3651)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest)
end
| uu____3655 -> begin
[]
end))
in (

let lblnegs1 = (lblnegs lines1)
in (FStar_All.pipe_right lblnegs1 (FStar_List.collect (fun l -> (

let uu____3688 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____3727 -> (match (uu____3727) with
| (m, uu____3739, uu____3740) -> begin
(Prims.op_Equality (FStar_Pervasives_Native.fst m) l)
end))))
in (match (uu____3688) with
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
| uu____3843 -> begin
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
| uu____3851 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| uu____3852 -> begin
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
| uu____3867 -> begin
ru
end))))
in (

let status = ((

let uu____3870 = (FStar_Options.debug_any ())
in (match (uu____3870) with
| true -> begin
(

let uu____3871 = (FStar_Util.format1 "Z3 says: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (FStar_All.pipe_left FStar_Util.print_string uu____3871))
end
| uu____3872 -> begin
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
| uu____3916 -> begin
(

let uu____3917 = (FStar_Util.format1 "Unexpected output from Z3: got output result: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (failwith uu____3917))
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

let uu____3927 = (tid ())
in (

let uu____3928 = (FStar_Options.z3_exe ())
in (

let uu____3929 = (ini_params ())
in (FStar_Util.launch_process false uu____3927 uu____3928 uu____3929 input cond))))
end
| uu____3930 -> begin
(

let proc = (bg_z3_proc.grab ())
in (

let stdout1 = (FStar_Util.ask_process proc input)
in ((bg_z3_proc.release ());
stdout1;
)))
end)
in (parse (FStar_Util.trim_string stdout1))))))


let z3_options : Prims.unit  ->  Prims.string = (fun uu____3937 -> "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n")

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


let with_monitor : 'Auu____4096 'Auu____4097 . 'Auu____4097  ->  (Prims.unit  ->  'Auu____4096)  ->  'Auu____4096 = (fun m f -> ((FStar_Util.monitor_enter m);
(

let res = (f ())
in ((FStar_Util.monitor_exit m);
res;
));
))


let z3_job : Prims.bool  ->  FStar_SMTEncoding_Term.error_labels  ->  Prims.string  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.unit  ->  z3result = (fun fresh1 label_messages input qhash uu____4135 -> (

let start = (FStar_Util.now ())
in (

let uu____4139 = (FStar_All.try_with (fun uu___122_4149 -> (match (()) with
| () -> begin
(doZ3Exe fresh1 input label_messages)
end)) (fun uu___121_4158 -> (match (uu___121_4158) with
| uu____4163 when (

let uu____4164 = (FStar_Options.trace_error ())
in (not (uu____4164))) -> begin
((bg_z3_proc.refresh ());
(

let uu____4166 = (FStar_Util.smap_create (Prims.parse_int "0"))
in ((UNKNOWN ((([]), (FStar_Pervasives_Native.Some ("Z3 raised an exception"))))), (uu____4166)));
)
end)))
in (match (uu____4139) with
| (status, statistics) -> begin
(

let uu____4177 = (

let uu____4182 = (FStar_Util.now ())
in (FStar_Util.time_diff start uu____4182))
in (match (uu____4177) with
| (uu____4183, elapsed_time) -> begin
{z3result_status = status; z3result_time = elapsed_time; z3result_statistics = statistics; z3result_query_hash = qhash}
end))
end))))


let running : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun uu____4200 -> (

let j = (

let uu____4202 = (FStar_ST.op_Bang job_queue)
in (match (uu____4202) with
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
(with_monitor job_queue (fun uu____4323 -> (FStar_Util.decr pending_jobs)));
(dequeue ());
)))
and dequeue : Prims.unit  ->  Prims.unit = (fun uu____4325 -> (

let uu____4326 = (FStar_ST.op_Bang running)
in if uu____4326 then begin
(

let rec aux = (fun uu____4376 -> ((FStar_Util.monitor_enter job_queue);
(

let uu____4382 = (FStar_ST.op_Bang job_queue)
in (match (uu____4382) with
| [] -> begin
((FStar_Util.monitor_exit job_queue);
(FStar_Util.sleep (Prims.parse_int "50"));
(aux ());
)
end
| uu____4441 -> begin
(dequeue' ())
end));
))
in (aux ()))
end else begin
()
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (

let uu____4445 = (j.job ())
in (FStar_All.pipe_left j.callback uu____4445)))


let init : Prims.unit  ->  Prims.unit = (fun uu____4449 -> ((FStar_ST.op_Colon_Equals running true);
(

let n_cores1 = (FStar_Options.n_cores ())
in (match ((n_cores1 > (Prims.parse_int "1"))) with
| true -> begin
(

let rec aux = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____4502 -> begin
((FStar_Util.spawn dequeue);
(aux (n1 - (Prims.parse_int "1")));
)
end))
in (aux n_cores1))
end
| uu____4504 -> begin
()
end));
))


let enqueue : z3job  ->  Prims.unit = (fun j -> ((FStar_Util.monitor_enter job_queue);
(

let uu____4515 = (

let uu____4518 = (FStar_ST.op_Bang job_queue)
in (FStar_List.append uu____4518 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue uu____4515));
(FStar_Util.monitor_pulse job_queue);
(FStar_Util.monitor_exit job_queue);
))


let finish : Prims.unit  ->  Prims.unit = (fun uu____4633 -> (

let rec aux = (fun uu____4637 -> (

let uu____4638 = (with_monitor job_queue (fun uu____4654 -> (

let uu____4655 = (FStar_ST.op_Bang pending_jobs)
in (

let uu____4702 = (

let uu____4703 = (FStar_ST.op_Bang job_queue)
in (FStar_List.length uu____4703))
in ((uu____4655), (uu____4702))))))
in (match (uu____4638) with
| (n1, m) -> begin
(match ((Prims.op_Equality (n1 + m) (Prims.parse_int "0"))) with
| true -> begin
(FStar_ST.op_Colon_Equals running false)
end
| uu____4812 -> begin
((FStar_Util.sleep (Prims.parse_int "500"));
(aux ());
)
end)
end)))
in (aux ())))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let mk_fresh_scope : Prims.unit  ->  scope_t = (fun uu____4842 -> (FStar_ST.op_Bang fresh_scope))


let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : Prims.string  ->  Prims.unit = (fun msg -> ((

let uu____4915 = (

let uu____4920 = (FStar_ST.op_Bang fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::uu____4920)
in (FStar_ST.op_Colon_Equals fresh_scope uu____4915));
(

let uu____5035 = (

let uu____5038 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____5038 ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____5035));
))


let pop : Prims.string  ->  Prims.unit = (fun msg -> ((

let uu____5146 = (

let uu____5151 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.tl uu____5151))
in (FStar_ST.op_Colon_Equals fresh_scope uu____5146));
(

let uu____5266 = (

let uu____5269 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____5269 ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____5266));
))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___117_5384 -> (match (uu___117_5384) with
| FStar_SMTEncoding_Term.Push -> begin
(failwith "Unexpected push/pop")
end
| FStar_SMTEncoding_Term.Pop -> begin
(failwith "Unexpected push/pop")
end
| uu____5385 -> begin
()
end))));
(

let uu____5387 = (FStar_ST.op_Bang fresh_scope)
in (match (uu____5387) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd1 decls))::tl1))
end
| uu____5512 -> begin
(failwith "Impossible")
end));
(

let uu____5517 = (

let uu____5520 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____5520 decls))
in (FStar_ST.op_Colon_Equals bg_scope uu____5517));
))


let refresh : Prims.unit  ->  Prims.unit = (fun uu____5626 -> ((

let uu____5628 = (

let uu____5629 = (FStar_Options.n_cores ())
in (uu____5629 < (Prims.parse_int "2")))
in (match (uu____5628) with
| true -> begin
(bg_z3_proc.refresh ())
end
| uu____5630 -> begin
()
end));
(

let uu____5631 = (

let uu____5634 = (

let uu____5639 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____5639))
in (FStar_List.flatten uu____5634))
in (FStar_ST.op_Colon_Equals bg_scope uu____5631));
))


let mk_input : FStar_SMTEncoding_Term.decl Prims.list  ->  (Prims.string * Prims.string FStar_Pervasives_Native.option) = (fun theory -> (

let options = (z3_options ())
in (

let uu____5765 = (

let uu____5772 = ((FStar_Options.record_hints ()) || ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())))
in (match (uu____5772) with
| true -> begin
(

let uu____5779 = (

let uu____5790 = (FStar_All.pipe_right theory (FStar_Util.prefix_until (fun uu___118_5818 -> (match (uu___118_5818) with
| FStar_SMTEncoding_Term.CheckSat -> begin
true
end
| uu____5819 -> begin
false
end))))
in (FStar_All.pipe_right uu____5790 FStar_Option.get))
in (match (uu____5779) with
| (prefix1, check_sat, suffix) -> begin
(

let suffix1 = (check_sat)::suffix
in (

let ps = (

let uu____5873 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) prefix1)
in (FStar_String.concat "\n" uu____5873))
in (

let ss = (

let uu____5877 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) suffix1)
in (FStar_String.concat "\n" uu____5877))
in (

let uu____5880 = (

let uu____5883 = (FStar_Util.digest_of_string ps)
in FStar_Pervasives_Native.Some (uu____5883))
in (((Prims.strcat ps (Prims.strcat "\n" ss))), (uu____5880))))))
end))
end
| uu____5886 -> begin
(

let uu____5887 = (

let uu____5888 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory)
in (FStar_All.pipe_right uu____5888 (FStar_String.concat "\n")))
in ((uu____5887), (FStar_Pervasives_Native.None)))
end))
in (match (uu____5765) with
| (r, hash) -> begin
((

let uu____5908 = (FStar_Options.log_queries ())
in (match (uu____5908) with
| true -> begin
(query_logging.write_to_log r)
end
| uu____5909 -> begin
()
end));
((r), (hash));
)
end))))


type cb =
z3result  ->  Prims.unit


let cache_hit : (Prims.string FStar_Pervasives_Native.option * unsat_core)  ->  Prims.string FStar_Pervasives_Native.option  ->  cb  ->  Prims.bool = (fun cache qhash cb -> (

let uu____5944 = ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()))
in (match (uu____5944) with
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
| uu____5957 -> begin
false
end)
end
| uu____5960 -> begin
false
end)))


let ask_1_core : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  (Prims.string FStar_Pervasives_Native.option * unsat_core)  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  cb  ->  Prims.unit = (fun filter_theory cache label_messages qry cb -> (

let theory = (

let uu____6011 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____6011 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
in (

let uu____6064 = (filter_theory theory)
in (match (uu____6064) with
| (theory1, used_unsat_core) -> begin
(

let uu____6071 = (mk_input theory1)
in (match (uu____6071) with
| (input, qhash) -> begin
((FStar_ST.op_Colon_Equals bg_scope []);
(

let uu____6135 = (

let uu____6136 = (cache_hit cache qhash cb)
in (not (uu____6136)))
in (match (uu____6135) with
| true -> begin
(run_job {job = (z3_job false label_messages input qhash); callback = cb})
end
| uu____6141 -> begin
()
end));
)
end))
end))))


let ask_n_cores : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  (Prims.string FStar_Pervasives_Native.option * unsat_core)  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  Prims.unit = (fun filter_theory cache label_messages qry scope cb -> (

let theory = (

let uu____6200 = (match (scope) with
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_List.rev s)
end
| FStar_Pervasives_Native.None -> begin
((FStar_ST.op_Colon_Equals bg_scope []);
(

let uu____6263 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____6263));
)
end)
in (FStar_List.flatten uu____6200))
in (

let theory1 = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let uu____6327 = (filter_theory theory1)
in (match (uu____6327) with
| (theory2, used_unsat_core) -> begin
(

let uu____6334 = (mk_input theory2)
in (match (uu____6334) with
| (input, qhash) -> begin
(

let uu____6347 = (

let uu____6348 = (cache_hit cache qhash cb)
in (not (uu____6348)))
in (match (uu____6347) with
| true -> begin
(enqueue {job = (z3_job true label_messages input qhash); callback = cb})
end
| uu____6353 -> begin
()
end))
end))
end)))))


let ask : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  (Prims.string FStar_Pervasives_Native.option * unsat_core)  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  Prims.unit = (fun filter1 cache label_messages qry scope cb -> (

let uu____6411 = (

let uu____6412 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____6412 (Prims.parse_int "1")))
in (match (uu____6411) with
| true -> begin
(ask_1_core filter1 cache label_messages qry cb)
end
| uu____6415 -> begin
(ask_n_cores filter1 cache label_messages qry scope cb)
end)))




