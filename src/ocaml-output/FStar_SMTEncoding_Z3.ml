
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


let z3version_as_string : z3version  ->  Prims.string = (fun uu___95_70 -> (match (uu___95_70) with
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
FStar_Pervasives_Native.Some ((match ((k1 <> w1)) with
| true -> begin
(w1 - k1)
end
| uu____111 -> begin
(match ((k2 <> w2)) with
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

let uu____174 = (

let uu____181 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc uu____181 "-version" ""))
in (match (uu____174) with
| (uu____182, out, uu____184) -> begin
(

let out1 = (match ((FStar_Util.splitlines out)) with
| (x)::uu____187 when (FStar_Util.starts_with x prefix1) -> begin
(

let x1 = (

let uu____191 = (FStar_Util.substring_from x (FStar_String.length prefix1))
in (FStar_Util.trim_string uu____191))
in (

let x2 = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x1 "."))
end)
with
| uu____206 -> begin
[]
end
in (match (x2) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V (((i1), (i2), (i3)))
end
| uu____210 -> begin
Z3V_Unknown (out)
end)))
end
| uu____213 -> begin
Z3V_Unknown (out)
end)
in ((FStar_ST.op_Colon_Equals _z3version (FStar_Pervasives_Native.Some (out1)));
out1;
))
end))
end))))


let ini_params : Prims.unit  ->  Prims.string = (fun uu____238 -> (

let z3_v = (get_z3version ())
in ((

let uu____241 = (

let uu____242 = (get_z3version ())
in (z3v_le uu____242 (((Prims.parse_int "4")), ((Prims.parse_int "4")), ((Prims.parse_int "0")))))
in (match (uu____241) with
| true -> begin
(

let uu____243 = (

let uu____244 = (

let uu____245 = (z3version_as_string z3_v)
in (FStar_Util.format1 "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n" uu____245))
in FStar_Util.Failure (uu____244))
in (FStar_All.pipe_left FStar_Exn.raise uu____243))
end
| uu____246 -> begin
()
end));
(

let uu____247 = (

let uu____250 = (

let uu____253 = (

let uu____256 = (

let uu____257 = (

let uu____258 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int uu____258))
in (FStar_Util.format1 "smt.random_seed=%s" uu____257))
in (uu____256)::[])
in ("-smt2 -in auto_config=false model=true smt.relevancy=2")::uu____253)
in (

let uu____259 = (FStar_Options.z3_cliopt ())
in (FStar_List.append uu____250 uu____259)))
in (FStar_String.concat " " uu____247));
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
| uu____305 -> begin
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
| uu____325 -> begin
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
| uu____363 -> begin
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
| uu____401 -> begin
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
| uu____432 -> begin
false
end))


type z3statistics =
Prims.string FStar_Util.smap


let status_tag : z3status  ->  Prims.string = (fun uu___96_438 -> (match (uu___96_438) with
| SAT (uu____439) -> begin
"sat"
end
| UNSAT (uu____446) -> begin
"unsat"
end
| UNKNOWN (uu____447) -> begin
"unknown"
end
| TIMEOUT (uu____454) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let status_string_and_errors : z3status  ->  (Prims.string * FStar_SMTEncoding_Term.error_labels) = (fun s -> (match (s) with
| KILLED -> begin
(((status_tag s)), ([]))
end
| UNSAT (uu____475) -> begin
(((status_tag s)), ([]))
end
| SAT (errs, msg) -> begin
(

let uu____484 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____484), (errs)))
end
| UNKNOWN (errs, msg) -> begin
(

let uu____492 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____492), (errs)))
end
| TIMEOUT (errs, msg) -> begin
(

let uu____500 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____500), (errs)))
end))


let tid : Prims.unit  ->  Prims.string = (fun uu____505 -> (

let uu____506 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right uu____506 FStar_Util.string_of_int)))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (

let uu____519 = (FStar_Options.z3_exe ())
in (

let uu____520 = (ini_params ())
in (FStar_Util.start_process id uu____519 uu____520 cond)))))

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

let get_module_name = (fun uu____879 -> (

let uu____880 = (FStar_ST.op_Bang current_module_name)
in (match (uu____880) with
| FStar_Pervasives_Native.None -> begin
(failwith "Module name not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in (

let new_log_file = (fun uu____919 -> (

let uu____920 = (FStar_ST.op_Bang current_module_name)
in (match (uu____920) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let file_name = (

let uu____957 = (

let uu____964 = (FStar_ST.op_Bang used_file_names)
in (FStar_List.tryFind (fun uu____1026 -> (match (uu____1026) with
| (m, uu____1032) -> begin
(n1 = m)
end)) uu____964))
in (match (uu____957) with
| FStar_Pervasives_Native.None -> begin
((

let uu____1038 = (

let uu____1045 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((Prims.parse_int "0"))))::uu____1045)
in (FStar_ST.op_Colon_Equals used_file_names uu____1038));
n1;
)
end
| FStar_Pervasives_Native.Some (uu____1152, k) -> begin
((

let uu____1159 = (

let uu____1166 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((k + (Prims.parse_int "1")))))::uu____1166)
in (FStar_ST.op_Colon_Equals used_file_names uu____1159));
(

let uu____1273 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n1 uu____1273));
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

let get_log_file = (fun uu____1345 -> (

let uu____1346 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____1346) with
| FStar_Pervasives_Native.None -> begin
(new_log_file ())
end
| FStar_Pervasives_Native.Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____1386 = (get_log_file ())
in (FStar_Util.append_to_file uu____1386 str)))
in (

let write_to_new_log = (fun str -> (

let dir_name = (

let uu____1392 = (FStar_ST.op_Bang current_file_name)
in (match (uu____1392) with
| FStar_Pervasives_Native.None -> begin
(

let dir_name = (

let uu____1428 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1428) with
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

let uu____1525 = (

let uu____1526 = (FStar_ST.op_Bang query_number)
in (uu____1526 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals query_number uu____1525));
(

let file_name = (

let uu____1576 = (FStar_Util.string_of_int qnum)
in (FStar_Util.format1 "query-%s.smt2" uu____1576))
in (

let file_name1 = (FStar_Util.concat_dir_filename dir_name file_name)
in (FStar_Util.write_file file_name1 str)));
))))
in (

let write_to_log = (fun str -> (

let uu____1582 = (

let uu____1583 = (FStar_Options.n_cores ())
in (uu____1583 > (Prims.parse_int "1")))
in (match (uu____1582) with
| true -> begin
(write_to_new_log str)
end
| uu____1584 -> begin
(append_to_log str)
end)))
in (

let close_log = (fun uu____1588 -> (

let uu____1589 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____1589) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (fh) -> begin
((FStar_Util.close_file fh);
(FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None);
)
end)))
in (

let log_file_name = (fun uu____1661 -> (

let uu____1662 = (FStar_ST.op_Bang current_file_name)
in (match (uu____1662) with
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
in (fun uu____1711 -> (

let uu____1712 = (

let uu____1713 = ((FStar_Util.incr ctr);
(

let uu____1736 = (FStar_ST.op_Bang ctr)
in (FStar_All.pipe_right uu____1736 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____1713))
in (new_z3proc uu____1712))))
in (

let z3proc = (fun uu____1764 -> ((

let uu____1766 = (

let uu____1767 = (FStar_ST.op_Bang the_z3proc)
in (uu____1767 = FStar_Pervasives_Native.None))
in (match (uu____1766) with
| true -> begin
(

let uu____1804 = (

let uu____1807 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____1807))
in (FStar_ST.op_Colon_Equals the_z3proc uu____1804))
end
| uu____1840 -> begin
()
end));
(

let uu____1841 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.must uu____1841));
))
in (

let x = []
in (

let grab = (fun uu____1882 -> ((FStar_Util.monitor_enter x);
(z3proc ());
))
in (

let release = (fun uu____1889 -> (FStar_Util.monitor_exit x))
in (

let refresh = (fun uu____1895 -> (

let proc = (grab ())
in ((FStar_Util.kill_process proc);
(

let uu____1899 = (

let uu____1902 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____1902))
in (FStar_ST.op_Colon_Equals the_z3proc uu____1899));
(query_logging.close_log ());
(release ());
)))
in (

let restart = (fun uu____1939 -> ((FStar_Util.monitor_enter ());
(query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(

let uu____1976 = (

let uu____1979 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____1979))
in (FStar_ST.op_Colon_Equals the_z3proc uu____1976));
(FStar_Util.monitor_exit ());
))
in {grab = grab; release = release; refresh = refresh; restart = restart}))))))))


let at_log_file : Prims.unit  ->  Prims.string = (fun uu____2015 -> (

let uu____2016 = (FStar_Options.log_queries ())
in (match (uu____2016) with
| true -> begin
(

let uu____2017 = (query_logging.log_file_name ())
in (Prims.strcat "@" uu____2017))
end
| uu____2018 -> begin
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
(match ((tag = l)) with
| true -> begin
FStar_Pervasives_Native.Some ((([]), (lines2)))
end
| uu____2223 -> begin
(

let uu____2224 = (until tag lines2)
in (FStar_Util.map_opt uu____2224 (fun uu____2254 -> (match (uu____2254) with
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

let uu____2324 = (until (start_tag tag) lines1)
in (match (uu____2324) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (lines1))
end
| FStar_Pervasives_Native.Some (prefix1, suffix) -> begin
(

let uu____2379 = (until (end_tag tag) suffix)
in (match (uu____2379) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Parse error: " (Prims.strcat (end_tag tag) " not found")))
end
| FStar_Pervasives_Native.Some (section, suffix1) -> begin
((FStar_Pervasives_Native.Some (section)), ((FStar_List.append prefix1 suffix1)))
end))
end)))
in (

let uu____2444 = (find_section "result" lines)
in (match (uu____2444) with
| (result_opt, lines1) -> begin
(

let result = (FStar_Util.must result_opt)
in (

let uu____2474 = (find_section "reason-unknown" lines1)
in (match (uu____2474) with
| (reason_unknown, lines2) -> begin
(

let uu____2499 = (find_section "unsat-core" lines2)
in (match (uu____2499) with
| (unsat_core, lines3) -> begin
(

let uu____2524 = (find_section "statistics" lines3)
in (match (uu____2524) with
| (statistics, lines4) -> begin
(

let uu____2549 = (find_section "labels" lines4)
in (match (uu____2549) with
| (labels, lines5) -> begin
(

let remaining = (

let uu____2577 = (until "Done!" lines5)
in (match (uu____2577) with
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
| uu____2617 -> begin
(

let uu____2620 = (

let uu____2621 = (query_logging.get_module_name ())
in (FStar_Util.format2 "%s: Unexpected output from Z3: %s\n" uu____2621 (FStar_String.concat "\n" remaining)))
in (FStar_Errors.warn FStar_Range.dummyRange uu____2620))
end);
(

let uu____2622 = (FStar_Util.must result_opt)
in {smt_result = uu____2622; smt_reason_unknown = reason_unknown; smt_unsat_core = unsat_core; smt_statistics = statistics; smt_labels = labels});
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
| uu____2681 -> begin
(

let uu____2682 = (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_Util.sort_with FStar_String.compare))
in FStar_Pervasives_Native.Some (uu____2682))
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

let uu____2743 = (lblnegs rest)
in (lname)::uu____2743)
end
| (lname)::(uu____2747)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest)
end
| uu____2751 -> begin
[]
end))
in (

let lblnegs1 = (lblnegs lines1)
in (FStar_All.pipe_right lblnegs1 (FStar_List.collect (fun l -> (

let uu____2784 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____2823 -> (match (uu____2823) with
| (m, uu____2835, uu____2836) -> begin
((FStar_Pervasives_Native.fst m) = l)
end))))
in (match (uu____2784) with
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
| uu____2939 -> begin
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
| uu____2947 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| uu____2948 -> begin
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
| uu____2963 -> begin
ru
end))))
in (

let status = ((

let uu____2966 = (FStar_Options.debug_any ())
in (match (uu____2966) with
| true -> begin
(

let uu____2967 = (FStar_Util.format1 "Z3 says: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (FStar_All.pipe_left FStar_Util.print_string uu____2967))
end
| uu____2968 -> begin
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
| uu____3012 -> begin
(

let uu____3013 = (FStar_Util.format1 "Unexpected output from Z3: got output result: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (failwith uu____3013))
end);
)
in ((status), (statistics))))))))))
in (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (

let stdout1 = (match (fresh1) with
| true -> begin
(

let uu____3023 = (tid ())
in (

let uu____3024 = (FStar_Options.z3_exe ())
in (

let uu____3025 = (ini_params ())
in (FStar_Util.launch_process uu____3023 uu____3024 uu____3025 input cond))))
end
| uu____3026 -> begin
(

let proc = (bg_z3_proc.grab ())
in (

let stdout1 = (FStar_Util.ask_process proc input)
in ((bg_z3_proc.release ());
stdout1;
)))
end)
in (parse (FStar_Util.trim_string stdout1))))))


let z3_options : Prims.unit  ->  Prims.string = (fun uu____3033 -> "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n")

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


type z3job =
(z3status * Prims.int * z3statistics) job


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let with_monitor : 'Auu____3136 'Auu____3137 . 'Auu____3137  ->  (Prims.unit  ->  'Auu____3136)  ->  'Auu____3136 = (fun m f -> ((FStar_Util.monitor_enter m);
(

let res = (f ())
in ((FStar_Util.monitor_exit m);
res;
));
))


let z3_job : Prims.bool  ->  FStar_SMTEncoding_Term.error_labels  ->  Prims.string  ->  Prims.unit  ->  (z3status * Prims.int * z3statistics) = (fun fresh1 label_messages input uu____3175 -> (

let start = (FStar_Util.now ())
in (

let uu____3183 = (doZ3Exe fresh1 input label_messages)
in (match (uu____3183) with
| (status, statistics) -> begin
(

let uu____3196 = (

let uu____3201 = (FStar_Util.now ())
in (FStar_Util.time_diff start uu____3201))
in (match (uu____3196) with
| (uu____3208, elapsed_time) -> begin
((status), (elapsed_time), (statistics))
end))
end))))


let running : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun uu____3225 -> (

let j = (

let uu____3227 = (FStar_ST.op_Bang job_queue)
in (match (uu____3227) with
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
(with_monitor job_queue (fun uu____3284 -> (FStar_Util.decr pending_jobs)));
(dequeue ());
)))
and dequeue : Prims.unit  ->  Prims.unit = (fun uu____3286 -> (

let uu____3287 = (FStar_ST.op_Bang running)
in if uu____3287 then begin
(

let rec aux = (fun uu____3301 -> ((FStar_Util.monitor_enter job_queue);
(

let uu____3307 = (FStar_ST.op_Bang job_queue)
in (match (uu____3307) with
| [] -> begin
((FStar_Util.monitor_exit job_queue);
(FStar_Util.sleep (Prims.parse_int "50"));
(aux ());
)
end
| uu____3334 -> begin
(dequeue' ())
end));
))
in (aux ()))
end else begin
()
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (

let uu____3338 = (j.job ())
in (FStar_All.pipe_left j.callback uu____3338)))


let init : Prims.unit  ->  Prims.unit = (fun uu____3366 -> ((FStar_ST.op_Colon_Equals running true);
(

let n_cores1 = (FStar_Options.n_cores ())
in (match ((n_cores1 > (Prims.parse_int "1"))) with
| true -> begin
(

let rec aux = (fun n1 -> (match ((n1 = (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____3383 -> begin
((FStar_Util.spawn dequeue);
(aux (n1 - (Prims.parse_int "1")));
)
end))
in (aux n_cores1))
end
| uu____3385 -> begin
()
end));
))


let enqueue : z3job  ->  Prims.unit = (fun j -> ((FStar_Util.monitor_enter job_queue);
(

let uu____3396 = (

let uu____3399 = (FStar_ST.op_Bang job_queue)
in (FStar_List.append uu____3399 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue uu____3396));
(FStar_Util.monitor_pulse job_queue);
(FStar_Util.monitor_exit job_queue);
))


let finish : Prims.unit  ->  Prims.unit = (fun uu____3450 -> (

let rec aux = (fun uu____3454 -> (

let uu____3455 = (with_monitor job_queue (fun uu____3471 -> (

let uu____3472 = (FStar_ST.op_Bang pending_jobs)
in (

let uu____3483 = (

let uu____3484 = (FStar_ST.op_Bang job_queue)
in (FStar_List.length uu____3484))
in ((uu____3472), (uu____3483))))))
in (match (uu____3455) with
| (n1, m) -> begin
(match (((n1 + m) = (Prims.parse_int "0"))) with
| true -> begin
(FStar_ST.op_Colon_Equals running false)
end
| uu____3525 -> begin
((FStar_Util.sleep (Prims.parse_int "500"));
(aux ());
)
end)
end)))
in (aux ())))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let mk_fresh_scope : Prims.unit  ->  scope_t = (fun uu____3555 -> (FStar_ST.op_Bang fresh_scope))


let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : Prims.string  ->  Prims.unit = (fun msg -> ((

let uu____3600 = (

let uu____3605 = (FStar_ST.op_Bang fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::uu____3605)
in (FStar_ST.op_Colon_Equals fresh_scope uu____3600));
(

let uu____3664 = (

let uu____3667 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____3667 ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____3664));
))


let pop : Prims.string  ->  Prims.unit = (fun msg -> ((

let uu____3711 = (

let uu____3716 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.tl uu____3716))
in (FStar_ST.op_Colon_Equals fresh_scope uu____3711));
(

let uu____3775 = (

let uu____3778 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____3778 ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____3775));
))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___97_3829 -> (match (uu___97_3829) with
| FStar_SMTEncoding_Term.Push -> begin
(failwith "Unexpected push/pop")
end
| FStar_SMTEncoding_Term.Pop -> begin
(failwith "Unexpected push/pop")
end
| uu____3830 -> begin
()
end))));
(

let uu____3832 = (FStar_ST.op_Bang fresh_scope)
in (match (uu____3832) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd1 decls))::tl1))
end
| uu____3901 -> begin
(failwith "Impossible")
end));
(

let uu____3906 = (

let uu____3909 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____3909 decls))
in (FStar_ST.op_Colon_Equals bg_scope uu____3906));
))


let refresh : Prims.unit  ->  Prims.unit = (fun uu____3951 -> ((

let uu____3953 = (

let uu____3954 = (FStar_Options.n_cores ())
in (uu____3954 < (Prims.parse_int "2")))
in (match (uu____3953) with
| true -> begin
(bg_z3_proc.refresh ())
end
| uu____3955 -> begin
()
end));
(

let uu____3956 = (

let uu____3959 = (

let uu____3964 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____3964))
in (FStar_List.flatten uu____3959))
in (FStar_ST.op_Colon_Equals bg_scope uu____3956));
))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> ((pop msg);
(refresh ());
))


let commit_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let uu____4028 = (FStar_ST.op_Bang fresh_scope)
in (match (uu____4028) with
| (hd1)::(s)::tl1 -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd1 s))::tl1))
end
| uu____4102 -> begin
(failwith "Impossible")
end)))


let mk_input : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.string = (fun theory -> (

let r = (

let uu____4116 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory)
in (FStar_All.pipe_right uu____4116 (FStar_String.concat "\n")))
in ((

let uu____4122 = (FStar_Options.log_queries ())
in (match (uu____4122) with
| true -> begin
(query_logging.write_to_log r)
end
| uu____4123 -> begin
()
end));
r;
)))


type z3result =
(z3status * Prims.int * z3statistics)


type cb =
z3result  ->  Prims.unit


let ask_1_core : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  cb  ->  Prims.unit = (fun filter_theory label_messages qry cb -> (

let theory = (

let uu____4166 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____4166 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
in (

let uu____4187 = (filter_theory theory)
in (match (uu____4187) with
| (theory1, used_unsat_core) -> begin
(

let input = (mk_input theory1)
in ((FStar_ST.op_Colon_Equals bg_scope []);
(run_job {job = (z3_job false label_messages input); callback = cb});
))
end))))


let ask_n_cores : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  Prims.unit = (fun filter_theory label_messages qry scope cb -> (

let theory = (

let uu____4264 = (match (scope) with
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_List.rev s)
end
| FStar_Pervasives_Native.None -> begin
((FStar_ST.op_Colon_Equals bg_scope []);
(

let uu____4295 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____4295));
)
end)
in (FStar_List.flatten uu____4264))
in (

let theory1 = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let uu____4331 = (filter_theory theory1)
in (match (uu____4331) with
| (theory2, used_unsat_core) -> begin
(

let input = (mk_input theory2)
in (enqueue {job = (z3_job true label_messages input); callback = cb}))
end)))))


let ask : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  Prims.unit = (fun filter1 label_messages qry scope cb -> (

let uu____4388 = (

let uu____4389 = (FStar_Options.n_cores ())
in (uu____4389 = (Prims.parse_int "1")))
in (match (uu____4388) with
| true -> begin
(ask_1_core filter1 label_messages qry cb)
end
| uu____4392 -> begin
(ask_n_cores filter1 label_messages qry scope cb)
end)))




