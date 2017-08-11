
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


let z3version_as_string : z3version  ->  Prims.string = (fun uu___96_70 -> (match (uu___96_70) with
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
| SAT of label Prims.list
| UNKNOWN of label Prims.list
| TIMEOUT of label Prims.list
| KILLED


let uu___is_UNSAT : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UNSAT (_0) -> begin
true
end
| uu____293 -> begin
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
| uu____309 -> begin
false
end))


let __proj__SAT__item___0 : z3status  ->  label Prims.list = (fun projectee -> (match (projectee) with
| SAT (_0) -> begin
_0
end))


let uu___is_UNKNOWN : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UNKNOWN (_0) -> begin
true
end
| uu____331 -> begin
false
end))


let __proj__UNKNOWN__item___0 : z3status  ->  label Prims.list = (fun projectee -> (match (projectee) with
| UNKNOWN (_0) -> begin
_0
end))


let uu___is_TIMEOUT : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TIMEOUT (_0) -> begin
true
end
| uu____353 -> begin
false
end))


let __proj__TIMEOUT__item___0 : z3status  ->  label Prims.list = (fun projectee -> (match (projectee) with
| TIMEOUT (_0) -> begin
_0
end))


let uu___is_KILLED : z3status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| KILLED -> begin
true
end
| uu____372 -> begin
false
end))


type z3statistics =
Prims.string FStar_Util.smap


let status_to_string : z3status  ->  Prims.string = (fun uu___97_378 -> (match (uu___97_378) with
| SAT (uu____379) -> begin
"sat"
end
| UNSAT (uu____382) -> begin
"unsat"
end
| UNKNOWN (uu____383) -> begin
"unknown"
end
| TIMEOUT (uu____386) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let tid : Prims.unit  ->  Prims.string = (fun uu____392 -> (

let uu____393 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right uu____393 FStar_Util.string_of_int)))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (

let uu____406 = (FStar_Options.z3_exe ())
in (

let uu____407 = (ini_params ())
in (FStar_Util.start_process id uu____406 uu____407 cond)))))

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

let get_module_name = (fun uu____766 -> (

let uu____767 = (FStar_ST.op_Bang current_module_name)
in (match (uu____767) with
| FStar_Pervasives_Native.None -> begin
(failwith "Module name not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in (

let new_log_file = (fun uu____806 -> (

let uu____807 = (FStar_ST.op_Bang current_module_name)
in (match (uu____807) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let file_name = (

let uu____844 = (

let uu____851 = (FStar_ST.op_Bang used_file_names)
in (FStar_List.tryFind (fun uu____913 -> (match (uu____913) with
| (m, uu____919) -> begin
(n1 = m)
end)) uu____851))
in (match (uu____844) with
| FStar_Pervasives_Native.None -> begin
((

let uu____925 = (

let uu____932 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((Prims.parse_int "0"))))::uu____932)
in (FStar_ST.op_Colon_Equals used_file_names uu____925));
n1;
)
end
| FStar_Pervasives_Native.Some (uu____1039, k) -> begin
((

let uu____1046 = (

let uu____1053 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((k + (Prims.parse_int "1")))))::uu____1053)
in (FStar_ST.op_Colon_Equals used_file_names uu____1046));
(

let uu____1160 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n1 uu____1160));
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

let get_log_file = (fun uu____1232 -> (

let uu____1233 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____1233) with
| FStar_Pervasives_Native.None -> begin
(new_log_file ())
end
| FStar_Pervasives_Native.Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____1273 = (get_log_file ())
in (FStar_Util.append_to_file uu____1273 str)))
in (

let write_to_new_log = (fun str -> (

let dir_name = (

let uu____1279 = (FStar_ST.op_Bang current_file_name)
in (match (uu____1279) with
| FStar_Pervasives_Native.None -> begin
(

let dir_name = (

let uu____1315 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1315) with
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

let uu____1412 = (

let uu____1413 = (FStar_ST.op_Bang query_number)
in (uu____1413 + (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals query_number uu____1412));
(

let file_name = (

let uu____1463 = (FStar_Util.string_of_int qnum)
in (FStar_Util.format1 "query-%s.smt2" uu____1463))
in (

let file_name1 = (FStar_Util.concat_dir_filename dir_name file_name)
in (FStar_Util.write_file file_name1 str)));
))))
in (

let write_to_log = (fun str -> (

let uu____1469 = (

let uu____1470 = (FStar_Options.n_cores ())
in (uu____1470 > (Prims.parse_int "1")))
in (match (uu____1469) with
| true -> begin
(write_to_new_log str)
end
| uu____1471 -> begin
(append_to_log str)
end)))
in (

let close_log = (fun uu____1475 -> (

let uu____1476 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____1476) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (fh) -> begin
((FStar_Util.close_file fh);
(FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None);
)
end)))
in (

let log_file_name = (fun uu____1548 -> (

let uu____1549 = (FStar_ST.op_Bang current_file_name)
in (match (uu____1549) with
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
in (fun uu____1598 -> (

let uu____1599 = (

let uu____1600 = ((FStar_Util.incr ctr);
(

let uu____1623 = (FStar_ST.op_Bang ctr)
in (FStar_All.pipe_right uu____1623 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____1600))
in (new_z3proc uu____1599))))
in (

let z3proc = (fun uu____1651 -> ((

let uu____1653 = (

let uu____1654 = (FStar_ST.op_Bang the_z3proc)
in (uu____1654 = FStar_Pervasives_Native.None))
in (match (uu____1653) with
| true -> begin
(

let uu____1691 = (

let uu____1694 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____1694))
in (FStar_ST.op_Colon_Equals the_z3proc uu____1691))
end
| uu____1727 -> begin
()
end));
(

let uu____1728 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.must uu____1728));
))
in (

let x = []
in (

let grab = (fun uu____1769 -> ((FStar_Util.monitor_enter x);
(z3proc ());
))
in (

let release = (fun uu____1776 -> (FStar_Util.monitor_exit x))
in (

let refresh = (fun uu____1782 -> (

let proc = (grab ())
in ((FStar_Util.kill_process proc);
(

let uu____1786 = (

let uu____1789 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____1789))
in (FStar_ST.op_Colon_Equals the_z3proc uu____1786));
(query_logging.close_log ());
(release ());
)))
in (

let restart = (fun uu____1826 -> ((FStar_Util.monitor_enter ());
(query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(

let uu____1863 = (

let uu____1866 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____1866))
in (FStar_ST.op_Colon_Equals the_z3proc uu____1863));
(FStar_Util.monitor_exit ());
))
in {grab = grab; release = release; refresh = refresh; restart = restart}))))))))


let at_log_file : Prims.unit  ->  Prims.string = (fun uu____1902 -> (

let uu____1903 = (FStar_Options.log_queries ())
in (match (uu____1903) with
| true -> begin
(

let uu____1904 = (query_logging.log_file_name ())
in (Prims.strcat "@" uu____1904))
end
| uu____1905 -> begin
""
end)))


let doZ3Exe' : Prims.bool  ->  Prims.string  ->  (z3status * z3statistics) = (fun fresh1 input -> (

let parse = (fun z3out -> (

let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (

let get_data = (fun lines1 -> (

let parse_core = (fun s -> (

let s1 = (FStar_Util.trim_string s)
in (

let s2 = (FStar_Util.substring s1 (Prims.parse_int "1") ((FStar_String.length s1) - (Prims.parse_int "2")))
in (match ((FStar_Util.starts_with s2 "error")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____1963 -> begin
(

let uu____1964 = (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_Util.sort_with FStar_String.compare))
in (FStar_All.pipe_right uu____1964 (fun _0_40 -> FStar_Pervasives_Native.Some (_0_40))))
end))))
in (

let core = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let statistics = (FStar_Util.smap_create (Prims.parse_int "0"))
in (

let reason_unknown = (FStar_Util.mk_ref "")
in (

let in_core = (FStar_Util.mk_ref false)
in (

let in_statistics = (FStar_Util.mk_ref false)
in (

let in_reason_unknown = (FStar_Util.mk_ref false)
in (

let parse = (fun line -> (match (line) with
| "<unsat-core>" -> begin
(FStar_ST.op_Colon_Equals in_core true)
end
| "<statistics>" -> begin
(FStar_ST.op_Colon_Equals in_statistics true)
end
| "<reason-unknown>" -> begin
(FStar_ST.op_Colon_Equals in_reason_unknown true)
end
| "</unsat-core>" -> begin
(FStar_ST.op_Colon_Equals in_core false)
end
| "</statistics>" -> begin
(FStar_ST.op_Colon_Equals in_statistics false)
end
| "</reason-unknown>" -> begin
(FStar_ST.op_Colon_Equals in_reason_unknown false)
end
| uu____2153 -> begin
(

let uu____2154 = (FStar_ST.op_Bang in_core)
in (match (uu____2154) with
| true -> begin
(

let uu____2179 = (parse_core line)
in (FStar_ST.op_Colon_Equals core uu____2179))
end
| uu____2224 -> begin
(

let uu____2225 = (FStar_ST.op_Bang in_statistics)
in (match (uu____2225) with
| true -> begin
(

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
| uu____2260 -> begin
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
| uu____2268 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| uu____2269 -> begin
()
end))
end
| uu____2272 -> begin
(

let uu____2273 = (FStar_ST.op_Bang in_reason_unknown)
in (match (uu____2273) with
| true -> begin
(

let tkns = (FStar_Util.split line "\"")
in (

let rsn = (match (tkns) with
| (uu____2302)::(txt)::(uu____2304)::[] -> begin
txt
end
| uu____2305 -> begin
line
end)
in (match ((rsn <> "unknown")) with
| true -> begin
(FStar_Util.smap_add statistics "reason-unknown" (Prims.strcat "\"" (Prims.strcat rsn "\"")))
end
| uu____2308 -> begin
()
end)))
end
| uu____2309 -> begin
()
end))
end))
end))
end))
in ((FStar_List.iter (fun line -> (parse line)) lines1);
(

let uu____2313 = (FStar_ST.op_Bang core)
in (

let uu____2358 = (FStar_ST.op_Bang reason_unknown)
in ((uu____2313), (statistics), (uu____2358))));
))))))))))
in (

let rec lblnegs = (fun lines1 -> (match (lines1) with
| (lname)::("false")::rest when (FStar_Util.starts_with lname "label_") -> begin
(

let uu____2403 = (lblnegs rest)
in (lname)::uu____2403)
end
| (lname)::(uu____2407)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest)
end
| uu____2411 -> begin
[]
end))
in (

let rec result = (fun lines1 core -> (match (lines1) with
| ("timeout")::tl1 -> begin
TIMEOUT ([])
end
| ("unknown")::tl1 -> begin
(

let uu____2431 = (lblnegs tl1)
in UNKNOWN (uu____2431))
end
| ("sat")::tl1 -> begin
(

let uu____2437 = (lblnegs tl1)
in SAT (uu____2437))
end
| ("unsat")::tl1 -> begin
UNSAT (core)
end
| ("killed")::tl1 -> begin
((bg_z3_proc.restart ());
KILLED;
)
end
| (hd1)::tl1 -> begin
((

let uu____2452 = (

let uu____2453 = (query_logging.get_module_name ())
in (FStar_Util.format2 "%s: Unexpected output from Z3: %s\n" uu____2453 hd1))
in (FStar_Errors.warn FStar_Range.dummyRange uu____2452));
(result tl1 core);
)
end
| uu____2454 -> begin
(

let uu____2457 = (

let uu____2458 = (

let uu____2459 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines1)
in (FStar_String.concat "\n" uu____2459))
in (FStar_Util.format1 "Unexpected output from Z3: got output lines: %s\n" uu____2458))
in (FStar_All.pipe_left failwith uu____2457))
end))
in (

let uu____2464 = (get_data lines)
in (match (uu____2464) with
| (core, statistics, reason_unknown) -> begin
(

let uu____2490 = (result lines core)
in ((uu____2490), (statistics)))
end)))))))
in (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (

let stdout1 = (match (fresh1) with
| true -> begin
(

let uu____2500 = (tid ())
in (

let uu____2501 = (FStar_Options.z3_exe ())
in (

let uu____2502 = (ini_params ())
in (FStar_Util.launch_process uu____2500 uu____2501 uu____2502 input cond))))
end
| uu____2503 -> begin
(

let proc = (bg_z3_proc.grab ())
in (

let stdout1 = (FStar_Util.ask_process proc input)
in ((bg_z3_proc.release ());
stdout1;
)))
end)
in (parse (FStar_Util.trim_string stdout1))))))


let doZ3Exe : Prims.bool  ->  Prims.string  ->  (z3status * z3statistics) = (fun fresh1 input -> (doZ3Exe' fresh1 input))


let z3_options : Prims.unit  ->  Prims.string = (fun uu____2522 -> "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n")

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

type error_kind =
| Timeout
| Kill
| Default


let uu___is_Timeout : error_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Timeout -> begin
true
end
| uu____2591 -> begin
false
end))


let uu___is_Kill : error_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Kill -> begin
true
end
| uu____2596 -> begin
false
end))


let uu___is_Default : error_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Default -> begin
true
end
| uu____2601 -> begin
false
end))


type z3job =
((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int * z3statistics) job


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let with_monitor : 'Auu____2648 'Auu____2649 . 'Auu____2649  ->  (Prims.unit  ->  'Auu____2648)  ->  'Auu____2648 = (fun m f -> ((FStar_Util.monitor_enter m);
(

let res = (f ())
in ((FStar_Util.monitor_exit m);
res;
));
))


let z3_job : Prims.bool  ->  FStar_SMTEncoding_Term.error_labels  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int * z3statistics) = (fun fresh1 label_messages input uu____2695 -> (

let ekind = (fun uu___98_2713 -> (match (uu___98_2713) with
| TIMEOUT (uu____2714) -> begin
Timeout
end
| SAT (uu____2717) -> begin
Default
end
| UNKNOWN (uu____2720) -> begin
Default
end
| KILLED -> begin
Kill
end
| uu____2723 -> begin
(failwith "Impossible")
end))
in (

let start = (FStar_Util.now ())
in (

let uu____2725 = (doZ3Exe fresh1 input)
in (match (uu____2725) with
| (status, statistics) -> begin
(

let uu____2746 = (

let uu____2751 = (FStar_Util.now ())
in (FStar_Util.time_diff start uu____2751))
in (match (uu____2746) with
| (uu____2766, elapsed_time) -> begin
(

let result = (match (status) with
| UNSAT (core) -> begin
((FStar_Util.Inl (core)), (elapsed_time), (statistics))
end
| KILLED -> begin
((FStar_Util.Inr ((([]), (Kill)))), (elapsed_time), (statistics))
end
| TIMEOUT (lblnegs) -> begin
((

let uu____2920 = (FStar_Options.debug_any ())
in (match (uu____2920) with
| true -> begin
(

let uu____2921 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string uu____2921))
end
| uu____2922 -> begin
()
end));
(

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (

let uu____2963 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____3002 -> (match (uu____3002) with
| (m, uu____3014, uu____3015) -> begin
((FStar_Pervasives_Native.fst m) = l)
end))))
in (match (uu____2963) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end)))))
in (

let uu____3101 = (

let uu____3122 = (

let uu____3139 = (ekind status)
in ((failing_assertions), (uu____3139)))
in FStar_Util.Inr (uu____3122))
in ((uu____3101), (elapsed_time), (statistics))));
)
end
| SAT (lblnegs) -> begin
((

let uu____3192 = (FStar_Options.debug_any ())
in (match (uu____3192) with
| true -> begin
(

let uu____3193 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string uu____3193))
end
| uu____3194 -> begin
()
end));
(

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (

let uu____3235 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____3274 -> (match (uu____3274) with
| (m, uu____3286, uu____3287) -> begin
((FStar_Pervasives_Native.fst m) = l)
end))))
in (match (uu____3235) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end)))))
in (

let uu____3373 = (

let uu____3394 = (

let uu____3411 = (ekind status)
in ((failing_assertions), (uu____3411)))
in FStar_Util.Inr (uu____3394))
in ((uu____3373), (elapsed_time), (statistics))));
)
end
| UNKNOWN (lblnegs) -> begin
((

let uu____3464 = (FStar_Options.debug_any ())
in (match (uu____3464) with
| true -> begin
(

let uu____3465 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string uu____3465))
end
| uu____3466 -> begin
()
end));
(

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (

let uu____3507 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____3546 -> (match (uu____3546) with
| (m, uu____3558, uu____3559) -> begin
((FStar_Pervasives_Native.fst m) = l)
end))))
in (match (uu____3507) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end)))))
in (

let uu____3645 = (

let uu____3666 = (

let uu____3683 = (ekind status)
in ((failing_assertions), (uu____3683)))
in FStar_Util.Inr (uu____3666))
in ((uu____3645), (elapsed_time), (statistics))));
)
end)
in result)
end))
end)))))


let running : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun uu____3747 -> (

let j = (

let uu____3749 = (FStar_ST.op_Bang job_queue)
in (match (uu____3749) with
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
(with_monitor job_queue (fun uu____3806 -> (FStar_Util.decr pending_jobs)));
(dequeue ());
)))
and dequeue : Prims.unit  ->  Prims.unit = (fun uu____3808 -> (

let uu____3809 = (FStar_ST.op_Bang running)
in if uu____3809 then begin
(

let rec aux = (fun uu____3823 -> ((FStar_Util.monitor_enter job_queue);
(

let uu____3829 = (FStar_ST.op_Bang job_queue)
in (match (uu____3829) with
| [] -> begin
((FStar_Util.monitor_exit job_queue);
(FStar_Util.sleep (Prims.parse_int "50"));
(aux ());
)
end
| uu____3856 -> begin
(dequeue' ())
end));
))
in (aux ()))
end else begin
()
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (

let uu____3860 = (j.job ())
in (FStar_All.pipe_left j.callback uu____3860)))


let init : Prims.unit  ->  Prims.unit = (fun uu____3920 -> ((FStar_ST.op_Colon_Equals running true);
(

let n_cores1 = (FStar_Options.n_cores ())
in (match ((n_cores1 > (Prims.parse_int "1"))) with
| true -> begin
(

let rec aux = (fun n1 -> (match ((n1 = (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____3937 -> begin
((FStar_Util.spawn dequeue);
(aux (n1 - (Prims.parse_int "1")));
)
end))
in (aux n_cores1))
end
| uu____3939 -> begin
()
end));
))


let enqueue : z3job  ->  Prims.unit = (fun j -> ((FStar_Util.monitor_enter job_queue);
(

let uu____3950 = (

let uu____3953 = (FStar_ST.op_Bang job_queue)
in (FStar_List.append uu____3953 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue uu____3950));
(FStar_Util.monitor_pulse job_queue);
(FStar_Util.monitor_exit job_queue);
))


let finish : Prims.unit  ->  Prims.unit = (fun uu____4004 -> (

let rec aux = (fun uu____4008 -> (

let uu____4009 = (with_monitor job_queue (fun uu____4025 -> (

let uu____4026 = (FStar_ST.op_Bang pending_jobs)
in (

let uu____4037 = (

let uu____4038 = (FStar_ST.op_Bang job_queue)
in (FStar_List.length uu____4038))
in ((uu____4026), (uu____4037))))))
in (match (uu____4009) with
| (n1, m) -> begin
(match (((n1 + m) = (Prims.parse_int "0"))) with
| true -> begin
(FStar_ST.op_Colon_Equals running false)
end
| uu____4079 -> begin
((FStar_Util.sleep (Prims.parse_int "500"));
(aux ());
)
end)
end)))
in (aux ())))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let mk_fresh_scope : Prims.unit  ->  scope_t = (fun uu____4109 -> (FStar_ST.op_Bang fresh_scope))


let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : Prims.string  ->  Prims.unit = (fun msg -> ((

let uu____4154 = (

let uu____4159 = (FStar_ST.op_Bang fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::uu____4159)
in (FStar_ST.op_Colon_Equals fresh_scope uu____4154));
(

let uu____4218 = (

let uu____4221 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____4221 ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____4218));
))


let pop : Prims.string  ->  Prims.unit = (fun msg -> ((

let uu____4265 = (

let uu____4270 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.tl uu____4270))
in (FStar_ST.op_Colon_Equals fresh_scope uu____4265));
(

let uu____4329 = (

let uu____4332 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____4332 ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____4329));
))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___99_4383 -> (match (uu___99_4383) with
| FStar_SMTEncoding_Term.Push -> begin
(failwith "Unexpected push/pop")
end
| FStar_SMTEncoding_Term.Pop -> begin
(failwith "Unexpected push/pop")
end
| uu____4384 -> begin
()
end))));
(

let uu____4386 = (FStar_ST.op_Bang fresh_scope)
in (match (uu____4386) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd1 decls))::tl1))
end
| uu____4455 -> begin
(failwith "Impossible")
end));
(

let uu____4460 = (

let uu____4463 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____4463 decls))
in (FStar_ST.op_Colon_Equals bg_scope uu____4460));
))


let refresh : Prims.unit  ->  Prims.unit = (fun uu____4505 -> ((

let uu____4507 = (

let uu____4508 = (FStar_Options.n_cores ())
in (uu____4508 < (Prims.parse_int "2")))
in (match (uu____4507) with
| true -> begin
(bg_z3_proc.refresh ())
end
| uu____4509 -> begin
()
end));
(

let uu____4510 = (

let uu____4513 = (

let uu____4518 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____4518))
in (FStar_List.flatten uu____4513))
in (FStar_ST.op_Colon_Equals bg_scope uu____4510));
))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> ((pop msg);
(refresh ());
))


let commit_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let uu____4582 = (FStar_ST.op_Bang fresh_scope)
in (match (uu____4582) with
| (hd1)::(s)::tl1 -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd1 s))::tl1))
end
| uu____4656 -> begin
(failwith "Impossible")
end)))


let mk_cb : 'Auu____4679 'Auu____4680 'Auu____4681 'Auu____4682 'Auu____4683 'Auu____4684 . Prims.bool  ->  ((('Auu____4684, ('Auu____4683 Prims.list * 'Auu____4682)) FStar_Util.either * 'Auu____4681 * 'Auu____4680)  ->  'Auu____4679)  ->  (('Auu____4684, ('Auu____4683 Prims.list * 'Auu____4682)) FStar_Util.either * 'Auu____4681 * 'Auu____4680)  ->  'Auu____4679 = (fun used_unsat_core cb uu____4731 -> (match (uu____4731) with
| (uc_errs, time, statistics) -> begin
(match (used_unsat_core) with
| true -> begin
(match (uc_errs) with
| FStar_Util.Inl (uu____4789) -> begin
(cb ((uc_errs), (time), (statistics)))
end
| FStar_Util.Inr (uu____4806, ek) -> begin
(cb ((FStar_Util.Inr ((([]), (ek)))), (time), (statistics)))
end)
end
| uu____4836 -> begin
(cb ((uc_errs), (time), (statistics)))
end)
end))


let mk_input : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.string = (fun theory -> (

let r = (

let uu____4856 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory)
in (FStar_All.pipe_right uu____4856 (FStar_String.concat "\n")))
in ((

let uu____4862 = (FStar_Options.log_queries ())
in (match (uu____4862) with
| true -> begin
(query_logging.write_to_log r)
end
| uu____4863 -> begin
()
end));
r;
)))


type z3result =
((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int * z3statistics)


type cb =
z3result  ->  Prims.unit


let ask_1_core : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  cb  ->  Prims.unit = (fun filter_theory label_messages qry cb -> (

let theory = (

let uu____4914 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____4914 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
in (

let uu____4935 = (filter_theory theory)
in (match (uu____4935) with
| (theory1, used_unsat_core) -> begin
(

let cb1 = (mk_cb used_unsat_core cb)
in (

let input = (mk_input theory1)
in ((FStar_ST.op_Colon_Equals bg_scope []);
(run_job {job = (z3_job false label_messages input); callback = cb1});
)))
end))))


let ask_n_cores : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  Prims.unit = (fun filter_theory label_messages qry scope cb -> (

let theory = (

let uu____5039 = (match (scope) with
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_List.rev s)
end
| FStar_Pervasives_Native.None -> begin
((FStar_ST.op_Colon_Equals bg_scope []);
(

let uu____5070 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____5070));
)
end)
in (FStar_List.flatten uu____5039))
in (

let theory1 = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let uu____5106 = (filter_theory theory1)
in (match (uu____5106) with
| (theory2, used_unsat_core) -> begin
(

let cb1 = (mk_cb used_unsat_core cb)
in (

let input = (mk_input theory2)
in (enqueue {job = (z3_job true label_messages input); callback = cb1})))
end)))))


let ask : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  Prims.unit = (fun filter1 label_messages qry scope cb -> (

let uu____5190 = (

let uu____5191 = (FStar_Options.n_cores ())
in (uu____5191 = (Prims.parse_int "1")))
in (match (uu____5190) with
| true -> begin
(ask_1_core filter1 label_messages qry cb)
end
| uu____5194 -> begin
(ask_n_cores filter1 label_messages qry scope cb)
end)))




