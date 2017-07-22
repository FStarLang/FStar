
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


let get_z3version : Prims.unit  ->  z3version = (fun uu____144 -> (

let prefix1 = "Z3 version "
in (

let uu____146 = (FStar_ST.read _z3version)
in (match (uu____146) with
| FStar_Pervasives_Native.Some (version) -> begin
version
end
| FStar_Pervasives_Native.None -> begin
(

let uu____152 = (

let uu____159 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc uu____159 "-version" ""))
in (match (uu____152) with
| (uu____160, out, uu____162) -> begin
(

let out1 = (match ((FStar_Util.splitlines out)) with
| (x)::uu____165 when (FStar_Util.starts_with x prefix1) -> begin
(

let x1 = (

let uu____169 = (FStar_Util.substring_from x (FStar_String.length prefix1))
in (FStar_Util.trim_string uu____169))
in (

let x2 = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x1 "."))
end)
with
| uu____184 -> begin
[]
end
in (match (x2) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V (((i1), (i2), (i3)))
end
| uu____188 -> begin
Z3V_Unknown (out)
end)))
end
| uu____191 -> begin
Z3V_Unknown (out)
end)
in ((FStar_ST.write _z3version (FStar_Pervasives_Native.Some (out1)));
out1;
))
end))
end))))


let ini_params : Prims.unit  ->  Prims.string = (fun uu____200 -> (

let z3_v = (get_z3version ())
in ((

let uu____203 = (

let uu____204 = (get_z3version ())
in (z3v_le uu____204 (((Prims.parse_int "4")), ((Prims.parse_int "4")), ((Prims.parse_int "0")))))
in (match (uu____203) with
| true -> begin
(

let uu____205 = (

let uu____206 = (

let uu____207 = (z3version_as_string z3_v)
in (FStar_Util.format1 "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n" uu____207))
in FStar_Util.Failure (uu____206))
in (FStar_All.pipe_left FStar_Pervasives.raise uu____205))
end
| uu____208 -> begin
()
end));
(

let uu____209 = (

let uu____212 = (

let uu____215 = (

let uu____218 = (

let uu____219 = (

let uu____220 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int uu____220))
in (FStar_Util.format1 "smt.random_seed=%s" uu____219))
in (uu____218)::[])
in ("-smt2 -in auto_config=false model=true smt.relevancy=2")::uu____215)
in (

let uu____221 = (FStar_Options.z3_cliopt ())
in (FStar_List.append uu____212 uu____221)))
in (FStar_String.concat " " uu____209));
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
| uu____255 -> begin
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
| uu____271 -> begin
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
| uu____293 -> begin
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
| uu____315 -> begin
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
| uu____334 -> begin
false
end))


type z3statistics =
Prims.string FStar_Util.smap


let status_to_string : z3status  ->  Prims.string = (fun uu___97_340 -> (match (uu___97_340) with
| SAT (uu____341) -> begin
"sat"
end
| UNSAT (uu____344) -> begin
"unsat"
end
| UNKNOWN (uu____345) -> begin
"unknown"
end
| TIMEOUT (uu____348) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let tid : Prims.unit  ->  Prims.string = (fun uu____354 -> (

let uu____355 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right uu____355 FStar_Util.string_of_int)))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (

let uu____368 = (FStar_Options.z3_exe ())
in (

let uu____369 = (ini_params ())
in (FStar_Util.start_process id uu____368 uu____369 cond)))))

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

let set_module_name = (fun n1 -> (FStar_ST.write current_module_name (FStar_Pervasives_Native.Some (n1))))
in (

let get_module_name = (fun uu____700 -> (

let uu____701 = (FStar_ST.read current_module_name)
in (match (uu____701) with
| FStar_Pervasives_Native.None -> begin
(failwith "Module name not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in (

let new_log_file = (fun uu____712 -> (

let uu____713 = (FStar_ST.read current_module_name)
in (match (uu____713) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let file_name = (

let uu____722 = (

let uu____729 = (FStar_ST.read used_file_names)
in (FStar_List.tryFind (fun uu____751 -> (match (uu____751) with
| (m, uu____757) -> begin
(n1 = m)
end)) uu____729))
in (match (uu____722) with
| FStar_Pervasives_Native.None -> begin
((

let uu____763 = (

let uu____770 = (FStar_ST.read used_file_names)
in (((n1), ((Prims.parse_int "0"))))::uu____770)
in (FStar_ST.write used_file_names uu____763));
n1;
)
end
| FStar_Pervasives_Native.Some (uu____797, k) -> begin
((

let uu____804 = (

let uu____811 = (FStar_ST.read used_file_names)
in (((n1), ((k + (Prims.parse_int "1")))))::uu____811)
in (FStar_ST.write used_file_names uu____804));
(

let uu____838 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n1 uu____838));
)
end))
in (

let file_name1 = (FStar_Util.format1 "queries-%s.smt2" file_name)
in ((FStar_ST.write current_file_name (FStar_Pervasives_Native.Some (file_name1)));
(

let fh = (FStar_Util.open_file_for_writing file_name1)
in ((FStar_ST.write log_file_opt (FStar_Pervasives_Native.Some (fh)));
fh;
));
)))
end)))
in (

let get_log_file = (fun uu____854 -> (

let uu____855 = (FStar_ST.read log_file_opt)
in (match (uu____855) with
| FStar_Pervasives_Native.None -> begin
(new_log_file ())
end
| FStar_Pervasives_Native.Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____867 = (get_log_file ())
in (FStar_Util.append_to_file uu____867 str)))
in (

let write_to_new_log = (fun str -> (

let dir_name = (

let uu____873 = (FStar_ST.read current_file_name)
in (match (uu____873) with
| FStar_Pervasives_Native.None -> begin
(

let dir_name = (

let uu____881 = (FStar_ST.read current_module_name)
in (match (uu____881) with
| FStar_Pervasives_Native.None -> begin
(failwith "current module not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
(FStar_Util.format1 "queries-%s" n1)
end))
in ((FStar_Util.mkdir true dir_name);
(FStar_ST.write current_file_name (FStar_Pervasives_Native.Some (dir_name)));
dir_name;
))
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end))
in (

let qnum = (FStar_ST.read query_number)
in ((

let uu____900 = (

let uu____901 = (FStar_ST.read query_number)
in (uu____901 + (Prims.parse_int "1")))
in (FStar_ST.write query_number uu____900));
(

let file_name = (

let uu____907 = (FStar_Util.string_of_int qnum)
in (FStar_Util.format1 "query-%s.smt2" uu____907))
in (

let file_name1 = (FStar_Util.concat_dir_filename dir_name file_name)
in (FStar_Util.write_file file_name1 str)));
))))
in (

let write_to_log = (fun str -> (

let uu____913 = (

let uu____914 = (FStar_Options.n_cores ())
in (uu____914 > (Prims.parse_int "1")))
in (match (uu____913) with
| true -> begin
(write_to_new_log str)
end
| uu____915 -> begin
(append_to_log str)
end)))
in (

let close_log = (fun uu____919 -> (

let uu____920 = (FStar_ST.read log_file_opt)
in (match (uu____920) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (fh) -> begin
((FStar_Util.close_file fh);
(FStar_ST.write log_file_opt FStar_Pervasives_Native.None);
)
end)))
in (

let log_file_name = (fun uu____936 -> (

let uu____937 = (FStar_ST.read current_file_name)
in (match (uu____937) with
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
in (fun uu____958 -> (

let uu____959 = (

let uu____960 = ((FStar_Util.incr ctr);
(

let uu____965 = (FStar_ST.read ctr)
in (FStar_All.pipe_right uu____965 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____960))
in (new_z3proc uu____959))))
in (

let z3proc = (fun uu____971 -> ((

let uu____973 = (

let uu____974 = (FStar_ST.read the_z3proc)
in (uu____974 = FStar_Pervasives_Native.None))
in (match (uu____973) with
| true -> begin
(

let uu____983 = (

let uu____986 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____986))
in (FStar_ST.write the_z3proc uu____983))
end
| uu____991 -> begin
()
end));
(

let uu____992 = (FStar_ST.read the_z3proc)
in (FStar_Util.must uu____992));
))
in (

let x = []
in (

let grab = (fun uu____1005 -> ((FStar_Util.monitor_enter x);
(z3proc ());
))
in (

let release = (fun uu____1012 -> (FStar_Util.monitor_exit x))
in (

let refresh = (fun uu____1018 -> (

let proc = (grab ())
in ((FStar_Util.kill_process proc);
(

let uu____1022 = (

let uu____1025 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____1025))
in (FStar_ST.write the_z3proc uu____1022));
(query_logging.close_log ());
(release ());
)))
in (

let restart = (fun uu____1034 -> ((FStar_Util.monitor_enter ());
(query_logging.close_log ());
(FStar_ST.write the_z3proc FStar_Pervasives_Native.None);
(

let uu____1043 = (

let uu____1046 = (new_proc ())
in FStar_Pervasives_Native.Some (uu____1046))
in (FStar_ST.write the_z3proc uu____1043));
(FStar_Util.monitor_exit ());
))
in {grab = grab; release = release; refresh = refresh; restart = restart}))))))))


let at_log_file : Prims.unit  ->  Prims.string = (fun uu____1054 -> (

let uu____1055 = (FStar_Options.log_queries ())
in (match (uu____1055) with
| true -> begin
(

let uu____1056 = (query_logging.log_file_name ())
in (Prims.strcat "@" uu____1056))
end
| uu____1057 -> begin
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
| uu____1115 -> begin
(

let uu____1116 = (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_Util.sort_with FStar_String.compare))
in (FStar_All.pipe_right uu____1116 (fun _0_38 -> FStar_Pervasives_Native.Some (_0_38))))
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
(FStar_ST.write in_core true)
end
| "<statistics>" -> begin
(FStar_ST.write in_statistics true)
end
| "<reason-unknown>" -> begin
(FStar_ST.write in_reason_unknown true)
end
| "</unsat-core>" -> begin
(FStar_ST.write in_core false)
end
| "</statistics>" -> begin
(FStar_ST.write in_statistics false)
end
| "</reason-unknown>" -> begin
(FStar_ST.write in_reason_unknown false)
end
| uu____1173 -> begin
(

let uu____1174 = (FStar_ST.read in_core)
in (match (uu____1174) with
| true -> begin
(

let uu____1177 = (parse_core line)
in (FStar_ST.write core uu____1177))
end
| uu____1188 -> begin
(

let uu____1189 = (FStar_ST.read in_statistics)
in (match (uu____1189) with
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
| uu____1202 -> begin
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
| uu____1210 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| uu____1211 -> begin
()
end))
end
| uu____1214 -> begin
(

let uu____1215 = (FStar_ST.read in_reason_unknown)
in (match (uu____1215) with
| true -> begin
(

let tkns = (FStar_Util.split line "\"")
in (

let rsn = (match (tkns) with
| (uu____1222)::(txt)::(uu____1224)::[] -> begin
txt
end
| uu____1225 -> begin
line
end)
in (match ((rsn <> "unknown")) with
| true -> begin
(FStar_Util.smap_add statistics "reason-unknown" (Prims.strcat "\"" (Prims.strcat rsn "\"")))
end
| uu____1228 -> begin
()
end)))
end
| uu____1229 -> begin
()
end))
end))
end))
end))
in ((FStar_List.iter (fun line -> (parse line)) lines1);
(

let uu____1233 = (FStar_ST.read core)
in (

let uu____1244 = (FStar_ST.read reason_unknown)
in ((uu____1233), (statistics), (uu____1244))));
))))))))))
in (

let rec lblnegs = (fun lines1 -> (match (lines1) with
| (lname)::("false")::rest when (FStar_Util.starts_with lname "label_") -> begin
(

let uu____1267 = (lblnegs rest)
in (lname)::uu____1267)
end
| (lname)::(uu____1271)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest)
end
| uu____1275 -> begin
[]
end))
in (

let rec result = (fun lines1 core -> (match (lines1) with
| ("timeout")::tl1 -> begin
TIMEOUT ([])
end
| ("unknown")::tl1 -> begin
(

let uu____1295 = (lblnegs tl1)
in UNKNOWN (uu____1295))
end
| ("sat")::tl1 -> begin
(

let uu____1301 = (lblnegs tl1)
in SAT (uu____1301))
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

let uu____1316 = (

let uu____1317 = (query_logging.get_module_name ())
in (FStar_Util.format2 "%s: Unexpected output from Z3: %s\n" uu____1317 hd1))
in (FStar_Errors.warn FStar_Range.dummyRange uu____1316));
(result tl1 core);
)
end
| uu____1318 -> begin
(

let uu____1321 = (

let uu____1322 = (

let uu____1323 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines1)
in (FStar_String.concat "\n" uu____1323))
in (FStar_Util.format1 "Unexpected output from Z3: got output lines: %s\n" uu____1322))
in (FStar_All.pipe_left failwith uu____1321))
end))
in (

let uu____1328 = (get_data lines)
in (match (uu____1328) with
| (core, statistics, reason_unknown) -> begin
(

let uu____1354 = (result lines core)
in ((uu____1354), (statistics)))
end)))))))
in (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (

let stdout1 = (match (fresh1) with
| true -> begin
(

let uu____1364 = (tid ())
in (

let uu____1365 = (FStar_Options.z3_exe ())
in (

let uu____1366 = (ini_params ())
in (FStar_Util.launch_process uu____1364 uu____1365 uu____1366 input cond))))
end
| uu____1367 -> begin
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


let z3_options : Prims.unit  ->  Prims.string = (fun uu____1386 -> "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n")

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
| uu____1455 -> begin
false
end))


let uu___is_Kill : error_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Kill -> begin
true
end
| uu____1460 -> begin
false
end))


let uu___is_Default : error_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Default -> begin
true
end
| uu____1465 -> begin
false
end))


type z3job =
((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int * z3statistics) job


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let with_monitor : 'Auu____1500 'Auu____1501 . 'Auu____1501  ->  (Prims.unit  ->  'Auu____1500)  ->  'Auu____1500 = (fun m f -> ((FStar_Util.monitor_enter m);
(

let res = (f ())
in ((FStar_Util.monitor_exit m);
res;
));
))


let z3_job : Prims.bool  ->  FStar_SMTEncoding_Term.error_labels  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int * z3statistics) = (fun fresh1 label_messages input uu____1547 -> (

let ekind = (fun uu___98_1565 -> (match (uu___98_1565) with
| TIMEOUT (uu____1566) -> begin
Timeout
end
| SAT (uu____1569) -> begin
Default
end
| UNKNOWN (uu____1572) -> begin
Default
end
| KILLED -> begin
Kill
end
| uu____1575 -> begin
(failwith "Impossible")
end))
in (

let start = (FStar_Util.now ())
in (

let uu____1577 = (doZ3Exe fresh1 input)
in (match (uu____1577) with
| (status, statistics) -> begin
(

let uu____1598 = (

let uu____1603 = (FStar_Util.now ())
in (FStar_Util.time_diff start uu____1603))
in (match (uu____1598) with
| (uu____1618, elapsed_time) -> begin
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

let uu____1772 = (FStar_Options.debug_any ())
in (match (uu____1772) with
| true -> begin
(

let uu____1773 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string uu____1773))
end
| uu____1774 -> begin
()
end));
(

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (

let uu____1815 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____1854 -> (match (uu____1854) with
| (m, uu____1866, uu____1867) -> begin
((FStar_Pervasives_Native.fst m) = l)
end))))
in (match (uu____1815) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end)))))
in (

let uu____1953 = (

let uu____1974 = (

let uu____1991 = (ekind status)
in ((failing_assertions), (uu____1991)))
in FStar_Util.Inr (uu____1974))
in ((uu____1953), (elapsed_time), (statistics))));
)
end
| SAT (lblnegs) -> begin
((

let uu____2044 = (FStar_Options.debug_any ())
in (match (uu____2044) with
| true -> begin
(

let uu____2045 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string uu____2045))
end
| uu____2046 -> begin
()
end));
(

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (

let uu____2087 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____2126 -> (match (uu____2126) with
| (m, uu____2138, uu____2139) -> begin
((FStar_Pervasives_Native.fst m) = l)
end))))
in (match (uu____2087) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end)))))
in (

let uu____2225 = (

let uu____2246 = (

let uu____2263 = (ekind status)
in ((failing_assertions), (uu____2263)))
in FStar_Util.Inr (uu____2246))
in ((uu____2225), (elapsed_time), (statistics))));
)
end
| UNKNOWN (lblnegs) -> begin
((

let uu____2316 = (FStar_Options.debug_any ())
in (match (uu____2316) with
| true -> begin
(

let uu____2317 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string uu____2317))
end
| uu____2318 -> begin
()
end));
(

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (

let uu____2359 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____2398 -> (match (uu____2398) with
| (m, uu____2410, uu____2411) -> begin
((FStar_Pervasives_Native.fst m) = l)
end))))
in (match (uu____2359) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end)))))
in (

let uu____2497 = (

let uu____2518 = (

let uu____2535 = (ekind status)
in ((failing_assertions), (uu____2535)))
in FStar_Util.Inr (uu____2518))
in ((uu____2497), (elapsed_time), (statistics))));
)
end)
in result)
end))
end)))))


let running : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun uu____2593 -> (

let j = (

let uu____2595 = (FStar_ST.read job_queue)
in (match (uu____2595) with
| [] -> begin
(failwith "Impossible")
end
| (hd1)::tl1 -> begin
((FStar_ST.write job_queue tl1);
hd1;
)
end))
in ((FStar_Util.incr pending_jobs);
(FStar_Util.monitor_exit job_queue);
(run_job j);
(with_monitor job_queue (fun uu____2620 -> (FStar_Util.decr pending_jobs)));
(dequeue ());
)))
and dequeue : Prims.unit  ->  Prims.unit = (fun uu____2622 -> (

let uu____2623 = (FStar_ST.read running)
in if uu____2623 then begin
(

let rec aux = (fun uu____2627 -> ((FStar_Util.monitor_enter job_queue);
(

let uu____2633 = (FStar_ST.read job_queue)
in (match (uu____2633) with
| [] -> begin
((FStar_Util.monitor_exit job_queue);
(FStar_Util.sleep (Prims.parse_int "50"));
(aux ());
)
end
| uu____2644 -> begin
(dequeue' ())
end));
))
in (aux ()))
end else begin
()
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (

let uu____2648 = (j.job ())
in (FStar_All.pipe_left j.callback uu____2648)))


let init : Prims.unit  ->  Prims.unit = (fun uu____2708 -> ((FStar_ST.write running true);
(

let n_cores1 = (FStar_Options.n_cores ())
in (match ((n_cores1 > (Prims.parse_int "1"))) with
| true -> begin
(

let rec aux = (fun n1 -> (match ((n1 = (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____2715 -> begin
((FStar_Util.spawn dequeue);
(aux (n1 - (Prims.parse_int "1")));
)
end))
in (aux n_cores1))
end
| uu____2717 -> begin
()
end));
))


let enqueue : z3job  ->  Prims.unit = (fun j -> ((FStar_Util.monitor_enter job_queue);
(

let uu____2728 = (

let uu____2731 = (FStar_ST.read job_queue)
in (FStar_List.append uu____2731 ((j)::[])))
in (FStar_ST.write job_queue uu____2728));
(FStar_Util.monitor_pulse job_queue);
(FStar_Util.monitor_exit job_queue);
))


let finish : Prims.unit  ->  Prims.unit = (fun uu____2750 -> (

let rec aux = (fun uu____2754 -> (

let uu____2755 = (with_monitor job_queue (fun uu____2771 -> (

let uu____2772 = (FStar_ST.read pending_jobs)
in (

let uu____2773 = (

let uu____2774 = (FStar_ST.read job_queue)
in (FStar_List.length uu____2774))
in ((uu____2772), (uu____2773))))))
in (match (uu____2755) with
| (n1, m) -> begin
(match (((n1 + m) = (Prims.parse_int "0"))) with
| true -> begin
(FStar_ST.write running false)
end
| uu____2789 -> begin
((FStar_Util.sleep (Prims.parse_int "500"));
(aux ());
)
end)
end)))
in (aux ())))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let mk_fresh_scope : Prims.unit  ->  scope_t = (fun uu____2813 -> (FStar_ST.read fresh_scope))


let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : Prims.string  ->  Prims.unit = (fun msg -> ((

let uu____2830 = (

let uu____2835 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::uu____2835)
in (FStar_ST.write fresh_scope uu____2830));
(

let uu____2850 = (

let uu____2853 = (FStar_ST.read bg_scope)
in (FStar_List.append uu____2853 ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.write bg_scope uu____2850));
))


let pop : Prims.string  ->  Prims.unit = (fun msg -> ((

let uu____2865 = (

let uu____2870 = (FStar_ST.read fresh_scope)
in (FStar_List.tl uu____2870))
in (FStar_ST.write fresh_scope uu____2865));
(

let uu____2885 = (

let uu____2888 = (FStar_ST.read bg_scope)
in (FStar_List.append uu____2888 ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[])))
in (FStar_ST.write bg_scope uu____2885));
))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___99_2907 -> (match (uu___99_2907) with
| FStar_SMTEncoding_Term.Push -> begin
(failwith "Unexpected push/pop")
end
| FStar_SMTEncoding_Term.Pop -> begin
(failwith "Unexpected push/pop")
end
| uu____2908 -> begin
()
end))));
(

let uu____2910 = (FStar_ST.read fresh_scope)
in (match (uu____2910) with
| (hd1)::tl1 -> begin
(FStar_ST.write fresh_scope (((FStar_List.append hd1 decls))::tl1))
end
| uu____2935 -> begin
(failwith "Impossible")
end));
(

let uu____2940 = (

let uu____2943 = (FStar_ST.read bg_scope)
in (FStar_List.append uu____2943 decls))
in (FStar_ST.write bg_scope uu____2940));
))


let refresh : Prims.unit  ->  Prims.unit = (fun uu____2953 -> ((

let uu____2955 = (

let uu____2956 = (FStar_Options.n_cores ())
in (uu____2956 < (Prims.parse_int "2")))
in (match (uu____2955) with
| true -> begin
(bg_z3_proc.refresh ())
end
| uu____2957 -> begin
()
end));
(

let uu____2958 = (

let uu____2961 = (

let uu____2966 = (FStar_ST.read fresh_scope)
in (FStar_List.rev uu____2966))
in (FStar_List.flatten uu____2961))
in (FStar_ST.write bg_scope uu____2958));
))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> ((pop msg);
(refresh ());
))


let commit_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let uu____2992 = (FStar_ST.read fresh_scope)
in (match (uu____2992) with
| (hd1)::(s)::tl1 -> begin
(FStar_ST.write fresh_scope (((FStar_List.append hd1 s))::tl1))
end
| uu____3022 -> begin
(failwith "Impossible")
end)))


let mk_cb : 'Auu____3045 'Auu____3046 'Auu____3047 'Auu____3048 'Auu____3049 'Auu____3050 . Prims.bool  ->  ((('Auu____3050, ('Auu____3049 Prims.list * 'Auu____3048)) FStar_Util.either * 'Auu____3047 * 'Auu____3046)  ->  'Auu____3045)  ->  (('Auu____3050, ('Auu____3049 Prims.list * 'Auu____3048)) FStar_Util.either * 'Auu____3047 * 'Auu____3046)  ->  'Auu____3045 = (fun used_unsat_core cb uu____3097 -> (match (uu____3097) with
| (uc_errs, time, statistics) -> begin
(match (used_unsat_core) with
| true -> begin
(match (uc_errs) with
| FStar_Util.Inl (uu____3155) -> begin
(cb ((uc_errs), (time), (statistics)))
end
| FStar_Util.Inr (uu____3172, ek) -> begin
(cb ((FStar_Util.Inr ((([]), (ek)))), (time), (statistics)))
end)
end
| uu____3202 -> begin
(cb ((uc_errs), (time), (statistics)))
end)
end))


let mk_input : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.string = (fun theory -> (

let r = (

let uu____3222 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory)
in (FStar_All.pipe_right uu____3222 (FStar_String.concat "\n")))
in ((

let uu____3228 = (FStar_Options.log_queries ())
in (match (uu____3228) with
| true -> begin
(query_logging.write_to_log r)
end
| uu____3229 -> begin
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

let uu____3280 = (FStar_ST.read bg_scope)
in (FStar_List.append uu____3280 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
in (

let uu____3285 = (filter_theory theory)
in (match (uu____3285) with
| (theory1, used_unsat_core) -> begin
(

let cb1 = (mk_cb used_unsat_core cb)
in (

let input = (mk_input theory1)
in ((FStar_ST.write bg_scope []);
(run_job {job = (z3_job false label_messages input); callback = cb1});
)))
end))))


let ask_n_cores : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  Prims.unit = (fun filter_theory label_messages qry scope cb -> (

let theory = (

let uu____3373 = (match (scope) with
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_List.rev s)
end
| FStar_Pervasives_Native.None -> begin
((FStar_ST.write bg_scope []);
(

let uu____3388 = (FStar_ST.read fresh_scope)
in (FStar_List.rev uu____3388));
)
end)
in (FStar_List.flatten uu____3373))
in (

let theory1 = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let uu____3402 = (filter_theory theory1)
in (match (uu____3402) with
| (theory2, used_unsat_core) -> begin
(

let cb1 = (mk_cb used_unsat_core cb)
in (

let input = (mk_input theory2)
in (enqueue {job = (z3_job true label_messages input); callback = cb1})))
end)))))


let ask : (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  Prims.unit = (fun filter1 label_messages qry scope cb -> (

let uu____3486 = (

let uu____3487 = (FStar_Options.n_cores ())
in (uu____3487 = (Prims.parse_int "1")))
in (match (uu____3486) with
| true -> begin
(ask_1_core filter1 label_messages qry cb)
end
| uu____3490 -> begin
(ask_n_cores filter1 label_messages qry scope cb)
end)))




