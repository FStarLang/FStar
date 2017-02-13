
open Prims
type z3version =
| Z3V_Unknown of Prims.string
| Z3V of (Prims.int * Prims.int * Prims.int)


let uu___is_Z3V_Unknown : z3version  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Z3V_Unknown (_0) -> begin
true
end
| uu____14 -> begin
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
| uu____29 -> begin
false
end))


let __proj__Z3V__item___0 : z3version  ->  (Prims.int * Prims.int * Prims.int) = (fun projectee -> (match (projectee) with
| Z3V (_0) -> begin
_0
end))


let z3version_as_string : z3version  ->  Prims.string = (fun uu___91_48 -> (match (uu___91_48) with
| Z3V_Unknown (s) -> begin
(FStar_Util.format1 "unknown version: %s" s)
end
| Z3V (i, j, k) -> begin
(

let uu____53 = (FStar_Util.string_of_int i)
in (

let uu____54 = (FStar_Util.string_of_int j)
in (

let uu____55 = (FStar_Util.string_of_int k)
in (FStar_Util.format3 "%s.%s.%s" uu____53 uu____54 uu____55))))
end))


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known uu____65 -> (match (uu____65) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown (uu____74) -> begin
None
end
| Z3V (k1, k2, k3) -> begin
Some ((match ((k1 <> w1)) with
| true -> begin
(w1 - k1)
end
| uu____78 -> begin
(match ((k2 <> w2)) with
| true -> begin
(w2 - k2)
end
| uu____79 -> begin
(w3 - k3)
end)
end))
end)
end))


let z3v_le : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.bool = (fun known wanted -> (match ((z3v_compare known wanted)) with
| None -> begin
false
end
| Some (i) -> begin
(i >= (Prims.parse_int "0"))
end))


let _z3version : z3version Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let get_z3version : Prims.unit  ->  z3version = (fun uu____100 -> (

let prefix = "Z3 version "
in (

let uu____102 = (FStar_ST.read _z3version)
in (match (uu____102) with
| Some (version) -> begin
version
end
| None -> begin
(

let uu____108 = (

let uu____112 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc uu____112 "-version" ""))
in (match (uu____108) with
| (uu____113, out, uu____115) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| (x)::uu____118 when (FStar_Util.starts_with x prefix) -> begin
(

let x = (

let uu____121 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string uu____121))
in (

let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| uu____131 -> begin
[]
end
in (match (x) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V (((i1), (i2), (i3)))
end
| uu____135 -> begin
Z3V_Unknown (out)
end)))
end
| uu____137 -> begin
Z3V_Unknown (out)
end)
in ((FStar_ST.write _z3version (Some (out)));
out;
))
end))
end))))


let ini_params : Prims.unit  ->  Prims.string = (fun uu____145 -> (

let z3_v = (get_z3version ())
in ((

let uu____148 = (

let uu____149 = (get_z3version ())
in (z3v_le uu____149 (((Prims.parse_int "4")), ((Prims.parse_int "4")), ((Prims.parse_int "0")))))
in (match (uu____148) with
| true -> begin
(

let uu____150 = (

let uu____151 = (

let uu____152 = (z3version_as_string z3_v)
in (FStar_Util.format1 "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n" uu____152))
in FStar_Util.Failure (uu____151))
in (FStar_All.pipe_left Prims.raise uu____150))
end
| uu____153 -> begin
()
end));
(

let uu____154 = (

let uu____156 = (

let uu____158 = (

let uu____160 = (

let uu____161 = (

let uu____162 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int uu____162))
in (FStar_Util.format1 "smt.random_seed=%s" uu____161))
in (uu____160)::[])
in ("-smt2 -in auto_config=false model=true smt.relevancy=2")::uu____158)
in (

let uu____163 = (FStar_Options.z3_cliopt ())
in (FStar_List.append uu____156 uu____163)))
in (FStar_String.concat " " uu____154));
)))


type label =
Prims.string


type unsat_core =
Prims.string Prims.list Prims.option

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
| uu____186 -> begin
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
| uu____199 -> begin
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
| uu____215 -> begin
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
| uu____231 -> begin
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
| uu____245 -> begin
false
end))


let status_to_string : z3status  ->  Prims.string = (fun uu___92_248 -> (match (uu___92_248) with
| SAT (uu____249) -> begin
"sat"
end
| UNSAT (uu____251) -> begin
"unsat"
end
| UNKNOWN (uu____252) -> begin
"unknown"
end
| TIMEOUT (uu____254) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let tid : Prims.unit  ->  Prims.string = (fun uu____258 -> (

let uu____259 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right uu____259 FStar_Util.string_of_int)))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (

let uu____271 = (FStar_Options.z3_exe ())
in (

let uu____272 = (ini_params ())
in (FStar_Util.start_process id uu____271 uu____272 cond)))))

type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit; restart : Prims.unit  ->  Prims.unit}

type query_log =
{get_module_name : Prims.unit  ->  Prims.string; set_module_name : Prims.string  ->  Prims.unit; append_to_log : Prims.string  ->  Prims.unit; close_log : Prims.unit  ->  Prims.unit; log_file_name : Prims.unit  ->  Prims.string}


let query_logging : query_log = (

let log_file_opt = (FStar_Util.mk_ref None)
in (

let used_file_names = (FStar_Util.mk_ref [])
in (

let current_module_name = (FStar_Util.mk_ref None)
in (

let current_file_name = (FStar_Util.mk_ref None)
in (

let set_module_name = (fun n -> (FStar_ST.write current_module_name (Some (n))))
in (

let get_module_name = (fun uu____435 -> (

let uu____436 = (FStar_ST.read current_module_name)
in (match (uu____436) with
| None -> begin
(failwith "Module name not set")
end
| Some (n) -> begin
n
end)))
in (

let new_log_file = (fun uu____445 -> (

let uu____446 = (FStar_ST.read current_module_name)
in (match (uu____446) with
| None -> begin
(failwith "current module not set")
end
| Some (n) -> begin
(

let file_name = (

let uu____453 = (

let uu____457 = (FStar_ST.read used_file_names)
in (FStar_List.tryFind (fun uu____468 -> (match (uu____468) with
| (m, uu____472) -> begin
(n = m)
end)) uu____457))
in (match (uu____453) with
| None -> begin
((

let uu____476 = (

let uu____480 = (FStar_ST.read used_file_names)
in (((n), ((Prims.parse_int "0"))))::uu____480)
in (FStar_ST.write used_file_names uu____476));
n;
)
end
| Some (uu____496, k) -> begin
((

let uu____501 = (

let uu____505 = (FStar_ST.read used_file_names)
in (((n), ((k + (Prims.parse_int "1")))))::uu____505)
in (FStar_ST.write used_file_names uu____501));
(

let uu____521 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n uu____521));
)
end))
in (

let file_name = (FStar_Util.format1 "queries-%s.smt2" file_name)
in ((FStar_ST.write current_file_name (Some (file_name)));
(

let fh = (FStar_Util.open_file_for_writing file_name)
in ((FStar_ST.write log_file_opt (Some (fh)));
fh;
));
)))
end)))
in (

let get_log_file = (fun uu____535 -> (

let uu____536 = (FStar_ST.read log_file_opt)
in (match (uu____536) with
| None -> begin
(new_log_file ())
end
| Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____546 = (get_log_file ())
in (FStar_Util.append_to_file uu____546 str)))
in (

let close_log = (fun uu____550 -> (

let uu____551 = (FStar_ST.read log_file_opt)
in (match (uu____551) with
| None -> begin
()
end
| Some (fh) -> begin
((FStar_Util.close_file fh);
(FStar_ST.write log_file_opt None);
)
end)))
in (

let log_file_name = (fun uu____564 -> (

let uu____565 = (FStar_ST.read current_file_name)
in (match (uu____565) with
| None -> begin
(failwith "no log file")
end
| Some (n) -> begin
n
end)))
in {get_module_name = get_module_name; set_module_name = set_module_name; append_to_log = append_to_log; close_log = close_log; log_file_name = log_file_name})))))))))))


let bg_z3_proc : bgproc = (

let the_z3proc = (FStar_Util.mk_ref None)
in (

let new_proc = (

let ctr = (FStar_Util.mk_ref (~- ((Prims.parse_int "1"))))
in (fun uu____582 -> (

let uu____583 = (

let uu____584 = ((FStar_Util.incr ctr);
(

let uu____589 = (FStar_ST.read ctr)
in (FStar_All.pipe_right uu____589 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____584))
in (new_z3proc uu____583))))
in (

let z3proc = (fun uu____595 -> ((

let uu____597 = (

let uu____598 = (FStar_ST.read the_z3proc)
in (uu____598 = None))
in (match (uu____597) with
| true -> begin
(

let uu____604 = (

let uu____606 = (new_proc ())
in Some (uu____606))
in (FStar_ST.write the_z3proc uu____604))
end
| uu____610 -> begin
()
end));
(

let uu____611 = (FStar_ST.read the_z3proc)
in (FStar_Util.must uu____611));
))
in (

let x = []
in (

let grab = (fun uu____621 -> ((FStar_Util.monitor_enter x);
(z3proc ());
))
in (

let release = (fun uu____627 -> (FStar_Util.monitor_exit x))
in (

let refresh = (fun uu____632 -> (

let proc = (grab ())
in ((FStar_Util.kill_process proc);
(

let uu____636 = (

let uu____638 = (new_proc ())
in Some (uu____638))
in (FStar_ST.write the_z3proc uu____636));
(query_logging.close_log ());
(release ());
)))
in (

let restart = (fun uu____646 -> ((FStar_Util.monitor_enter ());
(query_logging.close_log ());
(FStar_ST.write the_z3proc None);
(

let uu____654 = (

let uu____656 = (new_proc ())
in Some (uu____656))
in (FStar_ST.write the_z3proc uu____654));
(FStar_Util.monitor_exit ());
))
in {grab = grab; release = release; refresh = refresh; restart = restart}))))))))


let at_log_file : Prims.unit  ->  Prims.string = (fun uu____662 -> (

let uu____663 = (FStar_Options.log_queries ())
in (match (uu____663) with
| true -> begin
(

let uu____664 = (query_logging.log_file_name ())
in (Prims.strcat "@" uu____664))
end
| uu____665 -> begin
""
end)))


let doZ3Exe' : Prims.bool  ->  Prims.string  ->  z3status = (fun fresh input -> (

let parse = (fun z3out -> (

let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (

let print_stats = (fun lines -> (

let starts_with = (fun c s -> (((FStar_String.length s) >= (Prims.parse_int "1")) && (

let uu____696 = (FStar_String.get s (Prims.parse_int "0"))
in (uu____696 = c))))
in (

let ends_with = (fun c s -> (((FStar_String.length s) >= (Prims.parse_int "1")) && (

let uu____707 = (FStar_String.get s ((FStar_String.length s) - (Prims.parse_int "1")))
in (uu____707 = c))))
in (

let last = (fun l -> (FStar_List.nth l ((FStar_List.length l) - (Prims.parse_int "1"))))
in (

let uu____720 = (FStar_Options.print_z3_statistics ())
in (match (uu____720) with
| true -> begin
(

let uu____721 = ((((FStar_List.length lines) >= (Prims.parse_int "2")) && (

let uu____725 = (FStar_List.hd lines)
in (starts_with '(' uu____725))) && (

let uu____726 = (last lines)
in (ends_with ')' uu____726)))
in (match (uu____721) with
| true -> begin
((

let uu____728 = (

let uu____729 = (

let uu____730 = (query_logging.get_module_name ())
in (FStar_Util.format1 "BEGIN-STATS %s\n" uu____730))
in (

let uu____731 = (at_log_file ())
in (Prims.strcat uu____729 uu____731)))
in (FStar_Util.print_string uu____728));
(FStar_List.iter (fun s -> (

let uu____734 = (FStar_Util.format1 "%s\n" s)
in (FStar_Util.print_string uu____734))) lines);
(FStar_Util.print_string "END-STATS\n");
)
end
| uu____735 -> begin
(failwith "Unexpected output from Z3: could not find statistics\n")
end))
end
| uu____736 -> begin
()
end))))))
in (

let unsat_core = (fun lines -> (

let parse_core = (fun s -> (

let s = (FStar_Util.trim_string s)
in (

let s = (FStar_Util.substring s (Prims.parse_int "1") ((FStar_String.length s) - (Prims.parse_int "2")))
in (match ((FStar_Util.starts_with s "error")) with
| true -> begin
None
end
| uu____762 -> begin
(

let uu____763 = (FStar_All.pipe_right (FStar_Util.split s " ") (FStar_Util.sort_with FStar_String.compare))
in (FStar_All.pipe_right uu____763 (fun _0_28 -> Some (_0_28))))
end))))
in (match (lines) with
| ("<unsat-core>")::(core)::("</unsat-core>")::rest -> begin
(

let uu____779 = (parse_core core)
in ((uu____779), (lines)))
end
| uu____785 -> begin
((None), (lines))
end)))
in (

let rec lblnegs = (fun lines succeeded -> (match (lines) with
| (lname)::("false")::rest when (FStar_Util.starts_with lname "label_") -> begin
(

let uu____805 = (lblnegs rest succeeded)
in (lname)::uu____805)
end
| (lname)::(uu____808)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest succeeded)
end
| uu____811 -> begin
((match (succeeded) with
| true -> begin
(print_stats lines)
end
| uu____814 -> begin
()
end);
[];
)
end))
in (

let unsat_core_and_lblnegs = (fun lines succeeded -> (

let uu____829 = (unsat_core lines)
in (match (uu____829) with
| (core_opt, rest) -> begin
(

let uu____848 = (lblnegs rest succeeded)
in ((core_opt), (uu____848)))
end)))
in (

let rec result = (fun x -> (match (x) with
| ("timeout")::tl -> begin
TIMEOUT ([])
end
| ("unknown")::tl -> begin
(

let uu____863 = (

let uu____865 = (unsat_core_and_lblnegs tl false)
in (Prims.snd uu____865))
in UNKNOWN (uu____863))
end
| ("sat")::tl -> begin
(

let uu____876 = (

let uu____878 = (unsat_core_and_lblnegs tl false)
in (Prims.snd uu____878))
in SAT (uu____876))
end
| ("unsat")::tl -> begin
(

let uu____889 = (

let uu____890 = (unsat_core_and_lblnegs tl true)
in (Prims.fst uu____890))
in UNSAT (uu____889))
end
| ("killed")::tl -> begin
((bg_z3_proc.restart ());
KILLED;
)
end
| (hd)::tl -> begin
((

let uu____906 = (

let uu____907 = (query_logging.get_module_name ())
in (FStar_Util.format2 "%s: Unexpected output from Z3: %s\n" uu____907 hd))
in (FStar_Errors.warn FStar_Range.dummyRange uu____906));
(result tl);
)
end
| uu____908 -> begin
(

let uu____910 = (

let uu____911 = (

let uu____912 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" uu____912))
in (FStar_Util.format1 "Unexpected output from Z3: got output lines: %s\n" uu____911))
in (FStar_All.pipe_left failwith uu____910))
end))
in (result lines))))))))
in (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (

let stdout = (match (fresh) with
| true -> begin
(

let uu____924 = (tid ())
in (

let uu____925 = (FStar_Options.z3_exe ())
in (

let uu____926 = (ini_params ())
in (FStar_Util.launch_process uu____924 uu____925 uu____926 input cond))))
end
| uu____927 -> begin
(

let proc = (bg_z3_proc.grab ())
in (

let stdout = (FStar_Util.ask_process proc input)
in ((bg_z3_proc.release ());
stdout;
)))
end)
in (parse (FStar_Util.trim_string stdout))))))


let doZ3Exe : Prims.bool  ->  Prims.string  ->  z3status = (fun fresh input -> (doZ3Exe' fresh input))


let z3_options : Prims.unit  ->  Prims.string = (fun uu____939 -> "(set-option :global-decls false)(set-option :smt.mbqi false)(set-option :auto_config false)(set-option :produce-unsat-cores true)")

type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}

type error_kind =
| Timeout
| Kill
| Default


let uu___is_Timeout : error_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Timeout -> begin
true
end
| uu____990 -> begin
false
end))


let uu___is_Kill : error_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Kill -> begin
true
end
| uu____994 -> begin
false
end))


let uu___is_Default : error_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Default -> begin
true
end
| uu____998 -> begin
false
end))


type z3job =
((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int) job


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let with_monitor = (fun m f -> ((FStar_Util.monitor_enter m);
(

let res = (f ())
in ((FStar_Util.monitor_exit m);
res;
));
))


let z3_job : Prims.bool  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int) = (fun fresh label_messages input uu____1059 -> (

let ekind = (fun uu___93_1075 -> (match (uu___93_1075) with
| TIMEOUT (uu____1076) -> begin
Timeout
end
| (SAT (_)) | (UNKNOWN (_)) -> begin
Default
end
| KILLED -> begin
Kill
end
| uu____1080 -> begin
(failwith "Impossible")
end))
in (

let start = (FStar_Util.now ())
in (

let status = (doZ3Exe fresh input)
in (

let uu____1083 = (

let uu____1086 = (FStar_Util.now ())
in (FStar_Util.time_diff start uu____1086))
in (match (uu____1083) with
| (uu____1093, elapsed_time) -> begin
(

let result = (match (status) with
| UNSAT (core) -> begin
((FStar_Util.Inl (core)), (elapsed_time))
end
| KILLED -> begin
((FStar_Util.Inr ((([]), (Kill)))), (elapsed_time))
end
| (TIMEOUT (lblnegs)) | (SAT (lblnegs)) | (UNKNOWN (lblnegs)) -> begin
((

let uu____1173 = (FStar_Options.debug_any ())
in (match (uu____1173) with
| true -> begin
(

let uu____1174 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string uu____1174))
end
| uu____1175 -> begin
()
end));
(

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (

let uu____1196 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____1220 -> (match (uu____1220) with
| (m, uu____1227, uu____1228) -> begin
((Prims.fst m) = l)
end))))
in (match (uu____1196) with
| None -> begin
[]
end
| Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end)))))
in (

let uu____1273 = (

let uu____1284 = (

let uu____1293 = (ekind status)
in ((failing_assertions), (uu____1293)))
in FStar_Util.Inr (uu____1284))
in ((uu____1273), (elapsed_time))));
)
end)
in result)
end))))))


let running : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun uu____1327 -> (

let j = (

let uu____1329 = (FStar_ST.read job_queue)
in (match (uu____1329) with
| [] -> begin
(failwith "Impossible")
end
| (hd)::tl -> begin
((FStar_ST.write job_queue tl);
hd;
)
end))
in ((FStar_Util.incr pending_jobs);
(FStar_Util.monitor_exit job_queue);
(run_job j);
(with_monitor job_queue (fun uu____1356 -> (FStar_Util.decr pending_jobs)));
(dequeue ());
)))
and dequeue : Prims.unit  ->  Prims.unit = (fun uu____1361 -> (

let uu____1362 = (FStar_ST.read running)
in if uu____1362 then begin
(

let rec aux = (fun uu____1368 -> ((FStar_Util.monitor_enter job_queue);
(

let uu____1374 = (FStar_ST.read job_queue)
in (match (uu____1374) with
| [] -> begin
((FStar_Util.monitor_exit job_queue);
(FStar_Util.sleep (Prims.parse_int "50"));
(aux ());
)
end
| uu____1385 -> begin
(dequeue' ())
end));
))
in (aux ()))
end else begin
()
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (

let uu____1388 = (j.job ())
in (FStar_All.pipe_left j.callback uu____1388)))


let init : Prims.unit  ->  Prims.unit = (fun uu____1415 -> ((FStar_ST.write running true);
(

let n_cores = (FStar_Options.n_cores ())
in (match ((n_cores > (Prims.parse_int "1"))) with
| true -> begin
(

let rec aux = (fun n -> (match ((n = (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____1424 -> begin
((FStar_Util.spawn dequeue);
(aux (n - (Prims.parse_int "1")));
)
end))
in (aux n_cores))
end
| uu____1426 -> begin
()
end));
))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> (match ((not (fresh))) with
| true -> begin
(run_job j)
end
| uu____1433 -> begin
((FStar_Util.monitor_enter job_queue);
(

let uu____1440 = (

let uu____1442 = (FStar_ST.read job_queue)
in (FStar_List.append uu____1442 ((j)::[])))
in (FStar_ST.write job_queue uu____1440));
(FStar_Util.monitor_pulse job_queue);
(FStar_Util.monitor_exit job_queue);
)
end))


let finish : Prims.unit  ->  Prims.unit = (fun uu____1461 -> (

let rec aux = (fun uu____1465 -> (

let uu____1466 = (with_monitor job_queue (fun uu____1475 -> (

let uu____1476 = (FStar_ST.read pending_jobs)
in (

let uu____1479 = (

let uu____1480 = (FStar_ST.read job_queue)
in (FStar_List.length uu____1480))
in ((uu____1476), (uu____1479))))))
in (match (uu____1466) with
| (n, m) -> begin
(match (((n + m) = (Prims.parse_int "0"))) with
| true -> begin
((FStar_ST.write running false);
(

let uu____1495 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____1495 Prims.ignore));
)
end
| uu____1499 -> begin
((FStar_Util.sleep (Prims.parse_int "500"));
(aux ());
)
end)
end)))
in (aux ())))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : Prims.string  ->  Prims.unit = (fun msg -> ((

let uu____1521 = (

let uu____1524 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::uu____1524)
in (FStar_ST.write fresh_scope uu____1521));
(

let uu____1536 = (

let uu____1538 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) uu____1538))
in (FStar_ST.write bg_scope uu____1536));
))


let pop : Prims.string  ->  Prims.unit = (fun msg -> ((

let uu____1550 = (

let uu____1553 = (FStar_ST.read fresh_scope)
in (FStar_List.tl uu____1553))
in (FStar_ST.write fresh_scope uu____1550));
(

let uu____1565 = (

let uu____1567 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Pop)::(FStar_SMTEncoding_Term.Caption (msg))::[]) uu____1567))
in (FStar_ST.write bg_scope uu____1565));
))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___94_1582 -> (match (uu___94_1582) with
| (FStar_SMTEncoding_Term.Push) | (FStar_SMTEncoding_Term.Pop) -> begin
(failwith "Unexpected push/pop")
end
| uu____1583 -> begin
()
end))));
(

let uu____1585 = (FStar_ST.read fresh_scope)
in (match (uu____1585) with
| (hd)::tl -> begin
(FStar_ST.write fresh_scope (((FStar_List.append hd decls))::tl))
end
| uu____1603 -> begin
(failwith "Impossible")
end));
(

let uu____1606 = (

let uu____1608 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) uu____1608))
in (FStar_ST.write bg_scope uu____1606));
))


let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> (match (fresh) with
| true -> begin
((FStar_ST.write bg_scope []);
(

let uu____1625 = (

let uu____1628 = (FStar_ST.read fresh_scope)
in (FStar_List.rev uu____1628))
in (FStar_All.pipe_right uu____1625 FStar_List.flatten));
)
end
| uu____1639 -> begin
(

let bg = (FStar_ST.read bg_scope)
in ((FStar_ST.write bg_scope []);
(FStar_List.rev bg);
))
end))


let refresh : Prims.unit  ->  Prims.unit = (fun uu____1651 -> ((

let uu____1653 = (

let uu____1654 = (FStar_Options.n_cores ())
in (uu____1654 < (Prims.parse_int "2")))
in (match (uu____1653) with
| true -> begin
(bg_z3_proc.refresh ())
end
| uu____1655 -> begin
()
end));
(

let theory = (bgtheory true)
in (FStar_ST.write bg_scope (FStar_List.rev theory)));
))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> ((pop msg);
(refresh ());
))


let commit_mark = (fun msg -> (

let uu____1675 = (FStar_ST.read fresh_scope)
in (match (uu____1675) with
| (hd)::(s)::tl -> begin
(FStar_ST.write fresh_scope (((FStar_List.append hd s))::tl))
end
| uu____1696 -> begin
(failwith "Impossible")
end)))


let ask : unsat_core  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int)  ->  Prims.unit)  ->  Prims.unit = (fun core label_messages qry cb -> (

let fresh = (

let uu____1743 = (FStar_Options.n_cores ())
in (uu____1743 > (Prims.parse_int "1")))
in (

let filter_assertions = (fun theory -> (match (core) with
| None -> begin
((theory), (false))
end
| Some (core) -> begin
(

let uu____1761 = (FStar_List.fold_right (fun d uu____1771 -> (match (uu____1771) with
| (theory, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (uu____1789, uu____1790, Some (name)) -> begin
(match ((FStar_List.contains name core)) with
| true -> begin
(((d)::theory), ((n_retained + (Prims.parse_int "1"))), (n_pruned))
end
| uu____1798 -> begin
(match ((FStar_Util.starts_with name "@")) with
| true -> begin
(((d)::theory), (n_retained), (n_pruned))
end
| uu____1804 -> begin
((theory), (n_retained), ((n_pruned + (Prims.parse_int "1"))))
end)
end)
end
| uu____1806 -> begin
(((d)::theory), (n_retained), (n_pruned))
end)
end)) theory (([]), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (match (uu____1761) with
| (theory', n_retained, n_pruned) -> begin
(

let missed_assertions = (fun th core -> (

let missed = (

let uu____1829 = (FStar_All.pipe_right core (FStar_List.filter (fun nm -> (

let uu____1834 = (FStar_All.pipe_right th (FStar_Util.for_some (fun uu___95_1836 -> (match (uu___95_1836) with
| FStar_SMTEncoding_Term.Assume (uu____1837, uu____1838, Some (nm')) -> begin
(nm = nm')
end
| uu____1841 -> begin
false
end))))
in (FStar_All.pipe_right uu____1834 Prims.op_Negation)))))
in (FStar_All.pipe_right uu____1829 (FStar_String.concat ", ")))
in (

let included = (

let uu____1844 = (FStar_All.pipe_right th (FStar_List.collect (fun uu___96_1848 -> (match (uu___96_1848) with
| FStar_SMTEncoding_Term.Assume (uu____1850, uu____1851, Some (nm)) -> begin
(nm)::[]
end
| uu____1854 -> begin
[]
end))))
in (FStar_All.pipe_right uu____1844 (FStar_String.concat ", ")))
in (FStar_Util.format2 "missed={%s}; included={%s}" missed included))))
in ((

let uu____1857 = ((FStar_Options.hint_info ()) && (FStar_Options.debug_any ()))
in (match (uu____1857) with
| true -> begin
(

let n = (FStar_List.length core)
in (

let missed = (match ((n <> n_retained)) with
| true -> begin
(missed_assertions theory' core)
end
| uu____1863 -> begin
""
end)
in (

let uu____1864 = (FStar_Util.string_of_int n_retained)
in (

let uu____1865 = (match ((n <> n_retained)) with
| true -> begin
(

let uu____1868 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 " (expected %s (%s); replay may be inaccurate)" uu____1868 missed))
end
| uu____1872 -> begin
""
end)
in (

let uu____1873 = (FStar_Util.string_of_int n_pruned)
in (FStar_Util.print3 "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n" uu____1864 uu____1865 uu____1873))))))
end
| uu____1874 -> begin
()
end));
(

let uu____1875 = (

let uu____1877 = (

let uu____1879 = (

let uu____1880 = (

let uu____1881 = (FStar_All.pipe_right core (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " uu____1881))
in FStar_SMTEncoding_Term.Caption (uu____1880))
in (uu____1879)::[])
in (FStar_List.append theory' uu____1877))
in ((uu____1875), (true)));
))
end))
end))
in (

let theory = (bgtheory fresh)
in (

let theory = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let uu____1888 = (filter_assertions theory)
in (match (uu____1888) with
| (theory, used_unsat_core) -> begin
(

let cb = (fun uu____1905 -> (match (uu____1905) with
| (uc_errs, time) -> begin
(match (used_unsat_core) with
| true -> begin
(match (uc_errs) with
| FStar_Util.Inl (uu____1922) -> begin
(cb ((uc_errs), (time)))
end
| FStar_Util.Inr (uu____1929, ek) -> begin
(cb ((FStar_Util.Inr ((([]), (ek)))), (time)))
end)
end
| uu____1942 -> begin
(cb ((uc_errs), (time)))
end)
end))
in (

let input = (

let uu____1948 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory)
in (FStar_All.pipe_right uu____1948 (FStar_String.concat "\n")))
in ((

let uu____1952 = (FStar_Options.log_queries ())
in (match (uu____1952) with
| true -> begin
(query_logging.append_to_log input)
end
| uu____1953 -> begin
()
end));
(enqueue fresh {job = (z3_job fresh label_messages input); callback = cb});
)))
end)))))))




