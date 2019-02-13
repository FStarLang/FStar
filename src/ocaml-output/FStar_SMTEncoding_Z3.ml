
open Prims
open FStar_Pervasives

let _z3hash_checked : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let _z3hash_expected : Prims.string = "1f29cebd4df6"


let _z3url : Prims.string = "https://github.com/FStarLang/binaries/tree/master/z3-tested"


let parse_z3_version_lines : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun out -> (match ((FStar_Util.splitlines out)) with
| (x)::uu____38 -> begin
(

let trimmed = (FStar_Util.trim_string x)
in (

let parts = (FStar_Util.split trimmed " ")
in (

let rec aux = (fun uu___125_62 -> (match (uu___125_62) with
| (hash)::[] -> begin
(

let n1 = (Prims.min (FStar_String.strlen _z3hash_expected) (FStar_String.strlen hash))
in (

let hash_prefix = (FStar_String.substring hash (Prims.parse_int "0") n1)
in (match ((Prims.op_Equality hash_prefix _z3hash_expected)) with
| true -> begin
((

let uu____84 = (FStar_Options.debug_any ())
in (match (uu____84) with
| true -> begin
(

let msg = (FStar_Util.format1 "Successfully found expected Z3 commit hash %s\n" hash)
in (FStar_Util.print_string msg))
end
| uu____90 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| uu____93 -> begin
(

let msg = (FStar_Util.format2 "Expected Z3 commit hash \"%s\", got \"%s\"" _z3hash_expected trimmed)
in FStar_Pervasives_Native.Some (msg))
end)))
end
| (uu____99)::q -> begin
(aux q)
end
| uu____106 -> begin
FStar_Pervasives_Native.Some ("No Z3 commit hash found")
end))
in (aux parts))))
end
| uu____112 -> begin
FStar_Pervasives_Native.Some ("No Z3 version string found")
end))


let z3hash_warning_message : unit  ->  (FStar_Errors.raw_error * Prims.string) FStar_Pervasives_Native.option = (fun uu____130 -> (

let run_proc_result = (FStar_All.try_with (fun uu___131_140 -> (match (()) with
| () -> begin
(

let uu____144 = (

let uu____146 = (FStar_Options.z3_exe ())
in (FStar_Util.run_process "z3_version" uu____146 (("-version")::[]) FStar_Pervasives_Native.None))
in FStar_Pervasives_Native.Some (uu____144))
end)) (fun uu___130_155 -> FStar_Pervasives_Native.None))
in (match (run_proc_result) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((FStar_Errors.Error_Z3InvocationError), ("Could not run Z3")))
end
| FStar_Pervasives_Native.Some (out) -> begin
(

let uu____178 = (parse_z3_version_lines out)
in (match (uu____178) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (msg) -> begin
FStar_Pervasives_Native.Some (((FStar_Errors.Warning_Z3InvocationWarning), (msg)))
end))
end)))


let check_z3hash : unit  ->  unit = (fun uu____209 -> (

let uu____210 = (

let uu____212 = (FStar_ST.op_Bang _z3hash_checked)
in (not (uu____212)))
in (match (uu____210) with
| true -> begin
((FStar_ST.op_Colon_Equals _z3hash_checked true);
(

let uu____259 = (z3hash_warning_message ())
in (match (uu____259) with
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
| uu____287 -> begin
()
end)))


let ini_params : unit  ->  Prims.string Prims.list = (fun uu____297 -> ((check_z3hash ());
(

let uu____299 = (

let uu____303 = (

let uu____307 = (

let uu____311 = (

let uu____313 = (

let uu____315 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int uu____315))
in (FStar_Util.format1 "smt.random_seed=%s" uu____313))
in (uu____311)::[])
in ("-in")::uu____307)
in ("-smt2")::uu____303)
in (

let uu____324 = (FStar_Options.z3_cliopt ())
in (FStar_List.append uu____299 uu____324)));
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
| uu____388 -> begin
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
| uu____415 -> begin
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
| uu____463 -> begin
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
| uu____511 -> begin
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
| uu____551 -> begin
false
end))


type z3statistics =
Prims.string FStar_Util.smap


let status_tag : z3status  ->  Prims.string = (fun uu___126_562 -> (match (uu___126_562) with
| SAT (uu____564) -> begin
"sat"
end
| UNSAT (uu____573) -> begin
"unsat"
end
| UNKNOWN (uu____575) -> begin
"unknown"
end
| TIMEOUT (uu____584) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let status_string_and_errors : z3status  ->  (Prims.string * FStar_SMTEncoding_Term.error_labels) = (fun s -> (match (s) with
| KILLED -> begin
(((status_tag s)), ([]))
end
| UNSAT (uu____611) -> begin
(((status_tag s)), ([]))
end
| SAT (errs, msg) -> begin
(

let uu____621 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____621), (errs)))
end
| UNKNOWN (errs, msg) -> begin
(

let uu____640 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____640), (errs)))
end
| TIMEOUT (errs, msg) -> begin
(

let uu____659 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.strcat " because " msg1)
end))
in ((uu____659), (errs)))
end))


let tid : unit  ->  Prims.string = (fun uu____676 -> (

let uu____677 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right uu____677 FStar_Util.string_of_int)))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id1 -> (

let uu____689 = (FStar_Options.z3_exe ())
in (

let uu____691 = (ini_params ())
in (FStar_Util.start_process id1 uu____689 uu____691 (fun s -> (Prims.op_Equality s "Done!"))))))


let new_z3proc_with_id : unit  ->  FStar_Util.proc = (

let ctr = (FStar_Util.mk_ref (~- ((Prims.parse_int "1"))))
in (fun uu____711 -> (

let uu____712 = (

let uu____714 = ((FStar_Util.incr ctr);
(

let uu____750 = (FStar_ST.op_Bang ctr)
in (FStar_All.pipe_right uu____750 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____714))
in (new_z3proc uu____712))))

type bgproc =
{ask : Prims.string  ->  Prims.string; refresh : unit  ->  unit; restart : unit  ->  unit}


let __proj__Mkbgproc__item__ask : bgproc  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart} -> begin
ask
end))


let __proj__Mkbgproc__item__refresh : bgproc  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart} -> begin
refresh
end))


let __proj__Mkbgproc__item__restart : bgproc  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart} -> begin
restart
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

let get_module_name = (fun uu____1266 -> (

let uu____1267 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1267) with
| FStar_Pervasives_Native.None -> begin
(failwith "Module name not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in (

let next_file_name = (fun uu____1331 -> (

let n1 = (get_module_name ())
in (

let file_name = (

let uu____1336 = (

let uu____1345 = (FStar_ST.op_Bang used_file_names)
in (FStar_List.tryFind (fun uu____1420 -> (match (uu____1420) with
| (m, uu____1429) -> begin
(Prims.op_Equality n1 m)
end)) uu____1345))
in (match (uu____1336) with
| FStar_Pervasives_Native.None -> begin
((

let uu____1443 = (

let uu____1452 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((Prims.parse_int "0"))))::uu____1452)
in (FStar_ST.op_Colon_Equals used_file_names uu____1443));
n1;
)
end
| FStar_Pervasives_Native.Some (uu____1584, k) -> begin
((

let uu____1597 = (

let uu____1606 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((k + (Prims.parse_int "1")))))::uu____1606)
in (FStar_ST.op_Colon_Equals used_file_names uu____1597));
(

let uu____1738 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n1 uu____1738));
)
end))
in (FStar_Util.format1 "queries-%s.smt2" file_name))))
in (

let new_log_file = (fun uu____1753 -> (

let file_name = (next_file_name ())
in ((FStar_ST.op_Colon_Equals current_file_name (FStar_Pervasives_Native.Some (file_name)));
(

let fh = (FStar_Util.open_file_for_writing file_name)
in ((FStar_ST.op_Colon_Equals log_file_opt (FStar_Pervasives_Native.Some (((fh), (file_name)))));
((fh), (file_name));
));
)))
in (

let get_log_file = (fun uu____1879 -> (

let uu____1880 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____1880) with
| FStar_Pervasives_Native.None -> begin
(new_log_file ())
end
| FStar_Pervasives_Native.Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____1973 = (get_log_file ())
in (match (uu____1973) with
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

let write_to_log = (fun fresh str -> (

let uu____2013 = (fresh || (

let uu____2016 = (FStar_Options.n_cores ())
in (uu____2016 > (Prims.parse_int "1"))))
in (match (uu____2013) with
| true -> begin
(write_to_new_log str)
end
| uu____2021 -> begin
(append_to_log str)
end)))
in (

let close_log = (fun uu____2028 -> (

let uu____2029 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____2029) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (fh, uu____2098) -> begin
((FStar_Util.close_file fh);
(FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None);
)
end)))
in (

let log_file_name = (fun uu____2173 -> (

let uu____2174 = (FStar_ST.op_Bang current_file_name)
in (match (uu____2174) with
| FStar_Pervasives_Native.None -> begin
(failwith "no log file")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in {get_module_name = get_module_name; set_module_name = set_module_name; write_to_log = write_to_log; close_log = close_log})))))))))))))))


let bg_z3_proc : bgproc FStar_ST.ref = (

let the_z3proc = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let z3proc = (fun uu____2258 -> ((

let uu____2260 = (

let uu____2262 = (FStar_ST.op_Bang the_z3proc)
in (Prims.op_Equality uu____2262 FStar_Pervasives_Native.None))
in (match (uu____2260) with
| true -> begin
(

let uu____2313 = (

let uu____2316 = (new_z3proc_with_id ())
in FStar_Pervasives_Native.Some (uu____2316))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2313))
end
| uu____2362 -> begin
()
end));
(

let uu____2364 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.must uu____2364));
))
in (

let x = []
in (

let ask = (fun input -> (

let kill_handler = (fun uu____2430 -> "\nkilled\n")
in (

let uu____2432 = (z3proc ())
in (FStar_Util.ask_process uu____2432 input kill_handler))))
in (

let refresh = (fun uu____2438 -> ((

let uu____2440 = (z3proc ())
in (FStar_Util.kill_process uu____2440));
(

let uu____2442 = (

let uu____2445 = (new_z3proc_with_id ())
in FStar_Pervasives_Native.Some (uu____2445))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2442));
(query_logging.close_log ());
))
in (

let restart = (fun uu____2496 -> ((query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(

let uu____2544 = (

let uu____2547 = (new_z3proc_with_id ())
in FStar_Pervasives_Native.Some (uu____2547))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2544));
))
in (FStar_Util.mk_ref {ask = (FStar_Util.with_monitor x ask); refresh = (FStar_Util.with_monitor x refresh); restart = (FStar_Util.with_monitor x restart)})))))))


let set_bg_z3_proc : bgproc  ->  unit = (fun bgp -> (FStar_ST.op_Colon_Equals bg_z3_proc bgp))


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
| uu____2893 -> begin
(

let uu____2895 = (until tag lines2)
in (FStar_Util.map_opt uu____2895 (fun uu____2931 -> (match (uu____2931) with
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

let uu____3038 = (until (start_tag tag) lines1)
in (match (uu____3038) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (lines1))
end
| FStar_Pervasives_Native.Some (prefix1, suffix) -> begin
(

let uu____3108 = (until (end_tag tag) suffix)
in (match (uu____3108) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Parse error: " (Prims.strcat (end_tag tag) " not found")))
end
| FStar_Pervasives_Native.Some (section, suffix1) -> begin
((FStar_Pervasives_Native.Some (section)), ((FStar_List.append prefix1 suffix1)))
end))
end)))
in (

let uu____3193 = (find_section "result" lines)
in (match (uu____3193) with
| (result_opt, lines1) -> begin
(

let result = (FStar_Util.must result_opt)
in (

let uu____3232 = (find_section "reason-unknown" lines1)
in (match (uu____3232) with
| (reason_unknown, lines2) -> begin
(

let uu____3264 = (find_section "unsat-core" lines2)
in (match (uu____3264) with
| (unsat_core, lines3) -> begin
(

let uu____3296 = (find_section "statistics" lines3)
in (match (uu____3296) with
| (statistics, lines4) -> begin
(

let uu____3328 = (find_section "labels" lines4)
in (match (uu____3328) with
| (labels, lines5) -> begin
(

let remaining = (

let uu____3364 = (until "Done!" lines5)
in (match (uu____3364) with
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
| uu____3418 -> begin
(

let msg = (FStar_Util.format2 "%sUnexpected output from Z3: %s\n" (match (log_file) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (f) -> begin
(Prims.strcat f ": ")
end) (FStar_String.concat "\n" remaining))
in (FStar_Errors.log_issue r ((FStar_Errors.Warning_UnexpectedZ3Output), (msg))))
end);
(

let uu____3434 = (FStar_Util.must result_opt)
in {smt_result = uu____3434; smt_reason_unknown = reason_unknown; smt_unsat_core = unsat_core; smt_statistics = statistics; smt_labels = labels});
))
end))
end))
end))
end)))
end)))))))


let doZ3Exe : Prims.string FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  Prims.bool  ->  Prims.string  ->  FStar_SMTEncoding_Term.error_labels  ->  (z3status * z3statistics) = (fun log_file r fresh input label_messages -> (

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
| uu____3527 -> begin
(

let uu____3529 = (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_Util.sort_with FStar_String.compare))
in FStar_Pervasives_Native.Some (uu____3529))
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

let uu____3574 = (lblnegs rest)
in (lname)::uu____3574)
end
| (lname)::(uu____3580)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest)
end
| uu____3590 -> begin
[]
end))
in (

let lblnegs1 = (lblnegs lines1)
in (FStar_All.pipe_right lblnegs1 (FStar_List.collect (fun l -> (

let uu____3614 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____3654 -> (match (uu____3654) with
| (m, uu____3664, uu____3665) -> begin
(

let uu____3668 = (FStar_SMTEncoding_Term.fv_name m)
in (Prims.op_Equality uu____3668 l))
end))))
in (match (uu____3614) with
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
| uu____3765 -> begin
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
| uu____3794 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| uu____3797 -> begin
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
| uu____3826 -> begin
ru
end))))
in (

let status = ((

let uu____3830 = (FStar_Options.debug_any ())
in (match (uu____3830) with
| true -> begin
(

let uu____3833 = (FStar_Util.format1 "Z3 says: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (FStar_All.pipe_left FStar_Util.print_string uu____3833))
end
| uu____3838 -> begin
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

let uu____3865 = (

let uu____3870 = (FStar_ST.op_Bang bg_z3_proc)
in uu____3870.restart)
in (uu____3865 ()));
KILLED;
)
end
| uu____3890 -> begin
(

let uu____3891 = (FStar_Util.format1 "Unexpected output from Z3: got output result: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (failwith uu____3891))
end);
)
in ((status), (statistics))))))))))
in (

let stdout1 = (match (fresh) with
| true -> begin
(

let proc = (new_z3proc_with_id ())
in (

let kill_handler = (fun uu____3906 -> "\nkilled\n")
in (

let out = (FStar_Util.ask_process proc input kill_handler)
in ((FStar_Util.kill_process proc);
out;
))))
end
| uu____3911 -> begin
(

let uu____3913 = (

let uu____3920 = (FStar_ST.op_Bang bg_z3_proc)
in uu____3920.ask)
in (uu____3913 input))
end)
in (parse (FStar_Util.trim_string stdout1)))))


let z3_options : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n(set-option :model true)\n(set-option :smt.case_split 3)\n(set-option :smt.relevancy 2)\n")


let set_z3_options : Prims.string  ->  unit = (fun opts -> (FStar_ST.op_Colon_Equals z3_options opts))

type 'a job_t =
{job : unit  ->  'a; callback : 'a  ->  unit}


let __proj__Mkjob_t__item__job : 'a . 'a job_t  ->  unit  ->  'a = (fun projectee -> (match (projectee) with
| {job = job; callback = callback} -> begin
job
end))


let __proj__Mkjob_t__item__callback : 'a . 'a job_t  ->  'a  ->  unit = (fun projectee -> (match (projectee) with
| {job = job; callback = callback} -> begin
callback
end))

type z3result =
{z3result_status : z3status; z3result_time : Prims.int; z3result_statistics : z3statistics; z3result_query_hash : Prims.string FStar_Pervasives_Native.option; z3result_log_file : Prims.string FStar_Pervasives_Native.option}


let __proj__Mkz3result__item__z3result_status : z3result  ->  z3status = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_log_file = z3result_log_file} -> begin
z3result_status
end))


let __proj__Mkz3result__item__z3result_time : z3result  ->  Prims.int = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_log_file = z3result_log_file} -> begin
z3result_time
end))


let __proj__Mkz3result__item__z3result_statistics : z3result  ->  z3statistics = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_log_file = z3result_log_file} -> begin
z3result_statistics
end))


let __proj__Mkz3result__item__z3result_query_hash : z3result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_log_file = z3result_log_file} -> begin
z3result_query_hash
end))


let __proj__Mkz3result__item__z3result_log_file : z3result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_log_file = z3result_log_file} -> begin
z3result_log_file
end))


type z3job =
z3result job_t


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let z3_job : Prims.string FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  Prims.bool  ->  FStar_SMTEncoding_Term.error_labels  ->  Prims.string  ->  Prims.string FStar_Pervasives_Native.option  ->  unit  ->  z3result = (fun log_file r fresh label_messages input qhash uu____4280 -> (

let start = (FStar_Util.now ())
in (

let uu____4290 = (FStar_All.try_with (fun uu___133_4300 -> (match (()) with
| () -> begin
(doZ3Exe log_file r fresh input label_messages)
end)) (fun uu___132_4307 -> if (

let uu____4312 = (FStar_Options.trace_error ())
in (not (uu____4312))) then begin
(Obj.magic ((Obj.repr ((

let uu____4315 = (

let uu____4320 = (FStar_ST.op_Bang bg_z3_proc)
in uu____4320.refresh)
in (uu____4315 ()));
(FStar_Exn.raise uu___132_4307);
))))
end else begin
(Obj.magic ((Obj.repr (failwith "unreachable"))))
end))
in (match (uu____4290) with
| (status, statistics) -> begin
(

let uu____4346 = (

let uu____4352 = (FStar_Util.now ())
in (FStar_Util.time_diff start uu____4352))
in (match (uu____4346) with
| (uu____4353, elapsed_time) -> begin
{z3result_status = status; z3result_time = elapsed_time; z3result_statistics = statistics; z3result_query_hash = qhash; z3result_log_file = log_file}
end))
end))))


let running : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let rec dequeue' : unit  ->  unit = (fun uu____4387 -> (

let j = (

let uu____4389 = (FStar_ST.op_Bang job_queue)
in (match (uu____4389) with
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
(FStar_Util.with_monitor job_queue (fun uu____4457 -> (FStar_Util.decr pending_jobs)) ());
(dequeue ());
)))
and dequeue : unit  ->  unit = (fun uu____4459 -> (

let uu____4460 = (FStar_ST.op_Bang running)
in if uu____4460 then begin
(

let rec aux = (fun uu____4488 -> ((FStar_Util.monitor_enter job_queue);
(

let uu____4494 = (FStar_ST.op_Bang job_queue)
in (match (uu____4494) with
| [] -> begin
((FStar_Util.monitor_exit job_queue);
(FStar_Util.sleep (Prims.parse_int "50"));
(aux ());
)
end
| uu____4527 -> begin
(dequeue' ())
end));
))
in (aux ()))
end else begin
()
end))
and run_job : z3job  ->  unit = (fun j -> (

let uu____4531 = (j.job ())
in (FStar_All.pipe_left j.callback uu____4531)))


let init : unit  ->  unit = (fun uu____4537 -> ((FStar_ST.op_Colon_Equals running true);
(

let n_cores1 = (FStar_Options.n_cores ())
in (match ((n_cores1 > (Prims.parse_int "1"))) with
| true -> begin
(

let rec aux = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____4576 -> begin
((FStar_Util.spawn dequeue);
(aux (n1 - (Prims.parse_int "1")));
)
end))
in (aux n_cores1))
end
| uu____4580 -> begin
()
end));
))


let enqueue : z3job  ->  unit = (fun j -> (FStar_Util.with_monitor job_queue (fun uu____4594 -> ((

let uu____4596 = (

let uu____4599 = (FStar_ST.op_Bang job_queue)
in (FStar_List.append uu____4599 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue uu____4596));
(FStar_Util.monitor_pulse job_queue);
)) ()))


let finish : unit  ->  unit = (fun uu____4657 -> (

let rec aux = (fun uu____4663 -> (

let uu____4664 = (FStar_Util.with_monitor job_queue (fun uu____4682 -> (

let uu____4683 = (FStar_ST.op_Bang pending_jobs)
in (

let uu____4706 = (

let uu____4707 = (FStar_ST.op_Bang job_queue)
in (FStar_List.length uu____4707))
in ((uu____4683), (uu____4706))))) ())
in (match (uu____4664) with
| (n1, m) -> begin
(match ((Prims.op_Equality (n1 + m) (Prims.parse_int "0"))) with
| true -> begin
(FStar_ST.op_Colon_Equals running false)
end
| uu____4771 -> begin
((FStar_Util.sleep (Prims.parse_int "500"));
(aux ());
)
end)
end)))
in (aux ())))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let fresh_scope : scope_t FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let mk_fresh_scope : unit  ->  scope_t = (fun uu____4802 -> (FStar_ST.op_Bang fresh_scope))


let flatten_fresh_scope : unit  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun uu____4829 -> (

let uu____4830 = (

let uu____4835 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____4835))
in (FStar_List.flatten uu____4830)))


let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : Prims.string  ->  unit = (fun msg -> (FStar_Util.atomically (fun uu____4890 -> ((

let uu____4892 = (

let uu____4893 = (FStar_ST.op_Bang fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::uu____4893)
in (FStar_ST.op_Colon_Equals fresh_scope uu____4892));
(

let uu____4938 = (

let uu____4941 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____4941 ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____4938));
))))


let pop : Prims.string  ->  unit = (fun msg -> (FStar_Util.atomically (fun uu____5001 -> ((

let uu____5003 = (

let uu____5004 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.tl uu____5004))
in (FStar_ST.op_Colon_Equals fresh_scope uu____5003));
(

let uu____5049 = (

let uu____5052 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____5052 ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____5049));
))))


let snapshot : Prims.string  ->  (Prims.int * unit) = (fun msg -> (FStar_Common.snapshot push fresh_scope msg))


let rollback : Prims.string  ->  Prims.int FStar_Pervasives_Native.option  ->  unit = (fun msg depth -> (FStar_Common.rollback (fun uu____5139 -> (pop msg)) fresh_scope depth))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___127_5154 -> (match (uu___127_5154) with
| FStar_SMTEncoding_Term.Push -> begin
(failwith "Unexpected push/pop")
end
| FStar_SMTEncoding_Term.Pop -> begin
(failwith "Unexpected push/pop")
end
| uu____5157 -> begin
()
end))));
(

let uu____5159 = (FStar_ST.op_Bang fresh_scope)
in (match (uu____5159) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd1 decls))::tl1))
end
| uu____5210 -> begin
(failwith "Impossible")
end));
(

let uu____5212 = (

let uu____5215 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____5215 decls))
in (FStar_ST.op_Colon_Equals bg_scope uu____5212));
))


let refresh : unit  ->  unit = (fun uu____5269 -> ((

let uu____5271 = (

let uu____5273 = (FStar_Options.n_cores ())
in (uu____5273 < (Prims.parse_int "2")))
in (match (uu____5271) with
| true -> begin
(

let uu____5277 = (

let uu____5282 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5282.refresh)
in (uu____5277 ()))
end
| uu____5302 -> begin
()
end));
(

let uu____5304 = (flatten_fresh_scope ())
in (FStar_ST.op_Colon_Equals bg_scope uu____5304));
))


let context_profile : FStar_SMTEncoding_Term.decls_t  ->  unit = (fun theory -> (

let uu____5336 = (FStar_List.fold_left (fun uu____5369 d -> (match (uu____5369) with
| (out, _total) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Module (name, decls) -> begin
(

let decls1 = (FStar_List.filter (fun uu___128_5438 -> (match (uu___128_5438) with
| FStar_SMTEncoding_Term.Assume (uu____5440) -> begin
true
end
| uu____5442 -> begin
false
end)) decls)
in (

let n1 = (FStar_List.length decls1)
in (((((name), (n1)))::out), ((n1 + _total)))))
end
| uu____5469 -> begin
((out), (_total))
end)
end)) (([]), ((Prims.parse_int "0"))) theory)
in (match (uu____5336) with
| (modules, total_decls) -> begin
(

let modules1 = (FStar_List.sortWith (fun uu____5531 uu____5532 -> (match (((uu____5531), (uu____5532))) with
| ((uu____5558, n1), (uu____5560, m)) -> begin
(m - n1)
end)) modules)
in ((match ((Prims.op_disEquality modules1 [])) with
| true -> begin
(

let uu____5598 = (FStar_Util.string_of_int total_decls)
in (FStar_Util.print1 "Z3 Proof Stats: context_profile with %s assertions\n" uu____5598))
end
| uu____5601 -> begin
()
end);
(FStar_List.iter (fun uu____5613 -> (match (uu____5613) with
| (m, n1) -> begin
(match ((Prims.op_disEquality n1 (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5629 = (FStar_Util.string_of_int n1)
in (FStar_Util.print2 "Z3 Proof Stats: %s produced %s SMT decls\n" m uu____5629))
end
| uu____5632 -> begin
()
end)
end)) modules1);
))
end)))


let mk_input : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (Prims.string * Prims.string FStar_Pervasives_Native.option * Prims.string FStar_Pervasives_Native.option) = (fun fresh theory -> (

let options = (FStar_ST.op_Bang z3_options)
in ((

let uu____5688 = (FStar_Options.print_z3_statistics ())
in (match (uu____5688) with
| true -> begin
(context_profile theory)
end
| uu____5691 -> begin
()
end));
(

let uu____5693 = (

let uu____5702 = ((FStar_Options.record_hints ()) || ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())))
in (match (uu____5702) with
| true -> begin
(

let uu____5713 = (

let uu____5724 = (FStar_All.pipe_right theory (FStar_Util.prefix_until (fun uu___129_5752 -> (match (uu___129_5752) with
| FStar_SMTEncoding_Term.CheckSat -> begin
true
end
| uu____5755 -> begin
false
end))))
in (FStar_All.pipe_right uu____5724 FStar_Option.get))
in (match (uu____5713) with
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

let uu____5838 = (FStar_Options.keep_query_captions ())
in (match (uu____5838) with
| true -> begin
(

let uu____5842 = (FStar_All.pipe_right prefix1 (FStar_List.map (FStar_SMTEncoding_Term.declToSmt_no_caps options)))
in (FStar_All.pipe_right uu____5842 (FStar_String.concat "\n")))
end
| uu____5857 -> begin
ps
end))
in (

let uu____5859 = (

let uu____5863 = (FStar_Util.digest_of_string hs)
in FStar_Pervasives_Native.Some (uu____5863))
in (((Prims.strcat ps (Prims.strcat "\n" ss))), (uu____5859))))))))))
end))
end
| uu____5871 -> begin
(

let uu____5873 = (

let uu____5875 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory)
in (FStar_All.pipe_right uu____5875 (FStar_String.concat "\n")))
in ((uu____5873), (FStar_Pervasives_Native.None)))
end))
in (match (uu____5693) with
| (r, hash) -> begin
(

let log_file_name = (

let uu____5917 = (FStar_Options.log_queries ())
in (match (uu____5917) with
| true -> begin
(

let uu____5923 = (query_logging.write_to_log fresh r)
in FStar_Pervasives_Native.Some (uu____5923))
end
| uu____5926 -> begin
FStar_Pervasives_Native.None
end))
in ((r), (hash), (log_file_name)))
end));
)))


type cb =
z3result  ->  unit


let cache_hit : Prims.string FStar_Pervasives_Native.option  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string FStar_Pervasives_Native.option  ->  cb  ->  Prims.bool = (fun log_file cache qhash cb -> (

let uu____5983 = ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()))
in (match (uu____5983) with
| true -> begin
(match (qhash) with
| FStar_Pervasives_Native.Some (x) when (Prims.op_Equality qhash cache) -> begin
(

let stats = (FStar_Util.smap_create (Prims.parse_int "0"))
in ((FStar_Util.smap_add stats "fstar_cache_hit" "1");
(

let result = {z3result_status = UNSAT (FStar_Pervasives_Native.None); z3result_time = (Prims.parse_int "0"); z3result_statistics = stats; z3result_query_hash = qhash; z3result_log_file = log_file}
in ((cb result);
true;
));
))
end
| uu____6009 -> begin
false
end)
end
| uu____6014 -> begin
false
end)))


let ask_1_core : FStar_Range.range  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  cb  ->  Prims.bool  ->  unit = (fun r filter_theory cache label_messages qry cb fresh -> (

let theory = (match (fresh) with
| true -> begin
(flatten_fresh_scope ())
end
| uu____6086 -> begin
(

let theory = (FStar_ST.op_Bang bg_scope)
in ((FStar_ST.op_Colon_Equals bg_scope []);
theory;
))
end)
in (

let theory1 = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let uu____6141 = (filter_theory theory1)
in (match (uu____6141) with
| (theory2, _used_unsat_core) -> begin
(

let uu____6151 = (mk_input fresh theory2)
in (match (uu____6151) with
| (input, qhash, log_file_name) -> begin
(

let uu____6182 = (

let uu____6184 = (fresh && (cache_hit log_file_name cache qhash cb))
in (not (uu____6184)))
in (match (uu____6182) with
| true -> begin
(run_job {job = (z3_job log_file_name r fresh label_messages input qhash); callback = cb})
end
| uu____6191 -> begin
()
end))
end))
end)))))


let ask_n_cores : FStar_Range.range  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decls_t  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  unit = (fun r filter_theory cache label_messages qry scope cb -> (

let theory = (

let uu____6261 = (match (scope) with
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_List.rev s)
end
| FStar_Pervasives_Native.None -> begin
((FStar_ST.op_Colon_Equals bg_scope []);
(

let uu____6297 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____6297));
)
end)
in (FStar_List.flatten uu____6261))
in (

let theory1 = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let uu____6326 = (filter_theory theory1)
in (match (uu____6326) with
| (theory2, used_unsat_core) -> begin
(

let uu____6336 = (mk_input true theory2)
in (match (uu____6336) with
| (input, qhash, log_file_name) -> begin
(

let uu____6368 = (

let uu____6370 = (cache_hit log_file_name cache qhash cb)
in (not (uu____6370)))
in (match (uu____6368) with
| true -> begin
(enqueue {job = (z3_job log_file_name r true label_messages input qhash); callback = cb})
end
| uu____6378 -> begin
()
end))
end))
end)))))


let ask : FStar_Range.range  ->  (FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  Prims.bool  ->  unit = (fun r filter1 cache label_messages qry scope cb fresh -> (

let uu____6454 = (

let uu____6456 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____6456 (Prims.parse_int "1")))
in (match (uu____6454) with
| true -> begin
(ask_1_core r filter1 cache label_messages qry cb fresh)
end
| uu____6463 -> begin
(ask_n_cores r filter1 cache label_messages qry scope cb)
end)))




