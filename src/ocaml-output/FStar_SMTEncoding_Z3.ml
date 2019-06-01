
open Prims
open FStar_Pervasives

let _z3hash_checked : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let _z3hash_expected : Prims.string = "1f29cebd4df6"


let _z3url : Prims.string = "https://github.com/FStarLang/binaries/tree/master/z3-tested"


let parse_z3_version_lines : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun out -> (match ((FStar_Util.splitlines out)) with
| (x)::uu____50 -> begin
(

let trimmed = (FStar_Util.trim_string x)
in (

let parts = (FStar_Util.split trimmed " ")
in (

let rec aux = (fun uu___0_74 -> (match (uu___0_74) with
| (hash)::[] -> begin
(

let n1 = (Prims.min (FStar_String.strlen _z3hash_expected) (FStar_String.strlen hash))
in (

let hash_prefix = (FStar_String.substring hash (Prims.parse_int "0") n1)
in (match ((Prims.op_Equality hash_prefix _z3hash_expected)) with
| true -> begin
((

let uu____96 = (FStar_Options.debug_any ())
in (match (uu____96) with
| true -> begin
(

let msg = (FStar_Util.format1 "Successfully found expected Z3 commit hash %s\n" hash)
in (FStar_Util.print_string msg))
end
| uu____102 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| uu____105 -> begin
(

let msg = (FStar_Util.format2 "Expected Z3 commit hash \"%s\", got \"%s\"" _z3hash_expected trimmed)
in FStar_Pervasives_Native.Some (msg))
end)))
end
| (uu____111)::q -> begin
(aux q)
end
| uu____118 -> begin
FStar_Pervasives_Native.Some ("No Z3 commit hash found")
end))
in (aux parts))))
end
| uu____124 -> begin
FStar_Pervasives_Native.Some ("No Z3 version string found")
end))


let z3hash_warning_message : unit  ->  (FStar_Errors.raw_error * Prims.string) FStar_Pervasives_Native.option = (fun uu____142 -> (

let run_proc_result = (FStar_All.try_with (fun uu___29_152 -> (match (()) with
| () -> begin
(

let uu____156 = (

let uu____158 = (FStar_Options.z3_exe ())
in (FStar_Util.run_process "z3_version" uu____158 (("-version")::[]) FStar_Pervasives_Native.None))
in FStar_Pervasives_Native.Some (uu____156))
end)) (fun uu___28_167 -> FStar_Pervasives_Native.None))
in (match (run_proc_result) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((FStar_Errors.Error_Z3InvocationError), ("Could not run Z3")))
end
| FStar_Pervasives_Native.Some (out) -> begin
(

let uu____190 = (parse_z3_version_lines out)
in (match (uu____190) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (msg) -> begin
FStar_Pervasives_Native.Some (((FStar_Errors.Warning_Z3InvocationWarning), (msg)))
end))
end)))


let check_z3hash : unit  ->  unit = (fun uu____221 -> (

let uu____222 = (

let uu____224 = (FStar_ST.op_Bang _z3hash_checked)
in (not (uu____224)))
in (match (uu____222) with
| true -> begin
((FStar_ST.op_Colon_Equals _z3hash_checked true);
(

let uu____271 = (z3hash_warning_message ())
in (match (uu____271) with
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
| uu____299 -> begin
()
end)))


let ini_params : unit  ->  Prims.string Prims.list = (fun uu____309 -> ((check_z3hash ());
(

let uu____311 = (

let uu____315 = (

let uu____319 = (

let uu____323 = (

let uu____327 = (

let uu____329 = (

let uu____331 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int uu____331))
in (FStar_Util.format1 "smt.random_seed=%s" uu____329))
in (uu____327)::[])
in ("-in")::uu____323)
in ("-smt2")::uu____319)
in (

let uu____340 = (FStar_Options.z3_cliopt ())
in (FStar_List.append uu____315 uu____340)))
in (

let uu____345 = (

let uu____349 = (FStar_Options.report_qi ())
in (match (uu____349) with
| true -> begin
("smt.qi.profile=true")::[]
end
| uu____358 -> begin
[]
end))
in (FStar_List.append uu____311 uu____345)));
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
| uu____420 -> begin
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
| uu____446 -> begin
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
| uu____493 -> begin
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
| uu____540 -> begin
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
| uu____579 -> begin
false
end))


type z3statistics =
Prims.string FStar_Util.smap


let status_tag : z3status  ->  Prims.string = (fun uu___1_590 -> (match (uu___1_590) with
| SAT (uu____592) -> begin
"sat"
end
| UNSAT (uu____601) -> begin
"unsat"
end
| UNKNOWN (uu____603) -> begin
"unknown"
end
| TIMEOUT (uu____612) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let status_string_and_errors : z3status  ->  (Prims.string * FStar_SMTEncoding_Term.error_labels) = (fun s -> (match (s) with
| KILLED -> begin
(((status_tag s)), ([]))
end
| UNSAT (uu____639) -> begin
(((status_tag s)), ([]))
end
| SAT (errs, msg) -> begin
(

let uu____649 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.op_Hat " because " msg1)
end))
in ((uu____649), (errs)))
end
| UNKNOWN (errs, msg) -> begin
(

let uu____668 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.op_Hat " because " msg1)
end))
in ((uu____668), (errs)))
end
| TIMEOUT (errs, msg) -> begin
(

let uu____687 = (FStar_Util.format2 "%s%s" (status_tag s) (match (msg) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (msg1) -> begin
(Prims.op_Hat " because " msg1)
end))
in ((uu____687), (errs)))
end))


let tid : unit  ->  Prims.string = (fun uu____704 -> (

let uu____705 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right uu____705 FStar_Util.string_of_int)))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id1 -> (

let filter1 = (

let uu____724 = (FStar_Options.report_qi ())
in (match (uu____724) with
| true -> begin
(fun s -> (not ((FStar_Util.starts_with s "[quantifier_instances]"))))
end
| uu____735 -> begin
(fun s -> true)
end))
in (

let uu____740 = (FStar_Options.z3_exe ())
in (

let uu____742 = (ini_params ())
in (FStar_Util.start_process id1 uu____740 uu____742 (fun s -> (Prims.op_Equality s "Done!")) filter1)))))


let new_z3proc_with_id : unit  ->  FStar_Util.proc = (

let ctr = (FStar_Util.mk_ref (~- ((Prims.parse_int "1"))))
in (fun uu____762 -> (

let uu____763 = (

let uu____765 = ((FStar_Util.incr ctr);
(

let uu____768 = (FStar_ST.op_Bang ctr)
in (FStar_All.pipe_right uu____768 FStar_Util.string_of_int));
)
in (FStar_Util.format1 "bg-%s" uu____765))
in (new_z3proc uu____763))))

type bgproc =
{ask : Prims.string  ->  Prims.string; refresh : unit  ->  Prims.string; restart : unit  ->  unit; kill : unit  ->  Prims.string; store : FStar_SMTEncoding_QIReport.query_info  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  unit; extract : unit  ->  (FStar_SMTEncoding_QIReport.query_info * FStar_SMTEncoding_Term.decl Prims.list) Prims.list}


let __proj__Mkbgproc__item__ask : bgproc  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; kill = kill; store = store; extract = extract} -> begin
ask
end))


let __proj__Mkbgproc__item__refresh : bgproc  ->  unit  ->  Prims.string = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; kill = kill; store = store; extract = extract} -> begin
refresh
end))


let __proj__Mkbgproc__item__restart : bgproc  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; kill = kill; store = store; extract = extract} -> begin
restart
end))


let __proj__Mkbgproc__item__kill : bgproc  ->  unit  ->  Prims.string = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; kill = kill; store = store; extract = extract} -> begin
kill
end))


let __proj__Mkbgproc__item__store : bgproc  ->  FStar_SMTEncoding_QIReport.query_info  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; kill = kill; store = store; extract = extract} -> begin
store
end))


let __proj__Mkbgproc__item__extract : bgproc  ->  unit  ->  (FStar_SMTEncoding_QIReport.query_info * FStar_SMTEncoding_Term.decl Prims.list) Prims.list = (fun projectee -> (match (projectee) with
| {ask = ask; refresh = refresh; restart = restart; kill = kill; store = store; extract = extract} -> begin
extract
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

let get_module_name = (fun uu____1561 -> (

let uu____1562 = (FStar_ST.op_Bang current_module_name)
in (match (uu____1562) with
| FStar_Pervasives_Native.None -> begin
(failwith "Module name not set")
end
| FStar_Pervasives_Native.Some (n1) -> begin
n1
end)))
in (

let next_file_name = (fun uu____1604 -> (

let n1 = (get_module_name ())
in (

let file_name = (

let uu____1609 = (

let uu____1618 = (FStar_ST.op_Bang used_file_names)
in (FStar_List.tryFind (fun uu____1671 -> (match (uu____1671) with
| (m, uu____1680) -> begin
(Prims.op_Equality n1 m)
end)) uu____1618))
in (match (uu____1609) with
| FStar_Pervasives_Native.None -> begin
((

let uu____1694 = (

let uu____1703 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((Prims.parse_int "0"))))::uu____1703)
in (FStar_ST.op_Colon_Equals used_file_names uu____1694));
n1;
)
end
| FStar_Pervasives_Native.Some (uu____1791, k) -> begin
((

let uu____1804 = (

let uu____1813 = (FStar_ST.op_Bang used_file_names)
in (((n1), ((k + (Prims.parse_int "1")))))::uu____1813)
in (FStar_ST.op_Colon_Equals used_file_names uu____1804));
(

let uu____1901 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n1 uu____1901));
)
end))
in (FStar_Util.format1 "queries-%s.smt2" file_name))))
in (

let new_log_file = (fun uu____1916 -> (

let file_name = (next_file_name ())
in ((FStar_ST.op_Colon_Equals current_file_name (FStar_Pervasives_Native.Some (file_name)));
(

let fh = (FStar_Util.open_file_for_writing file_name)
in ((FStar_ST.op_Colon_Equals log_file_opt (FStar_Pervasives_Native.Some (((fh), (file_name)))));
((fh), (file_name));
));
)))
in (

let get_log_file = (fun uu____1998 -> (

let uu____1999 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____1999) with
| FStar_Pervasives_Native.None -> begin
(new_log_file ())
end
| FStar_Pervasives_Native.Some (fh) -> begin
fh
end)))
in (

let append_to_log = (fun str -> (

let uu____2070 = (get_log_file ())
in (match (uu____2070) with
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

let uu____2110 = (fresh || (

let uu____2113 = (FStar_Options.n_cores ())
in (uu____2113 > (Prims.parse_int "1"))))
in (match (uu____2110) with
| true -> begin
(write_to_new_log str)
end
| uu____2118 -> begin
(append_to_log str)
end)))
in (

let close_log = (fun uu____2125 -> (

let uu____2126 = (FStar_ST.op_Bang log_file_opt)
in (match (uu____2126) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (fh, uu____2173) -> begin
((FStar_Util.close_file fh);
(FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None);
)
end)))
in (

let log_file_name = (fun uu____2226 -> (

let uu____2227 = (FStar_ST.op_Bang current_file_name)
in (match (uu____2227) with
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

let the_queries = (FStar_Util.mk_ref [])
in (

let z3proc = (fun uu____2303 -> ((

let uu____2305 = (

let uu____2307 = (FStar_ST.op_Bang the_z3proc)
in (Prims.op_Equality uu____2307 FStar_Pervasives_Native.None))
in (match (uu____2305) with
| true -> begin
((

let uu____2337 = (

let uu____2340 = (new_z3proc_with_id ())
in FStar_Pervasives_Native.Some (uu____2340))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2337));
(FStar_ST.op_Colon_Equals the_queries []);
)
end
| uu____2405 -> begin
()
end));
(

let uu____2407 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.must uu____2407));
))
in (

let x = []
in (

let ask = (fun input -> (

let kill_handler = (fun uu____2451 -> "\nkilled\n")
in (

let uu____2453 = (z3proc ())
in (FStar_Util.ask_process uu____2453 input kill_handler))))
in (

let refresh = (fun uu____2460 -> (

let extra = (

let uu____2463 = (z3proc ())
in (FStar_Util.kill_process uu____2463))
in ((

let uu____2465 = (

let uu____2468 = (new_z3proc_with_id ())
in FStar_Pervasives_Native.Some (uu____2468))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2465));
(FStar_ST.op_Colon_Equals the_queries []);
(query_logging.close_log ());
extra;
)))
in (

let kill = (fun uu____2541 -> (

let uu____2543 = (

let uu____2545 = (FStar_ST.op_Bang the_z3proc)
in (FStar_Util.is_some uu____2545))
in (match (uu____2543) with
| true -> begin
(

let extra = (

let uu____2575 = (z3proc ())
in (FStar_Util.kill_process uu____2575))
in ((FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_queries []);
extra;
))
end
| uu____2643 -> begin
""
end)))
in (

let restart = (fun uu____2651 -> ((query_logging.close_log ());
(FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None);
(

let uu____2677 = (

let uu____2680 = (new_z3proc_with_id ())
in FStar_Pervasives_Native.Some (uu____2680))
in (FStar_ST.op_Colon_Equals the_z3proc uu____2677));
))
in (

let store = (fun info decls -> (

let uu____2719 = (

let uu____2728 = (FStar_ST.op_Bang the_queries)
in (FStar_List.append uu____2728 ((((info), (decls)))::[])))
in (FStar_ST.op_Colon_Equals the_queries uu____2719)))
in (

let extract = (fun uu____2840 -> (FStar_ST.op_Bang the_queries))
in (FStar_Util.mk_ref {ask = (FStar_Util.with_monitor x ask); refresh = (FStar_Util.with_monitor x refresh); restart = (FStar_Util.with_monitor x restart); kill = (FStar_Util.with_monitor x kill); store = store; extract = extract})))))))))))


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
| uu____3188 -> begin
(

let uu____3190 = (until tag lines2)
in (FStar_Util.map_opt uu____3190 (fun uu____3226 -> (match (uu____3226) with
| (until_tag, rest) -> begin
(((l)::until_tag), (rest))
end))))
end)
end))
in (

let start_tag = (fun tag -> (Prims.op_Hat "<" (Prims.op_Hat tag ">")))
in (

let end_tag = (fun tag -> (Prims.op_Hat "</" (Prims.op_Hat tag ">")))
in (

let find_section = (fun tag lines1 -> (

let uu____3333 = (until (start_tag tag) lines1)
in (match (uu____3333) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (lines1))
end
| FStar_Pervasives_Native.Some (prefix1, suffix) -> begin
(

let uu____3403 = (until (end_tag tag) suffix)
in (match (uu____3403) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.op_Hat "Parse error: " (Prims.op_Hat (end_tag tag) " not found")))
end
| FStar_Pervasives_Native.Some (section, suffix1) -> begin
((FStar_Pervasives_Native.Some (section)), ((FStar_List.append prefix1 suffix1)))
end))
end)))
in (

let uu____3488 = (find_section "result" lines)
in (match (uu____3488) with
| (result_opt, lines1) -> begin
(

let result = (FStar_Util.must result_opt)
in (

let uu____3527 = (find_section "reason-unknown" lines1)
in (match (uu____3527) with
| (reason_unknown, lines2) -> begin
(

let uu____3559 = (find_section "unsat-core" lines2)
in (match (uu____3559) with
| (unsat_core, lines3) -> begin
(

let uu____3591 = (find_section "statistics" lines3)
in (match (uu____3591) with
| (statistics, lines4) -> begin
(

let uu____3623 = (find_section "labels" lines4)
in (match (uu____3623) with
| (labels, lines5) -> begin
(

let remaining = (

let uu____3659 = (until "Done!" lines5)
in (match (uu____3659) with
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
| uu____3713 -> begin
(

let msg = (FStar_Util.format2 "%sUnexpected additional output from Z3: %s\n" (match (log_file) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (f) -> begin
(Prims.op_Hat f ": ")
end) (FStar_String.concat "\n" remaining))
in (FStar_Errors.log_issue r ((FStar_Errors.Warning_UnexpectedZ3Output), (msg))))
end);
(

let uu____3729 = (FStar_Util.must result_opt)
in {smt_result = uu____3729; smt_reason_unknown = reason_unknown; smt_unsat_core = unsat_core; smt_statistics = statistics; smt_labels = labels});
))
end))
end))
end))
end)))
end)))))))


let doZ3Exe : Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_QIReport.query_info  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.bool  ->  Prims.string  ->  FStar_SMTEncoding_Term.error_labels  ->  (z3status * z3statistics) = (fun log_file info decls fresh input label_messages -> (

let r = info.FStar_SMTEncoding_QIReport.query_info_range
in (

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
| uu____3832 -> begin
(

let uu____3834 = (FStar_All.pipe_right (FStar_Util.split s2 " ") (FStar_Util.sort_with FStar_String.compare))
in FStar_Pervasives_Native.Some (uu____3834))
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

let uu____3879 = (lblnegs rest)
in (lname)::uu____3879)
end
| (lname)::(uu____3885)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest)
end
| uu____3895 -> begin
[]
end))
in (

let lblnegs1 = (lblnegs lines1)
in (FStar_All.pipe_right lblnegs1 (FStar_List.collect (fun l -> (

let uu____3919 = (FStar_All.pipe_right label_messages (FStar_List.tryFind (fun uu____3959 -> (match (uu____3959) with
| (m, uu____3969, uu____3970) -> begin
(

let uu____3973 = (FStar_SMTEncoding_Term.fv_name m)
in (Prims.op_Equality uu____3973 l))
end))))
in (match (uu____3919) with
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
| uu____4070 -> begin
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
| uu____4099 -> begin
ltok
end)
in (FStar_Util.smap_add statistics key value)))))
end
| uu____4102 -> begin
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
| uu____4131 -> begin
ru
end))))
in (

let status = ((

let uu____4135 = (FStar_Options.debug_any ())
in (match (uu____4135) with
| true -> begin
(

let uu____4138 = (FStar_Util.format1 "Z3 says: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (FStar_All.pipe_left FStar_Util.print_string uu____4138))
end
| uu____4143 -> begin
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

let uu____4170 = (

let uu____4175 = (FStar_ST.op_Bang bg_z3_proc)
in uu____4175.restart)
in (uu____4170 ()));
KILLED;
)
end
| uu____4195 -> begin
(

let uu____4196 = (FStar_Util.format1 "Unexpected output from Z3: got output result: %s\n" (FStar_String.concat "\n" smt_output.smt_result))
in (failwith uu____4196))
end);
)
in ((status), (statistics))))))))))
in (

let stdout1 = (match (fresh) with
| true -> begin
(

let proc = (new_z3proc_with_id ())
in (

let kill_handler = (fun uu____4211 -> "\nkilled\n")
in (

let out = (FStar_Util.ask_process proc input kill_handler)
in (

let qip_output = (FStar_Util.kill_process proc)
in ((

let uu____4218 = (FStar_Options.report_qi ())
in (match (uu____4218) with
| true -> begin
(

let query_data = (((info), (decls)))::[]
in (FStar_SMTEncoding_QIReport.qiprofile_analysis query_data qip_output))
end
| uu____4244 -> begin
()
end));
out;
)))))
end
| uu____4246 -> begin
(

let uu____4248 = (

let uu____4255 = (FStar_ST.op_Bang bg_z3_proc)
in uu____4255.ask)
in (uu____4248 input))
end)
in (

let uu____4275 = (parse (FStar_Util.trim_string stdout1))
in (match (uu____4275) with
| (status, statistics) -> begin
(

let uu____4286 = uu____4275
in ((

let uu____4292 = (FStar_Options.report_qi ())
in (match (uu____4292) with
| true -> begin
(match (status) with
| UNSAT (uu____4295) -> begin
(match (fresh) with
| true -> begin
()
end
| uu____4297 -> begin
(

let uu____4299 = (

let uu____4310 = (FStar_ST.op_Bang bg_z3_proc)
in uu____4310.store)
in (uu____4299 info decls))
end)
end
| uu____4330 -> begin
()
end)
end
| uu____4331 -> begin
()
end));
((status), (statistics));
))
end))))))


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
{z3result_status : z3status; z3result_time : Prims.int; z3result_statistics : z3statistics; z3result_query_hash : Prims.string FStar_Pervasives_Native.option; z3result_query_decls : FStar_SMTEncoding_Term.decl Prims.list; z3result_log_file : Prims.string FStar_Pervasives_Native.option}


let __proj__Mkz3result__item__z3result_status : z3result  ->  z3status = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_log_file = z3result_log_file} -> begin
z3result_status
end))


let __proj__Mkz3result__item__z3result_time : z3result  ->  Prims.int = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_log_file = z3result_log_file} -> begin
z3result_time
end))


let __proj__Mkz3result__item__z3result_statistics : z3result  ->  z3statistics = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_log_file = z3result_log_file} -> begin
z3result_statistics
end))


let __proj__Mkz3result__item__z3result_query_hash : z3result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_log_file = z3result_log_file} -> begin
z3result_query_hash
end))


let __proj__Mkz3result__item__z3result_query_decls : z3result  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_log_file = z3result_log_file} -> begin
z3result_query_decls
end))


let __proj__Mkz3result__item__z3result_log_file : z3result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {z3result_status = z3result_status; z3result_time = z3result_time; z3result_statistics = z3result_statistics; z3result_query_hash = z3result_query_hash; z3result_query_decls = z3result_query_decls; z3result_log_file = z3result_log_file} -> begin
z3result_log_file
end))


type z3job =
z3result job_t


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let z3_job : Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_QIReport.query_info  ->  Prims.bool  ->  FStar_SMTEncoding_Term.error_labels  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.string FStar_Pervasives_Native.option  ->  unit  ->  z3result = (fun log_file r fresh label_messages input decls qhash uu____4694 -> (

let start = (FStar_Util.now ())
in (

let uu____4706 = (FStar_All.try_with (fun uu___446_4716 -> (match (()) with
| () -> begin
(doZ3Exe log_file r decls fresh input label_messages)
end)) (fun uu___445_4724 -> if (

let uu____4729 = (FStar_Options.trace_error ())
in (not (uu____4729))) then begin
(Obj.magic ((Obj.repr ((

let uu____4732 = (

let uu____4741 = (

let uu____4754 = (FStar_ST.op_Bang bg_z3_proc)
in uu____4754.extract)
in (uu____4741 ()))
in (FStar_All.pipe_left (fun a1 -> ()) uu____4732));
(

let uu____4783 = (

let uu____4785 = (

let uu____4791 = (FStar_ST.op_Bang bg_z3_proc)
in uu____4791.refresh)
in (uu____4785 ()))
in (FStar_All.pipe_left (fun a2 -> ()) uu____4783));
(FStar_Exn.raise uu___445_4724);
))))
end else begin
(Obj.magic ((Obj.repr (failwith "unreachable"))))
end))
in (match (uu____4706) with
| (status, statistics) -> begin
(

let uu____4818 = (

let uu____4824 = (FStar_Util.now ())
in (FStar_Util.time_diff start uu____4824))
in (match (uu____4818) with
| (uu____4825, elapsed_time) -> begin
{z3result_status = status; z3result_time = elapsed_time; z3result_statistics = statistics; z3result_query_hash = qhash; z3result_query_decls = decls; z3result_log_file = log_file}
end))
end))))


let running : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let rec dequeue' : unit  ->  unit = (fun uu____4848 -> (

let j = (

let uu____4850 = (FStar_ST.op_Bang job_queue)
in (match (uu____4850) with
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
(FStar_Util.with_monitor job_queue (fun uu____4918 -> (FStar_Util.decr pending_jobs)) ());
(dequeue ());
)))
and dequeue : unit  ->  unit = (fun uu____4920 -> (

let uu____4921 = (FStar_ST.op_Bang running)
in if uu____4921 then begin
(

let rec aux = (fun uu____4949 -> ((FStar_Util.monitor_enter job_queue);
(

let uu____4955 = (FStar_ST.op_Bang job_queue)
in (match (uu____4955) with
| [] -> begin
((FStar_Util.monitor_exit job_queue);
(FStar_Util.sleep (Prims.parse_int "50"));
(aux ());
)
end
| uu____4988 -> begin
(dequeue' ())
end));
))
in (aux ()))
end else begin
()
end))
and run_job : z3job  ->  unit = (fun j -> (

let uu____4992 = (j.job ())
in (FStar_All.pipe_left j.callback uu____4992)))


let kill : unit  ->  unit = (fun uu____4998 -> (

let uu____4999 = (

let uu____5001 = (FStar_Options.n_cores ())
in (uu____5001 < (Prims.parse_int "2")))
in (match (uu____4999) with
| true -> begin
(

let uu____5005 = (

let uu____5007 = (

let uu____5013 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5013.kill)
in (uu____5007 ()))
in (FStar_All.pipe_left (fun a3 -> ()) uu____5005))
end
| uu____5034 -> begin
()
end)))


let init : unit  ->  unit = (fun uu____5041 -> ((FStar_ST.op_Colon_Equals running true);
(

let n_cores1 = (FStar_Options.n_cores ())
in (match ((n_cores1 > (Prims.parse_int "1"))) with
| true -> begin
(

let rec aux = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
()
end
| uu____5080 -> begin
((FStar_Util.spawn dequeue);
(aux (n1 - (Prims.parse_int "1")));
)
end))
in (aux n_cores1))
end
| uu____5084 -> begin
()
end));
))


let enqueue : z3job  ->  unit = (fun j -> (FStar_Util.with_monitor job_queue (fun uu____5098 -> ((

let uu____5100 = (

let uu____5103 = (FStar_ST.op_Bang job_queue)
in (FStar_List.append uu____5103 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue uu____5100));
(FStar_Util.monitor_pulse job_queue);
)) ()))


let finish : unit  ->  unit = (fun uu____5161 -> (

let rec aux = (fun uu____5167 -> (

let uu____5168 = (FStar_Util.with_monitor job_queue (fun uu____5186 -> (

let uu____5187 = (FStar_ST.op_Bang pending_jobs)
in (

let uu____5210 = (

let uu____5211 = (FStar_ST.op_Bang job_queue)
in (FStar_List.length uu____5211))
in ((uu____5187), (uu____5210))))) ())
in (match (uu____5168) with
| (n1, m) -> begin
(match ((Prims.op_Equality (n1 + m) (Prims.parse_int "0"))) with
| true -> begin
(FStar_ST.op_Colon_Equals running false)
end
| uu____5267 -> begin
((FStar_Util.sleep (Prims.parse_int "500"));
(aux ());
)
end)
end)))
in (

let uu____5271 = (

let uu____5273 = (FStar_Options.n_cores ())
in (uu____5273 > (Prims.parse_int "1")))
in (match (uu____5271) with
| true -> begin
(aux ())
end
| uu____5277 -> begin
(kill ())
end))))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let fresh_scope : scope_t FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let mk_fresh_scope : unit  ->  scope_t = (fun uu____5295 -> (FStar_ST.op_Bang fresh_scope))


let flatten_fresh_scope : unit  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun uu____5322 -> (

let uu____5323 = (

let uu____5328 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____5328))
in (FStar_List.flatten uu____5323)))


let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : Prims.string  ->  unit = (fun msg -> (FStar_Util.atomically (fun uu____5372 -> ((

let uu____5374 = (

let uu____5375 = (FStar_ST.op_Bang fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::uu____5375)
in (FStar_ST.op_Colon_Equals fresh_scope uu____5374));
(

let uu____5420 = (

let uu____5423 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____5423 ((FStar_SMTEncoding_Term.Push)::(FStar_SMTEncoding_Term.Caption (msg))::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____5420));
))))


let pop : Prims.string  ->  unit = (fun msg -> (FStar_Util.atomically (fun uu____5483 -> ((

let uu____5485 = (

let uu____5486 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.tl uu____5486))
in (FStar_ST.op_Colon_Equals fresh_scope uu____5485));
(

let uu____5531 = (

let uu____5534 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____5534 ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[])))
in (FStar_ST.op_Colon_Equals bg_scope uu____5531));
))))


let snapshot : Prims.string  ->  (Prims.int * unit) = (fun msg -> (FStar_Common.snapshot push fresh_scope msg))


let rollback : Prims.string  ->  Prims.int FStar_Pervasives_Native.option  ->  unit = (fun msg depth -> (FStar_Common.rollback (fun uu____5621 -> (pop msg)) fresh_scope depth))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun decls -> ((FStar_All.pipe_right decls (FStar_List.iter (fun uu___2_5636 -> (match (uu___2_5636) with
| FStar_SMTEncoding_Term.Push -> begin
(failwith "Unexpected push/pop")
end
| FStar_SMTEncoding_Term.Pop -> begin
(failwith "Unexpected push/pop")
end
| uu____5639 -> begin
()
end))));
(

let uu____5641 = (FStar_ST.op_Bang fresh_scope)
in (match (uu____5641) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd1 decls))::tl1))
end
| uu____5692 -> begin
(failwith "Impossible")
end));
(

let uu____5694 = (

let uu____5697 = (FStar_ST.op_Bang bg_scope)
in (FStar_List.append uu____5697 decls))
in (FStar_ST.op_Colon_Equals bg_scope uu____5694));
))


let refresh : unit  ->  unit = (fun uu____5751 -> ((

let uu____5753 = (

let uu____5755 = (FStar_Options.n_cores ())
in (uu____5755 < (Prims.parse_int "2")))
in (match (uu____5753) with
| true -> begin
(

let qdata = (

let uu____5768 = (

let uu____5781 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5781.extract)
in (uu____5768 ()))
in (

let qip_output = (

let uu____5803 = (

let uu____5809 = (FStar_ST.op_Bang bg_z3_proc)
in uu____5809.refresh)
in (uu____5803 ()))
in (

let uu____5829 = (FStar_Options.report_qi ())
in (match (uu____5829) with
| true -> begin
(FStar_SMTEncoding_QIReport.qiprofile_analysis qdata qip_output)
end
| uu____5832 -> begin
()
end))))
end
| uu____5834 -> begin
()
end));
(

let uu____5836 = (flatten_fresh_scope ())
in (FStar_ST.op_Colon_Equals bg_scope uu____5836));
))


let context_profile : FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun theory -> (

let uu____5872 = (FStar_List.fold_left (fun uu____5905 d -> (match (uu____5905) with
| (out, _total) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Module (name, decls) -> begin
(

let decls1 = (FStar_List.filter (fun uu___3_5974 -> (match (uu___3_5974) with
| FStar_SMTEncoding_Term.Assume (uu____5976) -> begin
true
end
| uu____5978 -> begin
false
end)) decls)
in (

let n1 = (FStar_List.length decls1)
in (((((name), (n1)))::out), ((n1 + _total)))))
end
| uu____5995 -> begin
((out), (_total))
end)
end)) (([]), ((Prims.parse_int "0"))) theory)
in (match (uu____5872) with
| (modules, total_decls) -> begin
(

let modules1 = (FStar_List.sortWith (fun uu____6057 uu____6058 -> (match (((uu____6057), (uu____6058))) with
| ((uu____6084, n1), (uu____6086, m)) -> begin
(m - n1)
end)) modules)
in ((match ((Prims.op_disEquality modules1 [])) with
| true -> begin
(

let uu____6124 = (FStar_Util.string_of_int total_decls)
in (FStar_Util.print1 "Z3 Proof Stats: context_profile with %s assertions\n" uu____6124))
end
| uu____6127 -> begin
()
end);
(FStar_List.iter (fun uu____6139 -> (match (uu____6139) with
| (m, n1) -> begin
(match ((Prims.op_disEquality n1 (Prims.parse_int "0"))) with
| true -> begin
(

let uu____6155 = (FStar_Util.string_of_int n1)
in (FStar_Util.print2 "Z3 Proof Stats: %s produced %s SMT decls\n" m uu____6155))
end
| uu____6158 -> begin
()
end)
end)) modules1);
))
end)))


let mk_input : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (Prims.string * Prims.string FStar_Pervasives_Native.option * Prims.string FStar_Pervasives_Native.option) = (fun fresh theory -> (

let options = (FStar_ST.op_Bang z3_options)
in ((

let uu____6214 = (FStar_Options.print_z3_statistics ())
in (match (uu____6214) with
| true -> begin
(context_profile theory)
end
| uu____6217 -> begin
()
end));
(

let uu____6219 = (

let uu____6228 = ((FStar_Options.record_hints ()) || ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())))
in (match (uu____6228) with
| true -> begin
(

let uu____6239 = (

let uu____6250 = (FStar_All.pipe_right theory (FStar_Util.prefix_until (fun uu___4_6278 -> (match (uu___4_6278) with
| FStar_SMTEncoding_Term.CheckSat -> begin
true
end
| uu____6281 -> begin
false
end))))
in (FStar_All.pipe_right uu____6250 FStar_Option.get))
in (match (uu____6239) with
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

let uu____6364 = (FStar_Options.keep_query_captions ())
in (match (uu____6364) with
| true -> begin
(

let uu____6368 = (FStar_All.pipe_right prefix1 (FStar_List.map (FStar_SMTEncoding_Term.declToSmt_no_caps options)))
in (FStar_All.pipe_right uu____6368 (FStar_String.concat "\n")))
end
| uu____6383 -> begin
ps
end))
in (

let uu____6385 = (

let uu____6389 = (FStar_Util.digest_of_string hs)
in FStar_Pervasives_Native.Some (uu____6389))
in (((Prims.op_Hat ps (Prims.op_Hat "\n" ss))), (uu____6385))))))))))
end))
end
| uu____6397 -> begin
(

let uu____6399 = (

let uu____6401 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory)
in (FStar_All.pipe_right uu____6401 (FStar_String.concat "\n")))
in ((uu____6399), (FStar_Pervasives_Native.None)))
end))
in (match (uu____6219) with
| (r, hash) -> begin
(

let log_file_name = (

let uu____6443 = (FStar_Options.log_queries ())
in (match (uu____6443) with
| true -> begin
(

let uu____6449 = (query_logging.write_to_log fresh r)
in FStar_Pervasives_Native.Some (uu____6449))
end
| uu____6452 -> begin
FStar_Pervasives_Native.None
end))
in ((r), (hash), (log_file_name)))
end));
)))


type cb =
z3result  ->  unit


let cache_hit : FStar_SMTEncoding_QIReport.query_info  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string FStar_Pervasives_Native.option  ->  cb  ->  Prims.bool = (fun r log_file cache qhash cb -> (

let uu____6512 = ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()))
in (match (uu____6512) with
| true -> begin
(match (qhash) with
| FStar_Pervasives_Native.Some (x) when (Prims.op_Equality qhash cache) -> begin
(

let stats = (FStar_Util.smap_create (Prims.parse_int "0"))
in ((FStar_Util.smap_add stats "fstar_cache_hit" "1");
(

let result = {z3result_status = UNSAT (FStar_Pervasives_Native.None); z3result_time = (Prims.parse_int "0"); z3result_statistics = stats; z3result_query_hash = qhash; z3result_query_decls = []; z3result_log_file = log_file}
in ((cb result);
true;
));
))
end
| uu____6537 -> begin
false
end)
end
| uu____6542 -> begin
false
end)))


let ask_1_core : FStar_SMTEncoding_QIReport.query_info  ->  (FStar_SMTEncoding_Term.decl Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  cb  ->  Prims.bool  ->  unit = (fun r filter_theory cache label_messages qry cb fresh -> (

let theory = (match (fresh) with
| true -> begin
(flatten_fresh_scope ())
end
| uu____6624 -> begin
(

let theory = (FStar_ST.op_Bang bg_scope)
in ((FStar_ST.op_Colon_Equals bg_scope []);
theory;
))
end)
in (

let theory1 = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let uu____6679 = (filter_theory theory1)
in (match (uu____6679) with
| (theory2, _used_unsat_core) -> begin
(

let fscp = (

let uu____6698 = (FStar_Options.report_qi ())
in (match (uu____6698) with
| true -> begin
(

let fscp = (

let uu____6706 = (flatten_fresh_scope ())
in (FStar_List.append uu____6706 (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[])))))
in (

let uu____6709 = (filter_theory fscp)
in (match (uu____6709) with
| (fscp1, uu____6720) -> begin
fscp1
end)))
end
| uu____6727 -> begin
[]
end))
in (

let uu____6729 = (mk_input fresh theory2)
in (match (uu____6729) with
| (input, qhash, log_file_name) -> begin
(

let uu____6760 = (

let uu____6762 = (fresh && (cache_hit r log_file_name cache qhash cb))
in (not (uu____6762)))
in (match (uu____6760) with
| true -> begin
(run_job {job = (z3_job log_file_name r fresh label_messages input fscp qhash); callback = cb})
end
| uu____6765 -> begin
()
end))
end)))
end)))))


let ask_n_cores : FStar_SMTEncoding_QIReport.query_info  ->  (FStar_SMTEncoding_Term.decl Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  unit = (fun r filter_theory cache label_messages qry scope cb -> (

let theory = (

let uu____6845 = (match (scope) with
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_List.rev s)
end
| FStar_Pervasives_Native.None -> begin
((FStar_ST.op_Colon_Equals bg_scope []);
(

let uu____6881 = (FStar_ST.op_Bang fresh_scope)
in (FStar_List.rev uu____6881));
)
end)
in (FStar_List.flatten uu____6845))
in (

let theory1 = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let uu____6910 = (filter_theory theory1)
in (match (uu____6910) with
| (theory2, used_unsat_core) -> begin
(

let fscp = (

let uu____6929 = (FStar_Options.report_qi ())
in (match (uu____6929) with
| true -> begin
theory2
end
| uu____6934 -> begin
[]
end))
in (

let uu____6936 = (mk_input true theory2)
in (match (uu____6936) with
| (input, qhash, log_file_name) -> begin
(

let uu____6968 = (

let uu____6970 = (cache_hit r log_file_name cache qhash cb)
in (not (uu____6970)))
in (match (uu____6968) with
| true -> begin
(enqueue {job = (z3_job log_file_name r true label_messages input fscp qhash); callback = cb})
end
| uu____6974 -> begin
()
end))
end)))
end)))))


let ask : FStar_SMTEncoding_QIReport.query_info  ->  (FStar_SMTEncoding_Term.decl Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))  ->  Prims.string FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  scope_t FStar_Pervasives_Native.option  ->  cb  ->  Prims.bool  ->  unit = (fun r filter1 cache label_messages qry scope cb fresh -> (

let uu____7058 = (

let uu____7060 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____7060 (Prims.parse_int "1")))
in (match (uu____7058) with
| true -> begin
(ask_1_core r filter1 cache label_messages qry cb fresh)
end
| uu____7065 -> begin
(ask_n_cores r filter1 cache label_messages qry scope cb)
end)))




