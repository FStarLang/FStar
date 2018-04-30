
open Prims
open FStar_Pervasives
type debug_level_t =
| Low
| Medium
| High
| Extreme
| Other of Prims.string


let uu___is_Low : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Low -> begin
true
end
| uu____11 -> begin
false
end))


let uu___is_Medium : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Medium -> begin
true
end
| uu____17 -> begin
false
end))


let uu___is_High : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| High -> begin
true
end
| uu____23 -> begin
false
end))


let uu___is_Extreme : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Extreme -> begin
true
end
| uu____29 -> begin
false
end))


let uu___is_Other : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Other (_0) -> begin
true
end
| uu____36 -> begin
false
end))


let __proj__Other__item___0 : debug_level_t  ->  Prims.string = (fun projectee -> (match (projectee) with
| Other (_0) -> begin
_0
end))

type option_val =
| Bool of Prims.bool
| String of Prims.string
| Path of Prims.string
| Int of Prims.int
| List of option_val Prims.list
| Unset


let uu___is_Bool : option_val  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool (_0) -> begin
true
end
| uu____77 -> begin
false
end))


let __proj__Bool__item___0 : option_val  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool (_0) -> begin
_0
end))


let uu___is_String : option_val  ->  Prims.bool = (fun projectee -> (match (projectee) with
| String (_0) -> begin
true
end
| uu____91 -> begin
false
end))


let __proj__String__item___0 : option_val  ->  Prims.string = (fun projectee -> (match (projectee) with
| String (_0) -> begin
_0
end))


let uu___is_Path : option_val  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Path (_0) -> begin
true
end
| uu____105 -> begin
false
end))


let __proj__Path__item___0 : option_val  ->  Prims.string = (fun projectee -> (match (projectee) with
| Path (_0) -> begin
_0
end))


let uu___is_Int : option_val  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int (_0) -> begin
true
end
| uu____119 -> begin
false
end))


let __proj__Int__item___0 : option_val  ->  Prims.int = (fun projectee -> (match (projectee) with
| Int (_0) -> begin
_0
end))


let uu___is_List : option_val  ->  Prims.bool = (fun projectee -> (match (projectee) with
| List (_0) -> begin
true
end
| uu____135 -> begin
false
end))


let __proj__List__item___0 : option_val  ->  option_val Prims.list = (fun projectee -> (match (projectee) with
| List (_0) -> begin
_0
end))


let uu___is_Unset : option_val  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unset -> begin
true
end
| uu____154 -> begin
false
end))


let mk_bool : Prims.bool  ->  option_val = (fun _0_4 -> Bool (_0_4))


let mk_string : Prims.string  ->  option_val = (fun _0_5 -> String (_0_5))


let mk_path : Prims.string  ->  option_val = (fun _0_6 -> Path (_0_6))


let mk_int : Prims.int  ->  option_val = (fun _0_7 -> Int (_0_7))


let mk_list : option_val Prims.list  ->  option_val = (fun _0_8 -> List (_0_8))

type options =
| Set
| Reset
| Restore


let uu___is_Set : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Set -> begin
true
end
| uu____182 -> begin
false
end))


let uu___is_Reset : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reset -> begin
true
end
| uu____188 -> begin
false
end))


let uu___is_Restore : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Restore -> begin
true
end
| uu____194 -> begin
false
end))


let __unit_tests__ : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let __unit_tests : unit  ->  Prims.bool = (fun uu____212 -> (FStar_ST.op_Bang __unit_tests__))


let __set_unit_tests : unit  ->  unit = (fun uu____240 -> (FStar_ST.op_Colon_Equals __unit_tests__ true))


let __clear_unit_tests : unit  ->  unit = (fun uu____268 -> (FStar_ST.op_Colon_Equals __unit_tests__ false))


let as_bool : option_val  ->  Prims.bool = (fun uu___38_296 -> (match (uu___38_296) with
| Bool (b) -> begin
b
end
| uu____298 -> begin
(failwith "Impos: expected Bool")
end))


let as_int : option_val  ->  Prims.int = (fun uu___39_303 -> (match (uu___39_303) with
| Int (b) -> begin
b
end
| uu____305 -> begin
(failwith "Impos: expected Int")
end))


let as_string : option_val  ->  Prims.string = (fun uu___40_310 -> (match (uu___40_310) with
| String (b) -> begin
b
end
| Path (b) -> begin
(FStar_Common.try_convert_file_name_to_mixed b)
end
| uu____313 -> begin
(failwith "Impos: expected String")
end))


let as_list' : option_val  ->  option_val Prims.list = (fun uu___41_320 -> (match (uu___41_320) with
| List (ts) -> begin
ts
end
| uu____326 -> begin
(failwith "Impos: expected List")
end))


let as_list : 'Auu____335 . (option_val  ->  'Auu____335)  ->  option_val  ->  'Auu____335 Prims.list = (fun as_t x -> (

let uu____353 = (as_list' x)
in (FStar_All.pipe_right uu____353 (FStar_List.map as_t))))


let as_option : 'Auu____366 . (option_val  ->  'Auu____366)  ->  option_val  ->  'Auu____366 FStar_Pervasives_Native.option = (fun as_t uu___42_381 -> (match (uu___42_381) with
| Unset -> begin
FStar_Pervasives_Native.None
end
| v1 -> begin
(

let uu____385 = (as_t v1)
in FStar_Pervasives_Native.Some (uu____385))
end))


type optionstate =
option_val FStar_Util.smap


let fstar_options : optionstate Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let peek : unit  ->  optionstate = (fun uu____409 -> (

let uu____410 = (FStar_ST.op_Bang fstar_options)
in (FStar_List.hd uu____410)))


let pop : unit  ->  unit = (fun uu____444 -> (

let uu____445 = (FStar_ST.op_Bang fstar_options)
in (match (uu____445) with
| [] -> begin
(failwith "TOO MANY POPS!")
end
| (uu____475)::[] -> begin
(failwith "TOO MANY POPS!")
end
| (uu____476)::tl1 -> begin
(FStar_ST.op_Colon_Equals fstar_options tl1)
end)))


let push : unit  ->  unit = (fun uu____511 -> (

let uu____512 = (

let uu____515 = (

let uu____516 = (peek ())
in (FStar_Util.smap_copy uu____516))
in (

let uu____519 = (FStar_ST.op_Bang fstar_options)
in (uu____515)::uu____519))
in (FStar_ST.op_Colon_Equals fstar_options uu____512)))


let set : optionstate  ->  unit = (fun o -> (

let uu____581 = (FStar_ST.op_Bang fstar_options)
in (match (uu____581) with
| [] -> begin
(failwith "set on empty option stack")
end
| (uu____611)::os -> begin
(FStar_ST.op_Colon_Equals fstar_options ((o)::os))
end)))


let set_option : Prims.string  ->  option_val  ->  unit = (fun k v1 -> (

let uu____652 = (peek ())
in (FStar_Util.smap_add uu____652 k v1)))


let set_option' : (Prims.string * option_val)  ->  unit = (fun uu____663 -> (match (uu____663) with
| (k, v1) -> begin
(set_option k v1)
end))


let with_saved_options : 'a . (unit  ->  'a)  ->  'a = (fun f -> ((push ());
(

let retv = (f ())
in ((pop ());
retv;
));
))


let light_off_files : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let add_light_off_file : Prims.string  ->  unit = (fun filename -> (

let uu____710 = (

let uu____713 = (FStar_ST.op_Bang light_off_files)
in (filename)::uu____713)
in (FStar_ST.op_Colon_Equals light_off_files uu____710)))


let defaults : (Prims.string * option_val) Prims.list = ((("__temp_no_proj"), (List ([]))))::((("__temp_fast_implicits"), (Bool (false))))::((("admit_smt_queries"), (Bool (false))))::((("admit_except"), (Unset)))::((("cache_checked_modules"), (Bool (false))))::((("cache_dir"), (Unset)))::((("codegen"), (Unset)))::((("codegen-lib"), (List ([]))))::((("debug"), (List ([]))))::((("debug_level"), (List ([]))))::((("defensive"), (String ("no"))))::((("dep"), (Unset)))::((("detail_errors"), (Bool (false))))::((("detail_hint_replay"), (Bool (false))))::((("doc"), (Bool (false))))::((("dump_module"), (List ([]))))::((("eager_inference"), (Bool (false))))::((("expose_interfaces"), (Bool (false))))::((("extract"), (Unset)))::((("extract_all"), (Bool (false))))::((("extract_module"), (List ([]))))::((("extract_namespace"), (List ([]))))::((("fs_typ_app"), (Bool (false))))::((("fstar_home"), (Unset)))::((("full_context_dependency"), (Bool (true))))::((("hide_uvar_nums"), (Bool (false))))::((("hint_info"), (Bool (false))))::((("hint_file"), (Unset)))::((("in"), (Bool (false))))::((("ide"), (Bool (false))))::((("include"), (List ([]))))::((("indent"), (Bool (false))))::((("initial_fuel"), (Int ((Prims.parse_int "2")))))::((("initial_ifuel"), (Int ((Prims.parse_int "1")))))::((("lax"), (Bool (false))))::((("load"), (List ([]))))::((("log_queries"), (Bool (false))))::((("log_types"), (Bool (false))))::((("max_fuel"), (Int ((Prims.parse_int "8")))))::((("max_ifuel"), (Int ((Prims.parse_int "2")))))::((("min_fuel"), (Int ((Prims.parse_int "1")))))::((("MLish"), (Bool (false))))::((("n_cores"), (Int ((Prims.parse_int "1")))))::((("no_default_includes"), (Bool (false))))::((("no_extract"), (List ([]))))::((("no_location_info"), (Bool (false))))::((("no_smt"), (Bool (false))))::((("no_tactics"), (Bool (false))))::((("normalize_pure_terms_for_extraction"), (Bool (false))))::((("odir"), (Unset)))::((("prims"), (Unset)))::((("pretype"), (Bool (true))))::((("prims_ref"), (Unset)))::((("print_bound_var_types"), (Bool (false))))::((("print_effect_args"), (Bool (false))))::((("print_full_names"), (Bool (false))))::((("print_implicits"), (Bool (false))))::((("print_universes"), (Bool (false))))::((("print_z3_statistics"), (Bool (false))))::((("prn"), (Bool (false))))::((("query_stats"), (Bool (false))))::((("record_hints"), (Bool (false))))::((("reuse_hint_for"), (Unset)))::((("silent"), (Bool (false))))::((("smt"), (Unset)))::((("smtencoding.elim_box"), (Bool (false))))::((("smtencoding.nl_arith_repr"), (String ("boxwrap"))))::((("smtencoding.l_arith_repr"), (String ("boxwrap"))))::((("tactic_raw_binders"), (Bool (false))))::((("tactic_trace"), (Bool (false))))::((("tactic_trace_d"), (Int ((Prims.parse_int "0")))))::((("timing"), (Bool (false))))::((("trace_error"), (Bool (false))))::((("ugly"), (Bool (false))))::((("unthrottle_inductives"), (Bool (false))))::((("unsafe_tactic_exec"), (Bool (false))))::((("use_native_tactics"), (Unset)))::((("use_eq_at_higher_order"), (Bool (false))))::((("use_hints"), (Bool (false))))::((("use_hint_hashes"), (Bool (false))))::((("using_facts_from"), (Unset)))::((("vcgen.optimize_bind_as_seq"), (Unset)))::((("verify_module"), (List ([]))))::((("warn_default_effects"), (Bool (false))))::((("z3refresh"), (Bool (false))))::((("z3rlimit"), (Int ((Prims.parse_int "5")))))::((("z3rlimit_factor"), (Int ((Prims.parse_int "1")))))::((("z3seed"), (Int ((Prims.parse_int "0")))))::((("z3cliopt"), (List ([]))))::((("use_two_phase_tc"), (Bool (false))))::((("__no_positivity"), (Bool (false))))::((("__ml_no_eta_expand_coertions"), (Bool (false))))::((("warn_error"), (String (""))))::((("use_extracted_interfaces"), (Bool (false))))::[]


let init : unit  ->  unit = (fun uu____1160 -> (

let o = (peek ())
in ((FStar_Util.smap_clear o);
(FStar_All.pipe_right defaults (FStar_List.iter set_option'));
)))


let clear : unit  ->  unit = (fun uu____1177 -> (

let o = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_ST.op_Colon_Equals fstar_options ((o)::[]));
(FStar_ST.op_Colon_Equals light_off_files []);
(init ());
)))


let _run : unit = (clear ())


let get_option : Prims.string  ->  option_val = (fun s -> (

let uu____1242 = (

let uu____1245 = (peek ())
in (FStar_Util.smap_try_find uu____1245 s))
in (match (uu____1242) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Impossible: option " (Prims.strcat s " not found")))
end
| FStar_Pervasives_Native.Some (s1) -> begin
s1
end)))


let lookup_opt : 'Auu____1255 . Prims.string  ->  (option_val  ->  'Auu____1255)  ->  'Auu____1255 = (fun s c -> (

let uu____1271 = (get_option s)
in (c uu____1271)))


let get_admit_smt_queries : unit  ->  Prims.bool = (fun uu____1276 -> (lookup_opt "admit_smt_queries" as_bool))


let get_admit_except : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1283 -> (lookup_opt "admit_except" (as_option as_string)))


let get_cache_checked_modules : unit  ->  Prims.bool = (fun uu____1290 -> (lookup_opt "cache_checked_modules" as_bool))


let get_cache_dir : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1297 -> (lookup_opt "cache_dir" (as_option as_string)))


let get_codegen : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1306 -> (lookup_opt "codegen" (as_option as_string)))


let get_codegen_lib : unit  ->  Prims.string Prims.list = (fun uu____1315 -> (lookup_opt "codegen-lib" (as_list as_string)))


let get_debug : unit  ->  Prims.string Prims.list = (fun uu____1324 -> (lookup_opt "debug" (as_list as_string)))


let get_debug_level : unit  ->  Prims.string Prims.list = (fun uu____1333 -> (lookup_opt "debug_level" (as_list as_string)))


let get_defensive : unit  ->  Prims.string = (fun uu____1340 -> (lookup_opt "defensive" as_string))


let get_dep : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1347 -> (lookup_opt "dep" (as_option as_string)))


let get_detail_errors : unit  ->  Prims.bool = (fun uu____1354 -> (lookup_opt "detail_errors" as_bool))


let get_detail_hint_replay : unit  ->  Prims.bool = (fun uu____1359 -> (lookup_opt "detail_hint_replay" as_bool))


let get_doc : unit  ->  Prims.bool = (fun uu____1364 -> (lookup_opt "doc" as_bool))


let get_dump_module : unit  ->  Prims.string Prims.list = (fun uu____1371 -> (lookup_opt "dump_module" (as_list as_string)))


let get_eager_inference : unit  ->  Prims.bool = (fun uu____1378 -> (lookup_opt "eager_inference" as_bool))


let get_expose_interfaces : unit  ->  Prims.bool = (fun uu____1383 -> (lookup_opt "expose_interfaces" as_bool))


let get_extract : unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____1392 -> (lookup_opt "extract" (as_option (as_list as_string))))


let get_extract_module : unit  ->  Prims.string Prims.list = (fun uu____1405 -> (lookup_opt "extract_module" (as_list as_string)))


let get_extract_namespace : unit  ->  Prims.string Prims.list = (fun uu____1414 -> (lookup_opt "extract_namespace" (as_list as_string)))


let get_fs_typ_app : unit  ->  Prims.bool = (fun uu____1421 -> (lookup_opt "fs_typ_app" as_bool))


let get_fstar_home : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1428 -> (lookup_opt "fstar_home" (as_option as_string)))


let get_hide_uvar_nums : unit  ->  Prims.bool = (fun uu____1435 -> (lookup_opt "hide_uvar_nums" as_bool))


let get_hint_info : unit  ->  Prims.bool = (fun uu____1440 -> (lookup_opt "hint_info" as_bool))


let get_hint_file : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1447 -> (lookup_opt "hint_file" (as_option as_string)))


let get_in : unit  ->  Prims.bool = (fun uu____1454 -> (lookup_opt "in" as_bool))


let get_ide : unit  ->  Prims.bool = (fun uu____1459 -> (lookup_opt "ide" as_bool))


let get_include : unit  ->  Prims.string Prims.list = (fun uu____1466 -> (lookup_opt "include" (as_list as_string)))


let get_indent : unit  ->  Prims.bool = (fun uu____1473 -> (lookup_opt "indent" as_bool))


let get_initial_fuel : unit  ->  Prims.int = (fun uu____1478 -> (lookup_opt "initial_fuel" as_int))


let get_initial_ifuel : unit  ->  Prims.int = (fun uu____1483 -> (lookup_opt "initial_ifuel" as_int))


let get_lax : unit  ->  Prims.bool = (fun uu____1488 -> (lookup_opt "lax" as_bool))


let get_load : unit  ->  Prims.string Prims.list = (fun uu____1495 -> (lookup_opt "load" (as_list as_string)))


let get_log_queries : unit  ->  Prims.bool = (fun uu____1502 -> (lookup_opt "log_queries" as_bool))


let get_log_types : unit  ->  Prims.bool = (fun uu____1507 -> (lookup_opt "log_types" as_bool))


let get_max_fuel : unit  ->  Prims.int = (fun uu____1512 -> (lookup_opt "max_fuel" as_int))


let get_max_ifuel : unit  ->  Prims.int = (fun uu____1517 -> (lookup_opt "max_ifuel" as_int))


let get_min_fuel : unit  ->  Prims.int = (fun uu____1522 -> (lookup_opt "min_fuel" as_int))


let get_MLish : unit  ->  Prims.bool = (fun uu____1527 -> (lookup_opt "MLish" as_bool))


let get_n_cores : unit  ->  Prims.int = (fun uu____1532 -> (lookup_opt "n_cores" as_int))


let get_no_default_includes : unit  ->  Prims.bool = (fun uu____1537 -> (lookup_opt "no_default_includes" as_bool))


let get_no_extract : unit  ->  Prims.string Prims.list = (fun uu____1544 -> (lookup_opt "no_extract" (as_list as_string)))


let get_no_location_info : unit  ->  Prims.bool = (fun uu____1551 -> (lookup_opt "no_location_info" as_bool))


let get_no_smt : unit  ->  Prims.bool = (fun uu____1556 -> (lookup_opt "no_smt" as_bool))


let get_normalize_pure_terms_for_extraction : unit  ->  Prims.bool = (fun uu____1561 -> (lookup_opt "normalize_pure_terms_for_extraction" as_bool))


let get_odir : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1568 -> (lookup_opt "odir" (as_option as_string)))


let get_ugly : unit  ->  Prims.bool = (fun uu____1575 -> (lookup_opt "ugly" as_bool))


let get_prims : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1582 -> (lookup_opt "prims" (as_option as_string)))


let get_print_bound_var_types : unit  ->  Prims.bool = (fun uu____1589 -> (lookup_opt "print_bound_var_types" as_bool))


let get_print_effect_args : unit  ->  Prims.bool = (fun uu____1594 -> (lookup_opt "print_effect_args" as_bool))


let get_print_full_names : unit  ->  Prims.bool = (fun uu____1599 -> (lookup_opt "print_full_names" as_bool))


let get_print_implicits : unit  ->  Prims.bool = (fun uu____1604 -> (lookup_opt "print_implicits" as_bool))


let get_print_universes : unit  ->  Prims.bool = (fun uu____1609 -> (lookup_opt "print_universes" as_bool))


let get_print_z3_statistics : unit  ->  Prims.bool = (fun uu____1614 -> (lookup_opt "print_z3_statistics" as_bool))


let get_prn : unit  ->  Prims.bool = (fun uu____1619 -> (lookup_opt "prn" as_bool))


let get_query_stats : unit  ->  Prims.bool = (fun uu____1624 -> (lookup_opt "query_stats" as_bool))


let get_record_hints : unit  ->  Prims.bool = (fun uu____1629 -> (lookup_opt "record_hints" as_bool))


let get_reuse_hint_for : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1636 -> (lookup_opt "reuse_hint_for" (as_option as_string)))


let get_silent : unit  ->  Prims.bool = (fun uu____1643 -> (lookup_opt "silent" as_bool))


let get_smt : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1650 -> (lookup_opt "smt" (as_option as_string)))


let get_smtencoding_elim_box : unit  ->  Prims.bool = (fun uu____1657 -> (lookup_opt "smtencoding.elim_box" as_bool))


let get_smtencoding_nl_arith_repr : unit  ->  Prims.string = (fun uu____1662 -> (lookup_opt "smtencoding.nl_arith_repr" as_string))


let get_smtencoding_l_arith_repr : unit  ->  Prims.string = (fun uu____1667 -> (lookup_opt "smtencoding.l_arith_repr" as_string))


let get_tactic_raw_binders : unit  ->  Prims.bool = (fun uu____1672 -> (lookup_opt "tactic_raw_binders" as_bool))


let get_tactic_trace : unit  ->  Prims.bool = (fun uu____1677 -> (lookup_opt "tactic_trace" as_bool))


let get_tactic_trace_d : unit  ->  Prims.int = (fun uu____1682 -> (lookup_opt "tactic_trace_d" as_int))


let get_timing : unit  ->  Prims.bool = (fun uu____1687 -> (lookup_opt "timing" as_bool))


let get_trace_error : unit  ->  Prims.bool = (fun uu____1692 -> (lookup_opt "trace_error" as_bool))


let get_unthrottle_inductives : unit  ->  Prims.bool = (fun uu____1697 -> (lookup_opt "unthrottle_inductives" as_bool))


let get_unsafe_tactic_exec : unit  ->  Prims.bool = (fun uu____1702 -> (lookup_opt "unsafe_tactic_exec" as_bool))


let get_use_eq_at_higher_order : unit  ->  Prims.bool = (fun uu____1707 -> (lookup_opt "use_eq_at_higher_order" as_bool))


let get_use_hints : unit  ->  Prims.bool = (fun uu____1712 -> (lookup_opt "use_hints" as_bool))


let get_use_hint_hashes : unit  ->  Prims.bool = (fun uu____1717 -> (lookup_opt "use_hint_hashes" as_bool))


let get_use_native_tactics : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1724 -> (lookup_opt "use_native_tactics" (as_option as_string)))


let get_use_tactics : unit  ->  Prims.bool = (fun uu____1731 -> (

let uu____1732 = (lookup_opt "no_tactics" as_bool)
in (not (uu____1732))))


let get_using_facts_from : unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____1741 -> (lookup_opt "using_facts_from" (as_option (as_list as_string))))


let get_vcgen_optimize_bind_as_seq : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1754 -> (lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)))


let get_verify_module : unit  ->  Prims.string Prims.list = (fun uu____1763 -> (lookup_opt "verify_module" (as_list as_string)))


let get___temp_no_proj : unit  ->  Prims.string Prims.list = (fun uu____1772 -> (lookup_opt "__temp_no_proj" (as_list as_string)))


let get_version : unit  ->  Prims.bool = (fun uu____1779 -> (lookup_opt "version" as_bool))


let get_warn_default_effects : unit  ->  Prims.bool = (fun uu____1784 -> (lookup_opt "warn_default_effects" as_bool))


let get_z3cliopt : unit  ->  Prims.string Prims.list = (fun uu____1791 -> (lookup_opt "z3cliopt" (as_list as_string)))


let get_z3refresh : unit  ->  Prims.bool = (fun uu____1798 -> (lookup_opt "z3refresh" as_bool))


let get_z3rlimit : unit  ->  Prims.int = (fun uu____1803 -> (lookup_opt "z3rlimit" as_int))


let get_z3rlimit_factor : unit  ->  Prims.int = (fun uu____1808 -> (lookup_opt "z3rlimit_factor" as_int))


let get_z3seed : unit  ->  Prims.int = (fun uu____1813 -> (lookup_opt "z3seed" as_int))


let get_use_two_phase_tc : unit  ->  Prims.bool = (fun uu____1818 -> (lookup_opt "use_two_phase_tc" as_bool))


let get_no_positivity : unit  ->  Prims.bool = (fun uu____1823 -> (lookup_opt "__no_positivity" as_bool))


let get_ml_no_eta_expand_coertions : unit  ->  Prims.bool = (fun uu____1828 -> (lookup_opt "__ml_no_eta_expand_coertions" as_bool))


let get_warn_error : unit  ->  Prims.string = (fun uu____1833 -> (lookup_opt "warn_error" as_string))


let get_use_extracted_interfaces : unit  ->  Prims.bool = (fun uu____1838 -> (lookup_opt "use_extracted_interfaces" as_bool))


let dlevel : Prims.string  ->  debug_level_t = (fun uu___43_1843 -> (match (uu___43_1843) with
| "Low" -> begin
Low
end
| "Medium" -> begin
Medium
end
| "High" -> begin
High
end
| "Extreme" -> begin
Extreme
end
| s -> begin
Other (s)
end))


let one_debug_level_geq : debug_level_t  ->  debug_level_t  ->  Prims.bool = (fun l1 l2 -> (match (l1) with
| Other (uu____1855) -> begin
(Prims.op_Equality l1 l2)
end
| Low -> begin
(Prims.op_Equality l1 l2)
end
| Medium -> begin
((Prims.op_Equality l2 Low) || (Prims.op_Equality l2 Medium))
end
| High -> begin
(((Prims.op_Equality l2 Low) || (Prims.op_Equality l2 Medium)) || (Prims.op_Equality l2 High))
end
| Extreme -> begin
((((Prims.op_Equality l2 Low) || (Prims.op_Equality l2 Medium)) || (Prims.op_Equality l2 High)) || (Prims.op_Equality l2 Extreme))
end))


let debug_level_geq : debug_level_t  ->  Prims.bool = (fun l2 -> (

let uu____1861 = (get_debug_level ())
in (FStar_All.pipe_right uu____1861 (FStar_Util.for_some (fun l1 -> (one_debug_level_geq (dlevel l1) l2))))))


let universe_include_path_base_dirs : Prims.string Prims.list = ("/ulib")::("/lib/fstar")::[]


let _version : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _platform : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _compiler : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _date : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _commit : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let display_version : unit  ->  unit = (fun uu____1994 -> (

let uu____1995 = (

let uu____1996 = (FStar_ST.op_Bang _version)
in (

let uu____2020 = (FStar_ST.op_Bang _platform)
in (

let uu____2044 = (FStar_ST.op_Bang _compiler)
in (

let uu____2068 = (FStar_ST.op_Bang _date)
in (

let uu____2092 = (FStar_ST.op_Bang _commit)
in (FStar_Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1996 uu____2020 uu____2044 uu____2068 uu____2092))))))
in (FStar_Util.print_string uu____1995)))


let display_usage_aux : 'Auu____2122 'Auu____2123 . ('Auu____2122 * Prims.string * 'Auu____2123 FStar_Getopt.opt_variant * Prims.string) Prims.list  ->  unit = (fun specs -> ((FStar_Util.print_string "fstar.exe [options] file[s]\n");
(FStar_List.iter (fun uu____2171 -> (match (uu____2171) with
| (uu____2182, flag, p, doc) -> begin
(match (p) with
| FStar_Getopt.ZeroArgs (ig) -> begin
(match ((Prims.op_Equality doc "")) with
| true -> begin
(

let uu____2194 = (

let uu____2195 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format1 "  --%s\n" uu____2195))
in (FStar_Util.print_string uu____2194))
end
| uu____2196 -> begin
(

let uu____2197 = (

let uu____2198 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format2 "  --%s  %s\n" uu____2198 doc))
in (FStar_Util.print_string uu____2197))
end)
end
| FStar_Getopt.OneArg (uu____2199, argname) -> begin
(match ((Prims.op_Equality doc "")) with
| true -> begin
(

let uu____2207 = (

let uu____2208 = (FStar_Util.colorize_bold flag)
in (

let uu____2209 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format2 "  --%s %s\n" uu____2208 uu____2209)))
in (FStar_Util.print_string uu____2207))
end
| uu____2210 -> begin
(

let uu____2211 = (

let uu____2212 = (FStar_Util.colorize_bold flag)
in (

let uu____2213 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format3 "  --%s %s  %s\n" uu____2212 uu____2213 doc)))
in (FStar_Util.print_string uu____2211))
end)
end)
end)) specs);
))


let mk_spec : (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant * Prims.string)  ->  FStar_Getopt.opt = (fun o -> (

let uu____2239 = o
in (match (uu____2239) with
| (ns, name, arg, desc) -> begin
(

let arg1 = (match (arg) with
| FStar_Getopt.ZeroArgs (f) -> begin
(

let g = (fun uu____2272 -> (

let uu____2273 = (f ())
in (set_option name uu____2273)))
in FStar_Getopt.ZeroArgs (g))
end
| FStar_Getopt.OneArg (f, d) -> begin
(

let g = (fun x -> (

let uu____2288 = (f x)
in (set_option name uu____2288)))
in FStar_Getopt.OneArg (((g), (d))))
end)
in ((ns), (name), (arg1), (desc)))
end)))


let accumulated_option : Prims.string  ->  option_val  ->  option_val = (fun name value -> (

let prev_values = (

let uu____2307 = (lookup_opt name (as_option as_list'))
in (FStar_Util.dflt [] uu____2307))
in (mk_list ((value)::prev_values))))


let reverse_accumulated_option : Prims.string  ->  option_val  ->  option_val = (fun name value -> (

let uu____2330 = (

let uu____2333 = (lookup_opt name as_list')
in (FStar_List.append uu____2333 ((value)::[])))
in (mk_list uu____2330)))


let accumulate_string : 'Auu____2346 . Prims.string  ->  ('Auu____2346  ->  Prims.string)  ->  'Auu____2346  ->  unit = (fun name post_processor value -> (

let uu____2367 = (

let uu____2368 = (

let uu____2369 = (post_processor value)
in (mk_string uu____2369))
in (accumulated_option name uu____2368))
in (set_option name uu____2367)))


let add_extract_module : Prims.string  ->  unit = (fun s -> (accumulate_string "extract_module" FStar_String.lowercase s))


let add_extract_namespace : Prims.string  ->  unit = (fun s -> (accumulate_string "extract_namespace" FStar_String.lowercase s))


let add_verify_module : Prims.string  ->  unit = (fun s -> (accumulate_string "verify_module" FStar_String.lowercase s))

type opt_type =
| Const of option_val
| IntStr of Prims.string
| BoolStr
| PathStr of Prims.string
| SimpleStr of Prims.string
| EnumStr of Prims.string Prims.list
| OpenEnumStr of (Prims.string Prims.list * Prims.string)
| PostProcessed of ((option_val  ->  option_val) * opt_type)
| Accumulated of opt_type
| ReverseAccumulated of opt_type
| WithSideEffect of ((unit  ->  unit) * opt_type)


let uu___is_Const : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const (_0) -> begin
true
end
| uu____2465 -> begin
false
end))


let __proj__Const__item___0 : opt_type  ->  option_val = (fun projectee -> (match (projectee) with
| Const (_0) -> begin
_0
end))


let uu___is_IntStr : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| IntStr (_0) -> begin
true
end
| uu____2479 -> begin
false
end))


let __proj__IntStr__item___0 : opt_type  ->  Prims.string = (fun projectee -> (match (projectee) with
| IntStr (_0) -> begin
_0
end))


let uu___is_BoolStr : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| BoolStr -> begin
true
end
| uu____2492 -> begin
false
end))


let uu___is_PathStr : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PathStr (_0) -> begin
true
end
| uu____2499 -> begin
false
end))


let __proj__PathStr__item___0 : opt_type  ->  Prims.string = (fun projectee -> (match (projectee) with
| PathStr (_0) -> begin
_0
end))


let uu___is_SimpleStr : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SimpleStr (_0) -> begin
true
end
| uu____2513 -> begin
false
end))


let __proj__SimpleStr__item___0 : opt_type  ->  Prims.string = (fun projectee -> (match (projectee) with
| SimpleStr (_0) -> begin
_0
end))


let uu___is_EnumStr : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EnumStr (_0) -> begin
true
end
| uu____2529 -> begin
false
end))


let __proj__EnumStr__item___0 : opt_type  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| EnumStr (_0) -> begin
_0
end))


let uu___is_OpenEnumStr : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OpenEnumStr (_0) -> begin
true
end
| uu____2555 -> begin
false
end))


let __proj__OpenEnumStr__item___0 : opt_type  ->  (Prims.string Prims.list * Prims.string) = (fun projectee -> (match (projectee) with
| OpenEnumStr (_0) -> begin
_0
end))


let uu___is_PostProcessed : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PostProcessed (_0) -> begin
true
end
| uu____2594 -> begin
false
end))


let __proj__PostProcessed__item___0 : opt_type  ->  ((option_val  ->  option_val) * opt_type) = (fun projectee -> (match (projectee) with
| PostProcessed (_0) -> begin
_0
end))


let uu___is_Accumulated : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Accumulated (_0) -> begin
true
end
| uu____2629 -> begin
false
end))


let __proj__Accumulated__item___0 : opt_type  ->  opt_type = (fun projectee -> (match (projectee) with
| Accumulated (_0) -> begin
_0
end))


let uu___is_ReverseAccumulated : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ReverseAccumulated (_0) -> begin
true
end
| uu____2643 -> begin
false
end))


let __proj__ReverseAccumulated__item___0 : opt_type  ->  opt_type = (fun projectee -> (match (projectee) with
| ReverseAccumulated (_0) -> begin
_0
end))


let uu___is_WithSideEffect : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| WithSideEffect (_0) -> begin
true
end
| uu____2664 -> begin
false
end))


let __proj__WithSideEffect__item___0 : opt_type  ->  ((unit  ->  unit) * opt_type) = (fun projectee -> (match (projectee) with
| WithSideEffect (_0) -> begin
_0
end))

exception InvalidArgument of (Prims.string)


let uu___is_InvalidArgument : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidArgument (uu____2702) -> begin
true
end
| uu____2703 -> begin
false
end))


let __proj__InvalidArgument__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidArgument (uu____2710) -> begin
uu____2710
end))


let rec parse_opt_val : Prims.string  ->  opt_type  ->  Prims.string  ->  option_val = (fun opt_name typ str_val -> (FStar_All.try_with (fun uu___47_2728 -> (match (()) with
| () -> begin
(match (typ) with
| Const (c) -> begin
c
end
| IntStr (uu____2730) -> begin
(

let uu____2731 = (FStar_Util.safe_int_of_string str_val)
in (match (uu____2731) with
| FStar_Pervasives_Native.Some (v1) -> begin
(mk_int v1)
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end))
end
| BoolStr -> begin
(

let uu____2735 = (match ((Prims.op_Equality str_val "true")) with
| true -> begin
true
end
| uu____2736 -> begin
(match ((Prims.op_Equality str_val "false")) with
| true -> begin
false
end
| uu____2737 -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end)
end)
in (mk_bool uu____2735))
end
| PathStr (uu____2738) -> begin
(mk_path str_val)
end
| SimpleStr (uu____2739) -> begin
(mk_string str_val)
end
| EnumStr (strs) -> begin
(match ((FStar_List.mem str_val strs)) with
| true -> begin
(mk_string str_val)
end
| uu____2743 -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end)
end
| OpenEnumStr (uu____2744) -> begin
(mk_string str_val)
end
| PostProcessed (pp, elem_spec) -> begin
(

let uu____2759 = (parse_opt_val opt_name elem_spec str_val)
in (pp uu____2759))
end
| Accumulated (elem_spec) -> begin
(

let v1 = (parse_opt_val opt_name elem_spec str_val)
in (accumulated_option opt_name v1))
end
| ReverseAccumulated (elem_spec) -> begin
(

let v1 = (parse_opt_val opt_name elem_spec str_val)
in (reverse_accumulated_option opt_name v1))
end
| WithSideEffect (side_effect, elem_spec) -> begin
((side_effect ());
(parse_opt_val opt_name elem_spec str_val);
)
end)
end)) (fun uu___46_2776 -> (match (uu___46_2776) with
| InvalidArgument (opt_name1) -> begin
(

let uu____2778 = (FStar_Util.format1 "Invalid argument to --%s" opt_name1)
in (failwith uu____2778))
end))))


let rec desc_of_opt_type : opt_type  ->  Prims.string FStar_Pervasives_Native.option = (fun typ -> (

let desc_of_enum = (fun cases -> FStar_Pervasives_Native.Some ((Prims.strcat "[" (Prims.strcat (FStar_String.concat "|" cases) "]"))))
in (match (typ) with
| Const (c) -> begin
FStar_Pervasives_Native.None
end
| IntStr (desc) -> begin
FStar_Pervasives_Native.Some (desc)
end
| BoolStr -> begin
(desc_of_enum (("true")::("false")::[]))
end
| PathStr (desc) -> begin
FStar_Pervasives_Native.Some (desc)
end
| SimpleStr (desc) -> begin
FStar_Pervasives_Native.Some (desc)
end
| EnumStr (strs) -> begin
(desc_of_enum strs)
end
| OpenEnumStr (strs, desc) -> begin
(desc_of_enum (FStar_List.append strs ((desc)::[])))
end
| PostProcessed (uu____2815, elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| Accumulated (elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| ReverseAccumulated (elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| WithSideEffect (uu____2825, elem_spec) -> begin
(desc_of_opt_type elem_spec)
end)))


let rec arg_spec_of_opt_type : Prims.string  ->  opt_type  ->  option_val FStar_Getopt.opt_variant = (fun opt_name typ -> (

let parser = (parse_opt_val opt_name typ)
in (

let uu____2852 = (desc_of_opt_type typ)
in (match (uu____2852) with
| FStar_Pervasives_Native.None -> begin
FStar_Getopt.ZeroArgs ((fun uu____2858 -> (parser "")))
end
| FStar_Pervasives_Native.Some (desc) -> begin
FStar_Getopt.OneArg (((parser), (desc)))
end))))


let pp_validate_dir : option_val  ->  option_val = (fun p -> (

let pp = (as_string p)
in ((FStar_Util.mkdir false pp);
p;
)))


let pp_lowercase : option_val  ->  option_val = (fun s -> (

let uu____2875 = (

let uu____2876 = (as_string s)
in (FStar_String.lowercase uu____2876))
in (mk_string uu____2875)))


let rec specs_with_types : unit  ->  (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list = (fun uu____2897 -> (

let uu____2908 = (

let uu____2919 = (

let uu____2930 = (

let uu____2939 = (

let uu____2940 = (mk_bool true)
in Const (uu____2940))
in ((FStar_Getopt.noshort), ("cache_checked_modules"), (uu____2939), ("Write a \'.checked\' file for each module after verification and read from it if present, instead of re-verifying")))
in (

let uu____2941 = (

let uu____2952 = (

let uu____2963 = (

let uu____2974 = (

let uu____2985 = (

let uu____2996 = (

let uu____3007 = (

let uu____3018 = (

let uu____3029 = (

let uu____3038 = (

let uu____3039 = (mk_bool true)
in Const (uu____3039))
in ((FStar_Getopt.noshort), ("detail_errors"), (uu____3038), ("Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")))
in (

let uu____3040 = (

let uu____3051 = (

let uu____3060 = (

let uu____3061 = (mk_bool true)
in Const (uu____3061))
in ((FStar_Getopt.noshort), ("detail_hint_replay"), (uu____3060), ("Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")))
in (

let uu____3062 = (

let uu____3073 = (

let uu____3082 = (

let uu____3083 = (mk_bool true)
in Const (uu____3083))
in ((FStar_Getopt.noshort), ("doc"), (uu____3082), ("Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")))
in (

let uu____3084 = (

let uu____3095 = (

let uu____3106 = (

let uu____3115 = (

let uu____3116 = (mk_bool true)
in Const (uu____3116))
in ((FStar_Getopt.noshort), ("eager_inference"), (uu____3115), ("Solve all type-inference constraints eagerly; more efficient but at the cost of generality")))
in (

let uu____3117 = (

let uu____3128 = (

let uu____3139 = (

let uu____3150 = (

let uu____3161 = (

let uu____3170 = (

let uu____3171 = (mk_bool true)
in Const (uu____3171))
in ((FStar_Getopt.noshort), ("expose_interfaces"), (uu____3170), ("Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")))
in (

let uu____3172 = (

let uu____3183 = (

let uu____3194 = (

let uu____3203 = (

let uu____3204 = (mk_bool true)
in Const (uu____3204))
in ((FStar_Getopt.noshort), ("hide_uvar_nums"), (uu____3203), ("Don\'t print unification variable numbers")))
in (

let uu____3205 = (

let uu____3216 = (

let uu____3227 = (

let uu____3236 = (

let uu____3237 = (mk_bool true)
in Const (uu____3237))
in ((FStar_Getopt.noshort), ("hint_info"), (uu____3236), ("Print information regarding hints (deprecated; use --query_stats instead)")))
in (

let uu____3238 = (

let uu____3249 = (

let uu____3258 = (

let uu____3259 = (mk_bool true)
in Const (uu____3259))
in ((FStar_Getopt.noshort), ("in"), (uu____3258), ("Legacy interactive mode; reads input from stdin")))
in (

let uu____3260 = (

let uu____3271 = (

let uu____3280 = (

let uu____3281 = (mk_bool true)
in Const (uu____3281))
in ((FStar_Getopt.noshort), ("ide"), (uu____3280), ("JSON-based interactive mode for IDEs")))
in (

let uu____3282 = (

let uu____3293 = (

let uu____3304 = (

let uu____3313 = (

let uu____3314 = (mk_bool true)
in Const (uu____3314))
in ((FStar_Getopt.noshort), ("indent"), (uu____3313), ("Parses and outputs the files on the command line")))
in (

let uu____3315 = (

let uu____3326 = (

let uu____3337 = (

let uu____3348 = (

let uu____3357 = (

let uu____3358 = (mk_bool true)
in Const (uu____3358))
in ((FStar_Getopt.noshort), ("lax"), (uu____3357), ("Run the lax-type checker only (admit all verification conditions)")))
in (

let uu____3359 = (

let uu____3370 = (

let uu____3381 = (

let uu____3390 = (

let uu____3391 = (mk_bool true)
in Const (uu____3391))
in ((FStar_Getopt.noshort), ("log_types"), (uu____3390), ("Print types computed for data/val/let-bindings")))
in (

let uu____3392 = (

let uu____3403 = (

let uu____3412 = (

let uu____3413 = (mk_bool true)
in Const (uu____3413))
in ((FStar_Getopt.noshort), ("log_queries"), (uu____3412), ("Log the Z3 queries in several queries-*.smt2 files, as we go")))
in (

let uu____3414 = (

let uu____3425 = (

let uu____3436 = (

let uu____3447 = (

let uu____3458 = (

let uu____3467 = (

let uu____3468 = (mk_bool true)
in Const (uu____3468))
in ((FStar_Getopt.noshort), ("MLish"), (uu____3467), ("Trigger various specializations for compiling the F* compiler itself (not meant for user code)")))
in (

let uu____3469 = (

let uu____3480 = (

let uu____3491 = (

let uu____3500 = (

let uu____3501 = (mk_bool true)
in Const (uu____3501))
in ((FStar_Getopt.noshort), ("no_default_includes"), (uu____3500), ("Ignore the default module search paths")))
in (

let uu____3502 = (

let uu____3513 = (

let uu____3524 = (

let uu____3533 = (

let uu____3534 = (mk_bool true)
in Const (uu____3534))
in ((FStar_Getopt.noshort), ("no_location_info"), (uu____3533), ("Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")))
in (

let uu____3535 = (

let uu____3546 = (

let uu____3555 = (

let uu____3556 = (mk_bool true)
in Const (uu____3556))
in ((FStar_Getopt.noshort), ("no_smt"), (uu____3555), ("Do not send any queries to the SMT solver, and fail on them instead")))
in (

let uu____3557 = (

let uu____3568 = (

let uu____3577 = (

let uu____3578 = (mk_bool true)
in Const (uu____3578))
in ((FStar_Getopt.noshort), ("normalize_pure_terms_for_extraction"), (uu____3577), ("Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")))
in (

let uu____3579 = (

let uu____3590 = (

let uu____3601 = (

let uu____3612 = (

let uu____3621 = (

let uu____3622 = (mk_bool true)
in Const (uu____3622))
in ((FStar_Getopt.noshort), ("print_bound_var_types"), (uu____3621), ("Print the types of bound variables")))
in (

let uu____3623 = (

let uu____3634 = (

let uu____3643 = (

let uu____3644 = (mk_bool true)
in Const (uu____3644))
in ((FStar_Getopt.noshort), ("print_effect_args"), (uu____3643), ("Print inferred predicate transformers for all computation types")))
in (

let uu____3645 = (

let uu____3656 = (

let uu____3665 = (

let uu____3666 = (mk_bool true)
in Const (uu____3666))
in ((FStar_Getopt.noshort), ("print_full_names"), (uu____3665), ("Print full names of variables")))
in (

let uu____3667 = (

let uu____3678 = (

let uu____3687 = (

let uu____3688 = (mk_bool true)
in Const (uu____3688))
in ((FStar_Getopt.noshort), ("print_implicits"), (uu____3687), ("Print implicit arguments")))
in (

let uu____3689 = (

let uu____3700 = (

let uu____3709 = (

let uu____3710 = (mk_bool true)
in Const (uu____3710))
in ((FStar_Getopt.noshort), ("print_universes"), (uu____3709), ("Print universes")))
in (

let uu____3711 = (

let uu____3722 = (

let uu____3731 = (

let uu____3732 = (mk_bool true)
in Const (uu____3732))
in ((FStar_Getopt.noshort), ("print_z3_statistics"), (uu____3731), ("Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")))
in (

let uu____3733 = (

let uu____3744 = (

let uu____3753 = (

let uu____3754 = (mk_bool true)
in Const (uu____3754))
in ((FStar_Getopt.noshort), ("prn"), (uu____3753), ("Print full names (deprecated; use --print_full_names instead)")))
in (

let uu____3755 = (

let uu____3766 = (

let uu____3775 = (

let uu____3776 = (mk_bool true)
in Const (uu____3776))
in ((FStar_Getopt.noshort), ("query_stats"), (uu____3775), ("Print SMT query statistics")))
in (

let uu____3777 = (

let uu____3788 = (

let uu____3797 = (

let uu____3798 = (mk_bool true)
in Const (uu____3798))
in ((FStar_Getopt.noshort), ("record_hints"), (uu____3797), ("Record a database of hints for efficient proof replay")))
in (

let uu____3799 = (

let uu____3810 = (

let uu____3821 = (

let uu____3830 = (

let uu____3831 = (mk_bool true)
in Const (uu____3831))
in ((FStar_Getopt.noshort), ("silent"), (uu____3830), (" ")))
in (

let uu____3832 = (

let uu____3843 = (

let uu____3854 = (

let uu____3865 = (

let uu____3876 = (

let uu____3887 = (

let uu____3896 = (

let uu____3897 = (mk_bool true)
in Const (uu____3897))
in ((FStar_Getopt.noshort), ("tactic_raw_binders"), (uu____3896), ("Do not use the lexical scope of tactics to improve binder names")))
in (

let uu____3898 = (

let uu____3909 = (

let uu____3918 = (

let uu____3919 = (mk_bool true)
in Const (uu____3919))
in ((FStar_Getopt.noshort), ("tactic_trace"), (uu____3918), ("Print a depth-indexed trace of tactic execution (Warning: very verbose)")))
in (

let uu____3920 = (

let uu____3931 = (

let uu____3942 = (

let uu____3951 = (

let uu____3952 = (mk_bool true)
in Const (uu____3952))
in ((FStar_Getopt.noshort), ("timing"), (uu____3951), ("Print the time it takes to verify each top-level definition")))
in (

let uu____3953 = (

let uu____3964 = (

let uu____3973 = (

let uu____3974 = (mk_bool true)
in Const (uu____3974))
in ((FStar_Getopt.noshort), ("trace_error"), (uu____3973), ("Don\'t print an error message; show an exception trace instead")))
in (

let uu____3975 = (

let uu____3986 = (

let uu____3995 = (

let uu____3996 = (mk_bool true)
in Const (uu____3996))
in ((FStar_Getopt.noshort), ("ugly"), (uu____3995), ("Emit output formatted for debugging")))
in (

let uu____3997 = (

let uu____4008 = (

let uu____4017 = (

let uu____4018 = (mk_bool true)
in Const (uu____4018))
in ((FStar_Getopt.noshort), ("unthrottle_inductives"), (uu____4017), ("Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")))
in (

let uu____4019 = (

let uu____4030 = (

let uu____4039 = (

let uu____4040 = (mk_bool true)
in Const (uu____4040))
in ((FStar_Getopt.noshort), ("unsafe_tactic_exec"), (uu____4039), ("Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")))
in (

let uu____4041 = (

let uu____4052 = (

let uu____4061 = (

let uu____4062 = (mk_bool true)
in Const (uu____4062))
in ((FStar_Getopt.noshort), ("use_eq_at_higher_order"), (uu____4061), ("Use equality constraints when comparing higher-order types (Temporary)")))
in (

let uu____4063 = (

let uu____4074 = (

let uu____4083 = (

let uu____4084 = (mk_bool true)
in Const (uu____4084))
in ((FStar_Getopt.noshort), ("use_hints"), (uu____4083), ("Use a previously recorded hints database for proof replay")))
in (

let uu____4085 = (

let uu____4096 = (

let uu____4105 = (

let uu____4106 = (mk_bool true)
in Const (uu____4106))
in ((FStar_Getopt.noshort), ("use_hint_hashes"), (uu____4105), ("Admit queries if their hash matches the hash recorded in the hints database")))
in (

let uu____4107 = (

let uu____4118 = (

let uu____4129 = (

let uu____4138 = (

let uu____4139 = (mk_bool true)
in Const (uu____4139))
in ((FStar_Getopt.noshort), ("no_tactics"), (uu____4138), ("Do not run the tactic engine before discharging a VC")))
in (

let uu____4140 = (

let uu____4151 = (

let uu____4162 = (

let uu____4173 = (

let uu____4184 = (

let uu____4193 = (

let uu____4194 = (mk_bool true)
in Const (uu____4194))
in ((FStar_Getopt.noshort), ("__temp_fast_implicits"), (uu____4193), ("Don\'t use this option yet")))
in (

let uu____4195 = (

let uu____4206 = (

let uu____4215 = (

let uu____4216 = (

let uu____4224 = (

let uu____4225 = (mk_bool true)
in Const (uu____4225))
in (((fun uu____4231 -> ((display_version ());
(FStar_All.exit (Prims.parse_int "0"));
))), (uu____4224)))
in WithSideEffect (uu____4216))
in ((118 (*v*)), ("version"), (uu____4215), ("Display version number")))
in (

let uu____4234 = (

let uu____4245 = (

let uu____4254 = (

let uu____4255 = (mk_bool true)
in Const (uu____4255))
in ((FStar_Getopt.noshort), ("warn_default_effects"), (uu____4254), ("Warn when (a -> b) is desugared to (a -> Tot b)")))
in (

let uu____4256 = (

let uu____4267 = (

let uu____4278 = (

let uu____4287 = (

let uu____4288 = (mk_bool true)
in Const (uu____4288))
in ((FStar_Getopt.noshort), ("z3refresh"), (uu____4287), ("Restart Z3 after each query; useful for ensuring proof robustness")))
in (

let uu____4289 = (

let uu____4300 = (

let uu____4311 = (

let uu____4322 = (

let uu____4333 = (

let uu____4344 = (

let uu____4353 = (

let uu____4354 = (mk_bool true)
in Const (uu____4354))
in ((FStar_Getopt.noshort), ("__no_positivity"), (uu____4353), ("Don\'t check positivity of inductive types")))
in (

let uu____4355 = (

let uu____4366 = (

let uu____4375 = (

let uu____4376 = (mk_bool true)
in Const (uu____4376))
in ((FStar_Getopt.noshort), ("__ml_no_eta_expand_coertions"), (uu____4375), ("Do not eta-expand coertions in generated OCaml")))
in (

let uu____4377 = (

let uu____4388 = (

let uu____4399 = (

let uu____4408 = (

let uu____4409 = (mk_bool true)
in Const (uu____4409))
in ((FStar_Getopt.noshort), ("use_extracted_interfaces"), (uu____4408), ("Extract interfaces from the dependencies and use them for verification")))
in (

let uu____4410 = (

let uu____4421 = (

let uu____4430 = (

let uu____4431 = (

let uu____4439 = (

let uu____4440 = (mk_bool true)
in Const (uu____4440))
in (((fun uu____4446 -> ((

let uu____4448 = (specs ())
in (display_usage_aux uu____4448));
(FStar_All.exit (Prims.parse_int "0"));
))), (uu____4439)))
in WithSideEffect (uu____4431))
in ((104 (*h*)), ("help"), (uu____4430), ("Display this information")))
in (uu____4421)::[])
in (uu____4399)::uu____4410))
in (((FStar_Getopt.noshort), ("warn_error"), (SimpleStr ("")), ("The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")))::uu____4388)
in (uu____4366)::uu____4377))
in (uu____4344)::uu____4355))
in (((FStar_Getopt.noshort), ("use_two_phase_tc"), (BoolStr), ("Use the two phase typechecker (default \'false\')")))::uu____4333)
in (((FStar_Getopt.noshort), ("z3seed"), (IntStr ("positive_integer")), ("Set the Z3 random seed (default 0)")))::uu____4322)
in (((FStar_Getopt.noshort), ("z3rlimit_factor"), (IntStr ("positive_integer")), ("Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")))::uu____4311)
in (((FStar_Getopt.noshort), ("z3rlimit"), (IntStr ("positive_integer")), ("Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")))::uu____4300)
in (uu____4278)::uu____4289))
in (((FStar_Getopt.noshort), ("z3cliopt"), (ReverseAccumulated (SimpleStr ("option"))), ("Z3 command line options")))::uu____4267)
in (uu____4245)::uu____4256))
in (uu____4206)::uu____4234))
in (uu____4184)::uu____4195))
in (((FStar_Getopt.noshort), ("__temp_no_proj"), (Accumulated (SimpleStr ("module_name"))), ("Don\'t generate projectors for this module")))::uu____4173)
in (((FStar_Getopt.noshort), ("vcgen.optimize_bind_as_seq"), (EnumStr (("off")::("without_type")::("with_type")::[])), ("\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")))::uu____4162)
in (((FStar_Getopt.noshort), ("using_facts_from"), (Accumulated (SimpleStr ("One or more space-separated occurrences of \'[+|-]( * | namespace | fact id)\'"))), ("\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from \'* -FStar.Reflection +FStar.List -FStar.List.Tot\' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the \'+\' is optional: --using_facts_from \'FStar.List\' is equivalent to --using_facts_from \'+FStar.List\'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")))::uu____4151)
in (uu____4129)::uu____4140))
in (((FStar_Getopt.noshort), ("use_native_tactics"), (PathStr ("path")), ("Use compiled tactics from <path>")))::uu____4118)
in (uu____4096)::uu____4107))
in (uu____4074)::uu____4085))
in (uu____4052)::uu____4063))
in (uu____4030)::uu____4041))
in (uu____4008)::uu____4019))
in (uu____3986)::uu____3997))
in (uu____3964)::uu____3975))
in (uu____3942)::uu____3953))
in (((FStar_Getopt.noshort), ("tactic_trace_d"), (IntStr ("positive_integer")), ("Trace tactics up to a certain binding depth")))::uu____3931)
in (uu____3909)::uu____3920))
in (uu____3887)::uu____3898))
in (((FStar_Getopt.noshort), ("smtencoding.l_arith_repr"), (EnumStr (("native")::("boxwrap")::[])), ("Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if \'boxwrap\', use \'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus\'; \n\t\tif \'native\', use \'+, -, -\'; \n\t\t(default \'boxwrap\')")))::uu____3876)
in (((FStar_Getopt.noshort), ("smtencoding.nl_arith_repr"), (EnumStr (("native")::("wrapped")::("boxwrap")::[])), ("Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if \'boxwrap\' use \'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus\'; \n\t\tif \'native\' use \'*, div, mod\';\n\t\tif \'wrapped\' use \'_mul, _div, _mod : Int*Int -> Int\'; \n\t\t(default \'boxwrap\')")))::uu____3865)
in (((FStar_Getopt.noshort), ("smtencoding.elim_box"), (BoolStr), ("Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default \'false\')")))::uu____3854)
in (((FStar_Getopt.noshort), ("smt"), (PathStr ("path")), ("Path to the Z3 SMT solver (we could eventually support other solvers)")))::uu____3843)
in (uu____3821)::uu____3832))
in (((FStar_Getopt.noshort), ("reuse_hint_for"), (SimpleStr ("toplevel_name")), ("Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term \'g\'")))::uu____3810)
in (uu____3788)::uu____3799))
in (uu____3766)::uu____3777))
in (uu____3744)::uu____3755))
in (uu____3722)::uu____3733))
in (uu____3700)::uu____3711))
in (uu____3678)::uu____3689))
in (uu____3656)::uu____3667))
in (uu____3634)::uu____3645))
in (uu____3612)::uu____3623))
in (((FStar_Getopt.noshort), ("prims"), (PathStr ("file")), ("")))::uu____3601)
in (((FStar_Getopt.noshort), ("odir"), (PostProcessed (((pp_validate_dir), (PathStr ("dir"))))), ("Place output in directory <dir>")))::uu____3590)
in (uu____3568)::uu____3579))
in (uu____3546)::uu____3557))
in (uu____3524)::uu____3535))
in (((FStar_Getopt.noshort), ("no_extract"), (Accumulated (PathStr ("module name"))), ("Deprecated: use --extract instead; Do not extract code from this module")))::uu____3513)
in (uu____3491)::uu____3502))
in (((FStar_Getopt.noshort), ("n_cores"), (IntStr ("positive_integer")), ("Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")))::uu____3480)
in (uu____3458)::uu____3469))
in (((FStar_Getopt.noshort), ("min_fuel"), (IntStr ("non-negative integer")), ("Minimum number of unrolling of recursive functions to try (default 1)")))::uu____3447)
in (((FStar_Getopt.noshort), ("max_ifuel"), (IntStr ("non-negative integer")), ("Number of unrolling of inductive datatypes to try at most (default 2)")))::uu____3436)
in (((FStar_Getopt.noshort), ("max_fuel"), (IntStr ("non-negative integer")), ("Number of unrolling of recursive functions to try at most (default 8)")))::uu____3425)
in (uu____3403)::uu____3414))
in (uu____3381)::uu____3392))
in (((FStar_Getopt.noshort), ("load"), (ReverseAccumulated (PathStr ("module"))), ("Load compiled module")))::uu____3370)
in (uu____3348)::uu____3359))
in (((FStar_Getopt.noshort), ("initial_ifuel"), (IntStr ("non-negative integer")), ("Number of unrolling of inductive datatypes to try at first (default 1)")))::uu____3337)
in (((FStar_Getopt.noshort), ("initial_fuel"), (IntStr ("non-negative integer")), ("Number of unrolling of recursive functions to try initially (default 2)")))::uu____3326)
in (uu____3304)::uu____3315))
in (((FStar_Getopt.noshort), ("include"), (ReverseAccumulated (PathStr ("path"))), ("A directory in which to search for files included on the command line")))::uu____3293)
in (uu____3271)::uu____3282))
in (uu____3249)::uu____3260))
in (uu____3227)::uu____3238))
in (((FStar_Getopt.noshort), ("hint_file"), (PathStr ("path")), ("Read/write hints to <path> (instead of module-specific hints files)")))::uu____3216)
in (uu____3194)::uu____3205))
in (((FStar_Getopt.noshort), ("fstar_home"), (PathStr ("dir")), ("Set the FSTAR_HOME variable to <dir>")))::uu____3183)
in (uu____3161)::uu____3172))
in (((FStar_Getopt.noshort), ("extract_namespace"), (Accumulated (PostProcessed (((pp_lowercase), (SimpleStr ("namespace name")))))), ("Deprecated: use --extract instead; Only extract modules in the specified namespace")))::uu____3150)
in (((FStar_Getopt.noshort), ("extract_module"), (Accumulated (PostProcessed (((pp_lowercase), (SimpleStr ("module_name")))))), ("Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")))::uu____3139)
in (((FStar_Getopt.noshort), ("extract"), (Accumulated (SimpleStr ("One or more space-separated occurrences of \'[+|-]( * | namespace | module)\'"))), ("\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract \'* -FStar.Reflection +FStar.List -FStar.List.Tot\' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the \'+\' is optional: --extract \'+A\' and --extract \'A\' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract \'A B\'.")))::uu____3128)
in (uu____3106)::uu____3117))
in (((FStar_Getopt.noshort), ("dump_module"), (Accumulated (SimpleStr ("module_name"))), ("")))::uu____3095)
in (uu____3073)::uu____3084))
in (uu____3051)::uu____3062))
in (uu____3029)::uu____3040))
in (((FStar_Getopt.noshort), ("dep"), (EnumStr (("make")::("graph")::("full")::[])), ("Output the transitive closure of the full dependency graph in three formats:\n\t \'graph\': a format suitable the \'dot\' tool from \'GraphViz\'\n\t \'full\': a format suitable for \'make\', including dependences for producing .ml and .krml files\n\t \'make\': (deprecated) a format suitable for \'make\', including only dependences among source files")))::uu____3018)
in (((FStar_Getopt.noshort), ("defensive"), (EnumStr (("no")::("warn")::("fail")::[])), ("Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif \'no\', no checks are performed\n\t\tif \'warn\', checks are performed and raise a warning when they fail\n\t\tif \'fail\', like \'warn\', but the compiler aborts instead of issuing a warning\n\t\t(default \'no\')")))::uu____3007)
in (((FStar_Getopt.noshort), ("debug_level"), (Accumulated (OpenEnumStr (((("Low")::("Medium")::("High")::("Extreme")::[]), ("..."))))), ("Control the verbosity of debugging info")))::uu____2996)
in (((FStar_Getopt.noshort), ("debug"), (Accumulated (SimpleStr ("module_name"))), ("Print lots of debugging information while checking module")))::uu____2985)
in (((FStar_Getopt.noshort), ("codegen-lib"), (Accumulated (SimpleStr ("namespace"))), ("External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")))::uu____2974)
in (((FStar_Getopt.noshort), ("codegen"), (EnumStr (("OCaml")::("FSharp")::("Kremlin")::("Plugin")::[])), ("Generate code for further compilation to executable code, or build a compiler plugin")))::uu____2963)
in (((FStar_Getopt.noshort), ("cache_dir"), (PostProcessed (((pp_validate_dir), (PathStr ("dir"))))), ("Read and write .checked and .checked.lax in directory <dir>")))::uu____2952)
in (uu____2930)::uu____2941))
in (((FStar_Getopt.noshort), ("admit_except"), (SimpleStr ("[symbol|(symbol, id)]")), ("Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except \'(FStar.Fin.pigeonhole, 1)\' or --admit_except FStar.Fin.pigeonhole)")))::uu____2919)
in (((FStar_Getopt.noshort), ("admit_smt_queries"), (BoolStr), ("Admit SMT queries, unsafe! (default \'false\')")))::uu____2908))
and specs : unit  ->  FStar_Getopt.opt Prims.list = (fun uu____5204 -> (

let uu____5207 = (specs_with_types ())
in (FStar_List.map (fun uu____5232 -> (match (uu____5232) with
| (short, long, typ, doc) -> begin
(

let uu____5245 = (

let uu____5256 = (arg_spec_of_opt_type long typ)
in ((short), (long), (uu____5256), (doc)))
in (mk_spec uu____5245))
end)) uu____5207)))


let settable : Prims.string  ->  Prims.bool = (fun uu___44_5265 -> (match (uu___44_5265) with
| "admit_smt_queries" -> begin
true
end
| "admit_except" -> begin
true
end
| "debug" -> begin
true
end
| "debug_level" -> begin
true
end
| "defensive" -> begin
true
end
| "detail_errors" -> begin
true
end
| "detail_hint_replay" -> begin
true
end
| "eager_inference" -> begin
true
end
| "hide_uvar_nums" -> begin
true
end
| "hint_info" -> begin
true
end
| "hint_file" -> begin
true
end
| "initial_fuel" -> begin
true
end
| "initial_ifuel" -> begin
true
end
| "lax" -> begin
true
end
| "load" -> begin
true
end
| "log_types" -> begin
true
end
| "log_queries" -> begin
true
end
| "max_fuel" -> begin
true
end
| "max_ifuel" -> begin
true
end
| "min_fuel" -> begin
true
end
| "no_smt" -> begin
true
end
| "__no_positivity" -> begin
true
end
| "ugly" -> begin
true
end
| "print_bound_var_types" -> begin
true
end
| "print_effect_args" -> begin
true
end
| "print_full_names" -> begin
true
end
| "print_implicits" -> begin
true
end
| "print_universes" -> begin
true
end
| "print_z3_statistics" -> begin
true
end
| "prn" -> begin
true
end
| "query_stats" -> begin
true
end
| "silent" -> begin
true
end
| "smtencoding.elim_box" -> begin
true
end
| "smtencoding.nl_arith_repr" -> begin
true
end
| "smtencoding.l_arith_repr" -> begin
true
end
| "timing" -> begin
true
end
| "trace_error" -> begin
true
end
| "unthrottle_inductives" -> begin
true
end
| "use_eq_at_higher_order" -> begin
true
end
| "no_tactics" -> begin
true
end
| "normalize_pure_terms_for_extraction" -> begin
true
end
| "tactic_raw_binders" -> begin
true
end
| "tactic_trace" -> begin
true
end
| "tactic_trace_d" -> begin
true
end
| "__temp_fast_implicits" -> begin
true
end
| "__temp_no_proj" -> begin
true
end
| "reuse_hint_for" -> begin
true
end
| "warn_error" -> begin
true
end
| "z3rlimit_factor" -> begin
true
end
| "z3rlimit" -> begin
true
end
| "z3refresh" -> begin
true
end
| "use_two_phase_tc" -> begin
true
end
| "vcgen.optimize_bind_as_seq" -> begin
true
end
| uu____5266 -> begin
false
end))


let resettable : Prims.string  ->  Prims.bool = (fun s -> ((((settable s) || (Prims.op_Equality s "z3seed")) || (Prims.op_Equality s "z3cliopt")) || (Prims.op_Equality s "using_facts_from")))


let all_specs : FStar_Getopt.opt Prims.list = (specs ())


let all_specs_with_types : (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list = (specs_with_types ())


let settable_specs : (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____5335 -> (match (uu____5335) with
| (uu____5346, x, uu____5348, uu____5349) -> begin
(settable x)
end))))


let resettable_specs : (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____5405 -> (match (uu____5405) with
| (uu____5416, x, uu____5418, uu____5419) -> begin
(resettable x)
end))))


let display_usage : unit  ->  unit = (fun uu____5428 -> (

let uu____5429 = (specs ())
in (display_usage_aux uu____5429)))


let fstar_home : unit  ->  Prims.string = (fun uu____5446 -> (

let uu____5447 = (get_fstar_home ())
in (match (uu____5447) with
| FStar_Pervasives_Native.None -> begin
(

let x = (FStar_Util.get_exec_dir ())
in (

let x1 = (Prims.strcat x "/..")
in ((

let uu____5453 = (

let uu____5458 = (mk_string x1)
in (("fstar_home"), (uu____5458)))
in (set_option' uu____5453));
x1;
)))
end
| FStar_Pervasives_Native.Some (x) -> begin
x
end)))

exception File_argument of (Prims.string)


let uu___is_File_argument : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| File_argument (uu____5469) -> begin
true
end
| uu____5470 -> begin
false
end))


let __proj__File_argument__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| File_argument (uu____5477) -> begin
uu____5477
end))


let set_options : options  ->  Prims.string  ->  FStar_Getopt.parse_cmdline_res = (fun o s -> (

let specs1 = (match (o) with
| Set -> begin
settable_specs
end
| Reset -> begin
resettable_specs
end
| Restore -> begin
all_specs
end)
in (FStar_All.try_with (fun uu___49_5494 -> (match (()) with
| () -> begin
(match ((Prims.op_Equality s "")) with
| true -> begin
FStar_Getopt.Success
end
| uu____5495 -> begin
(FStar_Getopt.parse_string specs1 (fun s1 -> (FStar_Exn.raise (File_argument (s1)))) s)
end)
end)) (fun uu___48_5503 -> (match (uu___48_5503) with
| File_argument (s1) -> begin
(

let uu____5505 = (FStar_Util.format1 "File %s is not a valid option" s1)
in FStar_Getopt.Error (uu____5505))
end)))))


let file_list_ : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let parse_cmd_line : unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____5533 -> (

let res = (FStar_Getopt.parse_cmdline all_specs (fun i -> (

let uu____5538 = (

let uu____5541 = (FStar_ST.op_Bang file_list_)
in (FStar_List.append uu____5541 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list_ uu____5538))))
in (

let uu____5598 = (

let uu____5601 = (FStar_ST.op_Bang file_list_)
in (FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5601))
in ((res), (uu____5598)))))


let file_list : unit  ->  Prims.string Prims.list = (fun uu____5639 -> (FStar_ST.op_Bang file_list_))


let restore_cmd_line_options : Prims.bool  ->  FStar_Getopt.parse_cmdline_res = (fun should_clear -> (

let old_verify_module = (get_verify_module ())
in ((match (should_clear) with
| true -> begin
(clear ())
end
| uu____5676 -> begin
(init ())
end);
(

let r = (

let uu____5678 = (specs ())
in (FStar_Getopt.parse_cmdline uu____5678 (fun x -> ())))
in ((

let uu____5684 = (

let uu____5689 = (

let uu____5690 = (FStar_List.map mk_string old_verify_module)
in List (uu____5690))
in (("verify_module"), (uu____5689)))
in (set_option' uu____5684));
r;
));
)))


let module_name_of_file_name : Prims.string  ->  Prims.string = (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let f2 = (

let uu____5700 = (

let uu____5701 = (

let uu____5702 = (

let uu____5703 = (FStar_Util.get_file_extension f1)
in (FStar_String.length uu____5703))
in ((FStar_String.length f1) - uu____5702))
in (uu____5701 - (Prims.parse_int "1")))
in (FStar_String.substring f1 (Prims.parse_int "0") uu____5700))
in (FStar_String.lowercase f2))))


let should_verify : Prims.string  ->  Prims.bool = (fun m -> (

let uu____5709 = (get_lax ())
in (match (uu____5709) with
| true -> begin
false
end
| uu____5710 -> begin
(

let l = (get_verify_module ())
in (FStar_List.contains (FStar_String.lowercase m) l))
end)))


let should_verify_file : Prims.string  ->  Prims.bool = (fun fn -> (

let uu____5719 = (module_name_of_file_name fn)
in (should_verify uu____5719)))


let dont_gen_projectors : Prims.string  ->  Prims.bool = (fun m -> (

let uu____5725 = (get___temp_no_proj ())
in (FStar_List.contains m uu____5725)))


let should_print_message : Prims.string  ->  Prims.bool = (fun m -> (

let uu____5733 = (should_verify m)
in (match (uu____5733) with
| true -> begin
(Prims.op_disEquality m "Prims")
end
| uu____5734 -> begin
false
end)))


let include_path : unit  ->  Prims.string Prims.list = (fun uu____5741 -> (

let uu____5742 = (get_no_default_includes ())
in (match (uu____5742) with
| true -> begin
(get_include ())
end
| uu____5745 -> begin
(

let h = (fstar_home ())
in (

let defs = universe_include_path_base_dirs
in (

let uu____5750 = (

let uu____5753 = (FStar_All.pipe_right defs (FStar_List.map (fun x -> (Prims.strcat h x))))
in (FStar_All.pipe_right uu____5753 (FStar_List.filter FStar_Util.file_exists)))
in (

let uu____5766 = (

let uu____5769 = (get_include ())
in (FStar_List.append uu____5769 ((".")::[])))
in (FStar_List.append uu____5750 uu____5766)))))
end)))


let find_file : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun filename -> (

let uu____5779 = (FStar_Util.is_path_absolute filename)
in (match (uu____5779) with
| true -> begin
(match ((FStar_Util.file_exists filename)) with
| true -> begin
FStar_Pervasives_Native.Some (filename)
end
| uu____5784 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____5785 -> begin
(

let uu____5786 = (

let uu____5789 = (include_path ())
in (FStar_List.rev uu____5789))
in (FStar_Util.find_map uu____5786 (fun p -> (

let path = (match ((Prims.op_Equality p ".")) with
| true -> begin
filename
end
| uu____5796 -> begin
(FStar_Util.join_paths p filename)
end)
in (match ((FStar_Util.file_exists path)) with
| true -> begin
FStar_Pervasives_Native.Some (path)
end
| uu____5799 -> begin
FStar_Pervasives_Native.None
end)))))
end)))


let prims : unit  ->  Prims.string = (fun uu____5804 -> (

let uu____5805 = (get_prims ())
in (match (uu____5805) with
| FStar_Pervasives_Native.None -> begin
(

let filename = "prims.fst"
in (

let uu____5809 = (find_file filename)
in (match (uu____5809) with
| FStar_Pervasives_Native.Some (result) -> begin
result
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5813 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____5813))
end)))
end
| FStar_Pervasives_Native.Some (x) -> begin
x
end)))


let prims_basename : unit  ->  Prims.string = (fun uu____5819 -> (

let uu____5820 = (prims ())
in (FStar_Util.basename uu____5820)))


let pervasives : unit  ->  Prims.string = (fun uu____5825 -> (

let filename = "FStar.Pervasives.fst"
in (

let uu____5827 = (find_file filename)
in (match (uu____5827) with
| FStar_Pervasives_Native.Some (result) -> begin
result
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5831 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____5831))
end))))


let pervasives_basename : unit  ->  Prims.string = (fun uu____5836 -> (

let uu____5837 = (pervasives ())
in (FStar_Util.basename uu____5837)))


let pervasives_native_basename : unit  ->  Prims.string = (fun uu____5842 -> (

let filename = "FStar.Pervasives.Native.fst"
in (

let uu____5844 = (find_file filename)
in (match (uu____5844) with
| FStar_Pervasives_Native.Some (result) -> begin
(FStar_Util.basename result)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5848 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____5848))
end))))


let prepend_output_dir : Prims.string  ->  Prims.string = (fun fname -> (

let uu____5854 = (get_odir ())
in (match (uu____5854) with
| FStar_Pervasives_Native.None -> begin
fname
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Util.join_paths x fname)
end)))


let prepend_cache_dir : Prims.string  ->  Prims.string = (fun fpath -> (

let uu____5863 = (get_cache_dir ())
in (match (uu____5863) with
| FStar_Pervasives_Native.None -> begin
fpath
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____5867 = (FStar_Util.basename fpath)
in (FStar_Util.join_paths x uu____5867))
end)))


let parse_settings : Prims.string Prims.list  ->  (Prims.string Prims.list * Prims.bool) Prims.list = (fun ns -> (

let parse_one_setting = (fun s -> (match ((Prims.op_Equality s "*")) with
| true -> begin
(([]), (true))
end
| uu____5907 -> begin
(match ((FStar_Util.starts_with s "-")) with
| true -> begin
(

let path = (

let uu____5913 = (FStar_Util.substring_from s (Prims.parse_int "1"))
in (FStar_Ident.path_of_text uu____5913))
in ((path), (false)))
end
| uu____5914 -> begin
(

let s1 = (match ((FStar_Util.starts_with s "+")) with
| true -> begin
(FStar_Util.substring_from s (Prims.parse_int "1"))
end
| uu____5916 -> begin
s
end)
in (

let uu____5917 = (FStar_Ident.path_of_text s1)
in ((uu____5917), (true))))
end)
end))
in (

let uu____5918 = (FStar_All.pipe_right ns (FStar_List.collect (fun s -> (FStar_All.pipe_right (FStar_Util.split s " ") (FStar_List.map parse_one_setting)))))
in (FStar_All.pipe_right uu____5918 FStar_List.rev))))


let __temp_no_proj : Prims.string  ->  Prims.bool = (fun s -> (

let uu____5982 = (get___temp_no_proj ())
in (FStar_All.pipe_right uu____5982 (FStar_List.contains s))))


let __temp_fast_implicits : unit  ->  Prims.bool = (fun uu____5991 -> (lookup_opt "__temp_fast_implicits" as_bool))


let admit_smt_queries : unit  ->  Prims.bool = (fun uu____5996 -> (get_admit_smt_queries ()))


let admit_except : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6003 -> (get_admit_except ()))


let cache_checked_modules : unit  ->  Prims.bool = (fun uu____6008 -> (get_cache_checked_modules ()))

type codegen_t =
| OCaml
| FSharp
| Kremlin
| Plugin


let uu___is_OCaml : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OCaml -> begin
true
end
| uu____6014 -> begin
false
end))


let uu___is_FSharp : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FSharp -> begin
true
end
| uu____6020 -> begin
false
end))


let uu___is_Kremlin : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Kremlin -> begin
true
end
| uu____6026 -> begin
false
end))


let uu___is_Plugin : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Plugin -> begin
true
end
| uu____6032 -> begin
false
end))


let codegen : unit  ->  codegen_t FStar_Pervasives_Native.option = (fun uu____6039 -> (

let uu____6040 = (get_codegen ())
in (FStar_Util.map_opt uu____6040 (fun uu___45_6044 -> (match (uu___45_6044) with
| "OCaml" -> begin
OCaml
end
| "FSharp" -> begin
FSharp
end
| "Kremlin" -> begin
Kremlin
end
| "Plugin" -> begin
Plugin
end
| uu____6045 -> begin
(failwith "Impossible")
end)))))


let codegen_libs : unit  ->  Prims.string Prims.list Prims.list = (fun uu____6054 -> (

let uu____6055 = (get_codegen_lib ())
in (FStar_All.pipe_right uu____6055 (FStar_List.map (fun x -> (FStar_Util.split x "."))))))


let debug_any : unit  ->  Prims.bool = (fun uu____6072 -> (

let uu____6073 = (get_debug ())
in (Prims.op_disEquality uu____6073 [])))


let debug_module : Prims.string  ->  Prims.bool = (fun modul -> (

let uu____6083 = (get_debug ())
in (FStar_All.pipe_right uu____6083 (FStar_List.contains modul))))


let debug_at_level : Prims.string  ->  debug_level_t  ->  Prims.bool = (fun modul level -> ((

let uu____6100 = (get_debug ())
in (FStar_All.pipe_right uu____6100 (FStar_List.contains modul))) && (debug_level_geq level)))


let defensive : unit  ->  Prims.bool = (fun uu____6109 -> (

let uu____6110 = (get_defensive ())
in (Prims.op_disEquality uu____6110 "no")))


let defensive_fail : unit  ->  Prims.bool = (fun uu____6115 -> (

let uu____6116 = (get_defensive ())
in (Prims.op_Equality uu____6116 "fail")))


let dep : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6123 -> (get_dep ()))


let detail_errors : unit  ->  Prims.bool = (fun uu____6128 -> (get_detail_errors ()))


let detail_hint_replay : unit  ->  Prims.bool = (fun uu____6133 -> (get_detail_hint_replay ()))


let doc : unit  ->  Prims.bool = (fun uu____6138 -> (get_doc ()))


let dump_module : Prims.string  ->  Prims.bool = (fun s -> (

let uu____6144 = (get_dump_module ())
in (FStar_All.pipe_right uu____6144 (FStar_List.contains s))))


let eager_inference : unit  ->  Prims.bool = (fun uu____6153 -> (get_eager_inference ()))


let expose_interfaces : unit  ->  Prims.bool = (fun uu____6158 -> (get_expose_interfaces ()))


let fs_typ_app : Prims.string  ->  Prims.bool = (fun filename -> (

let uu____6164 = (FStar_ST.op_Bang light_off_files)
in (FStar_List.contains filename uu____6164)))


let full_context_dependency : unit  ->  Prims.bool = (fun uu____6198 -> true)


let hide_uvar_nums : unit  ->  Prims.bool = (fun uu____6203 -> (get_hide_uvar_nums ()))


let hint_info : unit  ->  Prims.bool = (fun uu____6208 -> ((get_hint_info ()) || (get_query_stats ())))


let hint_file : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6215 -> (get_hint_file ()))


let ide : unit  ->  Prims.bool = (fun uu____6220 -> (get_ide ()))


let indent : unit  ->  Prims.bool = (fun uu____6225 -> (get_indent ()))


let initial_fuel : unit  ->  Prims.int = (fun uu____6230 -> (

let uu____6231 = (get_initial_fuel ())
in (

let uu____6232 = (get_max_fuel ())
in (Prims.min uu____6231 uu____6232))))


let initial_ifuel : unit  ->  Prims.int = (fun uu____6237 -> (

let uu____6238 = (get_initial_ifuel ())
in (

let uu____6239 = (get_max_ifuel ())
in (Prims.min uu____6238 uu____6239))))


let interactive : unit  ->  Prims.bool = (fun uu____6244 -> ((get_in ()) || (get_ide ())))


let lax : unit  ->  Prims.bool = (fun uu____6249 -> (get_lax ()))


let load : unit  ->  Prims.string Prims.list = (fun uu____6256 -> (get_load ()))


let legacy_interactive : unit  ->  Prims.bool = (fun uu____6261 -> (get_in ()))


let log_queries : unit  ->  Prims.bool = (fun uu____6266 -> (get_log_queries ()))


let log_types : unit  ->  Prims.bool = (fun uu____6271 -> (get_log_types ()))


let max_fuel : unit  ->  Prims.int = (fun uu____6276 -> (get_max_fuel ()))


let max_ifuel : unit  ->  Prims.int = (fun uu____6281 -> (get_max_ifuel ()))


let min_fuel : unit  ->  Prims.int = (fun uu____6286 -> (get_min_fuel ()))


let ml_ish : unit  ->  Prims.bool = (fun uu____6291 -> (get_MLish ()))


let set_ml_ish : unit  ->  unit = (fun uu____6296 -> (set_option "MLish" (Bool (true))))


let n_cores : unit  ->  Prims.int = (fun uu____6301 -> (get_n_cores ()))


let no_default_includes : unit  ->  Prims.bool = (fun uu____6306 -> (get_no_default_includes ()))


let no_extract : Prims.string  ->  Prims.bool = (fun s -> (

let s1 = (FStar_String.lowercase s)
in (

let uu____6313 = (get_no_extract ())
in (FStar_All.pipe_right uu____6313 (FStar_Util.for_some (fun f -> (Prims.op_Equality (FStar_String.lowercase f) s1)))))))


let normalize_pure_terms_for_extraction : unit  ->  Prims.bool = (fun uu____6324 -> (get_normalize_pure_terms_for_extraction ()))


let no_location_info : unit  ->  Prims.bool = (fun uu____6329 -> (get_no_location_info ()))


let no_smt : unit  ->  Prims.bool = (fun uu____6334 -> (get_no_smt ()))


let output_dir : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6341 -> (get_odir ()))


let ugly : unit  ->  Prims.bool = (fun uu____6346 -> (get_ugly ()))


let print_bound_var_types : unit  ->  Prims.bool = (fun uu____6351 -> (get_print_bound_var_types ()))


let print_effect_args : unit  ->  Prims.bool = (fun uu____6356 -> (get_print_effect_args ()))


let print_implicits : unit  ->  Prims.bool = (fun uu____6361 -> (get_print_implicits ()))


let print_real_names : unit  ->  Prims.bool = (fun uu____6366 -> ((get_prn ()) || (get_print_full_names ())))


let print_universes : unit  ->  Prims.bool = (fun uu____6371 -> (get_print_universes ()))


let print_z3_statistics : unit  ->  Prims.bool = (fun uu____6376 -> ((get_print_z3_statistics ()) || (get_query_stats ())))


let query_stats : unit  ->  Prims.bool = (fun uu____6381 -> (get_query_stats ()))


let record_hints : unit  ->  Prims.bool = (fun uu____6386 -> (get_record_hints ()))


let reuse_hint_for : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6393 -> (get_reuse_hint_for ()))


let silent : unit  ->  Prims.bool = (fun uu____6398 -> (get_silent ()))


let smtencoding_elim_box : unit  ->  Prims.bool = (fun uu____6403 -> (get_smtencoding_elim_box ()))


let smtencoding_nl_arith_native : unit  ->  Prims.bool = (fun uu____6408 -> (

let uu____6409 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____6409 "native")))


let smtencoding_nl_arith_wrapped : unit  ->  Prims.bool = (fun uu____6414 -> (

let uu____6415 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____6415 "wrapped")))


let smtencoding_nl_arith_default : unit  ->  Prims.bool = (fun uu____6420 -> (

let uu____6421 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____6421 "boxwrap")))


let smtencoding_l_arith_native : unit  ->  Prims.bool = (fun uu____6426 -> (

let uu____6427 = (get_smtencoding_l_arith_repr ())
in (Prims.op_Equality uu____6427 "native")))


let smtencoding_l_arith_default : unit  ->  Prims.bool = (fun uu____6432 -> (

let uu____6433 = (get_smtencoding_l_arith_repr ())
in (Prims.op_Equality uu____6433 "boxwrap")))


let tactic_raw_binders : unit  ->  Prims.bool = (fun uu____6438 -> (get_tactic_raw_binders ()))


let tactic_trace : unit  ->  Prims.bool = (fun uu____6443 -> (get_tactic_trace ()))


let tactic_trace_d : unit  ->  Prims.int = (fun uu____6448 -> (get_tactic_trace_d ()))


let timing : unit  ->  Prims.bool = (fun uu____6453 -> (get_timing ()))


let trace_error : unit  ->  Prims.bool = (fun uu____6458 -> (get_trace_error ()))


let unthrottle_inductives : unit  ->  Prims.bool = (fun uu____6463 -> (get_unthrottle_inductives ()))


let unsafe_tactic_exec : unit  ->  Prims.bool = (fun uu____6468 -> (get_unsafe_tactic_exec ()))


let use_eq_at_higher_order : unit  ->  Prims.bool = (fun uu____6473 -> (get_use_eq_at_higher_order ()))


let use_hints : unit  ->  Prims.bool = (fun uu____6478 -> (get_use_hints ()))


let use_hint_hashes : unit  ->  Prims.bool = (fun uu____6483 -> (get_use_hint_hashes ()))


let use_native_tactics : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6490 -> (get_use_native_tactics ()))


let use_tactics : unit  ->  Prims.bool = (fun uu____6495 -> (get_use_tactics ()))


let using_facts_from : unit  ->  (FStar_Ident.path * Prims.bool) Prims.list = (fun uu____6506 -> (

let uu____6507 = (get_using_facts_from ())
in (match (uu____6507) with
| FStar_Pervasives_Native.None -> begin
((([]), (true)))::[]
end
| FStar_Pervasives_Native.Some (ns) -> begin
(parse_settings ns)
end)))


let vcgen_optimize_bind_as_seq : unit  ->  Prims.bool = (fun uu____6537 -> (

let uu____6538 = (get_vcgen_optimize_bind_as_seq ())
in (FStar_Option.isSome uu____6538)))


let vcgen_decorate_with_type : unit  ->  Prims.bool = (fun uu____6545 -> (

let uu____6546 = (get_vcgen_optimize_bind_as_seq ())
in (match (uu____6546) with
| FStar_Pervasives_Native.Some ("with_type") -> begin
true
end
| uu____6549 -> begin
false
end)))


let warn_default_effects : unit  ->  Prims.bool = (fun uu____6556 -> (get_warn_default_effects ()))


let z3_exe : unit  ->  Prims.string = (fun uu____6561 -> (

let uu____6562 = (get_smt ())
in (match (uu____6562) with
| FStar_Pervasives_Native.None -> begin
(FStar_Platform.exe "z3")
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let z3_cliopt : unit  ->  Prims.string Prims.list = (fun uu____6572 -> (get_z3cliopt ()))


let z3_refresh : unit  ->  Prims.bool = (fun uu____6577 -> (get_z3refresh ()))


let z3_rlimit : unit  ->  Prims.int = (fun uu____6582 -> (get_z3rlimit ()))


let z3_rlimit_factor : unit  ->  Prims.int = (fun uu____6587 -> (get_z3rlimit_factor ()))


let z3_seed : unit  ->  Prims.int = (fun uu____6592 -> (get_z3seed ()))


let use_two_phase_tc : unit  ->  Prims.bool = (fun uu____6597 -> (get_use_two_phase_tc ()))


let no_positivity : unit  ->  Prims.bool = (fun uu____6602 -> (get_no_positivity ()))


let ml_no_eta_expand_coertions : unit  ->  Prims.bool = (fun uu____6607 -> (get_ml_no_eta_expand_coertions ()))


let warn_error : unit  ->  Prims.string = (fun uu____6612 -> (get_warn_error ()))


let use_extracted_interfaces : unit  ->  Prims.bool = (fun uu____6617 -> (get_use_extracted_interfaces ()))


let should_extract : Prims.string  ->  Prims.bool = (fun m -> (

let m1 = (FStar_String.lowercase m)
in (

let uu____6624 = (get_extract ())
in (match (uu____6624) with
| FStar_Pervasives_Native.Some (extract_setting) -> begin
((

let uu____6635 = (

let uu____6648 = (get_no_extract ())
in (

let uu____6651 = (get_extract_namespace ())
in (

let uu____6654 = (get_extract_module ())
in ((uu____6648), (uu____6651), (uu____6654)))))
in (match (uu____6635) with
| ([], [], []) -> begin
()
end
| uu____6669 -> begin
(failwith "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module")
end));
(

let setting = (parse_settings extract_setting)
in (

let m_components = (FStar_Ident.path_of_text m1)
in (

let rec matches_path = (fun m_components1 path -> (match (((m_components1), (path))) with
| (uu____6715, []) -> begin
true
end
| ((m2)::ms, (p)::ps) -> begin
((Prims.op_Equality m2 (FStar_String.lowercase p)) && (matches_path ms ps))
end
| uu____6734 -> begin
false
end))
in (

let uu____6743 = (FStar_All.pipe_right setting (FStar_Util.try_find (fun uu____6777 -> (match (uu____6777) with
| (path, uu____6785) -> begin
(matches_path m_components path)
end))))
in (match (uu____6743) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____6796, flag) -> begin
flag
end)))));
)
end
| FStar_Pervasives_Native.None -> begin
(

let should_extract_namespace = (fun m2 -> (

let uu____6816 = (get_extract_namespace ())
in (match (uu____6816) with
| [] -> begin
false
end
| ns -> begin
(FStar_All.pipe_right ns (FStar_Util.for_some (fun n1 -> (FStar_Util.starts_with m2 (FStar_String.lowercase n1)))))
end)))
in (

let should_extract_module = (fun m2 -> (

let uu____6832 = (get_extract_module ())
in (match (uu____6832) with
| [] -> begin
false
end
| l -> begin
(FStar_All.pipe_right l (FStar_Util.for_some (fun n1 -> (Prims.op_Equality (FStar_String.lowercase n1) m2))))
end)))
in ((

let uu____6844 = (no_extract m1)
in (not (uu____6844))) && (

let uu____6846 = (

let uu____6855 = (get_extract_namespace ())
in (

let uu____6858 = (get_extract_module ())
in ((uu____6855), (uu____6858))))
in (match (uu____6846) with
| ([], []) -> begin
true
end
| uu____6869 -> begin
((should_extract_namespace m1) || (should_extract_module m1))
end)))))
end))))




