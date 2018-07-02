
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


let __set_unit_tests : unit  ->  unit = (fun uu____236 -> (FStar_ST.op_Colon_Equals __unit_tests__ true))


let __clear_unit_tests : unit  ->  unit = (fun uu____260 -> (FStar_ST.op_Colon_Equals __unit_tests__ false))


let as_bool : option_val  ->  Prims.bool = (fun uu___75_284 -> (match (uu___75_284) with
| Bool (b) -> begin
b
end
| uu____286 -> begin
(failwith "Impos: expected Bool")
end))


let as_int : option_val  ->  Prims.int = (fun uu___76_291 -> (match (uu___76_291) with
| Int (b) -> begin
b
end
| uu____293 -> begin
(failwith "Impos: expected Int")
end))


let as_string : option_val  ->  Prims.string = (fun uu___77_298 -> (match (uu___77_298) with
| String (b) -> begin
b
end
| Path (b) -> begin
(FStar_Common.try_convert_file_name_to_mixed b)
end
| uu____301 -> begin
(failwith "Impos: expected String")
end))


let as_list' : option_val  ->  option_val Prims.list = (fun uu___78_308 -> (match (uu___78_308) with
| List (ts) -> begin
ts
end
| uu____314 -> begin
(failwith "Impos: expected List")
end))


let as_list : 'Auu____323 . (option_val  ->  'Auu____323)  ->  option_val  ->  'Auu____323 Prims.list = (fun as_t x -> (

let uu____341 = (as_list' x)
in (FStar_All.pipe_right uu____341 (FStar_List.map as_t))))


let as_option : 'Auu____354 . (option_val  ->  'Auu____354)  ->  option_val  ->  'Auu____354 FStar_Pervasives_Native.option = (fun as_t uu___79_369 -> (match (uu___79_369) with
| Unset -> begin
FStar_Pervasives_Native.None
end
| v1 -> begin
(

let uu____373 = (as_t v1)
in FStar_Pervasives_Native.Some (uu____373))
end))


let as_comma_string_list : option_val  ->  Prims.string Prims.list = (fun uu___80_380 -> (match (uu___80_380) with
| List (ls) -> begin
(

let uu____386 = (FStar_List.map (fun l -> (

let uu____396 = (as_string l)
in (FStar_Util.split uu____396 ","))) ls)
in (FStar_All.pipe_left FStar_List.flatten uu____386))
end
| uu____403 -> begin
(failwith "Impos: expected String (comma list)")
end))


type optionstate =
option_val FStar_Util.smap


let fstar_options : optionstate Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let peek : unit  ->  optionstate = (fun uu____429 -> (

let uu____430 = (FStar_ST.op_Bang fstar_options)
in (FStar_List.hd uu____430)))


let pop : unit  ->  unit = (fun uu____460 -> (

let uu____461 = (FStar_ST.op_Bang fstar_options)
in (match (uu____461) with
| [] -> begin
(failwith "TOO MANY POPS!")
end
| (uu____487)::[] -> begin
(failwith "TOO MANY POPS!")
end
| (uu____488)::tl1 -> begin
(FStar_ST.op_Colon_Equals fstar_options tl1)
end)))


let push : unit  ->  unit = (fun uu____519 -> (

let uu____520 = (

let uu____523 = (

let uu____524 = (peek ())
in (FStar_Util.smap_copy uu____524))
in (

let uu____527 = (FStar_ST.op_Bang fstar_options)
in (uu____523)::uu____527))
in (FStar_ST.op_Colon_Equals fstar_options uu____520)))


let set : optionstate  ->  unit = (fun o -> (

let uu____581 = (FStar_ST.op_Bang fstar_options)
in (match (uu____581) with
| [] -> begin
(failwith "set on empty option stack")
end
| (uu____607)::os -> begin
(FStar_ST.op_Colon_Equals fstar_options ((o)::os))
end)))


let snapshot : unit  ->  (Prims.int * unit) = (fun uu____642 -> (FStar_Common.snapshot push fstar_options ()))


let rollback : Prims.int FStar_Pervasives_Native.option  ->  unit = (fun depth -> (FStar_Common.rollback pop fstar_options depth))


let set_option : Prims.string  ->  option_val  ->  unit = (fun k v1 -> (

let uu____662 = (peek ())
in (FStar_Util.smap_add uu____662 k v1)))


let set_option' : (Prims.string * option_val)  ->  unit = (fun uu____673 -> (match (uu____673) with
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

let uu____720 = (

let uu____723 = (FStar_ST.op_Bang light_off_files)
in (filename)::uu____723)
in (FStar_ST.op_Colon_Equals light_off_files uu____720)))


let defaults : (Prims.string * option_val) Prims.list = ((("__temp_no_proj"), (List ([]))))::((("__temp_fast_implicits"), (Bool (false))))::((("abort_on"), (Int ((Prims.parse_int "0")))))::((("admit_smt_queries"), (Bool (false))))::((("admit_except"), (Unset)))::((("cache_checked_modules"), (Bool (false))))::((("cache_dir"), (Unset)))::((("cache_off"), (Bool (false))))::((("codegen"), (Unset)))::((("codegen-lib"), (List ([]))))::((("debug"), (List ([]))))::((("debug_level"), (List ([]))))::((("defensive"), (String ("no"))))::((("dep"), (Unset)))::((("detail_errors"), (Bool (false))))::((("detail_hint_replay"), (Bool (false))))::((("doc"), (Bool (false))))::((("dump_module"), (List ([]))))::((("eager_embedding"), (Bool (false))))::((("eager_inference"), (Bool (false))))::((("eager_subtyping"), (Bool (false))))::((("expose_interfaces"), (Bool (false))))::((("extract"), (Unset)))::((("extract_all"), (Bool (false))))::((("extract_module"), (List ([]))))::((("extract_namespace"), (List ([]))))::((("fs_typ_app"), (Bool (false))))::((("full_context_dependency"), (Bool (true))))::((("hide_uvar_nums"), (Bool (false))))::((("hint_info"), (Bool (false))))::((("hint_file"), (Unset)))::((("in"), (Bool (false))))::((("ide"), (Bool (false))))::((("include"), (List ([]))))::((("indent"), (Bool (false))))::((("initial_fuel"), (Int ((Prims.parse_int "2")))))::((("initial_ifuel"), (Int ((Prims.parse_int "1")))))::((("lax"), (Bool (false))))::((("load"), (List ([]))))::((("log_queries"), (Bool (false))))::((("log_types"), (Bool (false))))::((("max_fuel"), (Int ((Prims.parse_int "8")))))::((("max_ifuel"), (Int ((Prims.parse_int "2")))))::((("min_fuel"), (Int ((Prims.parse_int "1")))))::((("MLish"), (Bool (false))))::((("n_cores"), (Int ((Prims.parse_int "1")))))::((("no_default_includes"), (Bool (false))))::((("no_extract"), (List ([]))))::((("no_location_info"), (Bool (false))))::((("no_smt"), (Bool (false))))::((("no_tactics"), (Bool (false))))::((("normalize_pure_terms_for_extraction"), (Bool (false))))::((("odir"), (Unset)))::((("prims"), (Unset)))::((("pretype"), (Bool (true))))::((("prims_ref"), (Unset)))::((("print_bound_var_types"), (Bool (false))))::((("print_effect_args"), (Bool (false))))::((("print_full_names"), (Bool (false))))::((("print_implicits"), (Bool (false))))::((("print_universes"), (Bool (false))))::((("print_z3_statistics"), (Bool (false))))::((("prn"), (Bool (false))))::((("query_stats"), (Bool (false))))::((("record_hints"), (Bool (false))))::((("reuse_hint_for"), (Unset)))::((("silent"), (Bool (false))))::((("smt"), (Unset)))::((("smtencoding.elim_box"), (Bool (false))))::((("smtencoding.nl_arith_repr"), (String ("boxwrap"))))::((("smtencoding.l_arith_repr"), (String ("boxwrap"))))::((("tactic_raw_binders"), (Bool (false))))::((("tactic_trace"), (Bool (false))))::((("tactic_trace_d"), (Int ((Prims.parse_int "0")))))::((("timing"), (Bool (false))))::((("trace_error"), (Bool (false))))::((("ugly"), (Bool (false))))::((("unthrottle_inductives"), (Bool (false))))::((("unsafe_tactic_exec"), (Bool (false))))::((("use_native_tactics"), (Unset)))::((("use_eq_at_higher_order"), (Bool (false))))::((("use_hints"), (Bool (false))))::((("use_hint_hashes"), (Bool (false))))::((("using_facts_from"), (Unset)))::((("vcgen.optimize_bind_as_seq"), (Unset)))::((("verify_module"), (List ([]))))::((("warn_default_effects"), (Bool (false))))::((("z3refresh"), (Bool (false))))::((("z3rlimit"), (Int ((Prims.parse_int "5")))))::((("z3rlimit_factor"), (Int ((Prims.parse_int "1")))))::((("z3seed"), (Int ((Prims.parse_int "0")))))::((("z3cliopt"), (List ([]))))::((("use_two_phase_tc"), (Bool (true))))::((("__no_positivity"), (Bool (false))))::((("__ml_no_eta_expand_coertions"), (Bool (false))))::((("__tactics_nbe"), (Bool (false))))::((("warn_error"), (String (""))))::((("use_extracted_interfaces"), (Bool (false))))::[]


let init : unit  ->  unit = (fun uu____1178 -> (

let o = (peek ())
in ((FStar_Util.smap_clear o);
(FStar_All.pipe_right defaults (FStar_List.iter set_option'));
)))


let clear : unit  ->  unit = (fun uu____1195 -> (

let o = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_ST.op_Colon_Equals fstar_options ((o)::[]));
(FStar_ST.op_Colon_Equals light_off_files []);
(init ());
)))


let _run : unit = (clear ())


let get_option : Prims.string  ->  option_val = (fun s -> (

let uu____1252 = (

let uu____1255 = (peek ())
in (FStar_Util.smap_try_find uu____1255 s))
in (match (uu____1252) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Impossible: option " (Prims.strcat s " not found")))
end
| FStar_Pervasives_Native.Some (s1) -> begin
s1
end)))


let lookup_opt : 'Auu____1265 . Prims.string  ->  (option_val  ->  'Auu____1265)  ->  'Auu____1265 = (fun s c -> (

let uu____1281 = (get_option s)
in (c uu____1281)))


let get_abort_on : unit  ->  Prims.int = (fun uu____1286 -> (lookup_opt "abort_on" as_int))


let get_admit_smt_queries : unit  ->  Prims.bool = (fun uu____1291 -> (lookup_opt "admit_smt_queries" as_bool))


let get_admit_except : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1298 -> (lookup_opt "admit_except" (as_option as_string)))


let get_cache_checked_modules : unit  ->  Prims.bool = (fun uu____1305 -> (lookup_opt "cache_checked_modules" as_bool))


let get_cache_dir : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1312 -> (lookup_opt "cache_dir" (as_option as_string)))


let get_cache_off : unit  ->  Prims.bool = (fun uu____1319 -> (lookup_opt "cache_off" as_bool))


let get_codegen : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1326 -> (lookup_opt "codegen" (as_option as_string)))


let get_codegen_lib : unit  ->  Prims.string Prims.list = (fun uu____1335 -> (lookup_opt "codegen-lib" (as_list as_string)))


let get_debug : unit  ->  Prims.string Prims.list = (fun uu____1344 -> (lookup_opt "debug" (as_list as_string)))


let get_debug_level : unit  ->  Prims.string Prims.list = (fun uu____1353 -> (lookup_opt "debug_level" as_comma_string_list))


let get_defensive : unit  ->  Prims.string = (fun uu____1360 -> (lookup_opt "defensive" as_string))


let get_dep : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1367 -> (lookup_opt "dep" (as_option as_string)))


let get_detail_errors : unit  ->  Prims.bool = (fun uu____1374 -> (lookup_opt "detail_errors" as_bool))


let get_detail_hint_replay : unit  ->  Prims.bool = (fun uu____1379 -> (lookup_opt "detail_hint_replay" as_bool))


let get_doc : unit  ->  Prims.bool = (fun uu____1384 -> (lookup_opt "doc" as_bool))


let get_dump_module : unit  ->  Prims.string Prims.list = (fun uu____1391 -> (lookup_opt "dump_module" (as_list as_string)))


let get_eager_embedding : unit  ->  Prims.bool = (fun uu____1398 -> (lookup_opt "eager_embedding" as_bool))


let get_eager_subtyping : unit  ->  Prims.bool = (fun uu____1403 -> (lookup_opt "eager_subtyping" as_bool))


let get_expose_interfaces : unit  ->  Prims.bool = (fun uu____1408 -> (lookup_opt "expose_interfaces" as_bool))


let get_extract : unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____1417 -> (lookup_opt "extract" (as_option (as_list as_string))))


let get_extract_module : unit  ->  Prims.string Prims.list = (fun uu____1430 -> (lookup_opt "extract_module" (as_list as_string)))


let get_extract_namespace : unit  ->  Prims.string Prims.list = (fun uu____1439 -> (lookup_opt "extract_namespace" (as_list as_string)))


let get_fs_typ_app : unit  ->  Prims.bool = (fun uu____1446 -> (lookup_opt "fs_typ_app" as_bool))


let get_hide_uvar_nums : unit  ->  Prims.bool = (fun uu____1451 -> (lookup_opt "hide_uvar_nums" as_bool))


let get_hint_info : unit  ->  Prims.bool = (fun uu____1456 -> (lookup_opt "hint_info" as_bool))


let get_hint_file : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1463 -> (lookup_opt "hint_file" (as_option as_string)))


let get_in : unit  ->  Prims.bool = (fun uu____1470 -> (lookup_opt "in" as_bool))


let get_ide : unit  ->  Prims.bool = (fun uu____1475 -> (lookup_opt "ide" as_bool))


let get_include : unit  ->  Prims.string Prims.list = (fun uu____1482 -> (lookup_opt "include" (as_list as_string)))


let get_indent : unit  ->  Prims.bool = (fun uu____1489 -> (lookup_opt "indent" as_bool))


let get_initial_fuel : unit  ->  Prims.int = (fun uu____1494 -> (lookup_opt "initial_fuel" as_int))


let get_initial_ifuel : unit  ->  Prims.int = (fun uu____1499 -> (lookup_opt "initial_ifuel" as_int))


let get_lax : unit  ->  Prims.bool = (fun uu____1504 -> (lookup_opt "lax" as_bool))


let get_load : unit  ->  Prims.string Prims.list = (fun uu____1511 -> (lookup_opt "load" (as_list as_string)))


let get_log_queries : unit  ->  Prims.bool = (fun uu____1518 -> (lookup_opt "log_queries" as_bool))


let get_log_types : unit  ->  Prims.bool = (fun uu____1523 -> (lookup_opt "log_types" as_bool))


let get_max_fuel : unit  ->  Prims.int = (fun uu____1528 -> (lookup_opt "max_fuel" as_int))


let get_max_ifuel : unit  ->  Prims.int = (fun uu____1533 -> (lookup_opt "max_ifuel" as_int))


let get_min_fuel : unit  ->  Prims.int = (fun uu____1538 -> (lookup_opt "min_fuel" as_int))


let get_MLish : unit  ->  Prims.bool = (fun uu____1543 -> (lookup_opt "MLish" as_bool))


let get_n_cores : unit  ->  Prims.int = (fun uu____1548 -> (lookup_opt "n_cores" as_int))


let get_no_default_includes : unit  ->  Prims.bool = (fun uu____1553 -> (lookup_opt "no_default_includes" as_bool))


let get_no_extract : unit  ->  Prims.string Prims.list = (fun uu____1560 -> (lookup_opt "no_extract" (as_list as_string)))


let get_no_location_info : unit  ->  Prims.bool = (fun uu____1567 -> (lookup_opt "no_location_info" as_bool))


let get_no_smt : unit  ->  Prims.bool = (fun uu____1572 -> (lookup_opt "no_smt" as_bool))


let get_normalize_pure_terms_for_extraction : unit  ->  Prims.bool = (fun uu____1577 -> (lookup_opt "normalize_pure_terms_for_extraction" as_bool))


let get_odir : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1584 -> (lookup_opt "odir" (as_option as_string)))


let get_ugly : unit  ->  Prims.bool = (fun uu____1591 -> (lookup_opt "ugly" as_bool))


let get_prims : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1598 -> (lookup_opt "prims" (as_option as_string)))


let get_print_bound_var_types : unit  ->  Prims.bool = (fun uu____1605 -> (lookup_opt "print_bound_var_types" as_bool))


let get_print_effect_args : unit  ->  Prims.bool = (fun uu____1610 -> (lookup_opt "print_effect_args" as_bool))


let get_print_full_names : unit  ->  Prims.bool = (fun uu____1615 -> (lookup_opt "print_full_names" as_bool))


let get_print_implicits : unit  ->  Prims.bool = (fun uu____1620 -> (lookup_opt "print_implicits" as_bool))


let get_print_universes : unit  ->  Prims.bool = (fun uu____1625 -> (lookup_opt "print_universes" as_bool))


let get_print_z3_statistics : unit  ->  Prims.bool = (fun uu____1630 -> (lookup_opt "print_z3_statistics" as_bool))


let get_prn : unit  ->  Prims.bool = (fun uu____1635 -> (lookup_opt "prn" as_bool))


let get_query_stats : unit  ->  Prims.bool = (fun uu____1640 -> (lookup_opt "query_stats" as_bool))


let get_record_hints : unit  ->  Prims.bool = (fun uu____1645 -> (lookup_opt "record_hints" as_bool))


let get_reuse_hint_for : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1652 -> (lookup_opt "reuse_hint_for" (as_option as_string)))


let get_silent : unit  ->  Prims.bool = (fun uu____1659 -> (lookup_opt "silent" as_bool))


let get_smt : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1666 -> (lookup_opt "smt" (as_option as_string)))


let get_smtencoding_elim_box : unit  ->  Prims.bool = (fun uu____1673 -> (lookup_opt "smtencoding.elim_box" as_bool))


let get_smtencoding_nl_arith_repr : unit  ->  Prims.string = (fun uu____1678 -> (lookup_opt "smtencoding.nl_arith_repr" as_string))


let get_smtencoding_l_arith_repr : unit  ->  Prims.string = (fun uu____1683 -> (lookup_opt "smtencoding.l_arith_repr" as_string))


let get_tactic_raw_binders : unit  ->  Prims.bool = (fun uu____1688 -> (lookup_opt "tactic_raw_binders" as_bool))


let get_tactic_trace : unit  ->  Prims.bool = (fun uu____1693 -> (lookup_opt "tactic_trace" as_bool))


let get_tactic_trace_d : unit  ->  Prims.int = (fun uu____1698 -> (lookup_opt "tactic_trace_d" as_int))


let get_tactics_nbe : unit  ->  Prims.bool = (fun uu____1703 -> (lookup_opt "__tactics_nbe" as_bool))


let get_timing : unit  ->  Prims.bool = (fun uu____1708 -> (lookup_opt "timing" as_bool))


let get_trace_error : unit  ->  Prims.bool = (fun uu____1713 -> (lookup_opt "trace_error" as_bool))


let get_unthrottle_inductives : unit  ->  Prims.bool = (fun uu____1718 -> (lookup_opt "unthrottle_inductives" as_bool))


let get_unsafe_tactic_exec : unit  ->  Prims.bool = (fun uu____1723 -> (lookup_opt "unsafe_tactic_exec" as_bool))


let get_use_eq_at_higher_order : unit  ->  Prims.bool = (fun uu____1728 -> (lookup_opt "use_eq_at_higher_order" as_bool))


let get_use_hints : unit  ->  Prims.bool = (fun uu____1733 -> (lookup_opt "use_hints" as_bool))


let get_use_hint_hashes : unit  ->  Prims.bool = (fun uu____1738 -> (lookup_opt "use_hint_hashes" as_bool))


let get_use_native_tactics : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1745 -> (lookup_opt "use_native_tactics" (as_option as_string)))


let get_use_tactics : unit  ->  Prims.bool = (fun uu____1752 -> (

let uu____1753 = (lookup_opt "no_tactics" as_bool)
in (not (uu____1753))))


let get_using_facts_from : unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____1762 -> (lookup_opt "using_facts_from" (as_option (as_list as_string))))


let get_vcgen_optimize_bind_as_seq : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1775 -> (lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)))


let get_verify_module : unit  ->  Prims.string Prims.list = (fun uu____1784 -> (lookup_opt "verify_module" (as_list as_string)))


let get___temp_no_proj : unit  ->  Prims.string Prims.list = (fun uu____1793 -> (lookup_opt "__temp_no_proj" (as_list as_string)))


let get_version : unit  ->  Prims.bool = (fun uu____1800 -> (lookup_opt "version" as_bool))


let get_warn_default_effects : unit  ->  Prims.bool = (fun uu____1805 -> (lookup_opt "warn_default_effects" as_bool))


let get_z3cliopt : unit  ->  Prims.string Prims.list = (fun uu____1812 -> (lookup_opt "z3cliopt" (as_list as_string)))


let get_z3refresh : unit  ->  Prims.bool = (fun uu____1819 -> (lookup_opt "z3refresh" as_bool))


let get_z3rlimit : unit  ->  Prims.int = (fun uu____1824 -> (lookup_opt "z3rlimit" as_int))


let get_z3rlimit_factor : unit  ->  Prims.int = (fun uu____1829 -> (lookup_opt "z3rlimit_factor" as_int))


let get_z3seed : unit  ->  Prims.int = (fun uu____1834 -> (lookup_opt "z3seed" as_int))


let get_use_two_phase_tc : unit  ->  Prims.bool = (fun uu____1839 -> (lookup_opt "use_two_phase_tc" as_bool))


let get_no_positivity : unit  ->  Prims.bool = (fun uu____1844 -> (lookup_opt "__no_positivity" as_bool))


let get_ml_no_eta_expand_coertions : unit  ->  Prims.bool = (fun uu____1849 -> (lookup_opt "__ml_no_eta_expand_coertions" as_bool))


let get_warn_error : unit  ->  Prims.string = (fun uu____1854 -> (lookup_opt "warn_error" as_string))


let get_use_extracted_interfaces : unit  ->  Prims.bool = (fun uu____1859 -> (lookup_opt "use_extracted_interfaces" as_bool))


let dlevel : Prims.string  ->  debug_level_t = (fun uu___81_1864 -> (match (uu___81_1864) with
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
| Other (uu____1876) -> begin
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

let uu____1882 = (get_debug_level ())
in (FStar_All.pipe_right uu____1882 (FStar_Util.for_some (fun l1 -> (one_debug_level_geq (dlevel l1) l2))))))


let universe_include_path_base_dirs : Prims.string Prims.list = ("/ulib")::("/lib/fstar")::[]


let _version : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _platform : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _compiler : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _date : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _commit : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let display_version : unit  ->  unit = (fun uu____2015 -> (

let uu____2016 = (

let uu____2017 = (FStar_ST.op_Bang _version)
in (

let uu____2037 = (FStar_ST.op_Bang _platform)
in (

let uu____2057 = (FStar_ST.op_Bang _compiler)
in (

let uu____2077 = (FStar_ST.op_Bang _date)
in (

let uu____2097 = (FStar_ST.op_Bang _commit)
in (FStar_Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2017 uu____2037 uu____2057 uu____2077 uu____2097))))))
in (FStar_Util.print_string uu____2016)))


let display_usage_aux : 'Auu____2123 'Auu____2124 . ('Auu____2123 * Prims.string * 'Auu____2124 FStar_Getopt.opt_variant * Prims.string) Prims.list  ->  unit = (fun specs -> ((FStar_Util.print_string "fstar.exe [options] file[s]\n");
(FStar_List.iter (fun uu____2172 -> (match (uu____2172) with
| (uu____2183, flag, p, doc) -> begin
(match (p) with
| FStar_Getopt.ZeroArgs (ig) -> begin
(match ((Prims.op_Equality doc "")) with
| true -> begin
(

let uu____2195 = (

let uu____2196 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format1 "  --%s\n" uu____2196))
in (FStar_Util.print_string uu____2195))
end
| uu____2197 -> begin
(

let uu____2198 = (

let uu____2199 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format2 "  --%s  %s\n" uu____2199 doc))
in (FStar_Util.print_string uu____2198))
end)
end
| FStar_Getopt.OneArg (uu____2200, argname) -> begin
(match ((Prims.op_Equality doc "")) with
| true -> begin
(

let uu____2208 = (

let uu____2209 = (FStar_Util.colorize_bold flag)
in (

let uu____2210 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format2 "  --%s %s\n" uu____2209 uu____2210)))
in (FStar_Util.print_string uu____2208))
end
| uu____2211 -> begin
(

let uu____2212 = (

let uu____2213 = (FStar_Util.colorize_bold flag)
in (

let uu____2214 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format3 "  --%s %s  %s\n" uu____2213 uu____2214 doc)))
in (FStar_Util.print_string uu____2212))
end)
end)
end)) specs);
))


let mk_spec : (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant * Prims.string)  ->  FStar_Getopt.opt = (fun o -> (

let uu____2242 = o
in (match (uu____2242) with
| (ns, name, arg, desc) -> begin
(

let arg1 = (match (arg) with
| FStar_Getopt.ZeroArgs (f) -> begin
(

let g = (fun uu____2278 -> (

let uu____2279 = (f ())
in (set_option name uu____2279)))
in FStar_Getopt.ZeroArgs (g))
end
| FStar_Getopt.OneArg (f, d) -> begin
(

let g = (fun x -> (

let uu____2294 = (f x)
in (set_option name uu____2294)))
in FStar_Getopt.OneArg (((g), (d))))
end)
in ((ns), (name), (arg1), (desc)))
end)))


let accumulated_option : Prims.string  ->  option_val  ->  option_val = (fun name value -> (

let prev_values = (

let uu____2314 = (lookup_opt name (as_option as_list'))
in (FStar_Util.dflt [] uu____2314))
in (mk_list ((value)::prev_values))))


let reverse_accumulated_option : Prims.string  ->  option_val  ->  option_val = (fun name value -> (

let uu____2337 = (

let uu____2340 = (lookup_opt name as_list')
in (FStar_List.append uu____2340 ((value)::[])))
in (mk_list uu____2337)))


let accumulate_string : 'Auu____2353 . Prims.string  ->  ('Auu____2353  ->  Prims.string)  ->  'Auu____2353  ->  unit = (fun name post_processor value -> (

let uu____2374 = (

let uu____2375 = (

let uu____2376 = (post_processor value)
in (mk_string uu____2376))
in (accumulated_option name uu____2375))
in (set_option name uu____2374)))


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
| uu____2472 -> begin
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
| uu____2486 -> begin
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
| uu____2499 -> begin
false
end))


let uu___is_PathStr : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PathStr (_0) -> begin
true
end
| uu____2506 -> begin
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
| uu____2520 -> begin
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
| uu____2536 -> begin
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
| uu____2562 -> begin
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
| uu____2601 -> begin
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
| uu____2636 -> begin
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
| uu____2650 -> begin
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
| uu____2671 -> begin
false
end))


let __proj__WithSideEffect__item___0 : opt_type  ->  ((unit  ->  unit) * opt_type) = (fun projectee -> (match (projectee) with
| WithSideEffect (_0) -> begin
_0
end))

exception InvalidArgument of (Prims.string)


let uu___is_InvalidArgument : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidArgument (uu____2709) -> begin
true
end
| uu____2710 -> begin
false
end))


let __proj__InvalidArgument__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidArgument (uu____2717) -> begin
uu____2717
end))


let rec parse_opt_val : Prims.string  ->  opt_type  ->  Prims.string  ->  option_val = (fun opt_name typ str_val -> (FStar_All.try_with (fun uu___86_2735 -> (match (()) with
| () -> begin
(match (typ) with
| Const (c) -> begin
c
end
| IntStr (uu____2737) -> begin
(

let uu____2738 = (FStar_Util.safe_int_of_string str_val)
in (match (uu____2738) with
| FStar_Pervasives_Native.Some (v1) -> begin
(mk_int v1)
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end))
end
| BoolStr -> begin
(

let uu____2742 = (match ((Prims.op_Equality str_val "true")) with
| true -> begin
true
end
| uu____2743 -> begin
(match ((Prims.op_Equality str_val "false")) with
| true -> begin
false
end
| uu____2744 -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end)
end)
in (mk_bool uu____2742))
end
| PathStr (uu____2745) -> begin
(mk_path str_val)
end
| SimpleStr (uu____2746) -> begin
(mk_string str_val)
end
| EnumStr (strs) -> begin
(match ((FStar_List.mem str_val strs)) with
| true -> begin
(mk_string str_val)
end
| uu____2750 -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end)
end
| OpenEnumStr (uu____2751) -> begin
(mk_string str_val)
end
| PostProcessed (pp, elem_spec) -> begin
(

let uu____2766 = (parse_opt_val opt_name elem_spec str_val)
in (pp uu____2766))
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
end)) (fun uu___85_2783 -> (match (uu___85_2783) with
| InvalidArgument (opt_name1) -> begin
(

let uu____2785 = (FStar_Util.format1 "Invalid argument to --%s" opt_name1)
in (failwith uu____2785))
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
| PostProcessed (uu____2822, elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| Accumulated (elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| ReverseAccumulated (elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| WithSideEffect (uu____2832, elem_spec) -> begin
(desc_of_opt_type elem_spec)
end)))


let rec arg_spec_of_opt_type : Prims.string  ->  opt_type  ->  option_val FStar_Getopt.opt_variant = (fun opt_name typ -> (

let parser = (parse_opt_val opt_name typ)
in (

let uu____2859 = (desc_of_opt_type typ)
in (match (uu____2859) with
| FStar_Pervasives_Native.None -> begin
FStar_Getopt.ZeroArgs ((fun uu____2865 -> (parser "")))
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

let uu____2882 = (

let uu____2883 = (as_string s)
in (FStar_String.lowercase uu____2883))
in (mk_string uu____2882)))


let abort_counter : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let rec specs_with_types : unit  ->  (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list = (fun uu____2931 -> (

let uu____2943 = (

let uu____2955 = (

let uu____2967 = (

let uu____2979 = (

let uu____2989 = (

let uu____2990 = (mk_bool true)
in Const (uu____2990))
in ((FStar_Getopt.noshort), ("cache_checked_modules"), (uu____2989), ("Write a \'.checked\' file for each module after verification and read from it if present, instead of re-verifying")))
in (

let uu____2992 = (

let uu____3004 = (

let uu____3016 = (

let uu____3026 = (

let uu____3027 = (mk_bool true)
in Const (uu____3027))
in ((FStar_Getopt.noshort), ("cache_off"), (uu____3026), ("Do not read or write any .checked files")))
in (

let uu____3029 = (

let uu____3041 = (

let uu____3053 = (

let uu____3065 = (

let uu____3077 = (

let uu____3089 = (

let uu____3101 = (

let uu____3113 = (

let uu____3123 = (

let uu____3124 = (mk_bool true)
in Const (uu____3124))
in ((FStar_Getopt.noshort), ("detail_errors"), (uu____3123), ("Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")))
in (

let uu____3126 = (

let uu____3138 = (

let uu____3148 = (

let uu____3149 = (mk_bool true)
in Const (uu____3149))
in ((FStar_Getopt.noshort), ("detail_hint_replay"), (uu____3148), ("Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")))
in (

let uu____3151 = (

let uu____3163 = (

let uu____3173 = (

let uu____3174 = (mk_bool true)
in Const (uu____3174))
in ((FStar_Getopt.noshort), ("doc"), (uu____3173), ("Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")))
in (

let uu____3176 = (

let uu____3188 = (

let uu____3200 = (

let uu____3210 = (

let uu____3211 = (mk_bool true)
in Const (uu____3211))
in ((FStar_Getopt.noshort), ("eager_embedding"), (uu____3210), ("Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")))
in (

let uu____3213 = (

let uu____3225 = (

let uu____3235 = (

let uu____3236 = (mk_bool true)
in Const (uu____3236))
in ((FStar_Getopt.noshort), ("eager_inference"), (uu____3235), ("Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")))
in (

let uu____3238 = (

let uu____3250 = (

let uu____3260 = (

let uu____3261 = (mk_bool true)
in Const (uu____3261))
in ((FStar_Getopt.noshort), ("eager_subtyping"), (uu____3260), ("Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")))
in (

let uu____3263 = (

let uu____3275 = (

let uu____3287 = (

let uu____3299 = (

let uu____3311 = (

let uu____3321 = (

let uu____3322 = (mk_bool true)
in Const (uu____3322))
in ((FStar_Getopt.noshort), ("expose_interfaces"), (uu____3321), ("Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")))
in (

let uu____3324 = (

let uu____3336 = (

let uu____3346 = (

let uu____3347 = (mk_bool true)
in Const (uu____3347))
in ((FStar_Getopt.noshort), ("hide_uvar_nums"), (uu____3346), ("Don\'t print unification variable numbers")))
in (

let uu____3349 = (

let uu____3361 = (

let uu____3373 = (

let uu____3383 = (

let uu____3384 = (mk_bool true)
in Const (uu____3384))
in ((FStar_Getopt.noshort), ("hint_info"), (uu____3383), ("Print information regarding hints (deprecated; use --query_stats instead)")))
in (

let uu____3386 = (

let uu____3398 = (

let uu____3408 = (

let uu____3409 = (mk_bool true)
in Const (uu____3409))
in ((FStar_Getopt.noshort), ("in"), (uu____3408), ("Legacy interactive mode; reads input from stdin")))
in (

let uu____3411 = (

let uu____3423 = (

let uu____3433 = (

let uu____3434 = (mk_bool true)
in Const (uu____3434))
in ((FStar_Getopt.noshort), ("ide"), (uu____3433), ("JSON-based interactive mode for IDEs")))
in (

let uu____3436 = (

let uu____3448 = (

let uu____3460 = (

let uu____3470 = (

let uu____3471 = (mk_bool true)
in Const (uu____3471))
in ((FStar_Getopt.noshort), ("indent"), (uu____3470), ("Parses and outputs the files on the command line")))
in (

let uu____3473 = (

let uu____3485 = (

let uu____3497 = (

let uu____3509 = (

let uu____3519 = (

let uu____3520 = (mk_bool true)
in Const (uu____3520))
in ((FStar_Getopt.noshort), ("lax"), (uu____3519), ("Run the lax-type checker only (admit all verification conditions)")))
in (

let uu____3522 = (

let uu____3534 = (

let uu____3546 = (

let uu____3556 = (

let uu____3557 = (mk_bool true)
in Const (uu____3557))
in ((FStar_Getopt.noshort), ("log_types"), (uu____3556), ("Print types computed for data/val/let-bindings")))
in (

let uu____3559 = (

let uu____3571 = (

let uu____3581 = (

let uu____3582 = (mk_bool true)
in Const (uu____3582))
in ((FStar_Getopt.noshort), ("log_queries"), (uu____3581), ("Log the Z3 queries in several queries-*.smt2 files, as we go")))
in (

let uu____3584 = (

let uu____3596 = (

let uu____3608 = (

let uu____3620 = (

let uu____3632 = (

let uu____3642 = (

let uu____3643 = (mk_bool true)
in Const (uu____3643))
in ((FStar_Getopt.noshort), ("MLish"), (uu____3642), ("Trigger various specializations for compiling the F* compiler itself (not meant for user code)")))
in (

let uu____3645 = (

let uu____3657 = (

let uu____3669 = (

let uu____3679 = (

let uu____3680 = (mk_bool true)
in Const (uu____3680))
in ((FStar_Getopt.noshort), ("no_default_includes"), (uu____3679), ("Ignore the default module search paths")))
in (

let uu____3682 = (

let uu____3694 = (

let uu____3706 = (

let uu____3716 = (

let uu____3717 = (mk_bool true)
in Const (uu____3717))
in ((FStar_Getopt.noshort), ("no_location_info"), (uu____3716), ("Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")))
in (

let uu____3719 = (

let uu____3731 = (

let uu____3741 = (

let uu____3742 = (mk_bool true)
in Const (uu____3742))
in ((FStar_Getopt.noshort), ("no_smt"), (uu____3741), ("Do not send any queries to the SMT solver, and fail on them instead")))
in (

let uu____3744 = (

let uu____3756 = (

let uu____3766 = (

let uu____3767 = (mk_bool true)
in Const (uu____3767))
in ((FStar_Getopt.noshort), ("normalize_pure_terms_for_extraction"), (uu____3766), ("Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")))
in (

let uu____3769 = (

let uu____3781 = (

let uu____3793 = (

let uu____3805 = (

let uu____3815 = (

let uu____3816 = (mk_bool true)
in Const (uu____3816))
in ((FStar_Getopt.noshort), ("print_bound_var_types"), (uu____3815), ("Print the types of bound variables")))
in (

let uu____3818 = (

let uu____3830 = (

let uu____3840 = (

let uu____3841 = (mk_bool true)
in Const (uu____3841))
in ((FStar_Getopt.noshort), ("print_effect_args"), (uu____3840), ("Print inferred predicate transformers for all computation types")))
in (

let uu____3843 = (

let uu____3855 = (

let uu____3865 = (

let uu____3866 = (mk_bool true)
in Const (uu____3866))
in ((FStar_Getopt.noshort), ("print_full_names"), (uu____3865), ("Print full names of variables")))
in (

let uu____3868 = (

let uu____3880 = (

let uu____3890 = (

let uu____3891 = (mk_bool true)
in Const (uu____3891))
in ((FStar_Getopt.noshort), ("print_implicits"), (uu____3890), ("Print implicit arguments")))
in (

let uu____3893 = (

let uu____3905 = (

let uu____3915 = (

let uu____3916 = (mk_bool true)
in Const (uu____3916))
in ((FStar_Getopt.noshort), ("print_universes"), (uu____3915), ("Print universes")))
in (

let uu____3918 = (

let uu____3930 = (

let uu____3940 = (

let uu____3941 = (mk_bool true)
in Const (uu____3941))
in ((FStar_Getopt.noshort), ("print_z3_statistics"), (uu____3940), ("Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")))
in (

let uu____3943 = (

let uu____3955 = (

let uu____3965 = (

let uu____3966 = (mk_bool true)
in Const (uu____3966))
in ((FStar_Getopt.noshort), ("prn"), (uu____3965), ("Print full names (deprecated; use --print_full_names instead)")))
in (

let uu____3968 = (

let uu____3980 = (

let uu____3990 = (

let uu____3991 = (mk_bool true)
in Const (uu____3991))
in ((FStar_Getopt.noshort), ("query_stats"), (uu____3990), ("Print SMT query statistics")))
in (

let uu____3993 = (

let uu____4005 = (

let uu____4015 = (

let uu____4016 = (mk_bool true)
in Const (uu____4016))
in ((FStar_Getopt.noshort), ("record_hints"), (uu____4015), ("Record a database of hints for efficient proof replay")))
in (

let uu____4018 = (

let uu____4030 = (

let uu____4042 = (

let uu____4052 = (

let uu____4053 = (mk_bool true)
in Const (uu____4053))
in ((FStar_Getopt.noshort), ("silent"), (uu____4052), (" ")))
in (

let uu____4055 = (

let uu____4067 = (

let uu____4079 = (

let uu____4091 = (

let uu____4103 = (

let uu____4115 = (

let uu____4125 = (

let uu____4126 = (mk_bool true)
in Const (uu____4126))
in ((FStar_Getopt.noshort), ("tactic_raw_binders"), (uu____4125), ("Do not use the lexical scope of tactics to improve binder names")))
in (

let uu____4128 = (

let uu____4140 = (

let uu____4150 = (

let uu____4151 = (mk_bool true)
in Const (uu____4151))
in ((FStar_Getopt.noshort), ("tactic_trace"), (uu____4150), ("Print a depth-indexed trace of tactic execution (Warning: very verbose)")))
in (

let uu____4153 = (

let uu____4165 = (

let uu____4177 = (

let uu____4187 = (

let uu____4188 = (mk_bool true)
in Const (uu____4188))
in ((FStar_Getopt.noshort), ("__tactics_nbe"), (uu____4187), ("Use NBE to evaluate metaprograms (experimental)")))
in (

let uu____4190 = (

let uu____4202 = (

let uu____4212 = (

let uu____4213 = (mk_bool true)
in Const (uu____4213))
in ((FStar_Getopt.noshort), ("timing"), (uu____4212), ("Print the time it takes to verify each top-level definition")))
in (

let uu____4215 = (

let uu____4227 = (

let uu____4237 = (

let uu____4238 = (mk_bool true)
in Const (uu____4238))
in ((FStar_Getopt.noshort), ("trace_error"), (uu____4237), ("Don\'t print an error message; show an exception trace instead")))
in (

let uu____4240 = (

let uu____4252 = (

let uu____4262 = (

let uu____4263 = (mk_bool true)
in Const (uu____4263))
in ((FStar_Getopt.noshort), ("ugly"), (uu____4262), ("Emit output formatted for debugging")))
in (

let uu____4265 = (

let uu____4277 = (

let uu____4287 = (

let uu____4288 = (mk_bool true)
in Const (uu____4288))
in ((FStar_Getopt.noshort), ("unthrottle_inductives"), (uu____4287), ("Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")))
in (

let uu____4290 = (

let uu____4302 = (

let uu____4312 = (

let uu____4313 = (mk_bool true)
in Const (uu____4313))
in ((FStar_Getopt.noshort), ("unsafe_tactic_exec"), (uu____4312), ("Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")))
in (

let uu____4315 = (

let uu____4327 = (

let uu____4337 = (

let uu____4338 = (mk_bool true)
in Const (uu____4338))
in ((FStar_Getopt.noshort), ("use_eq_at_higher_order"), (uu____4337), ("Use equality constraints when comparing higher-order types (Temporary)")))
in (

let uu____4340 = (

let uu____4352 = (

let uu____4362 = (

let uu____4363 = (mk_bool true)
in Const (uu____4363))
in ((FStar_Getopt.noshort), ("use_hints"), (uu____4362), ("Use a previously recorded hints database for proof replay")))
in (

let uu____4365 = (

let uu____4377 = (

let uu____4387 = (

let uu____4388 = (mk_bool true)
in Const (uu____4388))
in ((FStar_Getopt.noshort), ("use_hint_hashes"), (uu____4387), ("Admit queries if their hash matches the hash recorded in the hints database")))
in (

let uu____4390 = (

let uu____4402 = (

let uu____4414 = (

let uu____4424 = (

let uu____4425 = (mk_bool true)
in Const (uu____4425))
in ((FStar_Getopt.noshort), ("no_tactics"), (uu____4424), ("Do not run the tactic engine before discharging a VC")))
in (

let uu____4427 = (

let uu____4439 = (

let uu____4451 = (

let uu____4463 = (

let uu____4475 = (

let uu____4485 = (

let uu____4486 = (mk_bool true)
in Const (uu____4486))
in ((FStar_Getopt.noshort), ("__temp_fast_implicits"), (uu____4485), ("Don\'t use this option yet")))
in (

let uu____4488 = (

let uu____4500 = (

let uu____4510 = (

let uu____4511 = (

let uu____4519 = (

let uu____4520 = (mk_bool true)
in Const (uu____4520))
in (((fun uu____4526 -> ((display_version ());
(FStar_All.exit (Prims.parse_int "0"));
))), (uu____4519)))
in WithSideEffect (uu____4511))
in ((118 (*v*)), ("version"), (uu____4510), ("Display version number")))
in (

let uu____4530 = (

let uu____4542 = (

let uu____4552 = (

let uu____4553 = (mk_bool true)
in Const (uu____4553))
in ((FStar_Getopt.noshort), ("warn_default_effects"), (uu____4552), ("Warn when (a -> b) is desugared to (a -> Tot b)")))
in (

let uu____4555 = (

let uu____4567 = (

let uu____4579 = (

let uu____4589 = (

let uu____4590 = (mk_bool true)
in Const (uu____4590))
in ((FStar_Getopt.noshort), ("z3refresh"), (uu____4589), ("Restart Z3 after each query; useful for ensuring proof robustness")))
in (

let uu____4592 = (

let uu____4604 = (

let uu____4616 = (

let uu____4628 = (

let uu____4640 = (

let uu____4652 = (

let uu____4662 = (

let uu____4663 = (mk_bool true)
in Const (uu____4663))
in ((FStar_Getopt.noshort), ("__no_positivity"), (uu____4662), ("Don\'t check positivity of inductive types")))
in (

let uu____4665 = (

let uu____4677 = (

let uu____4687 = (

let uu____4688 = (mk_bool true)
in Const (uu____4688))
in ((FStar_Getopt.noshort), ("__ml_no_eta_expand_coertions"), (uu____4687), ("Do not eta-expand coertions in generated OCaml")))
in (

let uu____4690 = (

let uu____4702 = (

let uu____4714 = (

let uu____4726 = (

let uu____4736 = (

let uu____4737 = (

let uu____4745 = (

let uu____4746 = (mk_bool true)
in Const (uu____4746))
in (((fun uu____4752 -> ((

let uu____4754 = (specs ())
in (display_usage_aux uu____4754));
(FStar_All.exit (Prims.parse_int "0"));
))), (uu____4745)))
in WithSideEffect (uu____4737))
in ((104 (*h*)), ("help"), (uu____4736), ("Display this information")))
in (uu____4726)::[])
in (((FStar_Getopt.noshort), ("use_extracted_interfaces"), (BoolStr), ("Extract interfaces from the dependencies and use them for verification (default \'false\')")))::uu____4714)
in (((FStar_Getopt.noshort), ("warn_error"), (SimpleStr ("")), ("The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")))::uu____4702)
in (uu____4677)::uu____4690))
in (uu____4652)::uu____4665))
in (((FStar_Getopt.noshort), ("use_two_phase_tc"), (BoolStr), ("Use the two phase typechecker (default \'true\')")))::uu____4640)
in (((FStar_Getopt.noshort), ("z3seed"), (IntStr ("positive_integer")), ("Set the Z3 random seed (default 0)")))::uu____4628)
in (((FStar_Getopt.noshort), ("z3rlimit_factor"), (IntStr ("positive_integer")), ("Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")))::uu____4616)
in (((FStar_Getopt.noshort), ("z3rlimit"), (IntStr ("positive_integer")), ("Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")))::uu____4604)
in (uu____4579)::uu____4592))
in (((FStar_Getopt.noshort), ("z3cliopt"), (ReverseAccumulated (SimpleStr ("option"))), ("Z3 command line options")))::uu____4567)
in (uu____4542)::uu____4555))
in (uu____4500)::uu____4530))
in (uu____4475)::uu____4488))
in (((FStar_Getopt.noshort), ("__temp_no_proj"), (Accumulated (SimpleStr ("module_name"))), ("Don\'t generate projectors for this module")))::uu____4463)
in (((FStar_Getopt.noshort), ("vcgen.optimize_bind_as_seq"), (EnumStr (("off")::("without_type")::("with_type")::[])), ("\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")))::uu____4451)
in (((FStar_Getopt.noshort), ("using_facts_from"), (Accumulated (SimpleStr ("One or more space-separated occurrences of \'[+|-]( * | namespace | fact id)\'"))), ("\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from \'* -FStar.Reflection +FStar.List -FStar.List.Tot\' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the \'+\' is optional: --using_facts_from \'FStar.List\' is equivalent to --using_facts_from \'+FStar.List\'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")))::uu____4439)
in (uu____4414)::uu____4427))
in (((FStar_Getopt.noshort), ("use_native_tactics"), (PathStr ("path")), ("Use compiled tactics from <path>")))::uu____4402)
in (uu____4377)::uu____4390))
in (uu____4352)::uu____4365))
in (uu____4327)::uu____4340))
in (uu____4302)::uu____4315))
in (uu____4277)::uu____4290))
in (uu____4252)::uu____4265))
in (uu____4227)::uu____4240))
in (uu____4202)::uu____4215))
in (uu____4177)::uu____4190))
in (((FStar_Getopt.noshort), ("tactic_trace_d"), (IntStr ("positive_integer")), ("Trace tactics up to a certain binding depth")))::uu____4165)
in (uu____4140)::uu____4153))
in (uu____4115)::uu____4128))
in (((FStar_Getopt.noshort), ("smtencoding.l_arith_repr"), (EnumStr (("native")::("boxwrap")::[])), ("Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if \'boxwrap\', use \'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus\'; \n\t\tif \'native\', use \'+, -, -\'; \n\t\t(default \'boxwrap\')")))::uu____4103)
in (((FStar_Getopt.noshort), ("smtencoding.nl_arith_repr"), (EnumStr (("native")::("wrapped")::("boxwrap")::[])), ("Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if \'boxwrap\' use \'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus\'; \n\t\tif \'native\' use \'*, div, mod\';\n\t\tif \'wrapped\' use \'_mul, _div, _mod : Int*Int -> Int\'; \n\t\t(default \'boxwrap\')")))::uu____4091)
in (((FStar_Getopt.noshort), ("smtencoding.elim_box"), (BoolStr), ("Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default \'false\')")))::uu____4079)
in (((FStar_Getopt.noshort), ("smt"), (PathStr ("path")), ("Path to the Z3 SMT solver (we could eventually support other solvers)")))::uu____4067)
in (uu____4042)::uu____4055))
in (((FStar_Getopt.noshort), ("reuse_hint_for"), (SimpleStr ("toplevel_name")), ("Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term \'g\'")))::uu____4030)
in (uu____4005)::uu____4018))
in (uu____3980)::uu____3993))
in (uu____3955)::uu____3968))
in (uu____3930)::uu____3943))
in (uu____3905)::uu____3918))
in (uu____3880)::uu____3893))
in (uu____3855)::uu____3868))
in (uu____3830)::uu____3843))
in (uu____3805)::uu____3818))
in (((FStar_Getopt.noshort), ("prims"), (PathStr ("file")), ("")))::uu____3793)
in (((FStar_Getopt.noshort), ("odir"), (PostProcessed (((pp_validate_dir), (PathStr ("dir"))))), ("Place output in directory <dir>")))::uu____3781)
in (uu____3756)::uu____3769))
in (uu____3731)::uu____3744))
in (uu____3706)::uu____3719))
in (((FStar_Getopt.noshort), ("no_extract"), (Accumulated (PathStr ("module name"))), ("Deprecated: use --extract instead; Do not extract code from this module")))::uu____3694)
in (uu____3669)::uu____3682))
in (((FStar_Getopt.noshort), ("n_cores"), (IntStr ("positive_integer")), ("Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")))::uu____3657)
in (uu____3632)::uu____3645))
in (((FStar_Getopt.noshort), ("min_fuel"), (IntStr ("non-negative integer")), ("Minimum number of unrolling of recursive functions to try (default 1)")))::uu____3620)
in (((FStar_Getopt.noshort), ("max_ifuel"), (IntStr ("non-negative integer")), ("Number of unrolling of inductive datatypes to try at most (default 2)")))::uu____3608)
in (((FStar_Getopt.noshort), ("max_fuel"), (IntStr ("non-negative integer")), ("Number of unrolling of recursive functions to try at most (default 8)")))::uu____3596)
in (uu____3571)::uu____3584))
in (uu____3546)::uu____3559))
in (((FStar_Getopt.noshort), ("load"), (ReverseAccumulated (PathStr ("module"))), ("Load compiled module")))::uu____3534)
in (uu____3509)::uu____3522))
in (((FStar_Getopt.noshort), ("initial_ifuel"), (IntStr ("non-negative integer")), ("Number of unrolling of inductive datatypes to try at first (default 1)")))::uu____3497)
in (((FStar_Getopt.noshort), ("initial_fuel"), (IntStr ("non-negative integer")), ("Number of unrolling of recursive functions to try initially (default 2)")))::uu____3485)
in (uu____3460)::uu____3473))
in (((FStar_Getopt.noshort), ("include"), (ReverseAccumulated (PathStr ("path"))), ("A directory in which to search for files included on the command line")))::uu____3448)
in (uu____3423)::uu____3436))
in (uu____3398)::uu____3411))
in (uu____3373)::uu____3386))
in (((FStar_Getopt.noshort), ("hint_file"), (PathStr ("path")), ("Read/write hints to <path> (instead of module-specific hints files)")))::uu____3361)
in (uu____3336)::uu____3349))
in (uu____3311)::uu____3324))
in (((FStar_Getopt.noshort), ("extract_namespace"), (Accumulated (PostProcessed (((pp_lowercase), (SimpleStr ("namespace name")))))), ("Deprecated: use --extract instead; Only extract modules in the specified namespace")))::uu____3299)
in (((FStar_Getopt.noshort), ("extract_module"), (Accumulated (PostProcessed (((pp_lowercase), (SimpleStr ("module_name")))))), ("Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")))::uu____3287)
in (((FStar_Getopt.noshort), ("extract"), (Accumulated (SimpleStr ("One or more space-separated occurrences of \'[+|-]( * | namespace | module)\'"))), ("\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract \'* -FStar.Reflection +FStar.List -FStar.List.Tot\' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the \'+\' is optional: --extract \'+A\' and --extract \'A\' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract \'A B\'.")))::uu____3275)
in (uu____3250)::uu____3263))
in (uu____3225)::uu____3238))
in (uu____3200)::uu____3213))
in (((FStar_Getopt.noshort), ("dump_module"), (Accumulated (SimpleStr ("module_name"))), ("")))::uu____3188)
in (uu____3163)::uu____3176))
in (uu____3138)::uu____3151))
in (uu____3113)::uu____3126))
in (((FStar_Getopt.noshort), ("dep"), (EnumStr (("make")::("graph")::("full")::[])), ("Output the transitive closure of the full dependency graph in three formats:\n\t \'graph\': a format suitable the \'dot\' tool from \'GraphViz\'\n\t \'full\': a format suitable for \'make\', including dependences for producing .ml and .krml files\n\t \'make\': (deprecated) a format suitable for \'make\', including only dependences among source files")))::uu____3101)
in (((FStar_Getopt.noshort), ("defensive"), (EnumStr (("no")::("warn")::("fail")::[])), ("Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif \'no\', no checks are performed\n\t\tif \'warn\', checks are performed and raise a warning when they fail\n\t\tif \'fail\', like \'warn\', but the compiler aborts instead of issuing a warning\n\t\t(default \'no\')")))::uu____3089)
in (((FStar_Getopt.noshort), ("debug_level"), (Accumulated (OpenEnumStr (((("Low")::("Medium")::("High")::("Extreme")::[]), ("..."))))), ("Control the verbosity of debugging info")))::uu____3077)
in (((FStar_Getopt.noshort), ("debug"), (Accumulated (SimpleStr ("module_name"))), ("Print lots of debugging information while checking module")))::uu____3065)
in (((FStar_Getopt.noshort), ("codegen-lib"), (Accumulated (SimpleStr ("namespace"))), ("External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")))::uu____3053)
in (((FStar_Getopt.noshort), ("codegen"), (EnumStr (("OCaml")::("FSharp")::("Kremlin")::("Plugin")::[])), ("Generate code for further compilation to executable code, or build a compiler plugin")))::uu____3041)
in (uu____3016)::uu____3029))
in (((FStar_Getopt.noshort), ("cache_dir"), (PostProcessed (((pp_validate_dir), (PathStr ("dir"))))), ("Read and write .checked and .checked.lax in directory <dir>")))::uu____3004)
in (uu____2979)::uu____2992))
in (((FStar_Getopt.noshort), ("admit_except"), (SimpleStr ("[symbol|(symbol, id)]")), ("Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except \'(FStar.Fin.pigeonhole, 1)\' or --admit_except FStar.Fin.pigeonhole)")))::uu____2967)
in (((FStar_Getopt.noshort), ("admit_smt_queries"), (BoolStr), ("Admit SMT queries, unsafe! (default \'false\')")))::uu____2955)
in (((FStar_Getopt.noshort), ("abort_on"), (PostProcessed ((((fun uu___82_5689 -> (match (uu___82_5689) with
| Int (x) -> begin
((FStar_ST.op_Colon_Equals abort_counter x);
Int (x);
)
end
| x -> begin
(failwith "?")
end))), (IntStr ("non-negative integer"))))), ("Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")))::uu____2943))
and specs : unit  ->  FStar_Getopt.opt Prims.list = (fun uu____5712 -> (

let uu____5715 = (specs_with_types ())
in (FStar_List.map (fun uu____5742 -> (match (uu____5742) with
| (short, long, typ, doc) -> begin
(

let uu____5758 = (

let uu____5770 = (arg_spec_of_opt_type long typ)
in ((short), (long), (uu____5770), (doc)))
in (mk_spec uu____5758))
end)) uu____5715)))


let settable : Prims.string  ->  Prims.bool = (fun uu___83_5780 -> (match (uu___83_5780) with
| "abort_on" -> begin
true
end
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
| "eager_embedding" -> begin
true
end
| "eager_inference" -> begin
true
end
| "eager_subtyping" -> begin
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
| "__tactics_nbe" -> begin
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
| uu____5781 -> begin
false
end))


let resettable : Prims.string  ->  Prims.bool = (fun s -> ((((settable s) || (Prims.op_Equality s "z3seed")) || (Prims.op_Equality s "z3cliopt")) || (Prims.op_Equality s "using_facts_from")))


let all_specs : FStar_Getopt.opt Prims.list = (specs ())


let all_specs_with_types : (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list = (specs_with_types ())


let settable_specs : (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____5855 -> (match (uu____5855) with
| (uu____5867, x, uu____5869, uu____5870) -> begin
(settable x)
end))))


let resettable_specs : (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____5932 -> (match (uu____5932) with
| (uu____5944, x, uu____5946, uu____5947) -> begin
(resettable x)
end))))


let display_usage : unit  ->  unit = (fun uu____5958 -> (

let uu____5959 = (specs ())
in (display_usage_aux uu____5959)))


let fstar_bin_directory : Prims.string = (FStar_Util.get_exec_dir ())

exception File_argument of (Prims.string)


let uu___is_File_argument : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| File_argument (uu____5983) -> begin
true
end
| uu____5984 -> begin
false
end))


let __proj__File_argument__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| File_argument (uu____5991) -> begin
uu____5991
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
in (FStar_All.try_with (fun uu___88_6008 -> (match (()) with
| () -> begin
(match ((Prims.op_Equality s "")) with
| true -> begin
FStar_Getopt.Success
end
| uu____6009 -> begin
(FStar_Getopt.parse_string specs1 (fun s1 -> (FStar_Exn.raise (File_argument (s1)))) s)
end)
end)) (fun uu___87_6017 -> (match (uu___87_6017) with
| File_argument (s1) -> begin
(

let uu____6019 = (FStar_Util.format1 "File %s is not a valid option" s1)
in FStar_Getopt.Error (uu____6019))
end)))))


let file_list_ : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let parse_cmd_line : unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____6047 -> (

let res = (FStar_Getopt.parse_cmdline all_specs (fun i -> (

let uu____6052 = (

let uu____6055 = (FStar_ST.op_Bang file_list_)
in (FStar_List.append uu____6055 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list_ uu____6052))))
in (

let uu____6104 = (

let uu____6107 = (FStar_ST.op_Bang file_list_)
in (FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6107))
in ((res), (uu____6104)))))


let file_list : unit  ->  Prims.string Prims.list = (fun uu____6141 -> (FStar_ST.op_Bang file_list_))


let restore_cmd_line_options : Prims.bool  ->  FStar_Getopt.parse_cmdline_res = (fun should_clear -> (

let old_verify_module = (get_verify_module ())
in ((match (should_clear) with
| true -> begin
(clear ())
end
| uu____6174 -> begin
(init ())
end);
(

let r = (

let uu____6176 = (specs ())
in (FStar_Getopt.parse_cmdline uu____6176 (fun x -> ())))
in ((

let uu____6182 = (

let uu____6187 = (

let uu____6188 = (FStar_List.map mk_string old_verify_module)
in List (uu____6188))
in (("verify_module"), (uu____6187)))
in (set_option' uu____6182));
r;
));
)))


let module_name_of_file_name : Prims.string  ->  Prims.string = (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let f2 = (

let uu____6198 = (

let uu____6199 = (

let uu____6200 = (

let uu____6201 = (FStar_Util.get_file_extension f1)
in (FStar_String.length uu____6201))
in ((FStar_String.length f1) - uu____6200))
in (uu____6199 - (Prims.parse_int "1")))
in (FStar_String.substring f1 (Prims.parse_int "0") uu____6198))
in (FStar_String.lowercase f2))))


let should_verify : Prims.string  ->  Prims.bool = (fun m -> (

let uu____6207 = (get_lax ())
in (match (uu____6207) with
| true -> begin
false
end
| uu____6208 -> begin
(

let l = (get_verify_module ())
in (FStar_List.contains (FStar_String.lowercase m) l))
end)))


let should_verify_file : Prims.string  ->  Prims.bool = (fun fn -> (

let uu____6217 = (module_name_of_file_name fn)
in (should_verify uu____6217)))


let dont_gen_projectors : Prims.string  ->  Prims.bool = (fun m -> (

let uu____6223 = (get___temp_no_proj ())
in (FStar_List.contains m uu____6223)))


let should_print_message : Prims.string  ->  Prims.bool = (fun m -> (

let uu____6231 = (should_verify m)
in (match (uu____6231) with
| true -> begin
(Prims.op_disEquality m "Prims")
end
| uu____6232 -> begin
false
end)))


let include_path : unit  ->  Prims.string Prims.list = (fun uu____6239 -> (

let uu____6240 = (get_no_default_includes ())
in (match (uu____6240) with
| true -> begin
(get_include ())
end
| uu____6243 -> begin
(

let lib_paths = (

let uu____6247 = (FStar_Util.expand_environment_variable "FSTAR_LIB")
in (match (uu____6247) with
| FStar_Pervasives_Native.None -> begin
(

let fstar_home = (Prims.strcat fstar_bin_directory "/..")
in (

let defs = universe_include_path_base_dirs
in (

let uu____6256 = (FStar_All.pipe_right defs (FStar_List.map (fun x -> (Prims.strcat fstar_home x))))
in (FStar_All.pipe_right uu____6256 (FStar_List.filter FStar_Util.file_exists)))))
end
| FStar_Pervasives_Native.Some (s) -> begin
(s)::[]
end))
in (

let uu____6270 = (

let uu____6273 = (get_include ())
in (FStar_List.append uu____6273 ((".")::[])))
in (FStar_List.append lib_paths uu____6270)))
end)))


let find_file : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (

let file_map = (FStar_Util.smap_create (Prims.parse_int "100"))
in (fun filename -> (

let uu____6286 = (FStar_Util.smap_try_find file_map filename)
in (match (uu____6286) with
| FStar_Pervasives_Native.Some (f) -> begin
FStar_Pervasives_Native.Some (f)
end
| FStar_Pervasives_Native.None -> begin
(

let result = (FStar_All.try_with (fun uu___90_6299 -> (match (()) with
| () -> begin
(

let uu____6302 = (FStar_Util.is_path_absolute filename)
in (match (uu____6302) with
| true -> begin
(match ((FStar_Util.file_exists filename)) with
| true -> begin
FStar_Pervasives_Native.Some (filename)
end
| uu____6307 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____6308 -> begin
(

let uu____6309 = (

let uu____6312 = (include_path ())
in (FStar_List.rev uu____6312))
in (FStar_Util.find_map uu____6309 (fun p -> (

let path = (match ((Prims.op_Equality p ".")) with
| true -> begin
filename
end
| uu____6319 -> begin
(FStar_Util.join_paths p filename)
end)
in (match ((FStar_Util.file_exists path)) with
| true -> begin
FStar_Pervasives_Native.Some (path)
end
| uu____6322 -> begin
FStar_Pervasives_Native.None
end)))))
end))
end)) (fun uu___89_6325 -> (match (uu___89_6325) with
| uu____6328 -> begin
FStar_Pervasives_Native.None
end)))
in (match (result) with
| FStar_Pervasives_Native.None -> begin
result
end
| FStar_Pervasives_Native.Some (f) -> begin
((FStar_Util.smap_add file_map filename f);
result;
)
end))
end))))


let prims : unit  ->  Prims.string = (fun uu____6337 -> (

let uu____6338 = (get_prims ())
in (match (uu____6338) with
| FStar_Pervasives_Native.None -> begin
(

let filename = "prims.fst"
in (

let uu____6342 = (find_file filename)
in (match (uu____6342) with
| FStar_Pervasives_Native.Some (result) -> begin
result
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6346 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____6346))
end)))
end
| FStar_Pervasives_Native.Some (x) -> begin
x
end)))


let prims_basename : unit  ->  Prims.string = (fun uu____6352 -> (

let uu____6353 = (prims ())
in (FStar_Util.basename uu____6353)))


let pervasives : unit  ->  Prims.string = (fun uu____6358 -> (

let filename = "FStar.Pervasives.fst"
in (

let uu____6360 = (find_file filename)
in (match (uu____6360) with
| FStar_Pervasives_Native.Some (result) -> begin
result
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6364 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____6364))
end))))


let pervasives_basename : unit  ->  Prims.string = (fun uu____6369 -> (

let uu____6370 = (pervasives ())
in (FStar_Util.basename uu____6370)))


let pervasives_native_basename : unit  ->  Prims.string = (fun uu____6375 -> (

let filename = "FStar.Pervasives.Native.fst"
in (

let uu____6377 = (find_file filename)
in (match (uu____6377) with
| FStar_Pervasives_Native.Some (result) -> begin
(FStar_Util.basename result)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6381 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____6381))
end))))


let prepend_output_dir : Prims.string  ->  Prims.string = (fun fname -> (

let uu____6387 = (get_odir ())
in (match (uu____6387) with
| FStar_Pervasives_Native.None -> begin
fname
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Util.join_paths x fname)
end)))


let prepend_cache_dir : Prims.string  ->  Prims.string = (fun fpath -> (

let uu____6396 = (get_cache_dir ())
in (match (uu____6396) with
| FStar_Pervasives_Native.None -> begin
fpath
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____6400 = (FStar_Util.basename fpath)
in (FStar_Util.join_paths x uu____6400))
end)))


let path_of_text : Prims.string  ->  Prims.string Prims.list = (fun text -> (FStar_String.split ((46 (*.*))::[]) text))


let parse_settings : Prims.string Prims.list  ->  (Prims.string Prims.list * Prims.bool) Prims.list = (fun ns -> (

let parse_one_setting = (fun s -> (match ((Prims.op_Equality s "*")) with
| true -> begin
(([]), (true))
end
| uu____6456 -> begin
(match ((FStar_Util.starts_with s "-")) with
| true -> begin
(

let path = (

let uu____6466 = (FStar_Util.substring_from s (Prims.parse_int "1"))
in (path_of_text uu____6466))
in ((path), (false)))
end
| uu____6469 -> begin
(

let s1 = (match ((FStar_Util.starts_with s "+")) with
| true -> begin
(FStar_Util.substring_from s (Prims.parse_int "1"))
end
| uu____6471 -> begin
s
end)
in (((path_of_text s1)), (true)))
end)
end))
in (

let uu____6474 = (FStar_All.pipe_right ns (FStar_List.collect (fun s -> (FStar_All.pipe_right (FStar_Util.split s " ") (FStar_List.map parse_one_setting)))))
in (FStar_All.pipe_right uu____6474 FStar_List.rev))))


let __temp_no_proj : Prims.string  ->  Prims.bool = (fun s -> (

let uu____6544 = (get___temp_no_proj ())
in (FStar_All.pipe_right uu____6544 (FStar_List.contains s))))


let __temp_fast_implicits : unit  ->  Prims.bool = (fun uu____6553 -> (lookup_opt "__temp_fast_implicits" as_bool))


let admit_smt_queries : unit  ->  Prims.bool = (fun uu____6558 -> (get_admit_smt_queries ()))


let admit_except : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6565 -> (get_admit_except ()))


let cache_checked_modules : unit  ->  Prims.bool = (fun uu____6570 -> (get_cache_checked_modules ()))


let cache_off : unit  ->  Prims.bool = (fun uu____6575 -> (get_cache_off ()))

type codegen_t =
| OCaml
| FSharp
| Kremlin
| Plugin


let uu___is_OCaml : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OCaml -> begin
true
end
| uu____6581 -> begin
false
end))


let uu___is_FSharp : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FSharp -> begin
true
end
| uu____6587 -> begin
false
end))


let uu___is_Kremlin : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Kremlin -> begin
true
end
| uu____6593 -> begin
false
end))


let uu___is_Plugin : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Plugin -> begin
true
end
| uu____6599 -> begin
false
end))


let codegen : unit  ->  codegen_t FStar_Pervasives_Native.option = (fun uu____6606 -> (

let uu____6607 = (get_codegen ())
in (FStar_Util.map_opt uu____6607 (fun uu___84_6611 -> (match (uu___84_6611) with
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
| uu____6612 -> begin
(failwith "Impossible")
end)))))


let codegen_libs : unit  ->  Prims.string Prims.list Prims.list = (fun uu____6621 -> (

let uu____6622 = (get_codegen_lib ())
in (FStar_All.pipe_right uu____6622 (FStar_List.map (fun x -> (FStar_Util.split x "."))))))


let debug_any : unit  ->  Prims.bool = (fun uu____6639 -> (

let uu____6640 = (get_debug ())
in (Prims.op_disEquality uu____6640 [])))


let debug_module : Prims.string  ->  Prims.bool = (fun modul -> (

let uu____6650 = (get_debug ())
in (FStar_All.pipe_right uu____6650 (FStar_List.contains modul))))


let debug_at_level : Prims.string  ->  debug_level_t  ->  Prims.bool = (fun modul level -> ((

let uu____6667 = (get_debug ())
in (FStar_All.pipe_right uu____6667 (FStar_List.contains modul))) && (debug_level_geq level)))


let defensive : unit  ->  Prims.bool = (fun uu____6676 -> (

let uu____6677 = (get_defensive ())
in (Prims.op_disEquality uu____6677 "no")))


let defensive_fail : unit  ->  Prims.bool = (fun uu____6682 -> (

let uu____6683 = (get_defensive ())
in (Prims.op_Equality uu____6683 "fail")))


let dep : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6690 -> (get_dep ()))


let detail_errors : unit  ->  Prims.bool = (fun uu____6695 -> (get_detail_errors ()))


let detail_hint_replay : unit  ->  Prims.bool = (fun uu____6700 -> (get_detail_hint_replay ()))


let doc : unit  ->  Prims.bool = (fun uu____6705 -> (get_doc ()))


let dump_module : Prims.string  ->  Prims.bool = (fun s -> (

let uu____6711 = (get_dump_module ())
in (FStar_All.pipe_right uu____6711 (FStar_List.contains s))))


let eager_embedding : unit  ->  Prims.bool = (fun uu____6720 -> (get_eager_embedding ()))


let eager_subtyping : unit  ->  Prims.bool = (fun uu____6725 -> (get_eager_subtyping ()))


let expose_interfaces : unit  ->  Prims.bool = (fun uu____6730 -> (get_expose_interfaces ()))


let fs_typ_app : Prims.string  ->  Prims.bool = (fun filename -> (

let uu____6736 = (FStar_ST.op_Bang light_off_files)
in (FStar_List.contains filename uu____6736)))


let full_context_dependency : unit  ->  Prims.bool = (fun uu____6766 -> true)


let hide_uvar_nums : unit  ->  Prims.bool = (fun uu____6771 -> (get_hide_uvar_nums ()))


let hint_info : unit  ->  Prims.bool = (fun uu____6776 -> ((get_hint_info ()) || (get_query_stats ())))


let hint_file : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6783 -> (get_hint_file ()))


let ide : unit  ->  Prims.bool = (fun uu____6788 -> (get_ide ()))


let indent : unit  ->  Prims.bool = (fun uu____6793 -> (get_indent ()))


let initial_fuel : unit  ->  Prims.int = (fun uu____6798 -> (

let uu____6799 = (get_initial_fuel ())
in (

let uu____6800 = (get_max_fuel ())
in (Prims.min uu____6799 uu____6800))))


let initial_ifuel : unit  ->  Prims.int = (fun uu____6805 -> (

let uu____6806 = (get_initial_ifuel ())
in (

let uu____6807 = (get_max_ifuel ())
in (Prims.min uu____6806 uu____6807))))


let interactive : unit  ->  Prims.bool = (fun uu____6812 -> ((get_in ()) || (get_ide ())))


let lax : unit  ->  Prims.bool = (fun uu____6817 -> (get_lax ()))


let load : unit  ->  Prims.string Prims.list = (fun uu____6824 -> (get_load ()))


let legacy_interactive : unit  ->  Prims.bool = (fun uu____6829 -> (get_in ()))


let log_queries : unit  ->  Prims.bool = (fun uu____6834 -> (get_log_queries ()))


let log_types : unit  ->  Prims.bool = (fun uu____6839 -> (get_log_types ()))


let max_fuel : unit  ->  Prims.int = (fun uu____6844 -> (get_max_fuel ()))


let max_ifuel : unit  ->  Prims.int = (fun uu____6849 -> (get_max_ifuel ()))


let min_fuel : unit  ->  Prims.int = (fun uu____6854 -> (get_min_fuel ()))


let ml_ish : unit  ->  Prims.bool = (fun uu____6859 -> (get_MLish ()))


let set_ml_ish : unit  ->  unit = (fun uu____6864 -> (set_option "MLish" (Bool (true))))


let n_cores : unit  ->  Prims.int = (fun uu____6869 -> (get_n_cores ()))


let no_default_includes : unit  ->  Prims.bool = (fun uu____6874 -> (get_no_default_includes ()))


let no_extract : Prims.string  ->  Prims.bool = (fun s -> (

let s1 = (FStar_String.lowercase s)
in (

let uu____6881 = (get_no_extract ())
in (FStar_All.pipe_right uu____6881 (FStar_Util.for_some (fun f -> (Prims.op_Equality (FStar_String.lowercase f) s1)))))))


let normalize_pure_terms_for_extraction : unit  ->  Prims.bool = (fun uu____6892 -> (get_normalize_pure_terms_for_extraction ()))


let no_location_info : unit  ->  Prims.bool = (fun uu____6897 -> (get_no_location_info ()))


let no_smt : unit  ->  Prims.bool = (fun uu____6902 -> (get_no_smt ()))


let output_dir : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6909 -> (get_odir ()))


let ugly : unit  ->  Prims.bool = (fun uu____6914 -> (get_ugly ()))


let print_bound_var_types : unit  ->  Prims.bool = (fun uu____6919 -> (get_print_bound_var_types ()))


let print_effect_args : unit  ->  Prims.bool = (fun uu____6924 -> (get_print_effect_args ()))


let print_implicits : unit  ->  Prims.bool = (fun uu____6929 -> (get_print_implicits ()))


let print_real_names : unit  ->  Prims.bool = (fun uu____6934 -> ((get_prn ()) || (get_print_full_names ())))


let print_universes : unit  ->  Prims.bool = (fun uu____6939 -> (get_print_universes ()))


let print_z3_statistics : unit  ->  Prims.bool = (fun uu____6944 -> ((get_print_z3_statistics ()) || (get_query_stats ())))


let query_stats : unit  ->  Prims.bool = (fun uu____6949 -> (get_query_stats ()))


let record_hints : unit  ->  Prims.bool = (fun uu____6954 -> (get_record_hints ()))


let reuse_hint_for : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6961 -> (get_reuse_hint_for ()))


let silent : unit  ->  Prims.bool = (fun uu____6966 -> (get_silent ()))


let smtencoding_elim_box : unit  ->  Prims.bool = (fun uu____6971 -> (get_smtencoding_elim_box ()))


let smtencoding_nl_arith_native : unit  ->  Prims.bool = (fun uu____6976 -> (

let uu____6977 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____6977 "native")))


let smtencoding_nl_arith_wrapped : unit  ->  Prims.bool = (fun uu____6982 -> (

let uu____6983 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____6983 "wrapped")))


let smtencoding_nl_arith_default : unit  ->  Prims.bool = (fun uu____6988 -> (

let uu____6989 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____6989 "boxwrap")))


let smtencoding_l_arith_native : unit  ->  Prims.bool = (fun uu____6994 -> (

let uu____6995 = (get_smtencoding_l_arith_repr ())
in (Prims.op_Equality uu____6995 "native")))


let smtencoding_l_arith_default : unit  ->  Prims.bool = (fun uu____7000 -> (

let uu____7001 = (get_smtencoding_l_arith_repr ())
in (Prims.op_Equality uu____7001 "boxwrap")))


let tactic_raw_binders : unit  ->  Prims.bool = (fun uu____7006 -> (get_tactic_raw_binders ()))


let tactic_trace : unit  ->  Prims.bool = (fun uu____7011 -> (get_tactic_trace ()))


let tactic_trace_d : unit  ->  Prims.int = (fun uu____7016 -> (get_tactic_trace_d ()))


let tactics_nbe : unit  ->  Prims.bool = (fun uu____7021 -> (get_tactics_nbe ()))


let timing : unit  ->  Prims.bool = (fun uu____7026 -> (get_timing ()))


let trace_error : unit  ->  Prims.bool = (fun uu____7031 -> (get_trace_error ()))


let unthrottle_inductives : unit  ->  Prims.bool = (fun uu____7036 -> (get_unthrottle_inductives ()))


let unsafe_tactic_exec : unit  ->  Prims.bool = (fun uu____7041 -> (get_unsafe_tactic_exec ()))


let use_eq_at_higher_order : unit  ->  Prims.bool = (fun uu____7046 -> (get_use_eq_at_higher_order ()))


let use_hints : unit  ->  Prims.bool = (fun uu____7051 -> (get_use_hints ()))


let use_hint_hashes : unit  ->  Prims.bool = (fun uu____7056 -> (get_use_hint_hashes ()))


let use_native_tactics : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____7063 -> (get_use_native_tactics ()))


let use_tactics : unit  ->  Prims.bool = (fun uu____7068 -> (get_use_tactics ()))


let using_facts_from : unit  ->  (Prims.string Prims.list * Prims.bool) Prims.list = (fun uu____7081 -> (

let uu____7082 = (get_using_facts_from ())
in (match (uu____7082) with
| FStar_Pervasives_Native.None -> begin
((([]), (true)))::[]
end
| FStar_Pervasives_Native.Some (ns) -> begin
(parse_settings ns)
end)))


let vcgen_optimize_bind_as_seq : unit  ->  Prims.bool = (fun uu____7120 -> (

let uu____7121 = (get_vcgen_optimize_bind_as_seq ())
in (FStar_Option.isSome uu____7121)))


let vcgen_decorate_with_type : unit  ->  Prims.bool = (fun uu____7128 -> (

let uu____7129 = (get_vcgen_optimize_bind_as_seq ())
in (match (uu____7129) with
| FStar_Pervasives_Native.Some ("with_type") -> begin
true
end
| uu____7132 -> begin
false
end)))


let warn_default_effects : unit  ->  Prims.bool = (fun uu____7139 -> (get_warn_default_effects ()))


let z3_exe : unit  ->  Prims.string = (fun uu____7144 -> (

let uu____7145 = (get_smt ())
in (match (uu____7145) with
| FStar_Pervasives_Native.None -> begin
(FStar_Platform.exe "z3")
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let z3_cliopt : unit  ->  Prims.string Prims.list = (fun uu____7155 -> (get_z3cliopt ()))


let z3_refresh : unit  ->  Prims.bool = (fun uu____7160 -> (get_z3refresh ()))


let z3_rlimit : unit  ->  Prims.int = (fun uu____7165 -> (get_z3rlimit ()))


let z3_rlimit_factor : unit  ->  Prims.int = (fun uu____7170 -> (get_z3rlimit_factor ()))


let z3_seed : unit  ->  Prims.int = (fun uu____7175 -> (get_z3seed ()))


let use_two_phase_tc : unit  ->  Prims.bool = (fun uu____7180 -> ((get_use_two_phase_tc ()) && (

let uu____7182 = (lax ())
in (not (uu____7182)))))


let no_positivity : unit  ->  Prims.bool = (fun uu____7187 -> (get_no_positivity ()))


let ml_no_eta_expand_coertions : unit  ->  Prims.bool = (fun uu____7192 -> (get_ml_no_eta_expand_coertions ()))


let warn_error : unit  ->  Prims.string = (fun uu____7197 -> (get_warn_error ()))


let use_extracted_interfaces : unit  ->  Prims.bool = (fun uu____7202 -> (get_use_extracted_interfaces ()))


let should_extract : Prims.string  ->  Prims.bool = (fun m -> (

let m1 = (FStar_String.lowercase m)
in (

let uu____7209 = (get_extract ())
in (match (uu____7209) with
| FStar_Pervasives_Native.Some (extract_setting) -> begin
((

let uu____7220 = (

let uu____7233 = (get_no_extract ())
in (

let uu____7236 = (get_extract_namespace ())
in (

let uu____7239 = (get_extract_module ())
in ((uu____7233), (uu____7236), (uu____7239)))))
in (match (uu____7220) with
| ([], [], []) -> begin
()
end
| uu____7254 -> begin
(failwith "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module")
end));
(

let setting = (parse_settings extract_setting)
in (

let m_components = (path_of_text m1)
in (

let rec matches_path = (fun m_components1 path -> (match (((m_components1), (path))) with
| (uu____7302, []) -> begin
true
end
| ((m2)::ms, (p)::ps) -> begin
((Prims.op_Equality m2 (FStar_String.lowercase p)) && (matches_path ms ps))
end
| uu____7321 -> begin
false
end))
in (

let uu____7330 = (FStar_All.pipe_right setting (FStar_Util.try_find (fun uu____7364 -> (match (uu____7364) with
| (path, uu____7372) -> begin
(matches_path m_components path)
end))))
in (match (uu____7330) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____7383, flag) -> begin
flag
end)))));
)
end
| FStar_Pervasives_Native.None -> begin
(

let should_extract_namespace = (fun m2 -> (

let uu____7403 = (get_extract_namespace ())
in (match (uu____7403) with
| [] -> begin
false
end
| ns -> begin
(FStar_All.pipe_right ns (FStar_Util.for_some (fun n1 -> (FStar_Util.starts_with m2 (FStar_String.lowercase n1)))))
end)))
in (

let should_extract_module = (fun m2 -> (

let uu____7419 = (get_extract_module ())
in (match (uu____7419) with
| [] -> begin
false
end
| l -> begin
(FStar_All.pipe_right l (FStar_Util.for_some (fun n1 -> (Prims.op_Equality (FStar_String.lowercase n1) m2))))
end)))
in ((

let uu____7431 = (no_extract m1)
in (not (uu____7431))) && (

let uu____7433 = (

let uu____7442 = (get_extract_namespace ())
in (

let uu____7445 = (get_extract_module ())
in ((uu____7442), (uu____7445))))
in (match (uu____7433) with
| ([], []) -> begin
true
end
| uu____7456 -> begin
((should_extract_namespace m1) || (should_extract_module m1))
end)))))
end))))




